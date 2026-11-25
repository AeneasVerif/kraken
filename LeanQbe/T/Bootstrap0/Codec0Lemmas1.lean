module

public import LeanQbe.T.Bootstrap0.Codec0
public import LeanQbe.T.Bootstrap0.Codec0Kit

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
  | .let1 _ _ k, h => by
    simp only [checkTFlat0ListBounded, TFlat0ListBounded, Bool.and_eq_true,
      decide_eq_true_eq] at h ⊢
    exact ⟨h.1, checkTFlat0ListBounded_sound k h.2⟩
  | .let2Umulw64 _ _ k, h | .load _ _ k, h | .store _ _ _ k, h =>
    checkTFlat0ListBounded_sound k h
  | .call _ _ _ _ k, h => by
    simp only [checkTFlat0ListBounded, TFlat0ListBounded, Bool.and_eq_true,
      decide_eq_true_eq] at h ⊢
    exact ⟨h.1.1.1, h.1.1.2, h.1.2, checkTFlat0ListBounded_sound k h.2⟩
  | .tailCall _ _ _, h | .exit _ _ _, h => by
    simpa only [checkTFlat0ListBounded, TFlat0ListBounded, Bool.and_eq_true,
      decide_eq_true_eq] using h
  | .jnz _ t e, h => by
    simp only [checkTFlat0ListBounded, TFlat0ListBounded, Bool.and_eq_true] at h ⊢
    exact ⟨checkTFlat0ListBounded_sound t h.1, checkTFlat0ListBounded_sound e h.2⟩
  | .jump _ _, h | .ret _, h => by
    simpa only [checkTFlat0ListBounded, TFlat0ListBounded, decide_eq_true_eq] using h
  | .hlt, _ => trivial
  | .group bodies k, h => by
    simp only [checkTFlat0ListBounded, TFlat0ListBounded, Bool.and_eq_true,
      decide_eq_true_eq] at h ⊢
    exact ⟨h.1.1, checkBlocks0ListBounded_sound bodies h.1.2, checkTFlat0ListBounded_sound k h.2⟩

private theorem checkBlocks0ListBounded_sound :
    ∀ bs, checkBlocks0ListBounded bs = true → Blocks0ListBounded bs
  | [], _ => trivial
  | (_, b) :: rest, h => by
    simp only [checkBlocks0ListBounded, Blocks0ListBounded, Bool.and_eq_true,
      decide_eq_true_eq] at h ⊢
    exact ⟨h.1.1, checkTFlat0ListBounded_sound b h.1.2, checkBlocks0ListBounded_sound rest h.2⟩
end

/-- Soundness of `checkMod0Bounded` for proving `Mod0Bounded`. -/
public theorem mod0Bounded_of_check (m : TFlatModule0) (h : checkMod0Bounded m = true) :
    Mod0Bounded m := by
  simp only [checkMod0Bounded, Mod0Bounded, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at h ⊢
  refine ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, ?_, ?_⟩
  · intro fn hfn
    have h1 := h.1.2 fn hfn
    exact ⟨h1.1.1.1, h1.1.1.2, checkTFlat0ListBounded_sound fn.body h1.1.2, h1.2⟩
  · intro ex hex
    exact h.2 ex hex


namespace Codec0Spec

/-! ## 2. `ByteArray` and Slice Algebra Helpers -/

public abbrev baSlice (ba : ByteArray) (p0 p1 : Nat) : List UInt8 :=
  Codec0Kit.baSlice ba p0 p1

public theorem ba_eq_of_data_toList {a b : ByteArray} (h : a.data.toList = b.data.toList) :
    a = b := by
  cases a; cases b; congr 1; exact Array.ext' h

public theorem ba_data_toList_length (ba : ByteArray) : ba.data.toList.length = ba.size :=
  Codec0Kit.ba_data_toList_length ba

public theorem ba_push_data_toList (ba : ByteArray) (b : UInt8) :
    (ba.push b).data.toList = ba.data.toList ++ [b] := by
  cases ba; exact Array.toList_push

public theorem ba_emptyWithCapacity_data_toList (c : Nat) :
    (ByteArray.emptyWithCapacity c).data.toList = [] := rfl

public theorem ba_e2_data_toList (ba : ByteArray) (a b : UInt8) :
    (Codec0.e2 ba a b).data.toList = ba.data.toList ++ [a, b] := by
  dsimp only [Codec0.e2]; simp only [ba_push_data_toList, List.append_assoc]; rfl

public theorem ba_e4_data_toList (ba : ByteArray) (a b c d : UInt8) :
    (Codec0.e4 ba a b c d).data.toList = ba.data.toList ++ [a, b, c, d] := by
  dsimp only [Codec0.e4]; simp only [ba_push_data_toList, List.append_assoc]; rfl

public theorem drop_pos_add (l : List UInt8) (a b : Nat) :
    l.drop (a + b) = (l.drop a).drop b :=
  Codec0Kit.drop_pos_add l a b

public theorem baSlice_zero_self (ba : ByteArray) : baSlice ba 0 ba.size = ba.data.toList :=
  Codec0Kit.baSlice_zero_self ba

public theorem baSlice_self (ba : ByteArray) (p : Nat) : baSlice ba p p = [] :=
  Codec0Kit.baSlice_self ba p

public theorem baSlice_trans {ba : ByteArray} {p0 p1 p2 : Nat}
    (h01 : p0 ≤ p1) (h12 : p1 ≤ p2) :
    baSlice ba p0 p2 = baSlice ba p0 p1 ++ baSlice ba p1 p2 :=
  Codec0Kit.baSlice_trans h01 h12

public theorem dite_true_eq {p : Prop} [Decidable p] {α : Sort _} {a : p → α} {b : ¬ p → α}
    (h : p) : (if h' : p then a h' else b h') = a h :=
  Codec0Kit.dite_true_eq h

public theorem dite_false_eq {p : Prop} [Decidable p] {α : Sort _} {a : p → α} {b : ¬ p → α}
    (h : ¬ p) : (if h' : p then a h' else b h') = b h :=
  Codec0Kit.dite_false_eq h

public theorem ite_true_eq {p : Prop} [Decidable p] {α : Sort _} {a b : α} (h : p) :
    (if p then a else b) = a :=
  Codec0Kit.ite_true_eq h

public theorem ite_false_eq {p : Prop} [Decidable p] {α : Sort _} {a b : α} (h : ¬ p) :
    (if p then a else b) = b :=
  Codec0Kit.ite_false_eq h

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
  rw [ba_push_data_toList, ba_e4_data_toList, List.append_assoc]; rfl

public theorem encodeU32_bytes (ba : ByteArray) (v : UInt32) :
    (Codec0.encodeU32 ba v).data.toList = ba.data.toList ++ u32Bytes v := by
  exact ba_e4_data_toList ba _ _ _ _

private theorem encodeU64_bytes (ba : ByteArray) (v : UInt64) :
    (Codec0.encodeU64 ba v).data.toList = ba.data.toList ++ u64Bytes v := by
  dsimp only [Codec0.encodeU64, u64Bytes]
  rw [encodeU32_bytes, encodeU32_bytes, List.append_assoc]

public theorem decodeU8_of_bytes (ba : ByteArray) (pos : Nat) (b : UInt8) (rest : List UInt8)
    (h : ba.data.toList.drop pos = b :: rest) :
    Codec0.decodeU8 ba pos = .ok b (pos + 1) := by
  rcases (Codec0Kit.drop_eq_cons_iff ba pos b rest).mpr h with ⟨hlt, hb, _⟩
  dsimp only [Codec0.decodeU8]; rw [dite_true_eq hlt, hb]

public theorem decodeU8_ok_bytes (ba : ByteArray) (pos : Nat) (b : UInt8) (pos' : Nat)
    (h : Codec0.decodeU8 ba pos = .ok b pos') :
    pos ≤ pos' ∧ pos' ≤ ba.size ∧ pos' = pos + 1 ∧ baSlice ba pos pos' = [b] := by
  dsimp only [Codec0.decodeU8] at h
  by_cases hlt : pos < ba.size
  · rw [dite_true_eq hlt] at h; cases h
    have hdrop : ba.data.toList.drop pos = (ba[pos]'hlt) :: ba.data.toList.drop (pos + 1) :=
      (Codec0Kit.drop_eq_cons_iff ba pos (ba[pos]'hlt) _).mp ⟨hlt, rfl, rfl⟩
    have hsl := (Codec0Kit.baSlice_of_drop_prefix (xs := [ba[pos]'hlt])
      (rest := ba.data.toList.drop (pos + 1)) (by simpa using hdrop)).1
    exact ⟨Nat.le_succ pos, hlt, rfl, hsl⟩
  · rw [dite_false_eq hlt] at h; cases h

public theorem decodeU32_of_bytes (ba : ByteArray) (pos : Nat) (v : UInt32) (rest : List UInt8)
    (h : ba.data.toList.drop pos = u32Bytes v ++ rest) :
    Codec0.decodeU32 ba pos = .ok v (pos + 4) := by
  dsimp only [u32Bytes] at h
  have hd1 := Codec0Kit.drop_cons_step h
  have hd2 := Codec0Kit.drop_cons_step hd1
  have hd3 := Codec0Kit.drop_cons_step hd2
  dsimp only [Codec0.decodeU32, Codec0.decodeU16]
  rw [decodeU8_of_bytes ba pos _ _ h]; dsimp only
  rw [decodeU8_of_bytes ba (pos + 1) _ _ hd1]; dsimp only
  rw [show pos + 1 + 1 = pos + 2 by omega, decodeU8_of_bytes ba (pos + 2) _ _ hd2]; dsimp only
  rw [decodeU8_of_bytes ba (pos + 3) _ _ hd3]; dsimp only
  rw [show pos + 2 + 1 + 1 = pos + 4 by omega, Codec0Kit.u32_of_u8_pack v]

public theorem decodeU32_ok_bytes (ba : ByteArray) (pos : Nat) (v : UInt32) (pos' : Nat)
    (h : Codec0.decodeU32 ba pos = .ok v pos') :
    pos ≤ pos' ∧ pos' ≤ ba.size ∧ pos' = pos + 4 ∧ baSlice ba pos pos' = u32Bytes v := by
  dsimp only [Codec0.decodeU32] at h
  codec_match lo, p1, hlo ← Codec0.decodeU16 ba pos at h
  codec_match hi, p2, hhi ← Codec0.decodeU16 ba p1 at h
  dsimp only [Codec0.decodeU16] at hlo hhi
  codec_match b0, q0, hb0 ← Codec0.decodeU8 ba pos at hlo
  obtain ⟨_, _, hq0, hs0⟩ := decodeU8_ok_bytes ba pos b0 q0 hb0; subst hq0
  codec_match b1, q1, hb1 ← Codec0.decodeU8 ba (pos + 1) at hlo
  obtain ⟨_, _, hq1, hs1⟩ := decodeU8_ok_bytes ba (pos + 1) b1 q1 hb1; subst hq1; cases hlo
  codec_match b2, q2, hb2 ← Codec0.decodeU8 ba (pos + 1 + 1) at hhi
  obtain ⟨_, _, hq2, hs2⟩ := decodeU8_ok_bytes ba (pos + 1 + 1) b2 q2 hb2; subst hq2
  codec_match b3, q3, hb3 ← Codec0.decodeU8 ba (pos + 1 + 1 + 1) at hhi
  obtain ⟨_, hlt, hq3, hs3⟩ := decodeU8_ok_bytes ba (pos + 1 + 1 + 1) b3 q3 hb3; subst hq3
  cases hhi; cases h
  refine ⟨by omega, by omega, by omega, ?_⟩
  have hs : baSlice ba pos (pos + 1 + 1 + 1 + 1) = [b0, b1, b2, b3] := by
    ba_slice_join [hs0, hs1, hs2, hs3]
  have hp := Codec0Kit.u32_pack_unpack_bytes b0 b1 b2 b3
  simpa [u32Bytes, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2] using hs

private theorem decodeU64_of_bytes (ba : ByteArray) (pos : Nat) (v : UInt64) (rest : List UInt8)
    (h : ba.data.toList.drop pos = u64Bytes v ++ rest) :
    Codec0.decodeU64 ba pos = .ok v (pos + 8) := by
  dsimp only [u64Bytes] at h; rw [List.append_assoc] at h
  have h1 : ba.data.toList.drop (pos + 4) = u32Bytes (v >>> 32).toUInt32 ++ rest := by
    rw [drop_pos_add, h]; exact List.drop_left' rfl
  dsimp only [Codec0.decodeU64]
  rw [decodeU32_of_bytes ba pos v.toUInt32 _ h]; dsimp only
  rw [decodeU32_of_bytes ba (pos + 4) (v >>> 32).toUInt32 rest h1]; dsimp only
  rw [Codec0Kit.u64_of_u32_pack v, show pos + 4 + 4 = pos + 8 by omega]

private theorem decodeU64_ok_bytes (ba : ByteArray) (pos : Nat) (v : UInt64) (pos' : Nat)
    (h : Codec0.decodeU64 ba pos = .ok v pos') :
    pos ≤ pos' ∧ pos' ≤ ba.size ∧ pos' = pos + 8 ∧ baSlice ba pos pos' = u64Bytes v := by
  dsimp only [Codec0.decodeU64] at h
  codec_match lo, p1, hlo ← Codec0.decodeU32 ba pos at h
  obtain ⟨_, _, hp1, hs1⟩ := decodeU32_ok_bytes ba pos lo p1 hlo; subst hp1
  codec_match hi, p2, hhi ← Codec0.decodeU32 ba (pos + 4) at h
  obtain ⟨_, h2s, hp2, hs2⟩ := decodeU32_ok_bytes ba (pos + 4) hi p2 hhi; subst hp2; cases h
  have hp := Codec0Kit.u64_pack_unpack_u32 lo hi
  refine ⟨by omega, h2s, by omega, ?_⟩
  have hs : baSlice ba pos (pos + 4 + 4) = u32Bytes lo ++ u32Bytes hi := by
    ba_slice_join [hs1, hs2]
  simpa [u64Bytes, hp.1, hp.2] using hs

public theorem checkHeader_of_bytes (ba : ByteArray) (rest : List UInt8)
    (h : ba.data.toList = headerBytes ++ rest) : Codec0.checkHeader ba = true := by
  have hdrop0 : ba.data.toList.drop 0 = u32Bytes 0x3042514c ++ (0x01 :: rest) := by
    rw [List.drop_zero, h]; rfl
  have hdrop4 : ba.data.toList.drop 4 = 0x01 :: rest := by rw [h]; rfl
  dsimp only [Codec0.checkHeader]
  rw [decodeU32_of_bytes ba 0 0x3042514c (0x01 :: rest) hdrop0]; dsimp only
  c0_decide_ite
  rw [decodeU8_of_bytes ba 4 0x01 rest hdrop4]; rfl

public theorem checkHeader_ok_bytes (ba : ByteArray) (h : Codec0.checkHeader ba = true) :
    5 ≤ ba.size ∧ baSlice ba 0 5 = headerBytes := by
  dsimp only [Codec0.checkHeader] at h
  codec_match magic, p1, h1 ← Codec0.decodeU32 ba 0 at h
  by_cases hm : magic = 0x3042514c
  · subst hm; c0_decide_ite_at h
    obtain ⟨_, _, hp1, hs1⟩ := decodeU32_ok_bytes ba 0 0x3042514c p1 h1; subst hp1
    codec_match ver, p2, h2 ← Codec0.decodeU8 ba 4 at h
    by_cases hv : ver = 1
    · subst hv
      obtain ⟨_, h2s, hp2, hs2⟩ := decodeU8_ok_bytes ba 4 1 p2 h2; subst hp2
      exact ⟨h2s, by ba_slice_join [hs1, hs2]⟩
    · rcases ver with ⟨⟨⟨n, _⟩⟩⟩
      match n with
      | 0 => cases h
      | 1 => exact absurd rfl hv
      | _ + 2 => cases h
  · rw [Codec0Kit.ite_false_beq hm] at h; cases h

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
  | un _ _ | bin _ _ | cmp _ _ =>
    dsimp only [Codec0.encodeOpCode0, Codec0.encodeOpCodeLow0, opBytes]
    rw [ba_e2_data_toList, ba_push_data_toList, List.append_assoc]; rfl
  | select _ => exact ba_e2_data_toList ba _ _
  | conv _ _ _ => exact ba_e4_data_toList ba _ _ _ _
  | div _ _ =>
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
  decode_enum_tag! Codec0.decodeTy0 Codec0.ty0Tag h

private theorem decodeWidth0_of_bytes (ba : ByteArray) (pos : Nat) (w : Width)
    (rest : List UInt8) (h : ba.data.toList.drop pos = Codec0.widthTag w :: rest) :
    Codec0.decodeWidth0 ba pos = .ok w (pos + 1) := by
  dsimp only [Codec0.decodeWidth0]; rw [decodeU8_of_bytes ba pos _ rest h]; cases w <;> rfl

private theorem decodeWidth0_ok_bytes (ba : ByteArray) (pos : Nat) (w : Width) (pos' : Nat)
    (h : Codec0.decodeWidth0 ba pos = .ok w pos') :
    pos ≤ pos' ∧ pos' ≤ ba.size ∧ pos' = pos + 1 ∧
      baSlice ba pos pos' = [Codec0.widthTag w] := by
  decode_enum_tag! Codec0.decodeWidth0 Codec0.widthTag h

public theorem decodeArg0_of_bytes (ba : ByteArray) (pos : Nat) (a : Arg0) (rest : List UInt8)
    (h : ba.data.toList.drop pos = argBytes a ++ rest) :
    Codec0.decodeArg0 ba pos = .ok a (pos + (argBytes a).length) := by
  cases a with
  | var idx =>
    dsimp only [argBytes] at h ⊢
    have hd1 := Codec0Kit.drop_cons_step h
    dsimp only [Codec0.decodeArg0, Codec0.decodeArgVar0]
    rw [decodeU8_of_bytes ba pos 0 _ h]; dsimp only; c0_decide_ite
    rw [decodeU32_of_bytes ba (pos + 1) idx rest hd1]; rfl
  | immBool b =>
    cases b <;> (
      dsimp only [argBytes, Codec0.decodeArg0] at h ⊢
      rw [decodeU8_of_bytes ba pos _ rest h]; rfl)
  | immBits w val =>
    dsimp only [argBytes] at h ⊢
    have hd1 := Codec0Kit.drop_cons_step h
    have hd2 := Codec0Kit.drop_cons_step hd1
    dsimp only [Codec0.decodeArg0, Codec0.decodeArgBits0]
    rw [decodeU8_of_bytes ba pos 3 _ h]; dsimp only; c0_decide_ite
    rw [decodeWidth0_of_bytes ba (pos + 1) w _ hd1]; dsimp only
    rw [show pos + 1 + 1 = pos + 2 by omega, decodeU64_of_bytes ba (pos + 2) val rest hd2]
    dsimp only [u64Bytes, u32Bytes]; rw [show pos + 2 + 8 = pos + 10 by omega]; rfl

public theorem decodeArg0_ok_bytes (ba : ByteArray) (pos : Nat) (a : Arg0) (pos' : Nat)
    (h : Codec0.decodeArg0 ba pos = .ok a pos') :
    pos ≤ pos' ∧ pos' ≤ ba.size ∧ baSlice ba pos pos' = argBytes a := by
  dsimp only [Codec0.decodeArg0] at h
  codec_match tag, p1, hu ← Codec0.decodeU8 ba pos at h
  obtain ⟨_, h1s, hp1, hs1⟩ := decodeU8_ok_bytes ba pos tag p1 hu; subst hp1
  decode_ite_chain h with (try (cases h; exact ⟨by omega, h1s, hs1⟩)) else (cases h)
  · dsimp only [Codec0.decodeArgVar0] at h
    codec_match idx, p2, hx ← Codec0.decodeU32 ba (pos + 1) at h
    obtain ⟨_, h2s, hp2, hs2⟩ := decodeU32_ok_bytes ba (pos + 1) idx p2 hx; subst hp2; cases h
    exact ⟨by omega, h2s, by ba_slice_join [hs1, hs2]⟩
  · dsimp only [Codec0.decodeArgBits0] at h
    codec_match w, p2, hw ← Codec0.decodeWidth0 ba (pos + 1) at h
    obtain ⟨_, _, hp2, hs2⟩ := decodeWidth0_ok_bytes ba (pos + 1) w p2 hw; subst hp2
    codec_match val, p3, hv ← Codec0.decodeU64 ba (pos + 1 + 1) at h
    obtain ⟨_, h3s, hp3, hs3⟩ := decodeU64_ok_bytes ba (pos + 1 + 1) val p3 hv; subst hp3; cases h
    exact ⟨by omega, h3s, by ba_slice_join [hs1, hs2, hs3]⟩

private theorem decodeOpTagTy_of_bytes {ba : ByteArray} {pos : Nat} {tag k sub : UInt8}
    {t : Ty0} {rest : List UInt8} {op : OpCode0} {f : UInt8 → Ty0 → Nat → Codec0.DecOpRes}
    (htag : tag ≤ 2) (h : ba.data.toList.drop pos = [tag, sub, Codec0.ty0Tag t] ++ rest)
    (hbranch : Codec0.decodeOpCodeLow0 ba (pos + 1) tag =
      match Codec0.decodeU8 ba (pos + 1) with
      | .none => .none
      | .ok b p1 => if k < b then .none else
        match Codec0.decodeTy0 ba p1 with
        | .none => .none
        | .ok t' p2 => f b t' p2)
    (hsub : ¬ (k < sub)) (hf : f sub t (pos + 3) = .ok op (pos + 3)) :
    Codec0.decodeOpCode0 ba pos = .ok op (pos + 3) := by
  have hd1 := Codec0Kit.drop_cons_step h
  have hd2 := Codec0Kit.drop_cons_step hd1
  dsimp only [Codec0.decodeOpCode0]
  rw [decodeU8_of_bytes ba pos tag _ (by simpa [List.append_assoc] using h)]; dsimp only
  rw [ite_true_eq htag, hbranch, decodeU8_of_bytes ba (pos + 1) sub _ hd1]; dsimp only
  rw [ite_false_eq hsub, show pos + 1 + 1 = pos + 2 by omega,
    decodeTy0_of_bytes ba (pos + 2) t rest hd2]
  exact hf

public theorem decodeOpCode0_of_bytes (ba : ByteArray) (pos : Nat) (op : OpCode0)
    (rest : List UInt8) (h : ba.data.toList.drop pos = opBytes op ++ rest) :
    Codec0.decodeOpCode0 ba pos = .ok op (pos + (opBytes op).length) := by
  cases op with
  | un o t =>
    exact decodeOpTagTy_of_bytes (by decide) h
      (by dsimp only [Codec0.decodeOpCodeLow0, Codec0.decodeOpUn0]; c0_decide_ite; rfl)
      (by cases o <;> decide) (by cases o <;> rfl)
  | bin o t =>
    exact decodeOpTagTy_of_bytes (by decide) h
      (by dsimp only [Codec0.decodeOpCodeLow0, Codec0.decodeOpBin0]; c0_decide_ite; rfl)
      (by cases o <;> decide)
      (by dsimp only [Codec0.decodeOpBinLow0, Codec0.decodeOpBinHi0]; cases o <;> rfl)
  | cmp co t =>
    exact decodeOpTagTy_of_bytes (by decide) h
      (by dsimp only [Codec0.decodeOpCodeLow0, Codec0.decodeOpCmp0]; c0_decide_ite; rfl)
      (by cases co <;> decide)
      (by dsimp only [Codec0.decodeOpCmpLow0, Codec0.decodeOpCmpHi0]; cases co <;> rfl)
  | select t =>
    have hd1 := Codec0Kit.drop_cons_step h
    dsimp only [opBytes, Codec0.decodeOpCode0, Codec0.decodeOpCodeHi0] at h ⊢
    rw [decodeU8_of_bytes ba pos 3 _ h]; dsimp only; c0_decide_ite
    rw [decodeTy0_of_bytes ba (pos + 1) t rest hd1]; rfl
  | conv c ws wd =>
    have hd1 := Codec0Kit.drop_cons_step h; have hd2 := Codec0Kit.drop_cons_step hd1
    have hd3 := Codec0Kit.drop_cons_step hd2
    dsimp only [opBytes, Codec0.decodeOpCode0, Codec0.decodeOpCodeHi0, Codec0.decodeOpConv0,
      Codec0.mkConvOp0] at h ⊢
    rw [decodeU8_of_bytes ba pos 4 _ h]; dsimp only; c0_decide_ite
    rw [decodeU8_of_bytes ba (pos + 1) (Codec0.convOp0Tag c) _ hd1]; dsimp only
    rw [ite_false_eq (by cases c <;> decide : ¬ (3 < Codec0.convOp0Tag c)),
      show pos + 1 + 1 = pos + 2 by omega, decodeWidth0_of_bytes ba (pos + 2) ws _ hd2]
    dsimp only; rw [show pos + 2 + 1 = pos + 3 by omega,
      decodeWidth0_of_bytes ba (pos + 3) wd rest hd3]; cases c <;> rfl
  | div d w =>
    have hd1 := Codec0Kit.drop_cons_step h; have hd2 := Codec0Kit.drop_cons_step hd1
    dsimp only [opBytes, Codec0.decodeOpCode0, Codec0.decodeOpCodeHi0, Codec0.decodeOpDiv0,
      Codec0.mkDivOp0] at h ⊢
    rw [decodeU8_of_bytes ba pos 5 _ h]; dsimp only; c0_decide_ite
    rw [decodeU8_of_bytes ba (pos + 1) (Codec0.divOp0Tag d) _ hd1]; dsimp only
    rw [ite_false_eq (by cases d <;> decide : ¬ (3 < Codec0.divOp0Tag d)),
      show pos + 1 + 1 = pos + 2 by omega, decodeWidth0_of_bytes ba (pos + 2) w rest hd2]
    cases d <;> rfl
  | umulw64 =>
    dsimp only [opBytes, Codec0.decodeOpCode0, Codec0.decodeOpCodeHi0] at h ⊢
    rw [decodeU8_of_bytes ba pos 6 rest h]; rfl

private theorem decodeOpU8_lt_step {ba : ByteArray} {pos : Nat} {k : UInt8}
    {f : UInt8 → Nat → Codec0.DecOpRes} {op : OpCode0} {pos' : Nat}
    (h : (match Codec0.decodeU8 ba pos with
      | .none => Codec0.DecOpRes.none
      | .ok b p1 => if k < b then Codec0.DecOpRes.none else f b p1) = .ok op pos') :
    ∃ b, b.toNat ≤ k.toNat ∧ pos + 1 ≤ ba.size ∧
      baSlice ba pos (pos + 1) = [b] ∧ f b (pos + 1) = .ok op pos' := by
  codec_match b, p1, hu ← Codec0.decodeU8 ba pos at h
  by_cases hgt : k < b
  · rw [ite_true_eq hgt] at h; cases h
  · rw [ite_false_eq hgt] at h
    obtain ⟨_, h1s, hp1, hs1⟩ := decodeU8_ok_bytes ba pos b p1 hu; subst hp1
    exact ⟨b, by c0_bv32_omega, h1s, hs1, h⟩

private theorem decodeOpTy0_ok_of_split {ba : ByteArray} {pos pos' : Nat} {k tag : UInt8}
    {op : OpCode0} {f : UInt8 → Ty0 → Nat → Codec0.DecOpRes}
    (h : (match Codec0.decodeU8 ba pos with
      | .none => Codec0.DecOpRes.none
      | .ok b p1 => if k < b then Codec0.DecOpRes.none else
        match Codec0.decodeTy0 ba p1 with
        | .none => Codec0.DecOpRes.none
        | .ok t p2 => f b t p2) = .ok op pos')
    (hsplit : ∀ b t, b.toNat ≤ k.toNat → f b t (pos + 2) = .ok op pos' →
      pos' = pos + 2 ∧ tag :: [b, Codec0.ty0Tag t] = opBytes op) :
    pos ≤ pos' ∧ pos' ≤ ba.size ∧ tag :: baSlice ba pos pos' = opBytes op := by
  obtain ⟨b, hbn, _, hs1, hf⟩ := decodeOpU8_lt_step h
  codec_match t, p2, ht ← Codec0.decodeTy0 ba (pos + 1) at hf
  obtain ⟨_, h2s, hp2, hs2⟩ := decodeTy0_ok_bytes ba (pos + 1) t p2 ht; subst hp2
  obtain ⟨rfl, hop⟩ := hsplit b t hbn (by simpa using hf)
  exact ⟨by omega, h2s, by rw [← hop]; congr 1; ba_slice_join [hs1, hs2]⟩

private theorem decodeOpU8_width1_ok {ba : ByteArray} {pos pos' : Nat} {k : UInt8}
    {f : UInt8 → Width → Nat → Codec0.DecOpRes} {op : OpCode0}
    (h : (match Codec0.decodeU8 ba pos with
      | .none => Codec0.DecOpRes.none
      | .ok b p1 => if k < b then Codec0.DecOpRes.none else
        match Codec0.decodeWidth0 ba p1 with
        | .none => Codec0.DecOpRes.none
        | .ok w p2 => f b w p2) = .ok op pos') :
    ∃ b w, b.toNat ≤ k.toNat ∧ pos + 2 ≤ ba.size ∧
      baSlice ba pos (pos + 2) = [b, Codec0.widthTag w] ∧ f b w (pos + 2) = .ok op pos' := by
  obtain ⟨b, hbn, _, hs1, hf⟩ := decodeOpU8_lt_step h
  codec_match w, p2, hw ← Codec0.decodeWidth0 ba (pos + 1) at hf
  obtain ⟨_, h2s, hp2, hs2⟩ := decodeWidth0_ok_bytes ba (pos + 1) w p2 hw; subst hp2
  exact ⟨b, w, hbn, h2s, by ba_slice_join [hs1, hs2], by simpa using hf⟩

private theorem decodeOpUn0_ok_bytes (ba : ByteArray) (pos : Nat) (op : OpCode0) (pos' : Nat)
    (h : Codec0.decodeOpUn0 ba pos = .ok op pos') :
    pos ≤ pos' ∧ pos' ≤ ba.size ∧ 0 :: baSlice ba pos pos' = opBytes op :=
  decodeOpTy0_ok_of_split (tag := 0) (f := fun b t p =>
    if b == 0 then .ok (.un .copy t) p else if b == 1 then .ok (.un .neg t) p
    else .ok (.un .not t) p) h fun _ _ hbn hf => by
    revert hf; u8_split_le hbn with (intro hf; c0_decide_ite_at hf; cases hf; exact ⟨rfl, rfl⟩)

private theorem decodeOpBin0_ok_bytes (ba : ByteArray) (pos : Nat) (op : OpCode0) (pos' : Nat)
    (h : Codec0.decodeOpBin0 ba pos = .ok op pos') :
    pos ≤ pos' ∧ pos' ≤ ba.size ∧ 1 :: baSlice ba pos pos' = opBytes op :=
  decodeOpTy0_ok_of_split (tag := 1)
    (f := fun b t p => if b <= 5 then Codec0.decodeOpBinLow0 b t p else Codec0.decodeOpBinHi0 b t p)
    h fun _ _ hbn hf => by
    dsimp only [Codec0.decodeOpBinLow0, Codec0.decodeOpBinHi0] at hf
    revert hf; u8_split_le hbn with (intro hf; c0_decide_ite_at hf; cases hf; exact ⟨rfl, rfl⟩)

private theorem decodeOpCmp0_ok_bytes (ba : ByteArray) (pos : Nat) (op : OpCode0) (pos' : Nat)
    (h : Codec0.decodeOpCmp0 ba pos = .ok op pos') :
    pos ≤ pos' ∧ pos' ≤ ba.size ∧ 2 :: baSlice ba pos pos' = opBytes op :=
  decodeOpTy0_ok_of_split (tag := 2)
    (f := fun b t p => if b <= 4 then Codec0.decodeOpCmpLow0 b t p else Codec0.decodeOpCmpHi0 b t p)
    h fun _ _ hbn hf => by
    dsimp only [Codec0.decodeOpCmpLow0, Codec0.decodeOpCmpHi0] at hf
    revert hf; u8_split_le hbn with (intro hf; c0_decide_ite_at hf; cases hf; exact ⟨rfl, rfl⟩)

private theorem decodeOpConv0_ok_bytes (ba : ByteArray) (pos : Nat) (op : OpCode0) (pos' : Nat)
    (h : Codec0.decodeOpConv0 ba pos = .ok op pos') :
    pos ≤ pos' ∧ pos' ≤ ba.size ∧ 4 :: baSlice ba pos pos' = opBytes op := by
  dsimp only [Codec0.decodeOpConv0] at h
  obtain ⟨b, ws, hbn, _, hs12, hf⟩ := decodeOpU8_width1_ok h
  codec_match wd, p3, hwd ← Codec0.decodeWidth0 ba (pos + 2) at hf
  dsimp only [Codec0.mkConvOp0] at hf
  obtain ⟨_, h3s, hp3, hs3⟩ := decodeWidth0_ok_bytes ba (pos + 2) wd p3 hwd; subst hp3
  have decB : ∃ c, op = .conv c ws wd ∧ b = Codec0.convOp0Tag c ∧ pos' = pos + 3 := by
    revert hf; u8_split_le hbn with
      (intro hf; c0_decide_ite_at hf; cases hf; exact ⟨_, rfl, rfl, rfl⟩)
  rcases decB with ⟨c, rfl, rfl, rfl⟩
  exact ⟨by omega, h3s, by dsimp only [opBytes]; congr 1; ba_slice_join [hs12, hs3]⟩

private theorem decodeOpDiv0_ok_bytes (ba : ByteArray) (pos : Nat) (op : OpCode0) (pos' : Nat)
    (h : Codec0.decodeOpDiv0 ba pos = .ok op pos') :
    pos ≤ pos' ∧ pos' ≤ ba.size ∧ 5 :: baSlice ba pos pos' = opBytes op := by
  dsimp only [Codec0.decodeOpDiv0] at h
  obtain ⟨b, w, hbn, h2s, hs12, hf⟩ := decodeOpU8_width1_ok h
  dsimp only [Codec0.mkDivOp0] at hf
  have decB : ∃ d, op = .div d w ∧ b = Codec0.divOp0Tag d ∧ pos' = pos + 2 := by
    revert hf; u8_split_le hbn with
      (intro hf; c0_decide_ite_at hf; cases hf; exact ⟨_, rfl, rfl, rfl⟩)
  rcases decB with ⟨d, rfl, rfl, rfl⟩
  exact ⟨by omega, h2s, by rw [hs12]; rfl⟩

private theorem opCode_join_tag {ba : ByteArray} {pos pos' : Nat} {tag : UInt8} {op : OpCode0}
    (hs1 : baSlice ba pos (pos + 1) = [tag])
    (hsub : pos + 1 ≤ pos' ∧ pos' ≤ ba.size ∧ tag :: baSlice ba (pos + 1) pos' = opBytes op) :
    pos ≤ pos' ∧ pos' ≤ ba.size ∧ baSlice ba pos pos' = opBytes op :=
  ⟨Nat.le_trans (Nat.le_succ pos) hsub.1, hsub.2.1, by
    rw [baSlice_trans (Nat.le_succ pos) hsub.1, hs1, List.singleton_append, hsub.2.2]⟩

public theorem decodeOpCode0_ok_bytes (ba : ByteArray) (pos : Nat) (op : OpCode0) (pos' : Nat)
    (h : Codec0.decodeOpCode0 ba pos = .ok op pos') :
    pos ≤ pos' ∧ pos' ≤ ba.size ∧ baSlice ba pos pos' = opBytes op := by
  dsimp only [Codec0.decodeOpCode0] at h
  codec_match tag, p1, hu ← Codec0.decodeU8 ba pos at h
  obtain ⟨_, h1s, hp1, hs1⟩ := decodeU8_ok_bytes ba pos tag p1 hu; subst hp1
  by_cases hle2 : tag ≤ 2
  · rw [ite_true_eq hle2] at h; dsimp only [Codec0.decodeOpCodeLow0] at h
    decode_ite_chain h with skip else
      (have ht2 : tag = 2 := by c0_bv32_omega
       subst ht2; exact opCode_join_tag hs1 (decodeOpCmp0_ok_bytes ba (pos + 1) op pos' h))
    · exact opCode_join_tag hs1 (decodeOpUn0_ok_bytes ba (pos + 1) op pos' h)
    · exact opCode_join_tag hs1 (decodeOpBin0_ok_bytes ba (pos + 1) op pos' h)
  · rw [ite_false_eq hle2] at h; dsimp only [Codec0.decodeOpCodeHi0] at h
    decode_ite_chain h with (try (cases h; exact ⟨by omega, h1s, hs1⟩)) else (cases h)
    · codec_match t, p2, ht ← Codec0.decodeTy0 ba (pos + 1) at h
      obtain ⟨_, h2s, hp2, hs2⟩ := decodeTy0_ok_bytes ba (pos + 1) t p2 ht
      subst hp2; cases h; exact ⟨by omega, h2s, by ba_slice_join [hs1, hs2]⟩
    · exact opCode_join_tag hs1 (decodeOpConv0_ok_bytes ba (pos + 1) op pos' h)
    · exact opCode_join_tag hs1 (decodeOpDiv0_ok_bytes ba (pos + 1) op pos' h)

/-! ### List Codecs (`Ty0`, `Arg0`, `Sym0`) -/

@[expose] public def tySeqBytes : List Ty0 → List UInt8
  | [] => [] | t :: rest => Codec0.ty0Tag t :: tySeqBytes rest
@[expose] public def tyListBytes (xs : List Ty0) : List UInt8 :=
  u32Bytes (UInt32.ofNat xs.length) ++ tySeqBytes xs
@[expose] public def argSeqBytes : List Arg0 → List UInt8
  | [] => [] | a :: rest => argBytes a ++ argSeqBytes rest
@[expose] public def argListBytes (xs : List Arg0) : List UInt8 :=
  u32Bytes (UInt32.ofNat xs.length) ++ argSeqBytes xs
@[expose] public def symSeqBytes : List Sym0 → List UInt8
  | [] => [] | s :: rest => u32Bytes s ++ symSeqBytes rest
@[expose] public def symListBytes (xs : List Sym0) : List UInt8 :=
  u32Bytes (UInt32.ofNat xs.length) ++ symSeqBytes xs

public theorem u32Bytes_length (v : UInt32) : (u32Bytes v).length = 4 := rfl

public theorem u32_sub1_toNat {rem : UInt32} {n : Nat} (h : rem.toNat = n + 1) :
    rem ≠ 0 ∧ (rem - 1).toNat = n :=
  Codec0Kit.u32_sub1_toNat h

public theorem u32_ofNat_eq {n : Nat} {c : UInt32} (h : n = c.toNat) : UInt32.ofNat n = c :=
  Codec0Kit.u32_ofNat_eq h

private theorem ok_drop_triv {P1 P2 P3 P5 : Prop} {α : Type} {xs : List α}
    (h : P1 ∧ P2 ∧ P3 ∧ (∀ x ∈ xs, True) ∧ P5) : P1 ∧ P2 ∧ P3 ∧ P5 :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2⟩

public section
macro "c0_encode_list!" encList:term:arg encLoop:term:arg encElem:term:arg lenFn:term:arg
    elemB:term:arg seqB:term:arg listB:term:arg hElem:term:arg : tactic =>
  `(tactic| exact Codec0Kit.encodeList_bytes_of_steps $encList $encLoop Codec0.encodeU32 $lenFn
    u32Bytes $seqB $listB (fun _ _ => rfl)
    (Codec0Kit.encodeListLoop_bytes_of_steps $encLoop $encElem $elemB $seqB
      (fun _ => rfl) (fun _ _ _ => rfl) $hElem rfl (fun _ _ => rfl))
    encodeU32_bytes (Codec0Kit.lenU32_eq_of_steps $lenFn (fun _ => rfl) (fun _ _ _ => rfl))
    (fun _ => rfl) _ _)

macro "c0_decode_list_of!" mkOk:term:arg decList:ident decLoop:ident decElem:term:arg
    revFn:term:arg elemB:term:arg seqB:term:arg listB:term:arg elemOk:term:arg
    hDec:term:arg hBx:term:arg : tactic =>
  `(tactic| exact Codec0Kit.decodeList_of_bytes_of_steps $mkOk $decList $decLoop
    (fun b p v p' => Codec0.decodeU32 b p = .ok v p') u32Bytes $seqB $listB $elemOk
    (fun _ _ _ hv => by unfold $decList; rw [hv]) decodeU32_of_bytes
    (Codec0Kit.decodeListLoop_of_bytes_of_steps $mkOk $decLoop
      (fun b p v p' => $decElem b p = .ok v p') $revFn $elemB $seqB $elemOk
      (fun _ _ _ => by unfold $decLoop; rw [Codec0Kit.dite_true_eq rfl])
      (fun _ _ _ _ _ _ hne hx => by
        conv => lhs; unfold $decLoop; rw [Codec0Kit.dite_false_eq hne, hx])
      (Codec0Kit.revList_eq_of_steps $revFn (fun _ => rfl) (fun _ _ _ => rfl))
      rfl (fun _ _ => rfl) $hDec)
    u32Bytes_length (fun _ => rfl) _ _ _ _ ‹_› $hBx ‹_›)

macro "c0_decode_list_ok!" mkOk:term:arg decList:ident decLoop:ident decElem:term:arg
    revFn:term:arg elemB:term:arg seqB:term:arg listB:term:arg elemOk:term:arg
    hElemOk:term:arg : tactic =>
  `(tactic| exact Codec0Kit.decodeList_ok_bytes_of_steps $mkOk $decList $decLoop
    (fun b p v p' => Codec0.decodeU32 b p = .ok v p') u32Bytes $seqB $listB $elemOk
    (fun b p _ _ hdec => by
      unfold $decList at hdec
      codec_match cnt, p1, hu ← Codec0.decodeU32 b p at hdec
      exact ⟨cnt, p1, rfl, hdec⟩)
    decodeU32_ok_bytes
    (Codec0Kit.decodeListLoop_ok_bytes_of_steps $mkOk $decLoop $revFn $elemB $seqB $elemOk
      (fun _ _ _ _ _ h0 => by
        unfold $decLoop at h0; rw [Codec0Kit.dite_true_eq rfl] at h0; cases h0; exact ⟨rfl, rfl⟩)
      (fun b p _ _ _ _ hne h1 => by
        unfold $decLoop at h1; rw [Codec0Kit.dite_false_eq hne] at h1
        codec_match x, p1, hx ← $decElem b p at h1
        have hElem : ∀ (b : ByteArray) (p : Nat) x (p1 : Nat), $decElem b p = .ok x p1 →
            p ≤ p1 ∧ p1 ≤ b.size ∧ ($elemOk) x ∧ baSlice b p p1 = ($elemB) x := $hElemOk
        have hok := hElem b p x p1 hx
        exact ⟨x, p1, hok.1, fun _ => hok.2.1, hok.2.2.1, hok.2.2.2, h1⟩)
      (Codec0Kit.revList_eq_of_steps $revFn (fun _ => rfl) (fun _ _ _ => rfl))
      rfl (fun _ _ => rfl))
    (fun _ => rfl) _ _ _ _ ‹_›)
end

private theorem drop_triv_head {P1 P2 P3 P5 : Prop} {α : Type} {xs : List α} :
    (P1 ∧ P2 ∧ P3 ∧ (∀ x ∈ xs, True) ∧ P5) → P1 ∧ P2 ∧ P3 ∧ P5 := ok_drop_triv

public theorem encodeTyList0_bytes (ba : ByteArray) (xs : List Ty0) :
    (Codec0.encodeTyList0 ba xs).data.toList = ba.data.toList ++ tyListBytes xs := by
  c0_encode_list! Codec0.encodeTyList0 Codec0.encodeTyListLoop0 Codec0.encodeTy0
    Codec0.lenTysU32 (fun t => [Codec0.ty0Tag t]) tySeqBytes tyListBytes encodeTy0_bytes

public theorem encodeArgList0_bytes (ba : ByteArray) (xs : List Arg0) :
    (Codec0.encodeArgList0 ba xs).data.toList = ba.data.toList ++ argListBytes xs := by
  c0_encode_list! Codec0.encodeArgList0 Codec0.encodeArgListLoop0 Codec0.encodeArg0
    Codec0.lenArgsU32 argBytes argSeqBytes argListBytes encodeArg0_bytes

public theorem encodeSymList0_bytes (ba : ByteArray) (xs : List Sym0) :
    (Codec0.encodeSymList0 ba xs).data.toList = ba.data.toList ++ symListBytes xs := by
  c0_encode_list! Codec0.encodeSymList0 Codec0.encodeSymListLoop0 Codec0.encodeU32
    Codec0.lenSymsU32 u32Bytes symSeqBytes symListBytes encodeU32_bytes

public theorem decodeTyList0_of_bytes (ba : ByteArray) (pos : Nat) (xs : List Ty0)
    (rest : List UInt8) (hb : xs.length < 2 ^ 32)
    (h : ba.data.toList.drop pos = tyListBytes xs ++ rest) :
    Codec0.decodeTyList0 ba pos = .ok xs (pos + (tyListBytes xs).length) := by
  c0_decode_list_of! Codec0.DecTysRes.ok Codec0.decodeTyList0 Codec0.decodeTyListLoop0
    Codec0.decodeTy0 Codec0.revTys0 (fun t => [Codec0.ty0Tag t]) tySeqBytes tyListBytes
    (fun _ => True) (fun b p t r _ hr => decodeTy0_of_bytes b p t r hr) (fun _ _ => trivial)

public theorem decodeTyList0_ok_bytes (ba : ByteArray) (pos : Nat) (xs : List Ty0) (pos' : Nat)
    (h : Codec0.decodeTyList0 ba pos = .ok xs pos') :
    pos ≤ pos' ∧ pos' ≤ ba.size ∧ xs.length < 2 ^ 32 ∧ baSlice ba pos pos' = tyListBytes xs := by
  apply drop_triv_head
  c0_decode_list_ok! Codec0.DecTysRes.ok Codec0.decodeTyList0 Codec0.decodeTyListLoop0
    Codec0.decodeTy0 Codec0.revTys0 (fun t => [Codec0.ty0Tag t]) tySeqBytes tyListBytes
    (fun _ => True)
    (fun b p t p1 ht => let k := decodeTy0_ok_bytes b p t p1 ht; ⟨k.1, k.2.1, trivial, k.2.2.2⟩)

public theorem decodeArgList0_of_bytes (ba : ByteArray) (pos : Nat) (xs : List Arg0)
    (rest : List UInt8) (hb : xs.length < 2 ^ 32)
    (h : ba.data.toList.drop pos = argListBytes xs ++ rest) :
    Codec0.decodeArgList0 ba pos = .ok xs (pos + (argListBytes xs).length) := by
  c0_decode_list_of! Codec0.DecArgsRes.ok Codec0.decodeArgList0 Codec0.decodeArgListLoop0
    Codec0.decodeArg0 Codec0.revArgs0 argBytes argSeqBytes argListBytes (fun _ => True)
    (fun b p a r _ hr => decodeArg0_of_bytes b p a r hr) (fun _ _ => trivial)

public theorem decodeArgList0_ok_bytes (ba : ByteArray) (pos : Nat) (xs : List Arg0) (pos' : Nat)
    (h : Codec0.decodeArgList0 ba pos = .ok xs pos') :
    pos ≤ pos' ∧ pos' ≤ ba.size ∧ xs.length < 2 ^ 32 ∧ baSlice ba pos pos' = argListBytes xs := by
  apply drop_triv_head
  c0_decode_list_ok! Codec0.DecArgsRes.ok Codec0.decodeArgList0 Codec0.decodeArgListLoop0
    Codec0.decodeArg0 Codec0.revArgs0 argBytes argSeqBytes argListBytes (fun _ => True)
    (fun b p a p1 ha => let k := decodeArg0_ok_bytes b p a p1 ha; ⟨k.1, k.2.1, trivial, k.2.2⟩)

public theorem decodeSymList0_of_bytes (ba : ByteArray) (pos : Nat) (xs : List Sym0)
    (rest : List UInt8) (hb : xs.length < 2 ^ 32)
    (h : ba.data.toList.drop pos = symListBytes xs ++ rest) :
    Codec0.decodeSymList0 ba pos = .ok xs (pos + (symListBytes xs).length) := by
  c0_decode_list_of! Codec0.DecSymsRes.ok Codec0.decodeSymList0 Codec0.decodeSymListLoop0
    Codec0.decodeU32 Codec0.revSyms0 u32Bytes symSeqBytes symListBytes (fun _ => True)
    (fun b p s r _ hr => decodeU32_of_bytes b p s r hr) (fun _ _ => trivial)

public theorem decodeSymList0_ok_bytes (ba : ByteArray) (pos : Nat) (xs : List Sym0) (pos' : Nat)
    (h : Codec0.decodeSymList0 ba pos = .ok xs pos') :
    pos ≤ pos' ∧ pos' ≤ ba.size ∧ xs.length < 2 ^ 32 ∧ baSlice ba pos pos' = symListBytes xs := by
  apply drop_triv_head
  c0_decode_list_ok! Codec0.DecSymsRes.ok Codec0.decodeSymList0 Codec0.decodeSymListLoop0
    Codec0.decodeU32 Codec0.revSyms0 u32Bytes symSeqBytes symListBytes (fun _ => True)
    (fun b p s p1 hs => let k := decodeU32_ok_bytes b p s p1 hs; ⟨k.1, k.2.1, trivial, k.2.2.2⟩)

end Codec0Spec

end LeanQbe.T.Bootstrap0
