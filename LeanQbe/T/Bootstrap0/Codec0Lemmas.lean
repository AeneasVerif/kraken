module

public import LeanQbe.T.Bootstrap0.Codec0
public import LeanQbe.T.Bootstrap0.Codec0Lemmas1

/-!
# Verified Round-Trip, Determinism, and Injectivity Proofs for `Codec0`

Proves that `Codec0`'s iterative `LQB0` binary encoder (`encodeMod0`) and decoder (`decodeMod0`)
form an exact canonical bijection on `Mod0Bounded` `TFlatModule0`s:

* `decodeMod0_encodeMod0`: `Mod0Bounded m → decodeMod0 (encodeMod0 m) = some m`.
* `encodeMod0_decodeMod0`: `decodeMod0 ba = some m → encodeMod0 m = ba`.
* `decodeMod0_some_bounded`: `decodeMod0 ba = some m → Mod0Bounded m`.
* `encodeMod0_inj` / `decodeMod0_inj` / `decodeMod0_encodeMod0_iff`: injectivity, determinism,
  and canonical uniqueness (`0` sorry, `[propext, Classical.choice, Quot.sound]`, M1 `.olean`
  hygienic).
-/

set_option autoImplicit false

namespace LeanQbe.T.Bootstrap0

open Codec0Spec

/-! ## 4. Iterative `TFlat0` Encoder & Decoder Specifications -/

mutual
private def tflatBytes : TFlat0 → List UInt8
  | .let1 op args k => 0 :: opBytes op ++ argListBytes args ++ tflatBytes k
  | .let2Umulw64 a b k => 1 :: argBytes a ++ argBytes b ++ tflatBytes k
  | .load t addr k => 2 :: Codec0.ty0Tag t :: argBytes addr ++ tflatBytes k
  | .store t val addr k =>
    3 :: Codec0.ty0Tag t :: argBytes val ++ argBytes addr ++ tflatBytes k
  | .call fnSym as bs args k =>
    4 :: u32Bytes fnSym ++ tyListBytes as ++ tyListBytes bs ++ argListBytes args ++ tflatBytes k
  | .tailCall fnSym as args => 5 :: u32Bytes fnSym ++ tyListBytes as ++ argListBytes args
  | .jnz c t e => 6 :: argBytes c ++ tflatBytes t ++ tflatBytes e
  | .jump j args => 7 :: u32Bytes j ++ argListBytes args
  | .ret vs => 8 :: argListBytes vs
  | .exit fnSym as args => 9 :: u32Bytes fnSym ++ tyListBytes as ++ argListBytes args
  | .hlt => [10]
  | .group bodies k =>
    11 :: u32Bytes (UInt32.ofNat bodies.length) ++ blocksBytes bodies ++ tflatBytes k

private def blocksBytes : List (List Ty0 × TFlat0) → List UInt8
  | [] => []
  | (ts, b) :: rest => tyListBytes ts ++ tflatBytes b ++ blocksBytes rest
end

private def encWorkBytes : List Codec0.EncItem0 → List UInt8
  | [] => []
  | .node t :: rest => tflatBytes t ++ encWorkBytes rest
  | .blocks bs :: rest => blocksBytes bs ++ encWorkBytes rest

private theorem lenBlocksU32_eq (xs : List (List Ty0 × TFlat0)) (acc : UInt32) :
    Codec0.lenBlocksU32 xs acc = acc + UInt32.ofNat xs.length := by
  induction xs generalizing acc with
  | nil => exact (UInt32.add_zero acc).symm
  | cons _ rest ih =>
    dsimp only [Codec0.lenBlocksU32]
    rw [ih (acc + 1), List.length_cons, Nat.add_comm, UInt32.ofNat_add, UInt32.add_assoc]; rfl

private theorem encodeLinearHdr0_bytes (ba : ByteArray) (t : TFlat0) :
    (Codec0.encodeLinearHdr0 ba t).data.toList =
      ba.data.toList ++
        match t with
        | .let1 op args _ => 0 :: opBytes op ++ argListBytes args
        | .let2Umulw64 a b _ => 1 :: argBytes a ++ argBytes b
        | .load ty addr _ => 2 :: Codec0.ty0Tag ty :: argBytes addr
        | .store ty val addr _ => 3 :: Codec0.ty0Tag ty :: argBytes val ++ argBytes addr
        | .call f as bs args _ =>
          4 :: u32Bytes f ++ tyListBytes as ++ tyListBytes bs ++ argListBytes args
        | .tailCall f as args => 5 :: u32Bytes f ++ tyListBytes as ++ argListBytes args
        | .jnz c _ _ => 6 :: argBytes c
        | .jump j args => 7 :: u32Bytes j ++ argListBytes args
        | .ret vs => 8 :: argListBytes vs
        | .exit f as args => 9 :: u32Bytes f ++ tyListBytes as ++ argListBytes args
        | .hlt => [10]
        | .group bodies _ => 11 :: u32Bytes (UInt32.ofNat bodies.length) := by
  cases t with
  | let1 op args _ =>
    dsimp only [Codec0.encodeLinearHdr0, Codec0.encodeLet1Hdr0]
    rw [encodeArgList0_bytes, encodeOpCode0_bytes, ba_push_data_toList]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  | let2Umulw64 a b _ =>
    dsimp only [Codec0.encodeLinearHdr0]
    rw [encodeArg0_bytes, encodeArg0_bytes, ba_push_data_toList]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  | load ty addr _ =>
    dsimp only [Codec0.encodeLinearHdr0]
    rw [encodeArg0_bytes, encodeTy0_bytes, ba_push_data_toList]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  | store ty val addr _ =>
    dsimp only [Codec0.encodeLinearHdr0, Codec0.encodeStoreHdr0]
    rw [encodeArg0_bytes, encodeArg0_bytes, encodeTy0_bytes, ba_push_data_toList]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  | call f as bs args _ =>
    dsimp only [Codec0.encodeLinearHdr0, Codec0.encodeCallHdr0]
    rw [encodeArgList0_bytes, encodeTyList0_bytes, encodeTyList0_bytes, encodeU32_bytes,
      ba_push_data_toList]; simp only [List.append_assoc, List.cons_append, List.nil_append]
  | tailCall f as args =>
    dsimp only [Codec0.encodeLinearHdr0, Codec0.encodeLeafNode0, Codec0.encodeSigArgs0]
    rw [encodeArgList0_bytes, encodeTyList0_bytes, encodeU32_bytes, ba_push_data_toList]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  | jnz c _ _ =>
    dsimp only [Codec0.encodeLinearHdr0]; rw [encodeArg0_bytes, ba_push_data_toList]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  | jump j args =>
    dsimp only [Codec0.encodeLinearHdr0, Codec0.encodeLeafNode0]
    rw [encodeArgList0_bytes, encodeU32_bytes, ba_push_data_toList]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  | ret vs =>
    dsimp only [Codec0.encodeLinearHdr0, Codec0.encodeLeafNode0]
    rw [encodeArgList0_bytes, ba_push_data_toList]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  | exit f as args =>
    dsimp only [Codec0.encodeLinearHdr0, Codec0.encodeLeafNode0, Codec0.encodeSigArgs0]
    rw [encodeArgList0_bytes, encodeTyList0_bytes, encodeU32_bytes, ba_push_data_toList]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  | hlt => exact ba_push_data_toList ba 10
  | group bodies _ =>
    dsimp only [Codec0.encodeLinearHdr0]
    rw [encodeU32_bytes, ba_push_data_toList, lenBlocksU32_eq, UInt32.zero_add]
    simp only [List.append_assoc, List.cons_append, List.nil_append]

private theorem pushEncChildren0_lt (t : TFlat0) (rest : List Codec0.EncItem0) :
    Codec0.encWorkWeight (Codec0.pushEncChildren0 t rest) <
      Codec0.tflatWeight t + Codec0.encWorkWeight rest := by
  cases t <;> dsimp only [Codec0.pushEncChildren0, Codec0.pushEncLinChildren0,
    Codec0.encWorkWeight, Codec0.tflatWeight] <;> omega

private theorem encodeWorkStep0_lt (ba : ByteArray) (item : Codec0.EncItem0)
    (rest : List Codec0.EncItem0) :
    Codec0.encWorkWeight (Codec0.encodeWorkStep0 ba item rest).2 <
      Codec0.encWorkWeight (item :: rest) := by
  cases item with
  | blocks bs =>
    cases bs with
    | nil =>
      dsimp only [Codec0.encodeWorkStep0, Codec0.encodeBlocksStep0, Codec0.encWorkWeight,
        Codec0.blocksWeight]; omega
    | cons _ _ =>
      dsimp only [Codec0.encodeWorkStep0, Codec0.encodeBlocksStep0, Codec0.mkBlockCont0,
        Codec0.encWorkWeight, Codec0.blocksWeight]; omega
  | node t =>
    dsimp only [Codec0.encodeWorkStep0, Codec0.encWorkWeight]; exact pushEncChildren0_lt t rest

private theorem encodeTFlatWork0_bytes_aux :
    ∀ (w : Nat) (work : List Codec0.EncItem0) (ba : ByteArray),
      Codec0.encWorkWeight work = w →
      (Codec0.encodeTFlatWork0 ba work).data.toList = ba.data.toList ++ encWorkBytes work
  | _, [], ba, _ => by
    unfold Codec0.encodeTFlatWork0; dsimp only [encWorkBytes]; rw [List.append_nil]
  | w, item :: rest, ba, hw => by
    unfold Codec0.encodeTFlatWork0
    have hlt : Codec0.encWorkWeight (Codec0.encodeWorkStep0 ba item rest).2 < w := by
      rw [← hw]; exact encodeWorkStep0_lt ba item rest
    have ih := encodeTFlatWork0_bytes_aux
      (Codec0.encWorkWeight (Codec0.encodeWorkStep0 ba item rest).2)
      (Codec0.encodeWorkStep0 ba item rest).2 (Codec0.encodeWorkStep0 ba item rest).1 rfl
    rw [ih]
    cases item with
    | blocks bs =>
      cases bs with
      | nil => rfl
      | cons hd _ =>
        rcases hd with ⟨ts, b⟩
        dsimp only [Codec0.encodeWorkStep0, Codec0.encodeBlocksStep0, Codec0.mkBlockCont0,
          encWorkBytes, blocksBytes]
        rw [encodeTyList0_bytes, List.append_assoc, List.append_assoc, List.append_assoc]
    | node t =>
      dsimp only [Codec0.encodeWorkStep0, encWorkBytes]; rw [encodeLinearHdr0_bytes]
      cases t <;> (
        dsimp only [Codec0.pushEncChildren0, Codec0.pushEncLinChildren0, encWorkBytes, tflatBytes]
        simp only [List.append_assoc])
termination_by w => w

private theorem encodeTFlat0_bytes (ba : ByteArray) (t : TFlat0) :
    (Codec0.encodeTFlat0 ba t).data.toList = ba.data.toList ++ tflatBytes t := by
  dsimp only [Codec0.encodeTFlat0]
  rw [encodeTFlatWork0_bytes_aux (Codec0.encWorkWeight [.node t]) [.node t] ba rfl]
  dsimp only [encWorkBytes]; rw [List.append_nil]

mutual
private theorem tflatNodes_le_bytes_length : ∀ t, tflatNodes t ≤ (tflatBytes t).length
  | .let1 _ _ k | .let2Umulw64 _ _ k | .load _ _ k | .store _ _ _ k | .call _ _ _ _ k => by
    dsimp only [tflatNodes, tflatBytes]; have hk := tflatNodes_le_bytes_length k
    simp only [List.length_append, List.length_cons] at *; omega
  | .tailCall _ _ _ | .jump _ _ | .ret _ | .exit _ _ _ | .hlt => by
    dsimp only [tflatNodes, tflatBytes]
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  | .jnz _ t e => by
    dsimp only [tflatNodes, tflatBytes]
    have ht := tflatNodes_le_bytes_length t; have he := tflatNodes_le_bytes_length e
    simp only [List.length_append, List.length_cons]; omega
  | .group bodies k => by
    dsimp only [tflatNodes, tflatBytes]
    have hb := blocksNodes_le_bytes_length bodies; have hk := tflatNodes_le_bytes_length k
    simp only [List.length_append, List.length_cons]; omega

private theorem blocksNodes_le_bytes_length : ∀ bs, blocksNodes bs ≤ (blocksBytes bs).length
  | [] => by dsimp only [blocksNodes, blocksBytes]; omega
  | (_, b) :: rest => by
    dsimp only [blocksNodes, blocksBytes]
    have hb := tflatNodes_le_bytes_length b; have hr := blocksNodes_le_bytes_length rest
    simp only [List.length_append]; omega
end

/-! ### Forward `TFlat0` Decoder Proof (`decodeTFlat0_of_bytes`) -/

private theorem revBlocks0_eq (xs acc : List (List Ty0 × TFlat0)) :
    Codec0.revBlocks0 xs acc = xs.reverse ++ acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x rest ih =>
    dsimp only [Codec0.revBlocks0]; rw [ih, List.reverse_cons, List.append_assoc]; rfl

private theorem u32_sub_ofNat {a b : Nat} (ha : a ≤ 0xffffffff) (hba : b ≤ a) :
    UInt32.ofNat a - UInt32.ofNat b = UInt32.ofNat (a - b) := by
  apply UInt32.eq_of_toBitVec_eq; apply BitVec.eq_of_toNat_eq
  have ha' : (UInt32.ofNat a).toNat = a := by
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  have hb' : (UInt32.ofNat b).toNat = b := by
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  have hle : UInt32.ofNat b ≤ UInt32.ofNat a := by
    change (UInt32.ofNat b).toNat ≤ (UInt32.ofNat a).toNat; rw [ha', hb']; exact hba
  change (UInt32.ofNat a - UInt32.ofNat b).toNat = (UInt32.ofNat (a - b)).toNat
  rw [UInt32.toNat_sub_of_le _ _ hle, ha', hb', UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]

private theorem u32_sub1_ge {fuel : UInt32} {n : Nat} (h : 1 + n ≤ fuel.toNat) :
    n ≤ (fuel - 1).toNat := by
  have h1 : (1 : UInt32) ≤ fuel := by change 1 ≤ fuel.toNat; omega
  have h1n : (1 : UInt32).toNat = 1 := rfl
  rw [UInt32.toNat_sub_of_le fuel 1 h1, h1n]; omega

private theorem u32_sub1_sub {fuel : UInt32} {n : Nat} (h : 1 + n ≤ fuel.toNat) :
    fuel - 1 - UInt32.ofNat n = fuel - UInt32.ofNat (1 + n) := by
  have hf_lt := fuel.toNat_lt
  rw [show fuel = UInt32.ofNat fuel.toNat from UInt32.ofNat_toNat.symm,
    show (1 : UInt32) = UInt32.ofNat 1 from rfl,
    u32_sub_ofNat (by omega) (by omega), u32_sub_ofNat (by omega) (by omega),
    u32_sub_ofNat (by omega) (by omega)]
  congr 1; omega

private def frameApplyResult (ba : ByteArray) (pos : Nat) (t : TFlat0)
    (frames : List Codec0.DecFrame0) (fuel : UInt32) : Codec0.DecTFlatRes :=
  match Codec0.decodeApplyFrames0 ba pos t frames with
  | .none => .none | .done res pos2 => .ok res pos2
  | .cont pos2 frames' =>
    Codec0.decodeTFlatLoop0 (fuel - UInt32.ofNat (tflatNodes t)) ba pos2 frames'

private theorem tflatNodes_pos (t : TFlat0) : 1 ≤ tflatNodes t := by
  cases t <;> dsimp only [tflatNodes] <;> omega

private theorem decodeTFlatLoop0_step (fuel : UInt32) (hf : fuel ≠ 0) (ba : ByteArray)
    (pos : Nat) (frames : List Codec0.DecFrame0) :
    Codec0.decodeTFlatLoop0 fuel ba pos frames =
      match Codec0.stepLoopFrame0 ba (Codec0.decodeNodeStep0 ba pos) frames with
      | .none => .none | .done res pos2 => .ok res pos2
      | .cont pos2 frames' => Codec0.decodeTFlatLoop0 (fuel - 1) ba pos2 frames' := by
  conv => lhs; unfold Codec0.decodeTFlatLoop0; rw [dite_false_eq hf]
  rfl

mutual
private theorem decodeTFlatLoop0_of_bytes :
    ∀ (t : TFlat0) (ba : ByteArray) (pos : Nat) (frames : List Codec0.DecFrame0)
      (rest : List UInt8) (fuel : UInt32),
      TFlat0ListBounded t → tflatNodes t ≤ fuel.toNat →
      ba.data.toList.drop pos = tflatBytes t ++ rest →
      Codec0.decodeTFlatLoop0 fuel ba pos frames =
        frameApplyResult ba (pos + (tflatBytes t).length) t frames fuel
  | .let1 op args k, ba, pos, frames, rest, fuel, hb, hfuel, hdrop => by
    dsimp only [TFlat0ListBounded, tflatNodes, tflatBytes] at hb hfuel hdrop ⊢
    have hf0 : fuel ≠ 0 := fun hz => by subst hz; simp at hfuel
    have hd1 : ba.data.toList.drop (pos + 1) =
        opBytes op ++ (argListBytes args ++ (tflatBytes k ++ rest)) := by
      rw [drop_pos_add, hdrop]; simp [List.append_assoc]
    have hd2 : ba.data.toList.drop (pos + 1 + (opBytes op).length) =
        argListBytes args ++ (tflatBytes k ++ rest) := by rw [drop_pos_add, hd1, List.drop_left]
    have hd3 : ba.data.toList.drop (pos + 1 + (opBytes op).length + (argListBytes args).length) =
        tflatBytes k ++ rest := by rw [drop_pos_add, hd2, List.drop_left]
    have hstep : Codec0.decodeNodeStep0 ba pos =
        .push (pos + 1 + (opBytes op).length + (argListBytes args).length) (.let1 op args) := by
      dsimp only [Codec0.decodeNodeStep0, Codec0.decodeLinLowStep0, Codec0.decodeLet1Step0,
        Codec0.finishLet1Step0, Codec0.mkLet1Step0]
      rw [decodeU8_of_bytes ba pos 0 _ (by simpa [List.append_assoc] using hdrop)]; dsimp only
      rw [ite_true_eq (by decide : ((0 : UInt8) ≤ 3)),
        ite_true_eq (by decide : ((0 : UInt8) == 0) = true),
        decodeOpCode0_of_bytes ba (pos + 1) op _ hd1]; dsimp only
      rw [decodeArgList0_of_bytes ba (pos + 1 + (opBytes op).length) args _ hb.1 hd2]
    rw [decodeTFlatLoop0_step fuel hf0 ba pos frames, hstep]; dsimp only [Codec0.stepLoopFrame0]
    rw [decodeTFlatLoop0_of_bytes k ba _ (.let1 op args :: frames) rest (fuel - 1) hb.2
      (u32_sub1_ge hfuel) hd3]
    dsimp only [frameApplyResult, Codec0.decodeApplyFrames0, Codec0.applyLinFrame0,
      Codec0.applyLinLowFrame0, tflatNodes]
    rw [show pos + 1 + (opBytes op).length + (argListBytes args).length + (tflatBytes k).length =
        pos + (0 :: opBytes op ++ argListBytes args ++ tflatBytes k).length by
      simp only [List.length_cons, List.length_append]; omega, u32_sub1_sub hfuel]
  | .let2Umulw64 a b k, ba, pos, frames, rest, fuel, hb, hfuel, hdrop => by
    dsimp only [TFlat0ListBounded, tflatNodes, tflatBytes] at hb hfuel hdrop ⊢
    have hf0 : fuel ≠ 0 := fun hz => by subst hz; simp at hfuel
    have hd1 : ba.data.toList.drop (pos + 1) =
        argBytes a ++ (argBytes b ++ (tflatBytes k ++ rest)) := by
      rw [drop_pos_add, hdrop]; simp [List.append_assoc]
    have hd2 : ba.data.toList.drop (pos + 1 + (argBytes a).length) =
        argBytes b ++ (tflatBytes k ++ rest) := by rw [drop_pos_add, hd1, List.drop_left]
    have hd3 : ba.data.toList.drop (pos + 1 + (argBytes a).length + (argBytes b).length) =
        tflatBytes k ++ rest := by rw [drop_pos_add, hd2, List.drop_left]
    have hstep : Codec0.decodeNodeStep0 ba pos =
        .push (pos + 1 + (argBytes a).length + (argBytes b).length) (.let2Umulw64 a b) := by
      dsimp only [Codec0.decodeNodeStep0, Codec0.decodeLinLowStep0, Codec0.decodeLet2Step0]
      rw [decodeU8_of_bytes ba pos 1 _ (by simpa [List.append_assoc] using hdrop)]; dsimp only
      rw [ite_true_eq (by decide : ((1 : UInt8) ≤ 3)),
        ite_false_eq (by decide : ¬ ((1 : UInt8) == 0) = true),
        ite_true_eq (by decide : ((1 : UInt8) == 1) = true),
        decodeArg0_of_bytes ba (pos + 1) a _ hd1]; dsimp only
      rw [decodeArg0_of_bytes ba (pos + 1 + (argBytes a).length) b _ hd2]
    rw [decodeTFlatLoop0_step fuel hf0 ba pos frames, hstep]; dsimp only [Codec0.stepLoopFrame0]
    rw [decodeTFlatLoop0_of_bytes k ba _ (.let2Umulw64 a b :: frames) rest (fuel - 1) hb
      (u32_sub1_ge hfuel) hd3]
    dsimp only [frameApplyResult, Codec0.decodeApplyFrames0, Codec0.applyLinFrame0,
      Codec0.applyLinLowFrame0, tflatNodes]
    rw [show pos + 1 + (argBytes a).length + (argBytes b).length + (tflatBytes k).length =
        pos + (1 :: argBytes a ++ argBytes b ++ tflatBytes k).length by
      simp only [List.length_cons, List.length_append]; omega, u32_sub1_sub hfuel]
  | .load ty addr k, ba, pos, frames, rest, fuel, hb, hfuel, hdrop => by
    dsimp only [TFlat0ListBounded, tflatNodes, tflatBytes] at hb hfuel hdrop ⊢
    have hf0 : fuel ≠ 0 := fun hz => by subst hz; simp at hfuel
    have hd1 : ba.data.toList.drop (pos + 1) = Codec0.ty0Tag ty :: (argBytes addr ++
        (tflatBytes k ++ rest)) := by rw [drop_pos_add, hdrop]; simp [List.append_assoc]
    have hd2 : ba.data.toList.drop (pos + 2) = argBytes addr ++ (tflatBytes k ++ rest) := by
      rw [show pos + 2 = (pos + 1) + 1 by omega, drop_pos_add, hd1]; rfl
    have hd3 : ba.data.toList.drop (pos + 2 + (argBytes addr).length) = tflatBytes k ++ rest := by
      rw [drop_pos_add, hd2, List.drop_left]
    have hstep : Codec0.decodeNodeStep0 ba pos =
        .push (pos + 2 + (argBytes addr).length) (.load ty addr) := by
      dsimp only [Codec0.decodeNodeStep0, Codec0.decodeLinLowStep0, Codec0.decodeLoadStep0]
      rw [decodeU8_of_bytes ba pos 2 _ (by simpa [List.append_assoc] using hdrop)]; dsimp only
      rw [ite_true_eq (by decide : ((2 : UInt8) ≤ 3)),
        ite_false_eq (by decide : ¬ ((2 : UInt8) == 0) = true),
        ite_false_eq (by decide : ¬ ((2 : UInt8) == 1) = true),
        ite_true_eq (by decide : ((2 : UInt8) == 2) = true),
        decodeTy0_of_bytes ba (pos + 1) ty _ hd1]; dsimp only
      rw [show pos + 1 + 1 = pos + 2 by omega, decodeArg0_of_bytes ba (pos + 2) addr _ hd2]
    rw [decodeTFlatLoop0_step fuel hf0 ba pos frames, hstep]; dsimp only [Codec0.stepLoopFrame0]
    rw [decodeTFlatLoop0_of_bytes k ba _ (.load ty addr :: frames) rest (fuel - 1) hb
      (u32_sub1_ge hfuel) hd3]
    dsimp only [frameApplyResult, Codec0.decodeApplyFrames0, Codec0.applyLinFrame0,
      Codec0.applyLinLowFrame0, tflatNodes]
    rw [show pos + 2 + (argBytes addr).length + (tflatBytes k).length =
        pos + (2 :: Codec0.ty0Tag ty :: argBytes addr ++ tflatBytes k).length by
      simp only [List.length_cons, List.length_append]; omega, u32_sub1_sub hfuel]
  | .store ty val addr k, ba, pos, frames, rest, fuel, hb, hfuel, hdrop => by
    dsimp only [TFlat0ListBounded, tflatNodes, tflatBytes] at hb hfuel hdrop ⊢
    have hf0 : fuel ≠ 0 := fun hz => by subst hz; simp at hfuel
    have hd1 : ba.data.toList.drop (pos + 1) = Codec0.ty0Tag ty :: (argBytes val ++
        (argBytes addr ++ (tflatBytes k ++ rest))) := by
      rw [drop_pos_add, hdrop]; simp [List.append_assoc]
    have hd2 : ba.data.toList.drop (pos + 2) =
        argBytes val ++ (argBytes addr ++ (tflatBytes k ++ rest)) := by
      rw [show pos + 2 = (pos + 1) + 1 by omega, drop_pos_add, hd1]; rfl
    have hd3 : ba.data.toList.drop (pos + 2 + (argBytes val).length) =
        argBytes addr ++ (tflatBytes k ++ rest) := by rw [drop_pos_add, hd2, List.drop_left]
    have hd4 : ba.data.toList.drop (pos + 2 + (argBytes val).length + (argBytes addr).length) =
        tflatBytes k ++ rest := by rw [drop_pos_add, hd3, List.drop_left]
    have hstep : Codec0.decodeNodeStep0 ba pos =
        .push (pos + 2 + (argBytes val).length + (argBytes addr).length) (.store ty val addr) := by
      dsimp only [Codec0.decodeNodeStep0, Codec0.decodeLinLowStep0, Codec0.decodeStoreStep0,
        Codec0.finishStoreStep0]
      rw [decodeU8_of_bytes ba pos 3 _ (by simpa [List.append_assoc] using hdrop)]; dsimp only
      rw [ite_true_eq (by decide : ((3 : UInt8) ≤ 3)),
        ite_false_eq (by decide : ¬ ((3 : UInt8) == 0) = true),
        ite_false_eq (by decide : ¬ ((3 : UInt8) == 1) = true),
        ite_false_eq (by decide : ¬ ((3 : UInt8) == 2) = true),
        decodeTy0_of_bytes ba (pos + 1) ty _ hd1]; dsimp only
      rw [show pos + 1 + 1 = pos + 2 by omega, decodeArg0_of_bytes ba _ val _ hd2]; dsimp only
      rw [decodeArg0_of_bytes ba (pos + 2 + (argBytes val).length) addr _ hd3]
    rw [decodeTFlatLoop0_step fuel hf0 ba pos frames, hstep]; dsimp only [Codec0.stepLoopFrame0]
    rw [decodeTFlatLoop0_of_bytes k ba _ (.store ty val addr :: frames) rest (fuel - 1) hb
      (u32_sub1_ge hfuel) hd4]
    dsimp only [frameApplyResult, Codec0.decodeApplyFrames0, Codec0.applyLinFrame0,
      Codec0.applyLinLowFrame0, tflatNodes]
    rw [show pos + 2 + (argBytes val).length + (argBytes addr).length + (tflatBytes k).length =
        pos + (3 :: Codec0.ty0Tag ty :: argBytes val ++ argBytes addr ++ tflatBytes k).length by
      simp only [List.length_cons, List.length_append]; omega, u32_sub1_sub hfuel]
  | .call f as bs args k, ba, pos, frames, rest, fuel, hb, hfuel, hdrop => by
    dsimp only [TFlat0ListBounded, tflatNodes, tflatBytes] at hb hfuel hdrop ⊢
    have hf0 : fuel ≠ 0 := fun hz => by subst hz; simp at hfuel
    have hd1 : ba.data.toList.drop (pos + 1) = u32Bytes f ++ (tyListBytes as ++
        (tyListBytes bs ++ (argListBytes args ++ (tflatBytes k ++ rest)))) := by
      rw [drop_pos_add, hdrop]; simp [List.append_assoc]
    have hd2 : ba.data.toList.drop (pos + 5) = tyListBytes as ++ (tyListBytes bs ++
        (argListBytes args ++ (tflatBytes k ++ rest))) := by
      rw [show pos + 5 = (pos + 1) + 4 by omega, drop_pos_add, hd1]; exact List.drop_left' rfl
    have hd3 : ba.data.toList.drop (pos + 5 + (tyListBytes as).length) = tyListBytes bs ++
        (argListBytes args ++ (tflatBytes k ++ rest)) := by rw [drop_pos_add, hd2, List.drop_left]
    have hd4 : ba.data.toList.drop (pos + 5 + (tyListBytes as).length + (tyListBytes bs).length) =
        argListBytes args ++ (tflatBytes k ++ rest) := by rw [drop_pos_add, hd3, List.drop_left]
    have hd5 : ba.data.toList.drop (pos + 5 + (tyListBytes as).length +
        (tyListBytes bs).length + (argListBytes args).length) = tflatBytes k ++ rest := by
      rw [drop_pos_add, hd4, List.drop_left]
    have hstep : Codec0.decodeNodeStep0 ba pos = .push (pos + 5 + (tyListBytes as).length +
        (tyListBytes bs).length + (argListBytes args).length) (.call f as bs args) := by
      dsimp only [Codec0.decodeNodeStep0, Codec0.decodeCallStep0, Codec0.finishCallStep0,
        Codec0.mkCallStep0, Codec0.decodeCallSig0, Codec0.decodeSymTys0]
      rw [decodeU8_of_bytes ba pos 4 _ (by simpa [List.append_assoc] using hdrop)]; dsimp only
      rw [ite_false_eq (by decide : ¬ ((4 : UInt8) ≤ 3)),
        ite_true_eq (by decide : ((4 : UInt8) == 4) = true),
        decodeU32_of_bytes ba (pos + 1) f _ hd1]; dsimp only
      rw [show pos + 1 + 4 = pos + 5 by omega,
        decodeTyList0_of_bytes ba (pos + 5) as _ hb.1 hd2]; dsimp only
      rw [decodeTyList0_of_bytes ba (pos + 5 + (tyListBytes as).length) bs _ hb.2.1 hd3]; dsimp only
      rw [decodeArgList0_of_bytes ba _ args _ hb.2.2.1 hd4]
    rw [decodeTFlatLoop0_step fuel hf0 ba pos frames, hstep]; dsimp only [Codec0.stepLoopFrame0]
    rw [decodeTFlatLoop0_of_bytes k ba _ (.call f as bs args :: frames) rest (fuel - 1) hb.2.2.2
      (u32_sub1_ge hfuel) hd5]
    dsimp only [frameApplyResult, Codec0.decodeApplyFrames0, Codec0.applyLinFrame0, tflatNodes]
    rw [show pos + 5 + (tyListBytes as).length + (tyListBytes bs).length +
        (argListBytes args).length + (tflatBytes k).length =
        pos + (4 :: u32Bytes f ++ tyListBytes as ++ tyListBytes bs ++
          argListBytes args ++ tflatBytes k).length by
      simp only [List.length_cons, List.length_append, u32Bytes_length]; omega, u32_sub1_sub hfuel]
  | .tailCall f as args, ba, pos, frames, rest, fuel, hb, hfuel, hdrop => by
    dsimp only [TFlat0ListBounded, tflatNodes, tflatBytes] at hb hfuel hdrop ⊢
    have hf0 : fuel ≠ 0 := fun hz => by subst hz; simp at hfuel
    have hd1 : ba.data.toList.drop (pos + 1) =
        u32Bytes f ++ (tyListBytes as ++ (argListBytes args ++ rest)) := by
      rw [drop_pos_add, hdrop]; simp [List.append_assoc]
    have hd2 : ba.data.toList.drop (pos + 5) = tyListBytes as ++ (argListBytes args ++ rest) := by
      rw [show pos + 5 = (pos + 1) + 4 by omega, drop_pos_add, hd1]; exact List.drop_left' rfl
    have hd3 : ba.data.toList.drop (pos + 5 + (tyListBytes as).length) =
        argListBytes args ++ rest := by rw [drop_pos_add, hd2, List.drop_left]
    have hstep : Codec0.decodeNodeStep0 ba pos = .leaf (pos + 5 + (tyListBytes as).length +
        (argListBytes args).length) (.tailCall f as args) := by
      dsimp only [Codec0.decodeNodeStep0, Codec0.decodeBranchStep0, Codec0.decodeLeafStep0,
        Codec0.decodeTailOrExitStep0, Codec0.finishTailOrExit0, Codec0.mkTailOrExit0,
        Codec0.decodeSymTys0]
      rw [decodeU8_of_bytes ba pos 5 _ (by simpa [List.append_assoc] using hdrop)]; dsimp only
      rw [ite_false_eq (by decide : ¬ ((5 : UInt8) ≤ 3)),
        ite_false_eq (by decide : ¬ ((5 : UInt8) == 4) = true),
        ite_false_eq (by decide : ¬ ((5 : UInt8) == 6) = true),
        ite_false_eq (by decide : ¬ ((5 : UInt8) == 11) = true),
        ite_true_eq (by decide : ((5 : UInt8) == 5) = true),
        decodeU32_of_bytes ba (pos + 1) f _ hd1]; dsimp only
      rw [show pos + 1 + 4 = pos + 5 by omega,
        decodeTyList0_of_bytes ba (pos + 5) as _ hb.1 hd2]; dsimp only
      rw [decodeArgList0_of_bytes ba _ args _ hb.2 hd3]; rfl
    rw [decodeTFlatLoop0_step fuel hf0 ba pos frames, hstep]
    dsimp only [Codec0.stepLoopFrame0, frameApplyResult, tflatNodes]
    rw [show pos + 5 + (tyListBytes as).length + (argListBytes args).length =
        pos + (5 :: u32Bytes f ++ tyListBytes as ++ argListBytes args).length by
      simp only [List.length_cons, List.length_append, u32Bytes_length]; omega]; rfl
  | .jnz c t1 t2, ba, pos, frames, rest, fuel, hb, hfuel, hdrop => by
    dsimp only [TFlat0ListBounded, tflatNodes, tflatBytes] at hb hfuel hdrop ⊢
    have hf0 : fuel ≠ 0 := fun hz => by subst hz; simp at hfuel
    have hd1 : ba.data.toList.drop (pos + 1) =
        argBytes c ++ (tflatBytes t1 ++ (tflatBytes t2 ++ rest)) := by
      rw [drop_pos_add, hdrop]; simp [List.append_assoc]
    have hd2 : ba.data.toList.drop (pos + 1 + (argBytes c).length) =
        tflatBytes t1 ++ (tflatBytes t2 ++ rest) := by rw [drop_pos_add, hd1, List.drop_left]
    have hd3 : ba.data.toList.drop (pos + 1 + (argBytes c).length + (tflatBytes t1).length) =
        tflatBytes t2 ++ rest := by rw [drop_pos_add, hd2, List.drop_left]
    have hstep : Codec0.decodeNodeStep0 ba pos =
        .push (pos + 1 + (argBytes c).length) (.jnzL c) := by
      dsimp only [Codec0.decodeNodeStep0, Codec0.decodeBranchStep0]
      rw [decodeU8_of_bytes ba pos 6 _ (by simpa [List.append_assoc] using hdrop)]; dsimp only
      rw [ite_false_eq (by decide : ¬ ((6 : UInt8) ≤ 3)),
        ite_false_eq (by decide : ¬ ((6 : UInt8) == 4) = true),
        ite_true_eq (by decide : ((6 : UInt8) == 6) = true),
        decodeArg0_of_bytes ba (pos + 1) c _ hd1]
    rw [decodeTFlatLoop0_step fuel hf0 ba pos frames, hstep]; dsimp only [Codec0.stepLoopFrame0]
    rw [decodeTFlatLoop0_of_bytes t1 ba _ (.jnzL c :: frames) (tflatBytes t2 ++ rest) (fuel - 1)
      hb.1 (u32_sub1_ge (by omega)) hd2]
    dsimp only [frameApplyResult, Codec0.decodeApplyFrames0, Codec0.stepNonLinFrame0, tflatNodes]
    have hf_lt := fuel.toNat_lt
    have hfuel2 : tflatNodes t2 ≤ (fuel - 1 - UInt32.ofNat (tflatNodes t1)).toNat := by
      rw [u32_sub1_sub (by omega), show fuel = UInt32.ofNat fuel.toNat from UInt32.ofNat_toNat.symm,
        u32_sub_ofNat (by omega) (by omega), UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
      omega
    rw [decodeTFlatLoop0_of_bytes t2 ba _ (.jnzR c t1 :: frames) rest _ hb.2 hfuel2 hd3]
    dsimp only [frameApplyResult, Codec0.decodeApplyFrames0, Codec0.applyLinFrame0, tflatNodes]
    have hsub_eq : fuel - 1 - UInt32.ofNat (tflatNodes t1) - UInt32.ofNat (tflatNodes t2) =
        fuel - UInt32.ofNat (1 + tflatNodes t1 + tflatNodes t2) := by
      rw [u32_sub1_sub (by omega), show fuel = UInt32.ofNat fuel.toNat from UInt32.ofNat_toNat.symm,
        u32_sub_ofNat (by omega) (by omega), u32_sub_ofNat (by omega) (by omega),
        u32_sub_ofNat (by omega) (by omega)]; congr 1; omega
    rw [show pos + 1 + (argBytes c).length + (tflatBytes t1).length + (tflatBytes t2).length =
        pos + (6 :: argBytes c ++ tflatBytes t1 ++ tflatBytes t2).length by
      simp only [List.length_cons, List.length_append]; omega, hsub_eq]
  | .jump j args, ba, pos, frames, rest, fuel, hb, hfuel, hdrop => by
    dsimp only [TFlat0ListBounded, tflatNodes, tflatBytes] at hb hfuel hdrop ⊢
    have hf0 : fuel ≠ 0 := fun hz => by subst hz; simp at hfuel
    have hd1 : ba.data.toList.drop (pos + 1) = u32Bytes j ++ (argListBytes args ++ rest) := by
      rw [drop_pos_add, hdrop]; simp [List.append_assoc]
    have hd2 : ba.data.toList.drop (pos + 5) = argListBytes args ++ rest := by
      rw [show pos + 5 = (pos + 1) + 4 by omega, drop_pos_add, hd1]; exact List.drop_left' rfl
    have hstep : Codec0.decodeNodeStep0 ba pos =
        .leaf (pos + 5 + (argListBytes args).length) (.jump j args) := by
      dsimp only [Codec0.decodeNodeStep0, Codec0.decodeBranchStep0, Codec0.decodeLeafStep0,
        Codec0.decodeJumpStep0]
      rw [decodeU8_of_bytes ba pos 7 _ (by simpa [List.append_assoc] using hdrop)]; dsimp only
      rw [ite_false_eq (by decide : ¬ ((7 : UInt8) ≤ 3)),
        ite_false_eq (by decide : ¬ ((7 : UInt8) == 4) = true),
        ite_false_eq (by decide : ¬ ((7 : UInt8) == 6) = true),
        ite_false_eq (by decide : ¬ ((7 : UInt8) == 11) = true),
        ite_false_eq (by decide : ¬ ((7 : UInt8) == 5) = true),
        ite_true_eq (by decide : ((7 : UInt8) == 7) = true),
        decodeU32_of_bytes ba (pos + 1) j _ hd1]; dsimp only
      rw [show pos + 1 + 4 = pos + 5 by omega, decodeArgList0_of_bytes ba (pos + 5) args _ hb hd2]
    rw [decodeTFlatLoop0_step fuel hf0 ba pos frames, hstep]
    dsimp only [Codec0.stepLoopFrame0, frameApplyResult, tflatNodes]
    rw [show pos + 5 + (argListBytes args).length =
        pos + (7 :: u32Bytes j ++ argListBytes args).length by
      simp only [List.length_cons, List.length_append, u32Bytes_length]; omega]; rfl
  | .ret vs, ba, pos, frames, rest, fuel, hb, hfuel, hdrop => by
    dsimp only [TFlat0ListBounded, tflatNodes, tflatBytes] at hb hfuel hdrop ⊢
    have hf0 : fuel ≠ 0 := fun hz => by subst hz; simp at hfuel
    have hd1 : ba.data.toList.drop (pos + 1) = argListBytes vs ++ rest := by
      rw [drop_pos_add, hdrop]; rfl
    have hstep : Codec0.decodeNodeStep0 ba pos = .leaf (pos + 1 + (argListBytes vs).length)
        (.ret vs) := by
      dsimp only [Codec0.decodeNodeStep0, Codec0.decodeBranchStep0, Codec0.decodeLeafStep0,
        Codec0.decodeLeafHiStep0]
      rw [decodeU8_of_bytes ba pos 8 _ (by simpa [List.append_assoc] using hdrop)]; dsimp only
      rw [ite_false_eq (by decide : ¬ ((8 : UInt8) ≤ 3)),
        ite_false_eq (by decide : ¬ ((8 : UInt8) == 4) = true),
        ite_false_eq (by decide : ¬ ((8 : UInt8) == 6) = true),
        ite_false_eq (by decide : ¬ ((8 : UInt8) == 11) = true),
        ite_false_eq (by decide : ¬ ((8 : UInt8) == 5) = true),
        ite_false_eq (by decide : ¬ ((8 : UInt8) == 7) = true),
        ite_true_eq (by decide : ((8 : UInt8) == 8) = true),
        decodeArgList0_of_bytes ba (pos + 1) vs _ hb hd1]
    rw [decodeTFlatLoop0_step fuel hf0 ba pos frames, hstep]
    dsimp only [Codec0.stepLoopFrame0, frameApplyResult, tflatNodes]
    rw [show pos + 1 + (argListBytes vs).length = pos + (8 :: argListBytes vs).length by
      simp only [List.length_cons]; omega]; rfl
  | .exit f as args, ba, pos, frames, rest, fuel, hb, hfuel, hdrop => by
    dsimp only [TFlat0ListBounded, tflatNodes, tflatBytes] at hb hfuel hdrop ⊢
    have hf0 : fuel ≠ 0 := fun hz => by subst hz; simp at hfuel
    have hd1 : ba.data.toList.drop (pos + 1) =
        u32Bytes f ++ (tyListBytes as ++ (argListBytes args ++ rest)) := by
      rw [drop_pos_add, hdrop]; simp [List.append_assoc]
    have hd2 : ba.data.toList.drop (pos + 5) = tyListBytes as ++ (argListBytes args ++ rest) := by
      rw [show pos + 5 = (pos + 1) + 4 by omega, drop_pos_add, hd1]; exact List.drop_left' rfl
    have hd3 : ba.data.toList.drop (pos + 5 + (tyListBytes as).length) =
        argListBytes args ++ rest := by rw [drop_pos_add, hd2, List.drop_left]
    have hstep : Codec0.decodeNodeStep0 ba pos = .leaf (pos + 5 + (tyListBytes as).length +
        (argListBytes args).length) (.exit f as args) := by
      dsimp only [Codec0.decodeNodeStep0, Codec0.decodeBranchStep0, Codec0.decodeLeafStep0,
        Codec0.decodeLeafHiStep0, Codec0.decodeTailOrExitStep0, Codec0.finishTailOrExit0,
        Codec0.mkTailOrExit0, Codec0.decodeSymTys0]
      rw [decodeU8_of_bytes ba pos 9 _ (by simpa [List.append_assoc] using hdrop)]; dsimp only
      rw [ite_false_eq (by decide : ¬ ((9 : UInt8) ≤ 3)),
        ite_false_eq (by decide : ¬ ((9 : UInt8) == 4) = true),
        ite_false_eq (by decide : ¬ ((9 : UInt8) == 6) = true),
        ite_false_eq (by decide : ¬ ((9 : UInt8) == 11) = true),
        ite_false_eq (by decide : ¬ ((9 : UInt8) == 5) = true),
        ite_false_eq (by decide : ¬ ((9 : UInt8) == 7) = true),
        ite_false_eq (by decide : ¬ ((9 : UInt8) == 8) = true),
        ite_true_eq (by decide : ((9 : UInt8) == 9) = true),
        decodeU32_of_bytes ba (pos + 1) f _ hd1]; dsimp only
      rw [show pos + 1 + 4 = pos + 5 by omega,
        decodeTyList0_of_bytes ba (pos + 5) as _ hb.1 hd2]; dsimp only
      rw [decodeArgList0_of_bytes ba _ args _ hb.2 hd3]; rfl
    rw [decodeTFlatLoop0_step fuel hf0 ba pos frames, hstep]
    dsimp only [Codec0.stepLoopFrame0, frameApplyResult, tflatNodes]
    rw [show pos + 5 + (tyListBytes as).length + (argListBytes args).length =
        pos + (9 :: u32Bytes f ++ tyListBytes as ++ argListBytes args).length by
      simp only [List.length_cons, List.length_append, u32Bytes_length]; omega]; rfl
  | .hlt, ba, pos, frames, rest, fuel, _, hfuel, hdrop => by
    dsimp only [tflatNodes, tflatBytes] at hfuel hdrop ⊢
    have hf0 : fuel ≠ 0 := fun hz => by subst hz; simp at hfuel
    have hstep : Codec0.decodeNodeStep0 ba pos = .leaf (pos + 1) .hlt := by
      dsimp only [Codec0.decodeNodeStep0, Codec0.decodeBranchStep0, Codec0.decodeLeafStep0,
        Codec0.decodeLeafHiStep0]; rw [decodeU8_of_bytes ba pos 10 rest hdrop]; rfl
    rw [decodeTFlatLoop0_step fuel hf0 ba pos frames, hstep]; rfl
  | .group [] k, ba, pos, frames, rest, fuel, hb, hfuel, hdrop => by
    dsimp only [TFlat0ListBounded, tflatNodes, tflatBytes, blocksNodes, blocksBytes]
      at hb hfuel hdrop ⊢
    have hf0 : fuel ≠ 0 := by intro hz; subst hz; simp at hfuel
    have hd1 : ba.data.toList.drop (pos + 1) = u32Bytes (UInt32.ofNat 0) ++
        (tflatBytes k ++ rest) := by rw [drop_pos_add, hdrop]; simp [List.append_assoc]
    have hd2 : ba.data.toList.drop (pos + 5) = tflatBytes k ++ rest := by
      rw [show pos + 5 = (pos + 1) + 4 by omega, drop_pos_add, hd1]; exact List.drop_left' rfl
    have hstep : Codec0.decodeNodeStep0 ba pos = .push (pos + 5) .groupKEmpty := by
      dsimp only [Codec0.decodeNodeStep0, Codec0.decodeBranchStep0, Codec0.decodeGroupStep0]
      rw [decodeU8_of_bytes ba pos 11 _ (by simpa [List.append_assoc] using hdrop)]; dsimp only
      rw [ite_false_eq (by decide : ¬ ((11 : UInt8) ≤ 3)),
        ite_false_eq (by decide : ¬ ((11 : UInt8) == 4) = true),
        ite_false_eq (by decide : ¬ ((11 : UInt8) == 6) = true),
        ite_true_eq (by decide : ((11 : UInt8) == 11) = true),
        decodeU32_of_bytes ba (pos + 1) 0 _ hd1]; rfl
    rw [decodeTFlatLoop0_step fuel hf0 ba pos frames, hstep]; dsimp only [Codec0.stepLoopFrame0]
    rw [decodeTFlatLoop0_of_bytes k ba (pos + 5) (.groupKEmpty :: frames) rest (fuel - 1) hb.2.2
      (u32_sub1_ge (by omega)) hd2]
    dsimp only [frameApplyResult, Codec0.decodeApplyFrames0, Codec0.applyLinFrame0,
      tflatNodes, blocksNodes]
    rw [show pos + 5 + (tflatBytes k).length = pos + (11 :: u32Bytes
          (UInt32.ofNat ([] : List (List Ty0 × TFlat0)).length) ++ [] ++ tflatBytes k).length by
        simp only [List.length_cons, List.length_append, u32Bytes_length, List.length_nil]; omega,
      show 1 + 0 + tflatNodes k = 1 + tflatNodes k by omega, u32_sub1_sub (by omega)]
  | .group ((ts0, b0) :: tl) k, ba, pos, frames, rest, fuel, hb, hfuel, hdrop => by
    dsimp only [TFlat0ListBounded, Blocks0ListBounded, tflatNodes, tflatBytes,
      blocksNodes, blocksBytes] at hb hfuel hdrop ⊢
    have hf0 : fuel ≠ 0 := by intro hz; subst hz; simp at hfuel
    have hlen_lt : 1 + tl.length < 2 ^ 32 := by
      have h := hb.1; simp only [List.length_cons] at h; omega
    have hd1 : ba.data.toList.drop (pos + 1) = u32Bytes (UInt32.ofNat (1 + tl.length)) ++
        (tyListBytes ts0 ++ (tflatBytes b0 ++ (blocksBytes tl ++ (tflatBytes k ++ rest)))) := by
      rw [drop_pos_add, hdrop]; simp [List.append_assoc, Nat.add_comm]
    have hd2 : ba.data.toList.drop (pos + 5) = tyListBytes ts0 ++ (tflatBytes b0 ++
        (blocksBytes tl ++ (tflatBytes k ++ rest))) := by
      rw [show pos + 5 = (pos + 1) + 4 by omega, drop_pos_add, hd1]; exact List.drop_left' rfl
    have hd3 : ba.data.toList.drop (pos + 5 + (tyListBytes ts0).length) =
        tflatBytes b0 ++ (blocksBytes tl ++ (tflatBytes k ++ rest)) := by
      rw [drop_pos_add, hd2, List.drop_left]
    have hcnt_ne : UInt32.ofNat (1 + tl.length) ≠ 0 := (u32_sub1_toNat (n := tl.length) (by
      rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hlen_lt]; omega)).1
    have hcnt_sub : UInt32.ofNat (1 + tl.length) - 1 = UInt32.ofNat tl.length := by
      rw [show (1 : UInt32) = UInt32.ofNat 1 from rfl, u32_sub_ofNat (by omega) (by omega)]
      congr 1; omega
    have hstep : Codec0.decodeNodeStep0 ba pos = .push (pos + 5 + (tyListBytes ts0).length)
        (.groupBody (UInt32.ofNat tl.length) ts0 []) := by
      dsimp only [Codec0.decodeNodeStep0, Codec0.decodeBranchStep0, Codec0.decodeGroupStep0]
      rw [decodeU8_of_bytes ba pos 11 _ (by simpa [List.append_assoc, Nat.add_comm] using hdrop)]
      dsimp only
      rw [ite_false_eq (by decide : ¬ ((11 : UInt8) ≤ 3)),
        ite_false_eq (by decide : ¬ ((11 : UInt8) == 4) = true),
        ite_false_eq (by decide : ¬ ((11 : UInt8) == 6) = true),
        ite_true_eq (by decide : ((11 : UInt8) == 11) = true),
        decodeU32_of_bytes ba (pos + 1) (UInt32.ofNat (1 + tl.length)) _ hd1]; dsimp only
      rw [ite_false_eq (fun hb => hcnt_ne (beq_iff_eq.mp hb)), show pos + 1 + 4 = pos + 5 by omega,
        decodeTyList0_of_bytes ba (pos + 5) ts0 _ hb.2.1.1 hd2, hcnt_sub]
    rw [decodeTFlatLoop0_step fuel hf0 ba pos frames, hstep]; dsimp only [Codec0.stepLoopFrame0]
    rw [decodeGroupBlocks0_of_bytes tl ts0 b0 k [] ba (pos + 5 + (tyListBytes ts0).length)
      frames rest (fuel - 1) (by omega) hb.2.1.2.1 hb.2.1.2.2 hb.2.2
      (u32_sub1_ge (by omega)) hd3]
    dsimp only [frameApplyResult, tflatNodes, blocksNodes]; simp only [List.reverse_nil,
      List.nil_append, show 1 + (tflatNodes b0 + blocksNodes tl) + tflatNodes k =
        1 + (tflatNodes b0 + blocksNodes tl + tflatNodes k) by omega]
    rw [show pos + 5 + (tyListBytes ts0).length +
          ((tflatBytes b0).length + (blocksBytes tl).length + (tflatBytes k).length) =
        pos + (11 :: u32Bytes (UInt32.ofNat ((ts0, b0) :: tl).length) ++
          (tyListBytes ts0 ++ tflatBytes b0 ++ blocksBytes tl) ++ tflatBytes k).length by
      simp only [List.length_cons, List.length_append, u32Bytes_length]; omega,
      u32_sub1_sub (by omega)]
termination_by t _ _ _ _ _ _ _ _ => tflatNodes t
decreasing_by
  all_goals (try have _ := tflatNodes_pos t1; try have _ := tflatNodes_pos t2)
  all_goals (try have _ := tflatNodes_pos b0; try have _ := tflatNodes_pos k)
  all_goals (dsimp only [tflatNodes, blocksNodes]; omega)

private theorem decodeGroupBlocks0_of_bytes :
    ∀ (tl : List (List Ty0 × TFlat0)) (ts0 : List Ty0) (b0 k : TFlat0)
      (doneRev : List (List Ty0 × TFlat0)) (ba : ByteArray) (pos : Nat)
      (frames : List Codec0.DecFrame0) (rest : List UInt8) (fuel : UInt32),
      tl.length < 2 ^ 32 → TFlat0ListBounded b0 → Blocks0ListBounded tl → TFlat0ListBounded k →
      tflatNodes b0 + blocksNodes tl + tflatNodes k ≤ fuel.toNat →
      ba.data.toList.drop pos = tflatBytes b0 ++ (blocksBytes tl ++ (tflatBytes k ++ rest)) →
      Codec0.decodeTFlatLoop0 fuel ba pos
          (.groupBody (UInt32.ofNat tl.length) ts0 doneRev :: frames) =
        match Codec0.decodeApplyFrames0 ba
            (pos + ((tflatBytes b0).length + (blocksBytes tl).length + (tflatBytes k).length))
            (.group (doneRev.reverse ++ (ts0, b0) :: tl) k) frames with
        | .none => .none
        | .done res pos2 => .ok res pos2
        | .cont pos2 frames' => Codec0.decodeTFlatLoop0
            (fuel - UInt32.ofNat (tflatNodes b0 + blocksNodes tl + tflatNodes k)) ba pos2 frames'
  | [], ts0, b0, k, doneRev, ba, pos, frames, rest, fuel, _, hb0, _, hk, hfuel, hdrop => by
    dsimp only [blocksNodes, blocksBytes, List.length_nil] at hfuel hdrop ⊢
    rw [decodeTFlatLoop0_of_bytes b0 ba pos (.groupBody (UInt32.ofNat 0) ts0 doneRev :: frames)
      (tflatBytes k ++ rest) fuel hb0 (by omega) (by simpa using hdrop)]
    dsimp only [frameApplyResult, Codec0.decodeApplyFrames0, Codec0.stepNonLinFrame0,
      Codec0.applyGroupBody0, Codec0.nextGroupFrame0]
    rw [ite_true_eq (by decide : (UInt32.ofNat 0 == 0) = true), revBlocks0_eq,
      List.append_nil, List.reverse_cons]; dsimp only
    have hf_lt := fuel.toNat_lt
    have hfuelk : tflatNodes k ≤ (fuel - UInt32.ofNat (tflatNodes b0)).toNat := by
      rw [show fuel = UInt32.ofNat fuel.toNat from UInt32.ofNat_toNat.symm,
        u32_sub_ofNat (by omega) (by omega), UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
      omega
    have hdk : ba.data.toList.drop (pos + (tflatBytes b0).length) = tflatBytes k ++ rest := by
      rw [drop_pos_add, hdrop, List.nil_append]; exact List.drop_left
    rw [decodeTFlatLoop0_of_bytes k ba _ (.groupK (doneRev.reverse ++ [(ts0, b0)]) :: frames)
      rest _ hk hfuelk hdk]
    dsimp only [frameApplyResult, Codec0.decodeApplyFrames0, Codec0.applyLinFrame0,
      tflatNodes, blocksNodes]
    have hsub_eq : fuel - UInt32.ofNat (tflatNodes b0) - UInt32.ofNat (tflatNodes k) =
        fuel - UInt32.ofNat (tflatNodes b0 + 0 + tflatNodes k) := by
      rw [show fuel = UInt32.ofNat fuel.toNat from UInt32.ofNat_toNat.symm,
        u32_sub_ofNat (by omega) (by omega), u32_sub_ofNat (by omega) (by omega),
        u32_sub_ofNat (by omega) (by omega)]; congr 1; omega
    simp only [Nat.add_zero, Nat.add_assoc] at hsub_eq ⊢; rw [hsub_eq]
  | (ts1, b1) :: tl', ts0, b0, k, doneRev, ba, pos, frames, rest, fuel, htl, hb0, hbtl, hk,
      hfuel, hdrop => by
    dsimp only [Blocks0ListBounded, blocksNodes, blocksBytes] at hbtl hfuel hdrop ⊢
    rw [decodeTFlatLoop0_of_bytes b0 ba pos
      (.groupBody (UInt32.ofNat ((ts1, b1) :: tl').length) ts0 doneRev :: frames)
      (tyListBytes ts1 ++ tflatBytes b1 ++ blocksBytes tl' ++ (tflatBytes k ++ rest))
      fuel hb0 (by omega) (by simpa [List.append_assoc] using hdrop)]
    dsimp only [frameApplyResult, Codec0.decodeApplyFrames0, Codec0.stepNonLinFrame0,
      Codec0.applyGroupBody0, Codec0.nextGroupFrame0, Codec0.nextGroupBodyCont0]
    have hne0 : UInt32.ofNat ((ts1, b1) :: tl').length ≠ 0 := (u32_sub1_toNat (n := tl'.length) (by
      rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt htl, List.length_cons])).1
    have hsub1 : UInt32.ofNat ((ts1, b1) :: tl').length - 1 = UInt32.ofNat tl'.length := by
      rw [show (1 : UInt32) = UInt32.ofNat 1 from rfl,
        u32_sub_ofNat (by omega) (by simp only [List.length_cons]; omega)]; congr 1
    have hdts : ba.data.toList.drop (pos + (tflatBytes b0).length) =
        tyListBytes ts1 ++ (tflatBytes b1 ++ (blocksBytes tl' ++ (tflatBytes k ++ rest))) := by
      rw [drop_pos_add, hdrop, List.drop_left]; simp [List.append_assoc]
    rw [ite_false_eq (fun hb => hne0 (beq_iff_eq.mp hb)),
      decodeTyList0_of_bytes ba _ ts1 _ hbtl.1 hdts]; dsimp only; rw [hsub1]
    have hf_lt := fuel.toNat_lt
    have hfuel1 : tflatNodes b1 + blocksNodes tl' + tflatNodes k ≤
        (fuel - UInt32.ofNat (tflatNodes b0)).toNat := by
      rw [show fuel = UInt32.ofNat fuel.toNat from UInt32.ofNat_toNat.symm,
        u32_sub_ofNat (by omega) (by omega), UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
      omega
    have hdb1 : ba.data.toList.drop (pos + (tflatBytes b0).length + (tyListBytes ts1).length) =
        tflatBytes b1 ++ (blocksBytes tl' ++ (tflatBytes k ++ rest)) := by
      rw [drop_pos_add, hdts, List.drop_left]
    rw [decodeGroupBlocks0_of_bytes tl' ts1 b1 k ((ts0, b0) :: doneRev) ba _ frames rest _
      (by simp at htl; omega) hbtl.2.1 hbtl.2.2 hk hfuel1 hdb1]
    have hsub_eq : fuel - UInt32.ofNat (tflatNodes b0) -
          UInt32.ofNat (tflatNodes b1 + blocksNodes tl' + tflatNodes k) =
        fuel - UInt32.ofNat (tflatNodes b0 + (tflatNodes b1 + blocksNodes tl') + tflatNodes k) := by
      rw [show fuel = UInt32.ofNat fuel.toNat from UInt32.ofNat_toNat.symm,
        u32_sub_ofNat (by omega) (by omega), u32_sub_ofNat (by omega) (by omega),
        u32_sub_ofNat (by omega) (by omega)]; congr 1; omega
    simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append,
      List.length_append, Nat.add_assoc] at hsub_eq ⊢; rw [hsub_eq]
termination_by tl _ b0 k _ _ _ _ _ _ => tflatNodes b0 + blocksNodes tl + tflatNodes k
decreasing_by
  all_goals (have _ := tflatNodes_pos b0; have _ := tflatNodes_pos k)
  all_goals (try have _ := tflatNodes_pos b1)
  all_goals (dsimp only [blocksNodes]; omega)
end

private theorem decodeTFlat0_of_bytes (ba : ByteArray) (pos : Nat) (t : TFlat0)
    (rest : List UInt8) (hb : TFlat0Bounded t)
    (h : ba.data.toList.drop pos = tflatBytes t ++ rest) :
    Codec0.decodeTFlat0 ba pos = .ok t (pos + (tflatBytes t).length) := by
  dsimp only [Codec0.decodeTFlat0]
  have hlen_rem : (tflatBytes t).length ≤ ba.size - pos := by
    have := congrArg List.length h
    rw [List.length_drop, ba_data_toList_length, List.length_append] at this
    omega
  have hnodes_le_bytes := tflatNodes_le_bytes_length t
  have hnodes_le_rem : tflatNodes t ≤ ba.size - pos := Nat.le_trans hnodes_le_bytes hlen_rem
  have hfuel : tflatNodes t ≤
      (if ba.size - pos < 0xffffffff then UInt32.ofNat (ba.size - pos) else 0xffffffff).toNat := by
    by_cases hsmall : ba.size - pos < 0xffffffff
    · rw [ite_true_eq hsmall, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
      exact hnodes_le_rem
    · rw [ite_false_eq hsmall]
      exact hb.2
  rw [decodeTFlatLoop0_of_bytes t ba pos [] rest _ hb.1 hfuel h]
  rfl

/-! ### Reverse `TFlat0` Decoder Proof (`decodeTFlat0_ok_bytes`) -/

private def framePreBytes : Codec0.DecFrame0 → List UInt8
  | .let1 op args => 0 :: opBytes op ++ argListBytes args
  | .let2Umulw64 a b => 1 :: argBytes a ++ argBytes b
  | .load t addr => 2 :: Codec0.ty0Tag t :: argBytes addr
  | .store t val addr => 3 :: Codec0.ty0Tag t :: argBytes val ++ argBytes addr
  | .call f as bs args => 4 :: u32Bytes f ++ tyListBytes as ++ tyListBytes bs ++ argListBytes args
  | .jnzL c => 6 :: argBytes c
  | .jnzR c t => 6 :: argBytes c ++ tflatBytes t
  | .groupBody rem curTs doneRev =>
    11 :: u32Bytes (UInt32.ofNat doneRev.length + 1 + rem) ++
      blocksBytes doneRev.reverse ++ tyListBytes curTs
  | .groupKEmpty => 11 :: u32Bytes 0
  | .groupK bodies => 11 :: u32Bytes (UInt32.ofNat bodies.length) ++ blocksBytes bodies

private def framesPreBytes (frames : List Codec0.DecFrame0) : List UInt8 :=
  frames.foldr (fun f acc => acc ++ framePreBytes f) []

private def frameBounded : Codec0.DecFrame0 → Prop
  | .let1 _ args => args.length < 2 ^ 32
  | .let2Umulw64 _ _ => True
  | .load _ _ => True
  | .store _ _ _ => True
  | .call _ as bs args => as.length < 2 ^ 32 ∧ bs.length < 2 ^ 32 ∧ args.length < 2 ^ 32
  | .jnzL _ => True
  | .jnzR _ t => TFlat0ListBounded t
  | .groupBody rem curTs doneRev =>
    doneRev.length + 1 + rem.toNat < 2 ^ 32 ∧ curTs.length < 2 ^ 32 ∧
      Blocks0ListBounded doneRev.reverse
  | .groupKEmpty => True
  | .groupK bodies => bodies.length < 2 ^ 32 ∧ Blocks0ListBounded bodies

private def framesBounded : List Codec0.DecFrame0 → Prop
  | [] => True
  | f :: rest => frameBounded f ∧ framesBounded rest

private theorem blocks0ListBounded_append {a b : List (List Ty0 × TFlat0)}
    (ha : Blocks0ListBounded a) (hb : Blocks0ListBounded b) :
    Blocks0ListBounded (a ++ b) := by
  induction a with
  | nil => exact hb
  | cons hd tl ih =>
    rcases hd with ⟨ts, node⟩
    exact ⟨ha.1, ha.2.1, ih ha.2.2⟩

private theorem blocksBytes_append (a b : List (List Ty0 × TFlat0)) :
    blocksBytes (a ++ b) = blocksBytes a ++ blocksBytes b := by
  induction a with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨ts, node⟩; dsimp only [List.cons_append, blocksBytes]
    rw [ih]; simp only [List.append_assoc]

private def frameNodes : Codec0.DecFrame0 → Nat
  | .let1 _ _ | .let2Umulw64 _ _ | .load _ _ | .store _ _ _ | .call _ _ _ _
  | .jnzL _ | .groupKEmpty => 1
  | .jnzR _ t => 1 + tflatNodes t
  | .groupBody _ _ doneRev => 1 + blocksNodes doneRev.reverse
  | .groupK bodies => 1 + blocksNodes bodies

private def framesNodes (frames : List Codec0.DecFrame0) : Nat :=
  frames.foldr (fun f acc => acc + frameNodes f) 0

private theorem decodeTailOrExitStep0_ok_bytes (ba : ByteArray) (pos : Nat)
    (isExit : Bool) (step : Codec0.DecStep0) :
    Codec0.decodeTailOrExitStep0 ba pos isExit = step →
    (match step with
    | .none => True | .push _ _ => False
    | .leaf pos1 v =>
      pos ≤ pos1 ∧ pos1 ≤ ba.size ∧
        (if isExit then 9 else 5) :: baSlice ba pos pos1 = tflatBytes v ∧
        TFlat0ListBounded v ∧ tflatNodes v = 1) := by
  intro h
  dsimp only [Codec0.decodeTailOrExitStep0, Codec0.finishTailOrExit0,
    Codec0.mkTailOrExit0, Codec0.decodeSymTys0] at h
  cases hf : Codec0.decodeU32 ba pos with
  | none => rw [hf] at h; subst h; trivial | ok fnSym p1 =>
    rw [hf] at h; dsimp only at h
    cases has : Codec0.decodeTyList0 ba p1 with
    | none => rw [has] at h; subst h; trivial | ok as p2 =>
      rw [has] at h; dsimp only at h
      cases hargs : Codec0.decodeArgList0 ba p2 with
      | none => rw [hargs] at h; subst h; trivial | ok args p3 =>
        rw [hargs] at h; subst h
        obtain ⟨h01, _, hp1, hs1⟩ := decodeU32_ok_bytes ba pos fnSym p1 hf; subst hp1
        obtain ⟨h12, _, hbl1, hs2⟩ := decodeTyList0_ok_bytes ba (pos + 4) as p2 has
        obtain ⟨h23, h3s, hbl2, hs3⟩ := decodeArgList0_ok_bytes ba p2 args p3 hargs
        have hsl : baSlice ba pos p3 = u32Bytes fnSym ++ tyListBytes as ++ argListBytes args := by
          rw [baSlice_trans h01 (by omega : pos + 4 ≤ p3), hs1,
            baSlice_trans h12 h23, hs2, hs3, List.append_assoc]
        cases isExit <;> (
          dsimp only; refine ⟨by omega, h3s, ?_, ⟨hbl1, hbl2⟩, rfl⟩
          rw [hsl]; dsimp only [tflatBytes]
          simp only [List.append_assoc, Bool.false_eq_true, ite_true, ite_false]; rfl)

private theorem decodeNodeStep0_ok_bytes (ba : ByteArray) (pos : Nat) (step : Codec0.DecStep0) :
    Codec0.decodeNodeStep0 ba pos = step →
    (match step with
    | .none => True
    | .push pos1 f =>
      pos < pos1 ∧ pos1 ≤ ba.size ∧ baSlice ba pos pos1 = framePreBytes f ∧
        frameBounded f ∧ frameNodes f = 1
    | .leaf pos1 v =>
      pos < pos1 ∧ pos1 ≤ ba.size ∧ baSlice ba pos pos1 = tflatBytes v ∧
        TFlat0ListBounded v ∧ tflatNodes v = 1) := by
  intro h; dsimp only [Codec0.decodeNodeStep0] at h
  cases hu : Codec0.decodeU8 ba pos with
  | none => rw [hu] at h; subst h; trivial
  | ok tag p1 =>
    rw [hu] at h; dsimp only at h
    obtain ⟨_, h1s, hp1, hs1⟩ := decodeU8_ok_bytes ba pos tag p1 hu; subst hp1
    by_cases hle3 : tag ≤ 3
    · rw [ite_true_eq hle3] at h; dsimp only [Codec0.decodeLinLowStep0] at h
      by_cases ht0 : tag = 0
      · subst ht0; rw [ite_true_eq (by decide : ((0 : UInt8) == 0) = true)] at h
        dsimp only [Codec0.decodeLet1Step0, Codec0.finishLet1Step0, Codec0.mkLet1Step0] at h
        cases hop : Codec0.decodeOpCode0 ba (pos + 1) with
        | none => rw [hop] at h; subst h; trivial
        | ok op p2 =>
          rw [hop] at h; dsimp only at h
          cases hargs : Codec0.decodeArgList0 ba p2 with
          | none => rw [hargs] at h; subst h; trivial | ok args p3 =>
            rw [hargs] at h; subst h
            obtain ⟨h12, _, hs2⟩ := decodeOpCode0_ok_bytes ba (pos + 1) op p2 hop
            obtain ⟨h23, h3s, hbl, hs3⟩ := decodeArgList0_ok_bytes ba p2 args p3 hargs
            refine ⟨by omega, h3s, ?_, hbl, rfl⟩
            rw [baSlice_trans (by omega) (by omega), hs1, baSlice_trans h12 h23, hs2, hs3]; rfl
      · rw [ite_false_eq (fun hb => ht0 (beq_iff_eq.mp hb))] at h
        by_cases ht1 : tag = 1
        · subst ht1; rw [ite_true_eq (by decide : ((1 : UInt8) == 1) = true)] at h
          dsimp only [Codec0.decodeLet2Step0] at h
          cases ha : Codec0.decodeArg0 ba (pos + 1) with
          | none => rw [ha] at h; subst h; trivial | ok a p2 =>
            rw [ha] at h; dsimp only at h
            cases hb : Codec0.decodeArg0 ba p2 with
            | none => rw [hb] at h; subst h; trivial | ok b p3 =>
              rw [hb] at h; subst h
              obtain ⟨h12, _, hs2⟩ := decodeArg0_ok_bytes ba (pos + 1) a p2 ha
              obtain ⟨h23, h3s, hs3⟩ := decodeArg0_ok_bytes ba p2 b p3 hb
              refine ⟨by omega, h3s, ?_, trivial, rfl⟩
              rw [baSlice_trans (by omega) (by omega), hs1, baSlice_trans h12 h23, hs2, hs3]; rfl
        · rw [ite_false_eq (fun hb => ht1 (beq_iff_eq.mp hb))] at h
          by_cases ht2 : tag = 2
          · subst ht2; rw [ite_true_eq (by decide : ((2 : UInt8) == 2) = true)] at h
            dsimp only [Codec0.decodeLoadStep0] at h
            cases ht : Codec0.decodeTy0 ba (pos + 1) with
            | none => rw [ht] at h; subst h; trivial | ok ty p2 =>
              rw [ht] at h; dsimp only at h
              cases ha : Codec0.decodeArg0 ba p2 with
              | none => rw [ha] at h; subst h; trivial | ok addr p3 =>
                rw [ha] at h; subst h
                obtain ⟨h12, _, hp2, hs2⟩ := decodeTy0_ok_bytes ba (pos + 1) ty p2 ht; subst hp2
                obtain ⟨h23, h3s, hs3⟩ := decodeArg0_ok_bytes ba (pos + 1 + 1) addr p3 ha
                refine ⟨by omega, h3s, ?_, trivial, rfl⟩
                rw [baSlice_trans (by omega) (by omega), hs1, baSlice_trans h12 h23, hs2, hs3]
                rfl
          · rw [ite_false_eq (fun hb => ht2 (beq_iff_eq.mp hb))] at h
            have ht3 : tag = 3 := by
              have htb := UInt8.ofNat_toNat (x := tag); have : tag.toNat ≤ 3 := hle3
              have hn0 : tag.toNat ≠ 0 := fun hz => ht0 (by rw [← htb, hz]; rfl)
              have hn1 : tag.toNat ≠ 1 := fun hz => ht1 (by rw [← htb, hz]; rfl)
              have hn2 : tag.toNat ≠ 2 := fun hz => ht2 (by rw [← htb, hz]; rfl)
              rw [← htb, (by omega : tag.toNat = 3)]; rfl
            subst ht3; dsimp only [Codec0.decodeStoreStep0, Codec0.finishStoreStep0] at h
            cases ht : Codec0.decodeTy0 ba (pos + 1) with
            | none => rw [ht] at h; subst h; trivial | ok ty p2 =>
              rw [ht] at h; dsimp only at h
              cases hv : Codec0.decodeArg0 ba p2 with
              | none => rw [hv] at h; subst h; trivial | ok val p3 =>
                rw [hv] at h; dsimp only at h
                cases ha : Codec0.decodeArg0 ba p3 with
                | none => rw [ha] at h; subst h; trivial | ok addr p4 =>
                  rw [ha] at h; subst h
                  obtain ⟨h12, _, hp2, hs2⟩ := decodeTy0_ok_bytes ba (pos + 1) ty p2 ht; subst hp2
                  obtain ⟨h23, _, hs3⟩ := decodeArg0_ok_bytes ba (pos + 1 + 1) val p3 hv
                  obtain ⟨h34, h4s, hs4⟩ := decodeArg0_ok_bytes ba p3 addr p4 ha
                  refine ⟨by omega, h4s, ?_, trivial, rfl⟩
                  rw [baSlice_trans (by omega) (by omega : pos + 1 ≤ p4), hs1,
                    baSlice_trans h12 (by omega : pos + 1 + 1 ≤ p4), hs2,
                    baSlice_trans h23 h34, hs3, hs4]; rfl
    · rw [ite_false_eq hle3] at h
      by_cases ht4 : tag = 4
      · subst ht4; rw [ite_true_eq (by decide : ((4 : UInt8) == 4) = true)] at h
        dsimp only [Codec0.decodeCallStep0, Codec0.finishCallStep0, Codec0.mkCallStep0,
          Codec0.decodeCallSig0, Codec0.decodeSymTys0] at h
        cases hf : Codec0.decodeU32 ba (pos + 1) with
        | none => rw [hf] at h; subst h; trivial | ok fnSym p2 =>
          rw [hf] at h; dsimp only at h
          cases has : Codec0.decodeTyList0 ba p2 with
          | none => rw [has] at h; subst h; trivial | ok as p3 =>
            rw [has] at h; dsimp only at h
            cases hbs : Codec0.decodeTyList0 ba p3 with
            | none => rw [hbs] at h; subst h; trivial | ok bs p4 =>
              rw [hbs] at h; dsimp only at h
              cases hargs : Codec0.decodeArgList0 ba p4 with
              | none => rw [hargs] at h; subst h; trivial | ok args p5 =>
                rw [hargs] at h; subst h
                obtain ⟨h12, _, hp2, hs2⟩ := decodeU32_ok_bytes ba (pos + 1) fnSym p2 hf; subst hp2
                obtain ⟨h23, _, hbl1, hs3⟩ := decodeTyList0_ok_bytes ba (pos + 1 + 4) as p3 has
                obtain ⟨h34, _, hbl2, hs4⟩ := decodeTyList0_ok_bytes ba p3 bs p4 hbs
                obtain ⟨h45, h5s, hbl3, hs5⟩ := decodeArgList0_ok_bytes ba p4 args p5 hargs
                refine ⟨by omega, h5s, ?_, ⟨hbl1, hbl2, hbl3⟩, rfl⟩
                rw [baSlice_trans (by omega) (by omega : pos + 1 ≤ p5), hs1,
                  baSlice_trans h12 (by omega : pos + 1 + 4 ≤ p5), hs2,
                  baSlice_trans h23 (by omega : p3 ≤ p5), hs3, baSlice_trans h34 h45, hs4, hs5]
                dsimp only [framePreBytes]; simp only [List.append_assoc]; rfl
      · rw [ite_false_eq (fun hb => ht4 (beq_iff_eq.mp hb))] at h
        dsimp only [Codec0.decodeBranchStep0] at h
        by_cases ht6 : tag = 6
        · subst ht6; rw [ite_true_eq (by decide : ((6 : UInt8) == 6) = true)] at h
          cases hc : Codec0.decodeArg0 ba (pos + 1) with
          | none => rw [hc] at h; subst h; trivial | ok c p2 =>
            rw [hc] at h; subst h
            obtain ⟨h12, h2s, hs2⟩ := decodeArg0_ok_bytes ba (pos + 1) c p2 hc
            refine ⟨by omega, h2s, ?_, trivial, rfl⟩
            rw [baSlice_trans (by omega) h12, hs1, hs2]; rfl
        · rw [ite_false_eq (fun hb => ht6 (beq_iff_eq.mp hb))] at h
          by_cases ht11 : tag = 11
          · subst ht11; rw [ite_true_eq (by decide : ((11 : UInt8) == 11) = true)] at h
            dsimp only [Codec0.decodeGroupStep0] at h
            cases hcnt : Codec0.decodeU32 ba (pos + 1) with
            | none => rw [hcnt] at h; subst h; trivial | ok cnt p2 =>
              rw [hcnt] at h; dsimp only at h
              obtain ⟨h12, h2s, hp2, hs2⟩ := decodeU32_ok_bytes ba (pos + 1) cnt p2 hcnt; subst hp2
              by_cases hc0 : cnt = 0
              · subst hc0; rw [ite_true_eq (by decide : ((0 : UInt32) == 0) = true)] at h; subst h
                refine ⟨by omega, h2s, ?_, trivial, rfl⟩
                rw [baSlice_trans (by omega) (by omega), hs1, hs2]; rfl
              · rw [ite_false_eq (fun hb => hc0 (beq_iff_eq.mp hb))] at h
                cases hts : Codec0.decodeTyList0 ba (pos + 1 + 4) with
                | none => rw [hts] at h; subst h; trivial | ok ts0 p3 =>
                  rw [hts] at h; subst h
                  obtain ⟨h23, h3s, hbl, hs3⟩ := decodeTyList0_ok_bytes ba (pos + 1 + 4) ts0 p3 hts
                  have hcnt1 : 1 ≤ cnt.toNat := by
                    cases Nat.eq_zero_or_pos cnt.toNat with
                    | inl hz => exact absurd (by rw [← UInt32.ofNat_toNat (x := cnt), hz]; rfl) hc0
                    | inr hp => exact hp
                  have h1n : (1 : UInt32).toNat = 1 := rfl
                  have hrem : 0 + 1 + (cnt - 1).toNat < 2 ^ 32 := by
                    rw [UInt32.toNat_sub_of_le cnt 1 hcnt1, h1n]; have := cnt.toNat_lt; omega
                  have hcnt_eq : (UInt32.ofNat ([] : List (List Ty0 × TFlat0)).length +
                      1 + (cnt - 1)) = cnt := by
                    rw [List.length_nil]; change (0 : UInt32) + 1 + (cnt - 1) = cnt
                    rw [UInt32.zero_add, UInt32.add_comm 1 (cnt - 1), UInt32.sub_add_cancel]
                  refine ⟨by omega, h3s, ?_, ⟨hrem, hbl, trivial⟩, rfl⟩
                  rw [baSlice_trans (by omega) (by omega : pos + 1 ≤ p3), hs1,
                    baSlice_trans h12 h23, hs2, hs3]; dsimp only [framePreBytes]; rw [hcnt_eq]; rfl
          · rw [ite_false_eq (fun hb => ht11 (beq_iff_eq.mp hb))] at h
            dsimp only [Codec0.decodeLeafStep0, Codec0.decodeLeafHiStep0] at h
            by_cases ht5 : tag = 5
            · subst ht5; rw [ite_true_eq (by decide : ((5 : UInt8) == 5) = true)] at h
              have hte := decodeTailOrExitStep0_ok_bytes ba (pos + 1) false step h
              cases step with
              | none => trivial | push _ _ => exact False.elim hte
              | leaf p1' v =>
                obtain ⟨h1p, hps', heq, hbl, hnv⟩ := hte; refine ⟨by omega, hps', ?_, hbl, hnv⟩
                rw [baSlice_trans (by omega) h1p, hs1, ← heq]; rfl
            · rw [ite_false_eq (fun hb => ht5 (beq_iff_eq.mp hb))] at h
              by_cases ht7 : tag = 7
              · subst ht7; rw [ite_true_eq (by decide : ((7 : UInt8) == 7) = true)] at h
                dsimp only [Codec0.decodeJumpStep0] at h
                cases hj : Codec0.decodeU32 ba (pos + 1) with
                | none => rw [hj] at h; subst h; trivial | ok j p2 =>
                  rw [hj] at h; dsimp only at h
                  cases hargs : Codec0.decodeArgList0 ba p2 with
                  | none => rw [hargs] at h; subst h; trivial | ok args p3 =>
                    rw [hargs] at h; subst h
                    obtain ⟨h12, _, hp2, hs2⟩ := decodeU32_ok_bytes ba (pos + 1) j p2 hj; subst hp2
                    obtain ⟨h23, h3s, hbl, hs3⟩ :=
                      decodeArgList0_ok_bytes ba (pos + 1 + 4) args p3 hargs
                    refine ⟨by omega, h3s, ?_, hbl, rfl⟩
                    rw [baSlice_trans (by omega) (by omega : pos + 1 ≤ p3), hs1,
                      baSlice_trans h12 h23, hs2, hs3]; rfl
              · rw [ite_false_eq (fun hb => ht7 (beq_iff_eq.mp hb))] at h
                by_cases ht8 : tag = 8
                · subst ht8; rw [ite_true_eq (by decide : ((8 : UInt8) == 8) = true)] at h
                  cases hvs : Codec0.decodeArgList0 ba (pos + 1) with
                  | none => rw [hvs] at h; subst h; trivial | ok vs p2 =>
                    rw [hvs] at h; subst h
                    obtain ⟨h12, h2s, hbl, hs2⟩ := decodeArgList0_ok_bytes ba (pos + 1) vs p2 hvs
                    refine ⟨by omega, h2s, ?_, hbl, rfl⟩
                    rw [baSlice_trans (by omega) h12, hs1, hs2]; rfl
                · rw [ite_false_eq (fun hb => ht8 (beq_iff_eq.mp hb))] at h
                  by_cases ht9 : tag = 9
                  · subst ht9; rw [ite_true_eq (by decide : ((9 : UInt8) == 9) = true)] at h
                    have hte := decodeTailOrExitStep0_ok_bytes ba (pos + 1) true step h
                    cases step with
                    | none => trivial | push _ _ => exact False.elim hte
                    | leaf p1' v =>
                      obtain ⟨h1p, hps', heq, hbl, hnv⟩ := hte
                      refine ⟨by omega, hps', ?_, hbl, hnv⟩
                      rw [baSlice_trans (by omega) h1p, hs1, ← heq]; rfl
                  · rw [ite_false_eq (fun hb => ht9 (beq_iff_eq.mp hb))] at h
                    by_cases ht10 : tag = 10
                    · subst ht10; rw [ite_true_eq (by decide : ((10 : UInt8) == 10) = true)] at h
                      subst h; exact ⟨by omega, h1s, hs1, trivial, rfl⟩
                    · rw [ite_false_eq (fun hb => ht10 (beq_iff_eq.mp hb))] at h; subst h; trivial

private theorem applyLinFrame0_spec (f : Codec0.DecFrame0) (v : TFlat0)
    (hnl : match f with | .jnzL _ | .groupBody _ _ _ => False | _ => True) :
    framePreBytes f ++ tflatBytes v = tflatBytes (Codec0.applyLinFrame0 f v) ∧
    (frameBounded f → TFlat0ListBounded v → TFlat0ListBounded (Codec0.applyLinFrame0 f v)) ∧
    frameNodes f + tflatNodes v = tflatNodes (Codec0.applyLinFrame0 f v) := by
  cases f with
  | jnzL _ | groupBody _ _ _ => exact False.elim hnl
  | let1 op args =>
    refine ⟨?_, fun hf hv => ⟨hf, hv⟩, rfl⟩
    dsimp only [framePreBytes, Codec0.applyLinFrame0, Codec0.applyLinLowFrame0, tflatBytes]
  | let2Umulw64 a b =>
    refine ⟨?_, fun _ hv => hv, rfl⟩
    dsimp only [framePreBytes, Codec0.applyLinFrame0, Codec0.applyLinLowFrame0, tflatBytes]
  | load t addr => refine ⟨rfl, fun _ hv => hv, rfl⟩
  | store t val addr =>
    refine ⟨?_, fun _ hv => hv, rfl⟩
    dsimp only [framePreBytes, Codec0.applyLinFrame0, Codec0.applyLinLowFrame0, tflatBytes]
  | call fnSym as bs args =>
    refine ⟨?_, fun hf hv => ⟨hf.1, hf.2.1, hf.2.2, hv⟩, rfl⟩
    dsimp only [framePreBytes, Codec0.applyLinFrame0, tflatBytes]
  | jnzR c t =>
    refine ⟨?_, fun hf hv => ⟨hf, hv⟩, rfl⟩
    dsimp only [framePreBytes, Codec0.applyLinFrame0, tflatBytes]
  | groupKEmpty =>
    refine ⟨?_, fun _ hv => ⟨by decide, trivial, hv⟩, rfl⟩
    dsimp only [framePreBytes, Codec0.applyLinFrame0, tflatBytes, blocksBytes]
    simp only [List.append_assoc, List.nil_append]; rfl
  | groupK bodies =>
    refine ⟨?_, fun hf hv => ⟨hf.1, hf.2, hv⟩, rfl⟩
    dsimp only [framePreBytes, Codec0.applyLinFrame0, tflatBytes]

private theorem blocksNodes_snoc (xs : List (List Ty0 × TFlat0)) (ts : List Ty0) (v : TFlat0) :
    blocksNodes (xs ++ [(ts, v)]) = blocksNodes xs + tflatNodes v := by
  induction xs with
  | nil => dsimp only [List.nil_append, blocksNodes]; omega
  | cons hd _ ih =>
    rcases hd with ⟨_, b⟩; dsimp only [List.cons_append, blocksNodes]; rw [ih, Nat.add_assoc]

private theorem decodeApplyFrames0_ok_bytes :
    ∀ (frames : List Codec0.DecFrame0) (ba : ByteArray) (pos : Nat) (v : TFlat0),
      framesBounded frames → TFlat0ListBounded v → pos ≤ ba.size →
      match Codec0.decodeApplyFrames0 ba pos v frames with
      | .none => True
      | .done res pos' =>
        pos ≤ pos' ∧ pos' ≤ ba.size ∧
          framesPreBytes frames ++ tflatBytes v ++ baSlice ba pos pos' = tflatBytes res ∧
          TFlat0ListBounded res
      | .cont pos' frames' =>
        pos ≤ pos' ∧ pos' ≤ ba.size ∧
          framesPreBytes frames ++ tflatBytes v ++ baSlice ba pos pos' = framesPreBytes frames' ∧
          framesBounded frames'
  | [], ba, pos, v, _, hbv, hps => by
    dsimp only [Codec0.decodeApplyFrames0, framesPreBytes]
    rw [List.foldr_nil, List.nil_append, baSlice_self, List.append_nil]
    exact ⟨Nat.le_refl _, hps, rfl, hbv⟩
  | f :: rest, ba, pos, v, ⟨hbf, hbrest⟩, hbv, hps => by
    dsimp only [Codec0.decodeApplyFrames0]
    cases hf : f with
    | jnzL c =>
      dsimp only [Codec0.stepNonLinFrame0, framesPreBytes, framePreBytes,
        framesBounded, frameBounded]
      rw [List.foldr_cons, List.foldr_cons, baSlice_self, List.append_nil, List.append_assoc]
      exact ⟨Nat.le_refl _, hps, rfl, hbv, hbrest⟩
    | groupBody rem curTs doneRev =>
      dsimp only [Codec0.stepNonLinFrame0, Codec0.applyGroupBody0, Codec0.nextGroupFrame0]
      rw [hf] at hbf; rcases hbf with ⟨hlen_lt, hts, hbdone⟩
      have hblocks_eq : blocksBytes ((curTs, v) :: doneRev).reverse =
          blocksBytes doneRev.reverse ++ tyListBytes curTs ++ tflatBytes v := by
        rw [List.reverse_cons, blocksBytes_append]
        dsimp only [blocksBytes]; simp [List.append_assoc]
      have hblocks_b : Blocks0ListBounded ((curTs, v) :: doneRev).reverse := by
        rw [List.reverse_cons]; exact blocks0ListBounded_append hbdone ⟨hts, hbv, trivial⟩
      by_cases hrem0 : rem = 0
      · subst hrem0
        rw [ite_true_eq (by decide : ((0 : UInt32) == 0) = true), revBlocks0_eq, List.append_nil]
        dsimp only [framesPreBytes, framePreBytes, framesBounded, frameBounded]
        rw [List.foldr_cons, List.foldr_cons, baSlice_self, List.append_nil]; dsimp only
        have hlen_cons : ((curTs, v) :: doneRev).reverse.length < 2 ^ 32 := by simpa using hlen_lt
        have hcnt_eq : UInt32.ofNat ((curTs, v) :: doneRev).reverse.length =
            UInt32.ofNat doneRev.length + 1 + 0 := by
          simp only [List.length_reverse, List.length_cons, UInt32.add_zero]
          rw [UInt32.ofNat_add]; rfl
        refine ⟨Nat.le_refl _, hps, ?_, ⟨hlen_cons, hblocks_b⟩, hbrest⟩
        rw [hcnt_eq, hblocks_eq]; simp [List.append_assoc]
      · rw [ite_false_eq (fun hb => hrem0 (beq_iff_eq.mp hb))]
        dsimp only [Codec0.nextGroupBodyCont0]
        cases htsN : Codec0.decodeTyList0 ba pos with
        | none => simp
        | ok tsNext p1 =>
          dsimp only
          obtain ⟨h01, h1s, htsNl, hs1⟩ := decodeTyList0_ok_bytes ba pos tsNext p1 htsN
          dsimp only [framesPreBytes, framePreBytes, framesBounded, frameBounded]
          rw [List.foldr_cons, List.foldr_cons]; dsimp only
          have h1rem : 1 ≤ rem.toNat := by
            cases Nat.eq_zero_or_pos rem.toNat with
            | inl hz => exact absurd (by rw [← UInt32.ofNat_toNat (x := rem), hz]; rfl) hrem0
            | inr hp => exact hp
          have h1n : (1 : UInt32).toNat = 1 := rfl
          have hrem_b : ((curTs, v) :: doneRev).length + 1 + (rem - 1).toNat < 2 ^ 32 := by
            rw [UInt32.toNat_sub_of_le rem 1 h1rem, h1n]; simp only [List.length_cons]; omega
          have hcnt_eq : UInt32.ofNat ((curTs, v) :: doneRev).length + 1 + (rem - 1) =
              UInt32.ofNat doneRev.length + 1 + rem := by
            rw [List.length_cons, UInt32.ofNat_add, UInt32.add_assoc, UInt32.add_assoc,
              UInt32.add_comm 1 (rem - 1), UInt32.sub_add_cancel, ← UInt32.add_assoc]; rfl
          refine ⟨h01, h1s, ?_, ⟨hrem_b, htsNl, hblocks_b⟩, hbrest⟩
          rw [hcnt_eq, hblocks_eq, hs1]; simp [List.append_assoc]
    | _ =>
      have hwrap := applyLinFrame0_spec f v (by rw [hf]; trivial)
      have ih := decodeApplyFrames0_ok_bytes rest ba pos (Codec0.applyLinFrame0 f v) hbrest
        (hwrap.2.1 hbf hbv) hps
      dsimp only; rw [← hf]
      cases hdec : Codec0.decodeApplyFrames0 ba pos (Codec0.applyLinFrame0 f v) rest with
      | none => trivial
      | done _ _ =>
        rw [hdec] at ih; dsimp only at ih ⊢
        obtain ⟨h01, h1s, heq, hres⟩ := ih; refine ⟨h01, h1s, ?_, hres⟩
        rw [← heq, ← hwrap.1]; dsimp only [framesPreBytes]
        rw [List.foldr_cons]; simp only [List.append_assoc]
      | cont _ _ =>
        rw [hdec] at ih; dsimp only at ih ⊢
        obtain ⟨h01, h1s, heq, hfr⟩ := ih; refine ⟨h01, h1s, ?_, hfr⟩
        rw [← heq, ← hwrap.1]; dsimp only [framesPreBytes]
        rw [List.foldr_cons]; simp only [List.append_assoc]

private theorem decodeApplyFrames0_nodes :
    ∀ (frames : List Codec0.DecFrame0) (ba : ByteArray) (pos : Nat) (v : TFlat0),
      match Codec0.decodeApplyFrames0 ba pos v frames with
      | .none => True
      | .done res _ => tflatNodes res = framesNodes frames + tflatNodes v
      | .cont _ frames' => framesNodes frames' = framesNodes frames + tflatNodes v
  | [], ba, pos, v => by dsimp only [Codec0.decodeApplyFrames0, framesNodes]; simp
  | f :: rest, ba, pos, v => by
    dsimp only [Codec0.decodeApplyFrames0]
    cases hf : f with
    | jnzL c =>
      dsimp only [Codec0.stepNonLinFrame0, framesNodes, frameNodes]; simp [Nat.add_assoc]
    | groupBody rem curTs doneRev =>
      dsimp only [Codec0.stepNonLinFrame0, Codec0.applyGroupBody0, Codec0.nextGroupFrame0]
      by_cases hrem0 : rem = 0
      · subst hrem0; rw [ite_true_eq (by decide : ((0 : UInt32) == 0) = true),
          revBlocks0_eq, List.append_nil]
        dsimp only [framesNodes, frameNodes]
        rw [List.foldr_cons, List.foldr_cons]; dsimp only
        rw [List.reverse_cons, blocksNodes_snoc]; omega
      · rw [ite_false_eq (fun hb => hrem0 (beq_iff_eq.mp hb))]
        dsimp only [Codec0.nextGroupBodyCont0]
        cases htsN : Codec0.decodeTyList0 ba pos with
        | none => trivial
        | ok tsNext p1 =>
          dsimp only [framesNodes, frameNodes]
          rw [List.foldr_cons, List.foldr_cons]; dsimp only
          rw [List.reverse_cons, blocksNodes_snoc]; omega
    | _ =>
      have hfn := (applyLinFrame0_spec f v (by rw [hf]; trivial)).2.2
      have ih := decodeApplyFrames0_nodes rest ba pos (Codec0.applyLinFrame0 f v)
      dsimp only; rw [← hf]
      cases hdec : Codec0.decodeApplyFrames0 ba pos (Codec0.applyLinFrame0 f v) rest with
      | none => trivial
      | done _ _ =>
        rw [hdec] at ih; dsimp only at ih ⊢; rw [ih, ← hfn]; dsimp only [framesNodes]
        rw [List.foldr_cons]; omega
      | cont _ _ =>
        rw [hdec] at ih; dsimp only at ih ⊢; rw [ih, ← hfn]; dsimp only [framesNodes]
        rw [List.foldr_cons]; omega

private theorem decodeTFlatLoop0_ok_bytes :
    ∀ (fuelNat : Nat) (fuel : UInt32) (ba : ByteArray) (pos : Nat)
      (frames : List Codec0.DecFrame0) (res : TFlat0) (pos' : Nat),
      fuel.toNat = fuelNat → framesBounded frames → pos ≤ ba.size →
      Codec0.decodeTFlatLoop0 fuel ba pos frames = .ok res pos' →
      pos ≤ pos' ∧ pos' ≤ ba.size ∧
        framesPreBytes frames ++ baSlice ba pos pos' = tflatBytes res ∧
        TFlat0ListBounded res ∧ tflatNodes res ≤ fuelNat + framesNodes frames
  | 0, fuel, ba, pos, frames, res, pos', hfn, _, _, h => by
    have hz : fuel = 0 := by rw [← UInt32.ofNat_toNat (x := fuel), hfn]; rfl
    unfold Codec0.decodeTFlatLoop0 at h; rw [dite_true_eq hz] at h; cases h
  | fuelNat + 1, fuel, ba, pos, frames, res, pos', hfn, hbf, hps, h => by
    obtain ⟨hfne, hsub1⟩ := u32_sub1_toNat hfn
    rw [decodeTFlatLoop0_step fuel hfne] at h
    cases hns : Codec0.decodeNodeStep0 ba pos with
    | none => rw [hns] at h; cases h
    | push pos1 f =>
      obtain ⟨h01, h1s, hs1, hbf1, hfn1⟩ := decodeNodeStep0_ok_bytes ba pos (.push pos1 f) hns
      rw [hns] at h; dsimp only [Codec0.stepLoopFrame0] at h
      obtain ⟨h12, h2s, heq, hres, hnds⟩ :=
        decodeTFlatLoop0_ok_bytes fuelNat (fuel - 1) ba pos1 (f :: frames) res pos'
          hsub1 ⟨hbf1, hbf⟩ h1s h
      refine ⟨by omega, h2s, ?_, hres, ?_⟩
      · rw [baSlice_trans (by omega) h12, hs1, ← List.append_assoc]; exact heq
      · dsimp only [framesNodes] at hnds ⊢; rw [List.foldr_cons, hfn1] at hnds; omega
    | leaf pos1 v =>
      obtain ⟨h01, h1s, hs1, hbv1, hnv1⟩ := decodeNodeStep0_ok_bytes ba pos (.leaf pos1 v) hns
      rw [hns] at h; dsimp only [Codec0.stepLoopFrame0] at h
      have haf := decodeApplyFrames0_ok_bytes frames ba pos1 v hbf hbv1 h1s
      have hnd := decodeApplyFrames0_nodes frames ba pos1 v
      cases hda : Codec0.decodeApplyFrames0 ba pos1 v frames with
      | none => rw [hda] at h; cases h
      | done r p2 =>
        rw [hda] at h haf hnd; cases h
        obtain ⟨h12, h2s, heq, hr⟩ := haf
        refine ⟨by omega, h2s, ?_, hr, by omega⟩
        rw [baSlice_trans (by omega) h12, hs1, ← List.append_assoc]; exact heq
      | cont p2 frames' =>
        rw [hda] at h haf hnd; dsimp only at h haf hnd
        obtain ⟨h12, h2s, heq, hbf'⟩ := haf
        obtain ⟨h23, h3s, heq2, hres, hnds⟩ :=
          decodeTFlatLoop0_ok_bytes fuelNat (fuel - 1) ba p2 frames' res pos' hsub1 hbf' h2s h
        refine ⟨by omega, h3s, ?_, hres, by omega⟩
        rw [baSlice_trans (by omega) (by omega : pos1 ≤ pos'), hs1,
          baSlice_trans h12 h23, ← List.append_assoc, ← List.append_assoc, heq]
        exact heq2

private theorem decodeTFlat0_ok_bytes (ba : ByteArray) (pos : Nat) (t : TFlat0) (pos' : Nat)
    (hps : pos ≤ ba.size) (h : Codec0.decodeTFlat0 ba pos = .ok t pos') :
    pos ≤ pos' ∧ pos' ≤ ba.size ∧ TFlat0Bounded t ∧ baSlice ba pos pos' = tflatBytes t := by
  dsimp only [Codec0.decodeTFlat0] at h
  let fuel : UInt32 :=
    if ba.size - pos < 0xffffffff then UInt32.ofNat (ba.size - pos) else 0xffffffff
  obtain ⟨h01, h1s, heq, htl, hnds⟩ :=
    decodeTFlatLoop0_ok_bytes fuel.toNat fuel ba pos [] t pos' rfl trivial hps h
  have hfuel_le : fuel.toNat ≤ 0xffffffff := by have hlt := fuel.toNat_lt; omega
  dsimp only [framesPreBytes, List.foldr_nil, List.nil_append, framesNodes] at heq hnds
  exact ⟨h01, h1s, ⟨htl, by omega⟩, heq⟩

/-! ## 5. Function, Extern, and Module Codecs (`ExtSig0`, `TFlatFn0`, `TFlatModule0`) -/

private def extBytes (ex : ExtSig0) : List UInt8 :=
  u32Bytes ex.name ++ tyListBytes ex.as ++ tyListBytes ex.rs

private def extSeqBytes : List ExtSig0 → List UInt8
  | [] => []
  | ex :: rest => extBytes ex ++ extSeqBytes rest

private def extListBytes (xs : List ExtSig0) : List UInt8 :=
  u32Bytes (UInt32.ofNat xs.length) ++ extSeqBytes xs

private def fnBytes (fn : TFlatFn0) : List UInt8 :=
  u32Bytes fn.name ++ tyListBytes fn.as ++ tyListBytes fn.rs ++ tflatBytes fn.body

private def fnSeqBytes : List TFlatFn0 → List UInt8
  | [] => []
  | fn :: rest => fnBytes fn ++ fnSeqBytes rest

private def fnListBytes (xs : List TFlatFn0) : List UInt8 :=
  u32Bytes (UInt32.ofNat xs.length) ++ fnSeqBytes xs

private def modBytes (m : TFlatModule0) : List UInt8 :=
  headerBytes ++ fnListBytes m.fns ++ extListBytes m.externs ++ symListBytes m.exits

private theorem lenExtsU32_eq (xs : List ExtSig0) (acc : UInt32) :
    Codec0.lenExtsU32 xs acc = acc + UInt32.ofNat xs.length := by
  induction xs generalizing acc with
  | nil => exact (UInt32.add_zero acc).symm
  | cons _ _ ih =>
    dsimp only [Codec0.lenExtsU32]
    rw [ih (acc + 1), List.length_cons, Nat.add_comm, UInt32.ofNat_add, UInt32.add_assoc]; rfl

private theorem lenFnsU32_eq (xs : List TFlatFn0) (acc : UInt32) :
    Codec0.lenFnsU32 xs acc = acc + UInt32.ofNat xs.length := by
  induction xs generalizing acc with
  | nil => exact (UInt32.add_zero acc).symm
  | cons _ _ ih =>
    dsimp only [Codec0.lenFnsU32]
    rw [ih (acc + 1), List.length_cons, Nat.add_comm, UInt32.ofNat_add, UInt32.add_assoc]; rfl

private theorem encodeExt0_bytes (ba : ByteArray) (ex : ExtSig0) :
    (Codec0.encodeExt0 ba ex).data.toList = ba.data.toList ++ extBytes ex := by
  dsimp only [Codec0.encodeExt0, extBytes]
  rw [encodeTyList0_bytes, encodeTyList0_bytes, encodeU32_bytes]
  simp only [List.append_assoc]

private theorem encodeExtListLoop0_bytes (ba : ByteArray) (xs : List ExtSig0) :
    (Codec0.encodeExtListLoop0 ba xs).data.toList = ba.data.toList ++ extSeqBytes xs := by
  induction xs generalizing ba with
  | nil => dsimp only [Codec0.encodeExtListLoop0, extSeqBytes]; rw [List.append_nil]
  | cons ex _ ih =>
    dsimp only [Codec0.encodeExtListLoop0, extSeqBytes]
    rw [ih, encodeExt0_bytes, List.append_assoc]

private theorem encodeExtList0_bytes (ba : ByteArray) (xs : List ExtSig0) :
    (Codec0.encodeExtList0 ba xs).data.toList = ba.data.toList ++ extListBytes xs := by
  dsimp only [Codec0.encodeExtList0, extListBytes]
  rw [encodeExtListLoop0_bytes, encodeU32_bytes, lenExtsU32_eq, UInt32.zero_add, List.append_assoc]

private theorem encodeFn0_bytes (ba : ByteArray) (fn : TFlatFn0) :
    (Codec0.encodeFn0 ba fn).data.toList = ba.data.toList ++ fnBytes fn := by
  dsimp only [Codec0.encodeFn0, fnBytes]
  rw [encodeTFlat0_bytes, encodeTyList0_bytes, encodeTyList0_bytes, encodeU32_bytes]
  simp only [List.append_assoc]

private theorem encodeFnListLoop0_bytes (ba : ByteArray) (xs : List TFlatFn0) :
    (Codec0.encodeFnListLoop0 ba xs).data.toList = ba.data.toList ++ fnSeqBytes xs := by
  induction xs generalizing ba with
  | nil => dsimp only [Codec0.encodeFnListLoop0, fnSeqBytes]; rw [List.append_nil]
  | cons fn _ ih =>
    dsimp only [Codec0.encodeFnListLoop0, fnSeqBytes]; rw [ih, encodeFn0_bytes, List.append_assoc]

private theorem encodeFnList0_bytes (ba : ByteArray) (xs : List TFlatFn0) :
    (Codec0.encodeFnList0 ba xs).data.toList = ba.data.toList ++ fnListBytes xs := by
  dsimp only [Codec0.encodeFnList0, fnListBytes]
  rw [encodeFnListLoop0_bytes, encodeU32_bytes, lenFnsU32_eq, UInt32.zero_add, List.append_assoc]

private theorem encodeMod0_bytes (m : TFlatModule0) : (encodeMod0 m).data.toList = modBytes m := by
  dsimp only [encodeMod0, modBytes]
  rw [encodeSymList0_bytes, encodeExtList0_bytes, encodeFnList0_bytes, encodeHeader_bytes,
    ba_emptyWithCapacity_data_toList, List.nil_append, List.append_assoc, List.append_assoc]

private theorem revExts0_eq (xs acc : List ExtSig0) :
    Codec0.revExts0 xs acc = xs.reverse ++ acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x _ ih => dsimp only [Codec0.revExts0]; rw [ih, List.reverse_cons, List.append_assoc]; rfl

private theorem revFns0_eq (xs acc : List TFlatFn0) :
    Codec0.revFns0 xs acc = xs.reverse ++ acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x _ ih => dsimp only [Codec0.revFns0]; rw [ih, List.reverse_cons, List.append_assoc]; rfl

private theorem decodeExt0_of_bytes (ba : ByteArray) (pos : Nat) (ex : ExtSig0)
    (rest : List UInt8) (hb : ExtSig0Bounded ex)
    (h : ba.data.toList.drop pos = extBytes ex ++ rest) :
    Codec0.decodeExt0 ba pos = .ok ex (pos + (extBytes ex).length) := by
  dsimp only [extBytes] at h ⊢; rw [List.append_assoc, List.append_assoc] at h
  have hd1 : ba.data.toList.drop (pos + 4) = tyListBytes ex.as ++ (tyListBytes ex.rs ++ rest) := by
    rw [drop_pos_add, h]; exact List.drop_left' rfl
  have hd2 : ba.data.toList.drop (pos + 4 + (tyListBytes ex.as).length) =
      tyListBytes ex.rs ++ rest := by rw [drop_pos_add, hd1, List.drop_left]
  dsimp only [Codec0.decodeExt0, Codec0.decodeCallSig0, Codec0.decodeSymTys0]
  rw [decodeU32_of_bytes ba pos ex.name _ h]; dsimp only
  rw [decodeTyList0_of_bytes ba (pos + 4) ex.as _ hb.1 hd1]; dsimp only
  rw [decodeTyList0_of_bytes ba _ ex.rs rest hb.2 hd2]
  simp only [List.length_append, u32Bytes_length, Nat.add_assoc]

private theorem decodeExt0_ok_bytes (ba : ByteArray) (pos : Nat) (ex : ExtSig0) (pos' : Nat)
    (h : Codec0.decodeExt0 ba pos = .ok ex pos') :
    pos ≤ pos' ∧ pos' ≤ ba.size ∧ ExtSig0Bounded ex ∧ baSlice ba pos pos' = extBytes ex := by
  dsimp only [Codec0.decodeExt0, Codec0.decodeCallSig0, Codec0.decodeSymTys0] at h
  cases hu : Codec0.decodeU32 ba pos with
  | none => rw [hu] at h; cases h | ok name p1 =>
    rw [hu] at h; dsimp only at h
    cases has : Codec0.decodeTyList0 ba p1 with
    | none => rw [has] at h; cases h | ok as p2 =>
      rw [has] at h; dsimp only at h
      cases hrs : Codec0.decodeTyList0 ba p2 with
      | none => rw [hrs] at h; cases h | ok rs p3 =>
        rw [hrs] at h
        obtain ⟨_, _, hp1, hs1⟩ := decodeU32_ok_bytes ba pos name p1 hu; subst hp1
        obtain ⟨h12, _, hb1, hs2⟩ := decodeTyList0_ok_bytes ba (pos + 4) as p2 has
        obtain ⟨h23, h3s, hb2, hs3⟩ := decodeTyList0_ok_bytes ba p2 rs p3 hrs
        cases h; refine ⟨by omega, h3s, ⟨hb1, hb2⟩, ?_⟩
        rw [baSlice_trans (by omega) (by omega : pos + 4 ≤ pos'), hs1,
          baSlice_trans h12 h23, hs2, hs3]; dsimp only [extBytes]; simp only [List.append_assoc]

private theorem decodeFn0_of_bytes (ba : ByteArray) (pos : Nat) (fn : TFlatFn0)
    (rest : List UInt8) (hb : Fn0Bounded fn) (h : ba.data.toList.drop pos = fnBytes fn ++ rest) :
    Codec0.decodeFn0 ba pos = .ok fn (pos + (fnBytes fn).length) := by
  dsimp only [fnBytes] at h ⊢; rw [List.append_assoc, List.append_assoc] at h
  let ex : ExtSig0 := { name := fn.name, as := fn.as, rs := fn.rs }
  have hd_ex : ba.data.toList.drop pos = extBytes ex ++ (tflatBytes fn.body ++ rest) := by
    dsimp only [ex, extBytes]; rw [h]; simp only [List.append_assoc]
  have hd_body : ba.data.toList.drop (pos + (extBytes ex).length) = tflatBytes fn.body ++ rest := by
    rw [drop_pos_add, hd_ex, List.drop_left]
  dsimp only [Codec0.decodeFn0]
  rw [decodeExt0_of_bytes ba pos ex _ ⟨hb.1, hb.2.1⟩ hd_ex]; dsimp only
  rw [decodeTFlat0_of_bytes ba _ fn.body rest hb.2.2 hd_body]
  dsimp only [ex, extBytes]; simp only [List.length_append, Nat.add_assoc]

private theorem decodeFn0_ok_bytes (ba : ByteArray) (pos : Nat) (fn : TFlatFn0) (pos' : Nat)
    (h : Codec0.decodeFn0 ba pos = .ok fn pos') :
    pos ≤ pos' ∧ pos' ≤ ba.size ∧ Fn0Bounded fn ∧ baSlice ba pos pos' = fnBytes fn := by
  dsimp only [Codec0.decodeFn0] at h
  cases hex : Codec0.decodeExt0 ba pos with
  | none => rw [hex] at h; cases h | ok hdr p1 =>
    rw [hex] at h; dsimp only at h
    cases hbd : Codec0.decodeTFlat0 ba p1 with
    | none => rw [hbd] at h; cases h | ok body p2 =>
      rw [hbd] at h
      obtain ⟨h01, h1s, hbh, hs1⟩ := decodeExt0_ok_bytes ba pos hdr p1 hex
      obtain ⟨h12, h2s, hbb, hs2⟩ := decodeTFlat0_ok_bytes ba p1 body p2 h1s hbd
      cases h; refine ⟨by omega, h2s, ⟨hbh.1, hbh.2, hbb⟩, ?_⟩
      rw [baSlice_trans h01 h12, hs1, hs2]; rfl

private theorem decodeExtListLoop0_of_bytes (ba : ByteArray) :
    ∀ (xs acc : List ExtSig0) (pos : Nat) (rem : UInt32) (rest : List UInt8),
      rem.toNat = xs.length → (∀ ex ∈ xs, ExtSig0Bounded ex) →
      ba.data.toList.drop pos = extSeqBytes xs ++ rest →
      Codec0.decodeExtListLoop0 ba pos rem acc =
        .ok (acc.reverse ++ xs) (pos + (extSeqBytes xs).length)
  | [], acc, pos, rem, _, hlen, _, _ => by
    have hz : rem = 0 := UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hlen)
    unfold Codec0.decodeExtListLoop0; rw [dite_true_eq hz, revExts0_eq, List.append_nil]; rfl
  | ex :: xs, acc, pos, rem, rest, hlen, hbx, hdrop => by
    obtain ⟨hpos, hrem1⟩ := u32_sub1_toNat (by simpa using hlen)
    dsimp only [extSeqBytes] at hdrop ⊢; rw [List.append_assoc] at hdrop
    have hd1 : ba.data.toList.drop (pos + (extBytes ex).length) = extSeqBytes xs ++ rest := by
      rw [drop_pos_add, hdrop, List.drop_left]
    unfold Codec0.decodeExtListLoop0
    rw [dite_false_eq hpos, decodeExt0_of_bytes ba pos ex _ (hbx ex (by simp)) hdrop]; dsimp only
    rw [decodeExtListLoop0_of_bytes ba xs (ex :: acc) _ (rem - 1) rest hrem1
      (fun e he => hbx e (by simp [he])) hd1]
    simp only [List.length_append, List.reverse_cons, List.append_assoc, List.cons_append,
      List.nil_append, Nat.add_assoc]

private theorem decodeExtList0_of_bytes (ba : ByteArray) (pos : Nat) (xs : List ExtSig0)
    (rest : List UInt8) (hlen_lt : xs.length < 2 ^ 32) (hbx : ∀ ex ∈ xs, ExtSig0Bounded ex)
    (h : ba.data.toList.drop pos = extListBytes xs ++ rest) :
    Codec0.decodeExtList0 ba pos = .ok xs (pos + (extListBytes xs).length) := by
  dsimp only [extListBytes] at h ⊢; rw [List.append_assoc] at h
  have hd1 : ba.data.toList.drop (pos + 4) = extSeqBytes xs ++ rest := by
    rw [drop_pos_add, h]; exact List.drop_left' rfl
  have hlen : (UInt32.ofNat xs.length).toNat = xs.length := by
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hlen_lt]
  dsimp only [Codec0.decodeExtList0]
  rw [decodeU32_of_bytes ba pos (UInt32.ofNat xs.length) _ h]; dsimp only
  rw [decodeExtListLoop0_of_bytes ba xs [] (pos + 4) (UInt32.ofNat xs.length) rest hlen hbx hd1]
  simp only [List.reverse_nil, List.nil_append, List.length_append, u32Bytes_length, Nat.add_assoc]

private theorem decodeExtListLoop0_ok_bytes (ba : ByteArray) :
    ∀ (n pos : Nat) (rem : UInt32) (acc res : List ExtSig0) (pos' : Nat),
      rem.toNat = n → Codec0.decodeExtListLoop0 ba pos rem acc = .ok res pos' →
      pos ≤ pos' ∧ (pos ≤ ba.size → pos' ≤ ba.size) ∧
        ∃ tail : List ExtSig0, tail.length = n ∧ res = acc.reverse ++ tail ∧
          (∀ ex ∈ tail, ExtSig0Bounded ex) ∧ baSlice ba pos pos' = extSeqBytes tail
  | 0, pos, rem, acc, res, pos', hn, h => by
    have hz : rem = 0 := UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hn)
    unfold Codec0.decodeExtListLoop0 at h; rw [dite_true_eq hz, revExts0_eq] at h; cases h
    exact ⟨Nat.le_refl _, fun hp => hp, [], rfl, rfl, (fun _ h => by cases h), baSlice_self ba pos⟩
  | n + 1, pos, rem, acc, res, pos', hn, h => by
    obtain ⟨hne, hrem1⟩ := u32_sub1_toNat hn
    unfold Codec0.decodeExtListLoop0 at h; rw [dite_false_eq hne] at h
    cases hex : Codec0.decodeExt0 ba pos with
    | none => rw [hex] at h; cases h | ok ex p1 =>
      rw [hex] at h; dsimp only at h
      obtain ⟨h01, h1s, hbx, hs1⟩ := decodeExt0_ok_bytes ba pos ex p1 hex
      obtain ⟨h12, h2s, tail, hlen, hres, hbt, hs2⟩ :=
        decodeExtListLoop0_ok_bytes ba n p1 (rem - 1) (ex :: acc) res pos' hrem1 h
      refine ⟨by omega, fun _ => h2s h1s, ex :: tail, by simp [hlen], ?_, ?_, ?_⟩
      · rw [hres]; simp [List.reverse_cons, List.append_assoc]
      · intro e he; simp only [List.mem_cons] at he
        rcases he with rfl | he; exact hbx; exact hbt e he
      · rw [baSlice_trans h01 h12, hs1, hs2]; rfl

private theorem decodeExtList0_ok_bytes (ba : ByteArray) (pos : Nat)
    (xs : List ExtSig0) (pos' : Nat) (h : Codec0.decodeExtList0 ba pos = .ok xs pos') :
    pos ≤ pos' ∧ pos' ≤ ba.size ∧ xs.length < 2 ^ 32 ∧
      (∀ ex ∈ xs, ExtSig0Bounded ex) ∧ baSlice ba pos pos' = extListBytes xs := by
  dsimp only [Codec0.decodeExtList0] at h
  cases hu : Codec0.decodeU32 ba pos with
  | none => rw [hu] at h; cases h | ok cnt p1 =>
    rw [hu] at h; dsimp only at h
    obtain ⟨_, h1s, hp1, hs1⟩ := decodeU32_ok_bytes ba pos cnt p1 hu; subst hp1
    obtain ⟨h12, h2s, tail, hlen, hres, hbt, hs2⟩ :=
      decodeExtListLoop0_ok_bytes ba cnt.toNat (pos + 4) cnt [] xs pos' rfl h
    rw [List.reverse_nil, List.nil_append] at hres; subst xs
    have hlt : tail.length < 2 ^ 32 := by rw [hlen]; exact cnt.toNat_lt
    have hcnt : UInt32.ofNat tail.length = cnt := u32_ofNat_eq hlen
    refine ⟨by omega, h2s h1s, hlt, hbt, ?_⟩
    rw [baSlice_trans (by omega) h12, hs1, hs2]; dsimp only [extListBytes]; rw [hcnt]

private theorem decodeFnListLoop0_of_bytes (ba : ByteArray) :
    ∀ (xs acc : List TFlatFn0) (pos : Nat) (rem : UInt32) (rest : List UInt8),
      rem.toNat = xs.length → (∀ fn ∈ xs, Fn0Bounded fn) →
      ba.data.toList.drop pos = fnSeqBytes xs ++ rest →
      Codec0.decodeFnListLoop0 ba pos rem acc =
        .ok (acc.reverse ++ xs) (pos + (fnSeqBytes xs).length)
  | [], acc, pos, rem, _, hlen, _, _ => by
    have hz : rem = 0 := UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hlen)
    unfold Codec0.decodeFnListLoop0; rw [dite_true_eq hz, revFns0_eq, List.append_nil]; rfl
  | fn :: xs, acc, pos, rem, rest, hlen, hbf, hdrop => by
    obtain ⟨hpos, hrem1⟩ := u32_sub1_toNat (by simpa using hlen)
    dsimp only [fnSeqBytes] at hdrop ⊢; rw [List.append_assoc] at hdrop
    have hd1 : ba.data.toList.drop (pos + (fnBytes fn).length) = fnSeqBytes xs ++ rest := by
      rw [drop_pos_add, hdrop, List.drop_left]
    unfold Codec0.decodeFnListLoop0
    rw [dite_false_eq hpos, decodeFn0_of_bytes ba pos fn _ (hbf fn (by simp)) hdrop]; dsimp only
    rw [decodeFnListLoop0_of_bytes ba xs (fn :: acc) _ (rem - 1) rest hrem1
      (fun f hf => hbf f (by simp [hf])) hd1]
    simp only [List.length_append, List.reverse_cons, List.append_assoc, List.cons_append,
      List.nil_append, Nat.add_assoc]

private theorem decodeFnList0_of_bytes (ba : ByteArray) (pos : Nat) (xs : List TFlatFn0)
    (rest : List UInt8) (hlen_lt : xs.length < 2 ^ 32) (hbf : ∀ fn ∈ xs, Fn0Bounded fn)
    (h : ba.data.toList.drop pos = fnListBytes xs ++ rest) :
    Codec0.decodeFnList0 ba pos = .ok xs (pos + (fnListBytes xs).length) := by
  dsimp only [fnListBytes] at h ⊢; rw [List.append_assoc] at h
  have hd1 : ba.data.toList.drop (pos + 4) = fnSeqBytes xs ++ rest := by
    rw [drop_pos_add, h]; exact List.drop_left' rfl
  have hlen : (UInt32.ofNat xs.length).toNat = xs.length := by
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hlen_lt]
  dsimp only [Codec0.decodeFnList0]
  rw [decodeU32_of_bytes ba pos (UInt32.ofNat xs.length) _ h]; dsimp only
  rw [decodeFnListLoop0_of_bytes ba xs [] (pos + 4) (UInt32.ofNat xs.length) rest hlen hbf hd1]
  simp only [List.reverse_nil, List.nil_append, List.length_append, u32Bytes_length, Nat.add_assoc]

private theorem decodeFnListLoop0_ok_bytes (ba : ByteArray) :
    ∀ (n pos : Nat) (rem : UInt32) (acc res : List TFlatFn0) (pos' : Nat),
      rem.toNat = n → Codec0.decodeFnListLoop0 ba pos rem acc = .ok res pos' →
      pos ≤ pos' ∧ (pos ≤ ba.size → pos' ≤ ba.size) ∧
        ∃ tail : List TFlatFn0, tail.length = n ∧ res = acc.reverse ++ tail ∧
          (∀ fn ∈ tail, Fn0Bounded fn) ∧ baSlice ba pos pos' = fnSeqBytes tail
  | 0, pos, rem, acc, res, pos', hn, h => by
    have hz : rem = 0 := UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hn)
    unfold Codec0.decodeFnListLoop0 at h; rw [dite_true_eq hz, revFns0_eq] at h; cases h
    exact ⟨Nat.le_refl _, fun hp => hp, [], rfl, rfl, (fun _ h => by cases h), baSlice_self ba pos⟩
  | n + 1, pos, rem, acc, res, pos', hn, h => by
    obtain ⟨hne, hrem1⟩ := u32_sub1_toNat hn
    unfold Codec0.decodeFnListLoop0 at h; rw [dite_false_eq hne] at h
    cases hfn : Codec0.decodeFn0 ba pos with
    | none => rw [hfn] at h; cases h | ok fn p1 =>
      rw [hfn] at h; dsimp only at h
      obtain ⟨h01, h1s, hbf, hs1⟩ := decodeFn0_ok_bytes ba pos fn p1 hfn
      obtain ⟨h12, h2s, tail, hlen, hres, hbt, hs2⟩ :=
        decodeFnListLoop0_ok_bytes ba n p1 (rem - 1) (fn :: acc) res pos' hrem1 h
      refine ⟨by omega, fun _ => h2s h1s, fn :: tail, by simp [hlen], ?_, ?_, ?_⟩
      · rw [hres]; simp [List.reverse_cons, List.append_assoc]
      · intro f hf; simp only [List.mem_cons] at hf
        rcases hf with rfl | hf; exact hbf; exact hbt f hf
      · rw [baSlice_trans h01 h12, hs1, hs2]; rfl

private theorem decodeFnList0_ok_bytes (ba : ByteArray) (pos : Nat)
    (xs : List TFlatFn0) (pos' : Nat) (h : Codec0.decodeFnList0 ba pos = .ok xs pos') :
    pos ≤ pos' ∧ pos' ≤ ba.size ∧ xs.length < 2 ^ 32 ∧
      (∀ fn ∈ xs, Fn0Bounded fn) ∧ baSlice ba pos pos' = fnListBytes xs := by
  dsimp only [Codec0.decodeFnList0] at h
  cases hu : Codec0.decodeU32 ba pos with
  | none => rw [hu] at h; cases h | ok cnt p1 =>
    rw [hu] at h; dsimp only at h
    obtain ⟨_, h1s, hp1, hs1⟩ := decodeU32_ok_bytes ba pos cnt p1 hu; subst hp1
    obtain ⟨h12, h2s, tail, hlen, hres, hbt, hs2⟩ :=
      decodeFnListLoop0_ok_bytes ba cnt.toNat (pos + 4) cnt [] xs pos' rfl h
    rw [List.reverse_nil, List.nil_append] at hres; subst xs
    have hlt : tail.length < 2 ^ 32 := by rw [hlen]; exact cnt.toNat_lt
    have hcnt : UInt32.ofNat tail.length = cnt := u32_ofNat_eq hlen
    refine ⟨by omega, h2s h1s, hlt, hbt, ?_⟩
    rw [baSlice_trans (by omega) h12, hs1, hs2]; dsimp only [fnListBytes]; rw [hcnt]

/-! ## 6. Verified Round-Trip, Determinism, and Injectivity Theorems -/

private theorem decodeMod0_some_bytes {ba : ByteArray} {m : TFlatModule0}
    (h : decodeMod0 ba = some m) : Mod0Bounded m ∧ ba.data.toList = modBytes m := by
  dsimp only [decodeMod0] at h
  by_cases hhdr : Codec0.checkHeader ba = true
  · rw [ite_true_eq hhdr] at h
    obtain ⟨_, hs0⟩ := checkHeader_ok_bytes ba hhdr
    dsimp only [Codec0.decodeModBody0, Codec0.decodeModTail0, Codec0.decodeModExits0,
      Codec0.mkModIfEof0] at h
    cases hfns : Codec0.decodeFnList0 ba 5 with
    | none => rw [hfns] at h; cases h | ok fns p1 =>
      rw [hfns] at h; dsimp only at h
      cases hexts : Codec0.decodeExtList0 ba p1 with
      | none => rw [hexts] at h; cases h | ok exts p2 =>
        rw [hexts] at h; dsimp only at h
        cases hexits : Codec0.decodeSymList0 ba p2 with
        | none => rw [hexits] at h; cases h | ok exits p3 =>
          rw [hexits] at h; dsimp only at h
          by_cases heof : p3 = ba.size
          · rw [ite_true_eq (beq_iff_eq.mpr heof)] at h; cases h
            obtain ⟨h51, _, hlf, hbf, hs1⟩ := decodeFnList0_ok_bytes ba 5 fns p1 hfns
            obtain ⟨h12, _, hle, hbe, hs2⟩ := decodeExtList0_ok_bytes ba p1 exts p2 hexts
            obtain ⟨h23, _, hlx, hs3⟩ := decodeSymList0_ok_bytes ba p2 exits p3 hexits
            refine ⟨⟨hlf, hle, hlx, hbf, hbe⟩, ?_⟩
            rw [← baSlice_zero_self ba, ← heof,
              baSlice_trans (Nat.zero_le 5) (by omega : 5 ≤ p3), hs0,
              baSlice_trans h51 (by omega : p1 ≤ p3), hs1,
              baSlice_trans h12 h23, hs2, hs3]
            dsimp only [modBytes]; simp only [List.append_assoc]
          · rw [ite_false_eq (fun hb => heof (beq_iff_eq.mp hb))] at h; cases h
  · rw [ite_false_eq hhdr] at h; cases h

/-- Verified encoder/decoder round-trip for every 32-bit bounded `TFlatModule0`. -/
public theorem decodeMod0_encodeMod0 (m : TFlatModule0) (hm : Mod0Bounded m) :
    decodeMod0 (encodeMod0 m) = some m := by
  let ba := encodeMod0 m
  have hba : ba.data.toList = modBytes m := encodeMod0_bytes m
  have hd0 : ba.data.toList = headerBytes ++
      (fnListBytes m.fns ++ extListBytes m.externs ++ symListBytes m.exits) := by
    dsimp only [modBytes] at hba; rw [hba]; simp only [List.append_assoc]
  have hd1 : ba.data.toList.drop 5 =
      fnListBytes m.fns ++ (extListBytes m.externs ++ symListBytes m.exits) := by
    have := congrArg (List.drop 5) hd0
    dsimp only [headerBytes] at this
    simpa [List.append_assoc] using this
  have hd2 : ba.data.toList.drop (5 + (fnListBytes m.fns).length) =
      extListBytes m.externs ++ symListBytes m.exits := by rw [drop_pos_add, hd1, List.drop_left]
  have hd3 : ba.data.toList.drop
      (5 + (fnListBytes m.fns).length + (extListBytes m.externs).length) =
      symListBytes m.exits := by rw [drop_pos_add, hd2, List.drop_left]
  have heof : 5 + (fnListBytes m.fns).length + (extListBytes m.externs).length +
      (symListBytes m.exits).length = ba.size := by
    rw [← ba_data_toList_length ba, hba]
    dsimp only [modBytes, headerBytes]
    simp only [List.length_append, List.length_cons, List.length_nil]
  dsimp only [decodeMod0]
  rw [ite_true_eq (checkHeader_of_bytes ba _ hd0)]
  dsimp only [Codec0.decodeModBody0, Codec0.decodeModTail0, Codec0.decodeModExits0,
    Codec0.mkModIfEof0]
  rw [decodeFnList0_of_bytes ba 5 m.fns _ hm.1 hm.2.2.2.1 hd1]; dsimp only
  rw [decodeExtList0_of_bytes ba _ m.externs _ hm.2.1 hm.2.2.2.2 hd2]; dsimp only
  rw [decodeSymList0_of_bytes ba _ m.exits [] hm.2.2.1 (by simpa using hd3)]; dsimp only
  rw [ite_true_eq (beq_iff_eq.mpr heof)]

/-- Any successfully decoded byte buffer represents a `Mod0Bounded` module. -/
public theorem decodeMod0_some_bounded {ba : ByteArray} {m : TFlatModule0}
    (h : decodeMod0 ba = some m) : Mod0Bounded m := (decodeMod0_some_bytes h).1

/-- Canonical inverse: decoding is canonical (`encodeMod0 (decodeMod0 ba) = ba`). -/
public theorem encodeMod0_decodeMod0 {ba : ByteArray} {m : TFlatModule0}
    (h : decodeMod0 ba = some m) : encodeMod0 m = ba := by
  apply ba_eq_of_data_toList; rw [encodeMod0_bytes, (decodeMod0_some_bytes h).2]

/-- Injectivity of `encodeMod0` on `Mod0Bounded` modules. -/
public theorem encodeMod0_inj {m₁ m₂ : TFlatModule0}
    (h₁ : Mod0Bounded m₁) (h₂ : Mod0Bounded m₂) (heq : encodeMod0 m₁ = encodeMod0 m₂) :
    m₁ = m₂ := by
  have hdec : decodeMod0 (encodeMod0 m₁) = some m₁ := decodeMod0_encodeMod0 m₁ h₁
  rw [heq, decodeMod0_encodeMod0 m₂ h₂] at hdec; cases hdec; rfl

/-- Determinism / injectivity of `decodeMod0`: equal decoded modules come from equal buffers. -/
public theorem decodeMod0_inj {ba₁ ba₂ : ByteArray} {m : TFlatModule0}
    (h₁ : decodeMod0 ba₁ = some m) (h₂ : decodeMod0 ba₂ = some m) : ba₁ = ba₂ := by
  rw [← encodeMod0_decodeMod0 h₁, encodeMod0_decodeMod0 h₂]

/-- Exact characterization of `decodeMod0` on `Mod0Bounded` modules. -/
public theorem decodeMod0_encodeMod0_iff {m : TFlatModule0} (hm : Mod0Bounded m) {ba : ByteArray} :
    decodeMod0 ba = some m ↔ ba = encodeMod0 m := by
  constructor
  · intro h; exact (encodeMod0_decodeMod0 h).symm
  · intro h; subst h; exact decodeMod0_encodeMod0 m hm

end LeanQbe.T.Bootstrap0
