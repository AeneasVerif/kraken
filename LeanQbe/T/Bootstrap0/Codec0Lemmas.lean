module

public import LeanQbe.T.Bootstrap0.Codec0
public import LeanQbe.T.Bootstrap0.Codec0Lemmas1
import LeanQbe.T.Bootstrap0.Codec0Kit

/-!
# Verified Round-Trip, Determinism, and Injectivity Proofs for `Codec0`

Proves that `Codec0`'s iterative `LQB0` binary encoder (`encodeMod0`) and decoder (`decodeMod0`)
form an exact canonical bijection on `Mod0Bounded` `TFlatModule0`s:

* `decodeMod0_encodeMod0`: `Mod0Bounded m → decodeMod0 (encodeMod0 m) = some m`.
* `encodeMod0_decodeMod0`: `decodeMod0 ba = some m → encodeMod0 m = ba`.
* `decodeMod0_some_bounded`: `decodeMod0 ba = some m → Mod0Bounded m`.
* `encodeMod0_inj` / `decodeMod0_inj` / `decodeMod0_encodeMod0_iff`: injectivity, determinism,
  and canonical uniqueness (`0` sorry, `[propext, Classical.choice, Quot.sound]`, clean `.olean`
  exports).
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
  | group bodies _ =>
    dsimp only [Codec0.encodeLinearHdr0]
    rw [encodeU32_bytes, ba_push_data_toList, Codec0Kit.lenU32_eq_of_steps Codec0.lenBlocksU32
      (fun _ => rfl) (fun _ _ _ => rfl), UInt32.zero_add]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  | _ =>
    dsimp only [Codec0.encodeLinearHdr0, Codec0.encodeLet1Hdr0, Codec0.encodeStoreHdr0,
      Codec0.encodeCallHdr0, Codec0.encodeLeafNode0, Codec0.encodeSigArgs0]
    simp only [encodeOpCode0_bytes, encodeArgList0_bytes, encodeArg0_bytes, encodeTy0_bytes,
      encodeTyList0_bytes, encodeU32_bytes, ba_push_data_toList,
      List.append_assoc, List.cons_append, List.nil_append]

private theorem encodeWorkStep0_lt (ba : ByteArray) (item : Codec0.EncItem0)
    (rest : List Codec0.EncItem0) :
    Codec0.encWorkWeight (Codec0.encodeWorkStep0 ba item rest).2 <
      Codec0.encWorkWeight (item :: rest) := by
  cases item with
  | blocks bs =>
    cases bs <;> dsimp only [Codec0.encodeWorkStep0, Codec0.encodeBlocksStep0,
      Codec0.mkBlockCont0, Codec0.encWorkWeight, Codec0.blocksWeight] <;> omega
  | node t =>
    cases t <;> dsimp only [Codec0.encodeWorkStep0, Codec0.pushEncChildren0,
      Codec0.pushEncLinChildren0, Codec0.encWorkWeight, Codec0.tflatWeight] <;> omega

private theorem encodeTFlatWork0_bytes_aux :
    ∀ (w : Nat) (work : List Codec0.EncItem0) (ba : ByteArray),
      Codec0.encWorkWeight work = w →
      (Codec0.encodeTFlatWork0 ba work).data.toList = ba.data.toList ++ encWorkBytes work :=
  Codec0Kit.worklist_enc_bytes_of_steps Codec0.encodeTFlatWork0 Codec0.encodeWorkStep0
    Codec0.encWorkWeight encWorkBytes (fun _ => by unfold Codec0.encodeTFlatWork0; rfl)
    (fun b item rest => by conv => lhs; unfold Codec0.encodeTFlatWork0) rfl
    encodeWorkStep0_lt fun ba item rest => by
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

private theorem decodeSymTys0_of_bytes (ba : ByteArray) (pos : Nat) (fnSym : Sym0)
    (as : List Ty0) (rest : List UInt8) (ha : as.length < 2 ^ 32)
    (h : ba.data.toList.drop pos = u32Bytes fnSym ++ (tyListBytes as ++ rest)) :
    Codec0.decodeSymTys0 ba pos = .ok fnSym as (pos + 4 + (tyListBytes as).length) := by
  have hd := Codec0Kit.drop_append_step h; rw [u32Bytes_length] at hd
  dsimp only [Codec0.decodeSymTys0]
  rw [decodeU32_of_bytes ba pos fnSym _ h]; dsimp only
  rw [decodeTyList0_of_bytes ba (pos + 4) as rest ha hd, Nat.add_assoc]

private theorem decodeCallSig0_of_bytes (ba : ByteArray) (pos : Nat) (fnSym : Sym0)
    (as bs : List Ty0) (rest : List UInt8) (ha : as.length < 2 ^ 32) (hb : bs.length < 2 ^ 32)
    (h : ba.data.toList.drop pos =
      u32Bytes fnSym ++ (tyListBytes as ++ (tyListBytes bs ++ rest))) :
    Codec0.decodeCallSig0 ba pos =
      .ok fnSym as bs (pos + 4 + (tyListBytes as).length + (tyListBytes bs).length) := by
  have hd1 := Codec0Kit.drop_append_step h; rw [u32Bytes_length] at hd1
  have hd2 := Codec0Kit.drop_append_step hd1
  dsimp only [Codec0.decodeCallSig0]
  rw [decodeSymTys0_of_bytes ba pos fnSym as _ ha h]; dsimp only
  rw [decodeTyList0_of_bytes ba (pos + 4 + (tyListBytes as).length) bs rest hb hd2]

private theorem decodeLoop_linPush {ba : ByteArray} {pos pos1 : Nat}
    {f : Codec0.DecFrame0} {t k : TFlat0} {frames : List Codec0.DecFrame0} {fuel : UInt32}
    (hih : Codec0.decodeTFlatLoop0 (fuel - 1) ba pos1 (f :: frames) =
      frameApplyResult ba (pos1 + (tflatBytes k).length) k (f :: frames) (fuel - 1))
    (happly : Codec0.decodeApplyFrames0 ba (pos1 + (tflatBytes k).length) k (f :: frames) =
      Codec0.decodeApplyFrames0 ba (pos1 + (tflatBytes k).length) t frames)
    (hnodes : tflatNodes t = 1 + tflatNodes k)
    (hlen : pos1 + (tflatBytes k).length = pos + (tflatBytes t).length)
    (hfuel : tflatNodes t ≤ fuel.toNat)
    (hstep : Codec0.decodeNodeStep0 ba pos = .push pos1 f) :
    Codec0.decodeTFlatLoop0 fuel ba pos frames =
      frameApplyResult ba (pos + (tflatBytes t).length) t frames fuel := by
  have hf0 : fuel ≠ 0 := Codec0Kit.u32_ne_zero_of_toNat_pos (by omega)
  rw [decodeTFlatLoop0_step fuel hf0 ba pos frames, hstep]; dsimp only [Codec0.stepLoopFrame0]
  rw [hih]; dsimp only [frameApplyResult]
  rw [happly, hlen, Codec0Kit.u32_sub1_sub (by omega), ← hnodes]

private theorem decodeLoop_leaf {ba : ByteArray} {pos : Nat} {t : TFlat0}
    {frames : List Codec0.DecFrame0} {fuel : UInt32}
    (hfuel : 1 ≤ fuel.toNat) (hnodes : tflatNodes t = 1)
    (hstep : Codec0.decodeNodeStep0 ba pos = .leaf (pos + (tflatBytes t).length) t) :
    Codec0.decodeTFlatLoop0 fuel ba pos frames =
      frameApplyResult ba (pos + (tflatBytes t).length) t frames fuel := by
  have hf0 : fuel ≠ 0 := Codec0Kit.u32_ne_zero_of_toNat_pos hfuel
  rw [decodeTFlatLoop0_step fuel hf0 ba pos frames, hstep]
  dsimp only [Codec0.stepLoopFrame0, frameApplyResult]; rw [hnodes]; rfl

private theorem decodeLoop_tailOrExit (isExit : Bool) (ba : ByteArray) (pos : Nat)
    (f : Sym0) (as : List Ty0) (args : List Arg0) (frames : List Codec0.DecFrame0)
    (rest : List UInt8) (fuel : UInt32)
    (ha : as.length < 2 ^ 32) (hargs : args.length < 2 ^ 32) (hfuel : 1 ≤ fuel.toNat)
    (hdrop : ba.data.toList.drop pos =
      tflatBytes (if isExit then .exit f as args else .tailCall f as args) ++ rest) :
    Codec0.decodeTFlatLoop0 fuel ba pos frames =
      frameApplyResult ba
        (pos + (tflatBytes (if isExit then .exit f as args else .tailCall f as args)).length)
        (if isExit then .exit f as args else .tailCall f as args) frames fuel := by
  have hd1 : ba.data.toList.drop (pos + 1) =
      u32Bytes f ++ (tyListBytes as ++ (argListBytes args ++ rest)) := by
    rw [drop_pos_add]
    cases isExit <;> (
      simp only [Bool.false_eq_true, ite_true, ite_false, tflatBytes] at hdrop
      rw [hdrop]; simp [List.append_assoc])
  have hd2 := Codec0Kit.drop_append_step hd1; rw [u32Bytes_length] at hd2
  have hd3 := Codec0Kit.drop_append_step hd2
  apply decodeLoop_leaf hfuel
  · cases isExit <;> rfl
  · cases isExit <;> (
      dsimp only [Codec0.decodeNodeStep0, Codec0.decodeBranchStep0, Codec0.decodeLeafStep0,
        Codec0.decodeLeafHiStep0, Codec0.decodeTailOrExitStep0, Codec0.finishTailOrExit0,
        Codec0.mkTailOrExit0]
      simp only [Bool.false_eq_true, ite_true, ite_false, tflatBytes] at hdrop
      rw [decodeU8_of_bytes ba pos _ _ (by simpa [List.append_assoc] using hdrop)]; dsimp only
      c0_decide_ite; rw [decodeSymTys0_of_bytes ba (pos + 1) f as _ ha hd1]; dsimp only
      rw [decodeArgList0_of_bytes ba _ args rest hargs hd3]
      simp only [Bool.false_eq_true, ite_true, ite_false]
      congr 1; simp only [tflatBytes, List.length_cons, List.length_append, u32Bytes_length]; omega)

section
local macro "c0_prep" : tactic =>
  `(tactic| dsimp only [TFlat0ListBounded, Blocks0ListBounded, tflatNodes, tflatBytes,
      blocksNodes, blocksBytes] at *)

local macro "c0_tag" h:term:arg n:num : tactic =>
  `(tactic| (
      have hd_tag := $h
      rw [decodeU8_of_bytes _ _ $n _ (by simpa [List.append_assoc, Nat.add_comm] using hd_tag)]
      dsimp only; c0_decide_ite))

local macro "c0_lin_push" recFn:term:arg k:term:arg f:term:arg hk:term:arg hd:term:arg
    hfuel:term:arg : tactic =>
  `(tactic| (
      refine decodeLoop_linPush
        ($recFn $k _ _ ($f :: _) _ (_ - 1) $hk (Codec0Kit.u32_sub1_ge (by omega)) $hd)
        rfl ?_ ?_ $hfuel ?_
      · first | rfl | (dsimp only [Codec0.applyLinFrame0, tflatNodes, blocksNodes]; omega)
      · (try simp only [Codec0.applyLinFrame0, Codec0.applyLinLowFrame0, tflatBytes, blocksBytes,
          List.length_cons, List.length_append, List.length_nil, u32Bytes_length]); omega))

mutual
private theorem decodeTFlatLoop0_of_bytes :
    ∀ (t : TFlat0) (ba : ByteArray) (pos : Nat) (frames : List Codec0.DecFrame0)
      (rest : List UInt8) (fuel : UInt32),
      TFlat0ListBounded t → tflatNodes t ≤ fuel.toNat →
      ba.data.toList.drop pos = tflatBytes t ++ rest →
      Codec0.decodeTFlatLoop0 fuel ba pos frames =
        frameApplyResult ba (pos + (tflatBytes t).length) t frames fuel
  | .let1 op args k, ba, pos, frames, rest, fuel, hb, hfuel, hdrop => by
    c0_prep; have hd1 := Codec0Kit.drop_cons_step (by simpa [List.append_assoc] using hdrop)
    have hd2 := Codec0Kit.drop_append_step hd1; have hd3 := Codec0Kit.drop_append_step hd2
    c0_lin_push decodeTFlatLoop0_of_bytes k (.let1 op args) hb.2 hd3 hfuel
    dsimp only [Codec0.decodeNodeStep0, Codec0.decodeLinLowStep0, Codec0.decodeLet1Step0,
      Codec0.finishLet1Step0, Codec0.mkLet1Step0]
    c0_tag hdrop 0; rw [decodeOpCode0_of_bytes ba (pos + 1) op _ hd1]; dsimp only
    rw [decodeArgList0_of_bytes ba _ args _ hb.1 hd2]
  | .let2Umulw64 a b k, ba, pos, frames, rest, fuel, hb, hfuel, hdrop => by
    c0_prep; have hd1 := Codec0Kit.drop_cons_step (by simpa [List.append_assoc] using hdrop)
    have hd2 := Codec0Kit.drop_append_step hd1; have hd3 := Codec0Kit.drop_append_step hd2
    c0_lin_push decodeTFlatLoop0_of_bytes k (.let2Umulw64 a b) hb hd3 hfuel
    dsimp only [Codec0.decodeNodeStep0, Codec0.decodeLinLowStep0, Codec0.decodeLet2Step0]
    c0_tag hdrop 1; rw [decodeArg0_of_bytes ba (pos + 1) a _ hd1]; dsimp only
    rw [decodeArg0_of_bytes ba _ b _ hd2]
  | .load ty addr k, ba, pos, frames, rest, fuel, hb, hfuel, hdrop => by
    c0_prep; have hd1 := Codec0Kit.drop_cons_step (by simpa [List.append_assoc] using hdrop)
    have hd2 := Codec0Kit.drop_cons_step hd1; have hd3 := Codec0Kit.drop_append_step hd2
    c0_lin_push decodeTFlatLoop0_of_bytes k (.load ty addr) hb hd3 hfuel
    dsimp only [Codec0.decodeNodeStep0, Codec0.decodeLinLowStep0, Codec0.decodeLoadStep0]
    c0_tag hdrop 2; rw [decodeTy0_of_bytes ba (pos + 1) ty _ hd1]; dsimp only
    rw [decodeArg0_of_bytes ba (pos + 1 + 1) addr _ hd2]
  | .store ty val addr k, ba, pos, frames, rest, fuel, hb, hfuel, hdrop => by
    c0_prep; have hd1 := Codec0Kit.drop_cons_step (by simpa [List.append_assoc] using hdrop)
    have hd2 := Codec0Kit.drop_cons_step hd1; have hd3 := Codec0Kit.drop_append_step hd2
    c0_lin_push decodeTFlatLoop0_of_bytes k (.store ty val addr) hb
      (Codec0Kit.drop_append_step hd3) hfuel
    dsimp only [Codec0.decodeNodeStep0, Codec0.decodeLinLowStep0, Codec0.decodeStoreStep0,
      Codec0.finishStoreStep0]
    c0_tag hdrop 3; rw [decodeTy0_of_bytes ba (pos + 1) ty _ hd1]; dsimp only
    rw [decodeArg0_of_bytes ba (pos + 1 + 1) val _ hd2]; dsimp only
    rw [decodeArg0_of_bytes ba _ addr _ hd3]
  | .call f as bs args k, ba, pos, frames, rest, fuel, hb, hfuel, hdrop => by
    c0_prep; have hd1 := Codec0Kit.drop_cons_step (by simpa [List.append_assoc] using hdrop)
    have hd2 := Codec0Kit.drop_append_step hd1; rw [u32Bytes_length] at hd2
    have hd4 := Codec0Kit.drop_append_step (Codec0Kit.drop_append_step hd2)
    c0_lin_push decodeTFlatLoop0_of_bytes k (.call f as bs args) hb.2.2.2
      (Codec0Kit.drop_append_step hd4) hfuel
    dsimp only [Codec0.decodeNodeStep0, Codec0.decodeCallStep0, Codec0.finishCallStep0,
      Codec0.mkCallStep0]
    c0_tag hdrop 4; rw [decodeCallSig0_of_bytes ba (pos + 1) f as bs _ hb.1 hb.2.1 hd1]; dsimp only
    rw [decodeArgList0_of_bytes ba _ args _ hb.2.2.1 hd4]
  | .tailCall f as args, ba, pos, frames, rest, fuel, hb, hfuel, hdrop =>
    decodeLoop_tailOrExit false ba pos f as args frames rest fuel hb.1 hb.2 hfuel hdrop
  | .jnz c t1 t2, ba, pos, frames, rest, fuel, hb, hfuel, hdrop => by
    c0_prep; have hf0 : fuel ≠ 0 := Codec0Kit.u32_ne_zero_of_toNat_pos (by omega)
    have hd1 := Codec0Kit.drop_cons_step (by simpa [List.append_assoc] using hdrop)
    have hd2 := Codec0Kit.drop_append_step hd1
    have hstep : Codec0.decodeNodeStep0 ba pos =
        .push (pos + 1 + (argBytes c).length) (.jnzL c) := by
      dsimp only [Codec0.decodeNodeStep0, Codec0.decodeBranchStep0]
      c0_tag hdrop 6; rw [decodeArg0_of_bytes ba (pos + 1) c _ hd1]
    rw [decodeTFlatLoop0_step fuel hf0 ba pos frames, hstep]; dsimp only [Codec0.stepLoopFrame0]
    rw [decodeTFlatLoop0_of_bytes t1 ba _ (.jnzL c :: frames) (tflatBytes t2 ++ rest) (fuel - 1)
      hb.1 (Codec0Kit.u32_sub1_ge (by omega)) hd2]
    dsimp only [frameApplyResult, Codec0.decodeApplyFrames0, Codec0.stepNonLinFrame0, tflatNodes]
    rw [decodeTFlatLoop0_of_bytes t2 ba _ (.jnzR c t1 :: frames) rest _ hb.2
      (by rw [Codec0Kit.u32_sub1_sub (by omega), Codec0Kit.u32_sub_ofNat_toNat (by omega)]; omega)
      (Codec0Kit.drop_append_step hd2)]
    dsimp only [frameApplyResult, Codec0.decodeApplyFrames0, Codec0.applyLinFrame0, tflatNodes]
    rw [show pos + 1 + (argBytes c).length + (tflatBytes t1).length + (tflatBytes t2).length =
        pos + (6 :: argBytes c ++ tflatBytes t1 ++ tflatBytes t2).length by
      simp only [List.length_cons, List.length_append]; omega,
      Codec0Kit.u32_sub1_sub (by omega), Codec0Kit.u32_sub_sub_ofNat (by omega), Nat.add_assoc]
  | .jump j args, ba, pos, frames, rest, fuel, hb, hfuel, hdrop => by
    c0_prep; have hd1 := Codec0Kit.drop_cons_step (by simpa [List.append_assoc] using hdrop)
    have hd2 := Codec0Kit.drop_append_step hd1; rw [u32Bytes_length] at hd2
    apply decodeLoop_leaf (t := .jump j args) hfuel; · rfl
    · dsimp only [Codec0.decodeNodeStep0, Codec0.decodeBranchStep0, Codec0.decodeLeafStep0,
        Codec0.decodeJumpStep0]
      c0_tag hdrop 7; rw [decodeU32_of_bytes ba (pos + 1) j _ hd1]; dsimp only
      rw [decodeArgList0_of_bytes ba (pos + 1 + 4) args rest hb hd2,
        show pos + 1 + 4 + (argListBytes args).length = pos + (tflatBytes (.jump j args)).length by
          simp only [tflatBytes, List.length_cons, List.length_append, u32Bytes_length]; omega]
  | .ret vs, ba, pos, frames, rest, fuel, hb, hfuel, hdrop => by
    c0_prep; have hd1 := Codec0Kit.drop_cons_step hdrop
    apply decodeLoop_leaf (t := .ret vs) hfuel; · rfl
    · dsimp only [Codec0.decodeNodeStep0, Codec0.decodeBranchStep0, Codec0.decodeLeafStep0,
        Codec0.decodeLeafHiStep0]
      c0_tag hdrop 8; rw [decodeArgList0_of_bytes ba (pos + 1) vs rest hb hd1,
        show pos + 1 + (argListBytes vs).length = pos + (tflatBytes (.ret vs)).length by
          simp only [tflatBytes, List.length_cons]; omega]
  | .exit f as args, ba, pos, frames, rest, fuel, hb, hfuel, hdrop =>
    decodeLoop_tailOrExit true ba pos f as args frames rest fuel hb.1 hb.2 hfuel hdrop
  | .hlt, ba, pos, frames, rest, fuel, _, hfuel, hdrop => by
    c0_prep; apply decodeLoop_leaf (t := .hlt) hfuel; · rfl
    · dsimp only [Codec0.decodeNodeStep0, Codec0.decodeBranchStep0, Codec0.decodeLeafStep0,
        Codec0.decodeLeafHiStep0]; rw [decodeU8_of_bytes ba pos 10 rest hdrop]; rfl
  | .group [] k, ba, pos, frames, rest, fuel, hb, hfuel, hdrop => by
    c0_prep; have hd1 := Codec0Kit.drop_cons_step (by simpa [List.append_assoc] using hdrop)
    have hd2 := Codec0Kit.drop_append_step hd1; rw [u32Bytes_length] at hd2
    c0_lin_push decodeTFlatLoop0_of_bytes k .groupKEmpty hb.2.2 hd2 hfuel
    dsimp only [Codec0.decodeNodeStep0, Codec0.decodeBranchStep0, Codec0.decodeGroupStep0]
    c0_tag hdrop 11; rw [decodeU32_of_bytes ba (pos + 1) 0 _ hd1]; rfl
  | .group ((ts0, b0) :: tl) k, ba, pos, frames, rest, fuel, hb, hfuel, hdrop => by
    c0_prep; have hf0 : fuel ≠ 0 := Codec0Kit.u32_ne_zero_of_toNat_pos (by omega)
    have hlen_lt : tl.length + 1 < 2 ^ 32 := by simpa using hb.1
    have hd1 := Codec0Kit.drop_cons_step (by simpa [List.append_assoc] using hdrop)
    have hd2 := Codec0Kit.drop_append_step hd1; rw [u32Bytes_length] at hd2
    obtain ⟨hcnt_ne, hcnt_sub⟩ := Codec0Kit.u32_ofNat_succ_sub_one hlen_lt
    have hstep : Codec0.decodeNodeStep0 ba pos = .push (pos + 1 + 4 + (tyListBytes ts0).length)
        (.groupBody (UInt32.ofNat tl.length) ts0 []) := by
      dsimp only [Codec0.decodeNodeStep0, Codec0.decodeBranchStep0, Codec0.decodeGroupStep0]
      c0_tag hdrop 11; rw [decodeU32_of_bytes ba (pos + 1) _ _ hd1]; dsimp only
      rw [show UInt32.ofNat tl.length + 1 = UInt32.ofNat (tl.length + 1) from
          (UInt32.ofNat_add _ 1).symm,
        Codec0Kit.ite_false_beq hcnt_ne, decodeTyList0_of_bytes ba (pos + 1 + 4) ts0 _ hb.2.1.1
          (by simpa [Nat.add_assoc] using hd2), hcnt_sub]
    rw [decodeTFlatLoop0_step fuel hf0 ba pos frames, hstep]; dsimp only [Codec0.stepLoopFrame0]
    rw [decodeGroupBlocks0_of_bytes tl ts0 b0 k [] ba _ frames rest (fuel - 1) (by omega)
      hb.2.1.2.1 hb.2.1.2.2 hb.2.2 (Codec0Kit.u32_sub1_ge (by omega))
      (Codec0Kit.drop_append_step hd2)]
    dsimp only [frameApplyResult, tflatNodes, blocksNodes]; simp only [List.reverse_nil,
      List.nil_append, show 1 + (tflatNodes b0 + blocksNodes tl) + tflatNodes k =
        1 + (tflatNodes b0 + blocksNodes tl + tflatNodes k) by omega]
    rw [show pos + 1 + 4 + (tyListBytes ts0).length +
          ((tflatBytes b0).length + (blocksBytes tl).length + (tflatBytes k).length) =
        pos + (11 :: u32Bytes (UInt32.ofNat ((ts0, b0) :: tl).length) ++
          (tyListBytes ts0 ++ tflatBytes b0 ++ blocksBytes tl) ++ tflatBytes k).length by
      simp only [List.length_cons, List.length_append, u32Bytes_length]; omega,
      Codec0Kit.u32_sub1_sub (by omega)]
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
      Codec0.applyGroupBody0, Codec0.nextGroupFrame0]; c0_decide_ite
    rw [Codec0Kit.revList_eq_of_steps Codec0.revBlocks0 (fun _ => rfl) (fun _ _ _ => rfl),
      List.append_nil, List.reverse_cons]; dsimp only
    rw [decodeTFlatLoop0_of_bytes k ba _ (.groupK (doneRev.reverse ++ [(ts0, b0)]) :: frames)
      rest _ hk (by rw [Codec0Kit.u32_sub_ofNat_toNat (by omega)]; omega)
      (Codec0Kit.drop_append_step (by simpa using hdrop))]
    dsimp only [frameApplyResult, Codec0.decodeApplyFrames0, Codec0.applyLinFrame0,
      tflatNodes, blocksNodes]
    simp only [Nat.add_zero, Nat.add_assoc]; rw [Codec0Kit.u32_sub_sub_ofNat (by omega)]
  | (ts1, b1) :: tl', ts0, b0, k, doneRev, ba, pos, frames, rest, fuel, htl, hb0, hbtl, hk,
      hfuel, hdrop => by
    dsimp only [Blocks0ListBounded, blocksNodes, blocksBytes] at hbtl hfuel hdrop ⊢
    rw [decodeTFlatLoop0_of_bytes b0 ba pos
      (.groupBody (UInt32.ofNat ((ts1, b1) :: tl').length) ts0 doneRev :: frames)
      (tyListBytes ts1 ++ tflatBytes b1 ++ blocksBytes tl' ++ (tflatBytes k ++ rest))
      fuel hb0 (by omega) (by simpa [List.append_assoc] using hdrop)]
    dsimp only [frameApplyResult, Codec0.decodeApplyFrames0, Codec0.stepNonLinFrame0,
      Codec0.applyGroupBody0, Codec0.nextGroupFrame0, Codec0.nextGroupBodyCont0]
    have hlen1 : tl'.length + 1 < 2 ^ 32 := by simpa using htl
    obtain ⟨hne0, hsub1⟩ := Codec0Kit.u32_ofNat_succ_sub_one hlen1
    have hdts : ba.data.toList.drop (pos + (tflatBytes b0).length) =
        tyListBytes ts1 ++ (tflatBytes b1 ++ (blocksBytes tl' ++ (tflatBytes k ++ rest))) := by
      rw [drop_pos_add, hdrop, List.drop_left]; simp [List.append_assoc]
    rw [show UInt32.ofNat ((ts1, b1) :: tl').length = UInt32.ofNat (tl'.length + 1) from rfl,
      Codec0Kit.ite_false_beq hne0, decodeTyList0_of_bytes ba _ ts1 _ hbtl.1 hdts]
    dsimp only; rw [hsub1, decodeGroupBlocks0_of_bytes tl' ts1 b1 k ((ts0, b0) :: doneRev) ba _
      frames rest _ (by omega) hbtl.2.1 hbtl.2.2 hk
      (by rw [Codec0Kit.u32_sub_ofNat_toNat (by omega)]; omega) (Codec0Kit.drop_append_step hdts)]
    simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append,
      List.length_append, Nat.add_assoc]; rw [Codec0Kit.u32_sub_sub_ofNat (by omega)]
termination_by tl _ b0 k _ _ _ _ _ _ => tflatNodes b0 + blocksNodes tl + tflatNodes k
decreasing_by
  all_goals (have _ := tflatNodes_pos b0; have _ := tflatNodes_pos k)
  all_goals (try have _ := tflatNodes_pos b1)
  all_goals (dsimp only [blocksNodes]; omega)
end
end

private theorem decodeTFlat0_of_bytes (ba : ByteArray) (pos : Nat) (t : TFlat0)
    (rest : List UInt8) (hb : TFlat0Bounded t)
    (h : ba.data.toList.drop pos = tflatBytes t ++ rest) :
    Codec0.decodeTFlat0 ba pos = .ok t (pos + (tflatBytes t).length) := by
  dsimp only [Codec0.decodeTFlat0]
  have hlen_rem : (tflatBytes t).length ≤ ba.size - pos := by
    have := congrArg List.length h
    rw [List.length_drop, ba_data_toList_length, List.length_append] at this; omega
  have hfuel : tflatNodes t ≤
      (if ba.size - pos < 0xffffffff then UInt32.ofNat (ba.size - pos) else 0xffffffff).toNat := by
    by_cases hsmall : ba.size - pos < 0xffffffff
    · rw [ite_true_eq hsmall, Codec0Kit.u32_ofNat_toNat_lt (by omega)]
      exact Nat.le_trans (tflatNodes_le_bytes_length t) hlen_rem
    · rw [ite_false_eq hsmall]; exact hb.2
  rw [decodeTFlatLoop0_of_bytes t ba pos [] rest _ hb.1 hfuel h]; rfl

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
  | .let2Umulw64 _ _ | .load _ _ | .store _ _ _ | .jnzL _ | .groupKEmpty => True
  | .call _ as bs args => as.length < 2 ^ 32 ∧ bs.length < 2 ^ 32 ∧ args.length < 2 ^ 32
  | .jnzR _ t => TFlat0ListBounded t
  | .groupBody rem curTs doneRev =>
    doneRev.length + 1 + rem.toNat < 2 ^ 32 ∧ curTs.length < 2 ^ 32 ∧
      Blocks0ListBounded doneRev.reverse
  | .groupK bodies => bodies.length < 2 ^ 32 ∧ Blocks0ListBounded bodies

private def framesBounded : List Codec0.DecFrame0 → Prop
  | [] => True
  | f :: rest => frameBounded f ∧ framesBounded rest

private theorem blocks0ListBounded_append {a b : List (List Ty0 × TFlat0)}
    (ha : Blocks0ListBounded a) (hb : Blocks0ListBounded b) :
    Blocks0ListBounded (a ++ b) := by
  induction a with
  | nil => exact hb
  | cons _ _ ih => exact ⟨ha.1, ha.2.1, ih ha.2.2⟩

private theorem blocksBytes_append (a b : List (List Ty0 × TFlat0)) :
    blocksBytes (a ++ b) = blocksBytes a ++ blocksBytes b := by
  induction a with
  | nil => rfl
  | cons hd _ ih =>
    rcases hd with ⟨_, _⟩; dsimp only [List.cons_append, blocksBytes]; rw [ih]
    simp only [List.append_assoc]

private def frameNodes : Codec0.DecFrame0 → Nat
  | .let1 _ _ | .let2Umulw64 _ _ | .load _ _ | .store _ _ _ | .call _ _ _ _
  | .jnzL _ | .groupKEmpty => 1
  | .jnzR _ t => 1 + tflatNodes t
  | .groupBody _ _ doneRev => 1 + blocksNodes doneRev.reverse
  | .groupK bodies => 1 + blocksNodes bodies

private def framesNodes (frames : List Codec0.DecFrame0) : Nat :=
  frames.foldr (fun f acc => acc + frameNodes f) 0

private theorem decodeSymTys0_ok_bytes (ba : ByteArray) (pos : Nat) (fnSym : Sym0)
    (as : List Ty0) (pos' : Nat) (h : Codec0.decodeSymTys0 ba pos = .ok fnSym as pos') :
    pos ≤ pos' ∧ pos' ≤ ba.size ∧ as.length < 2 ^ 32 ∧
      baSlice ba pos pos' = u32Bytes fnSym ++ tyListBytes as := by
  dsimp only [Codec0.decodeSymTys0] at h
  codec_match sym, p1, hf ← Codec0.decodeU32 ba pos at h
  codec_match tys, p2, has ← Codec0.decodeTyList0 ba p1 at h
  obtain ⟨_, _, hp1, hs1⟩ := decodeU32_ok_bytes ba pos sym p1 hf; subst hp1
  obtain ⟨_, h2s, hbl, hs2⟩ := decodeTyList0_ok_bytes ba (pos + 4) tys p2 has
  cases h; exact ⟨by omega, h2s, hbl, by ba_slice_join [hs1, hs2]⟩

private theorem decodeCallSig0_ok_bytes (ba : ByteArray) (pos : Nat) (fnSym : Sym0)
    (as bs : List Ty0) (pos' : Nat)
    (h : Codec0.decodeCallSig0 ba pos = .ok fnSym as bs pos') :
    pos ≤ pos' ∧ pos' ≤ ba.size ∧ as.length < 2 ^ 32 ∧ bs.length < 2 ^ 32 ∧
      baSlice ba pos pos' = u32Bytes fnSym ++ tyListBytes as ++ tyListBytes bs := by
  dsimp only [Codec0.decodeCallSig0] at h
  codec_match sym, as', p1, hs ← Codec0.decodeSymTys0 ba pos at h
  codec_match bs', p2, hbs ← Codec0.decodeTyList0 ba p1 at h
  obtain ⟨_, _, ha, hs1⟩ := decodeSymTys0_ok_bytes ba pos sym as' p1 hs
  obtain ⟨_, h2s, hb, hs2⟩ := decodeTyList0_ok_bytes ba p1 bs' p2 hbs
  cases h; exact ⟨by omega, h2s, ha, hb, by ba_slice_join [hs1, hs2]⟩

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
  dsimp only [Codec0.decodeTailOrExitStep0, Codec0.finishTailOrExit0, Codec0.mkTailOrExit0] at h
  cases hs : Codec0.decodeSymTys0 ba pos with
  | none => rw [hs] at h; subst h; trivial
  | ok fnSym as p1 =>
    rw [hs] at h; dsimp only at h
    codec_step args, p2, hargs ← Codec0.decodeArgList0 ba p1 at h
    subst h
    obtain ⟨_, _, hbl1, hs1⟩ := decodeSymTys0_ok_bytes ba pos fnSym as p1 hs
    obtain ⟨_, h2s, hbl2, hs2⟩ := decodeArgList0_ok_bytes ba p1 args p2 hargs
    have hsl : baSlice ba pos p2 = u32Bytes fnSym ++ tyListBytes as ++ argListBytes args := by
      ba_slice_join [hs1, hs2]
    cases isExit <;> (
      try dsimp only
      refine ⟨by omega, h2s, ?_, ⟨hbl1, hbl2⟩, rfl⟩
      rw [hsl]; dsimp only [tflatBytes]
      simp only [List.append_assoc, Bool.false_eq_true, ite_true, ite_false]; rfl)

private theorem decodeTailOrExit_ok_join {ba : ByteArray} {pos : Nat} {isExit : Bool}
    (hs1 : baSlice ba pos (pos + 1) = [if isExit then 9 else 5]) :
    match Codec0.decodeTailOrExitStep0 ba (pos + 1) isExit with
    | .none => True
    | .push pos1 f => pos < pos1 ∧ pos1 ≤ ba.size ∧ baSlice ba pos pos1 = framePreBytes f ∧
        frameBounded f ∧ frameNodes f = 1
    | .leaf pos1 v => pos < pos1 ∧ pos1 ≤ ba.size ∧ baSlice ba pos pos1 = tflatBytes v ∧
        TFlat0ListBounded v ∧ tflatNodes v = 1 := by
  have hte := decodeTailOrExitStep0_ok_bytes ba (pos + 1) isExit _ rfl
  cases hd : Codec0.decodeTailOrExitStep0 ba (pos + 1) isExit with
  | none => trivial | push _ _ => rw [hd] at hte; exact False.elim hte
  | leaf _ _ =>
    rw [hd] at hte; obtain ⟨h1p, hps', heq, hbl, hnv⟩ := hte
    refine ⟨by omega, hps', ?_, hbl, hnv⟩; rw [baSlice_trans (by omega) h1p, hs1, ← heq]; rfl

private theorem decodeNodeStep0_ok_bytes (ba : ByteArray) (pos : Nat) (step : Codec0.DecStep0) :
    Codec0.decodeNodeStep0 ba pos = step →
    (match step with
    | .none => True
    | .push pos1 f => pos < pos1 ∧ pos1 ≤ ba.size ∧ baSlice ba pos pos1 = framePreBytes f ∧
        frameBounded f ∧ frameNodes f = 1
    | .leaf pos1 v => pos < pos1 ∧ pos1 ≤ ba.size ∧ baSlice ba pos pos1 = tflatBytes v ∧
        TFlat0ListBounded v ∧ tflatNodes v = 1) := by
  intro h; dsimp only [Codec0.decodeNodeStep0] at h
  codec_step tag, p1, hu ← Codec0.decodeU8 ba pos at h
  obtain ⟨_, h1s, hp1, hs1⟩ := decodeU8_ok_bytes ba pos tag p1 hu; subst hp1
  by_cases hle3 : tag ≤ 3
  · rw [ite_true_eq hle3] at h; dsimp only [Codec0.decodeLinLowStep0] at h
    decode_ite_chain h with skip else
      (have ht3 : tag = 3 := by c0_bv32_omega
       subst ht3; dsimp only [Codec0.decodeStoreStep0, Codec0.finishStoreStep0] at h
       codec_step ty, p2, ht ← Codec0.decodeTy0 ba (pos + 1) at h
       codec_step val, p3, hv ← Codec0.decodeArg0 ba p2 at h
       codec_step addr, p4, ha ← Codec0.decodeArg0 ba p3 at h; subst h
       obtain ⟨h12, _, hp2, hs2⟩ := decodeTy0_ok_bytes ba (pos + 1) ty p2 ht; subst hp2
       obtain ⟨h23, _, hs3⟩ := decodeArg0_ok_bytes ba (pos + 1 + 1) val p3 hv
       obtain ⟨h34, h4s, hs4⟩ := decodeArg0_ok_bytes ba p3 addr p4 ha
       exact ⟨by omega, h4s, by ba_slice_join [hs1, hs2, hs3, hs4], trivial, rfl⟩)
    · dsimp only [Codec0.decodeLet1Step0, Codec0.finishLet1Step0, Codec0.mkLet1Step0] at h
      codec_step op, p2, hop ← Codec0.decodeOpCode0 ba (pos + 1) at h
      codec_step args, p3, hargs ← Codec0.decodeArgList0 ba p2 at h; subst h
      obtain ⟨h12, _, hs2⟩ := decodeOpCode0_ok_bytes ba (pos + 1) op p2 hop
      obtain ⟨h23, h3s, hbl, hs3⟩ := decodeArgList0_ok_bytes ba p2 args p3 hargs
      exact ⟨by omega, h3s, by ba_slice_join [hs1, hs2, hs3], hbl, rfl⟩
    · dsimp only [Codec0.decodeLet2Step0] at h
      codec_step a, p2, ha ← Codec0.decodeArg0 ba (pos + 1) at h
      codec_step b, p3, hb ← Codec0.decodeArg0 ba p2 at h; subst h
      obtain ⟨h12, _, hs2⟩ := decodeArg0_ok_bytes ba (pos + 1) a p2 ha
      obtain ⟨h23, h3s, hs3⟩ := decodeArg0_ok_bytes ba p2 b p3 hb
      exact ⟨by omega, h3s, by ba_slice_join [hs1, hs2, hs3], trivial, rfl⟩
    · dsimp only [Codec0.decodeLoadStep0] at h
      codec_step ty, p2, ht ← Codec0.decodeTy0 ba (pos + 1) at h
      codec_step addr, p3, ha ← Codec0.decodeArg0 ba p2 at h; subst h
      obtain ⟨h12, _, hp2, hs2⟩ := decodeTy0_ok_bytes ba (pos + 1) ty p2 ht; subst hp2
      obtain ⟨h23, h3s, hs3⟩ := decodeArg0_ok_bytes ba (pos + 1 + 1) addr p3 ha
      exact ⟨by omega, h3s, by ba_slice_join [hs1, hs2, hs3], trivial, rfl⟩
  · rw [ite_false_eq hle3] at h
    decode_ite_chain h with skip else
      (dsimp only [Codec0.decodeBranchStep0] at h
       decode_ite_chain h with skip else
         (dsimp only [Codec0.decodeLeafStep0, Codec0.decodeLeafHiStep0] at h
          decode_ite_chain h with (try (subst h; exact ⟨by omega, h1s, hs1, trivial, rfl⟩))
            else (subst h; trivial)
          · subst h; exact decodeTailOrExit_ok_join hs1
          · dsimp only [Codec0.decodeJumpStep0] at h
            codec_step j, p2, hj ← Codec0.decodeU32 ba (pos + 1) at h
            codec_step args, p3, hargs ← Codec0.decodeArgList0 ba p2 at h; subst h
            obtain ⟨h12, _, hp2, hs2⟩ := decodeU32_ok_bytes ba (pos + 1) j p2 hj; subst hp2
            obtain ⟨h23, h3s, hbl, hs3⟩ := decodeArgList0_ok_bytes ba (pos + 1 + 4) args p3 hargs
            exact ⟨by omega, h3s, by ba_slice_join [hs1, hs2, hs3], hbl, rfl⟩
          · codec_step vs, p2, hvs ← Codec0.decodeArgList0 ba (pos + 1) at h; subst h
            obtain ⟨h12, h2s, hbl, hs2⟩ := decodeArgList0_ok_bytes ba (pos + 1) vs p2 hvs
            exact ⟨by omega, h2s, by ba_slice_join [hs1, hs2], hbl, rfl⟩
          · subst h; exact decodeTailOrExit_ok_join hs1)
       · codec_step c, p2, hc ← Codec0.decodeArg0 ba (pos + 1) at h; subst h
         obtain ⟨h12, h2s, hs2⟩ := decodeArg0_ok_bytes ba (pos + 1) c p2 hc
         exact ⟨by omega, h2s, by ba_slice_join [hs1, hs2], trivial, rfl⟩
       · dsimp only [Codec0.decodeGroupStep0] at h
         codec_step cnt, p2, hcnt ← Codec0.decodeU32 ba (pos + 1) at h
         obtain ⟨h12, h2s, hp2, hs2⟩ := decodeU32_ok_bytes ba (pos + 1) cnt p2 hcnt; subst hp2
         by_cases hc0 : cnt = 0
         · subst hc0; c0_decide_ite_at h; subst h
           exact ⟨by omega, h2s, by ba_slice_join [hs1, hs2], trivial, rfl⟩
         · rw [Codec0Kit.ite_false_beq hc0] at h
           codec_step ts0, p3, hts ← Codec0.decodeTyList0 ba (pos + 1 + 4) at h; subst h
           obtain ⟨h23, h3s, hbl, hs3⟩ := decodeTyList0_ok_bytes ba (pos + 1 + 4) ts0 p3 hts
           have hrem : 0 + 1 + (cnt - 1).toNat < 2 ^ 32 := by
             rw [Codec0Kit.u32_toNat_sub_of_le_toNat cnt 1
               (Codec0Kit.u32_toNat_pos_of_ne_zero hc0)]
             have := cnt.toNat_lt; have : (1 : UInt32).toNat = 1 := rfl; omega
           have hcnt_eq := (Codec0Kit.u32_cnt_sub1_add (done := 0) hc0).trans (UInt32.zero_add cnt)
           refine ⟨by omega, h3s, ?_, ⟨hrem, hbl, trivial⟩, rfl⟩
           dsimp only [framePreBytes]; rw [List.length_nil, hcnt_eq]; ba_slice_join [hs1, hs2, hs3])
    · dsimp only [Codec0.decodeCallStep0, Codec0.finishCallStep0, Codec0.mkCallStep0] at h
      cases hsig : Codec0.decodeCallSig0 ba (pos + 1) with
      | none => rw [hsig] at h; subst h; trivial
      | ok fnSym as bs p2 =>
        rw [hsig] at h; dsimp only at h
        codec_step args, p3, hargs ← Codec0.decodeArgList0 ba p2 at h; subst h
        obtain ⟨_, _, hbl1, hbl2, hs2⟩ := decodeCallSig0_ok_bytes ba (pos + 1) fnSym as bs p2 hsig
        obtain ⟨_, h3s, hbl3, hs3⟩ := decodeArgList0_ok_bytes ba p2 args p3 hargs
        refine ⟨by omega, h3s, ?_, ⟨hbl1, hbl2, hbl3⟩, rfl⟩
        dsimp only [framePreBytes]; ba_slice_join [hs1, hs2, hs3]

private theorem applyLinFrame0_spec (f : Codec0.DecFrame0) (v : TFlat0)
    (hnl : match f with | .jnzL _ | .groupBody _ _ _ => False | _ => True) :
    framePreBytes f ++ tflatBytes v = tflatBytes (Codec0.applyLinFrame0 f v) ∧
    (frameBounded f → TFlat0ListBounded v → TFlat0ListBounded (Codec0.applyLinFrame0 f v)) ∧
    frameNodes f + tflatNodes v = tflatNodes (Codec0.applyLinFrame0 f v) := by
  cases f with
  | jnzL _ | groupBody _ _ _ => exact False.elim hnl
  | let1 _ _ | jnzR _ _ => exact ⟨rfl, fun hf hv => ⟨hf, hv⟩, rfl⟩
  | let2Umulw64 _ _ | load _ _ | store _ _ _ => exact ⟨rfl, fun _ hv => hv, rfl⟩
  | call _ _ _ _ => exact ⟨rfl, fun hf hv => ⟨hf.1, hf.2.1, hf.2.2, hv⟩, rfl⟩
  | groupKEmpty =>
    refine ⟨?_, fun _ hv => ⟨by decide, trivial, hv⟩, rfl⟩
    dsimp only [framePreBytes, Codec0.applyLinFrame0, tflatBytes, blocksBytes]
    simp only [List.append_assoc, List.nil_append]; rfl
  | groupK _ => exact ⟨rfl, fun hf hv => ⟨hf.1, hf.2, hv⟩, rfl⟩

private theorem blocksNodes_snoc (xs : List (List Ty0 × TFlat0)) (ts : List Ty0) (v : TFlat0) :
    blocksNodes (xs ++ [(ts, v)]) = blocksNodes xs + tflatNodes v := by
  induction xs with
  | nil => dsimp only [List.nil_append, blocksNodes]; omega
  | cons _ _ ih => dsimp only [List.cons_append, blocksNodes]; rw [ih, Nat.add_assoc]

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
      · subst hrem0; c0_decide_ite
        rw [Codec0Kit.revList_eq_of_steps Codec0.revBlocks0 (fun _ => rfl) (fun _ _ _ => rfl),
          List.append_nil]
        dsimp only [framesPreBytes, framePreBytes, framesBounded, frameBounded]
        rw [List.foldr_cons, List.foldr_cons, baSlice_self, List.append_nil]; dsimp only
        have hlen_cons : ((curTs, v) :: doneRev).reverse.length < 2 ^ 32 := by simpa using hlen_lt
        have hcnt_eq : UInt32.ofNat ((curTs, v) :: doneRev).reverse.length =
            UInt32.ofNat doneRev.length + 1 + 0 := by
          simp only [List.length_reverse, List.length_cons, UInt32.add_zero]
          rw [UInt32.ofNat_add]; rfl
        refine ⟨Nat.le_refl _, hps, ?_, ⟨hlen_cons, hblocks_b⟩, hbrest⟩
        rw [hcnt_eq, hblocks_eq]; simp [List.append_assoc]
      · rw [Codec0Kit.ite_false_beq hrem0]
        dsimp only [Codec0.nextGroupBodyCont0]
        cases htsN : Codec0.decodeTyList0 ba pos with
        | none => simp
        | ok tsNext p1 =>
          dsimp only
          obtain ⟨h01, h1s, htsNl, hs1⟩ := decodeTyList0_ok_bytes ba pos tsNext p1 htsN
          dsimp only [framesPreBytes, framePreBytes, framesBounded, frameBounded]
          rw [List.foldr_cons, List.foldr_cons]; dsimp only
          have hrem_b : ((curTs, v) :: doneRev).length + 1 + (rem - 1).toNat < 2 ^ 32 := by
            simp only [List.length_cons]
            exact Codec0Kit.u32_cnt_sub1_lt hrem0 hlen_lt
          have hcnt_eq : UInt32.ofNat ((curTs, v) :: doneRev).length + 1 + (rem - 1) =
              UInt32.ofNat doneRev.length + 1 + rem := by
            rw [List.length_cons, UInt32.ofNat_add]; exact Codec0Kit.u32_cnt_sub1_add hrem0
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
      · subst hrem0; c0_decide_ite
        rw [Codec0Kit.revList_eq_of_steps Codec0.revBlocks0 (fun _ => rfl) (fun _ _ _ => rfl),
          List.append_nil]
        dsimp only [framesNodes, frameNodes]; rw [List.foldr_cons, List.foldr_cons]; dsimp only
        rw [List.reverse_cons, blocksNodes_snoc]; omega
      · rw [Codec0Kit.ite_false_beq hrem0]
        dsimp only [Codec0.nextGroupBodyCont0]
        cases Codec0.decodeTyList0 ba pos with
        | none => trivial
        | ok _ _ =>
          dsimp only [framesNodes, frameNodes]; rw [List.foldr_cons, List.foldr_cons]; dsimp only
          rw [List.reverse_cons, blocksNodes_snoc]; omega
    | _ =>
      have hfn := (applyLinFrame0_spec f v (by rw [hf]; trivial)).2.2
      have ih := decodeApplyFrames0_nodes rest ba pos (Codec0.applyLinFrame0 f v)
      dsimp only; rw [← hf]
      cases hdec : Codec0.decodeApplyFrames0 ba pos (Codec0.applyLinFrame0 f v) rest with
      | none => trivial
      | done _ _ | cont _ _ =>
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
    have hz : fuel = 0 := Codec0Kit.u32_eq_zero_of_toNat_eq_zero hfn
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
  | [] => [] | ex :: rest => extBytes ex ++ extSeqBytes rest

private def extListBytes (xs : List ExtSig0) : List UInt8 :=
  u32Bytes (UInt32.ofNat xs.length) ++ extSeqBytes xs

private def fnBytes (fn : TFlatFn0) : List UInt8 :=
  u32Bytes fn.name ++ tyListBytes fn.as ++ tyListBytes fn.rs ++ tflatBytes fn.body

private def fnSeqBytes : List TFlatFn0 → List UInt8
  | [] => [] | fn :: rest => fnBytes fn ++ fnSeqBytes rest

private def fnListBytes (xs : List TFlatFn0) : List UInt8 :=
  u32Bytes (UInt32.ofNat xs.length) ++ fnSeqBytes xs

private def modBytes (m : TFlatModule0) : List UInt8 :=
  headerBytes ++ fnListBytes m.fns ++ extListBytes m.externs ++ symListBytes m.exits

private theorem encodeExt0_bytes (ba : ByteArray) (ex : ExtSig0) :
    (Codec0.encodeExt0 ba ex).data.toList = ba.data.toList ++ extBytes ex := by
  dsimp only [Codec0.encodeExt0, extBytes]
  rw [encodeTyList0_bytes, encodeTyList0_bytes, encodeU32_bytes]; simp only [List.append_assoc]

private theorem encodeExtList0_bytes (ba : ByteArray) (xs : List ExtSig0) :
    (Codec0.encodeExtList0 ba xs).data.toList = ba.data.toList ++ extListBytes xs := by
  c0_encode_list! Codec0.encodeExtList0 Codec0.encodeExtListLoop0 Codec0.encodeExt0
    Codec0.lenExtsU32 extBytes extSeqBytes extListBytes encodeExt0_bytes

private theorem encodeFn0_bytes (ba : ByteArray) (fn : TFlatFn0) :
    (Codec0.encodeFn0 ba fn).data.toList = ba.data.toList ++ fnBytes fn := by
  dsimp only [Codec0.encodeFn0, fnBytes]
  rw [encodeTFlat0_bytes, encodeTyList0_bytes, encodeTyList0_bytes, encodeU32_bytes]
  simp only [List.append_assoc]

private theorem encodeFnList0_bytes (ba : ByteArray) (xs : List TFlatFn0) :
    (Codec0.encodeFnList0 ba xs).data.toList = ba.data.toList ++ fnListBytes xs := by
  c0_encode_list! Codec0.encodeFnList0 Codec0.encodeFnListLoop0 Codec0.encodeFn0
    Codec0.lenFnsU32 fnBytes fnSeqBytes fnListBytes encodeFn0_bytes

private theorem encodeMod0_bytes (m : TFlatModule0) : (encodeMod0 m).data.toList = modBytes m := by
  dsimp only [encodeMod0, modBytes]
  rw [encodeSymList0_bytes, encodeExtList0_bytes, encodeFnList0_bytes, encodeHeader_bytes,
    ba_emptyWithCapacity_data_toList, List.nil_append, List.append_assoc, List.append_assoc]

private theorem decodeExt0_of_bytes (ba : ByteArray) (pos : Nat) (ex : ExtSig0)
    (rest : List UInt8) (hb : ExtSig0Bounded ex)
    (h : ba.data.toList.drop pos = extBytes ex ++ rest) :
    Codec0.decodeExt0 ba pos = .ok ex (pos + (extBytes ex).length) := by
  dsimp only [Codec0.decodeExt0, extBytes] at h ⊢
  rw [decodeCallSig0_of_bytes ba pos ex.name ex.as ex.rs rest hb.1 hb.2
    (by simpa [List.append_assoc] using h)]
  simp only [List.length_append, u32Bytes_length, Nat.add_assoc]

private theorem decodeExt0_ok_bytes (ba : ByteArray) (pos : Nat) (ex : ExtSig0) (pos' : Nat)
    (h : Codec0.decodeExt0 ba pos = .ok ex pos') :
    pos ≤ pos' ∧ pos' ≤ ba.size ∧ ExtSig0Bounded ex ∧ baSlice ba pos pos' = extBytes ex := by
  dsimp only [Codec0.decodeExt0] at h
  codec_match name, as, rs, p1, hsig ← Codec0.decodeCallSig0 ba pos at h
  obtain ⟨h01, h1s, ha, hr, hs1⟩ := decodeCallSig0_ok_bytes ba pos name as rs p1 hsig
  cases h; exact ⟨h01, h1s, ⟨ha, hr⟩, hs1⟩

private theorem decodeFn0_of_bytes (ba : ByteArray) (pos : Nat) (fn : TFlatFn0)
    (rest : List UInt8) (hb : Fn0Bounded fn) (h : ba.data.toList.drop pos = fnBytes fn ++ rest) :
    Codec0.decodeFn0 ba pos = .ok fn (pos + (fnBytes fn).length) := by
  dsimp only [fnBytes] at h ⊢; rw [List.append_assoc, List.append_assoc] at h
  let ex : ExtSig0 := { name := fn.name, as := fn.as, rs := fn.rs }
  have hd_ex : ba.data.toList.drop pos = extBytes ex ++ (tflatBytes fn.body ++ rest) := by
    dsimp only [ex, extBytes]; rw [h]; simp only [List.append_assoc]
  dsimp only [Codec0.decodeFn0]
  rw [decodeExt0_of_bytes ba pos ex _ ⟨hb.1, hb.2.1⟩ hd_ex]; dsimp only
  rw [decodeTFlat0_of_bytes ba _ fn.body rest hb.2.2 (Codec0Kit.drop_append_step hd_ex)]
  dsimp only [ex, extBytes]; simp only [List.length_append, Nat.add_assoc]

private theorem decodeFn0_ok_bytes (ba : ByteArray) (pos : Nat) (fn : TFlatFn0) (pos' : Nat)
    (h : Codec0.decodeFn0 ba pos = .ok fn pos') :
    pos ≤ pos' ∧ pos' ≤ ba.size ∧ Fn0Bounded fn ∧ baSlice ba pos pos' = fnBytes fn := by
  dsimp only [Codec0.decodeFn0] at h
  codec_match hdr, p1, hex ← Codec0.decodeExt0 ba pos at h
  codec_match body, p2, hbd ← Codec0.decodeTFlat0 ba p1 at h
  obtain ⟨_, h1s, hbh, hs1⟩ := decodeExt0_ok_bytes ba pos hdr p1 hex
  obtain ⟨_, h2s, hbb, hs2⟩ := decodeTFlat0_ok_bytes ba p1 body p2 h1s hbd
  cases h; exact ⟨by omega, h2s, ⟨hbh.1, hbh.2, hbb⟩, by ba_slice_join [hs1, hs2]⟩

private theorem decodeExtList0_of_bytes (ba : ByteArray) (pos : Nat) (xs : List ExtSig0)
    (rest : List UInt8) (hlen_lt : xs.length < 2 ^ 32) (hbx : ∀ ex ∈ xs, ExtSig0Bounded ex)
    (h : ba.data.toList.drop pos = extListBytes xs ++ rest) :
    Codec0.decodeExtList0 ba pos = .ok xs (pos + (extListBytes xs).length) := by
  c0_decode_list_of! Codec0.DecExtsRes.ok Codec0.decodeExtList0 Codec0.decodeExtListLoop0
    Codec0.decodeExt0 Codec0.revExts0 extBytes extSeqBytes extListBytes ExtSig0Bounded
    decodeExt0_of_bytes hbx

private theorem decodeExtList0_ok_bytes (ba : ByteArray) (pos : Nat)
    (xs : List ExtSig0) (pos' : Nat) (h : Codec0.decodeExtList0 ba pos = .ok xs pos') :
    pos ≤ pos' ∧ pos' ≤ ba.size ∧ xs.length < 2 ^ 32 ∧
      (∀ ex ∈ xs, ExtSig0Bounded ex) ∧ baSlice ba pos pos' = extListBytes xs := by
  c0_decode_list_ok! Codec0.DecExtsRes.ok Codec0.decodeExtList0 Codec0.decodeExtListLoop0
    Codec0.decodeExt0 Codec0.revExts0 extBytes extSeqBytes extListBytes ExtSig0Bounded
    decodeExt0_ok_bytes

private theorem decodeFnList0_of_bytes (ba : ByteArray) (pos : Nat) (xs : List TFlatFn0)
    (rest : List UInt8) (hlen_lt : xs.length < 2 ^ 32) (hbf : ∀ fn ∈ xs, Fn0Bounded fn)
    (h : ba.data.toList.drop pos = fnListBytes xs ++ rest) :
    Codec0.decodeFnList0 ba pos = .ok xs (pos + (fnListBytes xs).length) := by
  c0_decode_list_of! Codec0.DecFnsRes.ok Codec0.decodeFnList0 Codec0.decodeFnListLoop0
    Codec0.decodeFn0 Codec0.revFns0 fnBytes fnSeqBytes fnListBytes Fn0Bounded
    decodeFn0_of_bytes hbf

private theorem decodeFnList0_ok_bytes (ba : ByteArray) (pos : Nat)
    (xs : List TFlatFn0) (pos' : Nat) (h : Codec0.decodeFnList0 ba pos = .ok xs pos') :
    pos ≤ pos' ∧ pos' ≤ ba.size ∧ xs.length < 2 ^ 32 ∧
      (∀ fn ∈ xs, Fn0Bounded fn) ∧ baSlice ba pos pos' = fnListBytes xs := by
  c0_decode_list_ok! Codec0.DecFnsRes.ok Codec0.decodeFnList0 Codec0.decodeFnListLoop0
    Codec0.decodeFn0 Codec0.revFns0 fnBytes fnSeqBytes fnListBytes Fn0Bounded
    decodeFn0_ok_bytes

/-! ## 6. Verified Round-Trip, Determinism, and Injectivity Theorems -/

private theorem decodeMod0_some_bytes {ba : ByteArray} {m : TFlatModule0}
    (h : decodeMod0 ba = some m) : Mod0Bounded m ∧ ba.data.toList = modBytes m := by
  dsimp only [decodeMod0] at h
  by_cases hhdr : Codec0.checkHeader ba = true
  · rw [ite_true_eq hhdr] at h; obtain ⟨_, hs0⟩ := checkHeader_ok_bytes ba hhdr
    dsimp only [Codec0.decodeModBody0, Codec0.decodeModTail0, Codec0.decodeModExits0,
      Codec0.mkModIfEof0] at h
    codec_match fns, p1, hfns ← Codec0.decodeFnList0 ba 5 at h
    codec_match exts, p2, hexts ← Codec0.decodeExtList0 ba p1 at h
    codec_match exits, p3, hexits ← Codec0.decodeSymList0 ba p2 at h
    by_cases heof : p3 = ba.size
    · rw [ite_true_eq (beq_iff_eq.mpr heof)] at h; cases h
      obtain ⟨_, _, hlf, hbf, hs1⟩ := decodeFnList0_ok_bytes ba 5 fns p1 hfns
      obtain ⟨_, _, hle, hbe, hs2⟩ := decodeExtList0_ok_bytes ba p1 exts p2 hexts
      obtain ⟨_, _, hlx, hs3⟩ := decodeSymList0_ok_bytes ba p2 exits p3 hexits
      refine ⟨⟨hlf, hle, hlx, hbf, hbe⟩, ?_⟩
      rw [← baSlice_zero_self ba, ← heof]; dsimp only [modBytes]; ba_slice_join [hs0, hs1, hs2, hs3]
    · rw [Codec0Kit.ite_false_beq heof] at h; cases h
  · rw [ite_false_eq hhdr] at h; cases h

/-- Verified encoder/decoder round-trip for every 32-bit bounded `TFlatModule0`. -/
public theorem decodeMod0_encodeMod0 (m : TFlatModule0) (hm : Mod0Bounded m) :
    decodeMod0 (encodeMod0 m) = some m := by
  let ba := encodeMod0 m; have hba : ba.data.toList = modBytes m := encodeMod0_bytes m
  have hd0 : ba.data.toList = headerBytes ++
      (fnListBytes m.fns ++ extListBytes m.externs ++ symListBytes m.exits) := by
    dsimp only [modBytes] at hba; rw [hba]; simp only [List.append_assoc]
  have hd1 : ba.data.toList.drop 5 =
      fnListBytes m.fns ++ (extListBytes m.externs ++ symListBytes m.exits) := by
    have := congrArg (List.drop 5) hd0; dsimp only [headerBytes] at this
    simpa [List.append_assoc] using this
  have hd2 := Codec0Kit.drop_append_step hd1; have hd3 := Codec0Kit.drop_append_step hd2
  have heof : 5 + (fnListBytes m.fns).length + (extListBytes m.externs).length +
      (symListBytes m.exits).length = ba.size := by
    rw [← ba_data_toList_length ba, hba]; dsimp only [modBytes, headerBytes]
    simp only [List.length_append, List.length_cons, List.length_nil]
  dsimp only [decodeMod0, Codec0.decodeModBody0, Codec0.decodeModTail0, Codec0.decodeModExits0,
    Codec0.mkModIfEof0]
  rw [ite_true_eq (checkHeader_of_bytes ba _ hd0),
    decodeFnList0_of_bytes ba 5 m.fns _ hm.1 hm.2.2.2.1 hd1]; dsimp only
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
