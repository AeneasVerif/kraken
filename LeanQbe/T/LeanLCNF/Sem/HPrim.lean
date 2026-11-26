module

public import LeanQbe.T.LeanLCNF.Sem.HBase

/-!
# Tier-H Built-in Primitive Semantics (`HPrim`)

Aligned with `Lower.externPrim`: covers `Nat.*` (tagged-fixnum inline fast paths + `lcnf_nat_slow`
/ `lcnf_nat_to_str`), `UIntN.*`/`USize.*`, `String.*`, `Array.*`, `ByteArray.*`, `getObjTagNat`,
`System.Platform.getNumBits`, and `outOfBounds._redArg`, together with `HPrim.wp_mono` and
`HNatPrimWp_add_fast`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF.Sem

open LeanQbe.T
open LeanQbe.T.LeanLCNF

/-! ## 1. Primitive Classifier and `Nat.*` Semantics -/

/-- Decidable classifier for imported primitive names lowered by `Lower.externPrim`. -/
@[expose] def isPrimName (name : String) : Bool :=
  match splitDot name with
  | ["Nat", _] | ["Array", _] | ["ByteArray", _] | ["Float", _]
  | ["Char", _] | ["Int", _] | ["Int64", _] | ["getObjTagNat"]
  | ["System", "Platform", "getNumBits"] | ["outOfBounds", "_redArg"] => true
  | "String" :: _ => true
  | [ty, _] => (uintWidth? ty).isSome
  | _ => false

/-- Slow-path WP for `lcnf_nat_slow(rt, op, a, b)` over `HState` (`natArith` ops `1..8, 17`). -/
@[expose] def HNatArithSlowWp (rt : BitVec 64) (op : Nat) (a b : BitVec 64) (resW : Nat)
    (K : HPost) (σ : HState) : Prop :=
  ∃ aVal bVal,
    natRepR0 a aVal σ.objs ∧ (op = 17 ∨ natRepR0 b bVal σ.objs) ∧
    natArithOkR0 op aVal bVal σ.scrLimbs.length σ.st ∧
    ∀ res st' scrLimbs' objs',
      st'.PreservesMeta σ.st → st'.rem ≤ σ.st.rem → BigNumRtWfR0 rt st' σ.scr scrLimbs' →
      natArithPostR0 op aVal bVal res σ.objs objs' →
      K ⟨.bits resW, res.setWidth resW⟩
        { st := st', objs := objs', scr := σ.scr, scrLimbs := scrLimbs' }

/-- Slow-path WP for `lcnf_nat_slow(rt, op, a, b)` (`natBits` ops `9..15, 19`). -/
@[expose] def HNatBitsSlowWp (rt : BitVec 64) (op : Nat) (a b : BitVec 64) (resW : Nat)
    (K : HPost) (σ : HState) : Prop :=
  ∃ aVal,
    (if op = 14 then aVal = a.toNat else natRepR0 a aVal σ.objs) ∧
    natBitsOkR0 op aVal b σ.objs σ.scrLimbs.length σ.st ∧
    ∀ res st' scrLimbs' objs',
      st'.PreservesMeta σ.st → st'.rem ≤ σ.st.rem → BigNumRtWfR0 rt st' σ.scr scrLimbs' →
      natBitsPostR0 op aVal b res σ.objs objs' →
      K ⟨.bits resW, res.setWidth resW⟩
        { st := st', objs := objs', scr := σ.scr, scrLimbs := scrLimbs' }

/-- Pure inline tagged-fixnum fast-path evaluator for binary `Nat` primitives (`none` ⇒ slow path).
-/
@[expose] def natBinFast? (op : String) (a b : BitVec 64) : Option Word :=
  if ((a &&& b) &&& 1#64) == 0#64 then none
  else
    let x := (a >>> 1).toNat
    let y := (b >>> 1).toNat
    match op with
    | "add" =>
      let r := (a - 1#64) + b
      if !(r < b) then some (Word.i64 r) else none
    | "sub" => some (Word.i64 (if a < b then 1#64 else (a - b) + 1#64))
    | "mul" =>
      if x * y < 2 ^ 63 then some (Word.i64 (BitVec.ofNat 64 (2 * (x * y) + 1))) else none
    | "div" =>
      some (Word.i64 (if y = 0 then 1#64 else BitVec.ofNat 64 (2 * (x / y) + 1)))
    | "mod" =>
      some (Word.i64 (if y = 0 then a else BitVec.ofNat 64 (2 * (x % y) + 1)))
    | "decEq" | "beq" => some (Word.i8 (if a = b then 1#8 else 0#8))
    | "decLt" | "blt" => some (Word.i8 (if a < b then 1#8 else 0#8))
    | "decLe" | "ble" => some (Word.i8 (if a ≤ b then 1#8 else 0#8))
    | "shiftRight" =>
      some (Word.i64 (if y < 63 then (((a >>> (y + 1)) <<< 1) ||| 1#64) else 1#64))
    | "land" => some (Word.i64 (a &&& b))
    | "lor" => some (Word.i64 (a ||| b))
    | "xor" => some (Word.i64 ((a ^^^ b) ||| 1#64))
    | "shiftLeft" =>
      if y < 63 && x <<< y < 2 ^ 63 then
        some (Word.i64 (BitVec.ofNat 64 (2 * (x <<< y) + 1)))
      else none
    | _ => none

/-- Metadata for binary `Nat` ops handled by `natBinFast?` + `lcnf_nat_slow`. -/
@[expose] def natBinSlowInfo? : String → Option (Nat × Nat × Bool)
  | "add" => some (1, 64, false) | "sub" => some (2, 64, false)
  | "mul" => some (3, 64, false) | "div" => some (4, 64, false)
  | "mod" => some (5, 64, false)
  | "decEq" | "beq" => some (6, 8, false)
  | "decLt" | "blt" => some (7, 8, false)
  | "decLe" | "ble" => some (8, 8, false)
  | "shiftRight" => some (9, 64, true)
  | "land" => some (10, 64, true) | "lor" => some (11, 64, true)
  | "xor" => some (12, 64, true) | "shiftLeft" => some (15, 64, true)
  | _ => none

/-- WP of `lcnf_nat_to_str(rt, n)` (`Nat.reprFast`) over `HState`. -/
@[expose] def HNatReprFastWp (n : BitVec 64) (K : HPost) (X : HXPost) (σ : HState) : Prop :=
  ∃ val, NatInHeap n val σ.objs ∧
    let dec := natToDecimalBytes val
    if (n &&& 1#64) ≠ 0#64 then
      canAllocBytesR0 σ.st (strAllocBytes (dec.length + 1)) ∧
      ∀ s st',
        s ≠ 0#64 → s.toNat % 8 = 0 → st'.PreservesMeta σ.st → st'.rem ≤ σ.st.rem →
        let sObj := mkStrObj s 1#32 (dec.length + 1) dec dec.length
        StrCanon sObj → K (Word.i64 s) { σ with st := st', objs := sObj :: σ.objs }
    else
      ∃ nObj ∈ σ.objs, nObj.addr = n ∧ MpzCanon nObj ∧
        let cn := trimZeroLimbsLen nObj.limbs nObj.arrSize
        (nObj.rc = 1#32 → σ.objs.length ≤ σ.st.workCap ∧ lcnfHeapClosed σ.objs ∧
          RcSound n σ.objs) ∧
        if cn = 0 then
          canAllocBytesR0 σ.st (strAllocBytes 2) ∧
          ∀ s st' objs',
            s ≠ 0#64 → s.toNat % 8 = 0 → st'.PreservesMeta σ.st → st'.rem ≤ σ.st.rem →
            let sObj := mkStrObj s 1#32 2 [UInt8.ofNat 48] 1
            StrCanon sObj → DecObjRel n σ.objs objs' →
            K (Word.i64 s) { σ with st := st', objs := sObj :: objs' }
        else if mpzMaxLimbsNat < cn then X panicCapCode σ
        else
          let needRem :=
            mpzAllocBytes cn + sarrayAllocBytes (20 * cn) + strAllocBytes (20 * cn + 1)
          needRem ≤ σ.st.rem ∧
          ∀ s st' objs',
            s ≠ 0#64 → s.toNat % 8 = 0 → st'.PreservesMeta σ.st → st'.rem ≤ σ.st.rem →
            let sObj := mkStrObj s 1#32 (dec.length + 1) dec dec.length
            StrCanon sObj → DecObjRel n σ.objs objs' →
            K (Word.i64 s) { σ with st := st', objs := sObj :: objs' }

/-- Inline tagged-fixnum fast path + `lcnf_nat_slow` / `lcnf_nat_to_str` slow path for `Nat.*`. -/
@[expose] def HNatPrimWp (rt : BitVec 64) (op : String) (as : List Word)
    (K : HPost) (X : HXPost) (σ : HState) : Prop :=
  match natBinSlowInfo? op, as with
  | some (code, resW, isBits), [wa, wb] =>
    match wa.toBV64?, wb.toBV64? with
    | some a, some b =>
      match natBinFast? op a b with
      | some w => K w σ
      | none =>
        if isBits then HNatBitsSlowWp rt code a b resW K σ
        else HNatArithSlowWp rt code a b resW K σ
    | _, _ => False
  | none, _ =>
    match op, as with
    | "pred", [wa] =>
      match wa.toBV64? with
      | some a =>
        if (a &&& 1#64) != 0#64 then
          K (Word.i64 (if a = 1#64 then 1#64 else a - 2#64)) σ
        else HNatArithSlowWp rt 17 a 1#64 64 K σ
      | none => False
    | "pow", [wa, wb] =>
      match wa.toBV64?, wb.toBV64? with
      | some a, some b =>
        ∃ aVal bVal, natRepR0 a aVal σ.objs ∧ natRepR0 b bVal σ.objs ∧
          natPowOkR0 aVal bVal σ.scrLimbs.length σ.st ∧
          ∀ res st' scrLimbs' objs',
            st'.PreservesMeta σ.st → st'.rem ≤ σ.st.rem → BigNumRtWfR0 rt st' σ.scr scrLimbs' →
            natRepR0 res (aVal ^ bVal) objs' →
            (∀ o ∈ σ.objs, o.addr ≠ res → o ∈ objs') →
            K (Word.i64 res) { st := st', objs := objs', scr := σ.scr, scrLimbs := scrLimbs' }
      | _, _ => False
    | "gcd", [wa, wb] =>
      match wa.toBV64?, wb.toBV64? with
      | some a, some b =>
        ∃ aVal bVal, natRepR0 a aVal σ.objs ∧ natRepR0 b bVal σ.objs ∧
          natGcdOkR0 aVal bVal σ.scrLimbs.length σ.st ∧
          ∀ res st' scrLimbs' objs',
            st'.PreservesMeta σ.st → st'.rem ≤ σ.st.rem → BigNumRtWfR0 rt st' σ.scr scrLimbs' →
            natRepR0 res (Nat.gcd aVal bVal) objs' →
            (∀ o ∈ σ.objs, o ∈ objs') →
            K (Word.i64 res) { st := st', objs := objs', scr := σ.scr, scrLimbs := scrLimbs' }
      | _, _ => False
    | "log2", [wa] =>
      match wa.toBV64? with
      | some a => HNatBitsSlowWp rt 19 a 1#64 64 K σ
      | none => False
    | "reprFast", [wn] =>
      match wn.toBV64? with
      | some n => HNatReprFastWp n K X σ
      | none => False
    | _, _ => False
  | _, _ => False

/-! ## 2. `UIntN.*`, `String.*`, `Array.*`, and `ByteArray.*` Semantics -/

/-- Pure bitvector evaluator for `UIntN.*` / `USize.*` arithmetic, comparisons, and casts. -/
@[expose] def uintPure? (w : Nat) (op : String) (as : List Word) : Option Word :=
  let bin (f : BitVec w → BitVec w → BitVec w) : Option Word :=
    match as with
    | [a, b] => match a.toBits? w, b.toBits? w with
      | some av, some bv => some ⟨.bits w, f av bv⟩ | _, _ => none
    | _ => none
  let cmp (p : BitVec w → BitVec w → Bool) : Option Word :=
    match as with
    | [a, b] => match a.toBits? w, b.toBits? w with
      | some av, some bv => some (Word.i8 (if p av bv then 1#8 else 0#8)) | _, _ => none
    | _ => none
  let un (f : BitVec w → Word) : Option Word :=
    match as with | [a] => (a.toBits? w).map f | _ => none
  match op with
  | "add" => bin (· + ·) | "sub" => bin (· - ·) | "mul" => bin (· * ·)
  | "land" => bin (· &&& ·) | "lor" => bin (· ||| ·) | "xor" => bin (· ^^^ ·)
  | "shiftLeft" => bin fun a b => a <<< (b &&& BitVec.ofNat w (w - 1))
  | "shiftRight" => bin fun a b => a >>> (b &&& BitVec.ofNat w (w - 1))
  | "div" => bin fun a b => if b = 0 then 0 else a / b
  | "mod" => bin fun a b => if b = 0 then a else a % b
  | "complement" => un fun a => ⟨.bits w, ~~~a⟩
  | "neg" => un fun a => ⟨.bits w, -a⟩
  | "decEq" | "beq" => cmp (· == ·)
  | "decLt" | "blt" => cmp (fun a b => decide (a < b))
  | "decLe" | "ble" => cmp (fun a b => decide (a ≤ b))
  | "toUInt8" => un fun a => Word.i8 (a.setWidth 8)
  | "toUInt16" => un fun a => Word.i16 (a.setWidth 16)
  | "toUInt32" => un fun a => Word.i32 (a.setWidth 32)
  | "toUInt64" | "toUSize" => un fun a => Word.i64 (a.setWidth 64)
  | _ => none

/-- Helper for `UIntN.ofNat` / `ofNatLT` / `ofBitVec`. -/
@[expose] def HUintOfNatWp (rt : BitVec 64) (w : Nat) (wa : Word) (decAfter : Bool)
    (K : HPost) (σ : HState) : Prop :=
  match wa.toBV64? with
  | none => False
  | some a =>
    let cont : HPost :=
      if decAfter then fun r σ' => HDecN a .tobject true 1 (K r) σ' else K
    if (a &&& 1#64) != 0#64 then cont ⟨.bits w, (a >>> 1).setWidth w⟩ σ
    else HNatBitsSlowWp rt 13 a (BitVec.ofNat 64 w) w cont σ

/-- Inline `UIntN.*` / `USize.*` semantics at width `w`. -/
@[expose] def HUintPrimWp (rt : BitVec 64) (w : Nat) (op : String) (as : List Word)
    (K : HPost) (σ : HState) : Prop :=
  match uintPure? w op as with
  | some r => K r σ
  | none =>
    match op, as with
    | "ofNat", [wa] | "ofNatLT", [wa] | "ofNatLT", [wa, _] => HUintOfNatWp rt w wa false K σ
    | "ofBitVec", [wa] => HUintOfNatWp rt w wa true K σ
    | "toNat", [a] | "toBitVec", [a] =>
      match a.toBits? w with
      | none => False
      | some av =>
        let x := av.setWidth 64
        if w < 64 || (x >>> 63) == 0#64 then K (Word.i64 ((x <<< 1) ||| 1#64)) σ
        else HNatBitsSlowWp rt 14 x 0#64 64 K σ
    | _, _ => False

/-- WP of `lcnf_string_append(rt, s1, s2)` over `HState`. -/
@[expose] def HStringAppendWp (s1 s2 : BitVec 64) (K : HPost) (X : HXPost) (σ : HState) : Prop :=
  ∃ s1Obj ∈ σ.objs, s1Obj.addr = s1 ∧ StrCanon s1Obj ∧
    ∃ s2Obj ∈ σ.objs, s2Obj.addr = s2 ∧ StrCanon s2Obj ∧
      let p1 := strPayload s1Obj
      let p2 := strPayload s2Obj
      if p2.length = 0 then K (Word.i64 s1) σ
      else if strMaxCap ≤ p1.length + p2.length then X panicCapCode σ
      else
        let newPayload := p1 ++ p2
        let newLen := (s1Obj.strLen + s2Obj.strLen) % 2 ^ 64
        let inPlace := s1Obj.rc = 1#32 ∧ newPayload.length + 1 ≤ s1Obj.cap
        let newCap :=
          if inPlace then s1Obj.cap else strGrowCap s1Obj.rc s1Obj.cap (newPayload.length + 1)
        (¬ inPlace → canAllocBytesR0 σ.st (strAllocBytes newCap) ∧
          (s1Obj.rc = 1#32 → σ.objs.length ≤ σ.st.workCap ∧ lcnfHeapClosed σ.objs ∧
            RcSound s1 σ.objs)) ∧
        ∀ r st' objs',
          r ≠ 0#64 → r.toNat % 8 = 0 → st'.PreservesMeta σ.st → st'.rem ≤ σ.st.rem →
          (inPlace → r = s1 ∧ st' = σ.st ∧
            objs' = σ.objs.map (fun o =>
              if o.addr = s1 then mkStrObj s1 1#32 s1Obj.cap newPayload newLen else o)) →
          (¬ inPlace → ∃ objs1, DecObjRel s1 σ.objs objs1 ∧
            objs' = mkStrObj r 1#32 newCap newPayload newLen :: objs1) →
          K (Word.i64 r) { σ with st := st', objs := objs' }

/-- Inline/runtime `String.*` semantics over `HState`. -/
@[expose] def HStringPrimWp (parts : List String) (as : List Word)
    (K : HPost) (X : HXPost) (σ : HState) : Prop :=
  match parts, as with
  | ["length"], [ws] | ["Internal", "length"], [ws] =>
    match ws.toBV64? with
    | some s => ∃ sObj ∈ σ.objs, sObj.addr = s ∧ StrCanon sObj ∧
        K (Word.i64 ((BitVec.ofNat 64 sObj.strLen <<< 1) ||| 1#64)) σ
    | none => False
  | ["utf8ByteSize"], [ws] =>
    match ws.toBV64? with
    | some s => ∃ sObj ∈ σ.objs, sObj.addr = s ∧ StrCanon sObj ∧
        K (Word.i64 ((BitVec.ofNat 64 (sObj.arrSize - 1) <<< 1) ||| 1#64)) σ
    | none => False
  | ["propagateMark"], [_, w] => K w σ
  | ["append"], [w1, w2] | ["Internal", "append"], [w1, w2] =>
    match w1.toBV64?, w2.toBV64? with
    | some s1, some s2 => HStringAppendWp s1 s2 K X σ
    | _, _ => False
  | ["decEq"], [w1, w2] =>
    match w1.toBV64?, w2.toBV64? with
    | some s1, some s2 =>
      if s1 = s2 then K (Word.i8 1#8) σ
      else ∃ s1Obj ∈ σ.objs, s1Obj.addr = s1 ∧ StrCanon s1Obj ∧
        ∃ s2Obj ∈ σ.objs, s2Obj.addr = s2 ∧ StrCanon s2Obj ∧
          K (Word.i8 ((strCmpOpVal 0#64 (strPayload s1Obj) (strPayload s2Obj)).setWidth 8)) σ
    | _, _ => False
  | ["decidableLT"], [w1, w2] =>
    match w1.toBV64?, w2.toBV64? with
    | some s1, some s2 =>
      if s1 = s2 then K (Word.i8 0#8) σ
      else ∃ s1Obj ∈ σ.objs, s1Obj.addr = s1 ∧ StrCanon s1Obj ∧
        ∃ s2Obj ∈ σ.objs, s2Obj.addr = s2 ∧ StrCanon s2Obj ∧
          K (Word.i8 ((strCmpOpVal 1#64 (strPayload s1Obj) (strPayload s2Obj)).setWidth 8)) σ
    | _, _ => False
  | _, _ => False

/-- WP of `lcnf_array_set(rt, arr, idx, v, 0)` over `HState`. -/
@[expose] def HArraySetWp (arr idx v : BitVec 64) (K : HPost) (σ : HState) : Prop :=
  ∃ (k : Nat) (hk : k < σ.objs.length),
    let arrObj := σ.objs[k]'hk
    arrObj.addr = arr ∧ ArrCanon arrObj ∧ arrObj.addr ∉ arrObj.fields ∧
    let iNat := if (idx &&& 1#64) ≠ 0#64 then (idx >>> 1).toNat else arrObj.fields.length
    if hlt : iNat < arrObj.fields.length then
      let old := arrObj.fields[iNat]'hlt
      (arrObj.rc ≠ 1#32 →
        canAllocBytesR0 σ.st (arrAllocBytes arrObj.cap) ∧
        (∀ y ∈ σ.objs.eraseIdx k, 0 < y.rc.toInt →
          y.rc.toInt + (arrObj.fields.count y.addr : Int) < 2147483648)) ∧
      (arrObj.rc = 1#32 → old ≠ 0#64 → (old &&& 1#64) = 0#64 →
        let mid2 := mkArrObj arr 1#32 arrObj.cap (arrObj.fields.set iNat v) :: σ.objs.eraseIdx k
        ∀ o2 ∈ mid2, o2.addr = old → o2.rc = 1#32 →
          mid2.length ≤ σ.st.workCap ∧ lcnfHeapClosed mid2 ∧ RcSound old mid2) ∧
      (old ≠ 0#64 → (old &&& 1#64) = 0#64 → (v &&& 1#64) = 0#64 →
        ∃ vo ∈ σ.objs, vo.addr = v) ∧
      ∀ r st' objs',
        r ≠ 0#64 → r.toNat % 8 = 0 → st'.PreservesMeta σ.st → st'.rem ≤ σ.st.rem →
        (arrObj.rc = 1#32 → r = arr) →
        ∀ (rObj : LcnfObj) (mid1 mid2 : List LcnfObj),
          rObj = mkArrObj r 1#32 arrObj.cap (arrObj.fields.set iNat v) →
          (arrObj.rc = 1#32 → mid1 = σ.objs.eraseIdx k) →
          (arrObj.rc ≠ 1#32 →
            mid1 = (incChildrenObjs arrObj.fields (σ.objs.eraseIdx k)).insertIdx k
              (arrObj.withRc (decNonExclRc arrObj.rc))) →
          mid2 = rObj :: mid1 → DecObjRel old mid2 objs' →
          K (Word.i64 r) { σ with st := st', objs := objs' }
    else
      ((v ≠ 0#64 ∧ (v &&& 1#64) = 0#64) →
        ∃ vo ∈ σ.objs, vo.addr = v ∧
          (vo.rc = 1#32 → σ.objs.length ≤ σ.st.workCap ∧ RcSound v σ.objs)) ∧
      ∀ st' objs', st'.PreservesMeta σ.st → st'.rem = σ.st.rem → DecObjRel v σ.objs objs' →
        K (Word.i64 arr) { σ with st := st', objs := objs' }

/-- Inline/runtime `Array.*` semantics over `HState`. -/
@[expose] def HArrayPrimWp (op : String) (as : List Word)
    (K : HPost) (X : HXPost) (σ : HState) : Prop :=
  match op, as with
  | "size", [_, wa] =>
    match wa.toBV64? with
    | some arr => ∃ arrObj ∈ σ.objs, arrObj.addr = arr ∧ ArrCanon arrObj ∧
        K (Word.i64 ((BitVec.ofNat 64 arrObj.fields.length <<< 1) ||| 1#64)) σ
    | none => False
  | "usize", [_, wa] =>
    match wa.toBV64? with
    | some arr => ∃ arrObj ∈ σ.objs, arrObj.addr = arr ∧ ArrCanon arrObj ∧
        K (Word.i64 (BitVec.ofNat 64 arrObj.fields.length)) σ
    | none => False
  | "propagateMark", [_, _, _, ys] => K ys σ
  | "empty", [_] =>
    canAllocBytesR0 σ.st (arrAllocBytes 0) ∧
    ∀ p st', p ≠ 0#64 → p.toNat % 8 = 0 → st'.PreservesMeta σ.st → st'.rem ≤ σ.st.rem →
      let arrObj := mkArrObj p 1#32 0 []
      ArrCanon arrObj → K (Word.i64 p) { σ with st := st', objs := arrObj :: σ.objs }
  | "mkEmpty", [_, wc] | "emptyWithCapacity", [_, wc] =>
    match wc.toBV64? with
    | none => False
    | some cap =>
      let c := if (cap &&& 1#64) ≠ 0#64 then (cap >>> 1).toNat else 0
      if c ≤ arrMaxCap then
        canAllocBytesR0 σ.st (arrAllocBytes c) ∧
        ∀ p st', p ≠ 0#64 → p.toNat % 8 = 0 → st'.PreservesMeta σ.st → st'.rem ≤ σ.st.rem →
          let arrObj := mkArrObj p 1#32 c []
          ArrCanon arrObj → K (Word.i64 p) { σ with st := st', objs := arrObj :: σ.objs }
      else X panicCapCode σ
  | "push", [_, wa, wv] =>
    match wa.toBV64?, wv.toBV64? with
    | some arr, some v =>
      ∃ (k : Nat) (hk : k < σ.objs.length),
        let arrObj := σ.objs[k]'hk
        let childObjs := σ.objs.eraseIdx k
        arrObj.addr = arr ∧ ArrCanon arrObj ∧
        (arrObj.rc ≠ 1#32 →
          (∀ f ∈ arrObj.fields, (f &&& 1#64) = 0#64 → ∃ y ∈ childObjs, y.addr = f) ∧
          (∀ y ∈ childObjs, 0 < y.rc.toInt →
            y.rc.toInt + (arrObj.fields.count y.addr : Int) < 2147483648)) ∧
        if arrObj.cap ≤ arrObj.fields.length ∧ arrMaxCap ≤ arrObj.cap then X panicCapCode σ
        else
          let newCap := arrEnsureCap arrObj.fields.length arrObj.cap 1#64
          let needAlloc := arrObj.rc ≠ 1#32 ∨ arrObj.fields.length ≥ arrObj.cap
          (needAlloc → canAllocBytesR0 σ.st (arrAllocBytes newCap)) ∧
          ∀ r st' childObjs',
            r ≠ 0#64 → r.toNat % 8 = 0 → st'.PreservesMeta σ.st → st'.rem ≤ σ.st.rem →
            (arrObj.rc = 1#32 → arrObj.fields.length < arrObj.cap → r = arr ∧ st' = σ.st) →
            let rObj := mkArrObj r 1#32 newCap (arrObj.fields ++ [v])
            ArrCanon rObj →
            (arrObj.rc = 1#32 → childObjs' = childObjs) →
            (arrObj.rc ≠ 1#32 → childObjs' = incChildrenObjs arrObj.fields childObjs) →
            let objs' :=
              if arrObj.rc = 1#32 then rObj :: childObjs'
              else rObj :: arrObj.withRc (decNonExclRc arrObj.rc) :: childObjs'
            K (Word.i64 r) { σ with st := st', objs := objs' }
    | _, _ => False
  | "get!Internal", [_, wdv, wa, wi] =>
    match wdv.toBV64?, wa.toBV64?, wi.toBV64? with
    | some dv, some arr, some idx =>
      ∃ arrObj ∈ σ.objs, arrObj.addr = arr ∧ ArrCanon arrObj ∧
        let ret :=
          if (idx &&& 1#64) ≠ 0#64 then
            if h : (idx >>> 1).toNat < arrObj.fields.length then arrObj.fields[(idx >>> 1).toNat]
            else dv
          else dv
        ((ret ≠ 0#64 ∧ (ret &&& 1#64) = 0#64) → ∃ o ∈ σ.objs, o.addr = ret) ∧
        let objs' :=
          if ret = 0#64 ∨ (ret &&& 1#64) ≠ 0#64 then σ.objs
          else σ.objs.map fun o => if o.addr = ret then o.withRc (incRcVal o.rc) else o
        K (Word.i64 ret) { σ with objs := objs' }
    | _, _, _ => False
  | "get!InternalBorrowed", [_, wdv, wa, wi] =>
    match wdv.toBV64?, wa.toBV64?, wi.toBV64? with
    | some dv, some arr, some idx =>
      ∃ arrObj ∈ σ.objs, arrObj.addr = arr ∧ ArrCanon arrObj ∧
        let ret :=
          if (idx &&& 1#64) ≠ 0#64 then
            if h : (idx >>> 1).toNat < arrObj.fields.length then arrObj.fields[(idx >>> 1).toNat]
            else dv
          else dv
        K (Word.i64 ret) σ
    | _, _, _ => False
  | "set!", [_, wa, wi, wv] | "set", [_, wa, wi, wv, _] =>
    match wa.toBV64?, wi.toBV64?, wv.toBV64? with
    | some arr, some idx, some v => HArraySetWp arr idx v K σ
    | _, _, _ => False
  | _, _ => False

/-- Inline/runtime `ByteArray.*` semantics over `HState`. -/
@[expose] def HByteArrayPrimWp (op : String) (as : List Word)
    (K : HPost) (X : HXPost) (σ : HState) : Prop :=
  match op, as with
  | "size", [wba] =>
    match wba.toBV64? with
    | some ba => ∃ baObj ∈ σ.objs, baObj.addr = ba ∧ BaCanon baObj ∧
        K (Word.i64 ((BitVec.ofNat 64 baObj.arrSize <<< 1) ||| 1#64)) σ
    | none => False
  | "usize", [wba] =>
    match wba.toBV64? with
    | some ba => ∃ baObj ∈ σ.objs, baObj.addr = ba ∧ BaCanon baObj ∧
        K (Word.i64 (BitVec.ofNat 64 baObj.arrSize)) σ
    | none => False
  | "propagateMark", [_, b] => K b σ
  | "get!", [wba, wi] | "get", [wba, wi, _] =>
    match wba.toBV64?, wi.toBV64? with
    | some ba, some idx => ∃ baObj ∈ σ.objs, baObj.addr = ba ∧ BaCanon baObj ∧
        K (Word.i8 ((baGetVal baObj.scalarData idx 0#64).setWidth 8)) σ
    | _, _ => False
  | "push", [wba, wb] =>
    match wba.toBV64?, wb.toBits? 8 with
    | some ba, some b =>
      ∃ (k : Nat) (hk : k < σ.objs.length),
        let baObj := σ.objs[k]'hk
        baObj.addr = ba ∧ BaCanon baObj ∧
        if baObj.cap ≤ baObj.arrSize ∧ baMaxCap ≤ baObj.cap then X panicCapCode σ
        else
          let newCap := baEnsureCap baObj.arrSize baObj.cap 1#64
          let needAlloc := baObj.rc ≠ 1#32 ∨ baObj.arrSize ≥ baObj.cap
          (needAlloc → canAllocBytesR0 σ.st (baAllocBytes newCap)) ∧
          ∀ r st',
            r ≠ 0#64 → r.toNat % 8 = 0 → st'.PreservesMeta σ.st → st'.rem ≤ σ.st.rem →
            (baObj.rc = 1#32 → baObj.arrSize < baObj.cap → r = ba ∧ st' = σ.st) →
            let rObj := mkBaObj r 1#32 newCap (baObj.scalarData ++ [UInt8.ofNat b.toNat])
            BaCanon rObj →
            let objs' :=
              if baObj.rc = 1#32 then σ.objs.set k rObj
              else rObj :: σ.objs.set k (baObj.withRc (decNonExclRc baObj.rc))
            K (Word.i64 r) { σ with st := st', objs := objs' }
    | _, _ => False
  | _, _ => False

/-- Top-level dispatch for built-in primitives (`Lower.externPrim`) at Tier H. -/
@[expose] def HPrim.wp (rt : BitVec 64) (name : String) (as : List Word)
    (K : HPost) (X : HXPost) (σ : HState) : Prop :=
  match splitDot name with
  | ["Nat", op] => HNatPrimWp rt op as K X σ
  | ["Array", op] => HArrayPrimWp op as K X σ
  | "String" :: rest => HStringPrimWp rest as K X σ
  | ["ByteArray", op] => HByteArrayPrimWp op as K X σ
  | ["System", "Platform", "getNumBits"] => K (Word.i64 (BitVec.ofNat 64 (2 * 64 + 1))) σ
  | ["getObjTagNat"] =>
    let wx? : Option Word := match as with | [_, w] => some w | [w] => some w | _ => none
    match wx?.bind Word.toBV64? with
    | some x =>
      if (x &&& 1#64) ≠ 0#64 then K (Word.i64 x) σ
      else ∃ o ∈ σ.objs, o.addr = x ∧
        K (Word.i64 ((BitVec.ofNat 64 o.tag <<< 1) ||| 1#64)) σ
    | none => False
  | ["outOfBounds", "_redArg"] =>
    match as with | [w] => if w.toBV64?.isSome then X panicOobCode σ else False | _ => False
  | [ty, op] =>
    match uintWidth? ty with
    | some w => HUintPrimWp rt w op as K σ
    | none => False
  | _ => False

/-! ## 3. Primitive Monotonicity & Fast-Path Lemmas -/

private theorem HNatArithSlowWp_mono {rt : BitVec 64} {op : Nat} {a b : BitVec 64} {resW : Nat}
    {K₁ K₂ : HPost} (hK : ∀ r σ, K₁ r σ → K₂ r σ) {σ : HState}
    (h : HNatArithSlowWp rt op a b resW K₁ σ) : HNatArithSlowWp rt op a b resW K₂ σ := by
  rcases h with ⟨aVal, bVal, ha, hb, hok, hk⟩
  exact ⟨aVal, bVal, ha, hb, hok, fun res st' scr' objs' h1 h2 h3 h4 =>
    hK _ _ (hk res st' scr' objs' h1 h2 h3 h4)⟩

private theorem HNatBitsSlowWp_mono {rt : BitVec 64} {op : Nat} {a b : BitVec 64} {resW : Nat}
    {K₁ K₂ : HPost} (hK : ∀ r σ, K₁ r σ → K₂ r σ) {σ : HState}
    (h : HNatBitsSlowWp rt op a b resW K₁ σ) : HNatBitsSlowWp rt op a b resW K₂ σ := by
  rcases h with ⟨aVal, ha, hok, hk⟩
  exact ⟨aVal, ha, hok, fun res st' scr' objs' h1 h2 h3 h4 =>
    hK _ _ (hk res st' scr' objs' h1 h2 h3 h4)⟩

private theorem HNatReprFastWp_mono {n : BitVec 64} {K₁ K₂ : HPost} {X₁ X₂ : HXPost}
    (hK : ∀ r σ, K₁ r σ → K₂ r σ) (hX : ∀ c σ, X₁ c σ → X₂ c σ) {σ : HState}
    (h : HNatReprFastWp n K₁ X₁ σ) : HNatReprFastWp n K₂ X₂ σ := by
  rcases h with ⟨val, hnih, hrest⟩
  refine ⟨val, hnih, ?_⟩
  dsimp only at hrest ⊢
  by_cases hsc : (n &&& 1#64) ≠ 0#64
  · rw [ite_eq_left hsc] at hrest ⊢
    exact ⟨hrest.1, fun s st' a1 a2 a3 a4 a5 => hK _ _ (hrest.2 s st' a1 a2 a3 a4 a5)⟩
  · rw [ite_eq_right hsc] at hrest ⊢
    rcases hrest with ⟨nObj, hm, had, hc, hrc, hif⟩
    refine ⟨nObj, hm, had, hc, hrc, ?_⟩
    by_cases hcn : trimZeroLimbsLen nObj.limbs nObj.arrSize = 0
    · rw [ite_eq_left hcn] at hif ⊢
      exact ⟨hif.1, fun s st' objs' a1 a2 a3 a4 a5 a6 =>
        hK _ _ (hif.2 s st' objs' a1 a2 a3 a4 a5 a6)⟩
    · rw [ite_eq_right hcn] at hif ⊢
      by_cases hcap : mpzMaxLimbsNat < trimZeroLimbsLen nObj.limbs nObj.arrSize
      · rw [ite_eq_left hcap] at hif ⊢; exact hX _ _ hif
      · rw [ite_eq_right hcap] at hif ⊢
        exact ⟨hif.1, fun s st' objs' a1 a2 a3 a4 a5 a6 =>
          hK _ _ (hif.2 s st' objs' a1 a2 a3 a4 a5 a6)⟩

private theorem HNatPrimWp_mono {rt : BitVec 64} {K₁ K₂ : HPost} {X₁ X₂ : HXPost}
    (hK : ∀ r σ, K₁ r σ → K₂ r σ) (hX : ∀ c σ, X₁ c σ → X₂ c σ)
    (op : String) (as : List Word) (σ : HState)
    (h : HNatPrimWp rt op as K₁ X₁ σ) : HNatPrimWp rt op as K₂ X₂ σ := by
  unfold HNatPrimWp at h ⊢
  cases hinfo : natBinSlowInfo? op with
  | some p =>
    rcases p with ⟨code, resW, isBits⟩
    simp only [hinfo] at h ⊢
    cases as with
    | nil => exact False.elim h
    | cons wa rest => cases rest with
      | nil => exact False.elim h
      | cons wb tail => cases tail with
        | cons _ _ => exact False.elim h
        | nil =>
          cases ha : wa.toBV64? with
          | none => simp [ha] at h
          | some a => cases hb : wb.toBV64? with
            | none => simp [ha, hb] at h
            | some b =>
              simp only [ha, hb] at h ⊢
              cases hf : natBinFast? op a b with
              | some w => simp only [hf] at h ⊢; exact hK w σ h
              | none =>
                simp only [hf] at h ⊢
                cases isBits
                · exact HNatArithSlowWp_mono hK h
                · exact HNatBitsSlowWp_mono hK h
  | none =>
    simp only [hinfo] at h ⊢
    by_cases h1 : op = "pred"
    · subst h1; cases as with
      | nil => exact False.elim h
      | cons wa tail => cases tail with
        | cons _ _ => exact False.elim h
        | nil => cases ha : wa.toBV64? with
          | none => simp [ha] at h
          | some a =>
            simp only [ha] at h ⊢
            by_cases hc : ((a &&& 1#64) != 0#64) = true
            · rw [ite_eq_left hc] at h ⊢; exact hK _ _ h
            · rw [ite_eq_right hc] at h ⊢; exact HNatArithSlowWp_mono hK h
    · by_cases h2 : op = "pow"
      · subst h2; cases as with
        | nil => exact False.elim h
        | cons wa rest => cases rest with
          | nil => exact False.elim h
          | cons wb tail => cases tail with
            | cons _ _ => exact False.elim h
            | nil => cases ha : wa.toBV64? with
              | none => simp [ha] at h
              | some _ => cases hb : wb.toBV64? with
                | none => simp [ha, hb] at h
                | some _ =>
                  simp only [ha, hb] at h ⊢
                  rcases h with ⟨aVal, bVal, b1, b2, b3, hk⟩
                  exact ⟨aVal, bVal, b1, b2, b3, fun r st' scr' objs' c1 c2 c3 c4 c5 =>
                    hK _ _ (hk r st' scr' objs' c1 c2 c3 c4 c5)⟩
      · by_cases h3 : op = "gcd"
        · subst h3; cases as with
          | nil => exact False.elim h
          | cons wa rest => cases rest with
            | nil => exact False.elim h
            | cons wb tail => cases tail with
              | cons _ _ => exact False.elim h
              | nil => cases ha : wa.toBV64? with
                | none => simp [ha] at h
                | some _ => cases hb : wb.toBV64? with
                  | none => simp [ha, hb] at h
                  | some _ =>
                    simp only [ha, hb] at h ⊢
                    rcases h with ⟨aVal, bVal, b1, b2, b3, hk⟩
                    exact ⟨aVal, bVal, b1, b2, b3, fun r st' scr' objs' c1 c2 c3 c4 c5 =>
                      hK _ _ (hk r st' scr' objs' c1 c2 c3 c4 c5)⟩
        · by_cases h4 : op = "log2"
          · subst h4; cases as with
            | nil => exact False.elim h
            | cons wa tail => cases tail with
              | cons _ _ => exact False.elim h
              | nil => cases ha : wa.toBV64? with
                | none => simp [ha] at h
                | some _ => simp only [ha] at h ⊢; exact HNatBitsSlowWp_mono hK h
          · by_cases h5 : op = "reprFast"
            · subst h5; cases as with
              | nil => exact False.elim h
              | cons wn tail => cases tail with
                | cons _ _ => exact False.elim h
                | nil => cases hn : wn.toBV64? with
                  | none => simp [hn] at h
                  | some _ => simp only [hn] at h ⊢; exact HNatReprFastWp_mono hK hX h
            · simp [h1, h2, h3, h4, h5] at h

private theorem HUintOfNatWp_mono {rt : BitVec 64} {w : Nat} {wa : Word} {decAfter : Bool}
    {K₁ K₂ : HPost} (hK : ∀ r σ, K₁ r σ → K₂ r σ) {σ : HState}
    (h : HUintOfNatWp rt w wa decAfter K₁ σ) : HUintOfNatWp rt w wa decAfter K₂ σ := by
  unfold HUintOfNatWp at h ⊢
  cases ha : wa.toBV64? with
  | none => simp [ha] at h
  | some a =>
    simp only [ha] at h ⊢
    cases decAfter
    · simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      by_cases hsc : ((a &&& 1#64) != 0#64) = true
      · rw [ite_eq_left hsc] at h ⊢; exact hK _ _ h
      · rw [ite_eq_right hsc] at h ⊢; exact HNatBitsSlowWp_mono hK h
    · simp only [↓reduceIte] at h ⊢
      have hcont : ∀ r σ', HDecN a .tobject true 1 (K₁ r) σ' →
          HDecN a .tobject true 1 (K₂ r) σ' :=
        fun r σ' hc => HDecN_mono (hK r) 1 σ' hc
      by_cases hsc : ((a &&& 1#64) != 0#64) = true
      · rw [ite_eq_left hsc] at h ⊢; exact hcont _ _ h
      · rw [ite_eq_right hsc] at h ⊢; exact HNatBitsSlowWp_mono hcont h

private theorem HUintPrimWp_mono {rt : BitVec 64} {w : Nat} {op : String} {as : List Word}
    {K₁ K₂ : HPost} (hK : ∀ r σ, K₁ r σ → K₂ r σ) {σ : HState}
    (h : HUintPrimWp rt w op as K₁ σ) : HUintPrimWp rt w op as K₂ σ := by
  unfold HUintPrimWp at h ⊢
  cases hp : uintPure? w op as with
  | some r => simp only [hp] at h ⊢; exact hK r σ h
  | none =>
    simp only [hp] at h ⊢
    by_cases h1 : op = "ofNat"
    · subst h1; cases as with
      | nil => exact False.elim h
      | cons wa tail => cases tail with
        | cons _ _ => exact False.elim h
        | nil => exact HUintOfNatWp_mono hK h
    · by_cases h2 : op = "ofNatLT"
      · subst h2; cases as with
        | nil => exact False.elim h
        | cons wa tail => cases tail with
          | nil => exact HUintOfNatWp_mono hK h
          | cons _ tail2 => cases tail2 with
            | nil => exact HUintOfNatWp_mono hK h
            | cons _ _ => exact False.elim h
      · by_cases h3 : op = "ofBitVec"
        · subst h3; cases as with
          | nil => exact False.elim h
          | cons wa tail => cases tail with
            | cons _ _ => exact False.elim h
            | nil => exact HUintOfNatWp_mono hK h
        · by_cases h4 : op = "toNat" ∨ op = "toBitVec"
          · rcases h4 with rfl | rfl <;> (
              cases as with
              | nil => exact False.elim h
              | cons a tail => cases tail with
                | cons _ _ => exact False.elim h
                | nil => cases hto : a.toBits? w with
                  | none => simp [hto] at h
                  | some av =>
                    simp only [hto] at h ⊢
                    by_cases hc : (w < 64 || (av.setWidth 64 >>> 63) == 0#64) = true
                    · rw [ite_eq_left hc] at h ⊢; exact hK _ _ h
                    · rw [ite_eq_right hc] at h ⊢; exact HNatBitsSlowWp_mono hK h)
          · rcases not_or.mp h4 with ⟨h4a, h4b⟩
            simp [h1, h2, h3, h4a, h4b] at h

private theorem HStringAppendWp_mono {s1 s2 : BitVec 64} {K₁ K₂ : HPost} {X₁ X₂ : HXPost}
    (hK : ∀ r σ, K₁ r σ → K₂ r σ) (hX : ∀ c σ, X₁ c σ → X₂ c σ) {σ : HState}
    (h : HStringAppendWp s1 s2 K₁ X₁ σ) : HStringAppendWp s1 s2 K₂ X₂ σ := by
  rcases h with ⟨o1, hm1, ha1, hc1, o2, hm2, ha2, hc2, hrest⟩
  refine ⟨o1, hm1, ha1, hc1, o2, hm2, ha2, hc2, ?_⟩
  dsimp only at hrest ⊢
  by_cases h0 : (strPayload o2).length = 0
  · rw [ite_eq_left h0] at hrest ⊢; exact hK _ _ hrest
  · rw [ite_eq_right h0] at hrest ⊢
    by_cases hcap : strMaxCap ≤ (strPayload o1).length + (strPayload o2).length
    · rw [ite_eq_left hcap] at hrest ⊢; exact hX _ _ hrest
    · rw [ite_eq_right hcap] at hrest ⊢
      exact ⟨hrest.1, fun r st' objs' a1 a2 a3 a4 a5 a6 =>
        hK _ _ (hrest.2 r st' objs' a1 a2 a3 a4 a5 a6)⟩

private theorem HStringPrimWp_mono {parts : List String} {as : List Word}
    {K₁ K₂ : HPost} {X₁ X₂ : HXPost}
    (hK : ∀ r σ, K₁ r σ → K₂ r σ) (hX : ∀ c σ, X₁ c σ → X₂ c σ) {σ : HState}
    (h : HStringPrimWp parts as K₁ X₁ σ) : HStringPrimWp parts as K₂ X₂ σ := by
  unfold HStringPrimWp at h ⊢
  by_cases h1 : parts = ["length"] ∨ parts = ["Internal", "length"]
  · rcases h1 with rfl | rfl <;> (
      cases as with
      | nil => exact False.elim h
      | cons ws tail => cases tail with
        | cons _ _ => exact False.elim h
        | nil => cases hs : ws.toBV64? with
          | none => simp [hs] at h
          | some _ =>
            simp only [hs] at h ⊢
            rcases h with ⟨o, hm, ha, hc, hk⟩; exact ⟨o, hm, ha, hc, hK _ _ hk⟩)
  · by_cases h2 : parts = ["utf8ByteSize"]
    · subst h2; cases as with
      | nil => exact False.elim h
      | cons ws tail => cases tail with
        | cons _ _ => exact False.elim h
        | nil => cases hs : ws.toBV64? with
          | none => simp [hs] at h
          | some _ =>
            simp only [hs] at h ⊢
            rcases h with ⟨o, hm, ha, hc, hk⟩; exact ⟨o, hm, ha, hc, hK _ _ hk⟩
    · by_cases h3 : parts = ["propagateMark"]
      · subst h3; cases as with
        | nil => exact False.elim h
        | cons _ rest => cases rest with
          | nil => exact False.elim h
          | cons _ tail => cases tail with
            | nil => exact hK _ _ h
            | cons _ _ => exact False.elim h
      · by_cases h4 : parts = ["append"] ∨ parts = ["Internal", "append"]
        · rcases h4 with rfl | rfl <;> (
            cases as with
            | nil => exact False.elim h
            | cons w1 rest => cases rest with
              | nil => exact False.elim h
              | cons w2 tail => cases tail with
                | cons _ _ => exact False.elim h
                | nil => cases h1' : w1.toBV64? with
                  | none => simp [h1'] at h
                  | some _ => cases h2' : w2.toBV64? with
                    | none => simp [h1', h2'] at h
                    | some _ =>
                      simp only [h1', h2'] at h ⊢; exact HStringAppendWp_mono hK hX h)
        · by_cases h5 : parts = ["decEq"] ∨ parts = ["decidableLT"]
          · rcases h5 with rfl | rfl <;> (
              cases as with
              | nil => exact False.elim h
              | cons w1 rest => cases rest with
                | nil => exact False.elim h
                | cons w2 tail => cases tail with
                  | cons _ _ => exact False.elim h
                  | nil => cases h1' : w1.toBV64? with
                    | none => simp [h1'] at h
                    | some s1 => cases h2' : w2.toBV64? with
                      | none => simp [h1', h2'] at h
                      | some s2 =>
                        simp only [h1', h2'] at h ⊢
                        by_cases heq : s1 = s2
                        · rw [ite_eq_left heq] at h ⊢; exact hK _ _ h
                        · rw [ite_eq_right heq] at h ⊢
                          rcases h with ⟨o1, hm1, ha1, hc1, o2, hm2, ha2, hc2, hk⟩
                          exact ⟨o1, hm1, ha1, hc1, o2, hm2, ha2, hc2, hK _ _ hk⟩)
          · rcases not_or.mp h1 with ⟨h1a, h1b⟩
            rcases not_or.mp h4 with ⟨h4a, h4b⟩
            rcases not_or.mp h5 with ⟨h5a, h5b⟩
            cases parts with
            | nil => exact False.elim h
            | cons p ps => cases ps with
              | nil =>
                have : p ≠ "length" ∧ p ≠ "utf8ByteSize" ∧ p ≠ "propagateMark" ∧
                    p ≠ "append" ∧ p ≠ "decEq" ∧ p ≠ "decidableLT" :=
                  ⟨fun e => h1a (by simp [e]), fun e => h2 (by simp [e]),
                   fun e => h3 (by simp [e]), fun e => h4a (by simp [e]),
                   fun e => h5a (by simp [e]), fun e => h5b (by simp [e])⟩
                simp [this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2.1,
                  this.2.2.2.2.2] at h
              | cons p2 ps2 => cases ps2 with
                | cons _ _ => simp at h
                | nil =>
                  by_cases hp : p = "Internal"
                  · subst hp
                    have : p2 ≠ "length" ∧ p2 ≠ "append" :=
                      ⟨fun e => h1b (by simp [e]), fun e => h4b (by simp [e])⟩
                    simp [this.1, this.2] at h
                  · simp [hp] at h

private theorem HArraySetWp_mono {arr idx v : BitVec 64} {K₁ K₂ : HPost}
    (hK : ∀ r σ, K₁ r σ → K₂ r σ) {σ : HState}
    (h : HArraySetWp arr idx v K₁ σ) : HArraySetWp arr idx v K₂ σ := by
  rcases h with ⟨k, hk, a1, a2, a3, hif⟩
  refine ⟨k, hk, a1, a2, a3, ?_⟩
  dsimp only at hif ⊢
  by_cases hlt :
      (if (idx &&& 1#64) ≠ 0#64 then (idx >>> 1).toNat else (σ.objs[k]'hk).fields.length) <
      (σ.objs[k]'hk).fields.length
  · rw [dite_eq_left hlt] at hif ⊢
    rcases hif with ⟨b1, b2, b3, hcont⟩
    exact ⟨b1, b2, b3, fun r st' objs' c1 c2 c3 c4 c5 rObj m1 m2 d1 d2 d3 d4 d5 =>
      hK _ _ (hcont r st' objs' c1 c2 c3 c4 c5 rObj m1 m2 d1 d2 d3 d4 d5)⟩
  · rw [dite_eq_right hlt] at hif ⊢
    exact ⟨hif.1, fun st' objs' c1 c2 c3 => hK _ _ (hif.2 st' objs' c1 c2 c3)⟩

private theorem HArrayPrimWp_mono {op : String} {as : List Word}
    {K₁ K₂ : HPost} {X₁ X₂ : HXPost}
    (hK : ∀ r σ, K₁ r σ → K₂ r σ) (hX : ∀ c σ, X₁ c σ → X₂ c σ) {σ : HState}
    (h : HArrayPrimWp op as K₁ X₁ σ) : HArrayPrimWp op as K₂ X₂ σ := by
  unfold HArrayPrimWp at h ⊢
  by_cases h1 : op = "size" ∨ op = "usize"
  · rcases h1 with rfl | rfl <;> (
      cases as with
      | nil => exact False.elim h
      | cons _ rest => cases rest with
        | nil => exact False.elim h
        | cons wa tail => cases tail with
          | cons _ _ => exact False.elim h
          | nil => cases ha : wa.toBV64? with
            | none => simp [ha] at h
            | some _ =>
              simp only [ha] at h ⊢
              rcases h with ⟨o, hm, ha', hc, hk⟩; exact ⟨o, hm, ha', hc, hK _ _ hk⟩)
  · by_cases h2 : op = "propagateMark"
    · subst h2; cases as with
      | nil => exact False.elim h
      | cons _ r1 => cases r1 with
        | nil => exact False.elim h
        | cons _ r2 => cases r2 with
          | nil => exact False.elim h
          | cons _ r3 => cases r3 with
            | nil => exact False.elim h
            | cons _ tail => cases tail with
              | nil => exact hK _ _ h
              | cons _ _ => exact False.elim h
    · by_cases h3 : op = "empty"
      · subst h3; cases as with
        | nil => exact False.elim h
        | cons _ tail => cases tail with
          | cons _ _ => exact False.elim h
          | nil => exact ⟨h.1, fun p st' a1 a2 a3 a4 a5 => hK _ _ (h.2 p st' a1 a2 a3 a4 a5)⟩
      · by_cases h4 : op = "mkEmpty" ∨ op = "emptyWithCapacity"
        · rcases h4 with rfl | rfl <;> (
            cases as with
            | nil => exact False.elim h
            | cons _ rest => cases rest with
              | nil => exact False.elim h
              | cons wc tail => cases tail with
                | cons _ _ => exact False.elim h
                | nil => cases hc : wc.toBV64? with
                  | none => simp [hc] at h
                  | some cap =>
                    simp only [hc] at h ⊢
                    by_cases hle :
                        (if (cap &&& 1#64) ≠ 0#64 then (cap >>> 1).toNat else 0) ≤ arrMaxCap
                    · rw [ite_eq_left hle] at h ⊢
                      exact ⟨h.1, fun p st' a1 a2 a3 a4 a5 => hK _ _ (h.2 p st' a1 a2 a3 a4 a5)⟩
                    · rw [ite_eq_right hle] at h ⊢; exact hX _ _ h)
        · by_cases h5 : op = "push"
          · subst h5; cases as with
            | nil => exact False.elim h
            | cons _ r1 => cases r1 with
              | nil => exact False.elim h
              | cons wa r2 => cases r2 with
                | nil => exact False.elim h
                | cons wv tail => cases tail with
                  | cons _ _ => exact False.elim h
                  | nil => cases ha : wa.toBV64? with
                    | none => simp [ha] at h
                    | some _ => cases hv : wv.toBV64? with
                      | none => simp [ha, hv] at h
                      | some _ =>
                        simp only [ha, hv] at h ⊢
                        rcases h with ⟨k, hk, a1, a2, a3, hif⟩
                        refine ⟨k, hk, a1, a2, a3, ?_⟩
                        by_cases hcap : (σ.objs[k]'hk).cap ≤ (σ.objs[k]'hk).fields.length ∧
                            arrMaxCap ≤ (σ.objs[k]'hk).cap
                        · rw [ite_eq_left hcap] at hif ⊢; exact hX _ _ hif
                        · rw [ite_eq_right hcap] at hif ⊢
                          exact ⟨hif.1, fun r st' ch' b1 b2 b3 b4 b5 b6 b7 b8 =>
                            hK _ _ (hif.2 r st' ch' b1 b2 b3 b4 b5 b6 b7 b8)⟩
          · by_cases h6 : op = "get!Internal" ∨ op = "get!InternalBorrowed"
            · rcases h6 with rfl | rfl <;> (
                cases as with
                | nil => exact False.elim h
                | cons _ r1 => cases r1 with
                  | nil => exact False.elim h
                  | cons wdv r2 => cases r2 with
                    | nil => exact False.elim h
                    | cons wa r3 => cases r3 with
                      | nil => exact False.elim h
                      | cons wi tail => cases tail with
                        | cons _ _ => exact False.elim h
                        | nil => cases hdv : wdv.toBV64? with
                          | none => simp [hdv] at h
                          | some _ => cases ha : wa.toBV64? with
                            | none => simp [hdv, ha] at h
                            | some _ => cases hi : wi.toBV64? with
                              | none => simp [hdv, ha, hi] at h
                              | some _ =>
                                simp only [hdv, ha, hi] at h ⊢
                                first
                                  | (rcases h with ⟨o, hm, ha', hc, hpre, hk⟩;
                                     exact ⟨o, hm, ha', hc, hpre, hK _ _ hk⟩)
                                  | (rcases h with ⟨o, hm, ha', hc, hk⟩;
                                     exact ⟨o, hm, ha', hc, hK _ _ hk⟩))
            · by_cases h7 : op = "set!" ∨ op = "set"
              · rcases h7 with rfl | rfl <;> (
                  cases as with
                  | nil => exact False.elim h
                  | cons _ r1 => cases r1 with
                    | nil => exact False.elim h
                    | cons wa r2 => cases r2 with
                      | nil => exact False.elim h
                      | cons wi r3 => cases r3 with
                        | nil => exact False.elim h
                        | cons wv tail =>
                          have hstep : (match wa.toBV64?, wi.toBV64?, wv.toBV64? with
                              | some arr, some idx, some v => HArraySetWp arr idx v K₁ σ
                              | _, _, _ => False) →
                            (match wa.toBV64?, wi.toBV64?, wv.toBV64? with
                              | some arr, some idx, some v => HArraySetWp arr idx v K₂ σ
                              | _, _, _ => False) := by
                            intro h'
                            cases ha : wa.toBV64? with
                            | none => simp [ha] at h'
                            | some _ => cases hi : wi.toBV64? with
                              | none => simp [ha, hi] at h'
                              | some _ => cases hv : wv.toBV64? with
                                | none => simp [ha, hi, hv] at h'
                                | some _ =>
                                  simp only [ha, hi, hv] at h' ⊢; exact HArraySetWp_mono hK h'
                          cases tail with
                          | nil => first | exact hstep h | simp at h
                          | cons _ tail2 => cases tail2 with
                            | nil => first | exact hstep h | simp at h
                            | cons _ _ => simp at h)
              · rcases not_or.mp h1 with ⟨h1a, h1b⟩
                rcases not_or.mp h4 with ⟨h4a, h4b⟩
                rcases not_or.mp h6 with ⟨h6a, h6b⟩
                rcases not_or.mp h7 with ⟨h7a, h7b⟩
                simp [h1a, h1b, h2, h3, h4a, h4b, h5, h6a, h6b, h7a, h7b] at h

private theorem HByteArrayPrimWp_mono {op : String} {as : List Word}
    {K₁ K₂ : HPost} {X₁ X₂ : HXPost}
    (hK : ∀ r σ, K₁ r σ → K₂ r σ) (hX : ∀ c σ, X₁ c σ → X₂ c σ) {σ : HState}
    (h : HByteArrayPrimWp op as K₁ X₁ σ) : HByteArrayPrimWp op as K₂ X₂ σ := by
  unfold HByteArrayPrimWp at h ⊢
  by_cases h1 : op = "size" ∨ op = "usize"
  · rcases h1 with rfl | rfl <;> (
      cases as with
      | nil => exact False.elim h
      | cons wba tail => cases tail with
        | cons _ _ => exact False.elim h
        | nil => cases hba : wba.toBV64? with
          | none => simp [hba] at h
          | some _ =>
            simp only [hba] at h ⊢
            rcases h with ⟨o, hm, ha, hc, hk⟩; exact ⟨o, hm, ha, hc, hK _ _ hk⟩)
  · by_cases h2 : op = "propagateMark"
    · subst h2; cases as with
      | nil => exact False.elim h
      | cons _ rest => cases rest with
        | nil => exact False.elim h
        | cons _ tail => cases tail with
          | nil => exact hK _ _ h
          | cons _ _ => exact False.elim h
    · by_cases h3 : op = "get!" ∨ op = "get"
      · rcases h3 with rfl | rfl <;> (
          cases as with
          | nil => exact False.elim h
          | cons wba rest => cases rest with
            | nil => exact False.elim h
            | cons wi tail =>
              have hget : (match wba.toBV64?, wi.toBV64? with
                  | some ba, some idx => ∃ baObj ∈ σ.objs, baObj.addr = ba ∧ BaCanon baObj ∧
                      K₁ (Word.i8 ((baGetVal baObj.scalarData idx 0#64).setWidth 8)) σ
                  | _, _ => False) →
                (match wba.toBV64?, wi.toBV64? with
                  | some ba, some idx => ∃ baObj ∈ σ.objs, baObj.addr = ba ∧ BaCanon baObj ∧
                      K₂ (Word.i8 ((baGetVal baObj.scalarData idx 0#64).setWidth 8)) σ
                  | _, _ => False) := by
                intro h'
                cases hba : wba.toBV64? with
                | none => simp [hba] at h'
                | some _ => cases hi : wi.toBV64? with
                  | none => simp [hba, hi] at h'
                  | some _ =>
                    simp only [hba, hi] at h' ⊢
                    rcases h' with ⟨o, hm, ha, hc, hk⟩; exact ⟨o, hm, ha, hc, hK _ _ hk⟩
              cases tail with
              | nil => first | exact hget h | simp at h
              | cons _ tail2 => cases tail2 with
                | nil => first | exact hget h | simp at h
                | cons _ _ => simp at h)
      · by_cases h4 : op = "push"
        · subst h4; cases as with
          | nil => exact False.elim h
          | cons wba rest => cases rest with
            | nil => exact False.elim h
            | cons wb tail => cases tail with
              | cons _ _ => exact False.elim h
              | nil => cases hba : wba.toBV64? with
                | none => simp [hba] at h
                | some _ => cases hb : wb.toBits? 8 with
                  | none => simp [hba, hb] at h
                  | some _ =>
                    simp only [hba, hb] at h ⊢
                    rcases h with ⟨k, hk, a1, a2, hif⟩
                    refine ⟨k, hk, a1, a2, ?_⟩
                    by_cases hcap :
                        (σ.objs[k]'hk).cap ≤ (σ.objs[k]'hk).arrSize ∧
                        baMaxCap ≤ (σ.objs[k]'hk).cap
                    · rw [ite_eq_left hcap] at hif ⊢; exact hX _ _ hif
                    · rw [ite_eq_right hcap] at hif ⊢
                      exact ⟨hif.1, fun r st' b1 b2 b3 b4 b5 b6 =>
                        hK _ _ (hif.2 r st' b1 b2 b3 b4 b5 b6)⟩
        · rcases not_or.mp h1 with ⟨h1a, h1b⟩
          rcases not_or.mp h3 with ⟨h3a, h3b⟩
          simp [h1a, h1b, h2, h3a, h3b, h4] at h

theorem HPrim.wp_mono {rt : BitVec 64} {name : String} {as : List Word}
    {K₁ K₂ : HPost} {X₁ X₂ : HXPost}
    (hK : ∀ r σ, K₁ r σ → K₂ r σ) (hX : ∀ c σ, X₁ c σ → X₂ c σ) {σ : HState}
    (h : HPrim.wp rt name as K₁ X₁ σ) : HPrim.wp rt name as K₂ X₂ σ := by
  unfold HPrim.wp at h ⊢
  generalize splitDot name = parts at h ⊢
  revert h
  split
  · exact HNatPrimWp_mono hK hX _ _ _
  · exact HArrayPrimWp_mono hK hX
  · exact HStringPrimWp_mono hK hX
  · exact HByteArrayPrimWp_mono hK hX
  · exact hK _ _
  · intro h
    have hstep : ∀ w : Word,
        (match w.toBV64? with
         | some x =>
           if (x &&& 1#64) ≠ 0#64 then K₁ (Word.i64 x) σ
           else ∃ o ∈ σ.objs, o.addr = x ∧
             K₁ (Word.i64 ((BitVec.ofNat 64 o.tag <<< 1) ||| 1#64)) σ
         | none => False) →
        (match w.toBV64? with
         | some x =>
           if (x &&& 1#64) ≠ 0#64 then K₂ (Word.i64 x) σ
           else ∃ o ∈ σ.objs, o.addr = x ∧
             K₂ (Word.i64 ((BitVec.ofNat 64 o.tag <<< 1) ||| 1#64)) σ
         | none => False) := by
      intro w h'
      cases hw : w.toBV64? with
      | none => simp [hw] at h'
      | some x =>
        simp only [hw] at h' ⊢
        by_cases hsc : (x &&& 1#64) ≠ 0#64
        · rw [ite_eq_left hsc] at h' ⊢; exact hK _ _ h'
        · rw [ite_eq_right hsc] at h' ⊢
          rcases h' with ⟨o, hm, ha, hk⟩; exact ⟨o, hm, ha, hK _ _ hk⟩
    cases as with
    | nil => simp at h
    | cons a tail => cases tail with
      | nil => exact hstep a (by simpa using h)
      | cons b tail2 => cases tail2 with
        | nil => exact hstep b (by simpa using h)
        | cons _ _ => simp at h
  · intro h
    cases as with
    | nil => simp at h
    | cons w tail => cases tail with
      | cons _ _ => simp at h
      | nil =>
        change (if w.toBV64?.isSome then X₁ panicOobCode σ else False) at h
        change (if w.toBV64?.isSome then X₂ panicOobCode σ else False)
        by_cases hbv : w.toBV64?.isSome = true
        · rw [ite_eq_left hbv] at h ⊢; exact hX _ _ h
        · rw [ite_eq_right hbv] at h; exact False.elim h
  · split
    · exact HUintPrimWp_mono hK
    · exact False.elim
  · intro h; simp at h

/-- Fast-path helper for `Nat.add` on small tagged scalars (no overflow). -/
theorem HNatPrimWp_add_fast {rt : BitVec 64} {a b : BitVec 64} {K : HPost} {X : HXPost}
    {σ : HState}
    (ha : (a &&& 1#64) ≠ 0#64) (hb : (b &&& 1#64) ≠ 0#64)
    (hnoovf : ¬(((a - 1#64) + b) < b))
    (hK : K (Word.i64 ((a - 1#64) + b)) σ) :
    HNatPrimWp rt "add" [Word.i64 a, Word.i64 b] K X σ := by
  have hbit0 : ∀ x : BitVec 64, (x &&& 1#64) ≠ 0#64 → x[0] = true := by
    intro x hx
    cases h0 : x[0]
    · exfalso; apply hx; apply BitVec.eq_of_getElem_eq; intro i hi
      cases i with | zero => simp [h0] | succ _ => simp
    · rfl
  have hne : ((a &&& b) &&& 1#64) ≠ 0#64 := by
    intro heq
    have h0 := congrArg (fun x : BitVec 64 => x[0]) heq
    simp [hbit0 a ha, hbit0 b hb] at h0
  have hfast : natBinFast? "add" a b = some (Word.i64 ((a - 1#64) + b)) := by
    simp [natBinFast?, hne, hnoovf]
  simpa [HNatPrimWp, natBinSlowInfo?, Word.i64, Word.toBV64?, hfast] using hK

end LeanQbe.T.LeanLCNF.Sem
