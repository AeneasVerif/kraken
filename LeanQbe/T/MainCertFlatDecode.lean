/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Flat
public import LeanQbe.T.Module
public meta import Lean
public meta import LeanQbe.T.Flat
public meta import LeanQbe.T.Module

/-!
# Zero-Bytecode `.olean` Inverse Decoder for Materialized `TFlatFn` Slices (`MainCertFlatDecode`)

Pure compiled `MetaM` inverse of `InlineMeta.tflatToExpr` / `tflatFnToExpr` that decodes exposed
`TFlatFn` / `denoteFunc`-backed `Fn` slice expressions directly from `(← getEnv).find?` without
calling `evalExpr` on `fnsE` or requiring `meta import` of the inlined module.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

meta section

open Lean Meta

private partial def decodeNat : Lean.Expr → Option Nat
  | .lit (.natVal n) => some n
  | .const ``Nat.zero [] => some 0
  | .app (.const ``Nat.succ []) e => (· + 1) <$> decodeNat e
  | .mdata _ e => decodeNat e
  | e => if e.isAppOfArity ``OfNat.ofNat 3 then decodeNat (e.getArg! 1) else none

private def decodeNatM (e : Lean.Expr) : OptionT MetaM Nat :=
  OptionT.mk do
    match decodeNat e with
    | some n => return some n
    | none => return decodeNat (← whnf e)

private def decodeBool (e : Lean.Expr) : Option Bool :=
  match e.consumeMData with
  | .const ``Bool.true [] => some true
  | .const ``Bool.false [] => some false
  | _ => none

private def decodeString (e : Lean.Expr) : Option String :=
  match e.consumeMData with | .lit (.strVal s) => some s | _ => none

private def decodeBitVec (n : Nat) (e : Lean.Expr) : Option (BitVec n) :=
  let e := e.consumeMData
  if e.isAppOfArity ``BitVec.ofNat 2 then do
    let w ← decodeNat (e.getArg! 0)
    if w == n then BitVec.ofNat n <$> decodeNat (e.getArg! 1) else none
  else if e.isAppOfArity ``OfNat.ofNat 3 then
    BitVec.ofNat n <$> decodeNat (e.getArg! 1)
  else none

private def decodeFmt (e : Lean.Expr) : Option Fmt :=
  match e.consumeMData with
  | .const ``LeanQbe.T.Fmt.h [] => some .h | .const ``LeanQbe.T.Fmt.s [] => some .s
  | .const ``LeanQbe.T.Fmt.d [] => some .d | .const ``LeanQbe.T.Fmt.q [] => some .q
  | _ => none

private def tyAliasTable : List (Name × Ty) :=
  [ (``LeanQbe.T.Ty.bool, .bool), (``LeanQbe.T.i8, i8), (``LeanQbe.T.i16, i16)
  , (``LeanQbe.T.i32, i32), (``LeanQbe.T.i64, i64), (``LeanQbe.T.f16, f16)
  , (``LeanQbe.T.f32, f32), (``LeanQbe.T.f64, f64), (``LeanQbe.T.f128, f128)
  , (``LeanQbe.T.v4i32, v4i32), (``LeanQbe.T.v8i32, v8i32)
  , (``LeanQbe.T.v2i64, v2i64), (``LeanQbe.T.v4f32, v4f32) ]

private partial def decodeTy (e : Lean.Expr) : Option Ty :=
  let e := e.consumeMData
  match e with
  | .const nm [] => tyAliasTable.lookup nm
  | _ =>
    if e.isAppOfArity ``LeanQbe.T.Ty.bits 1 then Ty.bits <$> decodeNat (e.getArg! 0)
    else if e.isAppOfArity ``LeanQbe.T.Ty.float 1 then Ty.float <$> decodeFmt (e.getArg! 0)
    else if e.isAppOfArity ``LeanQbe.T.Ty.pair 2 then
      Ty.pair <$> decodeTy (e.getArg! 0) <*> decodeTy (e.getArg! 1)
    else if e.isAppOfArity ``LeanQbe.T.Ty.vec 2 then
      Ty.vec <$> decodeNat (e.getArg! 0) <*> decodeTy (e.getArg! 1)
    else none

private def decodeList {α : Type} (elem : Lean.Expr → Option α) (e0 : Lean.Expr) :
    Option (List α) := Id.run do
  let mut cur := e0.consumeMData
  let mut acc : Array α := #[]
  while cur.isAppOfArity ``List.cons 3 do
    let some v := elem (cur.getArg! 1) | return none
    acc := acc.push v
    cur := (cur.getArg! 2).consumeMData
  if cur.isAppOfArity ``List.nil 1 then return some acc.toList else return none

private def cmpOpTable : List (Name × CmpOp) :=
  [ (``LeanQbe.T.CmpOp.eq, .eq), (``LeanQbe.T.CmpOp.ne, .ne)
  , (``LeanQbe.T.CmpOp.ult, .ult), (``LeanQbe.T.CmpOp.ule, .ule)
  , (``LeanQbe.T.CmpOp.ugt, .ugt), (``LeanQbe.T.CmpOp.uge, .uge)
  , (``LeanQbe.T.CmpOp.slt, .slt), (``LeanQbe.T.CmpOp.sle, .sle)
  , (``LeanQbe.T.CmpOp.sgt, .sgt), (``LeanQbe.T.CmpOp.sge, .sge) ]
private def fcmpOpTable : List (Name × FCmpOp) :=
  [ (``LeanQbe.T.FCmpOp.eq, .eq), (``LeanQbe.T.FCmpOp.ne, .ne)
  , (``LeanQbe.T.FCmpOp.lt, .lt), (``LeanQbe.T.FCmpOp.le, .le)
  , (``LeanQbe.T.FCmpOp.gt, .gt), (``LeanQbe.T.FCmpOp.ge, .ge)
  , (``LeanQbe.T.FCmpOp.ord, .ord), (``LeanQbe.T.FCmpOp.uno, .uno) ]
private def decodeConstFrom {α : Type} (tbl : List (Name × α)) (e : Lean.Expr) : Option α :=
  match e.consumeMData with | .const nm [] => tbl.lookup nm | _ => none
private partial def decodeVal (t : Ty) (e : Lean.Expr) : Option (Val t) :=
  match t with
  | .bool => decodeBool e
  | .bits n => decodeBitVec n e
  | .float f => decodeBitVec f.width e
  | .pair a b =>
    let e := e.consumeMData
    if e.isAppOfArity ``Prod.mk 4 then
      Prod.mk <$> decodeVal a (e.getArg! 2) <*> decodeVal b (e.getArg! 3)
    else none
private def decodeArgK (t : Ty) (e : Lean.Expr) : Option (Arg K t) :=
  let e := e.consumeMData
  if e.isAppOfArity ``LeanQbe.T.Arg.var 3 then Arg.var <$> decodeNat (e.getArg! 2)
  else if e.isAppOfArity ``LeanQbe.T.Arg.imm 3 then Arg.imm <$> decodeVal t (e.getArg! 2)
  else none
private def decodeTupArgK : (ts : List Ty) → Lean.Expr → Option (Tup (Arg K) ts)
  | [], e => if e.consumeMData.isConstOf ``Unit.unit then some () else none
  | t :: ts, e =>
    let e := e.consumeMData
    if e.isAppOfArity ``Prod.mk 4 then
      Prod.mk <$> decodeArgK t (e.getArg! 2) <*> decodeTupArgK ts (e.getArg! 3)
    else none

private abbrev AnyOpCode := (as : List Ty) × (rs : List Ty) × OpCode as rs

private def tyOpTable : List (Name × (Ty → AnyOpCode)) :=
  [ (``LeanQbe.T.OpCode.copy, fun t => ⟨[t], [t], .copy t⟩)
  , (``LeanQbe.T.OpCode.add, fun t => ⟨[t, t], [t], .add t⟩)
  , (``LeanQbe.T.OpCode.sub, fun t => ⟨[t, t], [t], .sub t⟩)
  , (``LeanQbe.T.OpCode.mul, fun t => ⟨[t, t], [t], .mul t⟩)
  , (``LeanQbe.T.OpCode.neg, fun t => ⟨[t], [t], .neg t⟩)
  , (``LeanQbe.T.OpCode.and, fun t => ⟨[t, t], [t], .and t⟩)
  , (``LeanQbe.T.OpCode.or, fun t => ⟨[t, t], [t], .or t⟩)
  , (``LeanQbe.T.OpCode.xor, fun t => ⟨[t, t], [t], .xor t⟩)
  , (``LeanQbe.T.OpCode.not, fun t => ⟨[t], [t], .not t⟩)
  , (``LeanQbe.T.OpCode.shl, fun t => ⟨[t, t], [t], .shl t⟩)
  , (``LeanQbe.T.OpCode.lshr, fun t => ⟨[t, t], [t], .lshr t⟩)
  , (``LeanQbe.T.OpCode.ashr, fun t => ⟨[t, t], [t], .ashr t⟩)
  , (``LeanQbe.T.OpCode.rotl, fun t => ⟨[t, t], [t], .rotl t⟩)
  , (``LeanQbe.T.OpCode.rotr, fun t => ⟨[t, t], [t], .rotr t⟩)
  , (``LeanQbe.T.OpCode.bswap, fun t => ⟨[t], [t], .bswap t⟩)
  , (``LeanQbe.T.OpCode.select, fun t => ⟨[.bool, t, t], [t], .select t⟩)
  , (``LeanQbe.T.OpCode.shufb, fun t => ⟨[t, t], [t], .shufb t⟩)
  , (``LeanQbe.T.OpCode.fadd, fun t => ⟨[t, t], [t], .fadd t⟩)
  , (``LeanQbe.T.OpCode.fsub, fun t => ⟨[t, t], [t], .fsub t⟩)
  , (``LeanQbe.T.OpCode.fmul, fun t => ⟨[t, t], [t], .fmul t⟩)
  , (``LeanQbe.T.OpCode.fdiv, fun t => ⟨[t, t], [t], .fdiv t⟩)
  , (``LeanQbe.T.OpCode.ffma, fun t => ⟨[t, t, t], [t], .ffma t⟩)
  , (``LeanQbe.T.OpCode.fsqrt, fun t => ⟨[t], [t], .fsqrt t⟩)
  , (``LeanQbe.T.OpCode.fneg, fun t => ⟨[t], [t], .fneg t⟩)
  , (``LeanQbe.T.OpCode.fabs, fun t => ⟨[t], [t], .fabs t⟩) ]

private def natOpTable : List (Name × (Nat → AnyOpCode)) :=
  [ (``LeanQbe.T.OpCode.fshl, fun n => ⟨[.bits n, .bits n, .bits n], [.bits n], .fshl n⟩)
  , (``LeanQbe.T.OpCode.fshr, fun n => ⟨[.bits n, .bits n, .bits n], [.bits n], .fshr n⟩)
  , (``LeanQbe.T.OpCode.clz, fun n => ⟨[.bits n], [.bits n], .clz n⟩)
  , (``LeanQbe.T.OpCode.cls, fun n => ⟨[.bits n], [.bits n], .cls n⟩)
  , (``LeanQbe.T.OpCode.rbit, fun n => ⟨[.bits n], [.bits n], .rbit n⟩)
  , (``LeanQbe.T.OpCode.ctz, fun n => ⟨[.bits n], [.bits n], .ctz n⟩)
  , (``LeanQbe.T.OpCode.popcnt, fun n => ⟨[.bits n], [.bits n], .popcnt n⟩)
  , (``LeanQbe.T.OpCode.ofBool, fun n => ⟨[.bool], [.bits n], .ofBool n⟩)
  , (``LeanQbe.T.OpCode.addc, fun n => ⟨[.bits n, .bits n, .bool], [.bits n, .bool], .addc n⟩)
  , (``LeanQbe.T.OpCode.subb, fun n => ⟨[.bits n, .bits n, .bool], [.bits n, .bool], .subb n⟩)
  , (``LeanQbe.T.OpCode.umulw, fun n => ⟨[.bits n, .bits n], [.bits n, .bits n], .umulw n⟩)
  , (``LeanQbe.T.OpCode.smulw, fun n => ⟨[.bits n, .bits n], [.bits n, .bits n], .smulw n⟩)
  , (``LeanQbe.T.OpCode.udiv, fun n => ⟨[.bits n, .bits n], [.bits n], .udiv n⟩)
  , (``LeanQbe.T.OpCode.sdiv, fun n => ⟨[.bits n, .bits n], [.bits n], .sdiv n⟩)
  , (``LeanQbe.T.OpCode.urem, fun n => ⟨[.bits n, .bits n], [.bits n], .urem n⟩)
  , (``LeanQbe.T.OpCode.srem, fun n => ⟨[.bits n, .bits n], [.bits n], .srem n⟩)
  , (``LeanQbe.T.OpCode.udiv0, fun n => ⟨[.bits n, .bits n], [.bits n], .udiv0 n⟩)
  , (``LeanQbe.T.OpCode.sdiv0, fun n => ⟨[.bits n, .bits n], [.bits n], .sdiv0 n⟩) ]

private def decodeOpCode2 (nm : Name) (a0 a1 : Lean.Expr) : Option AnyOpCode :=
  match nm with
  | ``LeanQbe.T.OpCode.zext => do
    let m ← decodeNat a0; let n ← decodeNat a1; return ⟨[.bits m], [.bits n], .zext m n⟩
  | ``LeanQbe.T.OpCode.sext => do
    let m ← decodeNat a0; let n ← decodeNat a1; return ⟨[.bits m], [.bits n], .sext m n⟩
  | ``LeanQbe.T.OpCode.trunc => do
    let m ← decodeNat a0; let n ← decodeNat a1; return ⟨[.bits m], [.bits n], .trunc m n⟩
  | ``LeanQbe.T.OpCode.mkpair => do
    let a ← decodeTy a0; let b ← decodeTy a1; return ⟨[a, b], [.pair a b], .mkpair a b⟩
  | ``LeanQbe.T.OpCode.unpair => do
    let a ← decodeTy a0; let b ← decodeTy a1; return ⟨[.pair a b], [a, b], .unpair a b⟩
  | ``LeanQbe.T.OpCode.fptoui => do
    let f ← decodeFmt a0; let n ← decodeNat a1; return ⟨[.float f], [.bits n], .fptoui f n⟩
  | ``LeanQbe.T.OpCode.fptosi => do
    let f ← decodeFmt a0; let n ← decodeNat a1; return ⟨[.float f], [.bits n], .fptosi f n⟩
  | ``LeanQbe.T.OpCode.uitofp => do
    let n ← decodeNat a0; let f ← decodeFmt a1; return ⟨[.bits n], [.float f], .uitofp n f⟩
  | ``LeanQbe.T.OpCode.sitofp => do
    let n ← decodeNat a0; let f ← decodeFmt a1; return ⟨[.bits n], [.float f], .sitofp n f⟩
  | ``LeanQbe.T.OpCode.fcvt => do
    let f ← decodeFmt a0; let g ← decodeFmt a1; return ⟨[.float f], [.float g], .fcvt f g⟩
  | ``LeanQbe.T.OpCode.ternlog => do
    let t ← decodeTy a0; let i ← decodeBitVec 8 a1; return ⟨[t, t, t], [t], .ternlog t i⟩
  | ``LeanQbe.T.OpCode.shufd => do
    let t ← decodeTy a0; let i ← decodeBitVec 8 a1; return ⟨[t], [t], .shufd t i⟩
  | ``LeanQbe.T.OpCode.alignr => do
    let t ← decodeTy a0; let i ← decodeBitVec 8 a1; return ⟨[t, t], [t], .alignr t i⟩
  | ``LeanQbe.T.OpCode.blendw => do
    let t ← decodeTy a0; let i ← decodeBitVec 8 a1; return ⟨[t, t], [t], .blendw t i⟩
  | _ => none

private def decodeOpCode (e : Lean.Expr) : Option AnyOpCode :=
  let e := e.consumeMData
  let args := e.getAppArgs
  match e.getAppFn.consumeMData, args.size with
  | .const ``LeanQbe.T.OpCode.sha256rnds2 [], 0 =>
    some ⟨[v4i32, v4i32, v4i32], [v4i32], .sha256rnds2⟩
  | .const ``LeanQbe.T.OpCode.sha256msg1 [], 0 => some ⟨[v4i32, v4i32], [v4i32], .sha256msg1⟩
  | .const ``LeanQbe.T.OpCode.sha256msg2 [], 0 => some ⟨[v4i32, v4i32], [v4i32], .sha256msg2⟩
  | .const nm [], 1 =>
    (decodeTy args[0]! >>= fun t => (tyOpTable.lookup nm).map (· t)) <|>
    (decodeNat args[0]! >>= fun n => (natOpTable.lookup nm).map (· n))
  | .const nm [], 2 => decodeOpCode2 nm args[0]! args[1]!
  | .const ``LeanQbe.T.OpCode.blend [], 3 => do
    let t ← decodeTy args[0]!; let m ← decodeTy args[1]!
    if h : m = t.mask then some ⟨[m, t, t], [t], .blend t m h⟩ else none
  | .const ``LeanQbe.T.OpCode.bitcast [], 3 => do
    let t ← decodeTy args[0]!; let u ← decodeTy args[1]!
    if h : t.size = u.size then some ⟨[t], [u], .bitcast t u h⟩ else none
  | .const ``LeanQbe.T.OpCode.cmp [], 4 => do
    let o ← decodeConstFrom cmpOpTable args[0]!
    let t ← decodeTy args[1]!; let m ← decodeTy args[2]!
    if h : m = t.mask then some ⟨[t, t], [m], .cmp o t m h⟩ else none
  | .const ``LeanQbe.T.OpCode.fcmp [], 4 => do
    let o ← decodeConstFrom fcmpOpTable args[0]!
    let t ← decodeTy args[1]!; let m ← decodeTy args[2]!
    if h : m = t.mask then some ⟨[t, t], [m], .fcmp o t m h⟩ else none
  | _, _ => none

private def decodeOpK (rs : List Ty) (e : Lean.Expr) : Option (Op K rs) := do
  let e := e.consumeMData
  if !e.isAppOfArity ``LeanQbe.T.Op.mk 5 then none
  let ⟨as, rs', code⟩ ← decodeOpCode (e.getArg! 3)
  if h : rs' = rs then
    let args ← decodeTupArgK as (e.getArg! 4)
    let code' : OpCode as rs := h ▸ code
    some ⟨code', args⟩
  else none

mutual
partial def decodeTFlat (rs : List Ty) (e : Lean.Expr) : Option (TFlat rs) := do
  let e := e.consumeMData
  if e.isAppOfArity ``LeanQbe.T.TFlat.let_ 4 then
    let ts ← decodeList decodeTy (e.getArg! 1)
    return .let_ (← decodeOpK ts (e.getArg! 2)) (← decodeTFlat rs (e.getArg! 3))
  else if e.isAppOfArity ``LeanQbe.T.TFlat.load 4 then
    return .load (← decodeTy (e.getArg! 1)) (← decodeArgK i64 (e.getArg! 2))
      (← decodeTFlat rs (e.getArg! 3))
  else if e.isAppOfArity ``LeanQbe.T.TFlat.store 5 then
    let t ← decodeTy (e.getArg! 1)
    return .store (← decodeArgK t (e.getArg! 2)) (← decodeArgK i64 (e.getArg! 3))
      (← decodeTFlat rs (e.getArg! 4))
  else if e.isAppOfArity ``LeanQbe.T.TFlat.call 6 then
    let as ← decodeList decodeTy (e.getArg! 2)
    return .call (← decodeString (e.getArg! 1)) (← decodeList decodeTy (e.getArg! 3))
      (← decodeTupArgK as (e.getArg! 4)) (← decodeTFlat rs (e.getArg! 5))
  else if e.isAppOfArity ``LeanQbe.T.TFlat.jnz 4 then
    return .jnz (← decodeArgK .bool (e.getArg! 1)) (← decodeTFlat rs (e.getArg! 2))
      (← decodeTFlat rs (e.getArg! 3))
  else if e.isAppOfArity ``LeanQbe.T.TFlat.jump 4 then
    let ts ← decodeList decodeTy (e.getArg! 1)
    return .jump (← decodeNat (e.getArg! 2)) (← decodeTupArgK ts (e.getArg! 3))
  else if e.isAppOfArity ``LeanQbe.T.TFlat.ret 2 then
    return .ret (← decodeTupArgK rs (e.getArg! 1))
  else if e.isAppOfArity ``LeanQbe.T.TFlat.exit 4 then
    let as ← decodeList decodeTy (e.getArg! 2)
    return .exit (← decodeString (e.getArg! 1)) (← decodeTupArgK as (e.getArg! 3))
  else if e.isAppOfArity ``LeanQbe.T.TFlat.hlt 1 then return .hlt
  else if e.isAppOfArity ``LeanQbe.T.TFlat.group 4 then
    let sig ← decodeList (decodeList decodeTy) (e.getArg! 1)
    return .group (← decodeTBlocks rs sig (e.getArg! 2)) (← decodeTFlat rs (e.getArg! 3))
  else none

partial def decodeTBlocks (rs : List Ty) :
    (sig : List (List Ty)) → Lean.Expr → Option (TBlocks rs sig)
  | [], e => if e.consumeMData.isAppOfArity ``LeanQbe.T.TBlocks.nil 1 then some .nil else none
  | ts :: sig', e => do
    let e := e.consumeMData
    if !e.isAppOfArity ``LeanQbe.T.TBlocks.cons 5 then none
    if (← decodeList decodeTy (e.getArg! 1)) != ts then none
    return .cons (← decodeTFlat rs (e.getArg! 3)) (← decodeTBlocks rs sig' (e.getArg! 4))
end

private def decodeTFlatFnFields (nmE asE rsE bodyE : Lean.Expr) : Option TFlatFn := do
  let name ← decodeString nmE
  let as ← decodeList decodeTy asE
  let rs ← decodeList decodeTy rsE
  return { name, as, rs, body := ← decodeTFlat rs bodyE }

private def findConstVal? (nm : Name) : OptionT MetaM Lean.Expr := do
  let some ci := (← getEnv).find? nm | failure
  let some v := ci.value? | failure
  return v

private partial def resolveModuleFns (modE : Lean.Expr) : OptionT MetaM Lean.Expr := do
  let m := modE.consumeMData
  if m.isAppOfArity ``LeanQbe.T.Module.mk 3 then return m.getArg! 0
  else if let .const nm [] := m then resolveModuleFns (← findConstVal? nm)
  else failure

private partial def resolveListExpr (fnWrap? : Bool) (e0 : Lean.Expr) :
    OptionT MetaM (Array Lean.Expr) := do
  let mut cur := e0.consumeMData
  let mut acc : Array Lean.Expr := #[]
  while cur.isAppOfArity ``List.cons 3 do
    let hd := cur.getArg! 1
    acc := acc.push (if fnWrap? then mkApp (Lean.mkConst ``LeanQbe.T.TFlatFn.toFn) hd else hd)
    cur := (cur.getArg! 2).consumeMData
  if cur.isAppOfArity ``List.nil 1 then return acc
  let tail ←
    if let .const nm [] := cur then resolveListExpr fnWrap? (← findConstVal? nm)
    else if cur.isAppOfArity ``LeanQbe.T.Module.fns 1 then
      if fnWrap? then failure else resolveListExpr false (← resolveModuleFns (cur.getArg! 0))
    else if let .proj ``LeanQbe.T.Module 0 modE := cur then
      if fnWrap? then failure else resolveListExpr false (← resolveModuleFns modE)
    else if cur.isAppOfArity ``List.append 3 then
      pure ((← resolveListExpr fnWrap? (cur.getArg! 1)) ++
        (← resolveListExpr fnWrap? (cur.getArg! 2)))
    else if cur.isAppOfArity ``HAppend.hAppend 6 then
      pure ((← resolveListExpr fnWrap? (cur.getArg! 4)) ++
        (← resolveListExpr fnWrap? (cur.getArg! 5)))
    else if cur.isAppOfArity ``List.drop 3 then
      let k ← decodeNatM (cur.getArg! 1)
      let xs ← resolveListExpr fnWrap? (cur.getArg! 2)
      pure (xs.extract k xs.size)
    else if cur.isAppOfArity ``List.take 3 then
      let k ← decodeNatM (cur.getArg! 1)
      let xs ← resolveListExpr fnWrap? (cur.getArg! 2)
      pure (xs.extract 0 (min k xs.size))
    else if !fnWrap? && cur.isAppOfArity ``List.map 4 &&
        (cur.getArg! 2).consumeMData.isConstOf ``LeanQbe.T.TFlatFn.toFn then
      resolveListExpr true (cur.getArg! 3)
    else failure
  return acc ++ tail

private def decodeFlatValue (flatE : Lean.Expr) : OptionT MetaM TFlatFn := do
  let e := flatE.consumeMData
  let e ← if let .const nm [] := e then pure (← findConstVal? nm).consumeMData else pure e
  if !e.isAppOfArity ``LeanQbe.T.TFlatFn.mk 4 then failure
  let some tf := decodeTFlatFnFields (e.getArg! 0) (e.getArg! 1) (e.getArg! 2) (e.getArg! 3)
    | failure
  return tf

private def decodeFlatElem (fnE : Lean.Expr) : OptionT MetaM (TFlatFn × Lean.Expr) := do
  let e := fnE.consumeMData
  let e ← if let .const nm [] := e then pure (← findConstVal? nm).consumeMData else pure e
  if e.isAppOfArity ``LeanQbe.T.TFlatFn.toFn 1 then
    let flatArg := (e.getArg! 0).consumeMData
    let tf ← decodeFlatValue flatArg
    let flatExpr := match flatArg with | .const flatNm [] => Lean.mkConst flatNm | _ => flatArg
    return (tf, flatExpr)
  else if e.isAppOfArity ``LeanQbe.T.Fn.mk 4 then
    let nmE := e.getArg! 0; let asE := e.getArg! 1; let rsE := e.getArg! 2
    let bodyE := (e.getArg! 3).consumeMData
    if !bodyE.isAppOfArity ``LeanQbe.T.denoteFunc 3 then failure
    let tfE := (bodyE.getArg! 2).consumeMData
    let some tf := decodeTFlatFnFields nmE asE rsE tfE | failure
    return (tf, mkApp4 (Lean.mkConst ``LeanQbe.T.TFlatFn.mk) nmE asE rsE tfE)
  else failure

/-- Decode a `List Fn` expression `fnsE` from exposed `.olean` definitions into
`(flatFns, flatListExpr, fnsFlatEqProof)` with `fnsE = flatListExpr.map TFlatFn.toFn`,
returning `none` when any element is not materialized as `TFlatFn` or `denoteFunc`. -/
def decodeFlatSliceExpr (fnsE : Lean.Expr) :
    MetaM (Option (List TFlatFn × Lean.Expr × Lean.Expr)) :=
  OptionT.run do
    let elems ← resolveListExpr false fnsE
    let decoded ← elems.mapM decodeFlatElem
    let flatTy := Lean.mkConst ``LeanQbe.T.TFlatFn
    let fnTy := Lean.mkConst ``LeanQbe.T.Fn
    let listFnTy := mkApp (Lean.mkConst ``List [.one]) fnTy
    let flatListExpr := decoded.foldr
      (fun (_, fe) acc => mkApp3 (Lean.mkConst ``List.cons [.zero]) flatTy fe acc)
      (mkApp (Lean.mkConst ``List.nil [.zero]) flatTy)
    let rhsE := mkApp4 (Lean.mkConst ``List.map [.zero, .one])
      flatTy fnTy (Lean.mkConst ``LeanQbe.T.TFlatFn.toFn) flatListExpr
    let l2 := Level.succ (.succ .zero)
    let eqTy := mkApp3 (Lean.mkConst ``Eq [l2]) listFnTy fnsE rhsE
    let reflPf := mkApp2 (Lean.mkConst ``Eq.refl [l2]) listFnTy rhsE
    let pf := mkApp2 (Lean.mkConst ``id [.zero]) eqTy reflPf
    return ((decoded.map Prod.fst).toList, flatListExpr, pf)

end

end LeanQbe.T
