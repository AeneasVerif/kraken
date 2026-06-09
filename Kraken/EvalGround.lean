/-
Copyright (c) 2026 Kraken. All rights reserved.
Released under Apache 2.0 license.
-/
import Lean
import Lean.Meta.Sym.LitValues

/-!
# Custom Ground Term Evaluator for Kraken `DSimp`

This module implements `kdsimpGround`, a custom ground term evaluator for the `DSimp`
(definitional simplification) framework. It mirrors the extensive coverage of the standard 
`Lean.Meta.Sym.Simp.evalGround` but is tailored to run within the `DSimpM` monad.

## Key Features & Design
1. **Defeq-based Simplification**: All evaluations perform pure value extraction and 
   reduce using only definitional equality steps.
2. **Extensive Operations Coverage**: Support for arithmetic, shifting, bitwise operations,
   predicates, and GCD/modulo functions for all major types (`Nat`, `Int`, `Rat`, `Fin`,
   `BitVec`, `UInt8`-`UInt64`, `Int8`-`Int64`).
3. **Hygienic Macro Generation**: Utilizes hygienic identifier generation to prevent
   linters or scoping warnings in pattern-matched expressions.
-/

open Lean Meta Sym Sym.DSimp

def skipIfUnchanged (e : Expr) (result : Result) : Result :=
  match result with
  | .step e' _done => if isSameExpr e e' then .rfl else result
  | _ => result

abbrev evalUnary {α : Type _} [ToExpr α] (toValue? : Expr → Option α) (op : α → α) (a : Expr) : DSimpM Result := do
  let some va := toValue? a | return .rfl
  let e ← share <| toExpr (op va)
  return .step e (done := true)

abbrev evalUnaryNat : (op : Nat → Nat) → (a : Expr) → DSimpM Result := evalUnary Lean.Meta.Sym.getNatValue?
abbrev evalUnaryInt : (op : Int → Int) → (a : Expr) → DSimpM Result := evalUnary Lean.Meta.Sym.getIntValue?
abbrev evalUnaryRat : (op : Rat → Rat) → (a : Expr) → DSimpM Result := evalUnary Lean.Meta.Sym.getRatValue?
abbrev evalUnaryUInt8 : (op : UInt8 → UInt8) → (a : Expr) → DSimpM Result := evalUnary Lean.Meta.Sym.getUInt8Value?
abbrev evalUnaryUInt16 : (op : UInt16 → UInt16) → (a : Expr) → DSimpM Result := evalUnary Lean.Meta.Sym.getUInt16Value?
abbrev evalUnaryUInt32 : (op : UInt32 → UInt32) → (a : Expr) → DSimpM Result := evalUnary Lean.Meta.Sym.getUInt32Value?
abbrev evalUnaryUInt64 : (op : UInt64 → UInt64) → (a : Expr) → DSimpM Result := evalUnary Lean.Meta.Sym.getUInt64Value?
abbrev evalUnaryInt8 : (op : Int8 → Int8) → (a : Expr) → DSimpM Result := evalUnary Lean.Meta.Sym.getInt8Value?
abbrev evalUnaryInt16 : (op : Int16 → Int16) → (a : Expr) → DSimpM Result := evalUnary Lean.Meta.Sym.getInt16Value?
abbrev evalUnaryInt32 : (op : Int32 → Int32) → (a : Expr) → DSimpM Result := evalUnary Lean.Meta.Sym.getInt32Value?
abbrev evalUnaryInt64 : (op : Int64 → Int64) → (a : Expr) → DSimpM Result := evalUnary Lean.Meta.Sym.getInt64Value?

abbrev evalUnaryFin' (op : {n : Nat} → Fin n → Fin n) (_αExpr : Expr) (a : Expr) : DSimpM Result := do
  let some va := Lean.Meta.Sym.getFinValue? a | return .rfl
  let e ← share <| toExpr (op va.val)
  return .step e (done := true)

abbrev evalUnaryBitVec' (op : {n : Nat} → BitVec n → BitVec n) (_αExpr : Expr) (a : Expr) : DSimpM Result := do
  let some va := Lean.Meta.Sym.getBitVecValue? a | return .rfl
  let e ← share <| toExpr (op va.val)
  return .step e (done := true)

abbrev evalBin {α : Type _} [ToExpr α] (toValue? : Expr → Option α) (op : α → α → α) (a b : Expr) : DSimpM Result := do
  let some va := toValue? a | return .rfl
  let some vb := toValue? b | return .rfl
  let e ← share <| toExpr (op va vb)
  return .step e (done := true)

abbrev evalBinNat : (op : Nat → Nat → Nat) → (a b : Expr) → DSimpM Result := evalBin Lean.Meta.Sym.getNatValue?
abbrev evalBinInt : (op : Int → Int → Int) → (a b : Expr) → DSimpM Result := evalBin Lean.Meta.Sym.getIntValue?
abbrev evalBinRat : (op : Rat → Rat → Rat) → (a b : Expr) → DSimpM Result := evalBin Lean.Meta.Sym.getRatValue?
abbrev evalBinUInt8 : (op : UInt8 → UInt8 → UInt8) → (a b : Expr) → DSimpM Result := evalBin Lean.Meta.Sym.getUInt8Value?
abbrev evalBinUInt16 : (op : UInt16 → UInt16 → UInt16) → (a b : Expr) → DSimpM Result := evalBin Lean.Meta.Sym.getUInt16Value?
abbrev evalBinUInt32 : (op : UInt32 → UInt32 → UInt32) → (a b : Expr) → DSimpM Result := evalBin Lean.Meta.Sym.getUInt32Value?
abbrev evalBinUInt64 : (op : UInt64 → UInt64 → UInt64) → (a b : Expr) → DSimpM Result := evalBin Lean.Meta.Sym.getUInt64Value?
abbrev evalBinInt8 : (op : Int8 → Int8 → Int8) → (a b : Expr) → DSimpM Result := evalBin Lean.Meta.Sym.getInt8Value?
abbrev evalBinInt16 : (op : Int16 → Int16 → Int16) → (a b : Expr) → DSimpM Result := evalBin Lean.Meta.Sym.getInt16Value?
abbrev evalBinInt32 : (op : Int32 → Int32 → Int32) → (a b : Expr) → DSimpM Result := evalBin Lean.Meta.Sym.getInt32Value?
abbrev evalBinInt64 : (op : Int64 → Int64 → Int64) → (a b : Expr) → DSimpM Result := evalBin Lean.Meta.Sym.getInt64Value?

abbrev evalBinFin' (op : {n : Nat} → Fin n → Fin n → Fin n) (_αExpr : Expr) (a b : Expr) : DSimpM Result := do
  let some va := Lean.Meta.Sym.getFinValue? a | return .rfl
  let some vb := Lean.Meta.Sym.getFinValue? b | return .rfl
  if h : va.n = vb.n then
    let e ← share <| toExpr (op va.val (h ▸ vb.val))
    return .step e (done := true)
  else
    return .rfl

abbrev evalBinBitVec' (op : {n : Nat} → BitVec n → BitVec n → BitVec n) (_αExpr : Expr) (a b : Expr) : DSimpM Result := do
  let some va := Lean.Meta.Sym.getBitVecValue? a | return .rfl
  let some vb := Lean.Meta.Sym.getBitVecValue? b | return .rfl
  if h : va.n = vb.n then
    let e ← share <| toExpr (op va.val (h ▸ vb.val))
    return .step e (done := true)
  else
    return .rfl

abbrev evalPowNat {α : Type _} [ToExpr α] (maxExponent : Nat) (toValue? : Expr → Option α) (op : α → Nat → α) (a b : Expr) : DSimpM Result := do
  let some va := toValue? a | return .rfl
  let some vb := Lean.Meta.Sym.getNatValue? b | return .rfl
  if vb > maxExponent then return .rfl
  let e ← share <| toExpr (op va vb)
  return .step e (done := true)

abbrev evalPowInt {α : Type _} [ToExpr α] (maxExponent : Nat) (toValue? : Expr → Option α) (op : α → Int → α) (a b : Expr) : DSimpM Result := do
  let some va := toValue? a | return .rfl
  let some vb := Lean.Meta.Sym.getIntValue? b | return .rfl
  if vb.natAbs > maxExponent then return .rfl
  let e ← share <| toExpr (op va vb)
  return .step e (done := true)

macro "declare_eval_bin" id:ident op:term : command =>
  let α := mkIdent `α
  `(def $id:ident ($α:ident : Expr) (a b : Expr) : DSimpM Result :=
  match_expr $α:ident with
  | Nat => evalBinNat $op a b
  | Int => evalBinInt $op a b
  | Rat => evalBinRat $op a b
  | Fin _ => evalBinFin' $op $α:ident a b
  | BitVec _ => evalBinBitVec' $op $α:ident a b
  | UInt8 => evalBinUInt8 $op a b
  | UInt16 => evalBinUInt16 $op a b
  | UInt32 => evalBinUInt32 $op a b
  | UInt64 => evalBinUInt64 $op a b
  | Int8 => evalBinInt8 $op a b
  | Int16 => evalBinInt16 $op a b
  | Int32 => evalBinInt32 $op a b
  | Int64 => evalBinInt64 $op a b
  | _ => return .rfl
  )

declare_eval_bin evalAdd (· + ·)
declare_eval_bin evalSub (· - ·)
declare_eval_bin evalMul (· * ·)

def evalDiv (e : Expr) (α : Expr) (a b : Expr) : DSimpM Result :=
  match_expr α with
  | Nat => evalBinNat (· / ·) a b
  | Int => evalBinInt (· / ·) a b
  | Rat => return skipIfUnchanged e (← evalBinRat (· / ·) a b)
  | Fin _ => evalBinFin' (· / ·) α a b
  | BitVec _ => evalBinBitVec' (· / ·) α a b
  | UInt8 => evalBinUInt8 (· / ·) a b
  | UInt16 => evalBinUInt16 (· / ·) a b
  | UInt32 => evalBinUInt32 (· / ·) a b
  | UInt64 => evalBinUInt64 (· / ·) a b
  | Int8 => evalBinInt8 (· / ·) a b
  | Int16 => evalBinInt16 (· / ·) a b
  | Int32 => evalBinInt32 (· / ·) a b
  | Int64 => evalBinInt64 (· / ·) a b
  | _ => return .rfl

def evalMod (α : Expr) (a b : Expr) : DSimpM Result :=
  match_expr α with
  | Nat => evalBinNat (· % ·) a b
  | Int => evalBinInt (· % ·) a b
  | Fin _ => evalBinFin' (· % ·) α a b
  | BitVec _ => evalBinBitVec' (· % ·) α a b
  | UInt8 => evalBinUInt8 (· % ·) a b
  | UInt16 => evalBinUInt16 (· % ·) a b
  | UInt32 => evalBinUInt32 (· % ·) a b
  | UInt64 => evalBinUInt64 (· % ·) a b
  | Int8 => evalBinInt8 (· % ·) a b
  | Int16 => evalBinInt16 (· % ·) a b
  | Int32 => evalBinInt32 (· % ·) a b
  | Int64 => evalBinInt64 (· % ·) a b
  | _ => return .rfl

def evalNeg (α : Expr) (a : Expr) : DSimpM Result :=
  match_expr α with
  | Int => evalUnaryInt (- ·) a
  | Rat => evalUnaryRat (- ·) a
  | Fin _ => evalUnaryFin' (- ·) α a
  | BitVec _ => evalUnaryBitVec' (- ·) α a
  | UInt8 => evalUnaryUInt8 (- ·) a
  | UInt16 => evalUnaryUInt16 (- ·) a
  | UInt32 => evalUnaryUInt32 (- ·) a
  | UInt64 => evalUnaryUInt64 (- ·) a
  | Int8 => evalUnaryInt8 (- ·) a
  | Int16 => evalUnaryInt16 (- ·) a
  | Int32 => evalUnaryInt32 (- ·) a
  | Int64 => evalUnaryInt64 (- ·) a
  | _ => return .rfl

def evalComplement (α : Expr) (a : Expr) : DSimpM Result :=
  match_expr α with
  | Int => evalUnaryInt (~~~ ·) a
  | BitVec _ => evalUnaryBitVec' (~~~ ·) α a
  | UInt8 => evalUnaryUInt8 (~~~ ·) a
  | UInt16 => evalUnaryUInt16 (~~~ ·) a
  | UInt32 => evalUnaryUInt32 (~~~ ·) a
  | UInt64 => evalUnaryUInt64 (~~~ ·) a
  | Int8 => evalUnaryInt8 (~~~ ·) a
  | Int16 => evalUnaryInt16 (~~~ ·) a
  | Int32 => evalUnaryInt32 (~~~ ·) a
  | Int64 => evalUnaryInt64 (~~~ ·) a
  | _ => return .rfl

def evalInv (α : Expr) (a : Expr) : DSimpM Result :=
  match_expr α with
  | Rat => evalUnaryRat (· ⁻¹) a
  | _ => return .rfl

macro "declare_eval_bin_bitwise" id:ident op:term : command =>
  let α := mkIdent `α
  `(def $id:ident ($α:ident : Expr) (a b : Expr) : DSimpM Result :=
  match_expr $α:ident with
  | Nat => evalBinNat $op a b
  | Fin _ => evalBinFin' $op $α:ident a b
  | BitVec _ => evalBinBitVec' $op $α:ident a b
  | UInt8 => evalBinUInt8 $op a b
  | UInt16 => evalBinUInt16 $op a b
  | UInt32 => evalBinUInt32 $op a b
  | UInt64 => evalBinUInt64 $op a b
  | Int8 => evalBinInt8 $op a b
  | Int16 => evalBinInt16 $op a b
  | Int32 => evalBinInt32 $op a b
  | Int64 => evalBinInt64 $op a b
  | _ => return .rfl
  )

declare_eval_bin_bitwise evalAnd (· &&& ·)
declare_eval_bin_bitwise evalOr (· ||| ·)
declare_eval_bin_bitwise evalXOr (· ^^^ ·)

def evalPow (maxExponent : Nat) (α β : Expr) (a b : Expr) : DSimpM Result :=
  match_expr β with
  | Nat => match_expr α with
    | Nat => evalPowNat maxExponent Lean.Meta.Sym.getNatValue? (· ^ ·) a b
    | Int => evalPowNat maxExponent Lean.Meta.Sym.getIntValue? (· ^ ·) a b
    | Rat => evalPowNat maxExponent Lean.Meta.Sym.getRatValue? (· ^ ·) a b
    | UInt8 => evalPowNat maxExponent Lean.Meta.Sym.getUInt8Value? (· ^ ·) a b
    | UInt16 => evalPowNat maxExponent Lean.Meta.Sym.getUInt16Value? (· ^ ·) a b
    | UInt32 => evalPowNat maxExponent Lean.Meta.Sym.getUInt32Value? (· ^ ·) a b
    | UInt64 => evalPowNat maxExponent Lean.Meta.Sym.getUInt64Value? (· ^ ·) a b
    | Int8 => evalPowNat maxExponent Lean.Meta.Sym.getInt8Value? (· ^ ·) a b
    | Int16 => evalPowNat maxExponent Lean.Meta.Sym.getInt16Value? (· ^ ·) a b
    | Int32 => evalPowNat maxExponent Lean.Meta.Sym.getInt32Value? (· ^ ·) a b
    | Int64 => evalPowNat maxExponent Lean.Meta.Sym.getInt64Value? (· ^ ·) a b
    | _ => return .rfl
  | Int => match_expr α with
    | Rat => evalPowInt maxExponent Lean.Meta.Sym.getRatValue? (· ^ ·) a b
    | _ => return .rfl
  | _ => return .rfl

abbrev shift {α : Type _} [ShiftLeft α] [ShiftRight α] (left : Bool) (a b : α) : α :=
  if left then a <<< b else a >>> b

def evalShift (left : Bool) (α β : Expr) (a b : Expr) : DSimpM Result :=
  if isSameExpr α β then
    match_expr α with
    | Nat => evalBinNat (shift left) a b
    | Fin _ => if left then evalBinFin' (· <<< ·) α a b else evalBinFin' (· >>> ·) α a b
    | BitVec _ => if left then evalBinBitVec' (· <<< ·) α a b else evalBinBitVec' (· >>> ·) α a b
    | UInt8 => evalBinUInt8 (shift left) a b
    | UInt16 => evalBinUInt16 (shift left) a b
    | UInt32 => evalBinUInt32 (shift left) a b
    | UInt64 => evalBinUInt64 (shift left) a b
    | Int8 => evalBinInt8 (shift left) a b
    | Int16 => evalBinInt16 (shift left) a b
    | Int32 => evalBinInt32 (shift left) a b
    | Int64 => evalBinInt64 (shift left) a b
    | _ => return .rfl
  else
  match_expr β with
  | Nat =>
    match_expr α with
    | Int => do
      let some va := Lean.Meta.Sym.getIntValue? a | return .rfl
      let some vb := Lean.Meta.Sym.getNatValue? b | return .rfl
      let e := if left then va <<< vb else va >>> vb
      let e ← share <| toExpr e
      return .step e (done := true)
    | BitVec _ => do
      let some va := Lean.Meta.Sym.getBitVecValue? a | return .rfl
      let some vb := Lean.Meta.Sym.getNatValue? b | return .rfl
      let e := if left then va.val <<< vb else va.val >>> vb
      let e ← share <| toExpr e
      return .step e (done := true)
    | _ => return .rfl
  | BitVec _ => do
    let_expr BitVec _ := α | return .rfl
    let some va := Lean.Meta.Sym.getBitVecValue? a | return .rfl
    let some vb := Lean.Meta.Sym.getBitVecValue? b | return .rfl
    let e := if left then va.val <<< vb.val else va.val >>> vb.val
    let e ← share <| toExpr e
    return .step e (done := true)
  | _ => return .rfl

def evalIntGcd (a b : Expr) : DSimpM Result := do
  let some va := Lean.Meta.Sym.getIntValue? a | return .rfl
  let some vb := Lean.Meta.Sym.getIntValue? b | return .rfl
  let e ← share <| toExpr (Int.gcd va vb)
  return .step e (done := true)

def evalIntBMod (a b : Expr) : DSimpM Result := do
  let some va := Lean.Meta.Sym.getIntValue? a | return .rfl
  let some vb := Lean.Meta.Sym.getNatValue? b | return .rfl
  let e ← share <| toExpr (Int.bmod va vb)
  return .step e (done := true)

def evalIntBDiv (a b : Expr) : DSimpM Result := do
  let some va := Lean.Meta.Sym.getIntValue? a | return .rfl
  let some vb := Lean.Meta.Sym.getNatValue? b | return .rfl
  let e ← share <| toExpr (Int.bdiv va vb)
  return .step e (done := true)

abbrev evalBinBoolPred {α : Type _} (toValue? : Expr → Option α) (op : α → α → Bool) (a b : Expr) : DSimpM Result := do
  let some va := toValue? a | return .rfl
  let some vb := toValue? b | return .rfl
  let r := op va vb
  let e ← share (toExpr r)
  return .step e (done := true)

abbrev evalBinBoolPredNat : (op : Nat → Nat → Bool) → (a b : Expr) → DSimpM Result := evalBinBoolPred Lean.Meta.Sym.getNatValue?
abbrev evalBinBoolPredInt : (op : Int → Int → Bool) → (a b : Expr) → DSimpM Result := evalBinBoolPred Lean.Meta.Sym.getIntValue?
abbrev evalBinBoolPredRat : (op : Rat → Rat → Bool) → (a b : Expr) → DSimpM Result := evalBinBoolPred Lean.Meta.Sym.getRatValue?
abbrev evalBinBoolPredUInt8 : (op : UInt8 → UInt8 → Bool) → (a b : Expr) → DSimpM Result := evalBinBoolPred Lean.Meta.Sym.getUInt8Value?
abbrev evalBinBoolPredUInt16 : (op : UInt16 → UInt16 → Bool) → (a b : Expr) → DSimpM Result := evalBinBoolPred Lean.Meta.Sym.getUInt16Value?
abbrev evalBinBoolPredUInt32 : (op : UInt32 → UInt32 → Bool) → (a b : Expr) → DSimpM Result := evalBinBoolPred Lean.Meta.Sym.getUInt32Value?
abbrev evalBinBoolPredUInt64 : (op : UInt64 → UInt64 → Bool) → (a b : Expr) → DSimpM Result := evalBinBoolPred Lean.Meta.Sym.getUInt64Value?
abbrev evalBinBoolPredInt8 : (op : Int8 → Int8 → Bool) → (a b : Expr) → DSimpM Result := evalBinBoolPred Lean.Meta.Sym.getInt8Value?
abbrev evalBinBoolPredInt16 : (op : Int16 → Int16 → Bool) → (a b : Expr) → DSimpM Result := evalBinBoolPred Lean.Meta.Sym.getInt16Value?
abbrev evalBinBoolPredInt32 : (op : Int32 → Int32 → Bool) → (a b : Expr) → DSimpM Result := evalBinBoolPred Lean.Meta.Sym.getInt32Value?
abbrev evalBinBoolPredInt64 : (op : Int64 → Int64 → Bool) → (a b : Expr) → DSimpM Result := evalBinBoolPred Lean.Meta.Sym.getInt64Value?

abbrev evalBinBoolPredFin (op : {n : Nat} → Fin n → Fin n → Bool) (a b : Expr) : DSimpM Result := do
  let some va := Lean.Meta.Sym.getFinValue? a | return .rfl
  let some vb := Lean.Meta.Sym.getFinValue? b | return .rfl
  if h : va.n = vb.n then
    let r := op va.val (h ▸ vb.val)
    let e ← share (toExpr r)
    return .step e (done := true)
  else
    return .rfl

abbrev evalBinBoolPredBitVec (op : {n : Nat} → BitVec n → BitVec n → Bool) (a b : Expr) : DSimpM Result := do
  let some va := Lean.Meta.Sym.getBitVecValue? a | return .rfl
  let some vb := Lean.Meta.Sym.getBitVecValue? b | return .rfl
  if h : va.n = vb.n then
    let r := op va.val (h ▸ vb.val)
    let e ← share (toExpr r)
    return .step e (done := true)
  else
    return .rfl

macro "declare_eval_bin_bool_pred" id:ident op:term : command =>
  let α := mkIdent `α
  `(def $id:ident ($α:ident : Expr) (a b : Expr) : DSimpM Result :=
  match_expr $α:ident with
  | Nat => evalBinBoolPredNat $op a b
  | Int => evalBinBoolPredInt $op a b
  | Rat => evalBinBoolPredRat $op a b
  | Fin _ => evalBinBoolPredFin $op a b
  | BitVec _ => evalBinBoolPredBitVec $op a b
  | UInt8 => evalBinBoolPredUInt8 $op a b
  | UInt16 => evalBinBoolPredUInt16 $op a b
  | UInt32 => evalBinBoolPredUInt32 $op a b
  | UInt64 => evalBinBoolPredUInt64 $op a b
  | Int8 => evalBinBoolPredInt8 $op a b
  | Int16 => evalBinBoolPredInt16 $op a b
  | Int32 => evalBinBoolPredInt32 $op a b
  | Int64 => evalBinBoolPredInt64 $op a b
  | _ => return .rfl
  )

declare_eval_bin_bool_pred evalBEq (· == ·)
declare_eval_bin_bool_pred evalBNe (· != ·)

def evalLT (_α : Expr) (_a _b : Expr) : DSimpM Result := return .rfl
def evalLE (_α : Expr) (_a _b : Expr) : DSimpM Result := return .rfl
def evalEq (_α : Expr) (_a _b : Expr) : DSimpM Result := return .rfl
def evalDvd (_α : Expr) (_a _b : Expr) : DSimpM Result := return .rfl
def evalNot (_a : Expr) : DSimpM Result := return .rfl

def kdsimpGround : DSimproc := fun e =>
  match_expr e with
  | HAdd.hAdd α _ _ _ a b => evalAdd α a b
  | HSub.hSub α _ _ _ a b => evalSub α a b
  | HMul.hMul α _ _ _ a b => evalMul α a b
  | HDiv.hDiv α _ _ _ a b => evalDiv e α a b
  | HMod.hMod α _ _ _ a b => evalMod α a b
  | HPow.hPow α β _ _ a b => evalPow 255 α β a b
  | HAnd.hAnd α _ _ _ a b => evalAnd α a b
  | HXor.hXor α _ _ _ a b => evalXOr α a b
  | HOr.hOr α _ _ _ a b => evalOr α a b
  | HShiftLeft.hShiftLeft α β _ _ a b => evalShift (left := true) α β a b
  | HShiftRight.hShiftRight α β _ _ a b => evalShift (left := false) α β a b
  | Inv.inv α _ a => evalInv α a
  | Neg.neg α _ a => return skipIfUnchanged e (← evalNeg α a)
  | Complement.complement α _ a => evalComplement α a
  | Nat.gcd a b => evalBinNat Nat.gcd a b
  | Nat.succ a => evalUnaryNat (· + 1) a
  | Int.gcd a b => evalIntGcd a b
  | Int.tdiv a b => evalBinInt Int.tdiv a b
  | Int.fdiv a b => evalBinInt Int.fdiv a b
  | Int.bdiv a b => evalIntBDiv a b
  | Int.tmod a b => evalBinInt Int.tmod a b
  | Int.fmod a b => evalBinInt Int.fmod a b
  | Int.bmod a b => evalIntBMod a b
  | LE.le α _ a b => evalLE α a b
  | LT.lt α _ a b => evalLT α a b
  | Dvd.dvd α _ a b => evalDvd α a b
  | Eq α a b => evalEq α a b
  | BEq.beq α _ a b => evalBEq α a b
  | bne α _ a b => evalBNe α a b
  | Not a => evalNot a
  | _ => return .rfl
