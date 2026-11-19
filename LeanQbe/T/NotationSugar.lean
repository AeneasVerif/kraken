module

public import LeanQbe.T.IL
public meta import LeanQbe.T.IL
public meta import Lean.Elab.Term
public meta import Lean.Elab.SyntheticMVars
public meta import Lean.Elab.Command
public meta import Lean.Elab.Tactic

/-!
# QBE-style typed notation for `LeanQbe.T`

`tqbe(%a:l, %b:l) { … }` is a function (`Func as rs` or `Tup V as → Expr V L rs`),
`tqbe { … }` is a code fragment (`Expr V L rs` or `Func [] rs`), and
`tqbe $name(%a:l, %b:l) -> l { … }` is a named function (`Fn`). All elaborate directly to
`LeanQbe.T.Expr` / `Func` / `Fn` via a direct de Bruijn term elaborator:

* Typed parameters: `@l(%x:w, %c:b)` (`w`=`i32`, `l`=`i64`, `b`=`bool`, `s`=`f32`, `d`=`f64`,
  `i8`/`i16`/`i32`/`i64`/`bits n`/`f16`/`f32`/`f64`/`f128`/`v4i32`/`v8i32`/`v2i64`/`v4f32`/
  `vec k t`/`pair a b`/`(a, b)`/any Lean `Ty` identifier such as `u128`).
* Multi-result and pair operations:
  `%s, %c =l addc %a, %b, %ci`, `%lo, %hi =l umulw %a, %b`, `%p =(l,l) mkpair %a, %b`,
  `%a0, %a1 = unpair %p`, `%x = fst %p`, `%y = snd %p`, `%_` wildcard binders.
* Structured control-flow sugar (macro/elaborator sugar only, no mutable locals; `G6`):
  - `loop @l(%x:t = init, …) { … }`, optionally with `-> @brk(%r:t)` or `%r:t <- loop …`,
  - `break` / `break(args)` / `break @k(args)` and `continue` / `continue(args)` / `continue @l(args)`,
  - `check %c else <target>`,
  - `switch %v { k => <target>, …, _ => <target> }` (omitting `_ =>` emits `.hlt` on fallthrough).
* Lane-wise vector immediates (`[a₀, a₁, …]`, `splat c`, `((a, b), (c, d))`, or scalar broadcast).
* Infer `group` block signatures directly from `@label(%x:t, …)` parameter annotations.
* **Performance design (`T2` `#29`):** emits projection lambdas `fun p => … p.1` / `p.2.1`
  (`Prod.fst` / `Prod.snd`) instead of pattern-matching lambdas `fun (x, ()) => …`, and explicit
  `Op.mk` applications with explicit `{rs}`/`{sig}` arguments, avoiding `LCNF base` blowup and
  making executable (`def`) 2000-instruction functions elaborate and compile fast.

Every word except `tqbe` and `tqbe_def` (plus already-reserved `break`, `continue`, `else`) is a
non-reserved symbol (`&"…"`), so importing this module does not pollute Lean's keyword table.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Notation

open Lean Elab Command Term Meta

declare_syntax_cat tqbe_ty (behavior := both)
declare_syntax_cat tqbe_arg (behavior := both)
declare_syntax_cat tqbe_opt_param
declare_syntax_cat tqbe_loop_param
declare_syntax_cat tqbe_sym
declare_syntax_cat tqbe_target (behavior := both)
declare_syntax_cat tqbe_stmt (behavior := both)
declare_syntax_cat tqbe_marg
declare_syntax_cat tqbe_rets
declare_syntax_cat tqbe_switch_arm

/-- Type syntax: QBE shorthands (`w`, `l`, `b`, `s`, `d`), explicit types (`bool`, `i8`, `i16`,
`i32`, `i64`, `bits n`, `f16`, `f32`, `f64`, `f128`, `float s`, `v4i32`, `vec k t`, `pair a b`,
`(a, b)`, `mask t`), Lean identifiers of type `Ty` (e.g. `u128`), or `⟨term⟩`. -/
syntax ident : tqbe_ty
syntax (priority := high) &"bits" ppSpace num : tqbe_ty
syntax (priority := high) &"bits" ppSpace "⟨" term "⟩" : tqbe_ty
syntax (priority := high) &"float" ppSpace ident : tqbe_ty
syntax (priority := high) &"vec" ppSpace num tqbe_ty : tqbe_ty
syntax (priority := high) &"vec" ppSpace ident tqbe_ty : tqbe_ty
syntax (priority := high) &"vec" ppSpace "⟨" term "⟩" tqbe_ty : tqbe_ty
syntax (priority := high) &"pair" ppSpace tqbe_ty tqbe_ty : tqbe_ty
syntax (priority := high) &"mask" ppSpace tqbe_ty : tqbe_ty
syntax (priority := high) "(" tqbe_ty ")" : tqbe_ty
syntax (priority := high) "(" tqbe_ty "," tqbe_ty,+ ")" : tqbe_ty
syntax "⟨" term "⟩" : tqbe_ty

/-- Operand syntax: `%x`, numeric/boolean/pair/lane-wise immediates, typed immediates `c:ty`,
or spliced Lean terms `⟨arg⟩` / `imm ⟨val⟩`. -/
syntax "%" noWs ident : tqbe_arg
syntax num : tqbe_arg
syntax "-" noWs num : tqbe_arg
syntax &"true" : tqbe_arg
syntax &"false" : tqbe_arg
syntax "[" tqbe_arg,* "]" : tqbe_arg
syntax &"splat" ppSpace tqbe_arg:60 : tqbe_arg
syntax "(" tqbe_arg "," tqbe_arg,+ ")" : tqbe_arg
syntax "(" tqbe_arg:51 ":" tqbe_ty ")" : tqbe_arg
syntax &"imm" ppSpace "⟨" term "⟩" : tqbe_arg
syntax "⟨" term "⟩" : tqbe_arg
syntax:50 tqbe_arg:51 ":" tqbe_ty : tqbe_arg

/-- Binder parameter `%x` or `%x:ty` (or wildcard `%_` / `%_:ty`). -/
syntax "%" noWs ident (":" tqbe_ty)? : tqbe_opt_param
syntax "%" noWs "_" (":" tqbe_ty)? : tqbe_opt_param

/-- Initialized loop parameter `%x:ty = init` (or `%x = init` when type is inferable from `init`, or wildcard `%_`). -/
syntax "%" noWs ident (":" tqbe_ty)? " = " tqbe_arg : tqbe_loop_param
syntax "%" noWs "_" (":" tqbe_ty)? " = " tqbe_arg : tqbe_loop_param

/-- Argument of a Lean macro: `%x`, `@l`, or `⟨term⟩`. -/
syntax "%" noWs ident : tqbe_marg
syntax "@" noWs ident : tqbe_marg
syntax "⟨" term "⟩" : tqbe_marg

/-- Global symbol `$f`. -/
syntax "$" noWs ident : tqbe_sym

/-- Return type list after `->`. -/
syntax (priority := high) "(" ")" : tqbe_rets
syntax (priority := high) "[" tqbe_ty,* "]" : tqbe_rets
syntax (priority := high) "(" tqbe_ty "," tqbe_ty,+ ")" : tqbe_rets
syntax tqbe_ty : tqbe_rets

/-- Branch/check/switch target. -/
syntax "@" noWs ident ("(" tqbe_arg,* ")")? : tqbe_target
syntax "{" tqbe_stmt* "}" : tqbe_target
syntax "break" ("@" noWs ident)? ("(" tqbe_arg,* ")")? : tqbe_target
syntax "continue" ("@" noWs ident)? ("(" tqbe_arg,* ")")? : tqbe_target

/-- Switch arm. -/
syntax tqbe_arg " => " tqbe_target (",")? : tqbe_switch_arm
syntax "_" " => " tqbe_target (",")? : tqbe_switch_arm

/-- Statements. -/
syntax tqbe_opt_param,+ " =" noWs tqbe_ty &"call" ppSpace tqbe_sym "(" tqbe_arg,* ")" : tqbe_stmt
syntax tqbe_opt_param,+ " =" noWs tqbe_ty &"load" ppSpace tqbe_arg : tqbe_stmt
syntax tqbe_opt_param,+ " =" noWs tqbe_ty ident tqbe_arg,* : tqbe_stmt
syntax tqbe_opt_param,+ " = " &"call" ppSpace tqbe_sym "(" tqbe_arg,* ")" : tqbe_stmt
syntax tqbe_opt_param,+ " = " &"load" ppSpace tqbe_ty "," tqbe_arg : tqbe_stmt
syntax tqbe_opt_param,+ " = " &"load" ppSpace tqbe_arg : tqbe_stmt
syntax tqbe_opt_param,+ " = " ident tqbe_arg,* : tqbe_stmt
syntax &"store" ppSpace tqbe_ty tqbe_arg "," tqbe_arg : tqbe_stmt
syntax (priority := high) &"store" ppSpace tqbe_arg "," tqbe_arg : tqbe_stmt
syntax &"call" ppSpace tqbe_sym "(" tqbe_arg,* ")" : tqbe_stmt
syntax &"exit" ppSpace tqbe_sym "(" tqbe_arg,* ")" : tqbe_stmt
syntax &"jmp" ppSpace "@" noWs ident ("(" tqbe_arg,* ")")? : tqbe_stmt
syntax &"jnz" ppSpace tqbe_arg "," tqbe_target "," tqbe_target : tqbe_stmt
syntax &"check" ppSpace tqbe_arg " else " tqbe_target : tqbe_stmt
syntax &"switch" ppSpace tqbe_arg "{" tqbe_switch_arm* "}" : tqbe_stmt
syntax (priority := high) tqbe_opt_param,+ " <- " &"loop" ("@" noWs ident)?
    "(" tqbe_loop_param,* ")" "{" tqbe_stmt* "}" : tqbe_stmt
syntax &"loop" ("@" noWs ident)? "(" tqbe_loop_param,* ")"
    ("->" "@" noWs ident ("(" tqbe_opt_param,* ")")?)? "{" tqbe_stmt* "}" : tqbe_stmt
syntax "break" ("@" noWs ident)? ("(" tqbe_arg,* ")")? : tqbe_stmt
syntax "continue" ("@" noWs ident)? ("(" tqbe_arg,* ")")? : tqbe_stmt
syntax &"ret" (ppSpace tqbe_arg),* : tqbe_stmt
syntax &"hlt" : tqbe_stmt
syntax "@" noWs ident ("(" tqbe_opt_param,* ")")? "{" tqbe_stmt* "}" : tqbe_stmt
syntax tqbe_opt_param,+ " <- " ident "(" tqbe_marg,* ")" : tqbe_stmt
syntax &"use" ppSpace ident "(" tqbe_marg,* ")" : tqbe_stmt
syntax "⟨" term "⟩" : tqbe_stmt
syntax "{" tqbe_stmt* "}" : tqbe_stmt

/-! ## Meta elaborator helpers -/

meta def fastNat? (e : Lean.Expr) : Option Nat :=
  match e with
  | .lit (.natVal n) => some n
  | .const ``Nat.zero [] => some 0
  | .app (.app (.app (.const ``OfNat.ofNat _) _) (.lit (.natVal n))) _ => some n
  | _ => none

meta def tyConst : Lean.Expr := Lean.mkConst ``LeanQbe.T.Ty
meta def listTyConst : Lean.Expr := mkApp (Lean.mkConst ``List [.zero]) tyConst
meta def boolTyExpr : Lean.Expr := Lean.mkConst ``LeanQbe.T.Ty.bool
meta def i64TyExpr : Lean.Expr := Lean.mkConst ``LeanQbe.T.i64
meta def i32TyExpr : Lean.Expr := Lean.mkConst ``LeanQbe.T.i32
meta def i16TyExpr : Lean.Expr := Lean.mkConst ``LeanQbe.T.i16
meta def i8TyExpr : Lean.Expr := Lean.mkConst ``LeanQbe.T.i8
meta def punitTy : Lean.Expr := Lean.mkConst ``PUnit [.succ .zero]
meta def punitVal : Lean.Expr := Lean.mkConst ``PUnit.unit [.succ .zero]

meta def fmtConst : Fmt → Lean.Expr
  | .h => Lean.mkConst ``LeanQbe.T.Fmt.h
  | .s => Lean.mkConst ``LeanQbe.T.Fmt.s
  | .d => Lean.mkConst ``LeanQbe.T.Fmt.d
  | .q => Lean.mkConst ``LeanQbe.T.Fmt.q

meta def mkBitsTy (nExpr : Lean.Expr) : Lean.Expr :=
  match fastNat? nExpr with
  | some 8 => i8TyExpr
  | some 16 => i16TyExpr
  | some 32 => i32TyExpr
  | some 64 => i64TyExpr
  | _ => mkApp (Lean.mkConst ``LeanQbe.T.Ty.bits) nExpr

meta def mkFloatTy : Fmt → Lean.Expr
  | .h => Lean.mkConst ``LeanQbe.T.f16
  | .s => Lean.mkConst ``LeanQbe.T.f32
  | .d => Lean.mkConst ``LeanQbe.T.f64
  | .q => Lean.mkConst ``LeanQbe.T.f128

meta def mkPairTy (a b : Lean.Expr) : Lean.Expr :=
  mkApp2 (Lean.mkConst ``LeanQbe.T.Ty.pair) a b

meta def listLit (elemTy : Lean.Expr) (es : List Lean.Expr) : Lean.Expr :=
  es.foldr (fun e acc => mkApp3 (Lean.mkConst ``List.cons [.zero]) elemTy e acc)
    (mkApp (Lean.mkConst ``List.nil [.zero]) elemTy)

meta def mkTupTy (elemKind f : Lean.Expr) (tys : List Lean.Expr) : Lean.Expr :=
  mkApp3 (Lean.mkConst ``LeanQbe.T.Tup) elemKind f (listLit elemKind tys)

meta def mkArgApp (ctxV : Lean.Expr) : Lean.Expr :=
  mkApp (Lean.mkConst ``LeanQbe.T.Arg) ctxV

meta def mkTupElems (elemKind f : Lean.Expr) (tys : List Lean.Expr) (vals : List Lean.Expr) :
    Lean.Expr :=
  match tys, vals with
  | [], [] => Lean.mkConst ``Unit.unit
  | t :: ts, v :: vs =>
    mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero]) (mkApp f t) (mkTupTy elemKind f ts) v
      (mkTupElems elemKind f ts vs)
  | _, _ => Lean.mkConst ``Unit.unit

meta def mkTypedProj (elemKind f : Lean.Expr) : List Lean.Expr → Lean.Expr → Nat → Lean.Expr
  | t :: ts, base, 0 =>
    mkApp3 (Lean.mkConst ``Prod.fst [.zero, .zero]) (mkApp f t) (mkTupTy elemKind f ts) base
  | t :: ts, base, i + 1 =>
    let snd := mkApp3 (Lean.mkConst ``Prod.snd [.zero, .zero]) (mkApp f t) (mkTupTy elemKind f ts) base
    mkTypedProj elemKind f ts snd i
  | [], base, _ => base

meta inductive TyShape
  | bool
  | bits (n? : Option Nat) (nExpr : Lean.Expr)
  | float (fmt : Fmt)
  | pair (a b : TyShape) (aExpr bExpr : Lean.Expr)
  | other (tyExpr : Lean.Expr)

meta def toTyShapeFast? : Lean.Expr → Option TyShape
  | .const ``LeanQbe.T.Ty.bool [] => some .bool
  | .app (.const ``LeanQbe.T.Ty.bits []) nExpr => do
    let n ← fastNat? nExpr
    pure (.bits (some n) nExpr)
  | .app (.const ``LeanQbe.T.Ty.float []) (.const fn []) =>
    if fn == ``LeanQbe.T.Fmt.h then some (.float .h)
    else if fn == ``LeanQbe.T.Fmt.s then some (.float .s)
    else if fn == ``LeanQbe.T.Fmt.d then some (.float .d)
    else if fn == ``LeanQbe.T.Fmt.q then some (.float .q)
    else none
  | .app (.app (.const ``LeanQbe.T.Ty.pair []) a) b => do
    let sa ← toTyShapeFast? a
    let sb ← toTyShapeFast? b
    pure (.pair sa sb a b)
  | .const ``LeanQbe.T.i8 [] => some (.bits (some 8) (mkNatLit 8))
  | .const ``LeanQbe.T.i16 [] => some (.bits (some 16) (mkNatLit 16))
  | .const ``LeanQbe.T.i32 [] => some (.bits (some 32) (mkNatLit 32))
  | .const ``LeanQbe.T.i64 [] => some (.bits (some 64) (mkNatLit 64))
  | .const ``LeanQbe.T.f16 [] => some (.float .h)
  | .const ``LeanQbe.T.f32 [] => some (.float .s)
  | .const ``LeanQbe.T.f64 [] => some (.float .d)
  | .const ``LeanQbe.T.f128 [] => some (.float .q)
  | _ => none

meta partial def toTyShape (e : Lean.Expr) : MetaM TyShape := do
  if let some s := toTyShapeFast? e then
    return s
  let w ← whnf e
  match w with
  | .const ``LeanQbe.T.Ty.bool [] => return .bool
  | .app (.const ``LeanQbe.T.Ty.bits []) nExpr =>
    let nExpr' ← whnf nExpr
    return .bits (fastNat? nExpr' <|> fastNat? nExpr) nExpr
  | .app (.const ``LeanQbe.T.Ty.float []) fExpr =>
    let fExpr ← whnf fExpr
    match fExpr with
    | .const ``LeanQbe.T.Fmt.h [] => return .float .h
    | .const ``LeanQbe.T.Fmt.s [] => return .float .s
    | .const ``LeanQbe.T.Fmt.d [] => return .float .d
    | .const ``LeanQbe.T.Fmt.q [] => return .float .q
    | _ => return .other w
  | .app (.app (.const ``LeanQbe.T.Ty.pair []) a) b =>
    return .pair (← toTyShape a) (← toTyShape b) a b
  | _ => return .other w

meta def TyShape.leafCount? : TyShape → Option Nat
  | .bool | .bits _ _ | .float _ => some 1
  | .pair a b _ _ => do pure ((← a.leafCount?) + (← b.leafCount?))
  | .other _ => none

meta def TyShape.valType : TyShape → Lean.Expr
  | .bool => Lean.mkConst ``Bool
  | .bits _ nExpr => mkApp (Lean.mkConst ``BitVec) nExpr
  | .float f => mkApp (Lean.mkConst ``BitVec) (mkNatLit f.width)
  | .pair a b _ _ => mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) a.valType b.valType
  | .other e => mkApp (Lean.mkConst ``LeanQbe.T.Val) e

meta def elabTyIdent (id : Ident) : TermElabM Lean.Expr :=
  match id.getId with
  | `b | `bool => pure boolTyExpr
  | `w | `i32 => pure (mkBitsTy (mkNatLit 32))
  | `l | `i64 => pure i64TyExpr
  | `i8 => pure (mkBitsTy (mkNatLit 8))
  | `i16 => pure (mkBitsTy (mkNatLit 16))
  | `s | `f32 => pure (mkFloatTy .s)
  | `d | `f64 => pure (mkFloatTy .d)
  | `f16 => pure (mkFloatTy .h)
  | `f128 => pure (mkFloatTy .q)
  | `v4i32 => pure (Lean.mkConst ``LeanQbe.T.v4i32)
  | `v8i32 => pure (Lean.mkConst ``LeanQbe.T.v8i32)
  | `v2i64 => pure (Lean.mkConst ``LeanQbe.T.v2i64)
  | `v4f32 => pure (Lean.mkConst ``LeanQbe.T.v4f32)
  | _ => do
    let e ← elabTermEnsuringType id tyConst
    synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    if e.hasExprMVar then
      throwErrorAt id "tqbe: could not resolve type {id}"
    return e

meta def elabFmtIdent (id : Ident) : TermElabM Fmt :=
  match id.getId with
  | `h => pure .h
  | `s => pure .s
  | `d => pure .d
  | `q => pure .q
  | _ => throwErrorAt id "tqbe: expected float format h, s, d, or q"

meta partial def elabTy : TSyntax `tqbe_ty → TermElabM Lean.Expr
  | `(tqbe_ty| $id:ident) => elabTyIdent id
  | `(tqbe_ty| bits $n:num) => pure (mkBitsTy (mkNatLit n.getNat))
  | stx@`(tqbe_ty| bits ⟨$t⟩) => do
    let e ← elabTermEnsuringType t (Lean.mkConst ``Nat)
    synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    if e.hasExprMVar then
      throwErrorAt stx m!"tqbe: could not resolve bit-width{indentExpr e}"
    pure (mkBitsTy e)
  | `(tqbe_ty| float $f:ident) => return mkFloatTy (← elabFmtIdent f)
  | `(tqbe_ty| vec $k:num $t:tqbe_ty) => do
    return mkApp2 (Lean.mkConst ``LeanQbe.T.Ty.vec) (mkNatLit k.getNat) (← elabTy t)
  | stx@`(tqbe_ty| vec $k:ident $t:tqbe_ty) => do
    let ke ← elabTermEnsuringType k (Lean.mkConst ``Nat)
    synthesizeSyntheticMVarsNoPostponing
    let ke ← instantiateMVars ke
    if ke.hasExprMVar then
      throwErrorAt stx m!"tqbe: could not resolve vector rank{indentExpr ke}"
    return mkApp2 (Lean.mkConst ``LeanQbe.T.Ty.vec) ke (← elabTy t)
  | stx@`(tqbe_ty| vec ⟨$k⟩ $t:tqbe_ty) => do
    let ke ← elabTermEnsuringType k (Lean.mkConst ``Nat)
    synthesizeSyntheticMVarsNoPostponing
    let ke ← instantiateMVars ke
    if ke.hasExprMVar then
      throwErrorAt stx m!"tqbe: could not resolve vector rank{indentExpr ke}"
    return mkApp2 (Lean.mkConst ``LeanQbe.T.Ty.vec) ke (← elabTy t)
  | `(tqbe_ty| pair $a:tqbe_ty $b:tqbe_ty) => do
    return mkPairTy (← elabTy a) (← elabTy b)
  | `(tqbe_ty| mask $t:tqbe_ty) => do
    return mkApp (Lean.mkConst ``LeanQbe.T.Ty.mask) (← elabTy t)
  | `(tqbe_ty| ($t:tqbe_ty)) => elabTy t
  | `(tqbe_ty| ($t:tqbe_ty, $ts:tqbe_ty,*)) => do
    let head ← elabTy t
    let tail ← ts.getElems.toList.mapM elabTy
    let rec foldPairs : Lean.Expr → List Lean.Expr → Lean.Expr
      | a, [] => a
      | a, [b] => mkPairTy a b
      | a, b :: rest => mkPairTy a (foldPairs b rest)
    return foldPairs head tail
  | stx@`(tqbe_ty| ⟨$t⟩) => do
    let e ← elabTermEnsuringType t tyConst
    synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    if e.hasExprMVar then
      throwErrorAt stx m!"tqbe: could not resolve spliced type{indentExpr e}"
    pure e
  | stx => throwErrorAt stx "tqbe: unsupported type syntax"

meta def elabRets : TSyntax `tqbe_rets → TermElabM (List Lean.Expr)
  | `(tqbe_rets| ()) => pure []
  | `(tqbe_rets| [$ts:tqbe_ty,*]) => ts.getElems.toList.mapM elabTy
  | `(tqbe_rets| ($t:tqbe_ty, $ts:tqbe_ty,*)) => do
    let head ← elabTy t
    let tail ← ts.getElems.toList.mapM elabTy
    pure (head :: tail)
  | `(tqbe_rets| $t:tqbe_ty) => do pure [← elabTy t]
  | stx => throwErrorAt stx "tqbe: unsupported return type list"

meta def parseOptParam (p : TSyntax `tqbe_opt_param) :
    TermElabM (Name × Option (TSyntax `tqbe_ty)) :=
  match p with
  | `(tqbe_opt_param| %$x:ident $[: $t:tqbe_ty]?) => pure (x.getId, t)
  | `(tqbe_opt_param| %_ $[: $t:tqbe_ty]?) => pure (`_, t)
  | _ => throwErrorAt p "tqbe: expected %name or %name:ty"

/-! ## Context and de Bruijn abstraction -/

meta structure VarBind where
  lvl : Nat
  proj? : Option (Nat × Lean.Expr × Lean.Expr × List Lean.Expr)
  ty : Lean.Expr

meta inductive LabelRole
  | normal
  | loopHeader
  | loopBreak
  deriving BEq, DecidableEq

meta structure LabelBind where
  lvl : Nat
  proj? : Option (Nat × Lean.Expr × Lean.Expr × List Lean.Expr)
  sig : List Lean.Expr
  sigExpr : Lean.Expr
  role : LabelRole

meta structure Ctx where
  V : Lean.Expr
  L : Lean.Expr
  rs? : Option (List Lean.Expr)
  rsExpr : Lean.Expr
  depth : Nat
  vars : NameMap VarBind
  labels : NameMap LabelBind
  varFVars : FVarIdMap (Nat × Option (Nat × Lean.Expr × Lean.Expr × List Lean.Expr))
  contTarget : Option (Nat × Option (Nat × Lean.Expr × Lean.Expr × List Lean.Expr) × List Lean.Expr × Lean.Expr)
  breakTarget : Option (Nat × Option (Nat × Lean.Expr × Lean.Expr × List Lean.Expr) × List Lean.Expr × Lean.Expr)

meta def Ctx.exprTy (ctx : Ctx) : Lean.Expr :=
  mkApp3 (Lean.mkConst ``LeanQbe.T.Expr) ctx.V ctx.L ctx.rsExpr

meta def Ctx.ref (ctx : Ctx) (lvl : Nat)
    (proj? : Option (Nat × Lean.Expr × Lean.Expr × List Lean.Expr)) (off : Nat := 0) : Lean.Expr :=
  let base := Lean.Expr.bvar (ctx.depth - 1 - lvl + off)
  match proj? with
  | none => base
  | some (i, kind, f, tys) => mkTypedProj kind f tys base i

meta partial def Ctx.abstract (ctx : Ctx) (e : Lean.Expr) (off : Nat := 0) : Lean.Expr :=
  if !e.hasFVar then e else
  match e with
  | .fvar id => match ctx.varFVars.get? id with
    | some (lvl, proj?) => ctx.ref lvl proj? off
    | none => e
  | .app f a => .app (ctx.abstract f off) (ctx.abstract a off)
  | .lam n t b bi => .lam n (ctx.abstract t off) (ctx.abstract b (off + 1)) bi
  | .forallE n t b bi => .forallE n (ctx.abstract t off) (ctx.abstract b (off + 1)) bi
  | .letE n t v b nd => .letE n (ctx.abstract t off) (ctx.abstract v off) (ctx.abstract b (off + 1)) nd
  | .mdata d b => .mdata d (ctx.abstract b off)
  | .proj s i b => .proj s i (ctx.abstract b off)
  | e => e

meta def elabLean (ctx : Ctx) (t : Syntax) (ty : Lean.Expr) : TermElabM Lean.Expr := do
  let e ← elabTermEnsuringType t ty
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  if e.hasExprMVar then
    throwErrorAt t m!"tqbe: could not elaborate{indentExpr e}\ncompletely (add a type ascription)"
  return ctx.abstract e

meta def withLoadBinder (ctx : Ctx) (x : Name) (ty : Lean.Expr) (k : Ctx → TermElabM Lean.Expr) :
    TermElabM Lean.Expr := do
  let lvl := ctx.depth
  let vTy := mkApp ctx.V ty
  if x == `_ || x == Name.anonymous then
    let body ← k { ctx with depth := ctx.depth + 1 }
    return .lam `v vTy body .default
  else
    withLocalDeclD x vTy fun fv => do
      let ctx' := { ctx with
        depth := ctx.depth + 1
        vars := ctx.vars.insert x { lvl, proj? := none, ty }
        varFVars := ctx.varFVars.insert fv.fvarId! (lvl, none) }
      let body ← k ctx'
      return .lam x vTy body .default

meta def withTupleVars (ctx : Ctx) (ps : List (Name × Lean.Expr)) (k : Ctx → TermElabM Lean.Expr) :
    TermElabM Lean.Expr := do
  let lvl := ctx.depth
  let elemTys := ps.map (·.2)
  let tupTy := mkTupTy tyConst ctx.V elemTys
  let rec go (i : Nat) (rem : List (Name × Lean.Expr)) (c : Ctx) : TermElabM Lean.Expr :=
    match rem with
    | [] => k c
    | (x, ty) :: rest =>
      if x == `_ || x == Name.anonymous then
        go (i + 1) rest c
      else
        withLocalDeclD x (mkApp ctx.V ty) fun fv =>
          let proj := some (i, tyConst, ctx.V, elemTys)
          let c' := { c with
            vars := c.vars.insert x { lvl, proj? := proj, ty }
            varFVars := c.varFVars.insert fv.fvarId! (lvl, proj) }
          go (i + 1) rest c'
  let body ← go 0 ps { ctx with depth := ctx.depth + 1 }
  return .lam `p tupTy body .default

meta def withGroupLabels (ctx : Ctx)
    (ls : List (Option Name × List Lean.Expr × Lean.Expr × LabelRole))
    (k : Ctx → TermElabM Lean.Expr) : TermElabM Lean.Expr := do
  let lvl := ctx.depth
  let elemTys := ls.map (·.2.2.1)
  let tupTy := mkTupTy listTyConst ctx.L elemTys
  let rec go (j : Nat) (rem : List (Option Name × List Lean.Expr × Lean.Expr × LabelRole))
      (c : Ctx) : TermElabM Lean.Expr :=
    match rem with
    | [] => k c
    | (lName?, ts, tsExpr, role) :: rest =>
      match lName? with
      | none => go (j + 1) rest c
      | some lName =>
        if lName == `_ || lName == Name.anonymous then
          go (j + 1) rest c
        else
          withLocalDeclD lName (mkApp ctx.L tsExpr) fun fv =>
            let proj := some (j, listTyConst, ctx.L, elemTys)
            let c' := { c with
              labels := c.labels.insert lName
                { lvl, proj? := proj, sig := ts, sigExpr := tsExpr, role }
              varFVars := c.varFVars.insert fv.fvarId! (lvl, proj) }
            go (j + 1) rest c'
  let body ← go 0 ls { ctx with depth := ctx.depth + 1 }
  return .lam `Js tupTy body .default

/-! ## Operands and lane-wise immediates -/

meta def bvNatLit (nExpr : Lean.Expr) (n : Nat) : Lean.Expr :=
  mkApp3 (Lean.mkConst ``OfNat.ofNat [.zero]) (mkApp (Lean.mkConst ``BitVec) nExpr)
    (mkRawNatLit n) (mkApp2 (Lean.mkConst ``BitVec.instOfNat) nExpr (mkRawNatLit n))

meta def bvNegLit (nExpr : Lean.Expr) (n : Nat) : Lean.Expr :=
  let bvTy := mkApp (Lean.mkConst ``BitVec) nExpr
  mkApp3 (Lean.mkConst ``Neg.neg [.zero]) bvTy (mkApp (Lean.mkConst ``BitVec.instNeg) nExpr)
    (bvNatLit nExpr n)

meta def extractTyList? (e : Lean.Expr) : MetaM (Option (List Lean.Expr)) := do
  let mut cur ← whnf e
  let mut acc : List Lean.Expr := []
  while true do
    match cur with
    | .app (.const ``List.nil _) _ => return some acc
    | .app (.app (.app (.const ``List.cons _) _) t) rest =>
      acc := acc ++ [t]
      cur ← whnf rest
    | _ => return none
  return none

meta def isArgTyApp? (ctxV : Lean.Expr) (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let w ← whnf e
  if w.isAppOfArity ``LeanQbe.T.Arg 2 then
    if ← isDefEq w.appFn!.appArg! ctxV then
      return some w.appArg!
  return none

meta def isVApp? (ctxV : Lean.Expr) (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let w ← whnf e
  match w with
  | .app fn arg =>
    if ← isDefEq fn ctxV then return some arg else return none
  | _ => return none

meta def isLApp? (ctxL : Lean.Expr) (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let w ← whnf e
  match w with
  | .app fn arg =>
    if ← isDefEq fn ctxL then return some arg else return none
  | _ => return none

meta def checkTyEq (stx : Syntax) (expected actual : Lean.Expr) : TermElabM Unit := do
  unless ← isDefEq expected actual do
    throwErrorAt stx m!"tqbe: type mismatch: expected{indentExpr expected}\nbut got{indentExpr actual}"

/-- Peek at the type of an operand without constructing `Arg` yet (for binary/cmp type inference). -/
meta partial def peekArgTy? (ctx : Ctx) : TSyntax `tqbe_arg → TermElabM (Option Lean.Expr)
  | `(tqbe_arg| %$x:ident) => do
    match ctx.vars.find? x.getId with
    | some vb => return some vb.ty
    | none =>
      let s ← saveState
      try
        let e ← withTheReader Term.Context (fun c => { c with errToSorry := false }) <| elabTerm x none
        isVApp? ctx.V (← inferType e)
      catch _ =>
        s.restore
        return none
  | `(tqbe_arg| ($_:tqbe_arg : $t:tqbe_ty))
  | `(tqbe_arg| $_:tqbe_arg : $t:tqbe_ty) => some <$> elabTy t
  | `(tqbe_arg| true) | `(tqbe_arg| false) => return some boolTyExpr
  | `(tqbe_arg| ($a:tqbe_arg, $rest:tqbe_arg,*)) => do
    let some ta ← peekArgTy? ctx a | return none
    let mut ts : List Lean.Expr := [ta]
    for r in rest.getElems do
      let some tr ← peekArgTy? ctx r | return none
      ts := ts ++ [tr]
    let rec foldPairs : List Lean.Expr → Option Lean.Expr
      | [] => none
      | [x] => some x
      | x :: xs => (foldPairs xs).map (mkPairTy x)
    return foldPairs ts
  | `(tqbe_arg| ⟨$t⟩) => do
    let s ← saveState
    try
      let e ← withTheReader Term.Context (fun c => { c with errToSorry := false }) <| elabTerm t none
      isArgTyApp? ctx.V (← inferType e)
    catch _ =>
      s.restore
      return none
  | _ => return none

meta def checkBitsNatRange (stx : Syntax) (tyExpr : Lean.Expr) (n k : Nat) : TermElabM Unit := do
  unless k == 0 || k.log2 < n do
    throwErrorAt stx m!"tqbe: integer literal {k} out of range for type{indentExpr tyExpr}\n(expected < 2^{n})"

meta def checkBitsNegRange (stx : Syntax) (tyExpr : Lean.Expr) (n k : Nat) : TermElabM Unit := do
  unless n ≥ 1 && k ≥ 1 && (k == 1 || (k - 1).log2 < n - 1) do
    if n == 0 then
      throwErrorAt stx m!"tqbe: negative literal -{k} not valid for 0-bit type{indentExpr tyExpr}"
    else if k == 0 then
      throwErrorAt stx m!"tqbe: negative literal -0 not valid for type{indentExpr tyExpr}"
    else
      throwErrorAt stx m!"tqbe: negative literal -{k} out of range for type{indentExpr tyExpr}\n(expected 1 ≤ k ≤ 2^{n - 1})"

meta partial def hasSymbolicFloat (e : Lean.Expr) : MetaM Bool := do
  let w ← whnf e
  if w.isAppOfArity ``LeanQbe.T.Ty.float 1 then
    return true
  else if w.isAppOfArity ``LeanQbe.T.Ty.vec 2 then
    hasSymbolicFloat w.appArg!
  else if w.isAppOfArity ``LeanQbe.T.Ty.pair 2 then
    return (← hasSymbolicFloat w.appFn!.appArg!) || (← hasSymbolicFloat w.appArg!)
  else
    return false

meta partial def elabImmAtShape (tyExpr : Lean.Expr) (shape : TyShape) (stx : TSyntax `tqbe_arg) :
    TermElabM Lean.Expr := do
  match stx with
  | `(tqbe_arg| $n:num) =>
    let k := n.getNat
    match shape with
    | .bits n? nExpr =>
      if let some w := n? then
        checkBitsNatRange stx tyExpr w k
      return bvNatLit nExpr k
    | .float _ =>
      throwErrorAt stx m!"tqbe: bare integer literal `{k}` is not valid for floating-point type{indentExpr tyExpr}\n(use `imm ⟨...⟩`)"
    | .bool =>
      if k == 0 then return Lean.mkConst ``Bool.false
      else if k == 1 then return Lean.mkConst ``Bool.true
      else throwErrorAt stx s!"tqbe: invalid bool literal {k} (expected true, false, 0, or 1)"
    | .pair sa sb aE bE =>
      let va ← elabImmAtShape aE sa stx
      let vb ← elabImmAtShape bE sb stx
      return mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero]) sa.valType sb.valType va vb
    | .other e =>
      if ← hasSymbolicFloat e then
        throwErrorAt stx m!"tqbe: bare integer literal `{k}` is not valid for floating-point type{indentExpr tyExpr}\n(use `imm ⟨...⟩`)"
      let valTy := mkApp (Lean.mkConst ``LeanQbe.T.Val) e
      let t ← elabTermEnsuringType n valTy
      synthesizeSyntheticMVarsNoPostponing
      let t ← instantiateMVars t
      if t.hasExprMVar then
        throwErrorAt stx m!"tqbe: could not elaborate immediate at symbolic type{indentExpr e}"
      return t
  | `(tqbe_arg| -$n:num) =>
    let k := n.getNat
    match shape with
    | .bits n? nExpr =>
      if k == 0 then
        throwErrorAt stx m!"tqbe: negative literal -0 not valid for type{indentExpr tyExpr}"
      if let some w := n? then
        checkBitsNegRange stx tyExpr w k
      return bvNegLit nExpr k
    | .pair sa sb aE bE =>
      let va ← elabImmAtShape aE sa stx
      let vb ← elabImmAtShape bE sb stx
      return mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero]) sa.valType sb.valType va vb
    | _ => throwErrorAt stx m!"tqbe: negative literal -{k} not valid for type{indentExpr tyExpr}"
  | `(tqbe_arg| true) =>
    match shape with
    | .bool => return Lean.mkConst ``Bool.true
    | .pair sa sb aE bE =>
      let va ← elabImmAtShape aE sa stx
      let vb ← elabImmAtShape bE sb stx
      return mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero]) sa.valType sb.valType va vb
    | _ => throwErrorAt stx m!"tqbe: boolean literal `true` not valid for type{indentExpr tyExpr}"
  | `(tqbe_arg| false) =>
    match shape with
    | .bool => return Lean.mkConst ``Bool.false
    | .pair sa sb aE bE =>
      let va ← elabImmAtShape aE sa stx
      let vb ← elabImmAtShape bE sb stx
      return mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero]) sa.valType sb.valType va vb
    | _ => throwErrorAt stx m!"tqbe: boolean literal `false` not valid for type{indentExpr tyExpr}"
  | `(tqbe_arg| splat $inner:tqbe_arg) =>
    match shape with
    | .pair sa sb aE bE =>
      let va ← elabImmAtShape aE sa stx
      let vb ← elabImmAtShape bE sb stx
      return mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero]) sa.valType sb.valType va vb
    | _ => elabImmAtShape tyExpr shape inner
  | `(tqbe_arg| [$elems:tqbe_arg,*]) =>
    let arr := elems.getElems
    let some nLanes := shape.leafCount?
      | throwErrorAt stx m!"tqbe: cannot build lane-wise immediate for symbolic type{indentExpr tyExpr}"
    unless arr.size == nLanes do
      throwErrorAt stx m!"tqbe: lane-wise immediate has {arr.size} lane(s), expected {nLanes} for{indentExpr tyExpr}"
    let rec fill (s : TyShape) (te : Lean.Expr) (idx : Nat) : TermElabM (Lean.Expr × Nat) := do
      match s with
      | .pair sa sb aE bE =>
        let (va, idx1) ← fill sa aE idx
        let (vb, idx2) ← fill sb bE idx1
        return (mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero]) sa.valType sb.valType va vb, idx2)
      | _ =>
        let v ← elabImmAtShape te s arr[idx]!
        return (v, idx + 1)
    let (v, _) ← fill shape tyExpr 0
    return v
  | `(tqbe_arg| ($a:tqbe_arg, $rest:tqbe_arg,*)) =>
    let tail := rest.getElems
    let rec fillPair (elems : List (TSyntax `tqbe_arg)) (s : TyShape) (te : Lean.Expr) :
        TermElabM Lean.Expr := do
      match elems, s with
      | [x], _ => elabImmAtShape te s x
      | x :: xs, .pair sa sb aE bE =>
        let va ← elabImmAtShape aE sa x
        let vb ← fillPair xs sb bE
        return mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero]) sa.valType sb.valType va vb
      | _, _ => throwErrorAt stx m!"tqbe: pair immediate arity mismatch for type{indentExpr tyExpr}"
    fillPair (a :: tail.toList) shape tyExpr
  | `(tqbe_arg| ($inner:tqbe_arg : $t:tqbe_ty))
  | `(tqbe_arg| $inner:tqbe_arg : $t:tqbe_ty) => do
    let ty' ← elabTy t
    checkTyEq stx tyExpr ty'
    elabImmAtShape tyExpr shape inner
  | `(tqbe_arg| imm ⟨$t⟩) => do
    let valTy := mkApp (Lean.mkConst ``LeanQbe.T.Val) tyExpr
    let e ← elabTermEnsuringType t valTy
    synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    if e.hasExprMVar then
      throwErrorAt stx m!"tqbe: could not elaborate immediate{indentExpr e}"
    return e
  | _ => throwErrorAt stx m!"tqbe: expected immediate value of type{indentExpr tyExpr}"

meta partial def elabArg (ctx : Ctx) (expectedTy? : Option Lean.Expr) (stx : TSyntax `tqbe_arg) :
    TermElabM (Lean.Expr × Lean.Expr) := do
  let mkVar (ty v : Lean.Expr) : Lean.Expr :=
    mkApp3 (Lean.mkConst ``LeanQbe.T.Arg.var) ctx.V ty v
  let mkImm (ty v : Lean.Expr) : Lean.Expr :=
    mkApp3 (Lean.mkConst ``LeanQbe.T.Arg.imm) ctx.V ty v
  match stx with
  | `(tqbe_arg| %$x:ident) =>
    match ctx.vars.find? x.getId with
    | some vb =>
      if let some et := expectedTy? then checkTyEq stx et vb.ty
      return (mkVar vb.ty (ctx.ref vb.lvl vb.proj?), vb.ty)
    | none =>
      match expectedTy? with
      | some et =>
        let e ← elabLean ctx x (mkApp ctx.V et)
        return (mkVar et e, et)
      | none =>
        let e ← elabTerm x none
        synthesizeSyntheticMVarsNoPostponing
        let e ← instantiateMVars e
        if e.hasExprMVar then
          throwErrorAt stx s!"tqbe: could not infer type for %{x.getId}"
        let some ty ← isVApp? ctx.V (← inferType e)
          | throwErrorAt stx s!"tqbe: unknown variable %{x.getId} (or not of type V _)"
        let ty ← instantiateMVars ty
        return (mkVar ty (ctx.abstract e), ty)
  | `(tqbe_arg| ($inner:tqbe_arg : $t:tqbe_ty))
  | `(tqbe_arg| $inner:tqbe_arg : $t:tqbe_ty) =>
    let ty ← elabTy t
    if let some et := expectedTy? then checkTyEq stx et ty
    elabArg ctx (some ty) inner
  | `(tqbe_arg| ⟨$t⟩) =>
    match expectedTy? with
    | some et =>
      let argTy := mkApp2 (Lean.mkConst ``LeanQbe.T.Arg) ctx.V et
      return (← elabLean ctx t argTy, et)
    | none =>
      let tyM ← mkFreshExprMVar (some tyConst)
      let argTy := mkApp2 (Lean.mkConst ``LeanQbe.T.Arg) ctx.V tyM
      let e ← elabTermEnsuringType t argTy
      synthesizeSyntheticMVarsNoPostponing
      let e ← instantiateMVars e
      let ty ← instantiateMVars tyM
      if ty.hasExprMVar || e.hasExprMVar then
        throwErrorAt stx "tqbe: could not infer type for spliced operand"
      return (ctx.abstract e, ty)
  | `(tqbe_arg| imm ⟨$t⟩) =>
    match expectedTy? with
    | some et =>
      let valTy := mkApp (Lean.mkConst ``LeanQbe.T.Val) et
      let e ← elabLean ctx t valTy
      return (mkImm et e, et)
    | none =>
      let tyM ← mkFreshExprMVar (some tyConst)
      let valTy := mkApp (Lean.mkConst ``LeanQbe.T.Val) tyM
      let e ← elabTermEnsuringType t valTy
      synthesizeSyntheticMVarsNoPostponing
      let e ← instantiateMVars e
      let ty ← instantiateMVars tyM
      if ty.hasExprMVar || e.hasExprMVar then
        throwErrorAt stx "tqbe: could not infer type for spliced immediate"
      return (mkImm ty (ctx.abstract e), ty)
  | `(tqbe_arg| true) =>
    let ty := expectedTy?.getD boolTyExpr
    if let some et := expectedTy? then
      let shape ← toTyShape et
      return (mkImm et (← elabImmAtShape et shape stx), et)
    else
      return (mkImm ty (Lean.mkConst ``Bool.true), ty)
  | `(tqbe_arg| false) =>
    let ty := expectedTy?.getD boolTyExpr
    if let some et := expectedTy? then
      let shape ← toTyShape et
      return (mkImm et (← elabImmAtShape et shape stx), et)
    else
      return (mkImm ty (Lean.mkConst ``Bool.false), ty)
  | _ =>
    match expectedTy? with
    | some et =>
      let shape ← toTyShape et
      let v ← elabImmAtShape et shape stx
      return (mkImm et v, et)
    | none =>
      if let some et ← peekArgTy? ctx stx then
        let shape ← toTyShape et
        let v ← elabImmAtShape et shape stx
        return (mkImm et v, et)
      throwErrorAt stx "tqbe: cannot infer type for immediate (add `:ty`, e.g. `0:l`)"

meta def elabArgListWithSig (ctx : Ctx) (stx : Syntax) (sig : List Lean.Expr)
    (args : Array (TSyntax `tqbe_arg)) : TermElabM Lean.Expr := do
  unless args.size == sig.length do
    throwErrorAt stx s!"tqbe: expected {sig.length} argument(s), got {args.size}"
  let argElems ← (args.toList.zip sig).mapM fun (a, t) => do
    let (ae, _) ← elabArg ctx (some t) a
    pure ae
  return mkTupElems tyConst (mkArgApp ctx.V) sig argElems

meta def elabArgListOpen (ctx : Ctx) (args : Array (TSyntax `tqbe_arg)) :
    TermElabM (List Lean.Expr × Lean.Expr) := do
  let res ← args.toList.mapM (elabArg ctx none)
  let tys := res.map (·.2)
  let aes := res.map (·.1)
  return (tys, mkTupElems tyConst (mkArgApp ctx.V) tys aes)

meta def symLit (s : TSyntax `tqbe_sym) : TermElabM Lean.Expr := do
  let some f := s.raw.getArgs.find? (·.isIdent) | throwErrorAt s "tqbe: expected $symbol"
  return mkStrLit f.getId.toString

meta def withResolvedMacroArgs {α : Type} (ctx : Ctx) (ys : Array (TSyntax `tqbe_marg))
    (k : Ctx → Array Term → TermElabM α) : TermElabM α :=
  let rec go (i : Nat) (c : Ctx) (acc : Array Term) : TermElabM α := do
    if _ : i < ys.size then
      let stx := ys[i]!
      match stx with
      | `(tqbe_marg| %$x:ident) =>
        match c.vars.find? x.getId with
        | some vb =>
          let fresh := Name.mkSimple s!"__tqbe_marg_{c.depth}_{i}"
          withLocalDeclD fresh (mkApp c.V vb.ty) fun fv =>
            let c' := { c with varFVars := c.varFVars.insert fv.fvarId! (vb.lvl, vb.proj?) }
            go (i + 1) c' (acc.push (mkIdentFrom x fresh))
        | none => go (i + 1) c (acc.push x)
      | `(tqbe_marg| @$l:ident) =>
        match c.labels.find? l.getId with
        | some lb =>
          let fresh := Name.mkSimple s!"__tqbe_marg_{c.depth}_{i}"
          withLocalDeclD fresh (mkApp c.L lb.sigExpr) fun fv =>
            let c' := { c with varFVars := c.varFVars.insert fv.fvarId! (lb.lvl, lb.proj?) }
            go (i + 1) c' (acc.push (mkIdentFrom l fresh))
        | none => go (i + 1) c (acc.push l)
      | `(tqbe_marg| ⟨$t⟩) => go (i + 1) c (acc.push t)
      | _ => throwErrorAt stx "tqbe: unsupported macro argument"
    else
      k c acc
  go 0 ctx #[]

meta def elabImm8 (stx : TSyntax `tqbe_arg) : TermElabM Lean.Expr :=
  match stx with
  | `(tqbe_arg| $n:num) => do
    let k := n.getNat
    unless k < 256 do
      throwErrorAt stx s!"tqbe: 8-bit immediate {k} out of range (expected < 256)"
    pure (bvNatLit (mkNatLit 8) k)
  | `(tqbe_arg| ⟨$t⟩) => do
    let e ← elabTermEnsuringType t (mkApp (Lean.mkConst ``BitVec) (mkNatLit 8))
    synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    if e.hasExprMVar then
      throwErrorAt stx m!"tqbe: could not elaborate 8-bit immediate{indentExpr e}"
    pure e
  | _ => throwErrorAt stx "tqbe: expected 8-bit immediate (numeral or ⟨BitVec 8⟩)"

/-! ## Operation instruction builder (`Op.mk` + projection lambdas) -/

meta def cmpNames : List (String × Name) :=
  [("eq", ``LeanQbe.T.CmpOp.eq), ("ne", ``LeanQbe.T.CmpOp.ne),
   ("ult", ``LeanQbe.T.CmpOp.ult), ("ule", ``LeanQbe.T.CmpOp.ule),
   ("ugt", ``LeanQbe.T.CmpOp.ugt), ("uge", ``LeanQbe.T.CmpOp.uge),
   ("slt", ``LeanQbe.T.CmpOp.slt), ("sle", ``LeanQbe.T.CmpOp.sle),
   ("sgt", ``LeanQbe.T.CmpOp.sgt), ("sge", ``LeanQbe.T.CmpOp.sge)]

meta def fcmpNames : List (String × Name) :=
  [("eq", ``LeanQbe.T.FCmpOp.eq), ("ne", ``LeanQbe.T.FCmpOp.ne),
   ("lt", ``LeanQbe.T.FCmpOp.lt), ("le", ``LeanQbe.T.FCmpOp.le),
   ("gt", ``LeanQbe.T.FCmpOp.gt), ("ge", ``LeanQbe.T.FCmpOp.ge),
   ("ord", ``LeanQbe.T.FCmpOp.ord), ("uno", ``LeanQbe.T.FCmpOp.uno)]

meta def parseQbeCmp? (s : String) : Option (Name × Lean.Expr) :=
  match s.toList with
  | 'c' :: rest =>
    match rest.getLast?, rest.dropLast with
    | some 'w', o => (cmpNames.lookup (String.ofList o)).map fun c => (c, mkBitsTy (mkNatLit 32))
    | some 'l', o => (cmpNames.lookup (String.ofList o)).map fun c => (c, i64TyExpr)
    | _, _ => none
  | _ => none

meta def parseFCmp? (s : String) : Option (Name × Option Lean.Expr) :=
  match s.toList with
  | 'f' :: rest =>
    match fcmpNames.lookup (String.ofList rest) with
    | some c => some (c, none)
    | none =>
      let fmtTy? := match rest.getLast? with
        | some 'h' => some (mkFloatTy .h)
        | some 's' => some (mkFloatTy .s)
        | some 'd' => some (mkFloatTy .d)
        | some 'q' => some (mkFloatTy .q)
        | _ => none
      match fcmpNames.lookup (String.ofList rest.dropLast), fmtTy? with
      | some c, some fty => some (c, some fty)
      | _, _ => none
  | _ => none

meta def mkMaskEqRefl (mExpr : Lean.Expr) : Lean.Expr :=
  mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) tyConst mExpr

meta def inferArgTyFromList (ctx : Ctx) (stx : Syntax) (args : Array (TSyntax `tqbe_arg)) :
    TermElabM Lean.Expr := do
  for a in args do
    if let some t ← peekArgTy? ctx a then
      return t
  throwErrorAt stx "tqbe: could not infer operand type (add `:ty` after `=` or on an operand)"

meta def requireBitsWidth (stx : Syntax) (ty : Lean.Expr) : TermElabM Lean.Expr := do
  match ← toTyShape ty with
  | .bits _ nExpr => return nExpr
  | _ => throwErrorAt stx m!"tqbe: expected bits type, got{indentExpr ty}"

meta def requireFloatFmt (stx : Syntax) (ty : Lean.Expr) : TermElabM Fmt := do
  match ← toTyShape ty with
  | .float f => return f
  | _ => throwErrorAt stx m!"tqbe: expected float type, got{indentExpr ty}"

meta def mkBitcastEq (stx : Syntax) (t u : Lean.Expr) : TermElabM Lean.Expr := do
  let szT := mkApp (Lean.mkConst ``LeanQbe.T.Ty.size) t
  let szU := mkApp (Lean.mkConst ``LeanQbe.T.Ty.size) u
  if ← isDefEq szT szU then
    return mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) (Lean.mkConst ``Nat) szT
  let eqProp := mkApp3 (Lean.mkConst ``Eq [.succ .zero]) (Lean.mkConst ``Nat) szT szU
  let mvar ← mkFreshExprSyntheticOpaqueMVar eqProp
  let s ← saveState
  try
    let tacStx ← `(tactic| (dsimp only [LeanQbe.T.Ty.size, LeanQbe.T.Fmt.width, LeanQbe.T.Ty.vec]; omega))
    let remaining ← Tactic.run mvar.mvarId! (Tactic.evalTactic tacStx)
    unless remaining.isEmpty do
      throwError "unsolved"
    let h ← instantiateMVars mvar
    if h.hasExprMVar then
      throwError "mvars"
    return h
  catch _ =>
    s.restore
    throwErrorAt stx m!"tqbe: bitcast size mismatch between{indentExpr t}\nand{indentExpr u}"

meta def mkOpApp (ctx : Ctx) (sig rs : List Lean.Expr) (code : Lean.Expr)
    (args : Array (TSyntax `tqbe_arg)) (stx : Syntax) : TermElabM Lean.Expr := do
  let sigExpr := listLit tyConst sig
  let rsExpr := listLit tyConst rs
  let argsTup ← elabArgListWithSig ctx stx sig args
  return mkAppN (Lean.mkConst ``LeanQbe.T.Op.mk) #[ctx.V, rsExpr, sigExpr, code, argsTup]

meta def wrapLet (ctx : Ctx) (rsList : List Lean.Expr) (op : Lean.Expr)
    (binders : List (Name × Lean.Expr)) (k : Ctx → TermElabM Lean.Expr) : TermElabM Lean.Expr := do
  let tsExpr := listLit tyConst rsList
  let lam ← withTupleVars ctx binders k
  return mkAppN (Lean.mkConst ``LeanQbe.T.Expr.let_) #[ctx.V, ctx.L, ctx.rsExpr, tsExpr, op, lam]

meta def elabMaskCmp (ctx : Ctx) (opId : Syntax) (args : Array (TSyntax `tqbe_arg))
    (singleResTy? : TermElabM (Option Lean.Expr)) (outName : Name)
    (k : Ctx → TermElabM Lean.Expr) (opCodeName cmpCtor : Name)
    (t : Lean.Expr) : TermElabM Lean.Expr := do
  let mDef := mkApp (Lean.mkConst ``LeanQbe.T.Ty.mask) t
  let mDefault ← match ← toTyShape t with
    | .bool | .bits _ _ | .float _ => pure boolTyExpr
    | _ => pure mDef
  let mUse ← match ← singleResTy? with
    | some rt => checkTyEq opId mDef rt; pure rt
    | none => pure mDefault
  let code := mkApp4 (Lean.mkConst opCodeName)
    (Lean.mkConst cmpCtor) t mUse (mkMaskEqRefl mUse)
  let op ← mkOpApp ctx [t, t] [mUse] code args opId
  wrapLet ctx [mUse] op [(outName, mUse)] k

meta def elabAssignOp (ctx : Ctx) (lhs : List (Name × Option Lean.Expr))
    (opResTy? : Option Lean.Expr) (opId : Ident) (args : Array (TSyntax `tqbe_arg))
    (k : Ctx → TermElabM Lean.Expr) : TermElabM Lean.Expr := do
  let name := opId.getId.toString
  let arity (n : Nat) : TermElabM Unit :=
    unless args.size == n do
      throwErrorAt opId s!"tqbe: `{name}` takes {n} operand(s), got {args.size}"
  let resArity (n : Nat) : TermElabM Unit :=
    unless lhs.length == n do
      throwErrorAt opId s!"tqbe: `{name}` produces {n} result(s), got {lhs.length} LHS binder(s)"

  -- Determine single result type when `lhs.length == 1`:
  let singleResTy? : TermElabM (Option Lean.Expr) := do
    match opResTy?, lhs with
    | some t1, [(_, some t2)] => checkTyEq opId t1 t2; return some t1
    | some t1, [(_, none)] => return some t1
    | none, [(_, some t2)] => return some t2
    | _, _ => return none

  let inferUnaryTy : TermElabM Lean.Expr := do
    if let some t ← singleResTy? then return t
    inferArgTyFromList ctx opId args

  -- Multi-result operations first
  if name == "addc" || name == "subb" then
    resArity 2; arity 3
    let nTy ← match opResTy?, lhs[0]!.2 with
      | some t, _ => pure t
      | none, some t => pure t
      | none, none => inferArgTyFromList ctx opId #[args[0]!, args[1]!]
    let nExpr ← requireBitsWidth opId nTy
    let bitsTy := mkBitsTy nExpr
    if let some t0 := lhs[0]!.2 then checkTyEq opId bitsTy t0
    if let some bt := lhs[1]!.2 then checkTyEq opId boolTyExpr bt
    let ctor := if name == "addc" then ``LeanQbe.T.OpCode.addc else ``LeanQbe.T.OpCode.subb
    let op ← mkOpApp ctx [bitsTy, bitsTy, boolTyExpr] [bitsTy, boolTyExpr]
      (mkApp (Lean.mkConst ctor) nExpr) args opId
    return ← wrapLet ctx [bitsTy, boolTyExpr] op [(lhs[0]!.1, bitsTy), (lhs[1]!.1, boolTyExpr)] k

  if name == "umulw" || name == "smulw" then
    resArity 2; arity 2
    let nTy ← match opResTy?, lhs[0]!.2, lhs[1]!.2 with
      | some t, _, _ => pure t
      | none, some t, _ => pure t
      | none, _, some t => pure t
      | none, none, none => inferArgTyFromList ctx opId args
    let nExpr ← requireBitsWidth opId nTy
    let bitsTy := mkBitsTy nExpr
    if let some t0 := lhs[0]!.2 then checkTyEq opId bitsTy t0
    if let some t1 := lhs[1]!.2 then checkTyEq opId bitsTy t1
    let ctor := if name == "umulw" then ``LeanQbe.T.OpCode.umulw else ``LeanQbe.T.OpCode.smulw
    let op ← mkOpApp ctx [bitsTy, bitsTy] [bitsTy, bitsTy]
      (mkApp (Lean.mkConst ctor) nExpr) args opId
    return ← wrapLet ctx [bitsTy, bitsTy] op [(lhs[0]!.1, bitsTy), (lhs[1]!.1, bitsTy)] k

  if name == "unpair" then
    resArity 2; arity 1
    let (aTy, bTy) ← match ← peekArgTy? ctx args[0]! with
      | some pTy =>
        match ← toTyShape pTy with
        | .pair _ _ aE bE =>
          if let some rt := opResTy? then checkTyEq opId (mkPairTy aE bE) rt
          pure (aE, bE)
        | _ => throwErrorAt opId m!"tqbe: `unpair` operand has non-pair type{indentExpr pTy}"
      | none =>
        match opResTy? with
        | some rt =>
          match ← toTyShape rt with
          | .pair _ _ aE bE => pure (aE, bE)
          | _ => throwErrorAt opId m!"tqbe: `unpair` expected pair type, got{indentExpr rt}"
        | none =>
          match lhs[0]!.2, lhs[1]!.2 with
          | some aE, some bE => pure (aE, bE)
          | _, _ => throwErrorAt opId "tqbe: could not infer types for `unpair`"
    if let some t0 := lhs[0]!.2 then checkTyEq opId aTy t0
    if let some t1 := lhs[1]!.2 then checkTyEq opId bTy t1
    let op ← mkOpApp ctx [mkPairTy aTy bTy] [aTy, bTy]
      (mkApp2 (Lean.mkConst ``LeanQbe.T.OpCode.unpair) aTy bTy) args opId
    return ← wrapLet ctx [aTy, bTy] op [(lhs[0]!.1, aTy), (lhs[1]!.1, bTy)] k

  -- All remaining operations produce 1 result
  resArity 1
  let outName := lhs[0]!.1

  if name == "fst" || name == "snd" then
    arity 1
    let some pTy ← peekArgTy? ctx args[0]!
      | throwErrorAt opId s!"tqbe: could not infer pair type for `{name}`"
    let .pair _ _ aTy bTy ← toTyShape pTy
      | throwErrorAt opId m!"tqbe: `{name}` operand has non-pair type{indentExpr pTy}"
    let expectedOut := if name == "fst" then aTy else bTy
    if let some rt ← singleResTy? then checkTyEq opId expectedOut rt
    let op ← mkOpApp ctx [mkPairTy aTy bTy] [aTy, bTy]
      (mkApp2 (Lean.mkConst ``LeanQbe.T.OpCode.unpair) aTy bTy) args opId
    let binds := if name == "fst" then [(outName, aTy), (`_, bTy)] else [(`_, aTy), (outName, bTy)]
    return ← wrapLet ctx [aTy, bTy] op binds k

  if name == "mkpair" then
    arity 2
    let (aTy, bTy, resTy) ← match ← singleResTy? with
      | some rt =>
        match ← toTyShape rt with
        | .pair _ _ aE bE => pure (aE, bE, rt)
        | _ => throwErrorAt opId m!"tqbe: `mkpair` expected pair result type, got{indentExpr rt}"
      | none =>
        let aE ← inferArgTyFromList ctx opId #[args[0]!]
        let bE ← inferArgTyFromList ctx opId #[args[1]!]
        pure (aE, bE, mkPairTy aE bE)
    let op ← mkOpApp ctx [aTy, bTy] [mkPairTy aTy bTy]
      (mkApp2 (Lean.mkConst ``LeanQbe.T.OpCode.mkpair) aTy bTy) args opId
    return ← wrapLet ctx [mkPairTy aTy bTy] op [(outName, resTy)] k

  -- Simple unary `OpCode t [t]` ops
  let unaryMap : List (String × Name) :=
    [("copy", ``LeanQbe.T.OpCode.copy), ("neg", ``LeanQbe.T.OpCode.neg),
     ("not", ``LeanQbe.T.OpCode.not), ("bswap", ``LeanQbe.T.OpCode.bswap),
     ("fsqrt", ``LeanQbe.T.OpCode.fsqrt), ("fneg", ``LeanQbe.T.OpCode.fneg),
     ("fabs", ``LeanQbe.T.OpCode.fabs)]
  if let some ctor := unaryMap.lookup name then
    arity 1
    let t ← inferUnaryTy
    let op ← mkOpApp ctx [t] [t] (mkApp (Lean.mkConst ctor) t) args opId
    return ← wrapLet ctx [t] op [(outName, t)] k

  -- Unary bits-width ops: `clz`, `cls`, `rbit`, `ctz`, `popcnt`
  let unaryBitsMap : List (String × Name) :=
    [("clz", ``LeanQbe.T.OpCode.clz), ("cls", ``LeanQbe.T.OpCode.cls),
     ("rbit", ``LeanQbe.T.OpCode.rbit), ("ctz", ``LeanQbe.T.OpCode.ctz),
     ("popcnt", ``LeanQbe.T.OpCode.popcnt)]
  if let some ctor := unaryBitsMap.lookup name then
    arity 1
    let t ← inferUnaryTy
    let nExpr ← requireBitsWidth opId t
    let bitsTy := mkBitsTy nExpr
    let op ← mkOpApp ctx [bitsTy] [bitsTy] (mkApp (Lean.mkConst ctor) nExpr) args opId
    return ← wrapLet ctx [bitsTy] op [(outName, bitsTy)] k

  -- Binary `OpCode [t, t] [t]` ops
  let binMap : List (String × Name) :=
    [("add", ``LeanQbe.T.OpCode.add), ("sub", ``LeanQbe.T.OpCode.sub),
     ("mul", ``LeanQbe.T.OpCode.mul), ("and", ``LeanQbe.T.OpCode.and),
     ("or", ``LeanQbe.T.OpCode.or), ("xor", ``LeanQbe.T.OpCode.xor),
     ("shl", ``LeanQbe.T.OpCode.shl), ("lshr", ``LeanQbe.T.OpCode.lshr),
     ("shr", ``LeanQbe.T.OpCode.lshr), ("ashr", ``LeanQbe.T.OpCode.ashr),
     ("sar", ``LeanQbe.T.OpCode.ashr), ("rotl", ``LeanQbe.T.OpCode.rotl),
     ("rotr", ``LeanQbe.T.OpCode.rotr), ("fadd", ``LeanQbe.T.OpCode.fadd),
     ("fsub", ``LeanQbe.T.OpCode.fsub), ("fmul", ``LeanQbe.T.OpCode.fmul),
     ("fdiv", ``LeanQbe.T.OpCode.fdiv), ("shufb", ``LeanQbe.T.OpCode.shufb)]
  if let some ctor := binMap.lookup name then
    arity 2
    let t ← inferUnaryTy
    let op ← mkOpApp ctx [t, t] [t] (mkApp (Lean.mkConst ctor) t) args opId
    return ← wrapLet ctx [t] op [(outName, t)] k

  -- Binary bits-width ops: `udiv`, `sdiv`, `urem`, `srem`, `udiv0`, `sdiv0`
  let divMap : List (String × Name) :=
    [("udiv", ``LeanQbe.T.OpCode.udiv), ("sdiv", ``LeanQbe.T.OpCode.sdiv),
     ("div", ``LeanQbe.T.OpCode.sdiv), ("urem", ``LeanQbe.T.OpCode.urem),
     ("srem", ``LeanQbe.T.OpCode.srem), ("rem", ``LeanQbe.T.OpCode.srem),
     ("udiv0", ``LeanQbe.T.OpCode.udiv0), ("sdiv0", ``LeanQbe.T.OpCode.sdiv0)]
  if let some ctor := divMap.lookup name then
    arity 2
    let t ← inferUnaryTy
    let nExpr ← requireBitsWidth opId t
    let bitsTy := mkBitsTy nExpr
    let op ← mkOpApp ctx [bitsTy, bitsTy] [bitsTy] (mkApp (Lean.mkConst ctor) nExpr) args opId
    return ← wrapLet ctx [bitsTy] op [(outName, bitsTy)] k

  -- Funnel shifts & `ffma`
  if name == "fshl" || name == "fshr" then
    arity 3
    let t ← inferUnaryTy
    let nExpr ← requireBitsWidth opId t
    let bitsTy := mkBitsTy nExpr
    let ctor := if name == "fshl" then ``LeanQbe.T.OpCode.fshl else ``LeanQbe.T.OpCode.fshr
    let op ← mkOpApp ctx [bitsTy, bitsTy, bitsTy] [bitsTy]
      (mkApp (Lean.mkConst ctor) nExpr) args opId
    return ← wrapLet ctx [bitsTy] op [(outName, bitsTy)] k

  if name == "ffma" then
    arity 3
    let t ← inferUnaryTy
    let op ← mkOpApp ctx [t, t, t] [t] (mkApp (Lean.mkConst ``LeanQbe.T.OpCode.ffma) t) args opId
    return ← wrapLet ctx [t] op [(outName, t)] k

  -- Immediate-parameterized SIMD / bitwise ops
  if name == "ternlog" then
    arity 4
    let t ← match ← singleResTy? with
      | some rt => pure rt
      | none => inferArgTyFromList ctx opId #[args[0]!, args[1]!, args[2]!]
    let imm8 ← elabImm8 args[3]!
    let op ← mkOpApp ctx [t, t, t] [t]
      (mkApp2 (Lean.mkConst ``LeanQbe.T.OpCode.ternlog) t imm8) #[args[0]!, args[1]!, args[2]!] opId
    return ← wrapLet ctx [t] op [(outName, t)] k

  if name == "shufd" then
    arity 2
    let t ← match ← singleResTy? with
      | some rt => pure rt
      | none => inferArgTyFromList ctx opId #[args[0]!]
    let imm8 ← elabImm8 args[1]!
    let op ← mkOpApp ctx [t] [t]
      (mkApp2 (Lean.mkConst ``LeanQbe.T.OpCode.shufd) t imm8) #[args[0]!] opId
    return ← wrapLet ctx [t] op [(outName, t)] k

  if name == "alignr" || name == "blendw" then
    arity 3
    let t ← match ← singleResTy? with
      | some rt => pure rt
      | none => inferArgTyFromList ctx opId #[args[0]!, args[1]!]
    let imm8 ← elabImm8 args[2]!
    let ctor := if name == "alignr" then ``LeanQbe.T.OpCode.alignr else ``LeanQbe.T.OpCode.blendw
    let op ← mkOpApp ctx [t, t] [t]
      (mkApp2 (Lean.mkConst ctor) t imm8) #[args[0]!, args[1]!] opId
    return ← wrapLet ctx [t] op [(outName, t)] k

  -- SHA-256
  if name == "sha256rnds2" then
    arity 3
    let v4 := Lean.mkConst ``LeanQbe.T.v4i32
    if let some rt ← singleResTy? then checkTyEq opId v4 rt
    let op ← mkOpApp ctx [v4, v4, v4] [v4] (Lean.mkConst ``LeanQbe.T.OpCode.sha256rnds2) args opId
    return ← wrapLet ctx [v4] op [(outName, v4)] k

  if name == "sha256msg1" || name == "sha256msg2" then
    arity 2
    let v4 := Lean.mkConst ``LeanQbe.T.v4i32
    if let some rt ← singleResTy? then checkTyEq opId v4 rt
    let ctor := if name == "sha256msg1" then ``LeanQbe.T.OpCode.sha256msg1 else ``LeanQbe.T.OpCode.sha256msg2
    let op ← mkOpApp ctx [v4, v4] [v4] (Lean.mkConst ctor) args opId
    return ← wrapLet ctx [v4] op [(outName, v4)] k

  -- Select & blend
  if name == "select" then
    arity 3
    let t ← match ← singleResTy? with
      | some rt => pure rt
      | none => inferArgTyFromList ctx opId #[args[1]!, args[2]!]
    let op ← mkOpApp ctx [boolTyExpr, t, t] [t]
      (mkApp (Lean.mkConst ``LeanQbe.T.OpCode.select) t) args opId
    return ← wrapLet ctx [t] op [(outName, t)] k

  if name == "blend" then
    arity 3
    let t ← match ← singleResTy? with
      | some rt => pure rt
      | none => inferArgTyFromList ctx opId #[args[1]!, args[2]!]
    let mExpr := mkApp (Lean.mkConst ``LeanQbe.T.Ty.mask) t
    let code := mkApp3 (Lean.mkConst ``LeanQbe.T.OpCode.blend) t mExpr (mkMaskEqRefl mExpr)
    let op ← mkOpApp ctx [mExpr, t, t] [t] code args opId
    return ← wrapLet ctx [t] op [(outName, t)] k

  -- Integer comparisons: bare (`eq`, `ult`, ...) or QBE-suffixed (`ceql`, `cultw`, ...)
  if let some cmpCtor := cmpNames.lookup name then
    arity 2
    let t ← inferArgTyFromList ctx opId args
    return ← elabMaskCmp ctx opId args singleResTy? outName k
      ``LeanQbe.T.OpCode.cmp cmpCtor t

  if let some (cmpCtor, t) := parseQbeCmp? name then
    arity 2
    return ← elabMaskCmp ctx opId args singleResTy? outName k
      ``LeanQbe.T.OpCode.cmp cmpCtor t

  -- Floating-point comparisons: bare (`feq`, `funo`, ...) or suffixed (`feqs`, `fltd`, ...)
  if let some (fcmpCtor, tOpt) := parseFCmp? name then
    arity 2
    let t ← match tOpt with
      | some ft => pure ft
      | none => inferArgTyFromList ctx opId args
    return ← elabMaskCmp ctx opId args singleResTy? outName k
      ``LeanQbe.T.OpCode.fcmp fcmpCtor t

  -- Integer extensions / truncations / `ofBool`
  if name == "zext" || name == "sext" || name == "trunc" then
    arity 1
    let some dstTy ← singleResTy?
      | throwErrorAt opId s!"tqbe: `{name}` requires explicit destination type (e.g. `=l {name}`)"
    let srcTy ← inferArgTyFromList ctx opId args
    let srcShape ← toTyShape srcTy
    let dstShape ← toTyShape dstTy
    let mExpr ← match srcShape with
      | .bits _ me => pure me
      | _ => throwErrorAt opId m!"tqbe: expected bits type, got{indentExpr srcTy}"
    let nExpr ← match dstShape with
      | .bits _ ne => pure ne
      | _ => throwErrorAt opId m!"tqbe: expected bits type, got{indentExpr dstTy}"
    if let (.bits (some m) _, .bits (some n) _) := (srcShape, dstShape) then
      if name == "trunc" then
        unless n ≤ m do
          throwErrorAt opId s!"tqbe: `trunc` destination width ({n}) cannot exceed source width ({m})"
      else
        unless m ≤ n do
          throwErrorAt opId s!"tqbe: `{name}` destination width ({n}) cannot be smaller than source width ({m})"
    let ctor := match name with
      | "zext" => ``LeanQbe.T.OpCode.zext
      | "sext" => ``LeanQbe.T.OpCode.sext
      | _ => ``LeanQbe.T.OpCode.trunc
    let srcBits := mkBitsTy mExpr
    let dstBits := mkBitsTy nExpr
    let op ← mkOpApp ctx [srcBits] [dstBits] (mkApp2 (Lean.mkConst ctor) mExpr nExpr) args opId
    return ← wrapLet ctx [dstBits] op [(outName, dstBits)] k

  if name.startsWith "ext" && name.length == 5 then
    let chars := name.toList
    match chars with
    | ['e', 'x', 't', sg, sz] =>
      let srcW? := match sz with | 'b' => some 8 | 'h' => some 16 | 'w' => some 32 | _ => none
      if (sg == 's' || sg == 'u') && srcW?.isSome then
        arity 1
        let some dstTy ← singleResTy?
          | throwErrorAt opId s!"tqbe: `{name}` requires explicit destination type (e.g. `=l {name}`)"
        let srcW := srcW?.get!
        let mExpr := mkNatLit srcW
        let dstShape ← toTyShape dstTy
        let nExpr ← match dstShape with
          | .bits _ ne => pure ne
          | _ => throwErrorAt opId m!"tqbe: expected bits type, got{indentExpr dstTy}"
        if let .bits (some n) _ := dstShape then
          unless srcW ≤ n do
            throwErrorAt opId s!"tqbe: `{name}` destination width ({n}) cannot be smaller than source width ({srcW})"
        let ctor := if sg == 's' then ``LeanQbe.T.OpCode.sext else ``LeanQbe.T.OpCode.zext
        let srcBits := mkBitsTy mExpr
        let dstBits := mkBitsTy nExpr
        let op ← mkOpApp ctx [srcBits] [dstBits] (mkApp2 (Lean.mkConst ctor) mExpr nExpr) args opId
        return ← wrapLet ctx [dstBits] op [(outName, dstBits)] k
    | _ => pure ()

  if name == "ofBool" then
    arity 1
    let some dstTy ← singleResTy?
      | throwErrorAt opId "tqbe: `ofBool` requires explicit destination type (e.g. `=l ofBool`)"
    let nExpr ← requireBitsWidth opId dstTy
    let dstBits := mkBitsTy nExpr
    let op ← mkOpApp ctx [boolTyExpr] [dstBits]
      (mkApp (Lean.mkConst ``LeanQbe.T.OpCode.ofBool) nExpr) args opId
    return ← wrapLet ctx [dstBits] op [(outName, dstBits)] k

  -- Float conversions
  if name == "fptoui" || name == "fptosi" then
    arity 1
    let some dstTy ← singleResTy?
      | throwErrorAt opId s!"tqbe: `{name}` requires explicit destination type"
    let srcTy ← inferArgTyFromList ctx opId args
    let f ← requireFloatFmt opId srcTy
    let nExpr ← requireBitsWidth opId dstTy
    let ctor := if name == "fptoui" then ``LeanQbe.T.OpCode.fptoui else ``LeanQbe.T.OpCode.fptosi
    let srcF := mkFloatTy f
    let dstB := mkBitsTy nExpr
    let op ← mkOpApp ctx [srcF] [dstB] (mkApp2 (Lean.mkConst ctor) (fmtConst f) nExpr) args opId
    return ← wrapLet ctx [dstB] op [(outName, dstB)] k

  if name == "uitofp" || name == "sitofp" then
    arity 1
    let some dstTy ← singleResTy?
      | throwErrorAt opId s!"tqbe: `{name}` requires explicit destination type"
    let srcTy ← inferArgTyFromList ctx opId args
    let nExpr ← requireBitsWidth opId srcTy
    let g ← requireFloatFmt opId dstTy
    let ctor := if name == "uitofp" then ``LeanQbe.T.OpCode.uitofp else ``LeanQbe.T.OpCode.sitofp
    let srcB := mkBitsTy nExpr
    let dstF := mkFloatTy g
    let op ← mkOpApp ctx [srcB] [dstF] (mkApp2 (Lean.mkConst ctor) nExpr (fmtConst g)) args opId
    return ← wrapLet ctx [dstF] op [(outName, dstF)] k

  if name == "fcvt" then
    arity 1
    let some dstTy ← singleResTy?
      | throwErrorAt opId "tqbe: `fcvt` requires explicit destination type"
    let srcTy ← inferArgTyFromList ctx opId args
    let f ← requireFloatFmt opId srcTy
    let g ← requireFloatFmt opId dstTy
    let srcF := mkFloatTy f
    let dstF := mkFloatTy g
    let op ← mkOpApp ctx [srcF] [dstF]
      (mkApp2 (Lean.mkConst ``LeanQbe.T.OpCode.fcvt) (fmtConst f) (fmtConst g)) args opId
    return ← wrapLet ctx [dstF] op [(outName, dstF)] k

  -- Bitcast
  if name == "bitcast" then
    arity 1
    let some dstTy ← singleResTy?
      | throwErrorAt opId "tqbe: `bitcast` requires explicit destination type (e.g. `=u128 bitcast`)"
    let srcTy ← inferArgTyFromList ctx opId args
    let h ← mkBitcastEq opId srcTy dstTy
    let op ← mkOpApp ctx [srcTy] [dstTy]
      (mkApp3 (Lean.mkConst ``LeanQbe.T.OpCode.bitcast) srcTy dstTy h) args opId
    return ← wrapLet ctx [dstTy] op [(outName, dstTy)] k

  throwErrorAt opId s!"tqbe: unknown operation `{name}`"


end LeanQbe.T.Notation
