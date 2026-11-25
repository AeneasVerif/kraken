module

/-!
# C0 Abstract Syntax Tree

Untyped surface AST for the C99-subset C0 language,
supporting fixed-width scalars, pointers, structs (with LSB-first bitfields, fixed arrays,
and optional trailing flexible arrays), tagged-word unions,
multi-return tuples (`C0_RET2`/`C0_RET3`),
`static inline` and external functions, structured loops, forward `goto`, non-fallthrough `switch`,
`c0_assume`, `check`, and `assert`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Frontend.C0

mutual
  /-- Surface C0 types. -/
  inductive C0Type : Type
    | void
    | bool
    | int (signed : Bool) (bits : Nat)
    | f64
    | ptr (elem : C0Type)
    | array (elem : C0Type) (len : Option Nat)
    | structRef (name : String)
    | unionRef (name : String)
    | typedefRef (name : String)
    | anonAggregate (isUnion : Bool) (fields : List FieldDecl)
    | tuple (elems : List C0Type)
    deriving Repr, BEq, Inhabited

  /-- A field inside a `struct` or `union`, optionally a bitfield `: width`. -/
  structure FieldDecl : Type where
    name : Option String
    ty : C0Type
    bitWidth : Option Nat := none
    deriving Repr, BEq, Inhabited
end

@[reducible] def C0Type.u8 : C0Type := .int false 8
@[reducible] def C0Type.u16 : C0Type := .int false 16
@[reducible] def C0Type.u32 : C0Type := .int false 32
@[reducible] def C0Type.u64 : C0Type := .int false 64
@[reducible] def C0Type.i8 : C0Type := .int true 8
@[reducible] def C0Type.i16 : C0Type := .int true 16
@[reducible] def C0Type.i32 : C0Type := .int true 32
@[reducible] def C0Type.i64 : C0Type := .int true 64

/-- Integer literal suffix in C99. -/
inductive IntSuffix : Type
  | none | u | l | ul | ll | ull
  deriving Repr, BEq, Inhabited

/-- Unary operators. -/
inductive UnaryOp : Type
  | neg | pos | bitnot | lognot | deref | addrOf
  deriving Repr, BEq, Inhabited

/-- Binary operators. -/
inductive BinOp : Type
  | add | sub | mul | div | mod
  | bitand | bitor | bitxor | shl | shr
  | eq | ne | lt | le | gt | ge
  | logand | logor
  deriving Repr, BEq, Inhabited

/-- Surface C0 expressions (pure except short-circuiting and calls). -/
inductive Expr : Type
  | intLit (val : Int) (suffix : IntSuffix := .none) (isDecimal : Bool := true)
  | floatLit (bits : UInt64)
  | boolLit (b : Bool)
  | null
  | var (name : String)
  | cast (ty : C0Type) (e : Expr)
  | sizeofTy (ty : C0Type)
  | sizeofExpr (e : Expr)
  | offsetof (ty : C0Type) (fld : String)
  | unary (op : UnaryOp) (e : Expr)
  | binary (op : BinOp) (lhs rhs : Expr)
  | ternary (cond thn els : Expr)
  | field (e : Expr) (fld : String)
  | arrow (e : Expr) (fld : String)
  | index (arr idx : Expr)
  | call (fn : String) (args : List Expr)
  deriving Repr, BEq, Inhabited

/-- Assignable lvalues (locals or memory locations). -/
inductive LVal : Type
  | var (name : String)
  | deref (ptr : Expr)
  | arrow (ptr : Expr) (fld : String)
  | index (arr idx : Expr)
  | dot (base : LVal) (fld : String)
  deriving Repr, BEq, Inhabited

/-- Local variable initializer (`= expr` or `= {0}`). -/
inductive InitVal : Type
  | expr (e : Expr)
  | zeroInit
  deriving Repr, BEq, Inhabited

mutual
  /-- An ordered `switch` arm (`case`/`default` labels + body; falls through unless exited). -/
  structure SwitchArm : Type where
    vals : List Int
    hasDefault : Bool := false
    body : List Stmt
    deriving Repr, BEq, Inhabited

  /-- Surface C0 statements. -/
  inductive Stmt : Type
    | empty
    | block (stmts : List Stmt)
    | decl (ty : C0Type) (name : String) (init : InitVal)
    | assign (lhs : LVal) (op : Option BinOp) (rhs : Expr)
    | incDec (lhs : LVal) (isInc : Bool)
    | callStmt (lhs : List String) (fn : String) (args : List Expr)
    | ifStmt (cond : Expr) (thn : Stmt) (els : Option Stmt)
    | whileStmt (cond : Expr) (body : Stmt)
    | doWhileStmt (body : Stmt) (cond : Expr)
    | forStmt (init : Option Stmt) (cond : Option Expr) (step : Option Stmt) (body : Stmt)
    | switchStmt (scrut : Expr) (arms : List SwitchArm)
    | breakStmt
    | continueStmt
    | retStmt (vals : List Expr)
    | gotoStmt (label : String)
    | labelStmt (label : String) (stmt : Stmt)
    | assumeStmt (cond : Expr)
    | checkStmt (cond : Expr) (line : Nat)
    | assertStmt (cond : Expr) (line : Nat)
    | staticAssertStmt (cond : Expr) (msg : String)
    deriving Repr, BEq, Inhabited
end

/-- Named `struct` or `union` definition. -/
structure StructDecl : Type where
  name : String
  isUnion : Bool
  fields : List FieldDecl
  deriving Repr, BEq, Inhabited

/-- Function signature (prototype / extern declaration). -/
structure FnSig : Type where
  retTy : C0Type
  name : String
  params : List (C0Type × Option String)
  deriving Repr, BEq, Inhabited

/-- Pragmas supported by C0: upstream provenance, fidelity tag, extension tag,
or bounded loop justification. -/
inductive C0Pragma : Type
  | upstream (loc : String) (fnName : Option String := none)
  | fidelity
  | extension
  | bounded (reason : String)
  deriving Repr, BEq, Inhabited

/-- Function definition. -/
structure FnDef : Type where
  isStatic : Bool := false
  isInline : Bool := false
  retTy : C0Type
  name : String
  params : List (C0Type × String)
  body : List Stmt
  upstreamLoc : Option String := none
  upstreamFn : Option String := none
  isFidelity : Bool := false
  isExtension : Bool := false
  boundedReasons : List String := []
  boundedLoops : List (Nat × String) := []
  deriving Repr, BEq, Inhabited

/-- Top-level C0 declaration. -/
inductive Decl : Type
  | typedef (name : String) (ty : C0Type)
  | structDef (sd : StructDecl)
  | fnDecl (sig : FnSig)
  | fnDef (fn : FnDef)
  | enumConsts (items : List (String × Int))
  | staticAssert (cond : Expr) (msg : String)
  | pragma (p : C0Pragma)
  deriving Repr, BEq, Inhabited

/-- Parsed C0 translation unit. -/
structure TranslationUnit : Type where
  decls : List Decl
  deriving Repr, BEq, Inhabited

def evalConstBitOp (op : BinOp) (va vb : Int) : Int :=
  if va >= 0 && vb >= 0 then
    match op with
    | .bitand => Int.ofNat (Nat.land va.toNat vb.toNat)
    | .bitor => Int.ofNat (Nat.lor va.toNat vb.toNat)
    | _ => Int.ofNat (Nat.xor va.toNat vb.toNat)
  else
    let ba := BitVec.ofInt 64 va
    let bb := BitVec.ofInt 64 vb
    match op with
    | .bitand => (ba &&& bb).toInt
    | .bitor => (ba ||| bb).toInt
    | _ => (ba ^^^ bb).toInt

/-- Evaluate a binary operator on compile-time integer constant values. -/
def evalConstBinOp (op : BinOp) (va vb : Int) : Except String Int :=
  match op with
  | .add => pure (va + vb)
  | .sub => pure (va - vb)
  | .mul => pure (va * vb)
  | .div =>
    if vb == 0 then throw "division by zero in constant expression"
    else pure (va / vb)
  | .mod =>
    if vb == 0 then throw "modulo by zero in constant expression"
    else pure (va % vb)
  | .shl =>
    if vb < 0 then throw "negative shift in constant expression"
    else pure (va * Int.ofNat (2 ^ vb.toNat))
  | .shr =>
    if vb < 0 then throw "negative shift in constant expression"
    else pure (va / Int.ofNat (2 ^ vb.toNat))
  | .bitand | .bitor | .bitxor => pure (evalConstBitOp op va vb)
  | .eq => pure (if va == vb then 1 else 0)
  | .ne => pure (if va != vb then 1 else 0)
  | .lt => pure (if va < vb then 1 else 0)
  | .le => pure (if va <= vb then 1 else 0)
  | .gt => pure (if va > vb then 1 else 0)
  | .ge => pure (if va >= vb then 1 else 0)
  | .logand => pure (if va != 0 && vb != 0 then 1 else 0)
  | .logor => pure (if va != 0 || vb != 0 then 1 else 0)

/-- Shared integer constant-expression evaluator parameterized by constant lookup and
layout-dependent leaf evaluation (`sizeof`, `offsetof`). -/
partial def evalConstIntWith (lookupConst : String → Option Int)
    (onSpecial : Expr → Except String Int) : Expr → Except String Int
  | .intLit v _ _ => pure v
  | .boolLit b => pure (if b then 1 else 0)
  | .var nm => match lookupConst nm with
    | some v => pure v
    | none => throw s!"unknown constant '{nm}' in integer constant expression"
  | .cast _ e => evalConstIntWith lookupConst onSpecial e
  | .unary .neg e => do pure (-(← evalConstIntWith lookupConst onSpecial e))
  | .unary .pos e => evalConstIntWith lookupConst onSpecial e
  | .unary .bitnot e => do
    let v ← evalConstIntWith lookupConst onSpecial e
    pure (-(v + 1))
  | .unary .lognot e => do
    let v ← evalConstIntWith lookupConst onSpecial e
    pure (if v == 0 then 1 else 0)
  | .binary op a b => do
    let va ← evalConstIntWith lookupConst onSpecial a
    let vb ← evalConstIntWith lookupConst onSpecial b
    evalConstBinOp op va vb
  | .ternary c t e => do
    let vc ← evalConstIntWith lookupConst onSpecial c
    if vc != 0 then evalConstIntWith lookupConst onSpecial t
    else evalConstIntWith lookupConst onSpecial e
  | e => onSpecial e

end LeanQbe.T.Frontend.C0
