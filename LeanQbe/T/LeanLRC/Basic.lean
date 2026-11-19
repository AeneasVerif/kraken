module

public import LeanQbe.T.IL
public meta import Lean

/-!
# `λRC` / `Lean.IR` Representation & `Lean.IR.Decl` Reader (`X3-R0`)

Minimal typed `λRC` / `Lean.IR` intermediate representation (`LrcVal`, `LrcExpr`, `LrcFn`,
`LrcModule`) covering constructor allocation/projection (`ctor`, `proj`, `uproj`, `sproj`),
tagging/RC (`box`, `unbox`, `inc`, `dec`, `del`), reset/reuse (`reset`, `reuse`, `isShared`,
`set`, `setTag`, `uset`, `sset`), control flow (`case`, `jdecl`, `jmp`, `ret`, `unreachable`),
calls/closures (`fap`, `pap`, `ap`), and scalar primitives (`scalar`), plus a `meta` reader
lowering real `Lean.IR.Decl` entries from `Lean.IR.findEnvDecl` / `Lean.IR.declMapExt`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.LeanLRC

open LeanQbe.T

/-! ## Core `λRC` AST (`Type 0`) -/

/-- Minimal `λRC` / `Lean.IR` type classification. -/
inductive LrcTy where
  | object | tobject | tagged | erased | void
  | uint8 | uint16 | uint32 | uint64 | usize
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Map `LrcTy` to typed target-independent IR type `LeanQbe.T.Ty`. -/
def LrcTy.toTTy : LrcTy → Ty
  | .uint8 => i8
  | .uint16 => i16
  | .uint32 => i32
  | .uint64 | .usize | .object | .tobject | .tagged | .erased | .void => i64

/-- True iff `t` is an unboxed scalar integer type in `Lean.IR`. -/
def LrcTy.isScalar : LrcTy → Bool
  | .uint8 | .uint16 | .uint32 | .uint64 | .usize => true
  | _ => false

/-- True iff `t` is an object or tagged-pointer word. -/
def LrcTy.isObj : LrcTy → Bool
  | .object | .tobject | .tagged | .erased | .void => true
  | _ => false

/-- Bit width of `LrcTy` (64 for object/tagged words). -/
def LrcTy.bitWidth : LrcTy → Nat
  | .uint8 => 8
  | .uint16 => 16
  | .uint32 => 32
  | _ => 64

/-- Literal value in `λRC`. -/
inductive LrcVal where
  | num (v : Nat)
  | str (v : String)
  | bool (b : Bool)
  | erased
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Operand argument in `λRC`. -/
inductive LrcArg where
  | var (id : Nat)
  | val (v : LrcVal)
  | erased
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Pure scalar primitive opcodes in `λRC`. -/
inductive LrcScalarOp where
  | add | sub | mul | udiv | urem
  | and | or | xor | shl | lshr | ashr
  | eq | ne | ult | ule | slt | sle
  | not | neg
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Constructor layout descriptor mirroring `Lean.IR.CtorInfo`. -/
structure LrcCtorInfo where
  name : String
  cidx : Nat
  size : Nat
  usize : Nat
  ssize : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

/-- True iff `info` has zero heap fields (represented as tagged scalar / enum). -/
def LrcCtorInfo.isScalar (info : LrcCtorInfo) : Bool :=
  info.size == 0 && info.usize == 0 && info.ssize == 0

/-- Function / join-point parameter descriptor. -/
structure LrcParam where
  id : Nat
  borrow : Bool := false
  ty : LrcTy := .tobject
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Pure/allocating RHS of a `vdecl` binding in `λRC`. -/
inductive LrcRhs where
  | ctor (info : LrcCtorInfo) (args : List LrcArg)
  | reset (n : Nat) (x : Nat)
  | reuse (x : Nat) (info : LrcCtorInfo) (updtHeader : Bool) (args : List LrcArg)
  | proj (i : Nat) (x : Nat)
  | uproj (i : Nat) (x : Nat)
  | sproj (n offset : Nat) (x : Nat)
  | fap (fn : String) (args : List LrcArg)
  | pap (fn : String) (args : List LrcArg)
  | ap (fnVar : Nat) (args : List LrcArg)
  | box (ty : LrcTy) (x : Nat)
  | unbox (x : Nat)
  | lit (v : LrcVal)
  | isShared (x : Nat)
  | scalar (op : LrcScalarOp) (args : List LrcArg)
  | copy (a : LrcArg)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Case alternative pattern in `λRC`. -/
inductive LrcAltPat where
  | ctor (info : LrcCtorInfo)
  | default
  deriving Repr, BEq, DecidableEq, Inhabited

/-- `λRC` function body statement/terminator tree. -/
inductive LrcExpr where
  | vdecl (x : Nat) (ty : LrcTy) (rhs : LrcRhs) (rest : LrcExpr)
  | jdecl (jp : Nat) (params : List LrcParam) (val : LrcExpr) (rest : LrcExpr)
  | set (x i : Nat) (y : LrcArg) (rest : LrcExpr)
  | setTag (x cidx : Nat) (rest : LrcExpr)
  | uset (x i y : Nat) (rest : LrcExpr)
  | sset (x i offset y : Nat) (ty : LrcTy) (rest : LrcExpr)
  | inc (x n : Nat) (checkRef persistent : Bool) (rest : LrcExpr)
  | dec (x n : Nat) (checkRef persistent : Bool) (rest : LrcExpr)
  | del (x : Nat) (rest : LrcExpr)
  | case (tid : String) (x : Nat) (xTy : LrcTy) (alts : List (LrcAltPat × LrcExpr))
  | ret (x : LrcArg)
  | jmp (jp : Nat) (args : List LrcArg)
  | unreachable
  deriving Repr, BEq, Inhabited

/-- A named `λRC` function declaration. -/
structure LrcFn where
  name : String
  params : List LrcParam
  retTy : LrcTy := .tobject
  body : LrcExpr
  deriving Repr, BEq, Inhabited

/-- An external C/runtime declaration referenced by `λRC`. -/
structure LrcExtern where
  name : String
  cName : String
  params : List LrcTy
  retTy : LrcTy
  deriving Repr, BEq, Inhabited

/-- A defunctionalized closure dispatch entry (`fun_id`, target symbol, arity excluding `rt`). -/
structure LrcClosureTarget where
  funId : Nat
  fnName : String
  arity : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A complete `λRC` module. -/
structure LrcModule where
  name : String
  fns : List LrcFn
  externs : List LrcExtern := []
  deriving Repr, BEq, Inhabited

/-! ## Analysis Helpers: Symbol Mangling, Closure Collection, and SCC Analysis -/

/-- Sanitize a `λRC`/Lean symbol name into a C/QBE/gas identifier with no `.L` substrings. -/
def mangleSym (s : String) : String :=
  let cleaned := String.ofList <| s.toList.map fun c =>
    if c.isAlphanum || c == '_' then c else '_'
  if cleaned.isEmpty then "lrc_empty"
  else if (cleaned.toList.head?.map (fun c => c.isDigit || c == '_')).getD false then
    "lrc_" ++ cleaned
  else cleaned

mutual
/-- Collect all `fap`, `pap`, and `ap` arities referenced in an `LrcExpr`. -/
partial def collectRhsRefs (rhs : LrcRhs) : List String × List String × Nat :=
  match rhs with
  | .fap f _ => ([f], [], 0)
  | .pap f _ => ([], [f], 0)
  | .ap _ args => ([], [], args.length)
  | _ => ([], [], 0)

/-- Collect `(fapSyms, papSyms, maxApArity)` across an `LrcExpr`. -/
partial def LrcExpr.collectRefs : LrcExpr → List String × List String × Nat
  | .vdecl _ _ rhs rest =>
    let (f1, p1, a1) := collectRhsRefs rhs
    let (f2, p2, a2) := rest.collectRefs
    (f1 ++ f2, p1 ++ p2, Nat.max a1 a2)
  | .jdecl _ _ v rest =>
    let (f1, p1, a1) := v.collectRefs
    let (f2, p2, a2) := rest.collectRefs
    (f1 ++ f2, p1 ++ p2, Nat.max a1 a2)
  | .set _ _ _ rest | .setTag _ _ rest | .uset _ _ _ rest | .sset _ _ _ _ _ rest
  | .inc _ _ _ _ rest | .dec _ _ _ _ rest | .del _ rest => rest.collectRefs
  | .case _ _ _ alts =>
    alts.foldl (fun (fs, ps, mx) (_, b) =>
      let (f1, p1, a1) := b.collectRefs
      (fs ++ f1, ps ++ p1, Nat.max mx a1)) ([], [], 0)
  | .ret _ | .jmp _ _ | .unreachable => ([], [], 0)
end

/-- Deduplicate a list of strings preserving first occurrence order. -/
def dedupStrings (xs : List String) : List String :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

/-- Extract the defunctionalized closure table for `m` from all `pap` expressions. -/
def LrcModule.closureTargets (m : LrcModule) : Except String (List LrcClosureTarget) := do
  let rawPaps := dedupStrings <| m.fns.flatMap fun fn => fn.body.collectRefs.2.1
  let mut idx := 0
  let mut out : List LrcClosureTarget := []
  for p in rawPaps do
    match m.fns.find? (fun f => f.name == p) with
    | some fn =>
      out := out ++ [{ funId := idx, fnName := mangleSym fn.name, arity := fn.params.length }]
      idx := idx + 1
    | none => throw s!"LrcModule.closureTargets: unknown pap target '{p}'"
  pure out

/-- Maximum `ap` argument arity appearing in `m` (minimum 1 if any `pap`/`ap` exists). -/
def LrcModule.maxApArity (m : LrcModule) : Nat :=
  let mx := m.fns.foldl (fun acc fn => Nat.max acc fn.body.collectRefs.2.2) 0
  let hasPap := m.fns.any (fun fn => !fn.body.collectRefs.2.1.isEmpty)
  if hasPap && mx == 0 then 1 else mx

/-- Compute strongly connected components (SCCs) of `m.fns` call graph (including `ap -> pap`). -/
def LrcModule.sccs (m : LrcModule) : List (List String) :=
  let nodes := m.fns.map (·.name)
  let papNames := dedupStrings <| m.fns.flatMap fun fn => fn.body.collectRefs.2.1
  let adj (nm : String) : List String :=
    match m.fns.find? (fun f => f.name == nm) with
    | none => []
    | some fn =>
      let (faps, _, apMax) := fn.body.collectRefs
      let apEdges := if apMax > 0 then papNames else []
      dedupStrings ((faps ++ apEdges).filter (nodes.contains ·))
  let revAdj (nm : String) : List String :=
    nodes.filter fun u => (adj u).contains nm
  let rec dfs1 : Nat → List String → String → List String → List String × List String
    | 0, vis, _, ord => (vis, ord)
    | fuel + 1, visited, u, order =>
      if visited.contains u then (visited, order)
      else
        let (vis', ord') := (adj u).foldl (fun (v, o) w =>
          if v.contains w then (v, o) else dfs1 fuel v w o) (u :: visited, order)
        (vis', u :: ord')
  let (_, postOrder) := nodes.foldl (fun (v, o) u =>
    if v.contains u then (v, o) else dfs1 (nodes.length + 1) v u o) ([], [])
  let rec dfs2 : Nat → List String → String → List String → List String × List String
    | 0, vis, _, comp => (vis, comp)
    | fuel + 1, visited, u, comp =>
      if visited.contains u then (visited, comp)
      else
        (revAdj u).foldl (fun (v, c) w =>
          if v.contains w then (v, c) else dfs2 fuel v w c) (u :: visited, u :: comp)
  let (_, comps) := postOrder.foldl (fun (vis, acc) u =>
    if vis.contains u then (vis, acc)
    else
      let (vis', comp) := dfs2 (nodes.length + 1) vis u []
      (vis', acc ++ [comp])) ([], [])
  comps

/-! ## Meta `Lean.IR.Decl` Reader (`Lean.IR.findEnvDecl` / `Lean.IR.declMapExt`) -/

meta section
open Lean Elab Command

/-- Meta `ToExpr` instances for splicing real `Lean.IR.Decl` into pure kernel `LrcModule`s. -/
def metaListExpr (tyE : Lean.Expr) (xs : List Lean.Expr) : Lean.Expr :=
  xs.foldr (fun x acc => Lean.mkApp3 (Lean.mkConst ``List.cons [.zero]) tyE x acc)
    (Lean.mkApp (Lean.mkConst ``List.nil [.zero]) tyE)

def tyToMetaExpr : LrcTy → Lean.Expr
  | .object => Lean.mkConst ``LrcTy.object
  | .tobject => Lean.mkConst ``LrcTy.tobject
  | .tagged => Lean.mkConst ``LrcTy.tagged
  | .erased => Lean.mkConst ``LrcTy.erased
  | .void => Lean.mkConst ``LrcTy.void
  | .uint8 => Lean.mkConst ``LrcTy.uint8
  | .uint16 => Lean.mkConst ``LrcTy.uint16
  | .uint32 => Lean.mkConst ``LrcTy.uint32
  | .uint64 => Lean.mkConst ``LrcTy.uint64
  | .usize => Lean.mkConst ``LrcTy.usize

def valToMetaExpr : LrcVal → Lean.Expr
  | .num n => Lean.mkApp (Lean.mkConst ``LrcVal.num) (Lean.mkNatLit n)
  | .str s => Lean.mkApp (Lean.mkConst ``LrcVal.str) (Lean.mkStrLit s)
  | .bool b => Lean.mkApp (Lean.mkConst ``LrcVal.bool) (Lean.toExpr b)
  | .erased => Lean.mkConst ``LrcVal.erased

def argToMetaExpr : LrcArg → Lean.Expr
  | .var id => Lean.mkApp (Lean.mkConst ``LrcArg.var) (Lean.mkNatLit id)
  | .val v => Lean.mkApp (Lean.mkConst ``LrcArg.val) (valToMetaExpr v)
  | .erased => Lean.mkConst ``LrcArg.erased

def scalarOpToMetaExpr : LrcScalarOp → Lean.Expr
  | .add => Lean.mkConst ``LrcScalarOp.add | .sub => Lean.mkConst ``LrcScalarOp.sub
  | .mul => Lean.mkConst ``LrcScalarOp.mul | .udiv => Lean.mkConst ``LrcScalarOp.udiv
  | .urem => Lean.mkConst ``LrcScalarOp.urem | .and => Lean.mkConst ``LrcScalarOp.and
  | .or => Lean.mkConst ``LrcScalarOp.or | .xor => Lean.mkConst ``LrcScalarOp.xor
  | .shl => Lean.mkConst ``LrcScalarOp.shl | .lshr => Lean.mkConst ``LrcScalarOp.lshr
  | .ashr => Lean.mkConst ``LrcScalarOp.ashr | .eq => Lean.mkConst ``LrcScalarOp.eq
  | .ne => Lean.mkConst ``LrcScalarOp.ne | .ult => Lean.mkConst ``LrcScalarOp.ult
  | .ule => Lean.mkConst ``LrcScalarOp.ule | .slt => Lean.mkConst ``LrcScalarOp.slt
  | .sle => Lean.mkConst ``LrcScalarOp.sle | .not => Lean.mkConst ``LrcScalarOp.not
  | .neg => Lean.mkConst ``LrcScalarOp.neg

def ctorInfoToMetaExpr (i : LrcCtorInfo) : Lean.Expr :=
  Lean.mkAppN (Lean.mkConst ``LrcCtorInfo.mk)
    #[Lean.mkStrLit i.name, Lean.mkNatLit i.cidx, Lean.mkNatLit i.size,
      Lean.mkNatLit i.usize, Lean.mkNatLit i.ssize]

def paramToMetaExpr (p : LrcParam) : Lean.Expr :=
  Lean.mkApp3 (Lean.mkConst ``LrcParam.mk)
    (Lean.mkNatLit p.id) (Lean.toExpr p.borrow) (tyToMetaExpr p.ty)

def rhsToMetaExpr : LrcRhs → Lean.Expr
  | .ctor i as => Lean.mkApp2 (Lean.mkConst ``LrcRhs.ctor)
    (ctorInfoToMetaExpr i) (metaListExpr (Lean.mkConst ``LrcArg) (as.map argToMetaExpr))
  | .reset n x => Lean.mkApp2 (Lean.mkConst ``LrcRhs.reset) (Lean.mkNatLit n) (Lean.mkNatLit x)
  | .reuse x i u as => Lean.mkApp4 (Lean.mkConst ``LrcRhs.reuse) (Lean.mkNatLit x)
    (ctorInfoToMetaExpr i) (Lean.toExpr u)
    (metaListExpr (Lean.mkConst ``LrcArg) (as.map argToMetaExpr))
  | .proj i x => Lean.mkApp2 (Lean.mkConst ``LrcRhs.proj) (Lean.mkNatLit i) (Lean.mkNatLit x)
  | .uproj i x => Lean.mkApp2 (Lean.mkConst ``LrcRhs.uproj) (Lean.mkNatLit i) (Lean.mkNatLit x)
  | .sproj n o x => Lean.mkApp3 (Lean.mkConst ``LrcRhs.sproj)
    (Lean.mkNatLit n) (Lean.mkNatLit o) (Lean.mkNatLit x)
  | .fap f as => Lean.mkApp2 (Lean.mkConst ``LrcRhs.fap)
    (Lean.mkStrLit f) (metaListExpr (Lean.mkConst ``LrcArg) (as.map argToMetaExpr))
  | .pap f as => Lean.mkApp2 (Lean.mkConst ``LrcRhs.pap)
    (Lean.mkStrLit f) (metaListExpr (Lean.mkConst ``LrcArg) (as.map argToMetaExpr))
  | .ap x as => Lean.mkApp2 (Lean.mkConst ``LrcRhs.ap)
    (Lean.mkNatLit x) (metaListExpr (Lean.mkConst ``LrcArg) (as.map argToMetaExpr))
  | .box ty x => Lean.mkApp2 (Lean.mkConst ``LrcRhs.box) (tyToMetaExpr ty) (Lean.mkNatLit x)
  | .unbox x => Lean.mkApp (Lean.mkConst ``LrcRhs.unbox) (Lean.mkNatLit x)
  | .lit v => Lean.mkApp (Lean.mkConst ``LrcRhs.lit) (valToMetaExpr v)
  | .isShared x => Lean.mkApp (Lean.mkConst ``LrcRhs.isShared) (Lean.mkNatLit x)
  | .scalar op as => Lean.mkApp2 (Lean.mkConst ``LrcRhs.scalar)
    (scalarOpToMetaExpr op) (metaListExpr (Lean.mkConst ``LrcArg) (as.map argToMetaExpr))
  | .copy a => Lean.mkApp (Lean.mkConst ``LrcRhs.copy) (argToMetaExpr a)

def altPatToMetaExpr : LrcAltPat → Lean.Expr
  | .ctor i => Lean.mkApp (Lean.mkConst ``LrcAltPat.ctor) (ctorInfoToMetaExpr i)
  | .default => Lean.mkConst ``LrcAltPat.default

partial def exprToMetaExpr : LrcExpr → Lean.Expr
  | .vdecl x ty rhs rest => Lean.mkApp4 (Lean.mkConst ``LrcExpr.vdecl)
    (Lean.mkNatLit x) (tyToMetaExpr ty) (rhsToMetaExpr rhs) (exprToMetaExpr rest)
  | .jdecl jp ps v rest => Lean.mkApp4 (Lean.mkConst ``LrcExpr.jdecl) (Lean.mkNatLit jp)
    (metaListExpr (Lean.mkConst ``LrcParam) (ps.map paramToMetaExpr))
    (exprToMetaExpr v) (exprToMetaExpr rest)
  | .set x i y rest => Lean.mkApp4 (Lean.mkConst ``LrcExpr.set)
    (Lean.mkNatLit x) (Lean.mkNatLit i) (argToMetaExpr y) (exprToMetaExpr rest)
  | .setTag x c rest => Lean.mkApp3 (Lean.mkConst ``LrcExpr.setTag)
    (Lean.mkNatLit x) (Lean.mkNatLit c) (exprToMetaExpr rest)
  | .uset x i y rest => Lean.mkApp4 (Lean.mkConst ``LrcExpr.uset)
    (Lean.mkNatLit x) (Lean.mkNatLit i) (Lean.mkNatLit y) (exprToMetaExpr rest)
  | .sset x i o y ty rest => Lean.mkApp6 (Lean.mkConst ``LrcExpr.sset)
    (Lean.mkNatLit x) (Lean.mkNatLit i) (Lean.mkNatLit o) (Lean.mkNatLit y)
    (tyToMetaExpr ty) (exprToMetaExpr rest)
  | .inc x n c p rest => Lean.mkApp5 (Lean.mkConst ``LrcExpr.inc)
    (Lean.mkNatLit x) (Lean.mkNatLit n) (Lean.toExpr c) (Lean.toExpr p) (exprToMetaExpr rest)
  | .dec x n c p rest => Lean.mkApp5 (Lean.mkConst ``LrcExpr.dec)
    (Lean.mkNatLit x) (Lean.mkNatLit n) (Lean.toExpr c) (Lean.toExpr p) (exprToMetaExpr rest)
  | .del x rest => Lean.mkApp2 (Lean.mkConst ``LrcExpr.del)
    (Lean.mkNatLit x) (exprToMetaExpr rest)
  | .case tid x xTy alts =>
    let pairTy := Lean.mkApp2 (Lean.mkConst ``Prod [.zero, .zero])
      (Lean.mkConst ``LrcAltPat) (Lean.mkConst ``LrcExpr)
    let altsE := metaListExpr pairTy <| alts.map fun (pat, b) =>
      Lean.mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero])
        (Lean.mkConst ``LrcAltPat) (Lean.mkConst ``LrcExpr)
        (altPatToMetaExpr pat) (exprToMetaExpr b)
    Lean.mkApp4 (Lean.mkConst ``LrcExpr.case)
      (Lean.mkStrLit tid) (Lean.mkNatLit x) (tyToMetaExpr xTy) altsE
  | .ret x => Lean.mkApp (Lean.mkConst ``LrcExpr.ret) (argToMetaExpr x)
  | .jmp jp as => Lean.mkApp2 (Lean.mkConst ``LrcExpr.jmp)
    (Lean.mkNatLit jp) (metaListExpr (Lean.mkConst ``LrcArg) (as.map argToMetaExpr))
  | .unreachable => Lean.mkConst ``LrcExpr.unreachable

def fnToMetaExpr (f : LrcFn) : Lean.Expr :=
  Lean.mkApp4 (Lean.mkConst ``LrcFn.mk) (Lean.mkStrLit f.name)
    (metaListExpr (Lean.mkConst ``LrcParam) (f.params.map paramToMetaExpr))
    (tyToMetaExpr f.retTy) (exprToMetaExpr f.body)

def externToMetaExpr (ex : LrcExtern) : Lean.Expr :=
  Lean.mkApp4 (Lean.mkConst ``LrcExtern.mk) (Lean.mkStrLit ex.name) (Lean.mkStrLit ex.cName)
    (metaListExpr (Lean.mkConst ``LrcTy) (ex.params.map tyToMetaExpr)) (tyToMetaExpr ex.retTy)

def moduleToMetaExpr (m : LrcModule) : Lean.Expr :=
  Lean.mkApp3 (Lean.mkConst ``LrcModule.mk) (Lean.mkStrLit m.name)
    (metaListExpr (Lean.mkConst ``LrcFn) (m.fns.map fnToMetaExpr))
    (metaListExpr (Lean.mkConst ``LrcExtern) (m.externs.map externToMetaExpr))

/-- Convert `Lean.IR.IRType` to `LrcTy`. -/
def irTyToLrc : Lean.IR.IRType → Except String LrcTy
  | .object => pure .object
  | .tobject => pure .tobject
  | .tagged => pure .tagged
  | .erased => pure .erased
  | .void => pure .void
  | .uint8 => pure .uint8
  | .uint16 => pure .uint16
  | .uint32 => pure .uint32
  | .uint64 => pure .uint64
  | .usize => pure .usize
  | t => throw s!"LeanLRC: unsupported Lean.IR.IRType {repr t}"

/-- Convert `Lean.IR.CtorInfo` to `LrcCtorInfo`. -/
def irCtorToLrc (info : Lean.IR.CtorInfo) : LrcCtorInfo :=
  { name := info.name.toString
    cidx := info.cidx
    size := info.size
    usize := info.usize
    ssize := info.ssize }

/-- Convert `Lean.IR.Arg` to `LrcArg`. -/
def irArgToLrc : Lean.IR.Arg → LrcArg
  | .var v => .var v.idx
  | .erased => .erased

/-- Convert `Lean.IR.LitVal` to `LrcVal`. -/
def irLitToLrc : Lean.IR.LitVal → LrcVal
  | .num n => .num n
  | .str s => .str s

/-- Convert `Lean.IR.Param` to `LrcParam`. -/
def irParamToLrc (p : Lean.IR.Param) : Except String LrcParam := do
  pure { id := p.x.idx, borrow := p.borrow, ty := ← irTyToLrc p.ty }

/-- Convert `Lean.IR.Expr` to `LrcRhs`. -/
def irExprToLrc : Lean.IR.Expr → Except String LrcRhs
  | .ctor i ys => pure (.ctor (irCtorToLrc i) (ys.toList.map irArgToLrc))
  | .reset n x => pure (.reset n x.idx)
  | .reuse x i u ys => pure (.reuse x.idx (irCtorToLrc i) u (ys.toList.map irArgToLrc))
  | .proj i x => pure (.proj i x.idx)
  | .uproj i x => pure (.uproj i x.idx)
  | .sproj n o x => pure (.sproj n o x.idx)
  | .fap c ys => pure (.fap c.toString (ys.toList.map irArgToLrc))
  | .pap c ys => pure (.pap c.toString (ys.toList.map irArgToLrc))
  | .ap x ys => pure (.ap x.idx (ys.toList.map irArgToLrc))
  | .box ty x => do pure (.box (← irTyToLrc ty) x.idx)
  | .unbox x => pure (.unbox x.idx)
  | .lit v => pure (.lit (irLitToLrc v))
  | .isShared x => pure (.isShared x.idx)

mutual
/-- Convert `Lean.IR.FnBody` to `LrcExpr`. -/
partial def irFnBodyToLrc : Lean.IR.FnBody → Except String LrcExpr
  | .vdecl x ty e b => do
    pure (.vdecl x.idx (← irTyToLrc ty) (← irExprToLrc e) (← irFnBodyToLrc b))
  | .jdecl j xs v b => do
    let ps ← xs.toList.mapM irParamToLrc
    pure (.jdecl j.idx ps (← irFnBodyToLrc v) (← irFnBodyToLrc b))
  | .set x i y b => do pure (.set x.idx i (irArgToLrc y) (← irFnBodyToLrc b))
  | .setTag x c b => do pure (.setTag x.idx c (← irFnBodyToLrc b))
  | .uset x i y b => do pure (.uset x.idx i y.idx (← irFnBodyToLrc b))
  | .sset x i o y ty b => do
    pure (.sset x.idx i o y.idx (← irTyToLrc ty) (← irFnBodyToLrc b))
  | .inc x n c p b => do pure (.inc x.idx n c p (← irFnBodyToLrc b))
  | .dec x n c p b => do pure (.dec x.idx n c p (← irFnBodyToLrc b))
  | .del x b => do pure (.del x.idx (← irFnBodyToLrc b))
  | .case tid x xTy alts => do
    let lAlts ← alts.toList.mapM irAltToLrc
    pure (.case tid.toString x.idx (← irTyToLrc xTy) lAlts)
  | .ret x => pure (.ret (irArgToLrc x))
  | .jmp j ys => pure (.jmp j.idx (ys.toList.map irArgToLrc))
  | .unreachable => pure .unreachable

/-- Convert `Lean.IR.Alt` to `LrcAltPat × LrcExpr`. -/
partial def irAltToLrc : Lean.IR.Alt → Except String (LrcAltPat × LrcExpr)
  | .ctor info b => do pure (.ctor (irCtorToLrc info), ← irFnBodyToLrc b)
  | .default b => do pure (.default, ← irFnBodyToLrc b)
end

/-- Sanitize a `λRC` / Lean symbol name in meta context. -/
def metaMangleSym (s : String) : String :=
  let cleaned := String.ofList <| s.toList.map fun c =>
    if c.isAlphanum || c == '_' then c else '_'
  if cleaned.isEmpty then "lrc_empty"
  else if (cleaned.toList.head?.map (fun c => c.isDigit || c == '_')).getD false then
    "lrc_" ++ cleaned
  else cleaned

/-- Convert a `Lean.IR.Decl` into `LrcFn` (or `Sum LrcFn LrcExtern`). -/
def irDeclToLrc : Lean.IR.Decl → Except String (Sum LrcFn LrcExtern)
  | .fdecl f xs ty body _ => do
    let ps ← xs.toList.mapM irParamToLrc
    let rTy ← irTyToLrc ty
    let lBody ← irFnBodyToLrc body
    pure (.inl { name := f.toString, params := ps, retTy := rTy, body := lBody })
  | .extern f xs ty extData => do
    let ps ← xs.toList.mapM (fun p => irTyToLrc p.ty)
    let rTy ← irTyToLrc ty
    let cName := match Lean.getExternEntryFor extData `c with
      | some (.standard _ s) => s
      | _ => metaMangleSym f.toString
    pure (.inr { name := f.toString, cName, params := ps, retTy := rTy })

/-- Look up a `Lean.IR.Decl` by `Name` using `findEnvDecl` and local `declMapExt`. -/
def lookupLeanIRDecl (env : Environment) (nm : Name) : Option Lean.IR.Decl :=
  Lean.IR.findEnvDecl env nm <|> (Lean.IR.declMapExt.getState env |>.find? nm)

/-- Collect referenced `fap` and `pap` names in meta context. -/
partial def metaCollectRefs : LrcExpr → List String
  | .vdecl _ _ (.fap f _) rest | .vdecl _ _ (.pap f _) rest => f :: metaCollectRefs rest
  | .vdecl _ _ _ rest => metaCollectRefs rest
  | .jdecl _ _ v rest => metaCollectRefs v ++ metaCollectRefs rest
  | .set _ _ _ rest | .setTag _ _ rest | .uset _ _ _ rest | .sset _ _ _ _ _ rest
  | .inc _ _ _ _ rest | .dec _ _ _ _ rest | .del _ rest => metaCollectRefs rest
  | .case _ _ _ alts => alts.flatMap (fun (_, b) => metaCollectRefs b)
  | .ret _ | .jmp _ _ | .unreachable => []

/-- Read a single Lean 4 declaration from the environment into `LrcFn`. -/
def readLeanIRFn (env : Environment) (nm : Name) : Except String LrcFn := do
  match lookupLeanIRDecl env nm with
  | none => throw s!"LeanLRC: no Lean.IR.Decl found for '{nm}'"
  | some d =>
    match ← irDeclToLrc d with
    | .inl fn => pure fn
    | .inr ex => throw s!"LeanLRC: '{nm}' is extern ('{ex.cName}'), not an IR definition"

/-- Read a transitive closure of `Lean.IR.Decl`s rooted at `roots` into an `LrcModule`. -/
partial def readLeanIRModule (env : Environment) (roots : List Name) (modName : String) :
    Except String LrcModule := do
  let mut queue : List Name := roots
  let mut visited : NameSet := {}
  let mut fns : List LrcFn := []
  let mut exts : List LrcExtern := []
  while !queue.isEmpty do
    match queue with
    | [] => break
    | nm :: rest =>
      queue := rest
      if visited.contains nm then continue
      visited := visited.insert nm
      match lookupLeanIRDecl env nm with
      | none => throw s!"LeanLRC: missing Lean.IR.Decl for '{nm}'"
      | some d =>
        match ← irDeclToLrc d with
        | .inr ex => exts := exts ++ [ex]
        | .inl fn =>
          fns := fns ++ [fn]
          for calleeStr in metaCollectRefs fn.body do
            let cName := String.toName calleeStr
            if !visited.contains cName then
              queue := queue ++ [cName]
  pure { name := modName, fns := fns.reverse, externs := exts }

/-- Elaborate a pure kernel `def <modIdent> : LrcModule` from real Lean 4 definitions in `env`. -/
elab "lrc_of_lean! " modIdent:ident "[" roots:ident,* "]" : command => do
  let env ← getEnv
  let ns ← getCurrNamespace
  let resolvedRoots ← liftTermElabM <| roots.getElems.toList.mapM fun id =>
    Lean.resolveGlobalConstNoOverload id.raw
  let mod ← match readLeanIRModule env resolvedRoots modIdent.getId.toString with
    | .ok m => pure m
    | .error err => throwError err
  let modExpr := moduleToMetaExpr mod
  let fullNm := ns ++ modIdent.getId
  liftCoreM <| do
    let decl := .defnDecl {
      name := fullNm
      levelParams := []
      type := Lean.mkConst ``LrcModule
      value := modExpr
      hints := .regular 0
      safety := .safe
    }
    addDecl decl (forceExpose := true)
    compileDecl decl
    enableRealizationsForConst fullNm

/-- Elaborate a pure kernel `def <fnIdent> : LrcFn` from a single Lean 4 definition. -/
elab "lrc_fn_of_lean! " fnIdent:ident root:ident : command => do
  let env ← getEnv
  let ns ← getCurrNamespace
  let resolved ← liftTermElabM <| Lean.resolveGlobalConstNoOverload root.raw
  let fn ← match readLeanIRFn env resolved with
    | .ok f => pure f
    | .error err => throwError err
  let fnExpr := fnToMetaExpr fn
  let fullNm := ns ++ fnIdent.getId
  liftCoreM <| do
    let decl := .defnDecl {
      name := fullNm
      levelParams := []
      type := Lean.mkConst ``LrcFn
      value := fnExpr
      hints := .regular 0
      safety := .safe
    }
    addDecl decl (forceExpose := true)
    compileDecl decl
    enableRealizationsForConst fullNm

end

end LeanQbe.T.LeanLRC
