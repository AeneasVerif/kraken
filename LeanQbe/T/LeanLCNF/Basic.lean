module

public import LeanQbe.T.IL
public meta import Lean

/-!
# Impure `LCNF` mirror and real `Lean.Compiler.LCNF.Decl .impure` extraction

`LcModule` is a `Type 0` mirror of Lean 4's final, impure LCNF (`Code .impure`,
`LetValue .impure`, `ImpureType`), read **directly** from the compiler's `impureExt`
(`getLocalImpureDecl?`), not from the legacy `Lean.IR.Decl`.

* `LcTy` mirrors `ImpureType` (`object`/`tobject`/`tagged`/`erased`/`void`/`uintN`/`usize`).
* `LcVal` mirrors `LetValue .impure` (`lit`, `erased`, `fvar` (= `ap`), `ctor`, `oproj`, `uproj`,
  `sproj`, `fap`, `pap`, `reset`, `reuse`, `box`, `unbox`, `isShared`).
* `LcCode` mirrors `Code .impure` (`let`, `jp`, `jmp`, `cases`, `return`, `unreach`, `oset`,
  `uset`, `sset`, `setTag`, `inc`, `dec`, `del`); `inc`/`dec[persistent]` are dropped exactly as
  `EmitC` drops them.
* `lcnf_of_lean! m [roots]` discovers the transitive `fap`/`pap` callees of `roots`, synthesizes
  `_boxed` wrappers of imported decls from their persisted impure signatures, records the imported
  callees as `LcExtern`s, and captures pretty-printed `.mono` and `.impure` snapshots (`LcSnap`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.LeanLCNF

/-! ## Core AST -/

/-- Mirror of `Lean.Compiler.LCNF.ImpureType`. -/
inductive LcTy where
  | object | tobject | tagged | erased | void
  | uint8 | uint16 | uint32 | uint64 | usize
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Unboxed scalar types. -/
def LcTy.isScalar : LcTy → Bool
  | .uint8 | .uint16 | .uint32 | .uint64 | .usize => true
  | _ => false

/-- Bit width of the machine representation (`64` for every object word). -/
def LcTy.width : LcTy → Nat
  | .uint8 => 8
  | .uint16 => 16
  | .uint32 => 32
  | _ => 64

/-- The `LeanQbe.T` type carrying a value of this impure type. -/
def LcTy.toTTy (t : LcTy) : Ty := .bits t.width

/-- Mirror of `Lean.Compiler.LCNF.Arg .impure`. -/
inductive LcArg where
  | erased
  | var (id : Nat)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Mirror of `LitValue` (`scalar` covers `uint8`..`usize`; the width is the binder's type). -/
inductive LcLit where
  | nat (n : Nat)
  | str (s : String)
  | scalar (n : Nat)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Mirror of `CtorInfo`. -/
structure LcCtor where
  name : String
  cidx : Nat
  size : Nat
  usize : Nat
  ssize : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A constructor without any field is a tagged scalar. -/
def LcCtor.isScalar (c : LcCtor) : Bool := c.size == 0 && c.usize == 0 && c.ssize == 0

/-- Mirror of `LetValue .impure`. -/
inductive LcVal where
  | lit (l : LcLit)
  | erased
  | ap (f : Nat) (args : List LcArg)
  | ctor (c : LcCtor) (args : List LcArg)
  | oproj (i x : Nat)
  | uproj (i x : Nat)
  | sproj (n off x : Nat)
  | fap (f : String) (args : List LcArg)
  | pap (f : String) (args : List LcArg)
  | reset (n x : Nat)
  | reuse (x : Nat) (c : LcCtor) (upd : Bool) (args : List LcArg)
  | box (ty : LcTy) (x : Nat)
  | unbox (x : Nat)
  | isShared (x : Nat)
  deriving Repr, BEq, Inhabited

/-- Function / join-point parameter. -/
structure LcParam where
  id : Nat
  ty : LcTy
  borrow : Bool := false
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A `cases` alternative pattern (`ctorAlt info` or `default`). -/
inductive LcPat where
  | ctor (cidx : Nat) (name : String)
  | dflt
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Mirror of `Code .impure`. -/
inductive LcCode where
  | let_ (x : Nat) (ty : LcTy) (v : LcVal) (k : LcCode)
  | jp (j : Nat) (ps : List LcParam) (body : LcCode) (k : LcCode)
  | jmp (j : Nat) (args : List LcArg)
  | cases (x : Nat) (alts : List (LcPat × LcCode))
  | ret (x : LcArg)
  | unreach
  | oset (x i : Nat) (y : LcArg) (k : LcCode)
  | uset (x i y : Nat) (k : LcCode)
  | sset (x n off y : Nat) (ty : LcTy) (k : LcCode)
  | setTag (x cidx : Nat) (k : LcCode)
  | inc (x n : Nat) (check : Bool) (k : LcCode)
  | dec (x n : Nat) (check : Bool) (k : LcCode)
  | del (x : Nat) (k : LcCode)
  deriving Repr, BEq, Inhabited

/-- An impure LCNF declaration with code. -/
structure LcDecl where
  name : String
  params : List LcParam
  retTy : LcTy
  body : LcCode
  deriving Repr, BEq, Inhabited

/-- An imported callee (only its persisted impure signature is available). -/
structure LcExtern where
  name : String
  params : List LcTy
  retTy : LcTy
  deriving Repr, BEq, Inhabited

/-- Stage-by-stage pretty-printed snapshots of one extracted declaration. -/
structure LcSnap where
  name : String
  mono : String
  impure : String
  deriving Repr, BEq, Inhabited

/-- A transitively closed impure LCNF program. -/
structure LcModule where
  name : String
  roots : List String
  decls : List LcDecl
  externs : List LcExtern
  snaps : List LcSnap
  deriving Repr, BEq, Inhabited

/-! ## Traversals -/

mutual
/-- `(fap targets, pap targets, max ap arity)` of a code tree. -/
def LcCode.refs : LcCode → List String × List String × Nat
  | .let_ _ _ v k =>
    let (f, p, a) := k.refs
    match v with
    | .fap g _ => (g :: f, p, a)
    | .pap g _ => (f, g :: p, a)
    | .ap _ as => (f, p, Nat.max a as.length)
    | _ => (f, p, a)
  | .jp _ _ b k =>
    let (f1, p1, a1) := b.refs
    let (f2, p2, a2) := k.refs
    (f1 ++ f2, p1 ++ p2, Nat.max a1 a2)
  | .cases _ alts => LcCode.altsRefs alts
  | .oset _ _ _ k | .uset _ _ _ k | .sset _ _ _ _ _ k | .setTag _ _ k
  | .inc _ _ _ k | .dec _ _ _ k | .del _ k => k.refs
  | .jmp _ _ | .ret _ | .unreach => ([], [], 0)

/-- `LcCode.refs` over `cases` alternatives. -/
def LcCode.altsRefs : List (LcPat × LcCode) → List String × List String × Nat
  | [] => ([], [], 0)
  | (_, b) :: rest =>
    let (f1, p1, a1) := b.refs
    let (f2, p2, a2) := LcCode.altsRefs rest
    (f1 ++ f2, p1 ++ p2, Nat.max a1 a2)
end

/-- Deduplicate preserving first occurrences. -/
def dedupStr (xs : List String) : List String :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

/-- All `pap` targets of a module (closure-table order). -/
def LcModule.papTargets (m : LcModule) : List String :=
  dedupStr (m.decls.flatMap fun d => d.body.refs.2.1)

/-- Maximum `ap` arity of a module. -/
def LcModule.maxAp (m : LcModule) : Nat :=
  m.decls.foldl (fun a d => Nat.max a d.body.refs.2.2) 0

/-- Mangle a Lean name into a C/assembly symbol (`l_` prefix, no `.L` substrings). -/
def mangleLc (s : String) : String :=
  "l_" ++ String.ofList (s.toList.map fun c => if c.isAlphanum || c == '_' then c else '_')

/-! ## Meta extraction from `impureExt` -/

meta section
open Lean Compiler LCNF

/-- Fresh-numbering state for `FVarId`s of one declaration. -/
structure XState where
  ids : Std.HashMap FVarId Nat := {}
  next : Nat := 1

/-- Extraction monad. -/
abbrev XM := StateT XState (Except String)

/-- Number an `FVarId`. -/
def xVar (f : FVarId) : XM Nat := do
  let s ← get
  match s.ids[f]? with
  | some n => pure n
  | none =>
    set { s with ids := s.ids.insert f s.next, next := s.next + 1 }
    pure s.next

/-- Convert an `ImpureType`. -/
def xTy (e : Lean.Expr) : Except String LcTy :=
  match e with
  | ImpureType.object => pure .object
  | ImpureType.tobject => pure .tobject
  | ImpureType.tagged => pure .tagged
  | ImpureType.erased => pure .erased
  | ImpureType.void => pure .void
  | ImpureType.uint8 => pure .uint8
  | ImpureType.uint16 => pure .uint16
  | ImpureType.uint32 => pure .uint32
  | ImpureType.uint64 => pure .uint64
  | ImpureType.usize => pure .usize
  | _ => throw s!"LeanLCNF: unsupported impure type {e}"

/-- Lift an `Except` into `XM`. -/
def liftX {α : Type} (x : Except String α) : XM α := StateT.lift x

/-- Convert an `Arg .impure`. -/
def xArg (a : Lean.Compiler.LCNF.Arg .impure) : XM LcArg := do
  match a with
  | .fvar f => pure (LcArg.var (← xVar f))
  | _ => pure LcArg.erased

/-- Convert a `CtorInfo`. -/
def xCtor (i : CtorInfo) : LcCtor :=
  { name := i.name.toString, cidx := i.cidx, size := i.size, usize := i.usize, ssize := i.ssize }

/-- Convert a `LitValue`. -/
def xLit : LitValue → LcLit
  | .nat n => .nat n
  | .str s => .str s
  | .uint8 v => .scalar v.toNat
  | .uint16 v => .scalar v.toNat
  | .uint32 v => .scalar v.toNat
  | .uint64 v => .scalar v.toNat
  | .usize v => .scalar v.toNat

/-- Convert a `LetValue .impure`. -/
def xVal (v : LetValue .impure) : XM LcVal := do
  match v with
  | .lit l => pure (.lit (xLit l))
  | .erased => pure .erased
  | .fvar f as => pure (.ap (← xVar f) (← as.toList.mapM xArg))
  | .ctor i as _ => pure (.ctor (xCtor i) (← as.toList.mapM xArg))
  | .oproj i x _ => pure (.oproj i (← xVar x))
  | .uproj i x _ => pure (.uproj i (← xVar x))
  | .sproj n o x _ => pure (.sproj n o (← xVar x))
  | .fap f as _ => pure (.fap f.toString (← as.toList.mapM xArg))
  | .pap f as _ => pure (.pap f.toString (← as.toList.mapM xArg))
  | .reset n x _ => pure (.reset n (← xVar x))
  | .reuse x i u as _ => pure (.reuse (← xVar x) (xCtor i) u (← as.toList.mapM xArg))
  | .box ty x _ => pure (.box (← liftX (xTy ty)) (← xVar x))
  | .unbox x _ => pure (.unbox (← xVar x))
  | .isShared x _ => pure (.isShared (← xVar x))
  | _ => liftX (throw "LeanLCNF: pure-only LetValue in impure code")

/-- Convert a `Param .impure`. -/
def xParam (p : Param .impure) : XM LcParam := do
  pure { id := ← xVar p.fvarId, ty := ← liftX (xTy p.type), borrow := p.borrow }

mutual
/-- Convert `Code .impure`. -/
partial def xCode (c : Code .impure) : XM LcCode := do
  match c with
  | .let d k =>
    let x ← xVar d.fvarId
    pure (.let_ x (← liftX (xTy d.type)) (← xVal d.value) (← xCode k))
  | .jp d k =>
    let j ← xVar d.fvarId
    let ps ← d.params.toList.mapM xParam
    pure (.jp j ps (← xCode d.value) (← xCode k))
  | .jmp f as => pure (.jmp (← xVar f) (← as.toList.mapM xArg))
  | .cases cs =>
    let x ← xVar cs.discr
    pure (.cases x (← cs.alts.toList.mapM xAlt))
  | .return f => pure (.ret (.var (← xVar f)))
  | .unreach _ => pure .unreach
  | .oset x i y k _ => pure (.oset (← xVar x) i (← xArg y) (← xCode k))
  | .uset x i y k _ => pure (.uset (← xVar x) i (← xVar y) (← xCode k))
  | .sset x i o y ty k _ =>
    pure (.sset (← xVar x) i o (← xVar y) (← liftX (xTy ty)) (← xCode k))
  | .setTag x c k _ => pure (.setTag (← xVar x) c (← xCode k))
  | .inc x n chk pers k _ =>
    if pers then xCode k else pure (.inc (← xVar x) n chk (← xCode k))
  | .dec x n chk pers _ k _ =>
    if pers then xCode k else pure (.dec (← xVar x) n chk (← xCode k))
  | .del x k _ => pure (.del (← xVar x) (← xCode k))
  | _ => liftX (throw "LeanLCNF: pure-only Code in impure decl")

/-- Convert an `Alt .impure`. -/
partial def xAlt (a : Alt .impure) : XM (LcPat × LcCode) := do
  match a with
  | .ctorAlt i k _ => pure (.ctor i.cidx i.name.toString, ← xCode k)
  | .default k => pure (.dflt, ← xCode k)
  | _ => liftX (throw "LeanLCNF: pure-only Alt in impure decl")
end

/-- Convert a real `Decl .impure` with code. -/
def xDecl (d : Decl .impure) : Except String LcDecl := do
  let body ← match d.value with
    | .code c => pure c
    | .extern _ => throw s!"LeanLCNF: '{d.name}' is extern"
  let act : XM LcDecl := do
    let ps ← d.params.toList.mapM xParam
    pure { name := d.name.toString, params := ps, retTy := ← liftX (xTy d.type),
           body := ← xCode body }
  (act.run {}).map (·.1)

/-- Meta copy of `LcTy.isScalar`. -/
def mIsScalar : LcTy → Bool
  | .uint8 | .uint16 | .uint32 | .uint64 | .usize => true
  | _ => false

/-- `ImpureType.boxed`. -/
def mBoxed : LcTy → LcTy
  | .object | .uint64 => .object
  | .void | .tagged | .uint8 | .uint16 => .tagged
  | _ => .tobject

/-- Is the boxed form of `t` a definite heap object? -/
def mBoxedIsObj : LcTy → Bool
  | .uint64 => true
  | _ => false

mutual
/-- Meta collection of `fap`/`pap` targets. -/
partial def mRefs : LcCode → List String
  | .let_ _ _ (.fap g _) k | .let_ _ _ (.pap g _) k => g :: mRefs k
  | .let_ _ _ _ k => mRefs k
  | .jp _ _ b k => mRefs b ++ mRefs k
  | .cases _ alts => mAltsRefs alts
  | .oset _ _ _ k | .uset _ _ _ k | .sset _ _ _ _ _ k | .setTag _ _ k
  | .inc _ _ _ k | .dec _ _ _ k | .del _ k => mRefs k
  | .jmp _ _ | .ret _ | .unreach => []

/-- `mRefs` over alternatives. -/
partial def mAltsRefs : List (LcPat × LcCode) → List String
  | [] => []
  | (_, b) :: rest => mRefs b ++ mAltsRefs rest
end

/-- Synthesize `X._boxed` from the persisted impure signature of an imported `X`
(mirrors `ExplicitBoxing.mkBoxedVersion` + `ExplicitRC`'s decs of borrowed params). -/
def synthBoxed (sig : Signature .impure) : Except String LcDecl := do
  let ps ← sig.params.toList.mapM fun p => do pure (← xTy p.type, p.borrow)
  let rTy ← xTy sig.type
  let n := ps.length
  let params := (List.range n).zip ps |>.map fun (i, (t, _)) =>
    ({ id := i + 1, ty := mBoxed t } : LcParam)
  -- ids: params 1..n, unboxed n+1..2n, result 2n+1, boxed result 2n+2
  let args := (List.range n).zip ps |>.map fun (i, (t, _)) =>
    if mIsScalar t then LcArg.var (n + 1 + i) else LcArg.var (i + 1)
  let res := 2 * n + 1
  let tail : LcCode :=
    if mIsScalar rTy then .let_ (res + 1) (mBoxed rTy) (.box rTy res) (.ret (.var (res + 1)))
    else .ret (.var res)
  let decs := (List.range n).zip ps |>.foldr (fun (i, (t, b)) acc =>
    if mBoxedIsObj t then .dec (i + 1) 1 true acc
    else if b && !mIsScalar t then .dec (i + 1) 1 true acc else acc) tail
  let call : LcCode := .let_ res rTy (.fap sig.name.toString args) decs
  let body := (List.range n).zip ps |>.foldr (fun (i, (t, _)) acc =>
    if mIsScalar t then .let_ (n + 1 + i) t (.unbox (i + 1)) acc else acc) call
  pure { name := (mkBoxedName sig.name).toString, params, retTy := mBoxed rTy, body }

/-! ### `Expr` encoders -/

/-- `List` literal. -/
def eList (ty : Lean.Expr) (xs : List Lean.Expr) : Lean.Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [.zero]) ty x acc)
    (mkApp (mkConst ``List.nil [.zero]) ty)

/-- Pair literal. -/
def ePair (a b : Lean.Expr) (x y : Lean.Expr) : Lean.Expr :=
  mkApp4 (mkConst ``Prod.mk [.zero, .zero]) a b x y

def eTy (t : LcTy) : Lean.Expr :=
  mkConst <| match t with
    | .object => ``LcTy.object | .tobject => ``LcTy.tobject | .tagged => ``LcTy.tagged
    | .erased => ``LcTy.erased | .void => ``LcTy.void | .uint8 => ``LcTy.uint8
    | .uint16 => ``LcTy.uint16 | .uint32 => ``LcTy.uint32 | .uint64 => ``LcTy.uint64
    | .usize => ``LcTy.usize

def eArg : LcArg → Lean.Expr
  | .erased => mkConst ``LcArg.erased
  | .var i => mkApp (mkConst ``LcArg.var) (mkNatLit i)

def eArgs (as : List LcArg) : Lean.Expr := eList (mkConst ``LcArg) (as.map eArg)

def eLit : LcLit → Lean.Expr
  | .nat n => mkApp (mkConst ``LcLit.nat) (mkNatLit n)
  | .str s => mkApp (mkConst ``LcLit.str) (mkStrLit s)
  | .scalar n => mkApp (mkConst ``LcLit.scalar) (mkNatLit n)

def eCtor (c : LcCtor) : Lean.Expr :=
  mkAppN (mkConst ``LcCtor.mk) #[mkStrLit c.name, mkNatLit c.cidx, mkNatLit c.size,
    mkNatLit c.usize, mkNatLit c.ssize]

def eVal : LcVal → Lean.Expr
  | .lit l => mkApp (mkConst ``LcVal.lit) (eLit l)
  | .erased => mkConst ``LcVal.erased
  | .ap f as => mkApp2 (mkConst ``LcVal.ap) (mkNatLit f) (eArgs as)
  | .ctor c as => mkApp2 (mkConst ``LcVal.ctor) (eCtor c) (eArgs as)
  | .oproj i x => mkApp2 (mkConst ``LcVal.oproj) (mkNatLit i) (mkNatLit x)
  | .uproj i x => mkApp2 (mkConst ``LcVal.uproj) (mkNatLit i) (mkNatLit x)
  | .sproj n o x => mkApp3 (mkConst ``LcVal.sproj) (mkNatLit n) (mkNatLit o) (mkNatLit x)
  | .fap f as => mkApp2 (mkConst ``LcVal.fap) (mkStrLit f) (eArgs as)
  | .pap f as => mkApp2 (mkConst ``LcVal.pap) (mkStrLit f) (eArgs as)
  | .reset n x => mkApp2 (mkConst ``LcVal.reset) (mkNatLit n) (mkNatLit x)
  | .reuse x c u as =>
    mkApp4 (mkConst ``LcVal.reuse) (mkNatLit x) (eCtor c) (toExpr u) (eArgs as)
  | .box t x => mkApp2 (mkConst ``LcVal.box) (eTy t) (mkNatLit x)
  | .unbox x => mkApp (mkConst ``LcVal.unbox) (mkNatLit x)
  | .isShared x => mkApp (mkConst ``LcVal.isShared) (mkNatLit x)

def eParam (p : LcParam) : Lean.Expr :=
  mkApp3 (mkConst ``LcParam.mk) (mkNatLit p.id) (eTy p.ty) (toExpr p.borrow)

def ePat : LcPat → Lean.Expr
  | .ctor i n => mkApp2 (mkConst ``LcPat.ctor) (mkNatLit i) (mkStrLit n)
  | .dflt => mkConst ``LcPat.dflt

partial def eCode : LcCode → Lean.Expr
  | .let_ x t v k => mkApp4 (mkConst ``LcCode.let_) (mkNatLit x) (eTy t) (eVal v) (eCode k)
  | .jp j ps b k => mkApp4 (mkConst ``LcCode.jp) (mkNatLit j)
    (eList (mkConst ``LcParam) (ps.map eParam)) (eCode b) (eCode k)
  | .jmp j as => mkApp2 (mkConst ``LcCode.jmp) (mkNatLit j) (eArgs as)
  | .cases x alts =>
    let pt := mkConst ``LcPat
    let ct := mkConst ``LcCode
    let pr := mkApp2 (mkConst ``Prod [.zero, .zero]) pt ct
    mkApp2 (mkConst ``LcCode.cases) (mkNatLit x)
      (eList pr (alts.map fun (p, b) => ePair pt ct (ePat p) (eCode b)))
  | .ret a => mkApp (mkConst ``LcCode.ret) (eArg a)
  | .unreach => mkConst ``LcCode.unreach
  | .oset x i y k => mkApp4 (mkConst ``LcCode.oset) (mkNatLit x) (mkNatLit i) (eArg y) (eCode k)
  | .uset x i y k =>
    mkApp4 (mkConst ``LcCode.uset) (mkNatLit x) (mkNatLit i) (mkNatLit y) (eCode k)
  | .sset x n o y t k => mkAppN (mkConst ``LcCode.sset)
    #[mkNatLit x, mkNatLit n, mkNatLit o, mkNatLit y, eTy t, eCode k]
  | .setTag x c k => mkApp3 (mkConst ``LcCode.setTag) (mkNatLit x) (mkNatLit c) (eCode k)
  | .inc x n c k =>
    mkApp4 (mkConst ``LcCode.inc) (mkNatLit x) (mkNatLit n) (toExpr c) (eCode k)
  | .dec x n c k =>
    mkApp4 (mkConst ``LcCode.dec) (mkNatLit x) (mkNatLit n) (toExpr c) (eCode k)
  | .del x k => mkApp2 (mkConst ``LcCode.del) (mkNatLit x) (eCode k)

def eDecl (d : LcDecl) : Lean.Expr :=
  mkApp4 (mkConst ``LcDecl.mk) (mkStrLit d.name)
    (eList (mkConst ``LcParam) (d.params.map eParam)) (eTy d.retTy) (eCode d.body)

def eExtern (e : LcExtern) : Lean.Expr :=
  mkApp3 (mkConst ``LcExtern.mk) (mkStrLit e.name)
    (eList (mkConst ``LcTy) (e.params.map eTy)) (eTy e.retTy)

def eSnap (s : LcSnap) : Lean.Expr :=
  mkApp3 (mkConst ``LcSnap.mk) (mkStrLit s.name) (mkStrLit s.mono) (mkStrLit s.impure)

/-! ### Transitive discovery -/

/-- Read a transitively closed `LcModule` rooted at `roots` from the current environment. -/
partial def readLcModule (modName : String) (roots : List Name) : CoreM LcModule := do
  let mut queue := roots
  let mut seen : NameSet := {}
  let mut decls : Array LcDecl := #[]
  let mut exts : Array LcExtern := #[]
  let mut snaps : Array LcSnap := #[]
  while true do
    match queue with
    | [] => break
    | nm :: rest =>
      queue := rest
      if seen.contains nm then continue
      seen := seen.insert nm
      let mut found : Option LcDecl := none
      if let some d ← getLocalImpureDecl? nm then
        match xDecl d with
        | .ok ld => found := some ld
        | .error e => throwError e
        let imp := toString (← ppDecl' d .impure)
        let mono ← match ← getMonoDecl? nm with
          | some m => pure (toString (← ppDecl' m .mono))
          | none => pure ""
        snaps := snaps.push { name := nm.toString, mono, impure := imp }
      else if let .str base "_boxed" := nm then
        if let some sig ← getImpureSignature? base then
          match synthBoxed sig with
          | .ok ld => found := some ld
          | .error e => throwError e
      match found with
      | some ld =>
        decls := decls.push ld
        for c in mRefs ld.body do
          let cn := c.toName
          if !seen.contains cn then queue := queue ++ [cn]
      | none =>
        match ← getImpureSignature? nm with
        | some sig =>
          let ps ← sig.params.toList.mapM fun p => ofExcept (xTy p.type)
          let rTy ← ofExcept (xTy sig.type)
          exts := exts.push { name := nm.toString, params := ps, retTy := rTy }
        | none => throwError m!"LeanLCNF: no impure LCNF decl or signature for '{nm}'"
  pure { name := modName, roots := roots.map (·.toString), decls := decls.toList,
         externs := exts.toList, snaps := snaps.toList }

open Elab Command in
/-- Add a closed, exposed, compiled definition `nm : ty := val`. -/
def addLcConst (nm : Name) (ty val : Lean.Expr) : CoreM Unit := do
  let decl := .defnDecl {
    name := nm, levelParams := [], type := ty, value := val
    hints := .regular 0, safety := .safe }
  addDecl decl (forceExpose := true)
  compileDecl decl

open Elab Command in
/-- `lcnf_of_lean! m [f, g, ...]` defines `m : LcModule` from the real impure LCNF of the given
roots (and their transitive `fap`/`pap` callees); every declaration and snapshot becomes its own
auxiliary constant `m.d<i>` / `m.s<i>` so that no single term is deeply nested. -/
elab "lcnf_of_lean! " modId:ident "[" roots:ident,* "]" : command => do
  let ns ← getCurrNamespace
  let rs ← liftTermElabM <| roots.getElems.toList.mapM fun r =>
    Lean.resolveGlobalConstNoOverload r.raw
  let fullNm := ns ++ modId.getId
  let m ← liftCoreM <| readLcModule modId.getId.toString rs
  liftCoreM do
    let mut dNames : Array Lean.Expr := #[]
    for (d, i) in m.decls.zip (List.range m.decls.length) do
      let nm := fullNm.str s!"d{i}"
      addLcConst nm (mkConst ``LcDecl) (eDecl d)
      dNames := dNames.push (mkConst nm)
    let mut sNames : Array Lean.Expr := #[]
    for (s, i) in m.snaps.zip (List.range m.snaps.length) do
      let nm := fullNm.str s!"s{i}"
      addLcConst nm (mkConst ``LcSnap) (eSnap s)
      sNames := sNames.push (mkConst nm)
    let strT := mkConst ``String
    let val := mkAppN (mkConst ``LcModule.mk) #[mkStrLit m.name,
      eList strT (m.roots.map mkStrLit), eList (mkConst ``LcDecl) dNames.toList,
      eList (mkConst ``LcExtern) (m.externs.map eExtern), eList (mkConst ``LcSnap) sNames.toList]
    addLcConst fullNm (mkConst ``LcModule) val
    enableRealizationsForConst fullNm

end

end LeanQbe.T.LeanLCNF
