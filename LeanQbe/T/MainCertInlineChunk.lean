module

public import LeanQbe.T.MainCertInline
public import LeanQbe.T.InlineChunk
public meta import Lean
public meta import LeanQbe.T.MainCertInline
public meta import LeanQbe.T.InlineChunk

/-!
# Chunked `inline_mod!` Materializers (`MainCertInlineChunk`)

Splits `Module.optInlinePolicy` materialization and kernel equality checking across small
independent modules (`<= 80` fns per chunk) so peak RAM stays well below `8 GB`:

* `inline_chunk_base! baseId srcMod policy`: materializes `siteCounts` / `loopCounts` and
  proves `(srcMod.optInlinePolicy policy).fns = inlRest ... 0 [] []`.
* `inline_mod_chunk! chunkId baseId srcMod policy startIdx count [(prev := ...)] [(isLast := ...)]`:
  materializes ONLY the `count` functions in `[startIdx, startIdx + count)` as `denoteFunc`-backed
  `Fn` defs, normalizes ONLY the new `cands` added in this slice via `normPhoasFn` (preserving
  definitional equality `rfl` without `denoteFunc`), and proves `step_eq` / `last_eq` over ONLY
  that slice.
* `inline_mod_join! modId fnsId srcMod policy baseId [c0, c1, ...]`: joins chunk function lists in
  `O(#chunks)` (`Eq.trans` / `inlRest_prepend_eq`) with zero kernel AST reduction, exporting
  `modId`, `fnsId`, `modId.fns_eq`, and `modId.eq`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

meta section

open Lean Elab Command Meta

private def mkListLit (u : Level) (ty : Lean.Expr) (elems : List Lean.Expr) : Lean.Expr :=
  elems.foldr
    (fun x acc => mkApp3 (Lean.mkConst ``List.cons [u]) ty x acc)
    (mkApp (Lean.mkConst ``List.nil [u]) ty)

private def listTyToExpr (ts : List Ty) : Lean.Expr :=
  mkListLit .zero (Lean.mkConst ``LeanQbe.T.Ty) (ts.map tyToExpr)

private def listListTyToExpr (tss : List (List Ty)) : Lean.Expr :=
  let listTy := mkApp (Lean.mkConst ``List [.zero]) (Lean.mkConst ``LeanQbe.T.Ty)
  mkListLit .zero listTy (tss.map listTyToExpr)

private def cmpOpToExpr : CmpOp → Lean.Expr
  | .eq => Lean.mkConst ``LeanQbe.T.CmpOp.eq
  | .ne => Lean.mkConst ``LeanQbe.T.CmpOp.ne
  | .ult => Lean.mkConst ``LeanQbe.T.CmpOp.ult
  | .ule => Lean.mkConst ``LeanQbe.T.CmpOp.ule
  | .ugt => Lean.mkConst ``LeanQbe.T.CmpOp.ugt
  | .uge => Lean.mkConst ``LeanQbe.T.CmpOp.uge
  | .slt => Lean.mkConst ``LeanQbe.T.CmpOp.slt
  | .sle => Lean.mkConst ``LeanQbe.T.CmpOp.sle
  | .sgt => Lean.mkConst ``LeanQbe.T.CmpOp.sgt
  | .sge => Lean.mkConst ``LeanQbe.T.CmpOp.sge

private def fcmpOpToExpr : FCmpOp → Lean.Expr
  | .eq => Lean.mkConst ``LeanQbe.T.FCmpOp.eq
  | .ne => Lean.mkConst ``LeanQbe.T.FCmpOp.ne
  | .lt => Lean.mkConst ``LeanQbe.T.FCmpOp.lt
  | .le => Lean.mkConst ``LeanQbe.T.FCmpOp.le
  | .gt => Lean.mkConst ``LeanQbe.T.FCmpOp.gt
  | .ge => Lean.mkConst ``LeanQbe.T.FCmpOp.ge
  | .ord => Lean.mkConst ``LeanQbe.T.FCmpOp.ord
  | .uno => Lean.mkConst ``LeanQbe.T.FCmpOp.uno

private def valToExpr : (t : Ty) → Val t → Lean.Expr
  | .bool, v => Lean.toExpr (v : Bool)
  | .bits n, v => @Lean.toExpr (BitVec n) _ v
  | .float f, v => @Lean.toExpr (BitVec f.width) _ v
  | .pair a b, v =>
    let ta := mkApp (Lean.mkConst ``LeanQbe.T.Val) (tyToExpr a)
    let tb := mkApp (Lean.mkConst ``LeanQbe.T.Val) (tyToExpr b)
    mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero]) ta tb (valToExpr a v.1) (valToExpr b v.2)

private def argKToExpr (t : Ty) : Arg K t → Lean.Expr
  | .var idx =>
    mkApp3 (Lean.mkConst ``LeanQbe.T.Arg.var) (Lean.mkConst ``LeanQbe.T.K)
      (tyToExpr t) (mkNatLit idx)
  | .imm c =>
    mkApp3 (Lean.mkConst ``LeanQbe.T.Arg.imm) (Lean.mkConst ``LeanQbe.T.K)
      (tyToExpr t) (valToExpr t c)

private def tupArgKToExpr : (ts : List Ty) → Tup (Arg K) ts → Lean.Expr
  | [], () => Lean.mkConst ``Unit.unit
  | t :: ts, (a, as) =>
    let kE := Lean.mkConst ``LeanQbe.T.K
    let ta := mkApp2 (Lean.mkConst ``LeanQbe.T.Arg) kE (tyToExpr t)
    let tb := mkApp3 (Lean.mkConst ``LeanQbe.T.Tup) (Lean.mkConst ``LeanQbe.T.Ty)
      (mkApp (Lean.mkConst ``LeanQbe.T.Arg) kE) (listTyToExpr ts)
    mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero]) ta tb (argKToExpr t a) (tupArgKToExpr ts as)

private def mkTyOpExpr (nm : Name) (t : Ty) : Lean.Expr :=
  mkApp (Lean.mkConst nm) (tyToExpr t)

private def mkNatOpExpr (nm : Name) (n : Nat) : Lean.Expr :=
  mkApp (Lean.mkConst nm) (mkNatLit n)

private def mkTyImmOpExpr (nm : Name) (t : Ty) (imm : BitVec 8) : Lean.Expr :=
  mkApp2 (Lean.mkConst nm) (tyToExpr t) (Lean.toExpr imm)

private def opCodeToExpr {sig rs : List Ty} : OpCode sig rs → Lean.Expr
  | .copy t => mkTyOpExpr ``LeanQbe.T.OpCode.copy t
  | .add t => mkTyOpExpr ``LeanQbe.T.OpCode.add t
  | .sub t => mkTyOpExpr ``LeanQbe.T.OpCode.sub t
  | .mul t => mkTyOpExpr ``LeanQbe.T.OpCode.mul t
  | .neg t => mkTyOpExpr ``LeanQbe.T.OpCode.neg t
  | .and t => mkTyOpExpr ``LeanQbe.T.OpCode.and t
  | .or t => mkTyOpExpr ``LeanQbe.T.OpCode.or t
  | .xor t => mkTyOpExpr ``LeanQbe.T.OpCode.xor t
  | .not t => mkTyOpExpr ``LeanQbe.T.OpCode.not t
  | .ternlog t imm => mkTyImmOpExpr ``LeanQbe.T.OpCode.ternlog t imm
  | .shl t => mkTyOpExpr ``LeanQbe.T.OpCode.shl t
  | .lshr t => mkTyOpExpr ``LeanQbe.T.OpCode.lshr t
  | .ashr t => mkTyOpExpr ``LeanQbe.T.OpCode.ashr t
  | .rotl t => mkTyOpExpr ``LeanQbe.T.OpCode.rotl t
  | .rotr t => mkTyOpExpr ``LeanQbe.T.OpCode.rotr t
  | .fshl n => mkNatOpExpr ``LeanQbe.T.OpCode.fshl n
  | .fshr n => mkNatOpExpr ``LeanQbe.T.OpCode.fshr n
  | .bswap t => mkTyOpExpr ``LeanQbe.T.OpCode.bswap t
  | .clz n => mkNatOpExpr ``LeanQbe.T.OpCode.clz n
  | .cls n => mkNatOpExpr ``LeanQbe.T.OpCode.cls n
  | .rbit n => mkNatOpExpr ``LeanQbe.T.OpCode.rbit n
  | .ctz n => mkNatOpExpr ``LeanQbe.T.OpCode.ctz n
  | .popcnt n => mkNatOpExpr ``LeanQbe.T.OpCode.popcnt n
  | .cmp o t m _ =>
    let me := tyToExpr m
    mkApp4 (Lean.mkConst ``LeanQbe.T.OpCode.cmp) (cmpOpToExpr o) (tyToExpr t) me
      (mkApp2 (Lean.mkConst ``Eq.refl [.one]) (Lean.mkConst ``LeanQbe.T.Ty) me)
  | .select t => mkTyOpExpr ``LeanQbe.T.OpCode.select t
  | .blend t m _ =>
    let me := tyToExpr m
    mkApp3 (Lean.mkConst ``LeanQbe.T.OpCode.blend) (tyToExpr t) me
      (mkApp2 (Lean.mkConst ``Eq.refl [.one]) (Lean.mkConst ``LeanQbe.T.Ty) me)
  | .zext m n => mkApp2 (Lean.mkConst ``LeanQbe.T.OpCode.zext) (mkNatLit m) (mkNatLit n)
  | .sext m n => mkApp2 (Lean.mkConst ``LeanQbe.T.OpCode.sext) (mkNatLit m) (mkNatLit n)
  | .trunc m n => mkApp2 (Lean.mkConst ``LeanQbe.T.OpCode.trunc) (mkNatLit m) (mkNatLit n)
  | .ofBool n => mkNatOpExpr ``LeanQbe.T.OpCode.ofBool n
  | .addc n => mkNatOpExpr ``LeanQbe.T.OpCode.addc n
  | .subb n => mkNatOpExpr ``LeanQbe.T.OpCode.subb n
  | .umulw n => mkNatOpExpr ``LeanQbe.T.OpCode.umulw n
  | .smulw n => mkNatOpExpr ``LeanQbe.T.OpCode.smulw n
  | .udiv n => mkNatOpExpr ``LeanQbe.T.OpCode.udiv n
  | .sdiv n => mkNatOpExpr ``LeanQbe.T.OpCode.sdiv n
  | .urem n => mkNatOpExpr ``LeanQbe.T.OpCode.urem n
  | .srem n => mkNatOpExpr ``LeanQbe.T.OpCode.srem n
  | .udiv0 n => mkNatOpExpr ``LeanQbe.T.OpCode.udiv0 n
  | .sdiv0 n => mkNatOpExpr ``LeanQbe.T.OpCode.sdiv0 n
  | .mkpair a b => mkApp2 (Lean.mkConst ``LeanQbe.T.OpCode.mkpair) (tyToExpr a) (tyToExpr b)
  | .unpair a b => mkApp2 (Lean.mkConst ``LeanQbe.T.OpCode.unpair) (tyToExpr a) (tyToExpr b)
  | .bitcast t u _ =>
    mkApp3 (Lean.mkConst ``LeanQbe.T.OpCode.bitcast) (tyToExpr t) (tyToExpr u)
      (mkApp2 (Lean.mkConst ``Eq.refl [.one]) (Lean.mkConst ``Nat) (mkNatLit t.size))
  | .shufd t imm => mkTyImmOpExpr ``LeanQbe.T.OpCode.shufd t imm
  | .shufb t => mkTyOpExpr ``LeanQbe.T.OpCode.shufb t
  | .alignr t imm => mkTyImmOpExpr ``LeanQbe.T.OpCode.alignr t imm
  | .blendw t imm => mkTyImmOpExpr ``LeanQbe.T.OpCode.blendw t imm
  | .sha256rnds2 => Lean.mkConst ``LeanQbe.T.OpCode.sha256rnds2
  | .sha256msg1 => Lean.mkConst ``LeanQbe.T.OpCode.sha256msg1
  | .sha256msg2 => Lean.mkConst ``LeanQbe.T.OpCode.sha256msg2
  | .fadd t => mkTyOpExpr ``LeanQbe.T.OpCode.fadd t
  | .fsub t => mkTyOpExpr ``LeanQbe.T.OpCode.fsub t
  | .fmul t => mkTyOpExpr ``LeanQbe.T.OpCode.fmul t
  | .fdiv t => mkTyOpExpr ``LeanQbe.T.OpCode.fdiv t
  | .ffma t => mkTyOpExpr ``LeanQbe.T.OpCode.ffma t
  | .fsqrt t => mkTyOpExpr ``LeanQbe.T.OpCode.fsqrt t
  | .fneg t => mkTyOpExpr ``LeanQbe.T.OpCode.fneg t
  | .fabs t => mkTyOpExpr ``LeanQbe.T.OpCode.fabs t
  | .fcmp o t m _ =>
    let me := tyToExpr m
    mkApp4 (Lean.mkConst ``LeanQbe.T.OpCode.fcmp) (fcmpOpToExpr o) (tyToExpr t) me
      (mkApp2 (Lean.mkConst ``Eq.refl [.one]) (Lean.mkConst ``LeanQbe.T.Ty) me)
  | .fptoui f n => mkApp2 (Lean.mkConst ``LeanQbe.T.OpCode.fptoui) (Lean.toExpr f) (mkNatLit n)
  | .fptosi f n => mkApp2 (Lean.mkConst ``LeanQbe.T.OpCode.fptosi) (Lean.toExpr f) (mkNatLit n)
  | .uitofp n f => mkApp2 (Lean.mkConst ``LeanQbe.T.OpCode.uitofp) (mkNatLit n) (Lean.toExpr f)
  | .sitofp n f => mkApp2 (Lean.mkConst ``LeanQbe.T.OpCode.sitofp) (mkNatLit n) (Lean.toExpr f)
  | .fcvt f g => mkApp2 (Lean.mkConst ``LeanQbe.T.OpCode.fcvt) (Lean.toExpr f) (Lean.toExpr g)

private def opKToExpr {rs : List Ty} (op : Op K rs) : Lean.Expr :=
  mkApp5 (Lean.mkConst ``LeanQbe.T.Op.mk) (Lean.mkConst ``LeanQbe.T.K)
    (listTyToExpr rs) (listTyToExpr op.sig) (opCodeToExpr op.code) (tupArgKToExpr op.sig op.args)

mutual
private def tflatToExpr (rs : List Ty) : TFlat rs → Lean.Expr
  | .let_ (ts := ts) op k =>
    mkApp4 (Lean.mkConst ``LeanQbe.T.TFlat.let_) (listTyToExpr rs) (listTyToExpr ts)
      (opKToExpr op) (tflatToExpr rs k)
  | .load t a k =>
    mkApp4 (Lean.mkConst ``LeanQbe.T.TFlat.load) (listTyToExpr rs) (tyToExpr t)
      (argKToExpr i64 a) (tflatToExpr rs k)
  | .store (t := t) v a k =>
    mkApp5 (Lean.mkConst ``LeanQbe.T.TFlat.store) (listTyToExpr rs) (tyToExpr t)
      (argKToExpr t v) (argKToExpr i64 a) (tflatToExpr rs k)
  | .call f (as := as) bs args k =>
    mkApp6 (Lean.mkConst ``LeanQbe.T.TFlat.call) (listTyToExpr rs) (Lean.toExpr f)
      (listTyToExpr as) (listTyToExpr bs) (tupArgKToExpr as args) (tflatToExpr rs k)
  | .jnz c t e =>
    mkApp4 (Lean.mkConst ``LeanQbe.T.TFlat.jnz) (listTyToExpr rs) (argKToExpr .bool c)
      (tflatToExpr rs t) (tflatToExpr rs e)
  | .jump (ts := ts) j args =>
    mkApp4 (Lean.mkConst ``LeanQbe.T.TFlat.jump) (listTyToExpr rs) (listTyToExpr ts)
      (mkNatLit j) (tupArgKToExpr ts args)
  | .ret vs =>
    mkApp2 (Lean.mkConst ``LeanQbe.T.TFlat.ret) (listTyToExpr rs) (tupArgKToExpr rs vs)
  | .exit f (as := as) args =>
    mkApp4 (Lean.mkConst ``LeanQbe.T.TFlat.exit) (listTyToExpr rs) (Lean.toExpr f)
      (listTyToExpr as) (tupArgKToExpr as args)
  | .hlt => mkApp (Lean.mkConst ``LeanQbe.T.TFlat.hlt) (listTyToExpr rs)
  | .group (sig := sig) bodies k =>
    mkApp4 (Lean.mkConst ``LeanQbe.T.TFlat.group) (listTyToExpr rs) (listListTyToExpr sig)
      (tblocksToExpr rs bodies) (tflatToExpr rs k)

private def tblocksToExpr (rs : List Ty) :
    {sig : List (List Ty)} → TBlocks rs sig → Lean.Expr
  | _, .nil => mkApp (Lean.mkConst ``LeanQbe.T.TBlocks.nil) (listTyToExpr rs)
  | _, .cons (ts := ts) (sig := sig') b bs =>
    mkApp5 (Lean.mkConst ``LeanQbe.T.TBlocks.cons) (listTyToExpr rs) (listTyToExpr ts)
      (listListTyToExpr sig') (tflatToExpr rs b) (tblocksToExpr rs bs)
end

private def matFnToExpr (f : MatFnData) : Lean.Expr :=
  let asE := listTyToExpr f.as
  let rsE := listTyToExpr f.rs
  let bodyE := mkApp3 (Lean.mkConst ``LeanQbe.T.denoteFunc) asE rsE (tflatToExpr f.rs f.flat)
  mkApp4 (Lean.mkConst ``LeanQbe.T.Fn.mk) (Lean.toExpr f.name) asE rsE bodyE

private def sigEntryToExpr (s : SigEntry) : Lean.Expr :=
  let listTy := mkApp (Lean.mkConst ``List [.zero]) (Lean.mkConst ``LeanQbe.T.Ty)
  let pairTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) listTy listTy
  let p := mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero]) listTy listTy
    (listTyToExpr s.2.1) (listTyToExpr s.2.2)
  mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero]) (Lean.mkConst ``LeanQbe.T.Sym) pairTy
    (Lean.toExpr s.1) p

private def listSigToExpr (ss : List SigEntry) : Lean.Expr :=
  mkListLit .zero (Lean.mkConst ``LeanQbe.T.SigEntry) (ss.map sigEntryToExpr)

private def listSymNatToExpr (xs : List (Sym × Nat)) : Lean.Expr :=
  let pairTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero])
    (Lean.mkConst ``LeanQbe.T.Sym) (Lean.mkConst ``Nat)
  let elems := xs.map fun (s, n) =>
    mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero])
      (Lean.mkConst ``LeanQbe.T.Sym) (Lean.mkConst ``Nat) (Lean.toExpr s) (mkNatLit n)
  mkListLit .zero pairTy elems

private def externToExpr (e : Extern) : Lean.Expr :=
  mkApp3 (Lean.mkConst ``LeanQbe.T.Extern.mk) (Lean.toExpr e.name)
    (listTyToExpr e.as) (listTyToExpr e.rs)

private def listExternToExpr (es : List Extern) : Lean.Expr :=
  mkListLit .zero (Lean.mkConst ``LeanQbe.T.Extern) (es.map externToExpr)

private def listSymToExpr (ss : List Sym) : Lean.Expr :=
  mkListLit .zero (Lean.mkConst ``LeanQbe.T.Sym) (ss.map Lean.toExpr)

private def listTyToExprM (ts : List Lean.Expr) : Lean.Expr :=
  let tyConst := Lean.mkConst ``LeanQbe.T.Ty
  ts.foldr (fun x acc => mkApp3 (Lean.mkConst ``List.cons [.zero]) tyConst x acc)
    (mkApp (Lean.mkConst ``List.nil [.zero]) tyConst)

private partial def normListExpr (e : Lean.Expr) : MetaM (List Lean.Expr) := do
  let e ← whnf e
  if e.isAppOfArity ``List.nil 1 then return []
  if e.isAppOfArity ``List.cons 3 then
    let args := e.getAppArgs
    return (← whnf args[1]!) :: (← normListExpr args[2]!)
  throwError "normListExpr: unexpected {e}"

private def normArg (vE tE e : Lean.Expr) : MetaM Lean.Expr := do
  let a ← whnf e
  if a.isAppOfArity ``LeanQbe.T.Arg.var 3 then
    let aArgs := a.getAppArgs
    let vNorm ← whnf aArgs[2]!
    return mkApp3 (Lean.mkConst ``LeanQbe.T.Arg.var) vE tE vNorm
  if a.isAppOfArity ``LeanQbe.T.Arg.imm 3 then
    let aArgs := a.getAppArgs
    let valNorm ← reduce (← whnf aArgs[2]!)
    return mkApp3 (Lean.mkConst ``LeanQbe.T.Arg.imm) vE tE valNorm
  return a

private partial def normTupArg (vE : Lean.Expr) (ts : List Lean.Expr) (e : Lean.Expr) :
    MetaM Lean.Expr := do
  match ts with
  | [] => return Lean.mkConst ``Unit.unit
  | t :: rest =>
    let e ← whnf e
    let args := e.getAppArgs
    if e.isAppOfArity ``Prod.mk 4 then
      let aNorm ← normArg vE t args[2]!
      let tailNorm ← normTupArg vE rest args[3]!
      return mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero]) args[0]! args[1]! aNorm tailNorm
    else
      throwError "normTupArg: unexpected {e}"

private def normOp (vE opE : Lean.Expr) : MetaM Lean.Expr := do
  let opW ← whnf opE
  if opW.isAppOfArity ``LeanQbe.T.Op.mk 5 then
    let args := opW.getAppArgs
    let sig ← normListExpr args[2]!
    let code ← reduce (← whnf args[3]!)
    let argsNorm ← normTupArg vE sig args[4]!
    return mkApp5 (Lean.mkConst ``LeanQbe.T.Op.mk) vE args[1]! args[2]! code argsNorm
  return opW

private def mkEtaTup (fE : Lean.Expr) (elemTys : List Lean.Expr) (tupVar : Lean.Expr)
    (mkTupTy : List Lean.Expr → Lean.Expr) : Lean.Expr :=
  let rec go (curVar : Lean.Expr) : List Lean.Expr → Lean.Expr
    | [] => Lean.mkConst ``Unit.unit
    | t :: ts =>
      let ta := mkApp fE t
      let tb := mkTupTy ts
      let fst := mkApp3 (Lean.mkConst ``Prod.fst [.zero, .zero]) ta tb curVar
      let snd := mkApp3 (Lean.mkConst ``Prod.snd [.zero, .zero]) ta tb curVar
      mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero]) ta tb fst (go snd ts)
  go tupVar elemTys

private def mkTupTyV (vE : Lean.Expr) (ts : List Lean.Expr) : Lean.Expr :=
  mkApp3 (Lean.mkConst ``LeanQbe.T.Tup) (Lean.mkConst ``LeanQbe.T.Ty) vE (listTyToExprM ts)

private def listListTyToExprM (tss : List Lean.Expr) : Lean.Expr :=
  let listTy := mkApp (Lean.mkConst ``List [.zero]) (Lean.mkConst ``LeanQbe.T.Ty)
  tss.foldr (fun x acc => mkApp3 (Lean.mkConst ``List.cons [.zero]) listTy x acc)
    (mkApp (Lean.mkConst ``List.nil [.zero]) listTy)

private def mkTupTyL (lE : Lean.Expr) (tss : List Lean.Expr) : Lean.Expr :=
  let listTy := mkApp (Lean.mkConst ``List [.zero]) (Lean.mkConst ``LeanQbe.T.Ty)
  mkApp3 (Lean.mkConst ``LeanQbe.T.Tup) listTy lE (listListTyToExprM tss)

private partial def normListListTy (e : Lean.Expr) : MetaM (List Lean.Expr) := do
  let e ← whnf e
  if e.isAppOfArity ``List.nil 1 then return []
  if e.isAppOfArity ``List.cons 3 then
    let args := e.getAppArgs
    return (← reduce args[1]!) :: (← normListListTy args[2]!)
  throwError "normListListTy: unexpected {e}"

private inductive LinStep where
  | let_ (tsE opNorm tupTy : Lean.Expr) (fvar : Lean.Expr)
  | load (tE aNorm vtTy : Lean.Expr) (fvar : Lean.Expr)
  | store (tE vNorm aNorm : Lean.Expr)
  | call (fNorm asE bsE argsNorm tupTy : Lean.Expr) (fvar : Lean.Expr)

mutual
private partial def normPhoasExpr (vE lE rsE e : Lean.Expr) : MetaM Lean.Expr := do
  let mut lctx ← getLCtx
  let insts ← getLocalInstances
  let mut cur := e
  let mut steps : Array LinStep := #[]
  let mut termNorm : Option Lean.Expr := none
  while termNorm.isNone do
    let eW ← withLCtx lctx insts (whnf cur)
    if eW.isAppOfArity ``LeanQbe.T.Expr.let_ 6 then
      let args := eW.getAppArgs
      let tsE ← withLCtx lctx insts (reduce args[3]!)
      let ts ← withLCtx lctx insts (normListExpr tsE)
      let opNorm ← withLCtx lctx insts (normOp vE args[4]!)
      let tupTy := mkTupTyV vE ts
      let fvarId ← mkFreshFVarId
      let fvar := Lean.mkFVar fvarId
      lctx := lctx.mkLocalDecl fvarId `x tupTy
      steps := steps.push (.let_ tsE opNorm tupTy fvar)
      cur := mkApp args[5]! (mkEtaTup vE ts fvar (mkTupTyV vE))
    else if eW.isAppOfArity ``LeanQbe.T.Expr.load 6 then
      let args := eW.getAppArgs
      let tE ← withLCtx lctx insts (reduce args[3]!)
      let aNorm ← withLCtx lctx insts (normArg vE (Lean.mkConst ``LeanQbe.T.i64) args[4]!)
      let vtTy := mkApp vE tE
      let fvarId ← mkFreshFVarId
      let fvar := Lean.mkFVar fvarId
      lctx := lctx.mkLocalDecl fvarId `v vtTy
      steps := steps.push (.load tE aNorm vtTy fvar)
      cur := mkApp args[5]! fvar
    else if eW.isAppOfArity ``LeanQbe.T.Expr.store 7 then
      let args := eW.getAppArgs
      let tE ← withLCtx lctx insts (reduce args[3]!)
      let vNorm ← withLCtx lctx insts (normArg vE tE args[4]!)
      let aNorm ← withLCtx lctx insts (normArg vE (Lean.mkConst ``LeanQbe.T.i64) args[5]!)
      steps := steps.push (.store tE vNorm aNorm)
      cur := args[6]!
    else if eW.isAppOfArity ``LeanQbe.T.Expr.call 8 then
      let args := eW.getAppArgs
      let fNorm ← withLCtx lctx insts (reduce args[3]!)
      let asE ← withLCtx lctx insts (reduce args[4]!)
      let bsE ← withLCtx lctx insts (reduce args[5]!)
      let asL ← withLCtx lctx insts (normListExpr asE)
      let bsL ← withLCtx lctx insts (normListExpr bsE)
      let argsNorm ← withLCtx lctx insts (normTupArg vE asL args[6]!)
      let tupTy := mkTupTyV vE bsL
      let fvarId ← mkFreshFVarId
      let fvar := Lean.mkFVar fvarId
      lctx := lctx.mkLocalDecl fvarId `xs tupTy
      steps := steps.push (.call fNorm asE bsE argsNorm tupTy fvar)
      cur := mkApp args[7]! (mkEtaTup vE bsL fvar (mkTupTyV vE))
    else
      let tail ← withLCtx lctx insts do
        if eW.isAppOfArity ``LeanQbe.T.Expr.jnz 6 then
          let args := eW.getAppArgs
          let cNorm ← normArg vE (Lean.mkConst ``LeanQbe.T.Ty.bool) args[3]!
          let tNorm ← normPhoasExpr vE lE rsE args[4]!
          let eNorm ← normPhoasExpr vE lE rsE args[5]!
          return mkAppN (Lean.mkConst ``LeanQbe.T.Expr.jnz) #[vE, lE, rsE, cNorm, tNorm, eNorm]
        if eW.isAppOfArity ``LeanQbe.T.Expr.jump 6 then
          let args := eW.getAppArgs
          let tsE ← reduce args[3]!
          let ts ← normListExpr tsE
          let jNorm ← whnf args[4]!
          let argsNorm ← normTupArg vE ts args[5]!
          return mkAppN (Lean.mkConst ``LeanQbe.T.Expr.jump) #[vE, lE, rsE, tsE, jNorm, argsNorm]
        if eW.isAppOfArity ``LeanQbe.T.Expr.ret 4 then
          let args := eW.getAppArgs
          let rsL ← normListExpr rsE
          let vsNorm ← normTupArg vE rsL args[3]!
          return mkAppN (Lean.mkConst ``LeanQbe.T.Expr.ret) #[vE, lE, rsE, vsNorm]
        if eW.isAppOfArity ``LeanQbe.T.Expr.exit 6 then
          let args := eW.getAppArgs
          let fNorm ← reduce args[3]!
          let asE ← reduce args[4]!
          let asL ← normListExpr asE
          let argsNorm ← normTupArg vE asL args[5]!
          return mkAppN (Lean.mkConst ``LeanQbe.T.Expr.exit) #[vE, lE, rsE, fNorm, asE, argsNorm]
        if eW.isAppOfArity ``LeanQbe.T.Expr.hlt 3 then
          return eW
        if eW.isAppOfArity ``LeanQbe.T.Expr.group 6 then
          let args := eW.getAppArgs
          let sigE ← reduce args[3]!
          let sigL ← normListListTy sigE
          let tupLTy := mkTupTyL lE sigL
          let bodiesNorm ← withLocalDeclD `Js tupLTy fun js => do
            let appB := mkApp args[4]! (mkEtaTup lE sigL js (mkTupTyL lE))
            let bNorm ← normPhoasBlocks vE lE rsE appB
            mkLambdaFVars #[js] bNorm
          let kNorm ← withLocalDeclD `Js tupLTy fun js => do
            let appK := mkApp args[5]! (mkEtaTup lE sigL js (mkTupTyL lE))
            let eNorm ← normPhoasExpr vE lE rsE appK
            mkLambdaFVars #[js] eNorm
          return mkAppN (Lean.mkConst ``LeanQbe.T.Expr.group)
            #[vE, lE, rsE, sigE, bodiesNorm, kNorm]
        throwError "normPhoasExpr: unexpected {eW}"
      termNorm := some tail
  let mut acc := termNorm.get!
  for step in steps.reverse do
    match step with
    | .let_ tsE opNorm tupTy fvar =>
      let kLam := Lean.mkLambda `x .default tupTy (acc.abstract #[fvar])
      acc := mkAppN (Lean.mkConst ``LeanQbe.T.Expr.let_) #[vE, lE, rsE, tsE, opNorm, kLam]
    | .load tE aNorm vtTy fvar =>
      let kLam := Lean.mkLambda `v .default vtTy (acc.abstract #[fvar])
      acc := mkAppN (Lean.mkConst ``LeanQbe.T.Expr.load) #[vE, lE, rsE, tE, aNorm, kLam]
    | .store tE vNorm aNorm =>
      acc := mkAppN (Lean.mkConst ``LeanQbe.T.Expr.store) #[vE, lE, rsE, tE, vNorm, aNorm, acc]
    | .call fNorm asE bsE argsNorm tupTy fvar =>
      let kLam := Lean.mkLambda `xs .default tupTy (acc.abstract #[fvar])
      acc := mkAppN (Lean.mkConst ``LeanQbe.T.Expr.call)
        #[vE, lE, rsE, fNorm, asE, bsE, argsNorm, kLam]
  return acc

private partial def normPhoasBlocks (vE lE rsE e : Lean.Expr) : MetaM Lean.Expr := do
  let e ← whnf e
  if e.isAppOfArity ``LeanQbe.T.Blocks.nil 3 then
    return e
  if e.isAppOfArity ``LeanQbe.T.Blocks.cons 7 then
    let args := e.getAppArgs
    let tsE ← reduce args[3]!
    let sigE ← reduce args[4]!
    let ts ← normListExpr tsE
    let tupTy := mkTupTyV vE ts
    let bNorm ← withLocalDeclD `xs tupTy fun xs => do
      let appB := mkApp args[5]! (mkEtaTup vE ts xs (mkTupTyV vE))
      let body ← normPhoasExpr vE lE rsE appB
      mkLambdaFVars #[xs] body
    let bsNorm ← normPhoasBlocks vE lE rsE args[6]!
    return mkAppN (Lean.mkConst ``LeanQbe.T.Blocks.cons)
      #[vE, lE, rsE, tsE, sigE, bNorm, bsNorm]
  throwError "normPhoasBlocks: unexpected {e}"
end

/-- Normalize a closed PHOAS `Fn` term into a flat literal `Fn.mk` without `denoteFunc`. -/
def normPhoasFn (fnE : Lean.Expr) : MetaM Lean.Expr := do
  let fnW ← whnf fnE
  if !fnW.isAppOfArity ``LeanQbe.T.Fn.mk 4 then
    throwError "normPhoasFn: unexpected {fnW}"
  let args := fnW.getAppArgs
  let nmE ← reduce args[0]!
  let asE ← reduce args[1]!
  let rsE ← reduce args[2]!
  let asL ← normListExpr asE
  let vTy := Lean.mkForall `t .default (Lean.mkConst ``LeanQbe.T.Ty) (mkSort Level.one)
  let listTy := mkApp (Lean.mkConst ``List [.zero]) (Lean.mkConst ``LeanQbe.T.Ty)
  let lTy := Lean.mkForall `ts .default listTy (mkSort Level.one)
  let bodyNorm ← withLocalDeclD `V vTy fun vE =>
    withLocalDeclD `L lTy fun lE => do
      let tupTy := mkTupTyV vE asL
      withLocalDeclD `xs tupTy fun xs => do
        let appBody := mkApp3 args[3]! vE lE (mkEtaTup vE asL xs (mkTupTyV vE))
        let exprNorm ← normPhoasExpr vE lE rsE appBody
        mkLambdaFVars #[vE, lE, xs] exprNorm
  return mkApp4 (Lean.mkConst ``LeanQbe.T.Fn.mk) nmE asE rsE bodyNorm

/-- Compiled MetaM output for a single inlining chunk `[a, a + n)`. -/
structure EvalChunkInlData where
  matFns : List MatFnData
  candFlags : List Bool
  seenOut : List SigEntry

/-- Evaluated base metadata for chunked `Module.optInlinePolicy` materialization. -/
structure EvalChunkBaseData where
  siteCounts : List (Sym × Nat)
  loopCounts : List (Sym × Nat)
  externs : List Extern
  exits : List Sym

/-- Evaluate `inlSiteCounts`, `inlLoopCounts`, `externs`, and `exits` once in MetaM. -/
def evalChunkBaseData (M : Module) (policy : InlinePolicy) : EvalChunkBaseData :=
  { siteCounts := inlSiteCounts policy M.fns
    loopCounts := inlLoopCounts policy M.fns
    externs := M.externs
    exits := M.exits }

/-- Evaluate `[a, a + n)` in compiled MetaM returning reified `MatFnData`, candidate flags,
and the cumulative `seen` signature list through `a + n`. -/
def evalChunkInlData (M : Module) (policy : InlinePolicy)
    (siteCounts loopCounts : List (Sym × Nat)) (a n : Nat) : EvalChunkInlData :=
  let pre := M.fns.take a
  let slice := (M.fns.drop a).take n
  let extSigs := M.externs.map Extern.sig
  let seenPre := pre.map Fn.sig
  let candsPre := inlineFnsPolicyCands policy siteCounts loopCounts extSigs M.exits [] [] pre
  let rec go (seen : List SigEntry) (cands : List Fn) :
      List Fn → List MatFnData × List Bool × List SigEntry
    | [] => ([], [], seen)
    | fn :: rest =>
      let candsFn := selectCandsForCaller policy cands fn
      let fn' := fn.inline candsFn
      let allowed := seen ++ extSigs
      let sites := lookupCallSite siteCounts fn'.name
      let loopSites := lookupCallSite loopCounts fn'.name
      let ok := inlineCandidateOkPolicy policy sites loopSites allowed M.exits fn'
      let cands' := if ok then fn' :: cands else cands
      let (ms, fs, sEnd) := go (seen ++ [fn.sig]) cands' rest
      (⟨fn.name, fn.as, fn.rs, reifyFunc fn'.body⟩ :: ms, ok :: fs, sEnd)
  let (ms, fs, sEnd) := go seenPre candsPre slice
  { matFns := ms, candFlags := fs, seenOut := sEnd }

private partial def peelListRange (listE : Lean.Expr) (start count : Nat)
    (bounded : Bool := true) : MetaM (Array Lean.Expr) := do
  let mut cur := listE
  let mut idx : Nat := 0
  let stop := start + count
  let mut out : Array Lean.Expr := #[]
  while !bounded || idx < stop do
    let w ← whnf cur
    if w.isAppOfArity ``List.nil 1 then
      return out
    else if w.isAppOfArity ``List.cons 3 then
      let args := w.getAppArgs
      if idx >= start then
        out := out.push args[1]!
      cur := args[2]!
      idx := idx + 1
    else
      throwError "inline_mod_chunk!: expected list cons/nil at index {idx}, got {w}"
  return out

private partial def resolveConstLitElems (constNm : Name) : MetaM (List Lean.Expr) := do
  let env ← getEnv
  let some cinfo := env.find? constNm
    | throwError "inline_mod_chunk!: unknown constant '{constNm}'"
  let some val := cinfo.value?
    | throwError "inline_mod_chunk!: constant '{constNm}' has no value"
  let rec go (acc : List Lean.Expr) (e : Lean.Expr) : MetaM (List Lean.Expr) :=
    if e.isAppOfArity ``List.nil 1 then
      return acc.reverse
    else if e.isAppOfArity ``List.cons 3 then
      let args := e.getAppArgs
      go (args[1]! :: acc) args[2]!
    else
      throwError "inline_mod_chunk!: expected literal list in '{constNm}', got {e}"
  go [] val

/-- `inline_chunk_base! baseId srcMod policy` emits materialized `siteCounts` / `loopCounts`
tables and `rest0_eq : (srcMod.optInlinePolicy policy).fns = inlRest ... 0 [] []`. -/
scoped syntax "inline_chunk_base! " ident term:arg term:arg : command

scoped elab_rules : command
  | `(inline_chunk_base! $baseId $srcModT $policyT) => do
    let ns ← getCurrNamespace
    let baseNm := ns ++ baseId.getId
    let (srcModE, policyE, baseData) ← liftTermElabM do
      let srcModE ← Term.elabTerm srcModT (some (Lean.mkConst ``LeanQbe.T.Module))
      let policyE ← Term.elabTerm policyT (some (Lean.mkConst ``LeanQbe.T.InlinePolicy))
      Term.synthesizeSyntheticMVarsNoPostponing
      let srcModE ← instantiateMVars srcModE
      let policyE ← instantiateMVars policyE
      let callE := mkApp2 (Lean.mkConst ``LeanQbe.T.evalChunkBaseData) srcModE policyE
      let bd ← unsafe evalExpr EvalChunkBaseData
        (Lean.mkConst ``LeanQbe.T.EvalChunkBaseData) callE
      return (srcModE, policyE, bd)
    let symNatTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero])
      (Lean.mkConst ``LeanQbe.T.Sym) (Lean.mkConst ``Nat)
    let listSymNatTy := mkApp (Lean.mkConst ``List [.zero]) symNatTy
    let listSymTy := mkApp (Lean.mkConst ``List [.zero]) (Lean.mkConst ``LeanQbe.T.Sym)
    let scNm := baseNm ++ `siteCounts
    let lcNm := baseNm ++ `loopCounts
    let extSigsNm := baseNm ++ `extSigs
    let exitsNm := baseNm ++ `exits
    let scEqNm := baseNm ++ `siteCounts_eq
    let lcEqNm := baseNm ++ `loopCounts_eq
    let rest0Nm := baseNm ++ `rest0_eq
    let fnsE := mkApp (Lean.mkConst ``LeanQbe.T.Module.fns) srcModE
    let extSigsLit := listSigToExpr (baseData.externs.map Extern.sig)
    let exitsLit := listSymToExpr baseData.exits
    liftCoreM do
      addCertDef scNm listSymNatTy (listSymNatToExpr baseData.siteCounts) true
      addCertDef lcNm listSymNatTy (listSymNatToExpr baseData.loopCounts) true
      addCertDef extSigsNm (mkApp (Lean.mkConst ``List [.zero])
        (Lean.mkConst ``LeanQbe.T.SigEntry)) extSigsLit false
      addCertDef exitsNm listSymTy exitsLit false
      addKernelEqThm scEqNm listSymNatTy
        (mkApp2 (Lean.mkConst ``LeanQbe.T.inlSiteCounts) policyE fnsE)
        (Lean.mkConst scNm) .zero
      addKernelEqThm lcEqNm listSymNatTy
        (mkApp2 (Lean.mkConst ``LeanQbe.T.inlLoopCounts) policyE fnsE)
        (Lean.mkConst lcNm) .zero
    let (rest0Ty, rest0Val) ← liftTermElabM do
      let pf := mkAppN (Lean.mkConst ``LeanQbe.T.Module.optInlinePolicy_fns_eq_inlRest)
        #[srcModE, policyE, Lean.mkConst scNm, Lean.mkConst lcNm,
          Lean.mkConst scEqNm, Lean.mkConst lcEqNm]
      let ty ← inferType pf
      return (← instantiateMVars ty, ← instantiateMVars pf)
    liftCoreM <| addCertThm rest0Nm rest0Ty rest0Val

/-- `inline_mod_chunk! chunkId baseId srcMod policy startIdx count [(prev := ...)]
[(isLast := ...)]` materializes and kernel-checks ONLY `[startIdx, startIdx + count)`. -/
scoped syntax "inline_mod_chunk! " ident ident term:arg term:arg num num
    ("(" ident " := " term ")")* : command

scoped elab_rules : command
  | `(inline_mod_chunk! $chunkId $baseId $srcModT $policyT $startLit $countLit
      $[($optKeys := $optVals)]*) => do
    let ns ← getCurrNamespace
    let chunkNm := ns ++ chunkId.getId
    let baseNm := ns ++ baseId.getId
    let aN := startLit.getNat
    let nN := countLit.getNat
    let mut prevNm? : Option Name := none
    let mut isLast := false
    for i in [:optKeys.size] do
      let k := optKeys[i]!.getId
      let v := optVals[i]!
      match k with
      | `prev =>
        if let `($pid:ident) := v then
          prevNm? := some (ns ++ pid.getId)
        else
          throwErrorAt v "inline_mod_chunk!: prev must be an identifier"
      | `isLast =>
        isLast ← liftTermElabM do
          let e ← Term.elabTerm v (some (Lean.mkConst ``Bool))
          Term.synthesizeSyntheticMVarsNoPostponing
          unsafe evalExpr Bool (Lean.mkConst ``Bool) (← instantiateMVars e)
      | _ => throwErrorAt optKeys[i]! "inline_mod_chunk!: unknown option '{k}'"
    let scNm := baseNm ++ `siteCounts
    let lcNm := baseNm ++ `loopCounts
    let (srcModE, policyE, chunkData) ← liftTermElabM do
      let srcModE ← Term.elabTerm srcModT (some (Lean.mkConst ``LeanQbe.T.Module))
      let policyE ← Term.elabTerm policyT (some (Lean.mkConst ``LeanQbe.T.InlinePolicy))
      Term.synthesizeSyntheticMVarsNoPostponing
      let srcModE ← instantiateMVars srcModE
      let policyE ← instantiateMVars policyE
      let callE := mkAppN (Lean.mkConst ``LeanQbe.T.evalChunkInlData)
        #[srcModE, policyE, Lean.mkConst scNm, Lean.mkConst lcNm,
          mkNatLit aN, mkNatLit nN]
      let cd ← unsafe evalExpr EvalChunkInlData
        (Lean.mkConst ``LeanQbe.T.EvalChunkInlData) callE
      return (srcModE, policyE, cd)
    let fnTy := Lean.mkConst ``LeanQbe.T.Fn
    let listFnTy := mkApp (Lean.mkConst ``List [1]) fnTy
    let listSigTy := mkApp (Lean.mkConst ``List [.zero]) (Lean.mkConst ``LeanQbe.T.SigEntry)
    let fnsE := mkApp (Lean.mkConst ``LeanQbe.T.Module.fns) srcModE
    let extSigsE := mkApp4 (Lean.mkConst ``List.map [.zero, .zero])
      (Lean.mkConst ``LeanQbe.T.Extern) (Lean.mkConst ``LeanQbe.T.SigEntry)
      (Lean.mkConst ``LeanQbe.T.Extern.sig)
      (mkApp (Lean.mkConst ``LeanQbe.T.Module.externs) srcModE)
    let exitsE := mkApp (Lean.mkConst ``LeanQbe.T.Module.exits) srcModE
    let seenInE := match prevNm? with
      | none => mkApp (Lean.mkConst ``List.nil [.zero]) (Lean.mkConst ``LeanQbe.T.SigEntry)
      | some p => Lean.mkConst (p ++ `seenOut)
    let candsInE := match prevNm? with
      | none => mkApp (Lean.mkConst ``List.nil [1]) fnTy
      | some p => Lean.mkConst (p ++ `candsOut)
    -- Emit compiled `denoteFunc`-backed `Fn` literals for `[aN, aN + nN)`
    let mut fnConsts : List Lean.Expr := []
    let mut idx : Nat := 0
    for f in chunkData.matFns do
      let fnNm := chunkNm ++ `fn ++ Name.mkSimple s!"f{idx}"
      liftCoreM <| addCertDef fnNm fnTy (matFnToExpr f) true
      fnConsts := fnConsts ++ [Lean.mkConst fnNm]
      idx := idx + 1
    let litFnsNm := chunkNm ++ `fns
    liftCoreM <| addCertDef litFnsNm listFnTy (mkListLit .one fnTy fnConsts) true
    let sliceE := mkApp3 (Lean.mkConst ``List.take [1]) fnTy (mkNatLit nN)
      (mkApp3 (Lean.mkConst ``List.drop [1]) fnTy (mkNatLit aN) fnsE)
    let rhsRaw := mkAppN (Lean.mkConst ``LeanQbe.T.inlineFnsPolicy)
      #[policyE, Lean.mkConst scNm, Lean.mkConst lcNm, extSigsE, exitsE,
        seenInE, candsInE, sliceE]
    let rhsLit := mkApp4 (Lean.mkConst ``List.map [1, 1]) fnTy fnTy
      (Lean.mkConst ``LeanQbe.T.Fn.renorm) rhsRaw
    let litEqNm := chunkNm ++ `fns_eq
    liftCoreM <| addKernelEqThm litEqNm listFnTy (Lean.mkConst litFnsNm) rhsLit .one
    if isLast then
      let lenLeNm := chunkNm ++ `len_le
      let bleLhs := mkApp2 (Lean.mkConst ``Nat.ble)
        (mkApp (Lean.mkConst ``List.length [1]) fnTy |>.app fnsE)
        (mkNatLit (aN + nN))
      liftCoreM <| addKernelEqThm lenLeNm (Lean.mkConst ``Bool)
        bleLhs (Lean.mkConst ``Bool.true) .zero
      let (lastTy, lastVal) ← liftTermElabM do
        let pf := mkAppN (Lean.mkConst ``LeanQbe.T.inlRest_last)
          #[policyE, Lean.mkConst scNm, Lean.mkConst lcNm, extSigsE, exitsE, fnsE,
            mkNatLit aN, mkNatLit nN, seenInE, candsInE, Lean.mkConst litFnsNm,
            Lean.mkConst lenLeNm, Lean.mkConst litEqNm]
        let ty ← inferType pf
        return (← instantiateMVars ty, ← instantiateMVars pf)
      liftCoreM <| addCertThm (chunkNm ++ `last_eq) lastTy lastVal
    else
      let seenOutNm := chunkNm ++ `seenOut
      let candsOutNm := chunkNm ++ `candsOut
      liftCoreM <| addCertDef seenOutNm listSigTy (listSigToExpr chunkData.seenOut) false
      let mut curCandConsts ← liftTermElabM do
        match prevNm? with
        | none => pure []
        | some p => resolveConstLitElems (p ++ `candsOut)
      let sliceFnExprs ← liftTermElabM do
        if chunkData.candFlags.any id then
          peelListRange fnsE aN nN
        else
          pure #[]
      let mut j : Nat := 0
      for ok in chunkData.candFlags do
        if ok then
          let normE ← liftTermElabM do
            let fnE := sliceFnExprs[j]!
            let prevListE := mkListLit .one fnTy curCandConsts
            let candsFnE := mkAppN (Lean.mkConst ``LeanQbe.T.selectCandsForCaller)
              #[policyE, prevListE, fnE]
            let selCands ← peelListRange candsFnE 0 0 false
            let selListE := mkListLit .one fnTy selCands.toList
            let inlFnE := mkApp2 (Lean.mkConst ``LeanQbe.T.Fn.inline) selListE fnE
            normPhoasFn inlFnE
          let cNm := chunkNm ++ `cand ++ Name.mkSimple s!"c{j}"
          liftCoreM <| addCertDef cNm fnTy normE false
          curCandConsts := Lean.mkConst cNm :: curCandConsts
        j := j + 1
      liftCoreM <| addCertDef candsOutNm listFnTy (mkListLit .one fnTy curCandConsts) false
      let seenRhs := mkApp3 (Lean.mkConst ``List.append [.zero])
        (Lean.mkConst ``LeanQbe.T.SigEntry) seenInE
        (mkApp4 (Lean.mkConst ``List.map [1, .zero]) fnTy (Lean.mkConst ``LeanQbe.T.SigEntry)
          (Lean.mkConst ``LeanQbe.T.Fn.sig) sliceE)
      let candsRhs := mkAppN (Lean.mkConst ``LeanQbe.T.inlineFnsPolicyCands)
        #[policyE, Lean.mkConst scNm, Lean.mkConst lcNm, extSigsE, exitsE,
          seenInE, candsInE, sliceE]
      let seenEqNm := chunkNm ++ `seen_eq
      let candsEqNm := chunkNm ++ `cands_eq
      liftCoreM do
        addKernelEqThm seenEqNm listSigTy (Lean.mkConst seenOutNm) seenRhs .zero
        addKernelEqThm candsEqNm listFnTy (Lean.mkConst candsOutNm) candsRhs .one
      let (stepTy, stepVal) ← liftTermElabM do
        let bLit := mkNatLit (aN + nN)
        let hab := mkApp2 (Lean.mkConst ``Eq.refl [.one]) (Lean.mkConst ``Nat) bLit
        let pf := mkAppN (Lean.mkConst ``LeanQbe.T.inlRest_step)
          #[policyE, Lean.mkConst scNm, Lean.mkConst lcNm, extSigsE, exitsE, fnsE,
            mkNatLit aN, mkNatLit nN, bLit, seenInE, Lean.mkConst seenOutNm,
            candsInE, Lean.mkConst candsOutNm, Lean.mkConst litFnsNm, hab,
            Lean.mkConst litEqNm, Lean.mkConst seenEqNm, Lean.mkConst candsEqNm]
        let ty ← inferType pf
        return (← instantiateMVars ty, ← instantiateMVars pf)
      liftCoreM <| addCertThm (chunkNm ++ `step_eq) stepTy stepVal

/-- `inline_mod_join! modId fnsId srcMod policy baseId [c0, c1, ...]` concatenates chunk
function lists right-associatively into `fnsId` and `modId`, proving `modId.fns_eq` and
`modId.eq` in `O(#chunks)` with zero kernel AST reduction. -/
scoped syntax "inline_mod_join! " ident ident term:arg term:arg ident
    "[" ident,* "]" : command

scoped elab_rules : command
  | `(inline_mod_join! $modId $fnsId $srcModT $policyT $baseId [$chunkIds,*]) => do
    let ns ← getCurrNamespace
    let modNm := ns ++ modId.getId
    let fnsNm := ns ++ fnsId.getId
    let baseNm := ns ++ baseId.getId
    let chunkNms := chunkIds.getElems.toList.map fun id => ns ++ id.getId
    if chunkNms.isEmpty then
      throwError "inline_mod_join!: chunk list cannot be empty"
    let (srcModE, policyE, baseData) ← liftTermElabM do
      let srcModE ← Term.elabTerm srcModT (some (Lean.mkConst ``LeanQbe.T.Module))
      let policyE ← Term.elabTerm policyT (some (Lean.mkConst ``LeanQbe.T.InlinePolicy))
      Term.synthesizeSyntheticMVarsNoPostponing
      let srcModE ← instantiateMVars srcModE
      let policyE ← instantiateMVars policyE
      let callE := mkApp2 (Lean.mkConst ``LeanQbe.T.evalChunkBaseData) srcModE policyE
      let bd ← unsafe evalExpr EvalChunkBaseData
        (Lean.mkConst ``LeanQbe.T.EvalChunkBaseData) callE
      return (srcModE, policyE, bd)
    let fnTy := Lean.mkConst ``LeanQbe.T.Fn
    let listFnTy := mkApp (Lean.mkConst ``List [1]) fnTy
    let modTy := Lean.mkConst ``LeanQbe.T.Module
    let chunkFnsExprs := chunkNms.map fun c => Lean.mkConst (c ++ `fns)
    let fnsVal := match chunkFnsExprs.reverse with
      | [] => mkApp (Lean.mkConst ``List.nil [1]) fnTy
      | last :: restRev =>
        restRev.foldl (fun acc pre =>
          mkApp3 (Lean.mkConst ``List.append [1]) fnTy pre acc) last
    liftCoreM <| addCertDef fnsNm listFnTy fnsVal true
    let modVal := mkApp3 (Lean.mkConst ``LeanQbe.T.Module.mk) (Lean.mkConst fnsNm)
      (listExternToExpr baseData.externs) (listSymToExpr baseData.exits)
    liftCoreM <| addCertDef modNm modTy modVal true
    -- Chain `last_eq` and `step_eq` from back to front:
    let (fnsEqTy, fnsEqProof, modEqTy, modEqProof) ← liftTermElabM do
      let revChunks := chunkNms.reverse
      let lastNm := revChunks.head!
      let mut eqPf : Lean.Expr := Lean.mkConst (lastNm ++ `last_eq)
      for cNm in revChunks.tail! do
        let stepE := Lean.mkConst (cNm ++ `step_eq)
        eqPf ← mkAppM ``LeanQbe.T.inlRest_prepend_eq #[stepE, eqPf]
      let restToFns ← mkEqTrans (Lean.mkConst (baseNm ++ `rest0_eq)) eqPf
      let fnsEqPf ← mkEqSymm restToFns
      let optModE := mkApp2 (Lean.mkConst ``LeanQbe.T.Module.optInlinePolicy) srcModE policyE
      let modFnsE := mkApp (Lean.mkConst ``LeanQbe.T.Module.fns) (Lean.mkConst modNm)
      let optFnsE := mkApp (Lean.mkConst ``LeanQbe.T.Module.fns) optModE
      let modFnsEqTy := mkApp3 (Lean.mkConst ``Eq [2]) listFnTy modFnsE optFnsE
      let extsEq := mkApp2 (Lean.mkConst ``Eq.refl [.one])
        (mkApp (Lean.mkConst ``List [.zero]) (Lean.mkConst ``LeanQbe.T.Extern))
        (listExternToExpr baseData.externs)
      let exitsEq := mkApp2 (Lean.mkConst ``Eq.refl [.one])
        (mkApp (Lean.mkConst ``List [.zero]) (Lean.mkConst ``LeanQbe.T.Sym))
        (listSymToExpr baseData.exits)
      let modEqPf := mkApp5 (Lean.mkConst ``LeanQbe.T.Module.eq_of_fields)
        (Lean.mkConst modNm) optModE fnsEqPf extsEq exitsEq
      let modEqTy := mkApp3 (Lean.mkConst ``Eq [2]) modTy (Lean.mkConst modNm) optModE
      return (← instantiateMVars modFnsEqTy, ← instantiateMVars fnsEqPf,
        ← instantiateMVars modEqTy, ← instantiateMVars modEqPf)
    liftCoreM do
      addCertThm (modNm ++ `fns_eq) fnsEqTy fnsEqProof
      addCertThm (modNm ++ `eq) modEqTy modEqProof

end

end LeanQbe.T
