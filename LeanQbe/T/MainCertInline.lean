module

public import LeanQbe.T.MainCertInlineProof
public import LeanQbe.T.MainCertProof
public import LeanQbe.T.MainInline
public meta import Lean
public meta import LeanQbe.T.MainInline
public meta import LeanQbe.T.MainCertElab
public meta import LeanQbe.T.MainLinkSplice

/-!
# Certified Inlined Compilation Bridge & `inline_mod!` Materializer (`MainCertInline`)

Re-exports `LeanQbe.T.MainCertInlineProof` (`moduleOk_parts`, `LinkedCert.{castFns, castModule,
of_eq}`, `optInlinePolicy`/`optInline` `FnSpec` and `TargetInit` `Eventually` lifts, and raw
`compileModuleOptInlinePolicy` bridges) alongside the `inline_mod!` MetaM materializer:
* `inline_mod! <inlModName> <srcMod> <policy>`: evaluates `srcMod.optInlinePolicy policy` once
  in MetaM, emits `<inlModName> : Module` as a literal `denoteFunc`-backed `Module` (zero
  nested PHOAS closures or `inlinePolicy` overhead in downstream `compile_linked_chunks!` slices),
  and emits `<inlModName>.eq : <inlModName> = srcMod.optInlinePolicy policy` and
  `<inlModName>.fns_eq` once via `addKernelEqThm`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

/-! ## `inline_mod!` Meta Materializer & Elaborator -/

meta section

open Lean Elab Command Meta

/-- `Type 0` materialized function payload extracted from `Module.inlinePolicy`. -/
structure MatFnData where
  name : Sym
  as : List Ty
  rs : List Ty
  flat : TFlat rs

/-- `Type 0` materialized module payload evaluated once in MetaM by `inline_mod!`. -/
structure MatModData where
  fns : List MatFnData
  externs : List Extern
  exits : List Sym

/-- Evaluate `M.inlinePolicy policy` and reify every function body once into `Type 0` `TFlat`. -/
def evalOptInlinePolicyData (M : Module) (policy : InlinePolicy) : MatModData :=
  let M' := M.inlinePolicy policy
  { fns := M'.fns.map fun fn => ⟨fn.name, fn.as, fn.rs, reifyFunc fn.body⟩
    externs := M'.externs
    exits := M'.exits }

-- Shared MetaM AST literal builders and elaboration helpers for `inline_mod!` and chunking.
namespace InlineMeta

def mkListLit (u : Level) (ty : Lean.Expr) (elems : List Lean.Expr) : Lean.Expr :=
  elems.reverse.foldl
    (fun acc x => mkApp3 (Lean.mkConst ``List.cons [u]) ty x acc)
    (mkApp (Lean.mkConst ``List.nil [u]) ty)

private def mkPairTy (a b : Lean.Expr) : Lean.Expr :=
  mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) a b

private def mkPair (a b x y : Lean.Expr) : Lean.Expr :=
  mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero]) a b x y

def listTyToExpr (ts : List Ty) : Lean.Expr :=
  mkListLit .zero (Lean.mkConst ``LeanQbe.T.Ty) (ts.map tyToExpr)

def listListTyToExpr (tss : List (List Ty)) : Lean.Expr :=
  let listTy := mkApp (Lean.mkConst ``List [.zero]) (Lean.mkConst ``LeanQbe.T.Ty)
  mkListLit .zero listTy (tss.map listTyToExpr)

def cmpOpToExpr : CmpOp → Lean.Expr
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

def fcmpOpToExpr : FCmpOp → Lean.Expr
  | .eq => Lean.mkConst ``LeanQbe.T.FCmpOp.eq
  | .ne => Lean.mkConst ``LeanQbe.T.FCmpOp.ne
  | .lt => Lean.mkConst ``LeanQbe.T.FCmpOp.lt
  | .le => Lean.mkConst ``LeanQbe.T.FCmpOp.le
  | .gt => Lean.mkConst ``LeanQbe.T.FCmpOp.gt
  | .ge => Lean.mkConst ``LeanQbe.T.FCmpOp.ge
  | .ord => Lean.mkConst ``LeanQbe.T.FCmpOp.ord
  | .uno => Lean.mkConst ``LeanQbe.T.FCmpOp.uno

def valToExpr : (t : Ty) → Val t → Lean.Expr
  | .bool, v => Lean.toExpr (v : Bool)
  | .bits n, v => @Lean.toExpr (BitVec n) _ v
  | .float f, v => @Lean.toExpr (BitVec f.width) _ v
  | .pair a b, v =>
    let ta := mkApp (Lean.mkConst ``LeanQbe.T.Val) (tyToExpr a)
    let tb := mkApp (Lean.mkConst ``LeanQbe.T.Val) (tyToExpr b)
    mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero]) ta tb (valToExpr a v.1) (valToExpr b v.2)

def argKToExpr (t : Ty) : Arg K t → Lean.Expr
  | .var idx =>
    mkApp3 (Lean.mkConst ``LeanQbe.T.Arg.var) (Lean.mkConst ``LeanQbe.T.K)
      (tyToExpr t) (mkNatLit idx)
  | .imm c =>
    mkApp3 (Lean.mkConst ``LeanQbe.T.Arg.imm) (Lean.mkConst ``LeanQbe.T.K)
      (tyToExpr t) (valToExpr t c)

def tupArgKToExpr : (ts : List Ty) → Tup (Arg K) ts → Lean.Expr
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

private def mkCmpOpExpr (nm : Name) (opE : Lean.Expr) (t m : Ty) : Lean.Expr :=
  let me := tyToExpr m
  mkApp4 (Lean.mkConst nm) opE (tyToExpr t) me
    (mkApp2 (Lean.mkConst ``Eq.refl [.one]) (Lean.mkConst ``LeanQbe.T.Ty) me)

def opCodeToExpr {sig rs : List Ty} : OpCode sig rs → Lean.Expr
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
  | .cmp o t m _ => mkCmpOpExpr ``LeanQbe.T.OpCode.cmp (cmpOpToExpr o) t m
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
  | .fcmp o t m _ => mkCmpOpExpr ``LeanQbe.T.OpCode.fcmp (fcmpOpToExpr o) t m
  | .fptoui f n => mkApp2 (Lean.mkConst ``LeanQbe.T.OpCode.fptoui) (Lean.toExpr f) (mkNatLit n)
  | .fptosi f n => mkApp2 (Lean.mkConst ``LeanQbe.T.OpCode.fptosi) (Lean.toExpr f) (mkNatLit n)
  | .uitofp n f => mkApp2 (Lean.mkConst ``LeanQbe.T.OpCode.uitofp) (mkNatLit n) (Lean.toExpr f)
  | .sitofp n f => mkApp2 (Lean.mkConst ``LeanQbe.T.OpCode.sitofp) (mkNatLit n) (Lean.toExpr f)
  | .fcvt f g => mkApp2 (Lean.mkConst ``LeanQbe.T.OpCode.fcvt) (Lean.toExpr f) (Lean.toExpr g)

def opKToExpr {rs : List Ty} (op : Op K rs) : Lean.Expr :=
  mkApp5 (Lean.mkConst ``LeanQbe.T.Op.mk) (Lean.mkConst ``LeanQbe.T.K)
    (listTyToExpr rs) (listTyToExpr op.sig) (opCodeToExpr op.code) (tupArgKToExpr op.sig op.args)

mutual
def tflatToExpr (rs : List Ty) : TFlat rs → Lean.Expr
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

def tblocksToExpr (rs : List Ty) : {sig : List (List Ty)} → TBlocks rs sig → Lean.Expr
  | _, .nil => mkApp (Lean.mkConst ``LeanQbe.T.TBlocks.nil) (listTyToExpr rs)
  | _, .cons (ts := ts) (sig := sig') b bs =>
    mkApp5 (Lean.mkConst ``LeanQbe.T.TBlocks.cons) (listTyToExpr rs) (listTyToExpr ts)
      (listListTyToExpr sig') (tflatToExpr rs b) (tblocksToExpr rs bs)
end

def matFnToExpr (f : MatFnData) : Lean.Expr :=
  let asE := listTyToExpr f.as
  let rsE := listTyToExpr f.rs
  let bodyE := mkApp3 (Lean.mkConst ``LeanQbe.T.denoteFunc) asE rsE (tflatToExpr f.rs f.flat)
  mkApp4 (Lean.mkConst ``LeanQbe.T.Fn.mk) (Lean.toExpr f.name) asE rsE bodyE

def externToExpr (e : Extern) : Lean.Expr :=
  mkApp3 (Lean.mkConst ``LeanQbe.T.Extern.mk) (Lean.toExpr e.name)
    (listTyToExpr e.as) (listTyToExpr e.rs)

def listExternToExpr (es : List Extern) : Lean.Expr :=
  mkListLit .zero (Lean.mkConst ``LeanQbe.T.Extern) (es.map externToExpr)

def listSymToExpr (ss : List Sym) : Lean.Expr :=
  mkListLit .zero (Lean.mkConst ``LeanQbe.T.Sym) (ss.map Lean.toExpr)

def sigEntryToExpr (s : SigEntry) : Lean.Expr :=
  let listTy := mkApp (Lean.mkConst ``List [.zero]) (Lean.mkConst ``LeanQbe.T.Ty)
  mkPair (Lean.mkConst ``LeanQbe.T.Sym) (mkPairTy listTy listTy) (Lean.toExpr s.1)
    (mkPair listTy listTy (listTyToExpr s.2.1) (listTyToExpr s.2.2))

def listSigToExpr (ss : List SigEntry) : Lean.Expr :=
  mkListLit .zero (Lean.mkConst ``LeanQbe.T.SigEntry) (ss.map sigEntryToExpr)

def listSymNatToExpr (xs : List (Sym × Nat)) : Lean.Expr :=
  let symE := Lean.mkConst ``LeanQbe.T.Sym
  let natE := Lean.mkConst ``Nat
  mkListLit .zero (mkPairTy symE natE)
    (xs.map fun (s, n) => mkPair symE natE (Lean.toExpr s) (mkNatLit n))

def elabModAndPolicy (srcModT policyT : Syntax) : TermElabM (Lean.Expr × Lean.Expr) := do
  let srcModE ← Term.elabTerm srcModT (some (Lean.mkConst ``LeanQbe.T.Module))
  let policyE ← Term.elabTerm policyT (some (Lean.mkConst ``LeanQbe.T.InlinePolicy))
  Term.synthesizeSyntheticMVarsNoPostponing
  return (← instantiateMVars srcModE, ← instantiateMVars policyE)

def emitMatFnDefs (pfx : Name) (fns : List MatFnData) : CoreM (List Lean.Expr) := do
  let fnTy := Lean.mkConst ``LeanQbe.T.Fn
  let mut fnConsts : Array Lean.Expr := #[]
  let mut idx : Nat := 0
  for f in fns do
    let fnNm := pfx ++ `fn ++ Name.mkSimple s!"f{idx}"
    addCertDef fnNm fnTy (matFnToExpr f) true
    fnConsts := fnConsts.push (Lean.mkConst fnNm)
    idx := idx + 1
  return fnConsts.toList

end InlineMeta

open InlineMeta

private def matModExpr (fnConsts : List Lean.Expr) (m : MatModData) : Lean.Expr :=
  let fnsE := mkListLit .one (Lean.mkConst ``LeanQbe.T.Fn) fnConsts
  mkApp3 (Lean.mkConst ``LeanQbe.T.Module.mk) fnsE
    (listExternToExpr m.externs) (listSymToExpr m.exits)

/-- `inline_mod! inlModName srcMod policy` evaluates `srcMod.optInlinePolicy policy` once in
MetaM, emits per-function literal `denoteFunc`-backed `Fn` definitions assembled into
`inlModName : Module` (avoiding monolithic codegen recursion depth on large modules), and proves
`inlModName.eq : inlModName = srcMod.optInlinePolicy policy` and `inlModName.fns_eq` once via
`addKernelEqThm` so parallel `compile_linked_chunks!` slices incur zero repeated inlining. -/
scoped syntax "inline_mod! " ident term:arg term:arg : command

scoped elab_rules : command
  | `(inline_mod! $inlId $srcModT $policyT) => do
    let ns ← getCurrNamespace
    let inlNm := ns ++ inlId.getId
    let (matData, optInlE) ← liftTermElabM do
      let (srcModE, policyE) ← elabModAndPolicy srcModT policyT
      let callE := mkApp2 (Lean.mkConst ``LeanQbe.T.evalOptInlinePolicyData) srcModE policyE
      let matData ← unsafe evalExpr MatModData (Lean.mkConst ``LeanQbe.T.MatModData) callE
      let optInlE ← instantiateMVars
        (mkApp2 (Lean.mkConst ``LeanQbe.T.Module.optInlinePolicy) srcModE policyE)
      return (matData, optInlE)
    let modTy := Lean.mkConst ``LeanQbe.T.Module
    liftCoreM do
      let fnConsts ← emitMatFnDefs inlNm matData.fns
      addCertDef inlNm modTy (matModExpr fnConsts matData) true
      addKernelEqThm (inlNm ++ `eq) modTy (Lean.mkConst inlNm) optInlE .one
    let (fnsEqTy, fnsEqProof) ← liftTermElabM do
      let proof ← mkAppM ``congrArg
        #[Lean.mkConst ``LeanQbe.T.Module.fns, Lean.mkConst (inlNm ++ `eq)]
      return (← instantiateMVars (← inferType proof), ← instantiateMVars proof)
    liftCoreM <| addCertThm (inlNm ++ `fns_eq) fnsEqTy fnsEqProof

end

end LeanQbe.T
