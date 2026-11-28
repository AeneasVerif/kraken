module

public import LeanQbe.T.Frontend.C0.Template.Snippet
public meta import LeanQbe.T.Frontend.C0.Template.Scan
public meta import Lean.Elab.Term
public meta import Lean.Parser

/-!
# Static PHOAS C0 Template Elaborator (`c0_fn_template!`, `c0_expr_template!`, `c0_stmt_template!`)

Translates lowered `LFn` ASTs with template splices into Lean lambdas returning
`LeanQbe.T.Func`, `C0ExprSnippet`, or `C0StmtSnippet` directly at elaboration time.
-/

set_option autoImplicit false

public meta section

namespace LeanQbe.T.Frontend.C0

open Lean Elab Term Meta
open LeanQbe.T

private structure TElabCtx where
  V : Lean.Expr
  L : Lean.Expr
  rsExpr : Lean.Expr
  vars : Std.HashMap Nat (Lean.Expr × Lean.Expr) := {}
  lbls : Std.HashMap Nat (Lean.Expr × Lean.Expr) := {}
  imms : Std.HashMap Nat (Lean.Expr × Lean.Expr) := {}
  tySplices : Array TySplice := #[]
  callSplices : Array CallSplice := #[]
  unrolls : Std.HashMap String (UnrollSplice × LFn) := {}
  valGetters : Std.HashMap String (Lean.Expr × Lean.Expr) := {}

private def tTyToExpr (tySplices : Array TySplice) (t : Ty) : Except String Lean.Expr :=
  match t with
  | .bool => pure LeanQbe.T.Notation.boolTyExpr
  | .bits n =>
    match tySplices.find? (fun ts => !ts.isOpaqueTy && ts.placeholderBits == n) with
    | some ts => pure (LeanQbe.T.Notation.mkBitsTy ts.leanExpr)
    | none =>
      match tySplices.find? (fun ts => ts.isOpaqueTy && ts.placeholderBits == n) with
      | some ts => pure ts.leanExpr
      | none => pure (LeanQbe.T.Notation.mkBitsTy (mkNatLit n))
  | .float f => pure (LeanQbe.T.Notation.mkFloatTy f)
  | .pair a b => do
    pure (LeanQbe.T.Notation.mkPairTy (← tTyToExpr tySplices a) (← tTyToExpr tySplices b))

private def isPlaceholderWidth (tySplices : Array TySplice) (n : Nat) : Bool :=
  tySplices.any (fun ts => ts.placeholderBits == n && n >= templatePlaceholderBase)

private def isPlaceholderByteVal (tySplices : Array TySplice) (t : Ty) (v : Val t) : Bool :=
  match t, v with
  | .bits 64, bv =>
    let x := bv.toNat
    tySplices.any fun ts =>
      ts.placeholderBits >= templatePlaceholderBase &&
      ((ts.placeholderBits + 7) / 8 == x || ts.placeholderBits == x)
  | _, _ => false

private def tValToExpr (tySplices : Array TySplice) (t : Ty) (v : Val t) :
    Except String Lean.Expr := do
  match t, v with
  | .bool, true => pure (Lean.mkConst ``Bool.true)
  | .bool, false => pure (Lean.mkConst ``Bool.false)
  | .bits n, bv =>
    match tySplices.find? (fun ts => !ts.isOpaqueTy && ts.placeholderBits == n &&
        n >= templatePlaceholderBase) with
    | some ts =>
      if bv.toNat == 0 then
        pure (mkApp2 (Lean.mkConst ``BitVec.ofNat) ts.leanExpr (mkNatLit 0))
      else
        throw ("c0 template: non-zero literal at symbolic width `bv$(w)` cannot be statically " ++
          "materialized; use an explicit `$(BitVec.ofNat w ...)` splice")
    | none =>
      if tySplices.any (fun ts => ts.isOpaqueTy && ts.placeholderBits == n &&
          n >= templatePlaceholderBase) then
        throw "c0 template: literal constant cannot be constructed for opaque `ty$(t)`"
      else if isPlaceholderByteVal tySplices (.bits n) bv then
        throw ("c0 template: `sizeof` / array indexing `arr[i]` on symbolic `bv$(w)` is " ++
          "unsupported (layout requires concrete byte stride); pass byte stride `$(stride)`")
      else
        pure (LeanQbe.T.Notation.bvNatLit (mkNatLit n) bv.toNat)
  | .float f, bv =>
    pure (LeanQbe.T.Notation.bvNatLit (mkNatLit f.width) bv.toNat)
  | .pair a b, (va, vb) =>
    let ta := mkApp (Lean.mkConst ``LeanQbe.T.Val) (← tTyToExpr tySplices a)
    let tb := mkApp (Lean.mkConst ``LeanQbe.T.Val) (← tTyToExpr tySplices b)
    pure (mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero]) ta tb
      (← tValToExpr tySplices a va) (← tValToExpr tySplices b vb))

private def tOpCodeToExpr (tySplices : Array TySplice) :
    {sig rs : List Ty} → OpCode sig rs → MetaM Lean.Expr
  | _, _, .copy t => do
    pure <| mkApp (Lean.mkConst ``LeanQbe.T.OpCode.copy) (← liftEx (tTyToExpr tySplices t))
  | _, _, .add t => do
    pure <| mkApp (Lean.mkConst ``LeanQbe.T.OpCode.add) (← liftEx (tTyToExpr tySplices t))
  | _, _, .sub t => do
    pure <| mkApp (Lean.mkConst ``LeanQbe.T.OpCode.sub) (← liftEx (tTyToExpr tySplices t))
  | _, _, .mul t => do
    pure <| mkApp (Lean.mkConst ``LeanQbe.T.OpCode.mul) (← liftEx (tTyToExpr tySplices t))
  | _, _, .neg t => do
    pure <| mkApp (Lean.mkConst ``LeanQbe.T.OpCode.neg) (← liftEx (tTyToExpr tySplices t))
  | _, _, .and t => do
    pure <| mkApp (Lean.mkConst ``LeanQbe.T.OpCode.and) (← liftEx (tTyToExpr tySplices t))
  | _, _, .or t => do
    pure <| mkApp (Lean.mkConst ``LeanQbe.T.OpCode.or) (← liftEx (tTyToExpr tySplices t))
  | _, _, .xor t => do
    pure <| mkApp (Lean.mkConst ``LeanQbe.T.OpCode.xor) (← liftEx (tTyToExpr tySplices t))
  | _, _, .not t => do
    pure <| mkApp (Lean.mkConst ``LeanQbe.T.OpCode.not) (← liftEx (tTyToExpr tySplices t))
  | _, _, .shl t => do
    pure <| mkApp (Lean.mkConst ``LeanQbe.T.OpCode.shl) (← liftEx (tTyToExpr tySplices t))
  | _, _, .lshr t => do
    pure <| mkApp (Lean.mkConst ``LeanQbe.T.OpCode.lshr) (← liftEx (tTyToExpr tySplices t))
  | _, _, .ashr t => do
    pure <| mkApp (Lean.mkConst ``LeanQbe.T.OpCode.ashr) (← liftEx (tTyToExpr tySplices t))
  | _, _, .rotl t => do
    pure <| mkApp (Lean.mkConst ``LeanQbe.T.OpCode.rotl) (← liftEx (tTyToExpr tySplices t))
  | _, _, .rotr t => do
    pure <| mkApp (Lean.mkConst ``LeanQbe.T.OpCode.rotr) (← liftEx (tTyToExpr tySplices t))
  | _, _, .fadd t => do
    pure <| mkApp (Lean.mkConst ``LeanQbe.T.OpCode.fadd) (← liftEx (tTyToExpr tySplices t))
  | _, _, .fsub t => do
    pure <| mkApp (Lean.mkConst ``LeanQbe.T.OpCode.fsub) (← liftEx (tTyToExpr tySplices t))
  | _, _, .fmul t => do
    pure <| mkApp (Lean.mkConst ``LeanQbe.T.OpCode.fmul) (← liftEx (tTyToExpr tySplices t))
  | _, _, .fdiv t => do
    pure <| mkApp (Lean.mkConst ``LeanQbe.T.OpCode.fdiv) (← liftEx (tTyToExpr tySplices t))
  | _, _, .fneg t => do
    pure <| mkApp (Lean.mkConst ``LeanQbe.T.OpCode.fneg) (← liftEx (tTyToExpr tySplices t))
  | _, _, .clz n => mkNatOp ``LeanQbe.T.OpCode.clz n
  | _, _, .ctz n => mkNatOp ``LeanQbe.T.OpCode.ctz n
  | _, _, .popcnt n => mkNatOp ``LeanQbe.T.OpCode.popcnt n
  | _, _, .ofBool n => mkNatOp ``LeanQbe.T.OpCode.ofBool n
  | _, _, .addc n => mkNatOp ``LeanQbe.T.OpCode.addc n
  | _, _, .subb n => mkNatOp ``LeanQbe.T.OpCode.subb n
  | _, _, .umulw n => mkNatOp ``LeanQbe.T.OpCode.umulw n
  | _, _, .udiv n => mkNatOp ``LeanQbe.T.OpCode.udiv n
  | _, _, .sdiv n => mkNatOp ``LeanQbe.T.OpCode.sdiv n
  | _, _, .urem n => mkNatOp ``LeanQbe.T.OpCode.urem n
  | _, _, .srem n => mkNatOp ``LeanQbe.T.OpCode.srem n
  | _, _, .zext m n => mkWidthCast ``LeanQbe.T.OpCode.zext m n
  | _, _, .sext m n => mkWidthCast ``LeanQbe.T.OpCode.sext m n
  | _, _, .trunc m n => mkWidthCast ``LeanQbe.T.OpCode.trunc m n
  | _, _, .cmp o t m _ => do
    let tE ← liftEx (tTyToExpr tySplices t)
    let mE ← liftEx (tTyToExpr tySplices m)
    let maskApp := mkApp (Lean.mkConst ``LeanQbe.T.Ty.mask) tE
    unless ← isDefEq mE maskApp do
      throwError m!"c0 template: `cmp` requires type with `.mask = bool`, got:{indentExpr tE}"
    pure <| mkApp4 (Lean.mkConst ``LeanQbe.T.OpCode.cmp) (cmpOpToExpr o) tE mE
      (LeanQbe.T.Notation.mkMaskEqRefl mE)
  | _, _, .fcmp o t m _ => do
    let tE ← liftEx (tTyToExpr tySplices t)
    let mE ← liftEx (tTyToExpr tySplices m)
    pure <| mkApp4 (Lean.mkConst ``LeanQbe.T.OpCode.fcmp) (fcmpOpToExpr o) tE mE
      (LeanQbe.T.Notation.mkMaskEqRefl mE)
  | _, _, .bitcast t u _ => do
    if isPlaceholderWidth tySplices t.size || isPlaceholderWidth tySplices u.size then
      throwError "c0 template: bitcast on symbolic width is not supported"
    let tE ← liftEx (tTyToExpr tySplices t)
    let uE ← liftEx (tTyToExpr tySplices u)
    let eqPf := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero])
      (Lean.mkConst ``Nat) (mkNatLit t.size)
    pure <| mkApp3 (Lean.mkConst ``LeanQbe.T.OpCode.bitcast) tE uE eqPf
  | _, _, .fptoui f n => do
    if isPlaceholderWidth tySplices n then
      throwError "c0 template: fptoui to symbolic width is not supported"
    pure <| mkApp2 (Lean.mkConst ``LeanQbe.T.OpCode.fptoui) (LeanQbe.T.Notation.fmtConst f)
      (mkNatLit n)
  | _, _, .fptosi f n => do
    if isPlaceholderWidth tySplices n then
      throwError "c0 template: fptosi to symbolic width is not supported"
    pure <| mkApp2 (Lean.mkConst ``LeanQbe.T.OpCode.fptosi) (LeanQbe.T.Notation.fmtConst f)
      (mkNatLit n)
  | _, _, .uitofp n f => do
    if isPlaceholderWidth tySplices n then
      throwError "c0 template: uitofp from symbolic width is not supported"
    pure <| mkApp2 (Lean.mkConst ``LeanQbe.T.OpCode.uitofp) (mkNatLit n)
      (LeanQbe.T.Notation.fmtConst f)
  | _, _, .sitofp n f => do
    if isPlaceholderWidth tySplices n then
      throwError "c0 template: sitofp from symbolic width is not supported"
    pure <| mkApp2 (Lean.mkConst ``LeanQbe.T.OpCode.sitofp) (mkNatLit n)
      (LeanQbe.T.Notation.fmtConst f)
  | _, _, _ => throwError "c0 template: unsupported OpCode"
where
  mkNatOp (nm : Name) (n : Nat) : MetaM Lean.Expr := do
    if isPlaceholderWidth tySplices n then
      if let some ts := tySplices.find? (fun s => !s.isOpaqueTy && s.placeholderBits == n) then
        return mkApp (Lean.mkConst nm) ts.leanExpr
      throwError "c0 template: bit-width OpCode requires `Nat` width, not opaque `Ty`"
    pure <| mkApp (Lean.mkConst nm) (mkNatLit n)
  mkWidthCast (ctor : Name) (m n : Nat) : MetaM Lean.Expr := do
    if isPlaceholderWidth tySplices m || isPlaceholderWidth tySplices n then
      throwError ("c0 template: width conversion (zext/sext/trunc) involving symbolic " ++
        "width `bv$(w)` cannot be statically decided without knowing width ordering")
    pure <| mkApp2 (Lean.mkConst ctor) (mkNatLit m) (mkNatLit n)

private def tArgToExpr (ctx : TElabCtx) (a : LArg) : Except String Lean.Expr := do
  match a with
  | .var id _ =>
    if let some (valE, tyE) := ctx.imms.get? id then
      pure <| mkApp3 (Lean.mkConst ``LeanQbe.T.Arg.imm) ctx.V tyE valE
    else if let some (fvar, tyE) := ctx.vars.get? id then
      pure <| mkApp3 (Lean.mkConst ``LeanQbe.T.Arg.var) ctx.V tyE fvar
    else
      throw s!"c0 template: unbound variable id {id}"
  | .imm t v =>
    let tyE ← tTyToExpr ctx.tySplices t
    let valE ← tValToExpr ctx.tySplices t v
    pure <| mkApp3 (Lean.mkConst ``LeanQbe.T.Arg.imm) ctx.V tyE valE

private def tArgListToTupExpr (ctx : TElabCtx) (args : List LArg) :
    Except String (List Lean.Expr × Lean.Expr) := do
  let argF := LeanQbe.T.Notation.mkArgApp ctx.V
  let tys ← args.mapM fun a => tTyToExpr ctx.tySplices a.ty
  let vals ← args.mapM (tArgToExpr ctx)
  pure (tys, LeanQbe.T.Notation.mkTupElems LeanQbe.T.Notation.tyConst argF tys vals)

private def tWithLoadVar (ctx : TElabCtx) (lv : LVar)
    (k : TElabCtx → MetaM Lean.Expr) : MetaM Lean.Expr := do
  let tyE ← liftEx (tTyToExpr ctx.tySplices lv.ty)
  let vTy := mkApp ctx.V tyE
  withLocalDeclD (Name.mkSimple lv.name) vTy fun x => do
    let ctx' := { ctx with vars := ctx.vars.insert lv.id (x, tyE) }
    mkLambdaFVars #[x] (← k ctx')

private def tWithTupleLVars (ctx : TElabCtx) (lvs : List LVar)
    (k : TElabCtx → MetaM Lean.Expr) : MetaM Lean.Expr := do
  let elemTys ← liftEx (lvs.mapM fun v => tTyToExpr ctx.tySplices v.ty)
  let tupTy := LeanQbe.T.Notation.mkTupTy LeanQbe.T.Notation.tyConst ctx.V elemTys
  withLocalDeclD `p tupTy fun p => do
    let mut vars := ctx.vars
    let mut i := 0
    for (lv, tyE) in lvs.zip elemTys do
      let proj := LeanQbe.T.Notation.mkTypedProj LeanQbe.T.Notation.tyConst ctx.V elemTys p i
      vars := vars.insert lv.id (proj, tyE)
      i := i + 1
    mkLambdaFVars #[p] (← k { ctx with vars })

private def tWithGroupLabels (ctx : TElabCtx) (blocks : List (Nat × List LVar × LExpr))
    (k : TElabCtx → MetaM Lean.Expr) : MetaM Lean.Expr := do
  let elemTys ← liftEx <| blocks.mapM fun (_, ps, _) => do
    let ts ← ps.mapM fun v => tTyToExpr ctx.tySplices v.ty
    pure (LeanQbe.T.Notation.listLit LeanQbe.T.Notation.tyConst ts)
  let tupTy := LeanQbe.T.Notation.mkTupTy LeanQbe.T.Notation.listTyConst ctx.L elemTys
  withLocalDeclD `Js tupTy fun js => do
    let mut lbls := ctx.lbls
    let mut j := 0
    for ((lid, _, _), sigE) in blocks.zip elemTys do
      let proj := LeanQbe.T.Notation.mkTypedProj LeanQbe.T.Notation.listTyConst ctx.L elemTys js j
      lbls := lbls.insert lid (proj, sigE)
      j := j + 1
    mkLambdaFVars #[js] (← k { ctx with lbls })

private def withMaterializedVars (ctx : TElabCtx) (args : List LArg)
    (k : TElabCtx → Array (Lean.Expr × Lean.Expr) → MetaM Lean.Expr) : MetaM Lean.Expr := do
  let rec go (c : TElabCtx) (rem : List LArg) (acc : Array (Lean.Expr × Lean.Expr)) :
      MetaM Lean.Expr := do
    match rem with
    | [] => k c acc
    | .var id _ :: rest =>
      if let some (valE, tyE) := c.imms.get? id then
        let copyOp := mkAppN (Lean.mkConst ``LeanQbe.T.Op.mk) #[
          c.V,
          LeanQbe.T.Notation.listLit LeanQbe.T.Notation.tyConst [tyE],
          LeanQbe.T.Notation.listLit LeanQbe.T.Notation.tyConst [tyE],
          mkApp (Lean.mkConst ``LeanQbe.T.OpCode.copy) tyE,
          LeanQbe.T.Notation.mkTupElems LeanQbe.T.Notation.tyConst (LeanQbe.T.Notation.mkArgApp c.V)
            [tyE] [mkApp3 (Lean.mkConst ``LeanQbe.T.Arg.imm) c.V tyE valE]
        ]
        let rsE := LeanQbe.T.Notation.listLit LeanQbe.T.Notation.tyConst [tyE]
        let tupTy := LeanQbe.T.Notation.mkTupTy LeanQbe.T.Notation.tyConst c.V [tyE]
        let lam ← withLocalDeclD `cp tupTy fun cp => do
          let proj := LeanQbe.T.Notation.mkTypedProj LeanQbe.T.Notation.tyConst c.V [tyE] cp 0
          let body ← go c rest (acc.push (proj, tyE))
          mkLambdaFVars #[cp] body
        pure <| mkAppN (Lean.mkConst ``LeanQbe.T.Expr.let_)
          #[c.V, c.L, c.rsExpr, rsE, copyOp, lam]
      else if let some (fv, tyE) := c.vars.get? id then
        go c rest (acc.push (fv, tyE))
      else
        throwError "c0 template: unbound variable id {id}"
    | .imm t v :: rest =>
      let tyE ← liftEx (tTyToExpr c.tySplices t)
      let valE ← liftEx (tValToExpr c.tySplices t v)
      let copyOp := mkAppN (Lean.mkConst ``LeanQbe.T.Op.mk) #[
        c.V,
        LeanQbe.T.Notation.listLit LeanQbe.T.Notation.tyConst [tyE],
        LeanQbe.T.Notation.listLit LeanQbe.T.Notation.tyConst [tyE],
        mkApp (Lean.mkConst ``LeanQbe.T.OpCode.copy) tyE,
        LeanQbe.T.Notation.mkTupElems LeanQbe.T.Notation.tyConst (LeanQbe.T.Notation.mkArgApp c.V)
          [tyE] [mkApp3 (Lean.mkConst ``LeanQbe.T.Arg.imm) c.V tyE valE]
      ]
      let rsE := LeanQbe.T.Notation.listLit LeanQbe.T.Notation.tyConst [tyE]
      let tupTy := LeanQbe.T.Notation.mkTupTy LeanQbe.T.Notation.tyConst c.V [tyE]
      let lam ← withLocalDeclD `cp tupTy fun cp => do
        let proj := LeanQbe.T.Notation.mkTypedProj LeanQbe.T.Notation.tyConst c.V [tyE] cp 0
        let body ← go c rest (acc.push (proj, tyE))
        mkLambdaFVars #[cp] body
      pure <| mkAppN (Lean.mkConst ``LeanQbe.T.Expr.let_)
        #[c.V, c.L, c.rsExpr, rsE, copyOp, lam]
  go ctx args #[]

private inductive RetContMode
  | normalRet
  | exprCont (contFVar : Lean.Expr)
  | stmtCont (contFVar : Lean.Expr) (stateTyExprs : List Lean.Expr)

private partial def tExprToLeanExpr (ctx : TElabCtx) (retMode : RetContMode) :
    LExpr → MetaM Lean.Expr
  | .let_ op binders k => do
    let rsE := LeanQbe.T.Notation.listLit LeanQbe.T.Notation.tyConst
      (← liftEx (op.rs.mapM (tTyToExpr ctx.tySplices)))
    let sigE := LeanQbe.T.Notation.listLit LeanQbe.T.Notation.tyConst
      (← liftEx (op.sig.mapM (tTyToExpr ctx.tySplices)))
    let codeE ← tOpCodeToExpr ctx.tySplices op.code
    let (_, argsE) ← liftEx (tArgListToTupExpr ctx op.args)
    let opE := mkAppN (Lean.mkConst ``LeanQbe.T.Op.mk) #[ctx.V, rsE, sigE, codeE, argsE]
    let lamE ← tWithTupleLVars ctx binders fun ctx' => tExprToLeanExpr ctx' retMode k
    pure <| mkAppN (Lean.mkConst ``LeanQbe.T.Expr.let_)
      #[ctx.V, ctx.L, ctx.rsExpr, rsE, opE, lamE]
  | .load t addr binder k => do
    let tE ← liftEx (tTyToExpr ctx.tySplices t)
    let addrE ← liftEx (tArgToExpr ctx addr)
    let lamE ← tWithLoadVar ctx binder fun ctx' => tExprToLeanExpr ctx' retMode k
    pure <| mkAppN (Lean.mkConst ``LeanQbe.T.Expr.load)
      #[ctx.V, ctx.L, ctx.rsExpr, tE, addrE, lamE]
  | .store t val addr k => do
    let tE ← liftEx (tTyToExpr ctx.tySplices t)
    let valE ← liftEx (tArgToExpr ctx val)
    let addrE ← liftEx (tArgToExpr ctx addr)
    let restE ← tExprToLeanExpr ctx retMode k
    pure <| mkAppN (Lean.mkConst ``LeanQbe.T.Expr.store)
      #[ctx.V, ctx.L, ctx.rsExpr, tE, valE, addrE, restE]
  | .call f as bs args binders k => do
    if let some cs := ctx.callSplices.find? (·.placeholderName == f) then
      match cs.kind with
      | .opCode opExpr sigExprs rsExprs =>
        let rsE := LeanQbe.T.Notation.listLit LeanQbe.T.Notation.tyConst rsExprs
        let sigE := LeanQbe.T.Notation.listLit LeanQbe.T.Notation.tyConst sigExprs
        let (_, argsE) ← liftEx (tArgListToTupExpr ctx args)
        let opE := mkAppN (Lean.mkConst ``LeanQbe.T.Op.mk) #[ctx.V, rsE, sigE, opExpr, argsE]
        let lamE ← tWithTupleLVars ctx binders fun ctx' => tExprToLeanExpr ctx' retMode k
        pure <| mkAppN (Lean.mkConst ``LeanQbe.T.Expr.let_)
          #[ctx.V, ctx.L, ctx.rsExpr, rsE, opE, lamE]
      | .cmpOp cmpExpr =>
        unless args.length == 2 do
          throwError "c0 template: CmpOp splice '{f}' requires 2 arguments"
        let tE ← liftEx (tTyToExpr ctx.tySplices args[0]!.ty)
        let maskApp := mkApp (Lean.mkConst ``LeanQbe.T.Ty.mask) tE
        let boolE := LeanQbe.T.Notation.boolTyExpr
        unless ← isDefEq boolE maskApp do
          throwError m!"c0 template: CmpOp needs `.mask = bool`, got:{indentExpr tE}"
        let rsE := LeanQbe.T.Notation.listLit LeanQbe.T.Notation.tyConst [boolE]
        let sigE := LeanQbe.T.Notation.listLit LeanQbe.T.Notation.tyConst [tE, tE]
        let codeE := mkApp4 (Lean.mkConst ``LeanQbe.T.OpCode.cmp) cmpExpr tE boolE
          (LeanQbe.T.Notation.mkMaskEqRefl boolE)
        let (_, argsE) ← liftEx (tArgListToTupExpr ctx args)
        let opE := mkAppN (Lean.mkConst ``LeanQbe.T.Op.mk) #[ctx.V, rsE, sigE, codeE, argsE]
        let lamE ← tWithTupleLVars ctx binders fun ctx' => tExprToLeanExpr ctx' retMode k
        pure <| mkAppN (Lean.mkConst ``LeanQbe.T.Expr.let_)
          #[ctx.V, ctx.L, ctx.rsExpr, rsE, opE, lamE]
      | .exprSnippet snipExpr _ _ =>
        unless binders.length == 1 do
          throwError "c0 template: expression snippet must bind 1 result"
        let (_, argsE) ← liftEx (tArgListToTupExpr ctx args)
        let lamE ← tWithLoadVar ctx binders[0]! fun ctx' => tExprToLeanExpr ctx' retMode k
        pure <| mkAppN snipExpr #[ctx.V, ctx.L, ctx.rsExpr, argsE, lamE]
      | .funcSnippet funcExpr asExprs rExpr =>
        unless binders.length == 1 do
          throwError "c0 template: function snippet must bind 1 result"
        let asE := LeanQbe.T.Notation.listLit LeanQbe.T.Notation.tyConst asExprs
        let (_, argsE) ← liftEx (tArgListToTupExpr ctx args)
        let snipApp := mkApp3 (Lean.mkConst ``LeanQbe.T.Frontend.C0.funcToExprSnippet)
          asE rExpr funcExpr
        let lamE ← tWithLoadVar ctx binders[0]! fun ctx' => tExprToLeanExpr ctx' retMode k
        pure <| mkAppN snipApp #[ctx.V, ctx.L, ctx.rsExpr, argsE, lamE]
      | .stmtSnippet snipExpr _ =>
        withMaterializedVars ctx args fun ctxM pairs => do
          let tsExprs := (pairs.map (·.2)).toList
          let initTup := LeanQbe.T.Notation.mkTupElems LeanQbe.T.Notation.tyConst ctxM.V
            tsExprs (pairs.map (·.1)).toList
          let contLam ← tWithTupleLVars ctxM binders fun ctx' =>
            tExprToLeanExpr ctx' retMode k
          pure <| mkAppN snipExpr #[ctxM.V, ctxM.L, ctxM.rsExpr, initTup, contLam]
    else if let some (valE, tyE) := ctx.valGetters.get? f then
      unless binders.length == 1 do
        throwError "c0 template: internal val getter expects 1 binder"
      let ctx' := { ctx with imms := ctx.imms.insert binders[0]!.id (valE, tyE) }
      tExprToLeanExpr ctx' retMode k
    else if let some (us, implLFn) := ctx.unrolls.get? f then
      let nState := us.stateVars.length
      let nRo := us.roVars.length
      let stateArgs := args.take nState
      let roArgs := args.drop nState
      withMaterializedVars ctx stateArgs fun ctxM statePairs => do
        let stateTyExprs := statePairs.toList.map (·.2)
        let stateListE := LeanQbe.T.Notation.listLit LeanQbe.T.Notation.tyConst stateTyExprs
        let initTup := LeanQbe.T.Notation.mkTupElems LeanQbe.T.Notation.tyConst ctxM.V
          stateTyExprs (statePairs.map (·.1)).toList
        let stepLam ← withLocalDeclD (Name.mkSimple us.elemName) us.elemTy fun elemFVar => do
          let tupTy := LeanQbe.T.Notation.mkTupTy LeanQbe.T.Notation.tyConst ctxM.V stateTyExprs
          let contTy := Lean.Expr.forallE `st' tupTy
            (mkApp3 (Lean.mkConst ``LeanQbe.T.Expr) ctxM.V ctxM.L ctxM.rsExpr) .default
          withLocalDeclD `st tupTy fun stFVar =>
          withLocalDeclD `ku contTy fun kuFVar => do
            let mut stepVars := ctxM.vars
            let mut stepImms := ctxM.imms
            let mut stepGetters := ctxM.valGetters
            let stateParams := implLFn.params.take nState
            let roParams := (implLFn.params.drop nState).take nRo
            let mut i := 0
            for (lv, tyE) in stateParams.zip stateTyExprs do
              let proj := LeanQbe.T.Notation.mkTypedProj LeanQbe.T.Notation.tyConst ctxM.V
                stateTyExprs stFVar i
              stepVars := stepVars.insert lv.id (proj, tyE)
              i := i + 1
            for (lv, rArg) in roParams.zip roArgs do
              match rArg with
              | .var oid _ =>
                if let some immEntry := ctxM.imms.get? oid then
                  stepImms := stepImms.insert lv.id immEntry
                else if let some varEntry := ctxM.vars.get? oid then
                  stepVars := stepVars.insert lv.id varEntry
                else
                  throwError "c0 template: unbound read-only variable id {oid} in #unroll"
              | .imm t v =>
                let tyE ← liftEx (tTyToExpr ctxM.tySplices t)
                let valE ← liftEx (tValToExpr ctxM.tySplices t v)
                stepImms := stepImms.insert lv.id (valE, tyE)
            for vs in us.bodyValSplices do
              let gName := s!"__c0tpl_vget_{us.uid}_{vs.placeholderName}"
              let substVal := vs.leanExpr.replaceFVarId us.elemFVarId elemFVar
              stepGetters := stepGetters.insert gName (substVal, vs.tyExpr)
            let stepCtx : TElabCtx := {
              ctxM with vars := stepVars, imms := stepImms, valGetters := stepGetters
            }
            let bodyExpr ← tExprToLeanExpr stepCtx (.stmtCont kuFVar stateTyExprs) implLFn.body
            let bodyExpr := bodyExpr.replaceFVarId us.elemFVarId elemFVar
            mkLambdaFVars #[elemFVar, stFVar, kuFVar] bodyExpr
        let restLam ← tWithTupleLVars ctxM binders fun ctx' => tExprToLeanExpr ctx' retMode k
        pure <| mkAppN (Lean.mkConst ``LeanQbe.T.Frontend.C0.c0UnrollK)
          #[us.elemTy, stateListE, ctxM.V, ctxM.L, ctxM.rsExpr, us.listExpr, stepLam,
            initTup, restLam]
    else
      let asE := LeanQbe.T.Notation.listLit LeanQbe.T.Notation.tyConst
        (← liftEx (as.mapM (tTyToExpr ctx.tySplices)))
      let bsE := LeanQbe.T.Notation.listLit LeanQbe.T.Notation.tyConst
        (← liftEx (bs.mapM (tTyToExpr ctx.tySplices)))
      let (_, argsE) ← liftEx (tArgListToTupExpr ctx args)
      let lamE ← tWithTupleLVars ctx binders fun ctx' => tExprToLeanExpr ctx' retMode k
      pure <| mkAppN (Lean.mkConst ``LeanQbe.T.Expr.call)
        #[ctx.V, ctx.L, ctx.rsExpr, mkStrLit f, asE, bsE, argsE, lamE]
  | .jnz c t e => do
    let cE ← liftEx (tArgToExpr ctx c)
    let tE ← tExprToLeanExpr ctx retMode t
    let eE ← tExprToLeanExpr ctx retMode e
    pure <| mkAppN (Lean.mkConst ``LeanQbe.T.Expr.jnz) #[ctx.V, ctx.L, ctx.rsExpr, cE, tE, eE]
  | .jump lid _ args => do
    let some (lRef, tsE) := ctx.lbls.get? lid
      | throwError "c0 template: unbound label id {lid}"
    let (_, argsE) ← liftEx (tArgListToTupExpr ctx args)
    pure <| mkAppN (Lean.mkConst ``LeanQbe.T.Expr.jump)
      #[ctx.V, ctx.L, ctx.rsExpr, tsE, lRef, argsE]
  | .ret _ args => do
    match retMode with
    | .normalRet =>
      let (_, vsE) ← liftEx (tArgListToTupExpr ctx args)
      pure <| mkAppN (Lean.mkConst ``LeanQbe.T.Expr.ret) #[ctx.V, ctx.L, ctx.rsExpr, vsE]
    | .exprCont contFV =>
      withMaterializedVars ctx args fun _ pairs => do
        unless pairs.size == 1 do
          throwError "c0_expr_template!: expected single return value"
        pure <| mkApp contFV pairs[0]!.1
    | .stmtCont contFV stateTyExprs =>
      withMaterializedVars ctx args fun ctxM pairs => do
        let tup := LeanQbe.T.Notation.mkTupElems LeanQbe.T.Notation.tyConst ctxM.V
          stateTyExprs (pairs.map (·.1)).toList
        pure <| mkApp contFV tup
  | .exit f as args => do
    let asE := LeanQbe.T.Notation.listLit LeanQbe.T.Notation.tyConst
      (← liftEx (as.mapM (tTyToExpr ctx.tySplices)))
    let (_, argsE) ← liftEx (tArgListToTupExpr ctx args)
    pure <| mkAppN (Lean.mkConst ``LeanQbe.T.Expr.exit)
      #[ctx.V, ctx.L, ctx.rsExpr, mkStrLit f, asE, argsE]
  | .hlt =>
    pure <| mkApp3 (Lean.mkConst ``LeanQbe.T.Expr.hlt) ctx.V ctx.L ctx.rsExpr
  | .group blocks k => do
    let sigList ← liftEx <| blocks.mapM fun (_, ps, _) => do
      let ts ← ps.mapM fun v => tTyToExpr ctx.tySplices v.ty
      pure (LeanQbe.T.Notation.listLit LeanQbe.T.Notation.tyConst ts)
    let sigE := LeanQbe.T.Notation.listLit LeanQbe.T.Notation.listTyConst sigList
    let bodiesLam ← tWithGroupLabels ctx blocks fun ctx' => mkBlocksExpr ctx' blocks
    let entryLam ← tWithGroupLabels ctx blocks fun ctx' => tExprToLeanExpr ctx' retMode k
    pure <| mkAppN (Lean.mkConst ``LeanQbe.T.Expr.group)
      #[ctx.V, ctx.L, ctx.rsExpr, sigE, bodiesLam, entryLam]
where
  mkBlocksExpr (c : TElabCtx) : List (Nat × List LVar × LExpr) → MetaM Lean.Expr
    | [] => pure <| mkApp3 (Lean.mkConst ``LeanQbe.T.Blocks.nil) c.V c.L c.rsExpr
    | (_, ps, body) :: rest => do
      let tsE := LeanQbe.T.Notation.listLit LeanQbe.T.Notation.tyConst
        (← liftEx (ps.mapM fun v => tTyToExpr c.tySplices v.ty))
      let restSigE := LeanQbe.T.Notation.listLit LeanQbe.T.Notation.listTyConst
        (← liftEx (rest.mapM fun (_, rps, _) => do
          let ts ← rps.mapM fun v => tTyToExpr c.tySplices v.ty
          pure (LeanQbe.T.Notation.listLit LeanQbe.T.Notation.tyConst ts)))
      let bLam ← tWithTupleLVars c ps fun c' => tExprToLeanExpr c' retMode body
      let bsE ← mkBlocksExpr c rest
      pure <| mkAppN (Lean.mkConst ``LeanQbe.T.Blocks.cons)
        #[c.V, c.L, c.rsExpr, tsE, restSigE, bLam, bsE]

/-! ## Top-Level Template Compilation Pipeline -/

private inductive TemplateTargetKind
  | fnTemplate
  | exprTemplate
  | stmtTemplate
  deriving BEq

private def elabC0TemplateCore (stxRef : Syntax) (src : String) (kind : TemplateTargetKind) :
    TermElabM Lean.Expr := do
  let (scannedSrc, scanEnv0) ← (scanTemplateSrc stxRef src).run {}
  let preamble ← buildPreamble scanEnv0
  let fullSrc := preamble ++ scannedSrc
  let headers := getC0Headers (← getEnv)
  let tu0 ← match parseC0 fullSrc headers with
    | .ok tu => pure tu
    | .error err => throwErrorAt stxRef err
  let mut unrollList : Array UnrollSplice := #[]
  for us in scanEnv0.unrolls do
    let wrapSrc := preamble ++ s!"void __c0tpl_wrap_{us.uid}(void) \{\n{us.bodyDeclsSrc}\n}"
    let bodyTu ← match parseC0 wrapSrc headers with
      | .ok tu => pure tu
      | .error err => throwErrorAt stxRef s!"c0 template #unroll body parse error: {err}"
    let bodyFn ← match bodyTu.decls.reverse.findSome?
        fun | .fnDef fd => some fd | _ => none with
      | some fd => pure fd
      | none => throwErrorAt stxRef "c0 template #unroll internal error"
    if bodyFn.body.any stmtHasControlExit then
      throwErrorAt stxRef
        "c0 template: #unroll body cannot contain `return`, `break`, `continue`, or `goto`"
    unrollList := unrollList.push { us with bodyStmts := bodyFn.body }
  let decls0 := patchTyTypedefs scanEnv0.tySplices tu0.decls
  let tuTmp : TranslationUnit := { decls := decls0 }
  let layout ← match buildLayoutEnv tuTmp with
    | .ok l => pure l
    | .error err => throwErrorAt stxRef err
  let mut enumMap : Std.HashMap String Int := {}
  let mut fnRets : Std.HashMap String C0Type := {}
  for d in decls0 do
    match d with
    | .enumConsts items =>
      for (nm, v) in items do enumMap := enumMap.insert nm v
    | .fnDecl sg => fnRets := fnRets.insert sg.name sg.retTy
    | .fnDef fd => fnRets := fnRets.insert fd.name fd.retTy
    | _ => pure ()
  let fnDefs := decls0.filterMap fun | .fnDef fd => some fd | _ => none
  let some targetFd0 :=
      (fnDefs.reverse.find? (fun f => !(f.isStatic && f.isInline))) <|> fnDefs.getLast?
    | throwErrorAt stxRef "c0 template: expected a C0 function definition"
  let mut valSplices := scanEnv0.valSplices
  let (bodyNat, valSplices1) ← match ((targetFd0.body.mapM
      (rewriteNatCastsInStmt scanEnv0.tySplices layout)).run valSplices) with
    | .ok p => pure p
    | .error err => throwErrorAt stxRef err
  valSplices := valSplices1
  let bodyStmtS ← match bodyNat.mapM (rewriteStmtSnippetCallsInStmt scanEnv0.callSplices) with
    | .ok bs => pure bs
    | .error err => throwErrorAt stxRef err
  let mut targetFd : FnDef := { targetFd0 with body := bodyStmtS }
  if kind == .stmtTemplate then
    if targetFd.body.any stmtHasControlExit then
      throwErrorAt stxRef
        "c0_stmt_template!: body cannot contain `return`, `break`, `continue`, or `goto`"
    let stateRetTy : C0Type := match targetFd.params with
      | [] => .void
      | [(t, _)] => t
      | ps => .tuple (ps.map (·.1))
    let retVars := targetFd.params.map fun (_, nm) => LeanQbe.T.Frontend.C0.Expr.var nm
    targetFd := {
      targetFd with
      retTy := stateRetTy
      body := targetFd.body ++ [.retStmt retVars]
    }
  let mut extraDecls : List Decl := []
  let mut resolvedUnrolls : Array UnrollSplice := #[]
  for us in unrollList do
    let (uBodyNat, uValSplices) ← match ((us.bodyStmts.mapM
        (rewriteNatCastsInStmt scanEnv0.tySplices layout)).run us.bodyValSplices) with
      | .ok p => pure p
      | .error err => throwErrorAt stxRef err
    let uBodyStmtS ← match uBodyNat.mapM (rewriteStmtSnippetCallsInStmt scanEnv0.callSplices) with
      | .ok bs => pure bs
      | .error err => throwErrorAt stxRef err
    let initScope := targetFd.params.map fun (t, nm) => (nm, t)
    let some (_, scopeVars) := findCallWithScope us.markName initScope targetFd.body
      | throwErrorAt stxRef s!"c0 template: internal #unroll marker '{us.markName}' not found"
    let mutSet := stmtMutatedLocals false false (.block uBodyStmtS)
    let stateVars := scopeVars.filter fun (nm, _) => mutSet.contains nm
    let usedInBody := (uBodyStmtS.flatMap collectStmtVars).foldl
      (fun s n => s.insert n) ({} : Std.HashSet String)
    let roVars := scopeVars.filter fun (nm, _) => !mutSet.contains nm && usedInBody.contains nm
    targetFd := {
      targetFd with
      body := targetFd.body.map (rewriteUnrollMarkInStmt us.markName us.implName stateVars roVars)
    }
    let stateRetTy : C0Type := match stateVars with
      | [] => .void
      | [(_, t)] => t
      | ps => .tuple (ps.map (·.2))
    let implSig : FnSig := {
      retTy := stateRetTy
      name := us.implName
      params := (stateVars ++ roVars).map fun (nm, t) => (t, some nm)
    }
    let implParams := (stateVars ++ roVars).map (fun (nm, t) => (t, nm))
    let retExprs := stateVars.map fun (nm, _) => LeanQbe.T.Frontend.C0.Expr.var nm
    let activeVals := uValSplices.toList.filter fun vs => usedInBody.contains vs.placeholderName
    let mut valDecls : List Decl := []
    let mut valInits : List Stmt := []
    for vs in activeVals do
      let gName := s!"__c0tpl_vget_{us.uid}_{vs.placeholderName}"
      fnRets := fnRets.insert gName vs.c0Ty
      valDecls := valDecls ++ [.fnDecl { retTy := vs.c0Ty, name := gName, params := [] }]
      valInits := valInits ++ [.decl vs.c0Ty vs.placeholderName (.expr (.call gName []))]
    let implFd : FnDef := {
      retTy := stateRetTy
      name := us.implName
      params := implParams
      body := valInits ++ uBodyStmtS ++ [.retStmt retExprs]
    }
    fnRets := fnRets.insert us.implName stateRetTy
    extraDecls := extraDecls ++ valDecls ++ [.fnDecl implSig, .fnDef implFd]
    resolvedUnrolls := resolvedUnrolls.push {
      us with bodyStmts := uBodyStmtS, bodyValSplices := uValSplices, stateVars, roVars
    }
  let allBodies : List (List (String × C0Type) × List Stmt) :=
    [(targetFd.params.map fun (t, nm) => (nm, t), targetFd.body)] ++
    (extraDecls.filterMap fun
      | .fnDef fd => some (fd.params.map fun (t, nm) => (nm, t), fd.body)
      | _ => none)
  let mut cmpParamMap : Std.HashMap String (List (C0Type × Option String)) := {}
  for cs in scanEnv0.callSplices do
    if let .cmpOp _ := cs.kind then
      let found? := allBodies.findSome? fun (initScope, stmts) =>
        findCallWithScope cs.placeholderName initScope stmts
      let some (cargs, scope) := found?
        | throwErrorAt stxRef s!"c0 template: unused comparator splice '{cs.placeholderName}'"
      unless cargs.length == 2 do
        throwErrorAt stxRef "c0 template: `CmpOp` splice requires exactly 2 arguments"
      let allVals := valSplices ++ resolvedUnrolls.foldl (fun a u => a ++ u.bodyValSplices) #[]
      let commonTy ← match inferCallArgCommonType layout enumMap fnRets scope allVals
          cargs[0]! cargs[1]! with
        | .ok t => pure t
        | .error err => throwErrorAt stxRef err
      cmpParamMap := cmpParamMap.insert cs.placeholderName [(commonTy, none), (commonTy, none)]
  let targetFdWithVals := appendValPlaceholders targetFd valSplices
  let patchedDecls : List Decl := (decls0.map fun
    | .fnDecl sg =>
      match cmpParamMap.get? sg.name with
      | some ps => .fnDecl { sg with params := ps }
      | none => .fnDecl sg
    | .fnDef fd =>
      if fd.name == targetFd0.name then .fnDef targetFdWithVals else .fnDef fd
    | d => d) ++ extraDecls
  let lmod ← match lowerTranslationUnit { decls := patchedDecls } with
    | .ok m => pure m
    | .error err => throwErrorAt stxRef err
  let some mainLFn := lmod.fns.find? (·.name == targetFdWithVals.name)
    | throwErrorAt stxRef "c0 template: lowered target function missing"
  let mut unrollMap : Std.HashMap String (UnrollSplice × LFn) := {}
  for us in resolvedUnrolls do
    if let some lfn := lmod.fns.find? (·.name == us.implName) then
      unrollMap := unrollMap.insert us.implName (us, lfn)
  let nOrigParams := targetFd0.params.length
  let origParams := mainLFn.params.take nOrigParams
  let valPlaceholderLVs := mainLFn.params.drop nOrigParams
  let tySplices := scanEnv0.tySplices
  let asExprs ← liftEx (origParams.mapM fun v => tTyToExpr tySplices v.ty)
  let rsExprs ← liftEx (mainLFn.rs.mapM (tTyToExpr tySplices))
  let rsListE := LeanQbe.T.Notation.listLit LeanQbe.T.Notation.tyConst rsExprs
  let vSort := Lean.Expr.forallE `t LeanQbe.T.Notation.tyConst (.sort 1) .default
  let lSort := Lean.Expr.forallE `ts LeanQbe.T.Notation.listTyConst (.sort 1) .default
  let resExpr ← withLocalDeclD `V vSort fun V =>
    withLocalDeclD `L lSort fun L => do
      let mut baseImms : Std.HashMap Nat (Lean.Expr × Lean.Expr) := {}
      for lv in valPlaceholderLVs do
        let some vs := valSplices.find? (·.placeholderName == lv.name)
          | throwErrorAt stxRef s!"c0 template: internal val placeholder '{lv.name}' mismatch"
        let tyE ← liftEx (tTyToExpr tySplices lv.ty)
        baseImms := baseImms.insert lv.id (vs.leanExpr, tyE)
      match kind with
      | .fnTemplate =>
        let ctx0 : TElabCtx := {
          V, L, rsExpr := rsListE, imms := baseImms
          tySplices, callSplices := scanEnv0.callSplices, unrolls := unrollMap
        }
        let bodyLam ← tWithTupleLVars ctx0 origParams fun ctx' =>
          tExprToLeanExpr ctx' .normalRet mainLFn.body
        mkLambdaFVars #[V, L] bodyLam
      | .exprTemplate =>
        unless rsExprs.length == 1 do
          throwErrorAt stxRef "c0_expr_template!: function must return exactly 1 value"
        let rE := rsExprs[0]!
        let listTy := LeanQbe.T.Notation.listTyConst
        withLocalDeclD `rs listTy fun rsFV => do
          let tupArgTy := LeanQbe.T.Notation.mkTupTy LeanQbe.T.Notation.tyConst
            (LeanQbe.T.Notation.mkArgApp V) asExprs
          let contTy := Lean.Expr.forallE `res (mkApp V rE)
            (mkApp3 (Lean.mkConst ``LeanQbe.T.Expr) V L rsFV) .default
          withLocalDeclD `args tupArgTy fun argsFV =>
          withLocalDeclD `k contTy fun kFV => do
            let argF := LeanQbe.T.Notation.mkArgApp V
            let ctxBase : TElabCtx := {
              V, L, rsExpr := rsFV, imms := baseImms
              tySplices, callSplices := scanEnv0.callSplices, unrolls := unrollMap
            }
            let inputs := (origParams.zip asExprs).zipIdx.map fun ((lv, tyE), idx) =>
              (lv, tyE, LeanQbe.T.Notation.mkTypedProj LeanQbe.T.Notation.tyConst argF
                asExprs argsFV idx)
            let rec bindArgInputs (c : TElabCtx) :
                List (LVar × Lean.Expr × Lean.Expr) → MetaM Lean.Expr
              | [] => tExprToLeanExpr c (.exprCont kFV) mainLFn.body
              | (lv, tyE, argProj) :: rest => do
                let matApp := mkAppN (Lean.mkConst ``LeanQbe.T.Frontend.C0.materializeArg)
                  #[V, L, rsFV, tyE, argProj]
                let vTy := mkApp V tyE
                let lam ← withLocalDeclD (Name.mkSimple lv.name) vTy fun vFV => do
                  let c' := { c with vars := c.vars.insert lv.id (vFV, tyE) }
                  mkLambdaFVars #[vFV] (← bindArgInputs c' rest)
                pure (mkApp matApp lam)
            let body ← bindArgInputs ctxBase inputs
            mkLambdaFVars #[V, L, rsFV, argsFV, kFV] body
      | .stmtTemplate =>
        let listTy := LeanQbe.T.Notation.listTyConst
        withLocalDeclD `rs listTy fun rsFV => do
          let tupTy := LeanQbe.T.Notation.mkTupTy LeanQbe.T.Notation.tyConst V asExprs
          let contTy := Lean.Expr.forallE `st' tupTy
            (mkApp3 (Lean.mkConst ``LeanQbe.T.Expr) V L rsFV) .default
          withLocalDeclD `st tupTy fun stFV =>
          withLocalDeclD `k contTy fun kFV => do
            let mut vars : Std.HashMap Nat (Lean.Expr × Lean.Expr) := {}
            let mut i := 0
            for (lv, tyE) in origParams.zip asExprs do
              let proj := LeanQbe.T.Notation.mkTypedProj LeanQbe.T.Notation.tyConst V asExprs
                stFV i
              vars := vars.insert lv.id (proj, tyE)
              i := i + 1
            let ctx0 : TElabCtx := {
              V, L, rsExpr := rsFV, vars, imms := baseImms
              tySplices, callSplices := scanEnv0.callSplices, unrolls := unrollMap
            }
            let body ← tExprToLeanExpr ctx0 (.stmtCont kFV asExprs) mainLFn.body
            mkLambdaFVars #[V, L, rsFV, stFV, kFV] body
  Meta.check resExpr
  pure resExpr

declare_syntax_cat c0_tpl_binder
syntax "(" ident+ " : " term ")" : c0_tpl_binder
syntax "{" ident+ " : " term "}" : c0_tpl_binder

private partial def elabTplBinders
    (bs : List (TSyntax `c0_tpl_binder)) (k : TermElabM Lean.Expr) : TermElabM Lean.Expr := do
  match bs with
  | [] => k
  | b :: rest =>
    match b with
    | `(c0_tpl_binder| ($ids:ident* : $tyStx:term)) =>
      let tyE ← Term.elabType tyStx
      let rec goExpIds (is : List Ident) (fvs : Array Lean.Expr) : TermElabM Lean.Expr := do
        match is with
        | [] =>
          let inner ← elabTplBinders rest k
          mkLambdaFVars fvs inner
        | id :: is' =>
          withLocalDeclD id.getId tyE fun fv => goExpIds is' (fvs.push fv)
      goExpIds ids.toList #[]
    | `(c0_tpl_binder| {$ids:ident* : $tyStx:term}) =>
      let tyE ← Term.elabType tyStx
      let rec goImpIds (is : List Ident) (fvs : Array Lean.Expr) : TermElabM Lean.Expr := do
        match is with
        | [] =>
          let inner ← elabTplBinders rest k
          mkLambdaFVars fvs inner
        | id :: is' =>
          withLocalDecl id.getId .implicit tyE fun fv => goImpIds is' (fvs.push fv)
      goImpIds ids.toList #[]
    | _ => throwErrorAt b "c0 template: invalid binder"

/-- Elaborate a C0 function template statically into a Lean `Func`. -/
syntax "c0_fn_template! " str : term
/-- Elaborate a C0 function template with Lean binders statically into a Lean lambda. -/
syntax "c0_fn_template! " c0_tpl_binder+ " => " str : term

/-- Elaborate a C0 expression/comparator snippet statically into a `C0ExprSnippet`. -/
syntax "c0_expr_template! " str : term
/-- Elaborate a C0 expression snippet with Lean binders statically into a Lean lambda. -/
syntax "c0_expr_template! " c0_tpl_binder+ " => " str : term

/-- Elaborate a C0 statement block statically into a `C0StmtSnippet`. -/
syntax "c0_stmt_template! " str : term
/-- Elaborate a C0 statement block with Lean binders statically into a Lean lambda. -/
syntax "c0_stmt_template! " c0_tpl_binder+ " => " str : term

elab_rules : term
  | `(c0_fn_template! $src:str) => elabC0TemplateCore src src.getString .fnTemplate
  | `(c0_fn_template! $bs:c0_tpl_binder* => $src:str) =>
    elabTplBinders bs.toList (elabC0TemplateCore src src.getString .fnTemplate)
  | `(c0_expr_template! $src:str) => elabC0TemplateCore src src.getString .exprTemplate
  | `(c0_expr_template! $bs:c0_tpl_binder* => $src:str) =>
    elabTplBinders bs.toList (elabC0TemplateCore src src.getString .exprTemplate)
  | `(c0_stmt_template! $src:str) => elabC0TemplateCore src src.getString .stmtTemplate
  | `(c0_stmt_template! $bs:c0_tpl_binder* => $src:str) =>
    elabTplBinders bs.toList (elabC0TemplateCore src src.getString .stmtTemplate)

end LeanQbe.T.Frontend.C0

end
