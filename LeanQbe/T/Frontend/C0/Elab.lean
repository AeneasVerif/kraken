module

public import LeanQbe.T.Frontend.C0.Syntax
public import LeanQbe.T.Frontend.C0.Parser
public import LeanQbe.T.Frontend.C0.Layout
public import LeanQbe.T.Frontend.C0.Lower
public import LeanQbe.T.Notation
public meta import LeanQbe.T.Frontend.C0.Syntax
public meta import LeanQbe.T.Frontend.C0.Parser
public meta import LeanQbe.T.Frontend.C0.Layout
public meta import LeanQbe.T.Frontend.C0.Lower
public meta import LeanQbe.T.Notation
public meta import Lean.Elab.Command

/-!
# C0 Direct PHOAS Elaborator, `c0_decl!`, `c0_file!`, and `#c0_shape` (`X0-core`)

Elaborates lowered C0 functions (`LFn`) directly into kernel `LeanQbe.T.Fn` definitions using
projection lambdas (`Prod.fst`/`Prod.snd`) and explicit `Op.mk` applications (`Notation.lean` `#29`),
checks acyclic `Module` ordering, and registers `#c0_shape` metadata for proof authors.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Frontend.C0

open Lean Elab Command Term Meta
open LeanQbe.T
open LeanQbe.T.Notation

/-! ## `#c0_shape` Environment Extension -/

meta initialize c0ShapeExt : SimpleScopedEnvExtension (Name × FnShape) (NameMap FnShape × Std.HashMap String FnShape) ←
  registerSimpleScopedEnvExtension {
    name := `LeanQbe.T.Frontend.C0.c0ShapeExt
    initial := ({}, {})
    addEntry := fun (byLean, byC) (nm, sh) => (byLean.insert nm sh, byC.insert sh.name sh)
  }

/-! ## Direct PHOAS `Lean.Expr` Builder from `LExpr` -/

meta def tyToExpr : Ty → Lean.Expr
  | .bool => boolTyExpr
  | .bits 8 => i8TyExpr
  | .bits 16 => i16TyExpr
  | .bits 32 => i32TyExpr
  | .bits 64 => i64TyExpr
  | .bits n => mkApp (Lean.mkConst ``LeanQbe.T.Ty.bits) (mkNatLit n)
  | .float f => mkFloatTy f
  | .pair a b => mkPairTy (tyToExpr a) (tyToExpr b)

meta def valToExpr : (t : Ty) → Val t → Lean.Expr
  | .bool, true => Lean.mkConst ``Bool.true
  | .bool, false => Lean.mkConst ``Bool.false
  | .bits n, v => bvNatLit (mkNatLit n) v.toNat
  | .float f, v => bvNatLit (mkNatLit f.width) v.toNat
  | .pair a b, (va, vb) =>
    let ta := mkApp (Lean.mkConst ``LeanQbe.T.Val) (tyToExpr a)
    let tb := mkApp (Lean.mkConst ``LeanQbe.T.Val) (tyToExpr b)
    mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero]) ta tb (valToExpr a va) (valToExpr b vb)

meta def cmpOpToExpr : CmpOp → Lean.Expr
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

meta def fcmpOpToExpr : FCmpOp → Lean.Expr
  | .eq => Lean.mkConst ``LeanQbe.T.FCmpOp.eq
  | .ne => Lean.mkConst ``LeanQbe.T.FCmpOp.ne
  | .lt => Lean.mkConst ``LeanQbe.T.FCmpOp.lt
  | .le => Lean.mkConst ``LeanQbe.T.FCmpOp.le
  | .gt => Lean.mkConst ``LeanQbe.T.FCmpOp.gt
  | .ge => Lean.mkConst ``LeanQbe.T.FCmpOp.ge
  | .ord => Lean.mkConst ``LeanQbe.T.FCmpOp.ord
  | .uno => Lean.mkConst ``LeanQbe.T.FCmpOp.uno

meta def opCodeToExpr {sig rs : List Ty} : OpCode sig rs → Except String Lean.Expr
  | .copy t => pure <| mkApp (Lean.mkConst ``LeanQbe.T.OpCode.copy) (tyToExpr t)
  | .add t => pure <| mkApp (Lean.mkConst ``LeanQbe.T.OpCode.add) (tyToExpr t)
  | .sub t => pure <| mkApp (Lean.mkConst ``LeanQbe.T.OpCode.sub) (tyToExpr t)
  | .mul t => pure <| mkApp (Lean.mkConst ``LeanQbe.T.OpCode.mul) (tyToExpr t)
  | .neg t => pure <| mkApp (Lean.mkConst ``LeanQbe.T.OpCode.neg) (tyToExpr t)
  | .and t => pure <| mkApp (Lean.mkConst ``LeanQbe.T.OpCode.and) (tyToExpr t)
  | .or t => pure <| mkApp (Lean.mkConst ``LeanQbe.T.OpCode.or) (tyToExpr t)
  | .xor t => pure <| mkApp (Lean.mkConst ``LeanQbe.T.OpCode.xor) (tyToExpr t)
  | .not t => pure <| mkApp (Lean.mkConst ``LeanQbe.T.OpCode.not) (tyToExpr t)
  | .shl t => pure <| mkApp (Lean.mkConst ``LeanQbe.T.OpCode.shl) (tyToExpr t)
  | .lshr t => pure <| mkApp (Lean.mkConst ``LeanQbe.T.OpCode.lshr) (tyToExpr t)
  | .ashr t => pure <| mkApp (Lean.mkConst ``LeanQbe.T.OpCode.ashr) (tyToExpr t)
  | .rotl t => pure <| mkApp (Lean.mkConst ``LeanQbe.T.OpCode.rotl) (tyToExpr t)
  | .rotr t => pure <| mkApp (Lean.mkConst ``LeanQbe.T.OpCode.rotr) (tyToExpr t)
  | .clz n => pure <| mkApp (Lean.mkConst ``LeanQbe.T.OpCode.clz) (mkNatLit n)
  | .ctz n => pure <| mkApp (Lean.mkConst ``LeanQbe.T.OpCode.ctz) (mkNatLit n)
  | .popcnt n => pure <| mkApp (Lean.mkConst ``LeanQbe.T.OpCode.popcnt) (mkNatLit n)
  | .cmp o t m _ =>
    let te := tyToExpr t
    let me := tyToExpr m
    pure <| mkApp4 (Lean.mkConst ``LeanQbe.T.OpCode.cmp) (cmpOpToExpr o) te me (mkMaskEqRefl me)
  | .zext m n => pure <| mkApp2 (Lean.mkConst ``LeanQbe.T.OpCode.zext) (mkNatLit m) (mkNatLit n)
  | .sext m n => pure <| mkApp2 (Lean.mkConst ``LeanQbe.T.OpCode.sext) (mkNatLit m) (mkNatLit n)
  | .trunc m n => pure <| mkApp2 (Lean.mkConst ``LeanQbe.T.OpCode.trunc) (mkNatLit m) (mkNatLit n)
  | .ofBool n => pure <| mkApp (Lean.mkConst ``LeanQbe.T.OpCode.ofBool) (mkNatLit n)
  | .addc n => pure <| mkApp (Lean.mkConst ``LeanQbe.T.OpCode.addc) (mkNatLit n)
  | .subb n => pure <| mkApp (Lean.mkConst ``LeanQbe.T.OpCode.subb) (mkNatLit n)
  | .umulw n => pure <| mkApp (Lean.mkConst ``LeanQbe.T.OpCode.umulw) (mkNatLit n)
  | .udiv n => pure <| mkApp (Lean.mkConst ``LeanQbe.T.OpCode.udiv) (mkNatLit n)
  | .sdiv n => pure <| mkApp (Lean.mkConst ``LeanQbe.T.OpCode.sdiv) (mkNatLit n)
  | .urem n => pure <| mkApp (Lean.mkConst ``LeanQbe.T.OpCode.urem) (mkNatLit n)
  | .srem n => pure <| mkApp (Lean.mkConst ``LeanQbe.T.OpCode.srem) (mkNatLit n)
  | .bitcast t u _ =>
    let eqPf := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) (Lean.mkConst ``Nat) (mkNatLit t.size)
    pure <| mkApp3 (Lean.mkConst ``LeanQbe.T.OpCode.bitcast) (tyToExpr t) (tyToExpr u) eqPf
  | .fadd t => pure <| mkApp (Lean.mkConst ``LeanQbe.T.OpCode.fadd) (tyToExpr t)
  | .fsub t => pure <| mkApp (Lean.mkConst ``LeanQbe.T.OpCode.fsub) (tyToExpr t)
  | .fmul t => pure <| mkApp (Lean.mkConst ``LeanQbe.T.OpCode.fmul) (tyToExpr t)
  | .fdiv t => pure <| mkApp (Lean.mkConst ``LeanQbe.T.OpCode.fdiv) (tyToExpr t)
  | .fneg t => pure <| mkApp (Lean.mkConst ``LeanQbe.T.OpCode.fneg) (tyToExpr t)
  | .fcmp o t m _ =>
    let te := tyToExpr t
    let me := tyToExpr m
    pure <| mkApp4 (Lean.mkConst ``LeanQbe.T.OpCode.fcmp) (fcmpOpToExpr o) te me (mkMaskEqRefl me)
  | .fptoui f n => pure <| mkApp2 (Lean.mkConst ``LeanQbe.T.OpCode.fptoui) (fmtConst f) (mkNatLit n)
  | .fptosi f n => pure <| mkApp2 (Lean.mkConst ``LeanQbe.T.OpCode.fptosi) (fmtConst f) (mkNatLit n)
  | .uitofp n f => pure <| mkApp2 (Lean.mkConst ``LeanQbe.T.OpCode.uitofp) (mkNatLit n) (fmtConst f)
  | .sitofp n f => pure <| mkApp2 (Lean.mkConst ``LeanQbe.T.OpCode.sitofp) (mkNatLit n) (fmtConst f)
  | _ => throw "unsupported OpCode in C0 elaborator"

meta structure ElabCtx : Type where
  V : Lean.Expr
  L : Lean.Expr
  rsExpr : Lean.Expr
  depth : Nat := 0
  vars : Std.HashMap Nat (Nat × Option (Nat × Lean.Expr × Lean.Expr × List Lean.Expr) × Lean.Expr) := {}
  lbls : Std.HashMap Nat (Nat × Option (Nat × Lean.Expr × Lean.Expr × List Lean.Expr) × Lean.Expr) := {}

meta def ElabCtx.varRef (ctx : ElabCtx) (id : Nat) : Except String Lean.Expr :=
  match ctx.vars.get? id with
  | some (lvl, proj?, _) =>
    let base := Lean.Expr.bvar (ctx.depth - 1 - lvl)
    pure <| match proj? with
      | none => base
      | some (i, kind, f, tys) => mkTypedProj kind f tys base i
  | none => throw s!"C0 elab: unbound variable id {id}"

meta def ElabCtx.lblRef (ctx : ElabCtx) (lid : Nat) : Except String (Lean.Expr × Lean.Expr) :=
  match ctx.lbls.get? lid with
  | some (lvl, proj?, sigExpr) =>
    let base := Lean.Expr.bvar (ctx.depth - 1 - lvl)
    let r := match proj? with
      | none => base
      | some (i, kind, f, tys) => mkTypedProj kind f tys base i
    pure (r, sigExpr)
  | none => throw s!"C0 elab: unbound label id {lid}"

meta def argToExpr (ctx : ElabCtx) (a : LArg) : Except String Lean.Expr := do
  let tyE := tyToExpr a.ty
  match a with
  | .var id _ =>
    let vRef ← ctx.varRef id
    pure <| mkApp3 (Lean.mkConst ``LeanQbe.T.Arg.var) ctx.V tyE vRef
  | .imm t v =>
    pure <| mkApp3 (Lean.mkConst ``LeanQbe.T.Arg.imm) ctx.V tyE (valToExpr t v)

meta def argListToTupExpr (ctx : ElabCtx) (args : List LArg) : Except String Lean.Expr := do
  let argF := mkArgApp ctx.V
  let tys := args.map fun a => tyToExpr a.ty
  let vals ← args.mapM (argToExpr ctx)
  pure (mkTupElems tyConst argF tys vals)

meta def withLoadVar (ctx : ElabCtx) (lv : LVar) (k : ElabCtx → Except String Lean.Expr) :
    Except String Lean.Expr := do
  let lvl := ctx.depth
  let tyE := tyToExpr lv.ty
  let vTy := mkApp ctx.V tyE
  let ctx' := {
    ctx with
    depth := ctx.depth + 1
    vars := ctx.vars.insert lv.id (lvl, none, tyE)
  }
  let body ← k ctx'
  pure (.lam (Name.mkSimple lv.name) vTy body .default)

meta def withTupleLVars (ctx : ElabCtx) (lvs : List LVar) (k : ElabCtx → Except String Lean.Expr) :
    Except String Lean.Expr := do
  let lvl := ctx.depth
  let elemTys := lvs.map fun v => tyToExpr v.ty
  let tupTy := mkTupTy tyConst ctx.V elemTys
  let mut vars := ctx.vars
  let mut i := 0
  for lv in lvs do
    let proj := some (i, tyConst, ctx.V, elemTys)
    vars := vars.insert lv.id (lvl, proj, tyToExpr lv.ty)
    i := i + 1
  let ctx' := { ctx with depth := ctx.depth + 1, vars }
  let body ← k ctx'
  pure (.lam `p tupTy body .default)

meta def withGroupLabelsL (ctx : ElabCtx) (blocks : List (Nat × List LVar × LExpr))
    (k : ElabCtx → Except String Lean.Expr) : Except String Lean.Expr := do
  let lvl := ctx.depth
  let elemTys := blocks.map fun (_, ps, _) => listLit tyConst (ps.map fun v => tyToExpr v.ty)
  let tupTy := mkTupTy listTyConst ctx.L elemTys
  let mut lbls := ctx.lbls
  let mut j := 0
  for (lid, ps, _) in blocks do
    let sigE := listLit tyConst (ps.map fun v => tyToExpr v.ty)
    let proj := some (j, listTyConst, ctx.L, elemTys)
    lbls := lbls.insert lid (lvl, proj, sigE)
    j := j + 1
  let ctx' := { ctx with depth := ctx.depth + 1, lbls }
  let body ← k ctx'
  pure (.lam `Js tupTy body .default)

meta partial def lExprToLeanExpr (ctx : ElabCtx) : LExpr → Except String Lean.Expr
  | .let_ op binders k => do
    let rsE := listLit tyConst (op.rs.map tyToExpr)
    let sigE := listLit tyConst (op.sig.map tyToExpr)
    let codeE ← opCodeToExpr op.code
    let argsE ← argListToTupExpr ctx op.args
    let opE := mkAppN (Lean.mkConst ``LeanQbe.T.Op.mk) #[ctx.V, rsE, sigE, codeE, argsE]
    let lamE ← withTupleLVars ctx binders fun ctx' => lExprToLeanExpr ctx' k
    pure <| mkAppN (Lean.mkConst ``LeanQbe.T.Expr.let_) #[ctx.V, ctx.L, ctx.rsExpr, rsE, opE, lamE]
  | .load t addr binder k => do
    let tE := tyToExpr t
    let addrE ← argToExpr ctx addr
    let lamE ← withLoadVar ctx binder fun ctx' => lExprToLeanExpr ctx' k
    pure <| mkAppN (Lean.mkConst ``LeanQbe.T.Expr.load) #[ctx.V, ctx.L, ctx.rsExpr, tE, addrE, lamE]
  | .store t val addr k => do
    let tE := tyToExpr t
    let valE ← argToExpr ctx val
    let addrE ← argToExpr ctx addr
    let restE ← lExprToLeanExpr ctx k
    pure <| mkAppN (Lean.mkConst ``LeanQbe.T.Expr.store) #[ctx.V, ctx.L, ctx.rsExpr, tE, valE, addrE, restE]
  | .call f as bs args binders k => do
    let asE := listLit tyConst (as.map tyToExpr)
    let bsE := listLit tyConst (bs.map tyToExpr)
    let argsE ← argListToTupExpr ctx args
    let lamE ← withTupleLVars ctx binders fun ctx' => lExprToLeanExpr ctx' k
    pure <| mkAppN (Lean.mkConst ``LeanQbe.T.Expr.call)
      #[ctx.V, ctx.L, ctx.rsExpr, mkStrLit f, asE, bsE, argsE, lamE]
  | .jnz c t e => do
    let cE ← argToExpr ctx c
    let tE ← lExprToLeanExpr ctx t
    let eE ← lExprToLeanExpr ctx e
    pure <| mkAppN (Lean.mkConst ``LeanQbe.T.Expr.jnz) #[ctx.V, ctx.L, ctx.rsExpr, cE, tE, eE]
  | .jump lid _ args => do
    let (lRef, tsE) ← ctx.lblRef lid
    let argsE ← argListToTupExpr ctx args
    pure <| mkAppN (Lean.mkConst ``LeanQbe.T.Expr.jump) #[ctx.V, ctx.L, ctx.rsExpr, tsE, lRef, argsE]
  | .ret _ args => do
    let vsE ← argListToTupExpr ctx args
    pure <| mkAppN (Lean.mkConst ``LeanQbe.T.Expr.ret) #[ctx.V, ctx.L, ctx.rsExpr, vsE]
  | .exit f as args => do
    let asE := listLit tyConst (as.map tyToExpr)
    let argsE ← argListToTupExpr ctx args
    pure <| mkAppN (Lean.mkConst ``LeanQbe.T.Expr.exit) #[ctx.V, ctx.L, ctx.rsExpr, mkStrLit f, asE, argsE]
  | .hlt =>
    pure <| mkApp3 (Lean.mkConst ``LeanQbe.T.Expr.hlt) ctx.V ctx.L ctx.rsExpr
  | .group blocks k => do
    let sigList := blocks.map fun (_, ps, _) => listLit tyConst (ps.map fun v => tyToExpr v.ty)
    let sigE := listLit listTyConst sigList
    let bodiesLam ← withGroupLabelsL ctx blocks fun ctx' => mkBlocksExpr ctx' blocks
    let entryLam ← withGroupLabelsL ctx blocks fun ctx' => lExprToLeanExpr ctx' k
    pure <| mkAppN (Lean.mkConst ``LeanQbe.T.Expr.group)
      #[ctx.V, ctx.L, ctx.rsExpr, sigE, bodiesLam, entryLam]
where
  mkBlocksExpr (ctx : ElabCtx) : List (Nat × List LVar × LExpr) → Except String Lean.Expr
    | [] => pure <| mkApp3 (Lean.mkConst ``LeanQbe.T.Blocks.nil) ctx.V ctx.L ctx.rsExpr
    | (_, ps, body) :: rest => do
      let tsE := listLit tyConst (ps.map fun v => tyToExpr v.ty)
      let restSigE := listLit listTyConst (rest.map fun (_, rps, _) => listLit tyConst (rps.map fun v => tyToExpr v.ty))
      let bLam ← withTupleLVars ctx ps fun ctx' => lExprToLeanExpr ctx' body
      let bsE ← mkBlocksExpr ctx rest
      pure <| mkAppN (Lean.mkConst ``LeanQbe.T.Blocks.cons)
        #[ctx.V, ctx.L, ctx.rsExpr, tsE, restSigE, bLam, bsE]

meta def lFnToLeanExprM (lfn : LFn) : MetaM (Lean.Expr × Lean.Expr × Lean.Expr) := do
  let asList := lfn.params.map fun v => tyToExpr v.ty
  let rsList := lfn.rs.map tyToExpr
  let asExpr := listLit tyConst asList
  let rsExpr := listLit tyConst rsList
  let vSort := Lean.Expr.forallE `t tyConst (.sort 1) .default
  let lSort := Lean.Expr.forallE `ts listTyConst (.sort 1) .default
  withLocalDeclD `V vSort fun V =>
  withLocalDeclD `L lSort fun L => do
    let initCtx : ElabCtx := { V, L, rsExpr }
    let bodyLam ← match withTupleLVars initCtx lfn.params fun ctx' => lExprToLeanExpr ctx' lfn.body with
      | .ok e => pure e
      | .error err => throwError err
    let funcExpr ← mkLambdaFVars #[V, L] bodyLam
    pure (funcExpr, asExpr, rsExpr)

/-! ## Acyclicity Check for Lowered Modules -/

meta partial def lExprCalls : LExpr → List Sym
  | .let_ _ _ k | .load _ _ _ k | .store _ _ _ k => lExprCalls k
  | .call f _ _ _ _ k => f :: lExprCalls k
  | .jnz _ t e => lExprCalls t ++ lExprCalls e
  | .jump _ _ _ | .ret _ _ | .exit _ _ _ | .hlt => []
  | .group blocks k =>
    (blocks.foldl (fun acc (_, _, b) => acc ++ lExprCalls b) []) ++ lExprCalls k

meta def checkLModuleAcyclic (m : LModule) : Except String Unit := do
  let mut definedSoFar : Std.HashSet String := {}
  let mut extSet : Std.HashSet String := {}
  for ex in m.externs do
    if extSet.contains ex.name then
      throw s!"duplicate extern declaration '{ex.name}'"
    extSet := extSet.insert ex.name
  let fnNames : Std.HashSet String := m.fns.foldl (fun s f => s.insert f.name) {}
  for fn in m.fns do
    if definedSoFar.contains fn.name then
      throw s!"duplicate function definition '{fn.name}'"
    if extSet.contains fn.name then
      throw s!"function '{fn.name}' collides with extern declaration"
    for callee in lExprCalls fn.body do
      if callee == fn.name then
        throw s!"recursive call to '{callee}' is not permitted in acyclic C0 module"
      if !definedSoFar.contains callee && !extSet.contains callee then
        if fnNames.contains callee then
          throw s!"forward/cyclic call from '{fn.name}' to '{callee}' violates callees-first acyclic module ordering"
        else
          throw s!"call from '{fn.name}' to undeclared function '{callee}'"
    definedSoFar := definedSoFar.insert fn.name

/-! ## Commands: `c0_decl!`, `c0_file!`, and `#c0_shape` -/

meta def elabC0Module (modPrefix? : Option Name) (src : String) : CommandElabM Unit := do
  let tu ← match parseC0 src with
    | .ok tu => pure tu
    | .error err => throwError err
  let lmod ← match lowerTranslationUnit tu with
    | .ok m => pure m
    | .error err => throwError err
  if let .error err := checkLModuleAcyclic lmod then
    throwError err
  let ns ← getCurrNamespace
  let mut fnConstNames : List Name := []
  for lfn in lmod.fns do
    let leanName := ns ++ Name.mkSimple lfn.name
    let bodyName := ns ++ Name.mkSimple (lfn.name ++ "_body")
    let (funcExpr, asExpr, rsExpr) ← liftTermElabM (lFnToLeanExprM lfn)
    -- Define `<lfn.name>_body : Func as rs` first so `<lfn.name> : Fn` references it cleanly
    let funcTy := mkApp2 (Lean.mkConst ``LeanQbe.T.Func) asExpr rsExpr
    liftCoreM <| do
      addAndCompile (.defnDecl {
        name := bodyName, levelParams := [], type := funcTy, value := funcExpr,
        hints := .regular 0, safety := .safe
      })
      enableRealizationsForConst bodyName
    let fnTy := Lean.mkConst ``LeanQbe.T.Fn
    let fnExpr := mkApp4 (Lean.mkConst ``LeanQbe.T.Fn.mk)
      (mkStrLit lfn.name) asExpr rsExpr (Lean.mkConst bodyName)
    liftCoreM <| do
      addAndCompile (.defnDecl {
        name := leanName, levelParams := [], type := fnTy, value := fnExpr,
        hints := .regular 0, safety := .safe
      })
      enableRealizationsForConst leanName
    modifyEnv fun env =>
      let env := c0ShapeExt.addEntry env (leanName, lfn.shape)
      c0ShapeExt.addEntry env (bodyName, lfn.shape)
    fnConstNames := fnConstNames ++ [leanName]
  if let some pfx := modPrefix? then
    let fnType := Lean.mkConst ``LeanQbe.T.Fn
    let fnsName := ns ++ Name.mkSimple (pfx.toString ++ "_fns")
    let fnsTy := mkApp (Lean.mkConst ``List [.one]) fnType
    let fnsVal := (fnConstNames.map Lean.mkConst).foldr
      (fun e acc => mkApp3 (Lean.mkConst ``List.cons [.one]) fnType e acc)
      (mkApp (Lean.mkConst ``List.nil [.one]) fnType)
    liftCoreM <| do
      addAndCompile (.defnDecl {
        name := fnsName, levelParams := [], type := fnsTy, value := fnsVal,
        hints := .regular 0, safety := .safe
      })
      enableRealizationsForConst fnsName
    let modName := ns ++ Name.mkSimple (pfx.toString ++ "_module")
    let extsExpr := listLit (Lean.mkConst ``LeanQbe.T.Extern) <| lmod.externs.map fun ex =>
      mkApp3 (Lean.mkConst ``LeanQbe.T.Extern.mk) (mkStrLit ex.name)
        (listLit tyConst (ex.as.map tyToExpr)) (listLit tyConst (ex.rs.map tyToExpr))
    let exitsExpr := listLit (Lean.mkConst ``LeanQbe.T.Sym) (lmod.exits.map mkStrLit)
    let modVal := mkApp3 (Lean.mkConst ``LeanQbe.T.Module.mk) (Lean.mkConst fnsName) extsExpr exitsExpr
    liftCoreM <| do
      addAndCompile (.defnDecl {
        name := modName, levelParams := [], type := Lean.mkConst ``LeanQbe.T.Module, value := modVal,
        hints := .regular 0, safety := .safe
      })
      enableRealizationsForConst modName

syntax "c0_decl! " (ident)? str : command
syntax "c0_file! " (ident)? str : command
syntax "#c0_shape " ident : command
syntax "#c0_shape " str : command

elab_rules : command
  | `(c0_decl! $[$pfx:ident]? $src:str) =>
    elabC0Module (pfx.map (·.getId)) src.getString
  | `(c0_file! $[$pfx:ident]? $path:str) => do
    let content ← IO.FS.readFile path.getString
    elabC0Module (pfx.map (·.getId)) content
  | `(#c0_shape $id:ident) => do
    let (byLean, byC) := c0ShapeExt.getState (← getEnv)
    let ns ← getCurrNamespace
    let sh? := byLean.find? id.getId <|> byLean.find? (ns ++ id.getId) <|> byC.get? id.getId.toString
    match sh? with
    | some sh => logInfo sh.format
    | none => throwErrorAt id s!"no C0 shape metadata registered for '{id.getId}'"
  | `(#c0_shape $nm:str) => do
    let (_, byC) := c0ShapeExt.getState (← getEnv)
    match byC.get? nm.getString with
    | some sh => logInfo sh.format
    | none => throwErrorAt nm s!"no C0 shape metadata registered for \"{nm.getString}\""

end LeanQbe.T.Frontend.C0
