module

public import LeanQbe.T.NotationSugar
public meta import LeanQbe.T.NotationSugar

/-!
# QBE-style typed notation (`tqbe` / `tqbe_def`) for `LeanQbe.T`

Statement, control-flow sugar (`loop`, `break`, `continue`, `check`, `switch`), top-level `tqbe`
term elaborators, and `tqbe_def` command elaborator, building on `LeanQbe.T.NotationSugar`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Notation

open Lean Elab Command Term Meta

/-! ## Statement, group, and control-flow sugar elaboration -/

meta def contTy (ctx : Ctx) : List Lean.Expr → Lean.Expr
  | [] => ctx.exprTy
  | t :: ts => .forallE `x (mkApp ctx.V t) (contTy ctx ts) .default

meta def checkUniqueBinders (stx : Syntax) (names : List Name) : TermElabM Unit := do
  let mut seen : NameSet := {}
  for nm in names do
    if nm != `_ && nm != Name.anonymous then
      if seen.contains nm then
        throwErrorAt stx s!"tqbe: duplicate binder name `%{nm}`"
      seen := seen.insert nm

meta def parseLhsBinders (ps : Array (TSyntax `tqbe_opt_param)) :
    TermElabM (List (Name × Option Lean.Expr)) := do
  let res ← ps.toList.mapM fun p => do
    let (nm, tyStx?) ← parseOptParam p
    let ty? ← tyStx?.mapM elabTy
    pure (nm, ty?)
  if let some p0 := ps[0]? then
    checkUniqueBinders p0.raw (res.map (·.1))
  pure res

/-- Resolve `=ty` vs LHS binder types for `call` results. -/
meta def resolveCallResultTys (stx : Syntax) (lhs : List (Name × Option Lean.Expr))
    (opResTy? : Option Lean.Expr) : TermElabM (List (Name × Lean.Expr)) := do
  match opResTy?, lhs with
  | some rt, [(x, some t)] => checkTyEq stx rt t; return [(x, rt)]
  | some rt, [(x, none)] => return [(x, rt)]
  | some rt, _ =>
    -- If `opResTy?` was written as `=(t1, t2, ...)` matching multi-result `lhs`, unpack right-nested `pair`
    let rec unpack : Nat → Lean.Expr → TermElabM (List Lean.Expr)
      | 0, _ => pure []
      | 1, t => pure [t]
      | n + 1, t => do
        match ← toTyShape t with
        | .pair _ _ a b => return a :: (← unpack n b)
        | _ => throwErrorAt stx "tqbe: `=` result annotation count does not match LHS binders"
    let rts ← unpack lhs.length rt
    (lhs.zip rts).mapM fun ((x, t?), rt) => do
      if let some t := t? then checkTyEq stx rt t
      pure (x, rt)
  | none, _ =>
    lhs.mapM fun (x, t?) => do
      let some t := t?
        | throwErrorAt stx s!"tqbe: call result `%{x}` requires a type annotation"
      pure (x, t)

meta def parseGroupParams (ps : Array (TSyntax `tqbe_opt_param)) :
    TermElabM (List (Name × Lean.Expr)) := do
  let res ← ps.toList.mapM fun p => do
    let (nm, ty?) ← parseOptParam p
    let some tyStx := ty?
      | throwErrorAt p s!"tqbe: block parameter `%{nm}` requires a type annotation `:ty`"
    pure (nm, ← elabTy tyStx)
  if let some p0 := ps[0]? then
    checkUniqueBinders p0.raw (res.map (·.1))
  pure res

meta def elabLoopInit (ctx : Ctx) (lp : TSyntax `tqbe_loop_param) :
    TermElabM (Name × Lean.Expr × TSyntax `tqbe_arg) :=
  match lp with
  | `(tqbe_loop_param| %$x:ident : $t:tqbe_ty = $init:tqbe_arg) => do
    return (x.getId, ← elabTy t, init)
  | `(tqbe_loop_param| %$x:ident = $init:tqbe_arg) => do
    let some ty ← peekArgTy? ctx init
      | throwErrorAt lp s!"tqbe: loop parameter `%{x.getId}` requires a type annotation `:ty`"
    return (x.getId, ty, init)
  | `(tqbe_loop_param| %_ : $t:tqbe_ty = $init:tqbe_arg) => do
    return (`_, ← elabTy t, init)
  | `(tqbe_loop_param| %_ = $init:tqbe_arg) => do
    let some ty ← peekArgTy? ctx init
      | throwErrorAt lp "tqbe: loop parameter `%_` requires a type annotation `:ty`"
    return (`_, ty, init)
  | _ => throwErrorAt lp "tqbe: expected `%x:ty = init` in loop header"

meta inductive SwitchArmKey
  | bool (b : Bool)
  | bits (val : Int)
  deriving BEq

meta partial def parseSwitchLit (scrutShape : TyShape) (scrutTy : Lean.Expr)
    (pat : TSyntax `tqbe_arg) : TermElabM SwitchArmKey := do
  match pat with
  | `(tqbe_arg| $n:num) =>
    let k := n.getNat
    match scrutShape with
    | .bool =>
      if k == 0 then return .bool false
      else if k == 1 then return .bool true
      else throwErrorAt pat s!"tqbe: invalid bool literal {k} (expected true, false, 0, or 1)"
    | .bits n? _ =>
      if let some w := n? then
        checkBitsNatRange pat scrutTy w k
      return .bits (k : Int)
    | _ => throwErrorAt pat m!"tqbe: `switch` literal not valid for type{indentExpr scrutTy}"
  | `(tqbe_arg| -$n:num) =>
    let k := n.getNat
    match scrutShape with
    | .bits n? _ =>
      if k == 0 then
        throwErrorAt pat m!"tqbe: negative literal -0 not valid for type{indentExpr scrutTy}"
      if let some w := n? then
        checkBitsNegRange pat scrutTy w k
        if w ≤ 4096 then
          return .bits ((2 ^ w - k : Nat) : Int)
      return .bits (-(k : Int))
    | _ => throwErrorAt pat m!"tqbe: negative literal -{k} not valid for type{indentExpr scrutTy}"
  | `(tqbe_arg| true) =>
    match scrutShape with
    | .bool => return .bool true
    | _ => throwErrorAt pat m!"tqbe: boolean literal `true` not valid for type{indentExpr scrutTy}"
  | `(tqbe_arg| false) =>
    match scrutShape with
    | .bool => return .bool false
    | _ => throwErrorAt pat m!"tqbe: boolean literal `false` not valid for type{indentExpr scrutTy}"
  | `(tqbe_arg| ($inner:tqbe_arg : $t:tqbe_ty))
  | `(tqbe_arg| $inner:tqbe_arg : $t:tqbe_ty) =>
    let ty' ← elabTy t
    checkTyEq pat scrutTy ty'
    parseSwitchLit scrutShape scrutTy inner
  | _ =>
    throwErrorAt pat "tqbe: `switch` arm pattern must be a literal (`n`, `-n`, `true`, `false`, or `_`)"

meta def elabBreakTarget (ctx : Ctx) (stx : Syntax) (l : Option Ident)
    (args : Array (TSyntax `tqbe_arg)) : TermElabM Lean.Expr := do
  if let some lbl := l then
    match ctx.labels.find? lbl.getId with
    | some lb =>
      match lb.role with
      | .loopBreak =>
        let argsTup ← elabArgListWithSig ctx lbl lb.sig args
        return mkAppN (Lean.mkConst ``LeanQbe.T.Expr.jump)
          #[ctx.V, ctx.L, ctx.rsExpr, lb.sigExpr, ctx.ref lb.lvl lb.proj?, argsTup]
      | .loopHeader =>
        throwErrorAt lbl s!"tqbe: `break @{lbl.getId}` targets loop header @{lbl.getId}, not a loop break label (use `continue @{lbl.getId}`)"
      | .normal =>
        throwErrorAt lbl s!"tqbe: `break @{lbl.getId}` targets non-loop label @{lbl.getId} (use `jmp @{lbl.getId}`)"
    | none =>
      throwErrorAt lbl s!"tqbe: unknown loop break label @{lbl.getId}"
  else
    let some (lvl, proj?, sig, sigExpr) := ctx.breakTarget
      | throwErrorAt stx "tqbe: `break` has no enclosing loop continuation (use `@label` or follow loop with statements)"
    let argsTup ← elabArgListWithSig ctx stx sig args
    return mkAppN (Lean.mkConst ``LeanQbe.T.Expr.jump)
      #[ctx.V, ctx.L, ctx.rsExpr, sigExpr, ctx.ref lvl proj?, argsTup]

meta def elabContTarget (ctx : Ctx) (stx : Syntax) (l : Option Ident)
    (args : Array (TSyntax `tqbe_arg)) : TermElabM Lean.Expr := do
  if let some lbl := l then
    match ctx.labels.find? lbl.getId with
    | some lb =>
      match lb.role with
      | .loopHeader =>
        let argsTup ← elabArgListWithSig ctx lbl lb.sig args
        return mkAppN (Lean.mkConst ``LeanQbe.T.Expr.jump)
          #[ctx.V, ctx.L, ctx.rsExpr, lb.sigExpr, ctx.ref lb.lvl lb.proj?, argsTup]
      | .loopBreak =>
        throwErrorAt lbl s!"tqbe: `continue @{lbl.getId}` targets loop break label @{lbl.getId}, not a loop header (use `break @{lbl.getId}`)"
      | .normal =>
        throwErrorAt lbl s!"tqbe: `continue @{lbl.getId}` targets non-loop label @{lbl.getId} (use `jmp @{lbl.getId}`)"
    | none =>
      throwErrorAt lbl s!"tqbe: unknown loop header label @{lbl.getId}"
  else
    let some (lvl, proj?, sig, sigExpr) := ctx.contTarget
      | throwErrorAt stx "tqbe: `continue` outside of a `loop`"
    let argsTup ← elabArgListWithSig ctx stx sig args
    return mkAppN (Lean.mkConst ``LeanQbe.T.Expr.jump)
      #[ctx.V, ctx.L, ctx.rsExpr, sigExpr, ctx.ref lvl proj?, argsTup]

mutual
meta partial def elabContCurried (ctx : Ctx) (ps : List (Name × Lean.Expr))
    (rest : List (TSyntax `tqbe_stmt)) : TermElabM Lean.Expr :=
  match ps with
  | [] => elabStmts ctx rest
  | (x, ty) :: restPs => withLoadBinder ctx x ty fun ctx' => elabContCurried ctx' restPs rest

meta partial def elabTarget (ctx : Ctx) : TSyntax `tqbe_target → TermElabM Lean.Expr
  | `(tqbe_target| @$l:ident $[($as,*)]?) => do
    let args := as.map (·.getElems) |>.getD #[]
    match ctx.labels.find? l.getId with
    | some lb =>
      let argsTup ← elabArgListWithSig ctx l lb.sig args
      return mkAppN (Lean.mkConst ``LeanQbe.T.Expr.jump)
        #[ctx.V, ctx.L, ctx.rsExpr, lb.sigExpr, ctx.ref lb.lvl lb.proj?, argsTup]
    | none =>
      let le ← elabTerm l none
      synthesizeSyntheticMVarsNoPostponing
      let le ← instantiateMVars le
      let some tsExpr ← isLApp? ctx.L (← inferType le)
        | throwErrorAt l s!"tqbe: unknown label @{l.getId}"
      let tsExpr ← instantiateMVars tsExpr
      match ← extractTyList? tsExpr with
      | some tsList =>
        let argsTup ← elabArgListWithSig ctx l tsList args
        return mkAppN (Lean.mkConst ``LeanQbe.T.Expr.jump)
          #[ctx.V, ctx.L, ctx.rsExpr, tsExpr, ctx.abstract le, argsTup]
      | none =>
        unless args.isEmpty do
          throwErrorAt l s!"tqbe: symbolic label @{l.getId} with non-empty arguments; add explicit jump"
        unless ← isDefEq tsExpr (listLit tyConst []) do
          throwErrorAt l m!"tqbe: cannot jump without arguments to symbolic label @{l.getId} of type{indentExpr tsExpr}"
        return mkAppN (Lean.mkConst ``LeanQbe.T.Expr.jump)
          #[ctx.V, ctx.L, ctx.rsExpr, tsExpr, ctx.abstract le, punitVal]
  | `(tqbe_target| { $ss* }) => elabStmts ctx ss.toList
  | stx@`(tqbe_target| break $[@$l:ident]? $[($as,*)]?) =>
    elabBreakTarget ctx stx l (as.map (·.getElems) |>.getD #[])
  | stx@`(tqbe_target| continue $[@$l:ident]? $[($as,*)]?) =>
    elabContTarget ctx stx l (as.map (·.getElems) |>.getD #[])
  | stx => throwErrorAt stx "tqbe: unsupported target"

meta partial def elabGroup (ctx : Ctx) (stx : Syntax)
    (grp : List (Name × List (Name × Lean.Expr) × List (TSyntax `tqbe_stmt)))
    (rest : List (TSyntax `tqbe_stmt)) : TermElabM Lean.Expr := do
  if rest.isEmpty then
    throwErrorAt stx "tqbe: label group must be followed by entry statements"
  let labelSpecs := grp.map fun (lName, ps, _) =>
    let ts := ps.map (·.2)
    (some lName, ts, listLit tyConst ts, LabelRole.normal)
  let sigExpr := listLit listTyConst (labelSpecs.map (·.2.2.1))
  let bodiesLam ← withGroupLabels ctx labelSpecs fun ctx' => do
    let rec buildBlocks :
        List (Name × List (Name × Lean.Expr) × List (TSyntax `tqbe_stmt)) →
        TermElabM (Lean.Expr × Lean.Expr)
      | [] =>
        return (listLit listTyConst [], mkApp3 (Lean.mkConst ``LeanQbe.T.Blocks.nil) ctx'.V ctx'.L ctx'.rsExpr)
      | (_, ps, body) :: more => do
        let ts := ps.map (·.2)
        let tsExpr := listLit tyConst ts
        let bLam ← withTupleVars ctx' ps fun ctxBody => elabStmts ctxBody body
        let (moreSigExpr, bsTail) ← buildBlocks more
        let bs := mkAppN (Lean.mkConst ``LeanQbe.T.Blocks.cons)
          #[ctx'.V, ctx'.L, ctx'.rsExpr, tsExpr, moreSigExpr, bLam, bsTail]
        return (mkApp3 (Lean.mkConst ``List.cons [.zero]) listTyConst tsExpr moreSigExpr, bs)
    let (_, bsExpr) ← buildBlocks grp
    return bsExpr
  let entryLam ← withGroupLabels ctx labelSpecs fun ctx' => elabStmts ctx' rest
  return mkAppN (Lean.mkConst ``LeanQbe.T.Expr.group)
    #[ctx.V, ctx.L, ctx.rsExpr, sigExpr, bodiesLam, entryLam]

meta partial def elabLoop (ctx : Ctx) (stx : Syntax)
    (lpName? : Option Name) (lParams : Array (TSyntax `tqbe_loop_param))
    (brkSpec? : Option (Option Name × List (Name × Lean.Expr)))
    (body : List (TSyntax `tqbe_stmt)) (rest : List (TSyntax `tqbe_stmt)) : TermElabM Lean.Expr := do
  if let (some lpName, some (some bName, _)) := (lpName?, brkSpec?) then
    if bName == lpName then
      throwErrorAt stx s!"tqbe: loop label @{lpName} and break label @{bName} cannot have the same name"
  if brkSpec?.isSome && rest.isEmpty then
    throwErrorAt stx "tqbe: loop with break binder/target requires statements after the loop"
  let lpParsed ← lParams.toList.mapM (elabLoopInit ctx)
  let lpBinders := lpParsed.map fun (x, t, _) => (x, t)
  checkUniqueBinders stx (lpBinders.map (·.1))
  let lpSig := lpParsed.map (·.2.1)
  let lpSigExpr := listLit tyConst lpSig
  let lpInits := lpParsed.map (·.2.2)
  let hasOuter := !(brkSpec?.isNone && rest.isEmpty)
  let initDepth := ctx.depth + (if hasOuter then 2 else 1)
  let initTup ← elabArgListWithSig { ctx with depth := initDepth } stx lpSig lpInits.toArray
  let mkInnerLoop (ctxIn : Ctx) : TermElabM Lean.Expr := do
    let groupSigExpr := listLit listTyConst [lpSigExpr]
    let lpLvl := ctxIn.depth
    let lpProj := some (0, listTyConst, ctxIn.L, [lpSigExpr])
    let bodiesLam ← withGroupLabels ctxIn [(lpName?, lpSig, lpSigExpr, .loopHeader)] fun ctxGrp => do
      let bLam ← withTupleVars ctxGrp lpBinders fun ctxBody =>
        let ctxBody' := { ctxBody with contTarget := some (lpLvl, lpProj, lpSig, lpSigExpr) }
        elabStmts ctxBody' body
      let nilSig := listLit listTyConst []
      let nilBs := mkApp3 (Lean.mkConst ``LeanQbe.T.Blocks.nil) ctxGrp.V ctxGrp.L ctxGrp.rsExpr
      return mkAppN (Lean.mkConst ``LeanQbe.T.Blocks.cons)
        #[ctxGrp.V, ctxGrp.L, ctxGrp.rsExpr, lpSigExpr, nilSig, bLam, nilBs]
    let entryLam ← withGroupLabels ctxIn [(none, lpSig, lpSigExpr, .loopHeader)] fun ctxEntry => do
      return mkAppN (Lean.mkConst ``LeanQbe.T.Expr.jump)
        #[ctxEntry.V, ctxEntry.L, ctxEntry.rsExpr, lpSigExpr, ctxEntry.ref lpLvl lpProj, initTup]
    return mkAppN (Lean.mkConst ``LeanQbe.T.Expr.group)
      #[ctxIn.V, ctxIn.L, ctxIn.rsExpr, groupSigExpr, bodiesLam, entryLam]
  if !hasOuter then
    mkInnerLoop { ctx with breakTarget := none }
  else
    let (brkName?, brkBinders) := brkSpec?.getD (none, [])
    let brkSig := brkBinders.map (·.2)
    let brkSigExpr := listLit tyConst brkSig
    let outerSigExpr := listLit listTyConst [brkSigExpr]
    let brkLvl := ctx.depth
    let brkProj := some (0, listTyConst, ctx.L, [brkSigExpr])
    let outerBodies ← withGroupLabels ctx [(none, brkSig, brkSigExpr, .normal)] fun ctxGrp => do
      let bLam ← withTupleVars ctxGrp brkBinders fun ctxRest => elabStmts ctxRest rest
      let nilSig := listLit listTyConst []
      let nilBs := mkApp3 (Lean.mkConst ``LeanQbe.T.Blocks.nil) ctxGrp.V ctxGrp.L ctxGrp.rsExpr
      return mkAppN (Lean.mkConst ``LeanQbe.T.Blocks.cons)
        #[ctxGrp.V, ctxGrp.L, ctxGrp.rsExpr, brkSigExpr, nilSig, bLam, nilBs]
    let outerEntry ← withGroupLabels ctx [(brkName?, brkSig, brkSigExpr, .loopBreak)] fun ctxEntry => do
      let ctxLoop := { ctxEntry with breakTarget := some (brkLvl, brkProj, brkSig, brkSigExpr) }
      mkInnerLoop ctxLoop
    return mkAppN (Lean.mkConst ``LeanQbe.T.Expr.group)
      #[ctx.V, ctx.L, ctx.rsExpr, outerSigExpr, outerBodies, outerEntry]

meta partial def elabSwitch (ctx : Ctx) (scrutStx : TSyntax `tqbe_arg)
    (arms : List (TSyntax `tqbe_switch_arm)) : TermElabM Lean.Expr := do
  let (_, scrutTy) ← elabArg ctx none scrutStx
  let mMask := mkApp (Lean.mkConst ``LeanQbe.T.Ty.mask) scrutTy
  unless ← isDefEq mMask boolTyExpr do
    throwErrorAt scrutStx m!"tqbe: `switch` scrutinee must be scalar (got type{indentExpr scrutTy})"
  let scrutShape ← toTyShape scrutTy
  match scrutShape with
  | .float _ =>
    throwErrorAt scrutStx m!"tqbe: `switch` does not support floating-point scrutinee{indentExpr scrutTy}"
  | .other e =>
    if e.isAppOfArity ``LeanQbe.T.Ty.float 1 then
      throwErrorAt scrutStx m!"tqbe: `switch` does not support floating-point scrutinee{indentExpr scrutTy}"
  | _ => pure ()
  let cmpCode := mkApp4 (Lean.mkConst ``LeanQbe.T.OpCode.cmp)
    (Lean.mkConst ``LeanQbe.T.CmpOp.eq) scrutTy boolTyExpr (mkMaskEqRefl boolTyExpr)
  let rec goOn (c : Ctx) (seen : Array SwitchArmKey) :
      List (TSyntax `tqbe_switch_arm) → TermElabM Lean.Expr
    | [] => return mkApp3 (Lean.mkConst ``LeanQbe.T.Expr.hlt) c.V c.L c.rsExpr
    | arm :: more =>
      match arm with
      | `(tqbe_switch_arm| _ => $tgt:tqbe_target $[,]?) => do
        unless more.isEmpty do
          throwErrorAt arm "tqbe: default `_` arm must be last in `switch`"
        elabTarget c tgt
      | `(tqbe_switch_arm| $pat:tqbe_arg => $tgt:tqbe_target $[,]?) => do
        let key ← parseSwitchLit scrutShape scrutTy pat
        if seen.contains key then
          throwErrorAt pat "tqbe: duplicate `switch` arm literal"
        let (scrutArgC, _) ← elabArg c (some scrutTy) scrutStx
        let (patArgC, _) ← elabArg c (some scrutTy) pat
        let sig := [scrutTy, scrutTy]
        let rs := [boolTyExpr]
        let sigExpr := listLit tyConst sig
        let rsExpr := listLit tyConst rs
        let opArgs := mkTupElems tyConst (mkArgApp c.V) sig [scrutArgC, patArgC]
        let op := mkAppN (Lean.mkConst ``LeanQbe.T.Op.mk) #[c.V, rsExpr, sigExpr, cmpCode, opArgs]
        let lam ← withTupleVars c [(`_, boolTyExpr)] fun cCond => do
          let condVar := cCond.ref c.depth (some (0, tyConst, cCond.V, [boolTyExpr]))
          let condArg := mkApp3 (Lean.mkConst ``LeanQbe.T.Arg.var) cCond.V boolTyExpr condVar
          let thenE ← elabTarget cCond tgt
          let elseE ← goOn cCond (seen.push key) more
          return mkAppN (Lean.mkConst ``LeanQbe.T.Expr.jnz)
            #[cCond.V, cCond.L, cCond.rsExpr, condArg, thenE, elseE]
        return mkAppN (Lean.mkConst ``LeanQbe.T.Expr.let_)
          #[c.V, c.L, c.rsExpr, rsExpr, op, lam]
      | _ => throwErrorAt arm "tqbe: invalid switch arm"
  goOn ctx #[] arms

meta partial def elabStmts (ctx : Ctx) : List (TSyntax `tqbe_stmt) → TermElabM Lean.Expr
  | [] => throwError "tqbe: block does not end in a terminator (ret, jmp, jnz, switch, exit, hlt, loop, break, continue)"
  | s :: rest => do
    match s with
    | `(tqbe_stmt| $xs:tqbe_opt_param,* =$k:tqbe_ty call $f:tqbe_sym($as,*)) => do
      let lhs ← parseLhsBinders xs.getElems
      let kt ← elabTy k
      let resBinders ← resolveCallResultTys s lhs (some kt)
      let (argTys, argsTup) ← elabArgListOpen ctx as.getElems
      let bs := resBinders.map (·.2)
      let asExpr := listLit tyConst argTys
      let bsExpr := listLit tyConst bs
      let lam ← withTupleVars ctx resBinders fun ctx' => elabStmts ctx' rest
      return mkAppN (Lean.mkConst ``LeanQbe.T.Expr.call)
        #[ctx.V, ctx.L, ctx.rsExpr, ← symLit f, asExpr, bsExpr, argsTup, lam]
    | `(tqbe_stmt| $xs:tqbe_opt_param,* = call $f:tqbe_sym($as,*)) => do
      let lhs ← parseLhsBinders xs.getElems
      let resBinders ← resolveCallResultTys s lhs none
      let (argTys, argsTup) ← elabArgListOpen ctx as.getElems
      let bs := resBinders.map (·.2)
      let asExpr := listLit tyConst argTys
      let bsExpr := listLit tyConst bs
      let lam ← withTupleVars ctx resBinders fun ctx' => elabStmts ctx' rest
      return mkAppN (Lean.mkConst ``LeanQbe.T.Expr.call)
        #[ctx.V, ctx.L, ctx.rsExpr, ← symLit f, asExpr, bsExpr, argsTup, lam]
    | `(tqbe_stmt| $xs:tqbe_opt_param,* =$k:tqbe_ty load $a:tqbe_arg) => do
      let lhs ← parseLhsBinders xs.getElems
      unless lhs.length == 1 do
        throwErrorAt s "tqbe: `load` produces exactly 1 result"
      let kt ← elabTy k
      if let some bt := lhs[0]!.2 then checkTyEq s kt bt
      let (addrArg, _) ← elabArg ctx (some i64TyExpr) a
      let lam ← withLoadBinder ctx lhs[0]!.1 kt fun ctx' => elabStmts ctx' rest
      return mkAppN (Lean.mkConst ``LeanQbe.T.Expr.load)
        #[ctx.V, ctx.L, ctx.rsExpr, kt, addrArg, lam]
    | `(tqbe_stmt| $xs:tqbe_opt_param,* = load $k:tqbe_ty, $a:tqbe_arg) => do
      let lhs ← parseLhsBinders xs.getElems
      unless lhs.length == 1 do
        throwErrorAt s "tqbe: `load` produces exactly 1 result"
      let kt ← elabTy k
      if let some bt := lhs[0]!.2 then checkTyEq s kt bt
      let (addrArg, _) ← elabArg ctx (some i64TyExpr) a
      let lam ← withLoadBinder ctx lhs[0]!.1 kt fun ctx' => elabStmts ctx' rest
      return mkAppN (Lean.mkConst ``LeanQbe.T.Expr.load)
        #[ctx.V, ctx.L, ctx.rsExpr, kt, addrArg, lam]
    | `(tqbe_stmt| $xs:tqbe_opt_param,* = load $a:tqbe_arg) => do
      let lhs ← parseLhsBinders xs.getElems
      unless lhs.length == 1 do
        throwErrorAt s "tqbe: `load` produces exactly 1 result"
      let some kt := lhs[0]!.2
        | throwErrorAt s "tqbe: `load` requires a type annotation (e.g. `=l load %p` or `%x:l = load %p`)"
      let (addrArg, _) ← elabArg ctx (some i64TyExpr) a
      let lam ← withLoadBinder ctx lhs[0]!.1 kt fun ctx' => elabStmts ctx' rest
      return mkAppN (Lean.mkConst ``LeanQbe.T.Expr.load)
        #[ctx.V, ctx.L, ctx.rsExpr, kt, addrArg, lam]
    | `(tqbe_stmt| $xs:tqbe_opt_param,* =$k:tqbe_ty $op:ident $as,*) => do
      let lhs ← parseLhsBinders xs.getElems
      let kt ← elabTy k
      elabAssignOp ctx lhs (some kt) op as.getElems fun ctx' => elabStmts ctx' rest
    | `(tqbe_stmt| $xs:tqbe_opt_param,* = $op:ident $as,*) => do
      let lhs ← parseLhsBinders xs.getElems
      elabAssignOp ctx lhs none op as.getElems fun ctx' => elabStmts ctx' rest
    | `(tqbe_stmt| store $t:tqbe_ty $v:tqbe_arg, $a:tqbe_arg) => do
      let vt ← elabTy t
      let (vArg, _) ← elabArg ctx (some vt) v
      let (aArg, _) ← elabArg ctx (some i64TyExpr) a
      let cont ← elabStmts ctx rest
      return mkAppN (Lean.mkConst ``LeanQbe.T.Expr.store)
        #[ctx.V, ctx.L, ctx.rsExpr, vt, vArg, aArg, cont]
    | `(tqbe_stmt| store $v:tqbe_arg, $a:tqbe_arg) => do
      let (vArg, vt) ← elabArg ctx none v
      let (aArg, _) ← elabArg ctx (some i64TyExpr) a
      let cont ← elabStmts ctx rest
      return mkAppN (Lean.mkConst ``LeanQbe.T.Expr.store)
        #[ctx.V, ctx.L, ctx.rsExpr, vt, vArg, aArg, cont]
    | `(tqbe_stmt| call $f:tqbe_sym($as,*)) => do
      let (argTys, argsTup) ← elabArgListOpen ctx as.getElems
      let asExpr := listLit tyConst argTys
      let bsExpr := listLit tyConst []
      let lam ← withTupleVars ctx [] fun ctx' => elabStmts ctx' rest
      return mkAppN (Lean.mkConst ``LeanQbe.T.Expr.call)
        #[ctx.V, ctx.L, ctx.rsExpr, ← symLit f, asExpr, bsExpr, argsTup, lam]
    | `(tqbe_stmt| check $c:tqbe_arg else $tgt:tqbe_target) => do
      let (cArg, _) ← elabArg ctx (some boolTyExpr) c
      let tExpr ← elabStmts ctx rest
      let eExpr ← elabTarget ctx tgt
      return mkAppN (Lean.mkConst ``LeanQbe.T.Expr.jnz)
        #[ctx.V, ctx.L, ctx.rsExpr, cArg, tExpr, eExpr]
    | `(tqbe_stmt| $bxs:tqbe_opt_param,* <- loop $[@$lp:ident]? ($lps,*) { $body* }) => do
      let brkParsed ← parseLhsBinders bxs.getElems
      let brkBinders ← brkParsed.mapM fun (nm, ty?) => do
        let some ty := ty?
          | throwErrorAt s s!"tqbe: loop break binder `%{nm}` requires a type annotation `:ty`"
        pure (nm, ty)
      let lpName? := lp.map (·.getId)
      elabLoop ctx s lpName? lps.getElems (some (none, brkBinders)) body.toList rest
    | `(tqbe_stmt| loop $[@$lp:ident]? ($lps,*) $[-> @$brk:ident $[($bps,*)]?]? { $body* }) => do
      let lpName? := lp.map (·.getId)
      let brkSpec? ← match brk with
        | some bId =>
          let bpElems := (bps.join.map (·.getElems)).getD #[]
          let bpParsed ← parseLhsBinders bpElems
          let brkBinders ← bpParsed.mapM fun (nm, ty?) => do
            let some ty := ty?
              | throwErrorAt s s!"tqbe: break target parameter `%{nm}` requires `:ty`"
            pure (nm, ty)
          pure (some (some bId.getId, brkBinders))
        | none => pure none
      elabLoop ctx s lpName? lps.getElems brkSpec? body.toList rest
    | `(tqbe_stmt| $xs:tqbe_opt_param,* <- $f:ident ($ys,*)) => do
      let parsed ← parseLhsBinders xs.getElems
      let tyExprs ← parsed.mapM fun (_, ty?) =>
        match ty? with
        | some t => pure t
        | none => mkFreshExprMVar (some tyConst)
      let kTy := contTy ctx tyExprs
      let fnExpr ← withResolvedMacroArgs ctx ys.getElems fun c' ysTerms => do
        let e ← elabTermEnsuringType (← `($f $ysTerms*)) (Lean.Expr.forallE `k kTy ctx.exprTy .default)
        synthesizeSyntheticMVarsNoPostponing
        let e ← instantiateMVars e
        if e.hasExprMVar then
          throwErrorAt s m!"tqbe: could not elaborate macro call{indentExpr e}"
        pure (c'.abstract e)
      let resolvedTys ← (parsed.zip tyExprs).mapM fun ((nm, _), te) => do
        let te' ← instantiateMVars te
        if te'.hasExprMVar then
          throwErrorAt s s!"tqbe: could not infer type for macro binder `%{nm}` (add `:ty`)"
        pure (nm, te')
      let cont ← elabContCurried ctx resolvedTys rest
      return .app fnExpr cont
    | `(tqbe_stmt| use $f:ident ($ys,*)) => do
      let fnExpr ← withResolvedMacroArgs ctx ys.getElems fun c' ysTerms => do
        elabLean c' (← `($f $ysTerms*)) (Lean.Expr.forallE `k ctx.exprTy ctx.exprTy .default)
      return .app fnExpr (← elabStmts ctx rest)
    | `(tqbe_stmt| @$l:ident $[($ps,*)]? { $body* }) => do
      let _ := (l, ps, body)
      let rec collect : List (TSyntax `tqbe_stmt) → NameSet →
          Array (Name × List (Name × Lean.Expr) × List (TSyntax `tqbe_stmt)) →
          TermElabM (Array (Name × List (Name × Lean.Expr) × List (TSyntax `tqbe_stmt)) ×
            List (TSyntax `tqbe_stmt))
        | st :: more, seen, acc => do
          match st with
          | `(tqbe_stmt| @$l:ident $[($ps,*)]? { $b* }) =>
            if seen.contains l.getId then
              throwErrorAt l s!"tqbe: duplicate label @{l.getId} in group"
            let parsedPs ← parseGroupParams (ps.map (·.getElems) |>.getD #[])
            collect more (seen.insert l.getId) (acc.push (l.getId, parsedPs, b.toList))
          | _ => return (acc, st :: more)
        | [], _, acc => return (acc, [])
      let (grp, tail) ← collect (s :: rest) {} #[]
      elabGroup ctx s grp.toList tail
    | _ =>
      let checkTerm : TermElabM Unit := do
        unless rest.isEmpty do
          throwErrorAt rest.head! "tqbe: statement after a terminator"
      match s with
      | `(tqbe_stmt| jmp @$l:ident $[($as,*)]?) => do
        checkTerm
        elabTarget ctx (← `(tqbe_target| @$l:ident $[($as,*)]?))
      | `(tqbe_stmt| jnz $c:tqbe_arg, $t:tqbe_target, $e:tqbe_target) => do
        checkTerm
        let (cArg, _) ← elabArg ctx (some boolTyExpr) c
        let tExpr ← elabTarget ctx t
        let eExpr ← elabTarget ctx e
        return mkAppN (Lean.mkConst ``LeanQbe.T.Expr.jnz)
          #[ctx.V, ctx.L, ctx.rsExpr, cArg, tExpr, eExpr]
      | `(tqbe_stmt| switch $scrut:tqbe_arg { $arms* }) => do
        checkTerm
        elabSwitch ctx scrut arms.toList
      | `(tqbe_stmt| break $[@$l:ident]? $[($as,*)]?) => do
        checkTerm
        elabBreakTarget ctx s l (as.map (·.getElems) |>.getD #[])
      | `(tqbe_stmt| continue $[@$l:ident]? $[($as,*)]?) => do
        checkTerm
        elabContTarget ctx s l (as.map (·.getElems) |>.getD #[])
      | `(tqbe_stmt| ret $as,*) => do
        checkTerm
        let some rsList := ctx.rs?
          | throwErrorAt s "tqbe: `ret` requires a concrete return type list `rs`"
        let vsTup ← elabArgListWithSig ctx s rsList as.getElems
        return mkAppN (Lean.mkConst ``LeanQbe.T.Expr.ret)
          #[ctx.V, ctx.L, ctx.rsExpr, vsTup]
      | `(tqbe_stmt| exit $f:tqbe_sym($as,*)) => do
        checkTerm
        let (argTys, argsTup) ← elabArgListOpen ctx as.getElems
        let asExpr := listLit tyConst argTys
        return mkAppN (Lean.mkConst ``LeanQbe.T.Expr.exit)
          #[ctx.V, ctx.L, ctx.rsExpr, ← symLit f, asExpr, argsTup]
      | `(tqbe_stmt| hlt) => do
        checkTerm
        return mkApp3 (Lean.mkConst ``LeanQbe.T.Expr.hlt) ctx.V ctx.L ctx.rsExpr
      | `(tqbe_stmt| ⟨$e⟩) => do
        checkTerm
        elabLean ctx e ctx.exprTy
      | `(tqbe_stmt| { $ss* }) => do
        checkTerm
        elabStmts ctx ss.toList
      | _ => throwErrorAt s "tqbe: unsupported statement"
end

/-! ## Top-level `tqbe` term elaborators and `tqbe_def` command -/

meta def extractFuncShape? (expectedType : Lean.Expr) :
    MetaM (Option (Lean.Expr × Lean.Expr)) := do
  if expectedType.isAppOfArity ``LeanQbe.T.Func 2 then
    return some (expectedType.appFn!.appArg!, expectedType.appArg!)
  let ty ← whnfR expectedType
  if ty.isAppOfArity ``LeanQbe.T.Func 2 then
    return some (ty.appFn!.appArg!, ty.appArg!)
  if ty.isForall then
    let b1 := ty.bindingBody!
    if b1.isForall then
      let b2 := b1.bindingBody!
      if b2.isArrow then
        let dom := b2.bindingDomain!
        let cod := b2.bindingBody!
        if dom.isAppOfArity ``LeanQbe.T.Tup 3 && cod.isAppOfArity ``LeanQbe.T.Expr 3 then
          return some (dom.appArg!, cod.appArg!)
  return none

meta def extractExprShape? (expectedType : Lean.Expr) :
    MetaM (Option (Lean.Expr × Lean.Expr × Lean.Expr)) := do
  if expectedType.isAppOfArity ``LeanQbe.T.Expr 3 then
    return some (expectedType.appFn!.appFn!.appArg!, expectedType.appFn!.appArg!, expectedType.appArg!)
  let ty ← whnfR expectedType
  if ty.isAppOfArity ``LeanQbe.T.Expr 3 then
    return some (ty.appFn!.appFn!.appArg!, ty.appFn!.appArg!, ty.appArg!)
  return none

meta def resolveParamsAgainst (stx : Syntax) (ps : Array (TSyntax `tqbe_opt_param))
    (asOpt : Option (List Lean.Expr)) : TermElabM (List (Name × Lean.Expr)) := do
  let parsed ← parseLhsBinders ps
  match asOpt with
  | none =>
    parsed.mapM fun (nm, ty?) => do
      let some ty := ty?
        | throwErrorAt stx s!"tqbe: parameter `%{nm}` requires a type annotation `:ty`"
      pure (nm, ty)
  | some asList =>
    unless parsed.length == asList.length do
      throwErrorAt stx s!"tqbe: expected {asList.length} parameter(s), got {parsed.length}"
    (parsed.zip asList).mapM fun ((nm, ty?), expTy) => do
      if let some ty := ty? then checkTyEq stx expTy ty
      pure (nm, expTy)

meta def elabFuncTerm (stx : Syntax) (expectedType : Lean.Expr)
    (ps : Array (TSyntax `tqbe_opt_param)) (rets? : Option (TSyntax `tqbe_rets))
    (stmts : Array (TSyntax `tqbe_stmt)) : TermElabM Lean.Expr := do
  let expected ← instantiateMVars expectedType
  let vSort := Lean.Expr.forallE `t tyConst (.sort 1) .default
  let lSort := Lean.Expr.forallE `ts listTyConst (.sort 1) .default
  -- Check if expectedType is `Tup V as → Expr V L rs` (e.g. inside `fun _ _ => tqbe(...) { ... }`)
  let expectedWhnf ← whnf expected
  if expectedWhnf.isArrow then
    let dom := expectedWhnf.bindingDomain!
    let cod := expectedWhnf.bindingBody!
    if let some (V, L, rsExpr) ← extractExprShape? cod then
      let rsList? ← extractTyList? rsExpr
      let asOpt ←
        if dom.isAppOfArity ``LeanQbe.T.Tup 3 then
          extractTyList? dom.appArg!
        else
          let domWhnf ← whnfR dom
          if domWhnf.isAppOfArity ``LeanQbe.T.Tup 3 then
            extractTyList? domWhnf.appArg!
          else pure none
      let binders ← resolveParamsAgainst stx ps asOpt
      if let some rStx := rets? then
        let rsFromStx ← elabRets rStx
        checkTyEq stx rsExpr (listLit tyConst rsFromStx)
      let ctx : Ctx := {
        V, L, rs? := rsList?, rsExpr, depth := 0, vars := {}, labels := {},
        varFVars := {}, contTarget := none, breakTarget := none }
      return ← withTupleVars ctx binders fun ctx' => elabStmts ctx' stmts.toList

  -- Otherwise elaborate to `Func as rs` (`∀ V L, Tup V as → Expr V L rs`)
  let (asOpt, rsOpt) ← match ← extractFuncShape? expected with
    | some (asE, rsE) =>
      let asL ← extractTyList? asE
      let rsL ← extractTyList? rsE
      pure (asL, some (rsL, rsE))
    | none => pure (none, none)
  let binders ← resolveParamsAgainst stx ps asOpt
  let (rsList?, rsExpr) ← match rets?, rsOpt with
    | some rStx, some (rsL?, rsE) =>
      let rGiven ← elabRets rStx
      let rGivenE := listLit tyConst rGiven
      checkTyEq stx rsE rGivenE
      pure (rsL? <|> some rGiven, rsE)
    | some rStx, none =>
      let rGiven ← elabRets rStx
      pure (some rGiven, listLit tyConst rGiven)
    | none, some (rsL?, rsE) => pure (rsL?, rsE)
    | none, none =>
      throwErrorAt stx "tqbe: could not infer return type list (add `-> ret_ty` or `: Func as rs`)"
  withLocalDeclD `V vSort fun V =>
  withLocalDeclD `L lSort fun L => do
    let ctx : Ctx := {
      V, L, rs? := rsList?, rsExpr, depth := 0, vars := {}, labels := {},
      varFVars := {}, contTarget := none, breakTarget := none }
    let body ← withTupleVars ctx binders fun ctx' => elabStmts ctx' stmts.toList
    mkLambdaFVars #[V, L] body

/-- A code fragment (`Expr V L rs`, or `Func [] rs` if expected type is `Func`). -/
syntax "tqbe " "{" tqbe_stmt* "}" : term
/-- A nullary function (`Func [] rs`) or fragment with explicit return types. -/
syntax "tqbe " "-> " tqbe_rets " {" tqbe_stmt* "}" : term
/-- A typed function (`Func as rs` or `Tup V as → Expr V L rs`). -/
syntax "tqbe" "(" tqbe_opt_param,* ")" (" -> " tqbe_rets)? " {" tqbe_stmt* "}" : term
/-- A named typed function (`Fn`). -/
syntax "tqbe " tqbe_sym "(" tqbe_opt_param,* ")" (" -> " tqbe_rets)? " {" tqbe_stmt* "}" : term

elab_rules : term <= expectedType
  | `(tqbe { $ss* }) => do
    let stx ← getRef
    let expected ← instantiateMVars expectedType
    if let some (V, L, rsExpr) ← extractExprShape? expected then
      let rsList? ← extractTyList? rsExpr
      let ctx : Ctx := {
        V, L, rs? := rsList?, rsExpr, depth := 0, vars := {}, labels := {},
        varFVars := {}, contTarget := none, breakTarget := none }
      elabStmts ctx ss.toList
    else if let some _ ← extractFuncShape? expected then
      elabFuncTerm stx expected #[] none ss
    else
      throwErrorAt stx m!"tqbe: expected type{indentExpr expected}\nis not `LeanQbe.T.Expr V L rs` or `LeanQbe.T.Func [] rs`"
  | `(tqbe -> $rets { $ss* }) => do
    let stx ← getRef
    let expected ← instantiateMVars expectedType
    if let some (V, L, rsExpr) ← extractExprShape? expected then
      let rsFromStx ← elabRets rets
      checkTyEq stx rsExpr (listLit tyConst rsFromStx)
      let ctx : Ctx := {
        V, L, rs? := some rsFromStx, rsExpr, depth := 0, vars := {}, labels := {},
        varFVars := {}, contTarget := none, breakTarget := none }
      elabStmts ctx ss.toList
    else
      elabFuncTerm stx expected #[] (some rets) ss
  | `(tqbe($ps,*) $[-> $rets]? { $ss* }) => do
    let stx ← getRef
    elabFuncTerm stx expectedType ps.getElems rets ss
  | `(tqbe $sym:tqbe_sym ($ps,*) $[-> $rets]? { $ss* }) => do
    let stx ← getRef
    let binders ← resolveParamsAgainst stx ps.getElems none
    let asList := binders.map (·.2)
    let asExpr := listLit tyConst asList
    let rsList ← match rets with
      | some rStx => elabRets rStx
      | none => pure []
    let rsExpr := listLit tyConst rsList
    let funcExpected := mkApp2 (Lean.mkConst ``LeanQbe.T.Func) asExpr rsExpr
    let bodyFn ← elabFuncTerm stx funcExpected ps.getElems rets ss
    return mkApp4 (Lean.mkConst ``LeanQbe.T.Fn.mk) (← symLit sym) asExpr rsExpr bodyFn

/-- Define a typed IR function directly in the kernel, bypassing `addPreDefinitions` and code
generation (recommended for large proof-only programs when codegen is not needed). -/
syntax (docComment)? "tqbe_def " ident (" : " term)? " := " term : command

elab_rules : command
  | `($[$doc:docComment]? tqbe_def $id:ident $[: $ty:term]? := $val:term) => do
    let name := (← getCurrNamespace) ++ id.getId
    liftTermElabM do
      let t ← match ty with
        | some ty => elabType ty
        | none => mkFreshExprMVar (some (.sort 2))
      let e ← elabTermEnsuringType val t
      synthesizeSyntheticMVarsNoPostponing
      let t ← instantiateMVars (← if ty.isSome then pure t else inferType e)
      let e ← instantiateMVars e
      if t.hasExprMVar || e.hasExprMVar then
        throwError "tqbe_def: could not elaborate completely (add explicit `: Func as rs`)"
      addDecl (.defnDecl {
        name, levelParams := [], type := t, value := e,
        hints := .regular 0, safety := .safe, all := [name]
      })
      enableRealizationsForConst name
      if let some doc := doc then
        addDocStringCore name (← getDocStringText doc)

end LeanQbe.T.Notation
