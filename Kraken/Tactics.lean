module

/-
Common Kraken Proof Tactics.

Core tactics and theorems for stepping through Kraken assembly proofs.
-/

public import Kraken.Attribute
import Kraken.Layout
import Kraken.OmniSemantics
public import Kraken.SeparationTactics
import Kraken.X64.OmniSemantics

public meta section

open Lean Meta Elab Tactic Kraken

/-- Set up a straight-line proof for `p` from `s`, naming the state fields and
general-purpose registers. `status` and `dmem` are called `flags` and `mem`. -/
syntax (name := kprologue) "kprologue" ident "with" ident : tactic

private def kprologueBinderName (field : Lean.Name) : Lean.Name :=
  if field == `status then `flags
  else if field == `dmem then `mem
  else field

elab_rules : tactic
  | `(tactic| kprologue $p:ident with $s:ident) => withMainContext do
      let env ← getEnv
      let state ← Term.elabTerm s none
      let stateType ← whnf (← inferType state)
      let some stateName := stateType.getAppFn.constName?
        | throwErrorAt s "kprologue: expected a state with a structure type"
      let some _ := getStructureInfo? env stateName
        | throwErrorAt s "kprologue: `{stateName}` is not a structure"

      let stateFields := getStructureFields env stateName
      let some regsInfo := getFieldInfo? env stateName `regs
        | throwErrorAt s "kprologue: `{stateName}` has no `regs` field"
      let regs ← mkAppM regsInfo.projFn #[state]
      let regsType ← whnf (← inferType regs)
      let some regsName := regsType.getAppFn.constName?
        | throwErrorAt s "kprologue: `{stateName}.regs` does not have a structure type"
      let some _ := getStructureInfo? env regsName
        | throwErrorAt s "kprologue: `{stateName}.regs` is not a structure"

      let regFields := getStructureFields env regsName
      let stateBinderNames :=
        (stateFields.filter (· != `regs)).map kprologueBinderName
      let binderNames := regFields ++ stateBinderNames

      let mut seen : NameSet := {}
      let mut duplicateNames := #[]
      for name in binderNames do
        if seen.contains name then
          unless duplicateNames.contains name do
            duplicateNames := duplicateNames.push name
        else
          seen := seen.insert name
      unless duplicateNames.isEmpty do
        let names := String.intercalate ", " (duplicateNames.toList.map (·.toString))
        throwErrorAt s "kprologue: duplicate local names: {names}"

      let lctx ← getLCtx
      let collisions := binderNames.filter fun name =>
        (lctx.findFromUserName? name).isSome
      unless collisions.isEmpty do
        let names := String.intercalate ", " (collisions.toList.map (·.toString))
        throwErrorAt s
          "kprologue: refusing to shadow existing locals: {names}"

      -- These binders must remain visible after the tactic, so give them no macro scopes.
      let regPats ← regFields.mapM fun field =>
        let id := mkIdentFrom s field
        `(rcasesPat| $id:ident)
      let regsPat ← `(rcasesPat| ⟨$[$regPats],*⟩)
      let statePats ← stateFields.mapM fun field =>
        if field == `regs then
          pure regsPat
        else
          let id := mkIdentFrom s (kprologueBinderName field)
          `(rcasesPat| $id:ident)
      let statePat ← `(rcasesPat| ⟨$[$statePats],*⟩)

      let eventuallyId := mkIdent `Eventually

      evalTactic (← `(tactic|
        (let ss := $s
         change ($eventuallyId:ident _ _ (ss, _))
         obtain $statePat:rcasesPat := $s
         delta $p at *)))

--------------------------------------------------------------------------------

open Sym Sym.DSimp

partial def peelLambdaLets (f : Expr) (args : Array Expr) (fvars : Array Expr) (k : Expr → Array Expr → DSimpM Result) : DSimpM Result := do
  -- (fun y => let x = e1 in e2) () ~~> let x = e1 in (fun y => e2) ()
  match f with
  | .lam binderName binderType body binderInfo =>
    match body with
    | .letE letName letType letVal letBody _ =>
      if !letType.hasLooseBVar 0 && !letVal.hasLooseBVar 0 then
        withLetDecl letName letType letVal fun fvarLet => do
          -- substitute open variable x for 0 in e2, shifting all other variables by 1
          let instBody : Expr := letBody.instantiate1 fvarLet
          -- meaning we can close in DeBruijn directly
          let newLambda := .lam binderName binderType instBody binderInfo
          -- and add our open variable to the list of variables to be folded over
          peelLambdaLets newLambda args (fvars.push fvarLet) k
      else
        k (mkAppN f args) fvars
    | _ => k (mkAppN f args) fvars
  | _ => k (mkAppN f args) fvars

partial def peelLets (e : Expr) (fvars : Array Expr) (k : Expr → Array Expr → DSimpM Result) : DSimpM Result := do
  match e with
  | .letE name type val body _ =>
    withLetDecl name type val fun fvar =>
      peelLets (body.instantiate1 fvar) (fvars.push fvar) k
  | _ =>
    if e.isApp && e.getAppFn.isLambda then
      peelLambdaLets e.getAppFn e.getAppArgs fvars k
    else
      k e fvars

partial def peelArgsLets (args : Array Expr) (i : Nat) (peeled : Array Expr) (fvars : Array Expr) (k : Array Expr → Array Expr → DSimpM Result) : DSimpM Result := do
  if h : i < args.size then
    let arg := args[i]
    peelLets arg fvars fun arg' fvars' =>
      peelArgsLets args (i + 1) (peeled.push arg') fvars' k
  else
    k peeled fvars

def kdeltaBetaOnly (targets: List Name) : DSimproc := fun e => do
  -- This focuses on application nodes.
  unless e.isApp && targets.any e.getAppFn'.isConstOf do return .rfl

  let f := e.getAppFn'
  let args := e.getAppArgs

  -- In order to unblock reduction, Meta.unfoldDefinition will happily inline
  -- away let-bindings to make e.g. a constructor appear as an argument to a
  -- match recursor. We intervene ahead of time, and hoist the lets that appear in
  -- argument position, which we know for a fact happens quite a bunch in our
  -- semantics. Concretely: `f (let x = ... in arg)` => `let x = ... in f arg`.
  peelArgsLets args 0 #[] #[] fun (args : Array Expr) (fvars : Array Expr) => do

    if f.isConstOf `Effects.All && args[1]!.isApp && args[1]!.getAppFn'.isConstOf `Directives.interp then
      -- Finding a node of the form `Effects.All ... (Directives.interp ...)`
      -- means that we are ready to step through. We manually force reduction of
      -- Directives.interp (since it is *not* is our list of targets), then let
      -- everything simplify until we're called again.
      let some arg1 ← Meta.unfoldDefinition? args[1]! true | throwError "can't unfold Directives.interp"
      let e := mkAppN f (args.set! 1 arg1)
      let e' ← shareCommon e
      let e'' ← mkLetFVars fvars e'
      return .step e''
      -- TODO: we could here have a post := in the simproc that forces the
      -- result to be .step ... (done := true) to prevent the next unrolling of
      -- Directives.interp from being applied. This would essentially allow
      -- implementing a kstep1 tactic (and leave it to done := false to keep
      -- stepping until something blocks).

      -- Essentially this behavior allows us to keep reducing and stepping,
      -- until we have no steps left to apply and YET the goal has landed us
      -- back on something that is neither Effects.All ... (Directives.interp
      -- ...), nor Effects.All ... (require_exec_access ...), handled in the
      -- case below.
    else
      -- Application, *sans* the let-bindings in the arguments.
      let e_rebuilt := mkAppN f args
      -- Remember that `Meta.unfoldDefinition` is "smart" and wants to see the whole
      -- application node `f ...` before deciding whether it's worth doing a step of
      -- delta and replacing `f` with its definition.
      if let some e' ← Meta.unfoldDefinition? e_rebuilt true then
        /- let step := (← get).numSteps -/
        /- logInfo m!"deltaBetaOnly {step}: {e_rebuilt}\nunfolds to:{e'}" -/
        let e' ← shareCommon e'
        let e'' ← betaRevS e'.getAppFn e'.getAppRevArgs
        let e'' ← mkLetFVars fvars e''
        /- logInfo m!"deltaBetaOnly {step}: {e}\nunfolds to:{e'}\nreduces to: {e''}" -/
        return .step e''
      else if fvars.size > 0 then
        -- Can't reduce application, but we should at least hoist the lets!
        let e ← mkLetFVars fvars e_rebuilt
        return .step e
      else
        -- Really nothing to do here.
        return .rfl

-- Enable with `set_option trace.Kraken.kstep true`.
initialize registerTraceClass `Kraken.kstep

structure KStepConfig where
  debug := false
declare_term_config_elab elabKStepConfig KStepConfig

syntax (name := symKStep) "kstep" optConfig (ppSpace num)? : grind

def kdsimpMatch: DSimproc := fun e => do
  let some e' ← reduceRecMatcher? e | return .rfl
  -- Iota-reduction may expose kernel `Expr.proj` terms via struct-eta,
  -- which the structural simplifier cannot consume directly.
  let e'' ← Sym.foldProjs e'
  if isSameExpr e e'' then
    return .rfl
  else
    return .step (← share e'')

def kbeta: DSimproc := fun e => do
  unless e.isApp do return .rfl
  let f := e.getAppFn
  if f.isHeadBetaTargetFn false then
    let e' ← betaRevS f e.getAppRevArgs
    /- let step := (← get).numSteps -/
    /- logInfo m!"kbeta {step}: {e}\nreduces to\n{e'}" -/
    return .step e'
  else
    return .rfl

def kdsimpProj : DSimproc := fun e => do
  let f := e.getAppFn
  let .const declName _ := f | return .rfl
  let some projInfo ← getProjectionFnInfo? declName | return .rfl
  if projInfo.fromClass && declName != ``Labels.label then
    return .rfl
  let args := e.getAppArgs
  if h : projInfo.numParams < args.size then
    let major := args[projInfo.numParams]
    if let some f ← withDefault (reduceProj? (mkProj declName.getPrefix projInfo.i major)) then
      return .step (← shareCommon (mkAppN f (args.extract (projInfo.numParams + 1) args.size)))
  return .rfl

def kdsimpFindLabel : DSimproc := fun e => do
  let_expr Option.getD _ opt _ := e | return .rfl
  unless opt.isAppOf ``List.findSome? do return .rfl
  let opt' ← withTransparency .all (whnf opt)
  let_expr Option.some _ val := opt' | return .rfl
  let val' ← Meta.transform val (pre := fun sub => do
    if sub.isAppOfArity ``Kraken.Layout.size 3 then
      let args := sub.getAppArgs
      let idx' ← withTransparency .all (reduce args[2]!)
      return .done (mkAppN sub.getAppFn (args.set! 2 idx'))
    return .continue)
  return .step (← share val')

def kLiftLets : DSimproc := fun e => do
  -- We only lift lets to the top-level (which is always an application of
  -- Effects.All)
  unless e.isApp && e.getAppFn'.isConstOf `Effects.All do return .rfl
  let e' ← Sym.liftLets e
  if isSameExpr e e' then return .rfl else return .step e'

def zetaFVars (e : Expr) : MetaM Expr :=
  Meta.transform e (usedLetOnly := true) (pre := fun sub => do
    let .fvar fvarId := sub.getAppFn | return .continue
    let some decl ← fvarId.findDecl? | return .continue
    let some val := decl.value? (allowNondep := true) | return .continue
    return .visit <| (← instantiateMVars val).beta sub.getAppArgs)

def kdsimpIteCond : DSimproc := fun e => do
  let_expr f@ite α c inst a b := e | return .rfl
  let c' ← zetaFVars c
  if c' == c then return .rfl
  let inst' ← zetaFVars inst
  return .step (← shareCommon (mkApp5 f α c' inst' a b))

def skipEventuallyDSimp : DSimproc := fun e => do
  if e.isAppOf ``Eventually then return .rfl (done := true) else return .rfl

def skipEventuallySimp : Sym.Simp.Simproc := fun e => do
  if e.isAppOf ``Eventually then return .rfl (done := true) else return .rfl

def preprocessGoal (goal : Grind.Goal) : Grind.GrindTacticM Grind.Goal := do
  let target' ← Grind.liftSymM <| Sym.preprocessExpr (← goal.mvarId.getType)
  return { goal with mvarId := ← goal.mvarId.replaceTargetDefEq target' }

def dsimpGoal (goal : Grind.Goal) (methods : Sym.DSimp.Methods) (config : Sym.DSimp.Config := {}) :
    Grind.GrindTacticM Grind.Goal := do
  let target' ← Grind.liftGrindM <| Sym.dsimp (config := config) (methods := methods) (← goal.mvarId.getType)
  return { goal with mvarId := ← goal.mvarId.replaceTargetDefEq target' }

def addDeclsAndLCtxTheorems (thms : Sym.Simp.Theorems) (decls : List Name) : MetaM Sym.Simp.Theorems := do
  let mut thms := thms
  for decl in decls do
    thms := thms.insert (← Sym.Simp.mkTheoremFromDecl decl)
  for ldecl in ← getLCtx do
    unless !ldecl.isImplementationDetail do continue
    try
      thms := thms.insert (← Sym.Simp.mkTheoremFromExpr ldecl.toExpr)
    catch _ =>
      pure ()
  return thms

def addDirectiveAddressTheorems (thms : Sym.Simp.Theorems) : MetaM Sym.Simp.Theorems := do
  let mut thms := thms
  let lctx ← getLCtx
  let lctx := ForIn.toArray lctx |>.filter (not ·.isImplementationDetail)
  for ldecl in lctx do
    let mkApp2 (.const ``Layout.Valid _) layoutExpr progExpr := ldecl.type | continue
    let hlayout := ldecl.toExpr
    thms := thms.insert (← Sym.Simp.mkTheoremFromExpr
      (← mkAppM ``Executable.directivesAtStart #[progExpr, hlayout]))
    for ldecl_wf in lctx do
      let mkApp2 (.const ``Kraken.Executable.WellFormed _) _ _ := ldecl_wf.type | continue
      let mut addrExpr ← mkAppOptM ``Kraken.Layout.start #[none, some layoutExpr]
      for n in [1:8] do
        let szExpr ← mkAppOptM ``Kraken.Layout.size #[none, some layoutExpr, some (mkNatLit (n - 1))]
        addrExpr ← mkAppM ``HAdd.hAdd #[addrExpr, ← mkAppM ``Int64.ofNat #[szExpr]]
        let validApp ← mkAppM ``validSplitIndex #[progExpr, mkNatLit n]
        if ← isDefEq validApp (mkConst ``true) then
          let haddr ← mkEqRefl addrExpr
          let hvalid ← mkEqRefl (mkConst ``true)
          for thm in [``Executable.directivesAtAddress_add, ``Executable.directivesFromAddress_add] do
            let e ← mkAppM thm #[progExpr, ldecl_wf.toExpr, hlayout, mkNatLit n, haddr, hvalid]
            thms := thms.insert (← Sym.Simp.mkTheoremFromExpr e)
  return thms

def prepStepGoal (goal : Grind.Goal) : Grind.GrindTacticM Grind.Goal :=
  goal.withContext do
    let goal ← preprocessGoal goal
    let goal ← dsimpGoal goal {
      pre := skipEventuallyDSimp >>
        kdeltaBetaOnly [`step1, `Executable.step, `straightlineStep, `Executable.straightline] >>
        kdsimpProj >> kbeta
    }
    let initTheorems ← addDirectiveAddressTheorems (← addDeclsAndLCtxTheorems {} [
      ``Kraken.Executable.directivesFromStart,
      ``Kraken.takeAtAddressWith.eq_1,
      ``Kraken.takeAtAddressWith.eq_2,
      ``Directive.isZeroSize.eq_1,
      ``Directive.isZeroSize.eq_2,
      ``Directive.isZeroSize.eq_3,
      ``List.drop_zero,
      ``List.drop_succ_cons,
      ``List.mapIdx_nil,
      ``List.mapIdx_cons,
      ``Bool.false_eq_true,
      ``_root_.ite_true,
      ``_root_.ite_false
    ])
    let initSimpMethods : Sym.Simp.Methods := {
      pre := skipEventuallySimp,
      post := Sym.Simp.evalGround >> initTheorems.rewrite
    }
    let mut goal := goal
    for _ in [:20] do
      match ← Grind.liftGrindM <| Sym.simpGoal goal.mvarId initSimpMethods with
      | .goal mvarId =>
        goal ← dsimpGoal { goal with mvarId } {
          pre := skipEventuallyDSimp >> evalGround >> kdsimpProj >> kbeta,
          post := evalGround >> kdsimpProj >> kbeta
        }
      | .noProgress => break
      | .closed => throwError "unexpected"
    pure goal

-- FIXME: a copy-paste of the Lean implementation since it's marked as private
def rwTarget (goal: Grind.Goal) (symm : Bool) (term : Expr) : Grind.GrindTacticM (Grind.Goal × List Grind.Goal) := do
  goal.withContext do
    let mvarCounterSaved := (← getMCtx).mvarCounter
    let target ← goal.mvarId.getType
    let (eNewRaw, eqProof, mvarIds) ← Term.withSynthesize do
      let heq := term
      /-
      The target is in `sym` normal form (e.g., reducible constants have been unfolded), but the
      given equation is not. We unfold reducible constants in its statement so that `kabstract`
      key-matching can find occurrences of the lhs in the target, and the rhs requires less
      normalization after the rewrite.
      -/
      let heqType ← instantiateMVars (← inferType heq)
      let heqType' ← Sym.unfoldReducible heqType
      let heq ← if isSameExpr heqType heqType' then pure heq else mkExpectedTypeHint heq heqType'
      letTelescope target (preserveNondepLet := false) fun fvars body => do
        let tmpMVar ← mkFreshExprMVar body (userName := ← goal.mvarId.getTag)
        let r ← tmpMVar.mvarId!.rewrite body heq symm
        let mctx ← getMCtx
        let mvarIds := r.mvarIds.filter fun mvarId => (mctx.getDecl mvarId |>.index) >= mvarCounterSaved
        let eNew ← mkLetFVars (usedLetOnly := false) (generalizeNondepLet := false) fvars (← instantiateMVars r.eNew)
        let eqProof ← mkLetFVars (usedLetOnly := false) (generalizeNondepLet := false) fvars (← instantiateMVars r.eqProof)
        let mvarIds ← mvarIds.mapM fun mvarId => do
          let mvarId' := (← instantiateMVars (mkMVar mvarId)).getAppFn.mvarId!
          mvarId'.setTag (← mvarId.getTag)
          return mvarId'
        return (eNew, eqProof, mvarIds)
    let eNew ← Grind.liftSymM <| Sym.preprocessExpr eNewRaw
    let mvarId ← goal.mvarId.replaceTargetEq eNew eqProof
    let mvarIds ← mvarIds.filterM fun mvarId => return !(← mvarId.isAssigned)
    let sideGoals ← mvarIds.mapM fun mvarId => mvarId.withContext do
      let target ← mvarId.getType
      let target' ← Grind.liftSymM <| Sym.preprocessExpr (← zetaReduce target)
      if isSameExpr target target' then
        -- The metavariable was created by `forallMetaTelescopeReducing` with kind `.natural`;
        -- prevent it from being assigned by unification in later steps.
        mvarId.setKind .syntheticOpaque
        return { goal with mvarId }
      else
        let mvarId ← mvarId.replaceTargetDefEq target'
        return { goal with mvarId }
    pure ({ goal with mvarId }, sideGoals)

def dsimpMethods (env : Environment) : Sym.DSimp.Methods :=
  let declsForDSimp := (kstepExtension.getState env).toList
  let kdsimpDecls := kdeltaBetaOnly declsForDSimp
  {
    pre := evalGround >> kLiftLets >> kdsimpDecls >> kdsimpMatch >> kdsimpProj >> kdsimpIteCond >> kbeta,
    post := evalGround >> kdsimpMatch >> kdsimpProj >> kdsimpFindLabel >> kbeta
  }

partial def kstepLoop
    (config : KStepConfig)
    (simpMethods : Sym.Simp.Methods)
    (specTree : DiscrTree Name)
    (goal : Grind.Goal) : Grind.GrindTacticM (Grind.Goal × List Grind.Goal) := do
  -- STEP 1: dsimp
  let methods := dsimpMethods (←getEnv)
  let goal ← do
    let goal ← dsimpGoal goal methods { maxSteps := 1000000 }
    let target ← Grind.liftSymM (Sym.liftLets (← goal.mvarId.getType) >>= Sym.letToHave)
    pure { goal with mvarId := ← goal.mvarId.replaceTargetDefEq target }
  if config.debug then
    let t ← goal.mvarId.getType
    logInfo m!"MAIN LOOP, after step 1: {t}"

  -- STEP 2: simp
  let (keepGoingSimp, goal) ← Grind.liftGrindM $ do
    let simpResult ← Sym.simpGoal goal.mvarId simpMethods
    match simpResult with
    | .noProgress => pure (false, goal)
    | .goal mvarId => pure (true, { goal with mvarId })
    | .closed => throwError "unexpected"
  if config.debug then
    let t ← goal.mvarId.getType
    logInfo m!"MAIN LOOP, after step 2: {t}"

  -- STEP 3: spec lemmas
  let goalState ← do
    let goalT ← instantiateMVars (← goal.mvarId.getType)
    let rec getEffectsState (e : Expr) : Option Expr :=
      match e with
      | .letE _ _ _ body _ => getEffectsState body
      | .forallE _ _ body _ => getEffectsState body
      | .mdata _ e => getEffectsState e
      | mkApp2 (.const ``Effects.All _) _ state => some state
      | _ => none
            -- No more Effects.All in the goal -- return to the user (we might be done,
    -- or realistically, we might need to debug).
    let some state := getEffectsState goalT | return (goal, [])
    pure state

  let (keepGoingSpec, goal) ←
    match Sym.getMatch (← getMCtx) specTree goalState with
    | #[ thmName ] =>
      logInfo m!"Found a spec lemma: {thmName}"
      let (goal, subGoals) ← rwTarget goal false (mkConst thmName)
      logInfo m!"{subGoals.length} subgoals generated"

      let subGoals ← subGoals.mapM fun (subGoal: Grind.Goal) => subGoal.withContext do
        -- Try simp -- who knows, one might get lucky
        let subGoal ← dsimpGoal subGoal methods { maxSteps := 1000000 }
        let simpResult ← Grind.liftGrindM (Sym.simpGoal subGoal.mvarId simpMethods)
        match simpResult with
        | .noProgress => pure subGoal
        | .goal mvarId => pure { subGoal with mvarId }
        | .closed => pure subGoal

      -- Found a spec lemma, which will generate subgoals; for now, subgoals (if not solved
      -- already!) are solved via `exact` (which may pick any hypothesis in the context, beware),
      -- or grind.
      let solveIfNotAlready: Grind.Goal → Grind.GrindTacticM Bool := fun subGoal => do
        -- Already solved this subgoal; skip
        if ← subGoal.mvarId.isAssigned then
          let t ← subGoal.mvarId.getType
          logInfo m!"Already solved: {t}"
          return false

        -- Solvable with exact; we made progress
        if ← withReducible subGoal.mvarId.assumptionCore then
          let t ← subGoal.mvarId.getType
          let .some e ← getExprMVarAssignment? subGoal.mvarId | throwError "oh noes"
          logInfo m!"Solved by exact: {t} by {e}"
          return true

        if (← subGoal.mvarId.getType).getAppFn.isConstOf `Std.ExtHashMap.sep then
          if ← Kraken.Tactic.solveSepGoal subGoal.mvarId then
            let t ← subGoal.mvarId.getType
            let .some e ← getExprMVarAssignment? subGoal.mvarId | throwError "oh noes"
            logInfo m!"Solved by ecancel: {t} by {e}"
            return true
          return false

        -- Solvable with refl, maybe.
        try
          subGoal.mvarId.refl
          let t ← subGoal.mvarId.getType
          logInfo m!"Solved by refl: {t}"
          return true
        catch _ => pure ()

        -- Try solving with grind, roll back state otherwise (we don't want to
        -- return the failed Grind state).
        try
          let subGoal ← Grind.liftGrindM subGoal.internalizeAll
          let t ← subGoal.mvarId.getType
          match ← Grind.liftGrindM subGoal.grind with
          | .closed =>
              logInfo m!"Solved by grind: {t}"
              return true
          | .failed _ =>
              logInfo m!"NOT solved by grind: {t}"
              throwError "catch me"
        catch _ =>
          return false

      -- For this reason, we try to be intentional about the order in which we solve subgoals:
      -- solving the ⋆ separation logic predicate first allows making sensible decisions about
      -- metavariables, rather than picking any random hypothesis in the context
      let starGoal ← subGoals.findM? (fun g => do
        let t ← g.mvarId.getType
        if t.getAppFn.isConstOf `Std.ExtHashMap.sep then
          logInfo m!"Found sep goal: {t}"
          return true
        else
          return false
      )

      -- If we couldn't solve the ⋆ goal, we are likely going to make bad
      -- decisions and instantiate metavariables randomly. Abort.
      if let some g := starGoal then
        let solved ← solveIfNotAlready g
        if not solved then
          return (goal, subGoals)

      -- Then, we repeatedly visit subgoals until we make no progress.
      while ← (
        subGoals.foldlM (fun progress subGoal => do
          let r ← solveIfNotAlready subGoal
          pure (r || progress)
        ) false
      ) do pure ()

      -- Unsolved goals left? Return control to the user
      let unsolvedGoals ← subGoals.filterMapM fun (g: Grind.Goal) => do
        if ← g.mvarId.isAssigned then
          return none
        else
          return some g
      unsolvedGoals.forM fun mvarId => do
        let t ← mvarId.mvarId.getType
        logInfo m!"Unsolved goal: {t}"
      if unsolvedGoals.length > 0 then
        return (goal, unsolvedGoals)

      pure (true, goal)
    | #[] =>
      pure (false, goal)
    | _ =>
      throwError "TODO"

  logInfo m!"kstep: keepGoing = {keepGoingSimp}"

  if keepGoingSimp || keepGoingSpec then
    kstepLoop config simpMethods specTree goal
  else
    pure (goal, [])

def evalSymKStepCore (config : KStepConfig) (maxSteps? : Option Nat) : Grind.GrindTacticM Unit := do
  let goal : Grind.Goal ← Grind.getMainGoal

  let env ← getEnv

  -- https://lean-lang.org/doc/api/Lean/Meta/Sym/Simp/SimpM.html
  -- note the "contextual ite handling" --> are we doing this?
  let simpTheorems ← goal.withContext do
    addDeclsAndLCtxTheorems (← ksimpExt.getTheorems)
      [``Bool.false_eq_true, ``eq_self, ``_root_.ite_true, ``_root_.ite_false]
  let simpMethods: Sym.Simp.Methods := {
    post := Sym.Simp.evalGround >> simpTheorems.rewrite
  }

  let specLemmas := (kspecExtension.getState env).toList
  let specTree: DiscrTree Name ← specLemmas.foldlM (fun specTree name => do
    -- NOTE: hardcoding left-to-right order, for now
    let (pat, _) ← mkEqPatternFromDecl name
    pure (insertPattern specTree pat name)
  ) {}


  unless (← goal.mvarId.getType).consumeMData.isAppOf ``Eventually do
    throwError "kstep: expected goal to be of the form Eventually"

  match maxSteps? with
  | .some maxSteps =>
      let mut goal := goal
      let mut allSubGoals : List Grind.Goal := []
      for _ in [:maxSteps] do
        unless (← goal.mvarId.getType).consumeMData.isAppOf ``Eventually do
          throwError "kstep: expected goal to be of the form Eventually"
        let [mvarId] ← goal.withContext <|
          goal.mvarId.apply (← mkConstWithFreshMVarLevels ``eventually_step_cps) | failure
        goal ← prepStepGoal { goal with mvarId }
        let (g, subGoals) ← kstepLoop config simpMethods specTree goal
        goal := g
        allSubGoals := allSubGoals ++ subGoals

      logInfo m!"END KSTEP: {allSubGoals.length} sub-goals left"
      Grind.setGoals (allSubGoals ++ [ goal ])
  | .none =>
      let [subGoal, mvarId] ← goal.withContext <|
        goal.mvarId.apply (← mkConstWithFreshMVarLevels ``eventually_straightlineStep_cps) | failure
      subGoal.withContext subGoal.assumption
      let goal ← prepStepGoal { goal with mvarId }
      let (goal, subGoals) ← kstepLoop config simpMethods specTree goal

      logInfo m!"END KSTEP: {subGoals.length} sub-goals left"
      Grind.setGoals (subGoals ++ [ goal ])

@[grind_tactic symKStep]
partial def evalSymKStep : Grind.GrindTactic :=
  fun stx : Syntax => do
  let cfg := stx[1]
  let config ← elabKStepConfig cfg
  let maxSteps? : Option Nat := if stx[2].isNone then none else some stx[2][0].toNat
  -- A `sym` tactic operates over a pair of the grind state and an MVarId. To avoid scope mistakes,
  -- we only ever use `goal` and never let-bind mvarId.
  evalSymKStepCore config maxSteps?

syntax (name := symRotateRight) "rotate_right" (ppSpace num)? : grind

@[grind_tactic symRotateRight]
def evalSymRotateRight : Grind.GrindTactic := fun stx => do
  let n := if stx[1].isNone then 1 else stx[1][0].toNat
  let goals ← Grind.getGoals
  Grind.setGoals (goals.rotateRight n)
