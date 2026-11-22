module

/-
Common Kraken Proof Tactics.

Core tactics and theorems for stepping through Kraken assembly proofs.
-/

public import Kraken.Attribute
import Kraken.Layout
import Kraken.Separation

public meta section

open Lean Meta Elab Tactic.Grind MainGoal Kraken

/-- Set up a straight-line proof for `p` from `s`, naming the state fields and
general-purpose registers. `status` and `dmem` are called `flags` and `mem`. -/
syntax (name := kprologue) "kprologue" ident "with" ident : tactic

private def kprologueBinderName (field : Lean.Name) : Lean.Name :=
  if field == `status then `flags
  else if field == `dmem then `mem
  else field

elab_rules : tactic
  | `(tactic| kprologue $p:ident with $s:ident) => Tactic.withMainContext do
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

      let straightlineStepId := mkIdent `straightlineStep
      let execStraightlineId := mkIdent `Executable.straightline

      Tactic.evalTactic (← `(tactic|
        (let ss := $s
         change ($straightlineStepId:ident _ ⟨ss, _⟩ _)
         obtain $statePat:rcasesPat := $s
         delta $p
         dsimp only [$straightlineStepId:ident, $execStraightlineId:ident]
         rw [Executable.directivesFromStart]
         simp [List.mapIdx, List.mapIdx.go])))

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

def kdeltaBetaOnly (targets: List Name) (maxInstrCount : Option (IO.Ref Nat)) : DSimproc := fun e => do
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
    if f.isConstOf `Effects.All then
      if hArg : 1 < args.size then
        if args[1].isApp && args[1].getAppFn'.isConstOf `Directives.interp then
          -- We optionally track how many times we've hit Directives.interp -- this tracks how
          -- many instructions we've stepped through.
          if (← maxInstrCount.mapM (·.get)) = .some 0 then
            return .rfl
          maxInstrCount.forM (fun r => r.modify (· - 1))

          -- Finding a node of the form `Effects.All ... (Directives.interp ...)`
          -- means that we are ready to step through. We manually force reduction of
          -- Directives.interp (since it is *not* is our list of targets), then let
          -- everything simplify until we're called again.
          let some arg1 ← Meta.unfoldDefinition? args[1] true | throwError "can't unfold Directives.interp"
          let e := mkAppN f (args.set 1 arg1)
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

def gimmickId (p: Prop): Prop := p

theorem gimmick {p: Prop} (h: gimmickId p): p := by
  simp [gimmickId] at h
  assumption

theorem gimmickInv {p: Prop} (h: p): gimmickId p := by
  simp [gimmickId]
  assumption

-- Enable with `set_option trace.Kraken.kstep true`.
initialize registerTraceClass `Kraken.kstep

-- Debugging the reduction steps: to easily have a marker that tells us when we've hit the top-level
-- term, we assume prior to running `kstep`, the user does `apply gimmick`. (This also avoids having
-- to reason about whether we're at the top-level term or not -- we never are.)
def klog : DSimproc := fun e => do
  -- Trace every top-level term to show the various states of the dsimp
  -- call.
  let s := (← get).numSteps
  /- if s = 789 then -/
  /-   return .rfl (done := true) -/
  if let `(gimmickId ?inner) := e then
    trace[Kraken.kstep] "step {s} visiting\n{inner}"
  return .rfl

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
  let some _projInfo ← getProjectionFnInfo? declName | return .rfl
  let reduceProjCont? (e? : Option Expr) : DSimpM Result := do
    match e? with
    | none   => return .rfl
    | some e =>
      match (← reduceProj? e.getAppFn) with
      | some f => return .step (← shareCommon (mkAppN f e.getAppArgs))
      | none   => return .rfl
  -- TODO: special support for instances?
  reduceProjCont? (← unfoldDefinition? e)

def kLiftLets : DSimproc := fun e => do
  -- We only lift lets to the top-level (which is always an application of
  -- Effects.all)
  unless e.isApp && e.getAppFn'.isConstOf `Effects.All do return .rfl

  let (es, st) ← ExtractLets.extract #[e] |>.run {} |>.run' {} |>.run { givenNames := [] }
  unless st.decls.size > 0 do return .rfl

  let e' := Meta.ExtractLets.mkLetDecls st.decls es[0]!
  let e' ← Sym.share e'
  /- logInfo m!"liftLets produces {e'}" -/
  return .step e'

private def stripLeadingLets : Expr → Expr
  | .letE _ _ _ body _ => stripLeadingLets body
  | .mdata _ e         => stripLeadingLets e
  | e                  => e

@[grind_tactic symKStep]
def evalSymKStep : GrindTactic := fun stx => do
  let config ← elabKStepConfig stx[1]
  let maxSteps? : Option Nat := if stx[2].isNone then none else some stx[2][0].toNat

  let env ← getEnv

  let declsForDSimp := (kstepExtension.getState env).toList
  let maxInstrCount ← maxSteps?.mapM (IO.mkRef ·)
  let kdsimpDecls := kdeltaBetaOnly declsForDSimp maxInstrCount
  let dsimpMethods : Sym.DSimp.Methods := {
    pre := klog >> evalGround >> kdsimpDecls >> kdsimpMatch >> kdsimpProj >> kbeta
  }

  -- https://lean-lang.org/doc/api/Lean/Meta/Sym/Simp/SimpM.html
  -- note the "contextual ite handling" --> are we doing this?
  let simpTheorems ← ksimpExt.getTheorems
  let simpMethods : Sym.Simp.Methods := { post := Sym.Simp.evalGround >> simpTheorems.rewrite }

  let specLemmas := (kspecExtension.getState env).toList
  let specTree : DiscrTree Name ← specLemmas.foldlM (fun specTree name => do
    -- NOTE: hardcoding left-to-right order, for now
    let (pat, _) ← mkEqPatternFromDecl name
    pure (insertPattern specTree pat name)
  ) {}

  -- TODO: remove once we have lift_lets
  let introsIf : GrindTacticM Unit := do
    if let `(gimmickId ?inner) := ← getMainTarget then
      let inner := inner.consumeMData
      unless inner.isForall || inner.isLet || inner.getAppFn.isMVar do
        return
    applyDecl ``gimmickInv
    discard intros
    applyDecl ``gimmick

  -- Found a spec lemma, which will generate subgoals; for now, subgoals (if not solved
  -- already!) are solved via `assumption?` (which may pick any hypothesis in the context, beware),
  -- `refl`, or `finish`.
  let solveSubgoal : GrindTacticM Unit := solve1 do
    if ← withReducible assumption? then return
    if ← tryCommit refl then return
    internalizeAll
    finish

  let solveSideGoals : GrindTacticM (List Grind.Goal) := do
    let sideCount := (← getUnsolvedGoals).length
    logInfo m!"{sideCount} subgoals generated"
    if sideCount == 0 then return []
    -- Try simp -- who knows, one might get lucky
    allGoals (discard <| simpMainGoal simpMethods)

    -- For this reason, we try to be intentional about the order in which we solve subgoals:
    -- solving the ⋆ separation logic predicate first allows making sensible decisions about
    -- metavariables, rather than picking any random hypothesis in the context
    if let some solved ← firstGoal? do
        let t ← getMainTarget
        let `(Std.ExtHashMap.sep _ _ _) := t | failure
        logInfo m!"Found sep goal: {t}"
        tryCommit solveSubgoal then
      -- If we couldn't solve the ⋆ goal, we are likely going to make bad
      -- decisions and instantiate metavariables randomly. Abort.
      unless solved do
        return ← getUnsolvedGoals

    -- Then, we repeatedly visit unsolved subgoals until we make no progress.
    while (← tryCommit (anyGoals solveSubgoal)) do
      pure ()

    allGoals do
      logInfo m!"Unsolved goal: {← getMainTarget}"
    getUnsolvedGoals

  -- A `sym` tactic operates over a pair of the grind state and an MVarId. To avoid scope mistakes,
  -- we only ever use `Grind.MainGoal` primitives and never let-bind `mvarId`.
  -- Apply the debug gimmick. We actually *do* expect the goal to be in this form (see comment in
  -- kdeltaBetaOnly).
  focus do
    applyDecl ``gimmick
    let mut subGoals : List Grind.Goal := []

    -- MAIN LOOP
    repeat do
      -- STEP 1: dsimp
      discard <| dsimpMainGoal dsimpMethods { maxSteps := 1000000 }
      introsIf

      if config.debug then
        withMainContext do
          logInfo m!"MAIN LOOP, after step 1: {← getMainTarget}"

      -- TEMPORARY: trying to simplify binders in the goal
      /- let goal ← Meta.letToHave goal -/
      /- let goal ← Grind.liftGrindM $ shareCommon goal -/
      /- let mvarId ← mvarId.replaceTargetDefEq goal -/

      -- STEP 2: simp
      let keepGoingSimp ← match ← simpMainGoalResult simpMethods with
        | .noProgress => pure false
        | .simplified => pure true
        | .closed     => throwError "unexpected"
      if config.debug then
        withMainContext do
          logInfo m!"MAIN LOOP, after step 2: {← getMainTarget}"

      -- STEP 3: spec lemmas
      let `(gimmickId ?goalT') := ← getMainTarget | throwError "missing gimmick"
      -- No more Effects.All in the goal -- return to the user (we might be done,
      -- or realistically, we might need to debug).
      let goalBody := stripLeadingLets goalT'
      unless goalBody.isApp && goalBody.getAppFn.isConstOf `Effects.All &&
          goalBody.getAppArgs.size == 2 do
        break
      let goalState := goalBody.getAppArgs[1]!

      let mut keepGoingSpec := false
      match Sym.getMatch (← getMCtx) specTree goalState with
      | #[ thmName ] =>
        logInfo m!"Found a spec lemma: {thmName}"
        rwTarget (mkConstWithFreshMVarLevels thmName) (allowMVars := true)
        let mainGoal :: sideGoals ← getUnsolvedGoals | throwError "unexpected"
        let remaining ← try setGoals sideGoals; solveSideGoals finally setGoals [mainGoal]
        unless remaining.isEmpty do
          subGoals := remaining
          break
        keepGoingSpec := true
      | #[] => pure ()
      | _ => throwError "TODO"

      logInfo m!"kstep: keepGoing = {keepGoingSimp}"

      unless keepGoingSimp || keepGoingSpec do
        break

    -- Remove the gimmick debug marker.
    applyDecl ``gimmickInv

    logInfo m!"END KSTEP: {subGoals.length} sub-goals left"

    if let .some r := maxInstrCount then
      let remaining ← r.get
      if remaining > 0 then
        throwError m!"kstep could not step through the remaining {remaining} steps"

    let mainGoals ← getUnsolvedGoals
    setGoals (subGoals ++ mainGoals)

syntax (name := symRotateRight) "rotate_right" (ppSpace num)? : grind

@[grind_tactic symRotateRight]
def evalSymRotateRight : GrindTactic := fun stx => do
  let n := if stx[1].isNone then 1 else stx[1][0].toNat
  let goals ← getUnsolvedGoals
  setGoals (goals.rotateRight n)
