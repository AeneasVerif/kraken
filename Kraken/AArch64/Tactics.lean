import Kraken.AArch64.Syntax
import Kraken.AArch64.Semantics
import Kraken.AArch64.OmniSemantics
import Kraken.AArch64.Sep

theorem Executable.withAddresses_map_snd (ds : List (Directive × Nat)) (a : Int64) :
    (Executable.withAddresses (a, ds)).map (·.2) = ds := by
  induction ds generalizing a with
  | nil =>
    unfold Executable.withAddresses
    rfl
  | cons d ds ih =>
    unfold Executable.withAddresses
    grind

theorem Executable.withAddresses_dropWhile_start (ds : List (Directive × Nat)) (a : Int64) :
    (Executable.withAddresses (a, ds)).dropWhile (fun x => x.1 ≠ a) =
      Executable.withAddresses (a, ds) := by
  cases ds with
  | nil =>
    unfold Executable.withAddresses
    rfl
  | cons d ds =>
    unfold Executable.withAddresses
    simp [List.dropWhile]

theorem Executable.directivesFromStart [layout : Layout] prog :
    (layout prog).directivesFromAddress layout.start =
      prog.mapIdx (fun i d => (d, layout.size i)) := by
  dsimp [Executable.directivesFromAddress, Layout.apply]
  rw [Executable.withAddresses_dropWhile_start]
  rw [Executable.withAddresses_map_snd]

macro "kprologue" p:ident : tactic =>
  `(tactic|
    (delta $p
     dsimp only [straightlineStep, Executable.straightline]
     rw [Executable.directivesFromStart]
     simp [List.mapIdx, List.mapIdx.go]))

--------------------------------------------------------------------------------

open Lean Meta Sym Sym.DSimp
open Elab Tactic

partial def peelLambdaLets (f : Expr) (args : Array Expr) (fvars : Array Expr) (k : Expr → Array Expr → DSimpM Result) : DSimpM Result := do
  match f with
  | .lam binderName binderType body binderInfo =>
    match body with
    | .letE letName letType letVal letBody _ =>
      if !letType.hasLooseBVar 0 && !letVal.hasLooseBVar 0 then
        withLetDecl letName letType letVal fun fvarLet => do
          let instBody : Expr := letBody.instantiate1 fvarLet
          let newLambda := .lam binderName binderType instBody binderInfo
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
  unless e.isApp && targets.any e.getAppFn'.isConstOf do return .rfl

  let f := e.getAppFn'
  let args := e.getAppArgs

  peelArgsLets args 0 #[] #[] fun (args : Array Expr) (fvars : Array Expr) => do

    if f.isConstOf ``Effects.All && args[1]!.isApp && args[1]!.getAppFn'.isConstOf ``Directives.interp then
      if (← maxInstrCount.mapM (·.get)) = .some 0 then
        return .rfl
      maxInstrCount.forM (fun r => r.modify (· - 1))

      let some arg1 ← Meta.unfoldDefinition? args[1]! true | throwError "can't unfold Directives.interp"
      let e := mkAppN f (args.set! 1 arg1)
      let e' ← shareCommon e
      let e'' ← mkLetFVars fvars e'
      return .step e''
    else
      let e_rebuilt := mkAppN f args
      if let some e' ← Meta.unfoldDefinition? e_rebuilt true then
        let e' ← shareCommon e'
        let e'' ← betaRevS e'.getAppFn e'.getAppRevArgs
        let e'' ← mkLetFVars fvars e''
        return .step e''
      else if fvars.size > 0 then
        let e ← mkLetFVars fvars e_rebuilt
        return .step e
      else
        return .rfl

def gimmickId (p: Prop): Prop := p

theorem gimmick {p: Prop} (h: gimmickId p): p := by
  simp [gimmickId] at h
  assumption

theorem gimmickInv {p: Prop} (h: p): gimmickId p := by
  simp [gimmickId]
  assumption

initialize registerTraceClass `Kraken.kstep

def klog : DSimproc := fun e => do
  let s := (← get).numSteps
  if e.isApp && e.getAppFn'.isConstOf ``gimmickId then
    trace[Kraken.kstep] "step {s} visiting\n{e.getAppRevArgs[0]!}"
  return .rfl

structure KStepConfig where
  debug := false
declare_term_config_elab elabKStepConfig KStepConfig

syntax (name := symKStep) "kstep" optConfig (ppSpace num)? : grind

def kdsimpMatch: DSimproc := fun e => do
  let some e' ← reduceRecMatcher? e | return .rfl
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
  reduceProjCont? (← unfoldDefinition? e)

def kLiftLets : DSimproc := fun e => do
  unless e.isApp && e.getAppFn'.isConstOf ``Effects.All do return .rfl

  let (es, st) ← ExtractLets.extract #[e] |>.run {} |>.run' {} |>.run { givenNames := [] }
  unless st.decls.size > 0 do return .rfl

  let e' := Meta.ExtractLets.mkLetDecls st.decls es[0]!
  let e' ← Sym.share e'
  return .step e'

def rwTarget (goal: Grind.Goal) (symm : Bool) (term : Expr) : Grind.GrindTacticM (Grind.Goal × List Grind.Goal) := do
  goal.withContext do
    let mvarCounterSaved := (← getMCtx).mvarCounter
    let r ← Term.withSynthesize do
      let heq := term
      let heqType ← instantiateMVars (← inferType heq)
      let heqType' ← Sym.unfoldReducible heqType
      let heq ← if isSameExpr heqType heqType' then pure heq else mkExpectedTypeHint heq heqType'
      goal.mvarId.rewrite (← goal.mvarId.getType) heq symm
    let mctx ← getMCtx
    let mvarIds := r.mvarIds.filter fun mvarId => (mctx.getDecl mvarId |>.index) >= mvarCounterSaved
    let eNew ← Grind.liftSymM <| Sym.preprocessExpr r.eNew
    let mvarId ← goal.mvarId.replaceTargetEq eNew r.eqProof
    let mvarIds ← mvarIds.filterM fun mvarId => return !(← mvarId.isAssigned)
    let sideGoals ← mvarIds.mapM fun mvarId => do
      let target ← mvarId.getType
      let target' ← Grind.liftSymM <| Sym.preprocessExpr target
      if isSameExpr target target' then
        mvarId.setKind .syntheticOpaque
        return { goal with mvarId }
      else
        let mvarId ← mvarId.replaceTargetDefEq target'
        return { goal with mvarId }
    pure ({ goal with mvarId }, sideGoals)

@[grind_tactic symKStep]
partial def evalSymKStep : Grind.GrindTactic :=
  fun stx : Syntax => do
  let cfg := stx[1]
  let config ← elabKStepConfig cfg
  let maxSteps? : Option Nat := if stx[2].isNone then none else some stx[2][0].toNat
  let goal : Grind.Goal ← Grind.getMainGoal

  let gimmickRule ← mkBackwardRuleFromDecl ``gimmick
  let insertGimmick (goal: Grind.Goal): Grind.GrindTacticM Grind.Goal := do
    let .goals [mvarId] ← Grind.liftGrindM (gimmickRule.apply goal.mvarId) | failure
    pure { goal with mvarId }

  let gimmickRule ← mkBackwardRuleFromDecl ``gimmickInv
  let removeGimmick (goal: Grind.Goal): Grind.GrindTacticM Grind.Goal := do
    let mvarId ← Grind.liftGrindM (do
      let .goals [mvarId] ← gimmickRule.apply goal.mvarId | failure
      pure mvarId
    )
    pure { goal with mvarId }

  let goal ← insertGimmick goal
  let env ← getEnv

  let declsForDSimp := (kstepExtension.getState env).toList
  let maxInstrCount ← maxSteps?.mapM (IO.mkRef ·)
  let kdsimpDecls := kdeltaBetaOnly declsForDSimp maxInstrCount

  let simpTheorems ← ksimpExt.getTheorems
  let simpMethods: Sym.Simp.Methods := { post := Sym.Simp.evalGround >> simpTheorems.rewrite }

  let specLemmas := (kspecExtension.getState env).toList
  let specTree: DiscrTree Name ← specLemmas.foldlM (fun specTree name => do
    let (pat, _) ← mkEqPatternFromDecl name
    pure (insertPattern specTree pat name)
  ) {}

  let introsIf (goal: Grind.Goal): Grind.GrindTacticM Grind.Goal := do
    let goal ← removeGimmick goal
    let goal ← match ← Grind.liftGrindM (goal.intros #[]) with
      | Grind.IntrosResult.failed => pure goal
      | .goal _ goal => pure goal
    pure (← insertGimmick goal)

  let rec go (goal: Grind.Goal): Grind.GrindTacticM (Grind.Goal × List Grind.Goal) := do
    let goal ← do
      let mvarId ← goal.mvarId.replaceTargetDefEq (← Grind.liftGrindM $
        Sym.dsimp
          (config := { maxSteps := 1000000 })
          (methods := {
            pre := klog >> evalGround >> kdsimpDecls >> kdsimpMatch >> kdsimpProj >> kbeta })
          (← goal.mvarId.getType))
      introsIf ({ goal with mvarId })

    if config.debug then
      let t ← goal.mvarId.getType
      logInfo m!"MAIN LOOP, after step 1: {goal.mvarId}"

    let (keepGoingSimp, goal) ← Grind.liftGrindM $ do
      let simpResult ← Sym.simpGoal goal.mvarId simpMethods
      match simpResult with
      | .noProgress => pure (false, goal)
      | .goal mvarId => pure (true, { goal with mvarId })
      | .closed => throwError "unexpected"
    if config.debug then
      let t ← goal.mvarId.getType
      logInfo m!"MAIN LOOP, after step 2: {t}"

    let goalState ← do
      let goalT ← goal.mvarId.getType
      let_expr gimmickId goalT' := goalT | throwError "missing gimmick"
      let_expr Effects.All post state := goalT' | return (goal, [])
      pure state

    let (keepGoingSpec, goal) ←
      match getMatch specTree goalState with
      | #[ thmName ] =>
        logInfo m!"Found a spec lemma: {thmName}"
        let (goal, subGoals) ← rwTarget goal false (mkConst thmName)
        logInfo m!"{subGoals.length} subgoals generated"

        let subGoals ← subGoals.mapM fun (subGoal: Grind.Goal) => do
          let simpResult ← Grind.liftGrindM (Sym.simpGoal subGoal.mvarId simpMethods)
          match simpResult with
          | .noProgress => pure subGoal
          | .goal mvarId => pure { subGoal with mvarId }
          | .closed => pure subGoal

        let solveIfNotAlready: Grind.Goal → Grind.GrindTacticM Bool := fun subGoal => do
          if ← subGoal.mvarId.isAssigned then
            let t ← subGoal.mvarId.getType
            logInfo m!"Already solved: {t}"
            return false

          if ← withReducible subGoal.mvarId.assumptionCore then
            let t ← subGoal.mvarId.getType
            let .some e ← getExprMVarAssignment? subGoal.mvarId | throwError "oh noes"
            logInfo m!"Solved by exact: {t} by {e}"
            return true

          try
            subGoal.mvarId.refl
            let t ← subGoal.mvarId.getType
            logInfo m!"Solved by refl: {t}"
            return true
          catch _ => pure ()

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

        let starGoal ← subGoals.findM? (fun g => do
          let t ← g.mvarId.getType
          if t.getAppFn.isConstOf ``Std.ExtHashMap.sep then
            logInfo m!"Found sep goal: {t}"
            return true
          else
            return false
        )

        if let some g := starGoal then
          let solved ← solveIfNotAlready g
          if not solved then
            return (goal, subGoals)

        while ← (
          subGoals.foldlM (fun progress subGoal => do
            let r ← solveIfNotAlready subGoal
            pure (r || progress)
          ) false
        ) do pure ()

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
      go goal
    else
      pure (goal, [])

  let (goal, subGoals) ← go goal
  let goal ← removeGimmick goal
  
  logInfo m!"END KSTEP: {subGoals.length} sub-goals left"

  if let .some r := maxInstrCount then
    let remaining ← r.get
    if remaining > 0 then
      throwError m!"kstep could not step through the remaining {remaining} steps"

  Grind.setGoals (subGoals ++ [ goal ])

syntax (name := symRotateRight) "rotate_right" (ppSpace num)? : grind

@[grind_tactic symRotateRight]
def evalSymRotateRight : Grind.GrindTactic := fun stx => do
  let n := if stx[1].isNone then 1 else stx[1][0].toNat
  let goals ← Grind.getGoals
  Grind.setGoals (goals.rotateRight n)
