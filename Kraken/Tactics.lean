module

/-
Common Kraken Proof Tactics.

Core tactics and theorems for stepping through Kraken assembly proofs.
-/

public import Kraken.Attribute
import Kraken.Layout
import Kraken.OmniSemantics

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

      let step1Id := mkIdent `step1

      evalTactic (← `(tactic|
        (let ss := $s
         change (Eventually ($step1Id:ident (Kraken.Layout.apply _ $p)) _
           ⟨ss, (Kraken.Layout.apply _ $p).startAddr⟩)
         obtain $statePat:rcasesPat := $s
         rw [← Kraken.Executable.addrOf_zero])))

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

def kdeltaBetaOnly (targets : List Name) : DSimproc := fun e => do
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
    -- Application, *sans* the let-bindings in the arguments.
    let e_rebuilt := mkAppN f args
    -- Remember that `Meta.unfoldDefinition` is "smart" and wants to see the whole
    -- application node `f ...` before deciding whether it's worth doing a step of
    -- delta and replacing `f` with its definition.
    if let some e' ← Meta.unfoldDefinition? e_rebuilt true then
      let e' ← shareCommon e'
      let e'' ← betaRevS e'.getAppFn e'.getAppRevArgs
      let e'' ← mkLetFVars fvars e''
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
  if e.isApp && e.getAppFn'.isConstOf ``gimmickId then
    trace[Kraken.kstep] "step {s} visiting\n{e.getAppRevArgs[0]!}"
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
  if declName == `Labels.label then return .rfl
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

-- FIXME: a copy-paste of the Lean implementation since it's marked as private
def rwTarget (goal: Grind.Goal) (symm : Bool) (term : Expr) : Grind.GrindTacticM (Grind.Goal × List Grind.Goal) := do
  goal.withContext do
    let mvarCounterSaved := (← getMCtx).mvarCounter
    let r ← Term.withSynthesize do
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
        -- The metavariable was created by `forallMetaTelescopeReducing` with kind `.natural`;
        -- prevent it from being assigned by unification in later steps.
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
  -- A `sym` tactic operates over a pair of the grind state and an MVarId. To avoid scope mistakes,
  -- we only ever use `goal` and never let-bind mvarId.
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

  -- Apply the debug gimmick. We actually *do* expect the goal to be in this form.
  let goal ← insertGimmick goal

  let env ← getEnv

  let declsForDSimp := (kstepExtension.getState env).toList
  let maxInstrCount ← maxSteps?.mapM (IO.mkRef ·)
  let kdsimpDecls := kdeltaBetaOnly declsForDSimp

  -- https://lean-lang.org/doc/api/Lean/Meta/Sym/Simp/SimpM.html
  -- note the "contextual ite handling" --> are we doing this?
  let simpTheorems ← ksimpExt.getTheorems
  let simpMethods: Sym.Simp.Methods := { post := Sym.Simp.evalGround >> simpTheorems.rewrite }

  let specLemmas := (kspecExtension.getState env).toList
  let specTree: DiscrTree Name ← specLemmas.foldlM (fun specTree name => do
    -- NOTE: hardcoding left-to-right order, for now
    let (pat, _) ← mkEqPatternFromDecl name
    pure (insertPattern specTree pat name)
  ) {}

  -- TODO: remove once we have lift_lets
  let introsIf (goal: Grind.Goal): Grind.GrindTacticM Grind.Goal := do
    let goal ← removeGimmick goal
    let goal ← match ← Grind.liftGrindM (goal.intros #[]) with
      | Grind.IntrosResult.failed => pure goal
      | .goal _ goal => pure goal
    pure (← insertGimmick goal)

  let rec getListElem? (xs : Expr) (i : Nat) : MetaM (Option Expr) := do
    let xs ← whnf xs
    match_expr xs with
    | List.cons _ hd tl =>
      match i with
      | 0 => return some hd
      | i + 1 => getListElem? tl i
    | _ => return none

  let rec findLabelIdx? (xs : Expr) (lbl : Expr) (i : Nat) : MetaM (Option Nat) := do
    let xs ← whnf xs
    match_expr xs with
    | List.cons _ hd tl =>
      let hd ← whnf hd
      match_expr hd with
      | Kraken.Directive.label _ _ l =>
        if ← isDefEq l lbl then
          return some i
        else
          findLabelIdx? tl lbl (i + 1)
      | _ => findLabelIdx? tl lbl (i + 1)
    | _ => return none

  let stepAt? (goal : Grind.Goal) : Grind.GrindTacticM (Option Grind.Goal) := do
    if (← maxInstrCount.mapM (·.get)) == some 0 then
      return none
    let goalT ← goal.withContext do instantiateMVars (← goal.mvarId.getType)
    let_expr gimmickId goalT' := goalT | return none
    let_expr Eventually _ trans post state := goalT' | return none
    unless trans.isAppOfArity `step1 1 do return none
    let exe := trans.getArg! 0
    let_expr Kraken.Layout.apply instrType constType l p := exe | return none
    unless state.isAppOfArity `MachineState.mk 2 do return none
    let s := state.getArg! 0
    let pc := state.getArg! 1
    if pc.isAppOfArity `Labels.label 2 then
      let labelsInst := pc.getArg! 0
      let lblExpr := pc.getArg! 1
      unless labelsInst.isAppOfArity `Executable.labels 1 do return none
      let pcExe := labelsInst.getArg! 0
      let some k ← goal.withContext do
        unless ← isDefEq pcExe exe do return none
        findLabelIdx? p lblExpr 0
      | return none
      let goal ← removeGimmick goal
      let goal ← goal.withContext do
        let isLabelPred ← mkAppOptM ``Kraken.Directive.isLabel #[some instrType, some constType, some lblExpr]
        let findIdxExpr ← mkAppM ``List.findIdx? #[isLabelPred, p]
        let someK ← mkAppM ``Option.some #[mkNatLit k]
        let hkType ← mkEq findIdxExpr someK
        let hkProof ← mkExpectedTypeHint (← mkEqRefl someK) hkType
        let stepFn ← mkAppOptM `step_label
          #[some l, some p, some lblExpr, some (mkNatLit k), some hkProof, some post, some s]
        let .forallE _ hType _ _ ← inferType stepFn | throwError "kstep: unexpected step_label type"
        let hType' ← Grind.liftSymM <| Sym.preprocessExpr hType
        let mvarNew ← mkFreshExprMVar hType'
        goal.mvarId.assign (mkApp stepFn mvarNew)
        return { goal with mvarId := mvarNew.mvarId! }
      return some (← insertGimmick goal)
    let_expr Kraken.Executable.addrOf _ _ pcExe kExpr := pc | return none
    let some k := kExpr.nat? <|> kExpr.rawNatLit? | return none
    let some d ← goal.withContext do
      unless ← isDefEq pcExe exe do return none
      getListElem? p k
    | return none
    unless d.isAppOfArity ``Kraken.Directive.label 3 do
      maxInstrCount.forM (·.modify (· - 1))
    let goal ← removeGimmick goal
    let goal ← goal.withContext do
      let someD ← mkAppM ``Option.some #[d]
      let getElemExpr ← mkAppM ``GetElem?.getElem? #[p, mkNatLit k]
      let hdType ← mkEq getElemExpr someD
      let hdProof ← mkExpectedTypeHint (← mkEqRefl someD) hdType
      let stepFn ← mkAppOptM `step_at
        #[some l, some p, none, some (mkNatLit k), some d, some hdProof, some post, some s]
      let .forallE _ hType _ _ ← inferType stepFn | throwError "kstep: unexpected step_at type"
      let hType' ← Grind.liftSymM <| Sym.preprocessExpr hType
      let mvarNew ← mkFreshExprMVar hType'
      goal.mvarId.assign (mkApp stepFn mvarNew)
      return { goal with mvarId := mvarNew.mvarId! }
    some <$> insertGimmick goal

  -- MAIN LOOP
  let rec go (goal: Grind.Goal): Grind.GrindTacticM (Grind.Goal × List Grind.Goal) := do
    -- STEP 1: dsimp
    let goal ← goal.withContext do
      let mvarId ← goal.mvarId.replaceTargetDefEq (← Grind.liftGrindM <|
        Sym.dsimp
          (config := { maxSteps := 1000000 })
          (methods := { pre := klog >> kdsimpDecls >> kdsimpMatch >> kdsimpProj >> kbeta })
          (← goal.mvarId.getType))
      let mvarId ← mvarId.replaceTargetDefEq (← Grind.liftGrindM <|
        Sym.dsimp
          (config := { maxSteps := 1000000 })
          (methods := {
            pre := klog >> evalGround >> kdsimpDecls >> kdsimpMatch >> kdsimpProj >> kbeta })
          (← mvarId.getType))
      introsIf ({ goal with mvarId })

    if config.debug then
      goal.withContext do
        logInfo m!"MAIN LOOP, after step 1: {goal.mvarId}"

    -- STEP 2: simp
    let (keepGoingSimp, goal) ← goal.withContext do
      Grind.liftGrindM do
        let simpResult ← Sym.simpGoal goal.mvarId simpMethods
        match simpResult with
        | .noProgress => pure (false, goal)
        | .goal mvarId => pure (true, { goal with mvarId })
        | .closed => throwError "unexpected"
    if config.debug then
      goal.withContext do
        let t ← goal.mvarId.getType
        logInfo m!"MAIN LOOP, after step 2: {t}"

    if let some goal' ← stepAt? goal then
      return ← go goal'

    -- STEP 3: spec lemmas
    goal.withContext do
      let goalT ← goal.mvarId.getType
      let_expr gimmickId goalT' := goalT | throwError "missing gimmick"
      let goalT' ← instantiateMVars goalT'
      let rec getEffectsState (e : Expr) : Option Expr :=
        match e with
        | .letE _ _ _ body _ => getEffectsState body
        | .mdata _ e => getEffectsState e
        | _ =>
          if e.isApp && e.getAppFn.isConstOf `Effects.All && e.getAppArgs.size == 2 then
            some e.getAppArgs[1]!
          else
            none
      -- No more Effects.All in the goal -- return to the user (we might be done,
      -- or realistically, we might need to debug).
      let some goalState := getEffectsState goalT' | return (goal, [])

      let (keepGoingSpec, goal) ←
        match Sym.getMatch (← getMCtx) specTree goalState with
        | #[ thmName ] =>
          logInfo m!"Found a spec lemma: {thmName}"
          let (goal, subGoals) ← rwTarget goal false (mkConst thmName)
          logInfo m!"{subGoals.length} subgoals generated"

          let subGoals ← subGoals.mapM fun (subGoal: Grind.Goal) => do
            -- Try simp -- who knows, one might get lucky
            let simpResult ← Grind.liftGrindM (Sym.simpGoal subGoal.mvarId simpMethods)
            match simpResult with
            | .noProgress => pure subGoal
            | .goal mvarId => pure { subGoal with mvarId }
            | .closed => pure subGoal

          -- Found a spec lemma, which will generate subgoals; for now, subgoals (if not solved
          -- already!) are solved via `exact` (which may pick any hypothesis in the context,
          -- beware), or grind.
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
        go goal
      else
        pure (goal, [])

  let (goal, subGoals) ← go goal

  -- Remove the gimmick debug marker.
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
