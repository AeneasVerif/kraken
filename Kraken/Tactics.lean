module

/-
Common Kraken Proof Tactics.

Core tactics and theorems for stepping through Kraken assembly proofs.
-/

public import Kraken.Attribute
import Kraken.Layout
import Kraken.OmniSemantics
public meta import Kraken.ForLean

public meta section

open Lean Meta Elab Tactic Kraken

/-- Set up a straight-line proof for `p` from `s`, naming the state fields and
general-purpose registers. `status` and `dmem` are called `flags` and `mem`. -/

private def kprologueBinderName (field : Lean.Name) : Lean.Name :=
  if field == `status then `flags
  else if field == `dmem then `mem
  else field

-- NOTE: Do we need this?
elab "kprologue" p:term "with" s:term : tactic => withMainContext do
  evalTactic (← `(tactic|
    (change (Eventually ($(mkIdent `step1):ident (Kraken.Layout.apply $p _)) _
        ⟨$s, (Kraken.Layout.apply $p _).startAddr⟩)
     rw [← Kraken.Executable.addrOf_zero])))

--------------------------------------------------------------------------------


open Sym Sym.DSimp

section
variable {α : Type}

private partial def peelLambdaLetsImp (f : Expr) (args : Array Expr) (fvars : Array Expr)
    (k : Expr → Array Expr → MetaM α) : MetaM α := do
  -- (fun y => let x = e1 in e2) () ~~> let x = e1 in (fun y => e2) ()
  match f with
  | .lam binderName binderType body binderInfo =>
    match body with
    | .letE letName letType letVal letBody nondep =>
      if !letType.hasLooseBVar 0 && !letVal.hasLooseBVar 0 then
        withLetDecl letName letType letVal (nondep := nondep) fun fvarLet => do
          -- substitute open variable x for 0 in e2, shifting all other variables by 1
          let instBody : Expr := letBody.instantiate1 fvarLet
          -- meaning we can close in DeBruijn directly
          let newLambda := .lam binderName binderType instBody binderInfo
          -- and add our open variable to the list of variables to be folded over
          peelLambdaLetsImp newLambda args (fvars.push fvarLet) k
      else
        k (mkAppN f args) fvars
    | _ => k (mkAppN f args) fvars
  | _ => k (mkAppN f args) fvars

private partial def peelLetsImp (e : Expr) (fvars : Array Expr) (k : Expr → Array Expr → MetaM α) : MetaM α := do
  match e with
  | .letE name type val body nondep =>
    withLetDecl name type val (nondep := nondep) fun fvar =>
      peelLetsImp (body.instantiate1 fvar) (fvars.push fvar) k
  | _ =>
    if e.isApp && e.getAppFn.isLambda then
      peelLambdaLetsImp e.getAppFn e.getAppArgs fvars k
    else
      k e fvars

private partial def peelArgsLetsImp (args : Array Expr) (i : Nat) (peeled : Array Expr) (fvars : Array Expr) (k : Array Expr → Array Expr → MetaM α) : MetaM α := do
  if h : i < args.size then
    let arg := args[i]
    peelLetsImp arg fvars fun arg' fvars' =>
      peelArgsLetsImp args (i + 1) (peeled.push arg') fvars' k
  else
    k fvars peeled

def peelArgsLets {n : Type → Type} [MonadControlT MetaM n] [Monad n] (expr : Expr)
    (k : Array Expr → Expr → Array Expr → n α) : n α :=
  expr.withApp fun f args => map2MetaM (fun k => peelArgsLetsImp args 0 #[] #[] k) (k · f)

end

def kdeltaBetaOnly (isTarget : Name → Bool) : DSimproc := fun e => do
  -- This focuses on application nodes.
  unless e.isApp && isTarget e.getAppFn'.constName do return .rfl

  -- In order to unblock reduction, Meta.unfoldDefinition will happily inline
  -- away let-bindings to make e.g. a constructor appear as an argument to a
  -- match recursor. We intervene ahead of time, and hoist the lets that appear in
  -- argument position, which we know for a fact happens quite a bunch in our
  -- semantics. Concretely: `f (let x = ... in arg)` => `let x = ... in f arg`.
  peelArgsLets e fun (fvars : Array Expr) f (args : Array Expr) => do
    -- Application, *sans* the let-bindings in the arguments.
    let e_rebuilt := mkAppN f args
    -- Remember that `Meta.unfoldDefinition` is "smart" and wants to see the whole
    -- application node `f ...` before deciding whether it's worth doing a step of
    -- delta and replacing `f` with its definition.
    if let some e' ← Meta.unfoldDefinition? e_rebuilt true then
      let e' ← shareCommon e'
      let e'' ← betaRevS e'.getAppFn e'.getAppRevArgs
      let e'' ← mkLetFVars fvars e'' (generalizeNondepLet := false)
      return .step e''
    else if fvars.size > 0 then
      -- Can't reduce application, but we should at least hoist the lets!
      let e ← mkLetFVars fvars e_rebuilt (generalizeNondepLet := false)
      return .step e
    else
      -- Really nothing to do here.
      return .rfl

-- Enable with `set_option trace.Kraken.kstep true`.
initialize registerTraceClass `Kraken.kstep
initialize registerTraceClass `Kraken.kstep.loop (inherited := true)
initialize registerTraceClass `Kraken.kstep.dsimp (inherited := true)
initialize registerTraceClass `Kraken.kstep.ksimp (inherited := true)
initialize registerTraceClass `Kraken.kstep.kmem (inherited := true)

structure KStepConfig
declare_term_config_elab elabKStepConfig KStepConfig

syntax (name := symKStep) "kstep" optConfig (ppSpace num)? : grind
syntax (name := tacKStep) "kstep" optConfig (ppSpace num)? : tactic

def kdsimpMatch: DSimproc := fun e => do
  let some e' ← reduceRecMatcher? e | return .rfl
  -- Iota-reduction may expose kernel `Expr.proj` terms via struct-eta,
  -- which the structural simplifier cannot consume directly.
  let e'' ← Sym.foldProjs e'
  if isSameExpr e e'' then
    return .rfl
  else
    return .step (← share e'')

-- Unfolds the definition if it is a projection function to
-- reduce the projection.
def kdsimpProj : DSimproc := fun e => do
  let f := e.getAppFn
  let .const declName _ := f | return .rfl
  if declName == `Labels.label? then return .rfl
  unless ← isProjectionFn declName do return .rfl
  let reduceProjCont? (e? : Option Expr) : DSimpM Result := do
    let some e := e? | return .rfl
    match (← reduceProj? e.getAppFn) with
    | some f => return .step (← shareCommon (mkAppN f e.getAppArgs))
    | none   => return .rfl
  -- TODO: special support for instances?
  reduceProjCont? (← unfoldDefinition? e)

def mkDSimpMethods (env : Environment) : Sym.DSimp.Methods :=
  let kdsimpDecls := kdeltaBetaOnly (kstepExtension.getState env).contains
  { pre := kdsimpDecls >> kdsimpMatch >> kdsimpProj >> beta
    post := evalGround }

def resolveLabelSimproc (thm : Sym.Simp.Theorem) : Sym.Simp.Simproc := fun e => do
  unless e.isAppOfArity `Labels.label? 2 do return .rfl
  withNewMCtxDepth do
    let some result ← thm.pattern.match? e | return .rfl
    let #[_, _, _, .mvar _kMVar, .mvar hkMVar] := result.args | return .rfl
    -- NOTE: Computing the index `k` through unification (result in `_kMVar`).
    -- We should cache this computation.
    try withDefault hkMVar.refl catch _ => return .rfl
    let args ← result.args.mapM fun arg => Sym.instantiateMVarsS arg
    let us ← result.us.mapM instantiateLevelMVars
    let proof := mkAppN (mkConst `label?_eq_some_addrOf us) args
    let rhs ← Sym.share (thm.rhs.instantiateLevelParams thm.pattern.levelParams us)
    let expr ← Sym.instantiateRevBetaS rhs args
    return .step expr proof

def mkSimpMethods : MetaM Sym.Simp.Methods := do
  -- https://lean-lang.org/doc/api/Lean/Meta/Sym/Simp/SimpM.html
  -- note the "contextual ite handling" --> are we doing this?
  let simpTheorems ← ksimpExt.getTheorems
  let post ← if (← getEnv).contains `label?_eq_some_addrOf then
    let thm ← Sym.Simp.mkTheoremFromDecl `label?_eq_some_addrOf
    pure (Sym.Simp.evalGround >> resolveLabelSimproc thm >> simpTheorems.rewrite)
  else
    pure (Sym.Simp.evalGround >> simpTheorems.rewrite)
  -- NOTE: We use `simpControl` to invoke the simplification procedure, whenever we enter
  -- a new subexpression, on the condition / discriminats of the control statement. This
  -- is not done by default by `Sym.simp`, and it is necessary for us to resolve calls to
  -- `Labels.label? lbl` when in a match discriminant. Ideally, we would have a simproc
  -- which behaves like `simpControl` but calls `resolveLabelSimproc` over conditions /
  -- discriminants, instead of all of `simp`, but `simpControl` as implemented
  -- today is not this procedure. `simpControl` is put in `pre` since on success it allows
  -- to skip simplification of branches not taken in the control flow.
  return { pre := Simp.simpControl, post }

private def introsIf (goal : Grind.Goal) : Grind.GrindTacticM Grind.Goal := do
  match ← Grind.liftGrindM (goal.intros #[]) with
  | Grind.IntrosResult.failed => pure goal
  | .goal _ goal => pure goal

private partial def getListElem? (xs : Expr) (i : Nat) : MetaM (Option Expr) := do
  let xs ← whnf xs
  let_expr List.cons _ hd tl := xs | return none
  match i with
  | 0 => return some hd
  | i + 1 => getListElem? tl i

private def getEffectsState : Expr → Option Expr
  | .letE _ _ _ body _ => getEffectsState body
  | .mdata _ e => getEffectsState e
  | mkApp3 (.const `Effects.All _) _ _ eff => some eff
  | _ => none

/- TODO: Check whether computing `d` by unifying with `refl` the `hd` precondition is any
   slower than just getting it from the program directly.  -/
public def stepAt? (maxInstrCount : Option (IO.Ref Nat)) (goal : Grind.Goal) :
    Grind.GrindTacticM (Option Grind.Goal) := do
  if (← maxInstrCount.mapM (·.get)) == some 0 then
    return none
  let stepAtRule ← getOrCreateBackwardRule `step_at
  let .goals [reflPrecond, mvarId, d] ← Grind.liftGrindM (stepAtRule.apply goal.mvarId) | throwError m!"Help me!"
  reflPrecond.refl
  trace[Kraken.kstep] "stepAt: {Expr.mvar d}"
  return some {goal with mvarId}

/-- Step 1 of `kstep`: apply the `@[kstep]` `Sym.dsimp` rewrites and introduce binders. -/
def applyKStepDSimp (goal : Grind.Goal) : Grind.GrindTacticM Grind.Goal :=
  withTraceNode `Kraken.kstep.dsimp (fun _ => return m!"applyKStepDSimp") do
    let dsimpMethods := mkDSimpMethods (← getEnv)
    goal.withContext do
      let mvarId ← goal.mvarId.replaceTargetDefEq (← Grind.liftGrindM <|
        Sym.dsimp
          (config := { maxSteps := 1000000 })
          (methods := dsimpMethods)
          (← goal.mvarId.getType))
      trace[Kraken.kstep.dsimp] "after dsimp:\n{← mvarId.getType}"
      introsIf ({ goal with mvarId })

/-- Step 2 of `kstep`: apply the `@[ksimp]` `Sym.simp` rewrites. -/
def applyKSimp (simpMethods : Sym.Simp.Methods) (goal : Grind.Goal) :
    Grind.GrindTacticM (Bool × Grind.Goal) :=
  withTraceNode `Kraken.kstep.ksimp (fun _ => return m!"applyKSimp") do
    goal.withContext do
      Grind.liftGrindM do
        match ← Sym.simpGoal goal.mvarId simpMethods with
        | .noProgress => pure (false, goal)
        | .goal mvarId => pure (true, { goal with mvarId })
        | .closed => throwError "unexpected"

inductive KMemResult where
  /-- Goal no longer has an `Effects.All` head; stop stepping. -/
  | done (goal : Grind.Goal)
  /-- No `@[kmem]` theorem matched. -/
  | noMatch (goal : Grind.Goal)
  /-- A `@[kmem]` theorem matched and all side goals were solved; continue stepping. -/
  | progress (goal : Grind.Goal)
  /-- A `@[kmem]` theorem matched but left unsolved side goals; pause and return them. -/
  | subgoals (goal : Grind.Goal) (subGoals : List Grind.Goal)

/-- Step 3 of `kstep`: match and rewrite using `@[kmem]` separation-logic memory lemmas. -/
def applyKMem (simpMethods : Sym.Simp.Methods) (goal : Grind.Goal) :
    Grind.GrindTacticM KMemResult :=
  withTraceNode `Kraken.kstep.kmem (fun _ => return m!"applyKMem") do
    goal.withContext do
    let goalT ← goal.mvarId.getType
    let goalT' ← instantiateMVars goalT
    -- No more Effects.All in the goal -- return to the user (we might be done,
    -- or realistically, we might need to debug).
    let some goalState := getEffectsState goalT' | return .done goal

    let kmemTree := kmemExtension.getState (← getEnv)
    let thmNames := Sym.getMatch (← getMCtx) kmemTree goalState
    if thmNames.isEmpty then return .noMatch goal
    let #[thmName] := thmNames | throwError m!"Multiple kmem theorems not yet supported"
    logInfo m!"Found a spec lemma: {thmName}"
    let (goal, subGoals) ← rwTarget goal false (mkConst thmName)
    logInfo m!"{subGoals.length} subgoals generated"

    let subGoals ← subGoals.mapM fun (subGoal : Grind.Goal) => do
      -- Try simp -- who knows, one might get lucky
      let simpResult ← Grind.liftGrindM (Sym.simpGoal subGoal.mvarId simpMethods)
      match simpResult with
      | .noProgress => pure subGoal
      | .goal mvarId => pure { subGoal with mvarId }
      | .closed => pure subGoal

    -- Found a kmem lemma, which will generate subgoals; for now, subgoals (if not solved
    -- already!) are solved via `exact` (which may pick any hypothesis in the context,
    -- beware), or grind.
    let solveIfNotAlready : Grind.Goal → Grind.GrindTacticM Bool := fun subGoal => do
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
        return .subgoals goal subGoals

    -- Then, we repeatedly visit subgoals until we make no progress.
    while ← (
      subGoals.foldlM (fun progress subGoal => do
        let r ← solveIfNotAlready subGoal
        pure (r || progress)
      ) false
    ) do pure ()

    -- Unsolved goals left? Return control to the user
    let unsolvedGoals ← subGoals.filterMapM fun (g : Grind.Goal) => do
      if ← g.mvarId.isAssigned then
        return none
      else
        return some g
    unsolvedGoals.forM fun mvarId => do
      let t ← mvarId.mvarId.getType
      logInfo m!"Unsolved goal: {t}"
    if unsolvedGoals.length > 0 then
      return .subgoals goal unsolvedGoals

    return .progress goal

inductive KStepLoop.Step where
  | continue (goal : Grind.Goal)
  | done (res : Grind.Goal × List Grind.Goal)

partial def kstepLoop
    (config : KStepConfig)
    (maxInstrCount : Option (IO.Ref Nat))
    (goal : Grind.Goal) : Grind.GrindTacticM (Grind.Goal × List Grind.Goal) := do
  let next : KStepLoop.Step ← withTraceNode `Kraken.kstep.loop (fun _ => return m!"kstepLoop") do
    -- STEP 1: kstep dsimp
    let goal ← applyKStepDSimp goal
    if (← getOptions).get `debug (defVal := false) then
      goal.withContext do
        logInfo m!"MAIN LOOP, after step 1: {goal.mvarId}"

    -- STEP 2: ksimp
    let simpMethods ← mkSimpMethods
    let (keepGoingSimp, goal) ← applyKSimp simpMethods goal
    if (← getOptions).get `debug (defVal := false) then
      goal.withContext do
        let t ← goal.mvarId.getType
        logInfo m!"MAIN LOOP, after step 2: {t}"

    if let some goal' ← stepAt? maxInstrCount goal then
      return .continue goal'

    -- STEP 3: kmem lemmas
    match ← applyKMem simpMethods goal with
    | .done goal => pure (.done (goal, []))
    | .subgoals goal subGoals => pure (.done (goal, subGoals))
    | .progress goal =>
      logInfo m!"kstep: keepGoing = {keepGoingSimp}"
      pure (.continue goal)
    | .noMatch goal =>
      logInfo m!"kstep: keepGoing = {keepGoingSimp}"
      if keepGoingSimp then
        pure (.continue goal)
      else
        pure (.done (goal, []))
  match next with
  | .continue goal' => kstepLoop config maxInstrCount goal'
  | .done res => pure res

def evalSymKStepCore (config : KStepConfig) (maxSteps? : Option Nat) : Grind.GrindTacticM Unit :=
  withTraceNode `Kraken.kstep (fun _ => return m!"kstep") do
    -- A `sym` tactic operates over a pair of the grind state and an MVarId. To avoid scope mistakes,
    -- we only ever use `goal` and never let-bind mvarId.
    let goal : Grind.Goal ← Grind.getMainGoal
    /- NOTE: Why is `maxInstrCount` a `IO.Ref`? -/
    let maxInstrCount ← maxSteps?.mapM (IO.mkRef ·)

    let (goal, subGoals) ← kstepLoop config maxInstrCount goal

    logInfo m!"END KSTEP: {subGoals.length} sub-goals left"

    if let .some r := maxInstrCount then
      let remaining ← r.get
      if remaining > 0 then
        throwError m!"kstep could not step through the remaining {remaining} steps"

    Grind.setGoals (subGoals ++ [ goal ])

private def parseKStepArgs (stx : Syntax) : TermElabM (KStepConfig × Option Nat) := do
  let config ← elabKStepConfig stx[1]
  let maxSteps? := if stx[2].isNone then none else some stx[2][0].toNat
  return (config, maxSteps?)

@[grind_tactic symKStep]
partial def evalSymKStep : Grind.GrindTactic :=
  fun stx : Syntax => do
  let (config, maxSteps?) ← parseKStepArgs stx
  evalSymKStepCore config maxSteps?

@[tactic tacKStep]
partial def evalTacKStep : Tactic :=
  fun stx : Syntax => withMainContext do
  let (config, maxSteps?) ← parseKStepArgs stx
  let (_, st) ← (evalSymKStepCore config maxSteps?).runAtGoal (← getMainGoal) (← Grind.mkDefaultParams {}) (sym := true)
  replaceMainGoal (st.goals.map (·.mvarId))

syntax (name := symKStepKStep) "kstep_kstep" : grind
syntax (name := symKStepKSimp) "kstep_ksimp" : grind
syntax (name := symKStepStepAt) "kstep_step_at" : grind
syntax (name := symKStepKMem) "kstep_kmem" : grind

@[grind_tactic symKStepKStep]
def evalSymKStepKStep : Grind.GrindTactic := fun _ => do
  let goal ← Grind.getMainGoal
  let goal ← applyKStepDSimp goal
  Grind.replaceMainGoal [goal]

@[grind_tactic symKStepKSimp]
def evalSymKStepKSimp : Grind.GrindTactic := fun _ => do
  let goal ← Grind.getMainGoal
  let simpMethods ← mkSimpMethods
  let (_, goal) ← applyKSimp simpMethods goal
  Grind.replaceMainGoal [goal]

@[grind_tactic symKStepStepAt]
def evalSymKStepStepAt : Grind.GrindTactic := fun _ => do
  let goal ← Grind.getMainGoal
  let some goal ← stepAt? none goal | throwError "kstep_step_at: could not apply `step_at`"
  Grind.replaceMainGoal [goal]

@[grind_tactic symKStepKMem]
def evalSymKStepKMem : Grind.GrindTactic := fun _ => do
  let goal ← Grind.getMainGoal
  let simpMethods ← mkSimpMethods
  match ← applyKMem simpMethods goal with
  | .done goal | .noMatch goal | .progress goal => Grind.replaceMainGoal [goal]
  | .subgoals goal subGoals => Grind.replaceMainGoal (subGoals ++ [goal])

syntax (name := symRotateRight) "rotate_right" (ppSpace num)? : grind

@[grind_tactic symRotateRight]
def evalSymRotateRight : Grind.GrindTactic := fun stx => do
  let n := if stx[1].isNone then 1 else stx[1][0].toNat
  let goals ← Grind.getGoals
  Grind.setGoals (goals.rotateRight n)
