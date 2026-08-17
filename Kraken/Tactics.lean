/-
Common Kraken Proof Tactics.

Core tactics and theorems for stepping through Kraken assembly proofs.
-/

import Kraken.Attribute
import Kraken.Layout
import Lean
import Std

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

      let straightlineStepId := mkIdent `straightlineStep
      let execStraightlineId := mkIdent `Executable.straightline

      evalTactic (← `(tactic|
        (let ss := $s
         change ($straightlineStepId:ident _ (ss, _) _)
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

/-- Is `e` an application headed by a constructor of the (ISA-local, root-level)
`Effects` inductive? -/
def isEffectsCtorHead (e : Expr) : MetaM Bool := do
  let some n := e.getAppFn'.constName? | return false
  match (← getEnv).find? n with
  | some (.ctorInfo ci) => return ci.induct == `Effects
  | _ => return false

/-- Advance the effects tree sitting under `Effects.All` by one defeq step.

The tree is a left-nested `Effects.bind` spine (or a bare `Directives.interp`
application), and the reduction site is its leftmost operand: a
`Directives.interp` there gets force-unfolded in place, which is the event
the step budget counts, one directive consumed from the list. A
constructor-headed operand lets the `bind` matcher itself reduce by plain
definitional unfolding; the constructor commutes with `bind` one node at a
time. Neither `Directives.interp` nor `Effects.bind` may be `@[kstep]`-tagged:
the dsimp traversal is pre-order, so unfolding them head-first would produce
matchers stuck on unreduced scrutinees.

`stuck` means nothing here can advance (a `@[kspec]` hand-off such as
`MachineData.load`/`store`, or a symbolic branch). `budgetExhausted` means
the next advance would consume a directive the step budget does not allow;
the caller must block further reduction of this node rather than fall
through to generic unfolding, which would step through directives behind the
counter's back. -/
inductive AdvanceResult where
  | stepped (tree : Expr)
  | budgetExhausted
  | stuck

partial def advanceEffectsTree (maxInstrCount : Option (IO.Ref Nat)) (t : Expr) :
    DSimpM AdvanceResult := do
  if t.isApp && t.getAppFn'.isConstOf ``Bind.bind && t.getAppArgs.size ≥ 6 then
    -- `do`-notation elaborates to the `Bind.bind` method; when the instance is
    -- the canonical `Effects` monad this is definitionally the structural
    -- `Effects.bind`, and rebuilding it in that form gives the spine walk
    -- below one head to work with. The equality is verified before stepping:
    -- for any other instance the rebuild is not defeq, and the node is left
    -- alone. Argument layout of `@Bind.bind`: [monad, inst, α, β, x, f].
    let bargs := t.getAppArgs
    let t' := mkApp4 (mkConst `Effects.bind)
      bargs[bargs.size - 4]! bargs[bargs.size - 3]! bargs[bargs.size - 2]! bargs[bargs.size - 1]!
    if ← (try withNewMCtxDepth (Meta.withTransparency .default (Meta.isDefEq t' t)) catch _ => pure false) then
      return .stepped t'
    else
      return .stuck
  else if t.isApp && t.getAppFn'.isConstOf ``Pure.pure && t.getAppArgs.size ≥ 4 then
    -- Likewise `pure` is the `Pure.pure` method over `Effects.done`, with the
    -- same canonical-instance check. Argument layout of `@Pure.pure`:
    -- [monad, inst, α, a].
    let bargs := t.getAppArgs
    let t' := mkApp2 (mkConst `Effects.done)
      bargs[bargs.size - 2]! bargs[bargs.size - 1]!
    if ← (try withNewMCtxDepth (Meta.withTransparency .default (Meta.isDefEq t' t)) catch _ => pure false) then
      return .stepped t'
    else
      return .stuck
  else if t.isApp && t.getAppFn'.isConstOf `Directives.interp then
    -- We optionally track how many times we've hit Directives.interp -- this tracks how
    -- many instructions we've stepped through.
    if (← maxInstrCount.mapM (·.get)) = .some 0 then
      return .budgetExhausted
    let some t' ← Meta.unfoldDefinition? t true | throwError "can't unfold Directives.interp"
    maxInstrCount.forM (fun r => r.modify (· - 1))
    trace[Kraken.kstep] "consumed a directive at {t}"
    return .stepped t'
  else if t.isApp && t.getAppFn'.isConstOf `Effects.bind then
    let bargs := t.getAppArgs
    if bargs.size < 2 then
      return .stuck
    else
      let m := bargs[bargs.size - 2]!.consumeMData
      if m.isLet then
        -- Float the let through the bind (a defeq step):
        -- `bind (let x := v; T) k ≡ let x := v; bind T k`. Everything here is
        -- locally closed except the let body's own binder, so no lifting is
        -- needed to move `k` under it. The arg-peeling machinery at the
        -- enclosing `Effects.All` node then hoists it into the context, where
        -- reduction can continue around it.
        let .letE n ty val body nondep := m | return .stuck
        return .stepped (.letE n ty val
          (mkAppN t.getAppFn' ((bargs.set! (bargs.size - 2) body))) nondep)
      else if ← isEffectsCtorHead m then
        -- `m` is a constructor application: delta `bind` here so the matcher
        -- can consume it on the next pass.
        let some t' ← Meta.unfoldDefinition? t true | return .stuck
        return .stepped t'
      else
        match ← advanceEffectsTree maxInstrCount m with
        | .stepped m' => return .stepped (mkAppN t.getAppFn' (bargs.set! (bargs.size - 2) m'))
        | r => return r
  else
    return .stuck

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

    -- The generic path: force one step of delta-beta on a `@[kstep]`-tagged
    -- application. (Also the fallback when the effects tree cannot advance:
    -- this keeps reducing and stepping until we have no steps left to apply
    -- and YET the goal has landed us back on something that is neither
    -- `Effects.All ... (Directives.interp ...)` nor
    -- `Effects.All ... (require_exec_access ...)`.)
    let generic : DSimpM Result := do
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

    -- The effects tree is `Effects.All`'s last argument; indexing from the
    -- end keeps this independent of the number of leading implicit
    -- arguments.
    let treeIdx := args.size - 1
    if f.isConstOf `Effects.All && args.size ≥ 2 && args[treeIdx]!.isApp then
      match ← advanceEffectsTree maxInstrCount args[treeIdx]! with
      | .stepped tree' =>
        let e := mkAppN f (args.set! treeIdx tree')
        let e' ← shareCommon e
        let e'' ← mkLetFVars fvars e'
        return .step e''
        -- TODO: we could here have a post := in the simproc that forces the
        -- result to be .step ... (done := true) to prevent the next unrolling of
        -- Directives.interp from being applied. This would essentially allow
        -- implementing a kstep1 tactic (and leave it to done := false to keep
        -- stepping until something blocks).
      | .budgetExhausted =>
        -- Out of steps: freeze this node. Falling through to the generic
        -- branch would let smart unfolding of `Effects.All` keep executing
        -- directives without counting them.
        return .rfl
      | .stuck => generic
    else
      generic

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

  -- Apply the debug gimmick. We actually *do* expect the goal to be in this form (see comment in
  -- kdeltaBetaOnly).
  let goal ← insertGimmick goal

  let env ← getEnv

  let declsForDSimp := (kstepExtension.getState env).toList
  let maxInstrCount ← maxSteps?.mapM (IO.mkRef ·)
  let kdsimpDecls := kdeltaBetaOnly declsForDSimp maxInstrCount

  -- https://lean-lang.org/doc/api/Lean/Meta/Sym/Simp/SimpM.html
  -- note the "contextual ite handling" --> are we doing this?
  let simpTheorems ← ksimpExt.getTheorems
  let simpMethods: Sym.Simp.Methods := { post := Sym.Simp.evalGround >> simpTheorems.rewrite }

  let specLemmas := (kspecExtension.getState env).toList
  let specTree: DiscrTree Name ← specLemmas.foldlM (fun specTree name => do
    -- NOTE: hardcoding left-to-right order, for now
    -- Key each lemma on the effectful operation itself: for a bind-context
    -- equation `(op …).bind k = …` that is the bind's first operand. Keying
    -- on the whole bind node would drag `Effects.bind`'s type argument into
    -- the key; for a load that is the dependent `w.type × MachineData`, which
    -- never matches the goal's already-reduced form.
    let (pat, _) ← Sym.mkPatternFromDeclWithKey name (selectKey := fun type => do
      let_expr Eq _ lhs _ := type | throwError "kspec lemma {name} is not an equation"
      let lhs := lhs.consumeMData
      if lhs.isApp && lhs.getAppFn.isConstOf `Effects.bind && lhs.getAppArgs.size ≥ 2 then
        pure (lhs.getAppArgs[lhs.getAppArgs.size - 2]!, ())
      else
        pure (lhs, ()))
    pure (insertPattern specTree pat name)
  ) {}

  -- TODO: remove once we have lift_lets
  let introsIf (goal: Grind.Goal): Grind.GrindTacticM Grind.Goal := do
    let goal ← removeGimmick goal
    let goal ← match ← Grind.liftGrindM (goal.intros #[]) with
      | Grind.IntrosResult.failed => pure goal
      | .goal _ goal => pure goal
    pure (← insertGimmick goal)

  -- MAIN LOOP
  let rec go (goal: Grind.Goal): Grind.GrindTacticM (Grind.Goal × List Grind.Goal) := do
    -- STEP 1: dsimp
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

    -- TEMPORARY: trying to simplify binders in the goal
    /- let goal ← Meta.letToHave goal -/
    /- let goal ← Grind.liftGrindM $ shareCommon goal -/
    /- let mvarId ← mvarId.replaceTargetDefEq goal -/

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
      let goalT ← goal.mvarId.getType
      let_expr gimmickId goalT' := goalT | throwError "missing gimmick"
      let goalT' ← instantiateMVars goalT'
      let rec getEffectsState (e : Expr) : Option Expr :=
        match e with
        | .letE _ _ _ body _ => getEffectsState body
        | .mdata _ e => getEffectsState e
        | _ =>
          -- The effects tree is `Effects.All`'s last argument; indexing
          -- from the end keeps this independent of the leading implicits.
          if e.isApp && e.getAppFn.isConstOf `Effects.All && e.getAppArgs.size ≥ 2 then
            some e.getAppArgs.back!
          else
            none
      -- No more Effects.All in the goal -- return to the user (we might be done,
      -- or realistically, we might need to debug).
      let some state := getEffectsState goalT' | return (goal, [])
      -- Guard against shape drift: what we hand to the spec engine must be an
      -- `Effects` tree. (A partially applied `Effects.All` would satisfy the
      -- arity test above and silently hand a predicate to the DiscrTree.)
      let stateTy ← inferType state
      unless stateTy.getAppFn.isConstOf `Effects do
        throwError m!"kstep: found Effects.All but its last argument is not an effects tree:{indentExpr state}"
      pure state

    -- A spec lemma's subject may sit at the top of the tree or at the
    -- leftmost operand of an `Effects.bind` spine. Offer the tree and each
    -- spine operand to the DiscrTree, outermost first, and take the first
    -- hit.
    let rec specCandidates (t : Expr) (acc : Array Expr) : Array Expr :=
      let acc := acc.push t
      if t.isApp && t.getAppFn.isConstOf `Effects.bind && t.getAppArgs.size ≥ 2 then
        specCandidates t.getAppArgs[t.getAppArgs.size - 2]! acc
      else
        acc
    let specMatches := ((specCandidates goalState #[]).findSome? (fun c =>
      let ms := getMatch specTree c
      if ms.isEmpty then none else some ms)).getD #[]

    let (keepGoingSpec, goal) ←
      match specMatches with
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
