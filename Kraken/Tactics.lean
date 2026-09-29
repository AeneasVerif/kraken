module

/-
Common Kraken Proof Tactics.

Core tactics and theorems for stepping through Kraken assembly proofs.
-/

public import Kraken.Attribute
import Kraken.Layout
import Kraken.OmniSemantics
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
         delta $p)))

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
    let lctx₀ ← getLCtx
    let localInsts₀ ← getLocalInstances
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
      if let some inner := target.app1? ``gimmickId then
        let rec rwUnderLets (e : Expr) (fvars : Array Expr) (letInfo : Array (Name × Expr × Expr × Bool)) :
            MetaM (Expr × Expr × List MVarId) := do
          match e with
          | .letE n t v b nondep =>
            let tInst := t.instantiateRev fvars
            let vInst := v.instantiateRev fvars
            withLetDecl n tInst vInst (nondep := false) fun x =>
              rwUnderLets b (fvars.push x) (letInfo.push (n, t, v, nondep))
          | _ =>
            let eInst := e.instantiateRev fvars
            let tmpMVar ← mkFreshExprMVar eInst
            let r ← tmpMVar.mvarId!.rewrite eInst heq symm
            let mctx ← getMCtx
            let mut outerMVarIds : List MVarId := []
            for mvarId in r.mvarIds do
              if !(← mvarId.isAssigned) then
                let mDecl := mctx.getDecl mvarId
                if mDecl.index >= mvarCounterSaved then
                  let mut mType := (← instantiateMVars mDecl.type).abstract fvars
                  if mType.hasLooseBVars then
                    for (n, t, v, _) in letInfo.reverse do
                      mType := .letE n t v mType false
                  let outerMVar ← mkFreshExprMVarAt lctx₀ localInsts₀ mType mDecl.kind mDecl.userName
                  mvarId.assign outerMVar
                  outerMVarIds := outerMVarIds ++ [outerMVar.mvarId!]
            let mut eNew := (← instantiateMVars r.eNew).abstract fvars
            let mut eqPrf := (← instantiateMVars r.eqProof).abstract fvars
            for (n, t, v, nondep) in letInfo.reverse do
              eNew := .letE n t v eNew nondep
              eqPrf := .letE n t v eqPrf false
            let propSort := mkSort Level.zero
            let eqProofGimmick := mkApp6 (mkConst ``congrArg [Level.one, Level.one])
              propSort propSort inner eNew (mkConst ``gimmickId) eqPrf
            return (mkApp (mkConst ``gimmickId) eNew, eqProofGimmick, outerMVarIds)
        rwUnderLets inner #[] #[]
      else
        let r ← goal.mvarId.rewrite target heq symm
        let mctx ← getMCtx
        let mvarIds := r.mvarIds.filter fun mvarId => (mctx.getDecl mvarId |>.index) >= mvarCounterSaved
        return (r.eNew, r.eqProof, mvarIds)
    let eNew ← Grind.liftSymM <| Sym.preprocessExpr eNewRaw
    let mvarId ← goal.mvarId.replaceTargetEq eNew eqProof
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

-- Workaround for upstream bug in `Lean.Meta.Sym.Simp.toHave` (Have.lean:258 in nightly-2026-09-21),
-- which calls `args[i].betaRev ys` instead of `args[i].betaRev ys.reverse`, reversing the
-- dependencies of any `have` binding that depends on two or more earlier `have` bindings.
namespace KSimpHave
open Lean.Meta.Sym
open Lean.Meta.Sym.Simp
open Lean.Meta.Sym.Internal

private def consumeForallN (type : Expr) (n : Nat) : Expr :=
  match n with
  | 0 => type
  | n+1 => consumeForallN type.bindingBody! n

private def elimAuxApps (e : Expr) (xs : Array Expr) (varDeps : Array (Array Nat)) : SymM Expr := do
  let n := xs.size
  replaceS e fun e offset => do
    if offset >= e.looseBVarRange then
      return some e
    match e.getAppFn with
    | .bvar idx =>
      if _h : idx >= offset then
        if _h : idx < offset + n then
          let i := n - (idx - offset) - 1
          let expectedNumArgs := varDeps[i]!.size
          let numArgs := e.getAppNumArgs
          if numArgs > expectedNumArgs then
            return none
          else
            return xs[i]
        else
          mkBVarS (idx - n)
      else
        return some e
    | _ => return none

private def toHave (e : Expr) (varDeps : Array (Array Nat)) : SymM Expr :=
  e.withApp fun f args => do
  if _h : args.size ≠ varDeps.size then unreachable! else
  let rec go (f : Expr) (xs : Array Expr) (i : Nat) : SymM Expr := do
    if _h : i < args.size then
      let .lam n t b _ := f | unreachable!
      let varPos := varDeps[i]
      let ys := varPos.map fun i => xs[i]!
      let type := consumeForallN t varPos.size
      let val ← share <| args[i].betaRev ys.reverse
      withLetDecl (nondep := true) n type val fun x => do
      go b (xs.push (← share x)) (i+1)
    else
      let f ← elimAuxApps f xs varDeps
      let result ← mkLetFVars (generalizeNondepLet := false) (usedLetOnly := false) xs f
      share result
  go f #[] 0

private def getUnivs (fType : Expr) : SymM (Array Level × Array Level) := do
  let rec go (type : Expr) (argUnivs : Array Level) : SymM (Array Level × Array Level) := do
    match type with
    | .forallE _ d b _ =>
      go b (argUnivs.push (← Sym.getLevel d))
    | _ =>
      let mut v ← Sym.getLevel type
      let mut i := argUnivs.size
      let mut fnUnivs := #[]
      while i > 0 do
        i := i - 1
        let u := argUnivs[i]!
        v := mkLevelIMax' u v |>.normalize
        fnUnivs := fnUnivs.push v
      fnUnivs := fnUnivs.reverse
      return (argUnivs, fnUnivs)
  go fType #[]

private def simpBetaApp (e : Expr) (fType : Expr) (fnUnivs argUnivs : Array Level)
    (simpBody : Sym.Simp.Simproc) : Sym.Simp.SimpM Sym.Simp.Result := do
  let numArgs := argUnivs.size
  let mkCongrPrefix (declName : Name) (fType : Expr) (i : Nat) : SymM Expr := do
    let α := fType.bindingDomain!
    let β := fType.bindingBody!
    let u := argUnivs[i]!
    let v := fnUnivs[i]!
    return mkApp2 (mkConst declName [u, v]) α β
  let rec go (e : Expr) (i : Nat) : Sym.Simp.SimpM (Sym.Simp.Result × Expr) := do
    match e with
    | .app f a =>
      let (rf, fType) ← go f (i-1)
      let r ← match rf, (← Sym.Simp.simp a) with
        | .rfl _ cd₁, .rfl _ cd₂ =>
          pure (mkRflResultCD (cd₁ || cd₂))
        | .step f' hf _ cd₁, .rfl _ cd₂ =>
          let e' ← mkAppS f' a
          let h := mkApp4 (← mkCongrPrefix ``congrFun' fType i) f f' hf a
          pure <| .step e' h (contextDependent := cd₁ || cd₂)
        | .rfl _ cd₁, .step a' ha _ cd₂ =>
          let e' ← mkAppS f a'
          let h := mkApp4 (← mkCongrPrefix ``congrArg fType i) a a' f ha
          pure <| .step e' h (contextDependent := cd₁ || cd₂)
        | .step f' hf _ cd₁, .step a' ha _ cd₂ =>
          let e' ← mkAppS f' a'
          let h := mkApp6 (← mkCongrPrefix ``congr fType i) f f' a a' hf ha
          pure <| .step e' h (contextDependent := cd₁ || cd₂)
      return (r, fType.bindingBody!)
    | .lam .. => return (← simpBody e, fType)
    | _ => unreachable!
  return (← go e (numArgs - 1)).1

public def ksimpLet : Sym.Simp.Simproc := fun e₁ => do
  let .letE _ _ _ _ true := e₁ | return .rfl
  let r ← toBetaApp e₁
  let e₂ := r.e
  let (argUnivs, fnUnivs) ← getUnivs r.fType
  let res : Sym.Simp.Result ← match (← simpBetaApp e₂ r.fType fnUnivs argUnivs simpLambda) with
    | .rfl _ cd =>
      let e₂' ← zetaUnused e₁
      if isSameExpr e₁ e₂' then
        pure (mkRflResultCD cd)
      else
        let h := mkApp2 (mkConst ``Eq.refl [r.u]) r.α e₂'
        pure (.step e₂' h (contextDependent := cd))
    | .step e₃ h _ cd =>
      let h₁ := mkApp6 (mkConst ``Eq.trans [r.u]) r.α e₁ e₂ e₃ r.h h
      let e₄ ← toHave e₃ r.varDeps
      let eq := mkApp3 (mkConst ``Eq [r.u]) r.α e₃ e₄
      let h₂ := mkExpectedPropHint (mkApp2 (mkConst ``Eq.refl [r.u]) r.α e₃) eq
      let h := mkApp6 (mkConst ``Eq.trans [r.u]) r.α e₁ e₃ e₄ h₁ h₂
      let e₅ ← zetaUnused e₄
      if isSameExpr e₄ e₅ then
        pure (.step e₄ h (contextDependent := cd))
      else
        let h := mkApp6 (mkConst ``Eq.trans [r.u]) r.α e₁ e₄ e₅ h
          (mkApp2 (mkConst ``Eq.refl [r.u]) r.α e₅)
        pure (.step e₅ h (contextDependent := cd))
  return res.markAsDone

end KSimpHave

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

  let env ← getEnv

  let declsForDSimp := (kstepExtension.getState env).toList
  let kdsimpDecls := kdeltaBetaOnly declsForDSimp

  -- https://lean-lang.org/doc/api/Lean/Meta/Sym/Simp/SimpM.html
  -- note the "contextual ite handling" --> are we doing this?
  let simpTheorems ← goal.withContext do
    let mut simpTheorems ← ksimpExt.getTheorems
    for decl in [``Bool.false_eq_true, ``eq_self, ``_root_.ite_true, ``_root_.ite_false] do
      simpTheorems := simpTheorems.insert (← Sym.Simp.mkTheoremFromDecl decl)
    for ldecl in ← getLCtx do
      if !ldecl.isImplementationDetail then
        try
          simpTheorems := simpTheorems.insert (← Sym.Simp.mkTheoremFromExpr ldecl.toExpr)
        catch _ =>
          pure ()
    pure simpTheorems
  let simpMethods: Sym.Simp.Methods := {
    pre := KSimpHave.ksimpLet,
    post := Sym.Simp.evalGround >> simpTheorems.rewrite
  }

  let specLemmas := (kspecExtension.getState env).toList
  let specTree: DiscrTree Name ← specLemmas.foldlM (fun specTree name => do
    -- NOTE: hardcoding left-to-right order, for now
    let (pat, _) ← mkEqPatternFromDecl name
    pure (insertPattern specTree pat name)
  ) {}

  let zetaFVars (e : Expr) : MetaM Expr :=
    Meta.transform e (usedLetOnly := true) (pre := fun sub => do
      let .fvar fvarId := sub.getAppFn | return .continue
      let some decl ← fvarId.findDecl? | return .continue
      let some val := decl.value? (allowNondep := true) | return .continue
      return .visit <| (← instantiateMVars val).beta sub.getAppArgs)

  let kdsimpIteCond : DSimproc := fun e => do
    let_expr f@ite α c inst a b := e | return .rfl
    let c' ← zetaFVars c
    if c' == c then return .rfl
    let inst' ← zetaFVars inst
    return .step (← shareCommon (mkApp5 f α c' inst' a b))

  let rec liftLetsUnderForall (e : Expr) : SymM Expr := do
    let e ← Sym.liftLets e
    let rec go (e : Expr) (fvars : Array Expr) : SymM Expr := do
      match e with
      | .letE n t v b nondep =>
        let tInst ← Sym.instantiateRevBetaS t fvars
        let vInst ← Sym.instantiateRevBetaS v fvars
        withLetDecl n tInst vInst (nondep := nondep) fun x =>
          go b (fvars.push x)
      | .forallE n d b bi =>
        let dInst ← Sym.instantiateRevBetaS d fvars
        withLocalDecl n bi dInst fun x => do
          let bInst ← Sym.instantiateRevBetaS b (fvars.push x)
          let bLifted ← liftLetsUnderForall bInst
          let res ← mkForallFVars #[x] bLifted
          let res ← mkLetFVars (generalizeNondepLet := false) (usedLetOnly := false) fvars res
          Sym.shareCommon res
      | _ =>
        if fvars.isEmpty then
          return e
        else
          let eInst ← Sym.instantiateRevBetaS e fvars
          let res ← mkLetFVars (generalizeNondepLet := false) (usedLetOnly := false) fvars eInst
          Sym.shareCommon res
    if e.isLet || e.isForall then
      go e #[]
    else
      return e

  -- MAIN LOOP
  let rec go (goal: Grind.Goal): Grind.GrindTacticM (Grind.Goal × List Grind.Goal) := do
    -- STEP 1: dsimp
    let goal ← do
      let target ← Grind.liftGrindM $
        Sym.dsimp
          (config := { maxSteps := 1000000, instances := true })
          (methods := {
            pre := klog >> evalGround >> kdsimpDecls >> kdsimpMatch >> kdsimpProj >> kbeta,
            post := evalGround >> kdsimpMatch >> kdsimpProj >> kdsimpIteCond >> kbeta })
          (← goal.mvarId.getType)
      let_expr gimmickId inner := target | throwError "missing gimmick"
      let target ← Grind.liftSymM <| do
        let inner ← liftLetsUnderForall inner
        let inner ← Sym.letToHave inner
        Sym.Internal.mkAppS target.appFn! inner
      let mvarId ← goal.mvarId.replaceTargetDefEq target
      pure { goal with mvarId }

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
      let goalT ← goal.mvarId.getType
      let_expr gimmickId goalT' := goalT | throwError "missing gimmick"
      let goalT' ← instantiateMVars goalT'
      let rec getEffectsState (e : Expr) : Option Expr :=
        match e with
        | .letE _ _ _ body _ => getEffectsState body
        | .forallE _ _ body _ => getEffectsState body
        | .mdata _ e => getEffectsState e
        | _ =>
          if e.isApp && e.getAppFn.isConstOf `Effects.All && e.getAppArgs.size == 2 then
            some e.getAppArgs[1]!
          else
            none
      -- No more Effects.All in the goal -- return to the user (we might be done,
      -- or realistically, we might need to debug).
      let some state := getEffectsState goalT' | return (goal, [])
      pure state

    let (keepGoingSpec, goal) ←
      match Sym.getMatch (← getMCtx) specTree goalState with
      | #[ thmName ] =>
        logInfo m!"Found a spec lemma: {thmName}"
        let (goal, subGoals) ← rwTarget goal false (mkConst thmName)
        logInfo m!"{subGoals.length} subgoals generated"

        let kzeta : DSimproc := fun e => do
          match e with
          | .letE _ _ v b _ => return .step (b.instantiate1 v)
          | _ => return .rfl

        let subGoals ← subGoals.mapM fun (subGoal: Grind.Goal) => do
          -- Try simp -- who knows, one might get lucky
          let mut subGoal := subGoal
          for _ in [:3] do
            let mvarId ← subGoal.mvarId.replaceTargetDefEq (← Grind.liftGrindM $
              Sym.dsimp
                (config := { maxSteps := 1000000 })
                (methods := {
                  pre := evalGround >> kdsimpDecls >> kdsimpMatch >> kdsimpProj >> kbeta >> kzeta,
                  post := evalGround >> kdsimpMatch >> kdsimpProj >> kbeta })
                (← subGoal.mvarId.getType))
            subGoal := { subGoal with mvarId }
            let simpResult ← Grind.liftGrindM (Sym.simpGoal subGoal.mvarId simpMethods)
            match simpResult with
            | .noProgress => break
            | .goal mvarId => subGoal := { subGoal with mvarId }
            | .closed => break
          pure subGoal

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
      go goal
    else
      pure (goal, [])

  let skipEventuallyDSimp : DSimproc := fun e => do
    if e.isAppOf ``Eventually then return .rfl (done := true) else return .rfl

  let skipEventuallySimp : Sym.Simp.Simproc := fun e => do
    if e.isAppOf ``Eventually then return .rfl (done := true) else return .rfl

  let tryQuiet {α} (act : Grind.GrindTacticM α) : Grind.GrindTacticM (Option α) := do
    let savedMsgs ← Core.getMessageLog
    try
      let res ← act
      if (← Core.getMessageLog).hasErrors then
        Core.setMessageLog savedMsgs
        return none
      return some res
    catch _ =>
      Core.setMessageLog savedMsgs
      return none

  let adHocSimp (decls : List Name) (goal : Grind.Goal) : Grind.GrindTacticM Grind.Goal :=
    goal.withContext do
      let mut initTheorems : Sym.Simp.Theorems := {}
      for decl in decls do
        initTheorems := initTheorems.insert (← Sym.Simp.mkTheoremFromDecl decl)
      let lctx ← getLCtx
      for ldecl in lctx do
        if !ldecl.isImplementationDetail then
          try
            initTheorems := initTheorems.insert (← Sym.Simp.mkTheoremFromExpr ldecl.toExpr)
          catch _ =>
            pure ()
          if ldecl.type.isAppOfArity ``Layout.Valid 2 then
            let layoutExpr := ldecl.type.getAppArgs[0]!
            let progExpr := ldecl.type.getAppArgs[1]!
            let prog' ← match progExpr.constName? with
              | some _ => pure ((← unfoldDefinition? progExpr true).getD progExpr)
              | none => pure progExpr
            let extraThms : Array Sym.Simp.Theorem ← (do
              let mut acc : Array Sym.Simp.Theorem := #[]
              let hlayoutType ← mkAppM ``Layout.Valid #[layoutExpr, prog']
              let hlayout' ← mkExpectedTypeHint ldecl.toExpr hlayoutType
              let thmStart ← mkAppM ``Executable.directivesAtStart #[prog', hlayout']
              acc := acc.push (← Sym.Simp.mkTheoremFromExpr thmStart)
              for ldecl_wf in lctx do
                if !ldecl_wf.isImplementationDetail && ldecl_wf.type.isAppOfArity ``Kraken.Executable.WellFormed 2 then
                  let wfApp ← mkAppM ``Kraken.Layout.apply #[layoutExpr, prog']
                  let hwfType ← mkAppM ``Kraken.Executable.WellFormed #[wfApp]
                  let hwf' ← mkExpectedTypeHint ldecl_wf.toExpr hwfType
                  let mut addrExpr ← mkAppOptM ``Kraken.Layout.start #[some (mkConst ``Directive), some layoutExpr]
                  for n in [1:8] do
                    let szExpr ← mkAppOptM ``Kraken.Layout.size #[some (mkConst ``Directive), some layoutExpr, some (mkNatLit (n - 1))]
                    let ofNatExpr ← mkAppM ``Int64.ofNat #[szExpr]
                    addrExpr ← mkAppM ``HAdd.hAdd #[addrExpr, ofNatExpr]
                    let validApp ← mkAppM ``validSplitIndex #[prog', mkNatLit n]
                    if ← isDefEq validApp (mkConst ``true) then
                      let haddr ← mkEqRefl addrExpr
                      let hvalid ← mkExpectedTypeHint (← mkEqRefl (mkConst ``true)) (← mkEq validApp (mkConst ``true))
                      let eAt ← mkAppOptM ``Executable.directivesAtAddress_add #[some layoutExpr, some prog', some hwf', some hlayout', some (mkNatLit n), some addrExpr, some haddr, some hvalid]
                      acc := acc.push (← Sym.Simp.mkTheoremFromExpr eAt)
                      let eFrom ← mkAppOptM ``Executable.directivesFromAddress_add #[some layoutExpr, some prog', some hwf', some hlayout', some (mkNatLit n), some addrExpr, some haddr, some hvalid]
                      acc := acc.push (← Sym.Simp.mkTheoremFromExpr eFrom)
              pure acc
            ) <|> pure #[]
            for t in extraThms do
              initTheorems := initTheorems.insert t
      let initSimpMethods : Sym.Simp.Methods := {
        pre := skipEventuallySimp,
        post := Sym.Simp.evalGround >> initTheorems.rewrite
      }
      let mut goal := goal
      for _ in [:20] do
        let simpRes ← Grind.liftGrindM <| Sym.simpGoal goal.mvarId initSimpMethods
        match simpRes with
        | .goal mvarId =>
          let mvarId ← mvarId.replaceTargetDefEq (← Grind.liftGrindM $
            Sym.dsimp (methods := {
              pre := skipEventuallyDSimp >> evalGround >> kdsimpProj >> kbeta,
              post := evalGround >> kdsimpProj >> kbeta }) (← mvarId.getType))
          goal := { goal with mvarId }
        | .noProgress => break
        | _ => throwError "unexpected"
      pure goal

  unless (← goal.mvarId.getType).consumeMData.isAppOf ``Eventually do
    throwError "kstep: expected goal to be of the form Eventually"

  match maxSteps? with
  | .some maxSteps =>
      let mut goal := goal
      let mut allSubGoals : List Grind.Goal := []
      for _ in [:maxSteps] do
        unless (← goal.mvarId.getType).consumeMData.isAppOf ``Eventually do
          throwError "kstep: expected goal to be of the form Eventually"
        goal ← goal.withContext do
          let [mvarId] ← goal.mvarId.apply (← mkConstWithFreshMVarLevels ``eventually_step_cps) | failure
          let target' ← Grind.liftSymM <| Sym.preprocessExpr (← mvarId.getType)
          let mvarId ← mvarId.replaceTargetDefEq target'
          let goal := { goal with mvarId }

          let mvarId ← goal.mvarId.replaceTargetDefEq (← Grind.liftGrindM $
            Sym.dsimp
              (methods := {
                pre := skipEventuallyDSimp >> kdeltaBetaOnly [`step1, `Executable.step] >> kdsimpProj >> kbeta })
              (← goal.mvarId.getType))
          let goal := { goal with mvarId }

          adHocSimp [
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
          ] goal

        let g1 ← insertGimmick goal
        let (g2, subGoals) ← go g1
        goal ← removeGimmick g2
        allSubGoals := allSubGoals ++ subGoals

      logInfo m!"END KSTEP: {allSubGoals.length} sub-goals left"
      Grind.setGoals (allSubGoals ++ [ goal ])
  | .none =>
      let goal ← goal.withContext do
        -- apply eventually_straightlineStep_cps
        let [subGoal, mvarId] ← goal.mvarId.apply (← mkConstWithFreshMVarLevels ``eventually_straightlineStep_cps) | failure
        -- subgoal for well-formedness: an assumption
        subGoal.withContext subGoal.assumption
        let target' ← Grind.liftSymM <| Sym.preprocessExpr (← mvarId.getType)
        let mvarId ← mvarId.replaceTargetDefEq target'
        let goal := { goal with mvarId }

        -- Administrative steps:
        --  dsimp [straightlineStep,Executable.straightline]
        --  rw [Kraken.Executable.directivesFromStart]
        --  simp [List.mapIdx, List.mapIdx.go]
        let mvarId ← goal.mvarId.replaceTargetDefEq (← Grind.liftGrindM $
          Sym.dsimp
            (methods := {
              pre := kdeltaBetaOnly [`straightlineStep, `Executable.straightline] >> kdsimpProj >> kbeta })
            (← goal.mvarId.getType))
        let goal := { goal with mvarId }

        adHocSimp [``Kraken.Executable.directivesFromStart, ``List.mapIdx_nil, ``List.mapIdx_cons, ``List.drop_zero, ``List.drop_succ_cons] goal

      -- Apply the debug gimmick. We actually *do* expect the goal to be in this form (see comment in
      -- kdeltaBetaOnly).
      let goal ← insertGimmick goal

      let (goal, subGoals) ← go goal

      -- Remove the gimmick debug marker.
      let goal ← removeGimmick goal

      logInfo m!"END KSTEP: {subGoals.length} sub-goals left"

      Grind.setGoals (subGoals ++ [ goal ])

--   if let .some r := maxInstrCount then
--     let remaining ← r.get
--     if remaining > 0 then
--       throwError m!"kstep could not step through the remaining {remaining} steps"


syntax (name := symRotateRight) "rotate_right" (ppSpace num)? : grind

@[grind_tactic symRotateRight]
def evalSymRotateRight : Grind.GrindTactic := fun stx => do
  let n := if stx[1].isNone then 1 else stx[1][0].toNat
  let goals ← Grind.getGoals
  Grind.setGoals (goals.rotateRight n)
