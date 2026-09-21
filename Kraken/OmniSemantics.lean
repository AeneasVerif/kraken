/-
Common Kraken Temporal Logic and OmniSemantics.
-/

import Lean

abbrev Post {State : Type} := State → Prop

-- NOTE: 'initial' cannot be moved to the left of the colon as a parameter
-- because it varies in the recursive call in the 'step' constructor (it becomes 'mid').
inductive Eventually {State : Type} (trans : State → Post → Prop) (post : Post) : Post
  | done (initial: State):
      post initial →
      Eventually trans post initial
  | step (initial: State):
      (mid_p: Post) →
      trans initial mid_p →
      (forall (mid: State), mid_p mid → Eventually trans post mid) →
      Eventually trans post initial

theorem step_cps {State : Type} (trans : State → Post → Prop) (post : Post) (initial : State) :
  trans initial (fun mid => Eventually trans post mid) → Eventually trans post initial :=
  by
    intro h
    exact .step initial _ h (fun _ => id)

theorem eventually_trans {State : Type} (trans : State → Post → Prop) (p q : Post) (initial : State)
  (e : Eventually trans p initial)
  (h : ∀ s, p s → Eventually trans q s) :
    Eventually trans q initial
  := by
    induction e with
    | done initial hp => exact h initial hp
    | step initial mid_p ht _ ih => exact .step initial mid_p ht ih

theorem eventually_weaken {State : Type} (trans : State → Post → Prop) (p q : Post) (initial : State)
  (h : ∀ s, p s → q s) :
    Eventually trans p initial → Eventually trans q initial
  := by
    exact fun hp => eventually_trans trans p q initial hp fun s hs => .done s (h s hs)



-- Tailrec-style loop rule
-- Adapted from: https://github.com/mit-plv/bedrock2/blob/8ec2c459bbf16d6cf2baa7d433ae211a243b1011/bedrock2/src/bedrock2/Loops.v#L48
-- This version moves the choice inside the Eventually postcondition.
theorem tailrec_loop {State Measure Ghost : Type}
  (trans : State → Post → Prop) (post : Post) (initial : State)
  (P Q : Measure → Ghost → Post)
  (lt : Measure → Measure → Prop)
  (Hwf : WellFounded lt)
  (v0 : Measure) (g0 : Ghost) :
  P v0 g0 initial →
  (∀ v g state, P v g state →
    Eventually trans (fun mid_s =>
      (Q v g mid_s) ∨
      (∃ v' g', P v' g' mid_s ∧ lt v' v ∧ (∀ t_s, Q v' g' t_s → Q v g t_s))
    ) state) →
  (∀ state, Q v0 g0 state → post state) →
  Eventually trans post initial := by
  intro hP hbody hpost
  have h_general : ∀ v g state, P v g state → (∀ t_s, Q v g t_s → Q v0 g0 t_s) → Eventually trans post state := by
    intro v
    induction v using Hwf.induction with
    | h v ih =>
      intro g state hP_state hQ_impl
      have hstep := hbody v g state hP_state
      apply eventually_trans trans _ post state hstep
      intro mid_state h_mid
      match h_mid with
      | .inl hQ =>
        apply Eventually.done
        apply hpost
        apply hQ_impl
        apply hQ
      | .inr ⟨v', ⟨g', ⟨hP_mid, hlt, hQ_impl'⟩⟩⟩ =>
        apply ih v' hlt g' mid_state hP_mid
        intro t_s hQ_t
        apply hQ_impl
        apply hQ_impl'
        apply hQ_t
  apply h_general v0 g0 initial hP
  intro t_s hQ_t
  apply hQ_t

section MonoGen
open Lean Meta Elab Command

structure MonoEntry where
  monoName : Name
  numParams : Nat
  isContParam : Array Bool
  deriving Inhabited

private def stripOptParam (t : Expr) : Expr :=
  if t.isOptParam then t.getArg! 0 else t

private def isContType (t : Expr) : MetaM Bool :=
  forallTelescope (stripOptParam t) fun _ body =>
    return body.isConstOf `Effects

private def getMonoEntry? (fnName : Name) : MetaM (Option MonoEntry) := do
  let monoName := fnName.appendAfter "_mono"
  unless (← getEnv).contains monoName do return none
  let .defnInfo cinfo ← getConstInfo fnName | return none
  lambdaTelescope cinfo.value fun xs _ => do
    let isContParam ← xs.mapM fun x => do isContType (← x.fvarId!.getDecl).type
    return some { monoName, numParams := xs.size, isContParam }

private partial def proveMono (post₁ post₂ : Expr)
    (contMap : Std.HashMap FVarId (Expr × Expr × Expr))
    (e : Expr) : MetaM Expr := do
  let replaceConts (which : Bool) (ex : Expr) : Expr :=
    ex.replace fun sub =>
      if sub.isFVar then
        match contMap[sub.fvarId!]? with
        | some (c1, c2, _) => some (if which then c2 else c1)
        | none => none
      else none
  let e := e.consumeMData
  if e.isHeadBetaTarget then
    return ← proveMono post₁ post₂ contMap e.headBeta
  match e with
  | .letE name type val body nonDep =>
    withLetDecl name type val (nondep := nonDep) fun x => do
      let prf ← proveMono post₁ post₂ contMap (body.instantiate1 x)
      return .letE name type val (prf.abstract #[x]) nonDep
  | _ =>
    if let some ma ← matchMatcherApp? e (alsoCasesOn := true) then
      let some ma₁ ← matchMatcherApp? (replaceConts false e) (alsoCasesOn := true) | unreachable!
      let some ma₂ ← matchMatcherApp? (replaceConts true e) (alsoCasesOn := true) | unreachable!
      let levels := match ma.uElimPos? with
        | some pos => ma.matcherLevels.set! pos Level.zero
        | none     => ma.matcherLevels
      let newMotive ← forallBoundedTelescope (← inferType ma₁.motive) (some ma.discrs.size) fun xs _ => do
        let e₁_xs := { ma₁ with discrs := xs }.toExpr
        let e₂_xs := { ma₂ with discrs := xs }.toExpr
        let goal ← mkArrow (mkApp2 (mkConst `Effects.All) post₁ e₁_xs) (mkApp2 (mkConst `Effects.All) post₂ e₂_xs)
        mkLambdaFVars xs goal
      let mut newAlts := #[]
      for i in [:ma.alts.size] do
        let alt := ma.alts[i]!
        let numParams := ma.altNumParams[i]!
        let newAlt ← forallBoundedTelescope (← inferType alt) (some numParams) fun patVars _ => do
          let altPrf ← proveMono post₁ post₂ contMap (mkAppN (alt.beta patVars) ma.remaining).headBeta
          mkLambdaFVars patVars altPrf
        newAlts := newAlts.push newAlt
      let res := { ma₁ with matcherLevels := levels, motive := newMotive, alts := newAlts, remaining := #[] }.toExpr
      if ← isTypeCorrect res then
        return res
      let discr := ma.discrs[0]!
      let discrTy ← inferType discr
      let forallGoal ← withLocalDeclD `x discrTy fun x =>
        mkForallFVars #[x] (newMotive.beta #[x])
      let mvar ← mkFreshExprSyntheticOpaqueMVar forallGoal
      let (fvarId, mvarId) ← mvar.mvarId!.intro1P
      let rec solveCases (mId : MVarId) (curTerm : Expr) (fields : Array Expr) : MetaM Unit :=
        mId.withContext do
          let reduced ← whnfCore ({ ma with discrs := #[curTerm] }.toExpr)
          if reduced.getAppFn != e.getAppFn then
            let prf ← proveMono post₁ post₂ contMap reduced
            mId.assign prf
          else if let some fld := fields[0]? then
            let subgoals ← mId.cases fld.fvarId!
            for sg in subgoals do
              let nextTerm := sg.subst.apply curTerm
              let nextFields := sg.fields ++ (fields.drop 1).map sg.subst.apply
              solveCases sg.mvarId nextTerm nextFields
          else
            throwError "proveMono: could not reduce matcher:\n{reduced}"
      solveCases mvarId (mkFVar fvarId) #[mkFVar fvarId]
      return mkApp (← instantiateMVars mvar) discr
    let fn := e.getAppFn
    let args := e.getAppArgs
    if fn.isFVar then
      if let some (_, _, hc) := contMap[fn.fvarId!]? then
        return mkAppN hc args
    if fn.isConstOf `Effects.unimplemented || fn.isConstOf `Effects.gp_unaligned ||
       fn.isConstOf `Effects.unaligned_sp || fn.isConstOf `Effects.nonmem_load ||
       fn.isConstOf `Effects.nonmem_store then
      return mkApp4 (mkConst `Effects.All_of_false) (replaceConts false e) (replaceConts true e) post₁ post₂
    if fn.isConstOf `Effects.require_read_access || fn.isConstOf `Effects.require_write_access then
      return ← proveMono post₁ post₂ contMap (mkApp args[2]! (mkConst ``Unit.unit)).headBeta
    if fn.isConstOf `Effects.require_exec_access then
      return ← proveMono post₁ post₂ contMap (mkApp args[1]! (mkConst ``Unit.unit)).headBeta
    if fn.isConstOf `Effects.undefined then
      let α := args[0]!
      let inst := args[1]!
      let cont := args[2]!
      let hcont ← withLocalDeclD `v α fun v => do
        let prf ← proveMono post₁ post₂ contMap (mkApp cont v).headBeta
        mkLambdaFVars #[v] prf
      return mkAppN (mkConst `Effects.All_undefined)
        #[α, inst, replaceConts false cont, replaceConts true cont, post₁, post₂, hcont]
    if fn.isConstOf ``ite && args.size == 5 then
      let c := args[1]!
      let inst := args[2]!
      let t := args[3]!
      let el := args[4]!
      let ht ← proveMono post₁ post₂ contMap t
      let he ← proveMono post₁ post₂ contMap el
      return mkAppN (mkConst `Effects.All_ite)
        #[c, inst, replaceConts false t, replaceConts true t, replaceConts false el, replaceConts true el, post₁, post₂, ht, he]
    if fn.isConstOf ``dite && args.size == 5 then
      let c := args[1]!
      let inst := args[2]!
      let t := args[3]!
      let el := args[4]!
      let ht ← withLocalDeclD `h c fun h => do
        mkLambdaFVars #[h] (← proveMono post₁ post₂ contMap (mkApp t h).headBeta)
      let he ← withLocalDeclD `h (mkNot c) fun h => do
        mkLambdaFVars #[h] (← proveMono post₁ post₂ contMap (mkApp el h).headBeta)
      return mkAppN (mkConst `Effects.All_dite)
        #[c, inst, replaceConts false t, replaceConts true t, replaceConts false el, replaceConts true el, post₁, post₂, ht, he]
    if fn.isConst then
      if let some entry ← getMonoEntry? fn.constName! then
        if args.size == entry.numParams then
          let mut regArgs := #[]
          let mut contPairArgs := #[]
          let mut contHypArgs := #[]
          for i in [:args.size] do
            let arg := args[i]!
            if entry.isContParam[i]! then
              contPairArgs := contPairArgs.push (replaceConts false arg)
              contPairArgs := contPairArgs.push (replaceConts true arg)
              let hArg ← forallTelescope (← inferType arg) fun as _ => do
                let subPrf ← proveMono post₁ post₂ contMap (mkAppN arg as).headBeta
                mkLambdaFVars as subPrf
              contHypArgs := contHypArgs.push hArg
            else
              regArgs := regArgs.push arg
          let allArgs := regArgs ++ contPairArgs ++ #[post₁, post₂] ++ contHypArgs
          return mkAppN (mkConst entry.monoName fn.constLevels!) allArgs
      if let .defnInfo info ← getConstInfo fn.constName! then
        let e' := (info.value.instantiateLevelParams info.levelParams fn.constLevels!).beta args
        return ← proveMono post₁ post₂ contMap e'
    throwError "proveMono: unsupported expression:\n{e}"

def genMonoFor (fnName : Name) : CommandElabM Unit := do
  let monoName := fnName.appendAfter "_mono"
  liftTermElabM do
    let cinfo ← getConstInfoDefn fnName
    let bInfos ← forallTelescope cinfo.type fun xs _ =>
      xs.mapM fun x => do return (← x.fvarId!.getDecl).binderInfo
    lambdaTelescope cinfo.value fun xs body => do
      let mut lctx ← getLCtx
      let mut isContParam : Array Bool := #[]
      let mut actualRegFVars : Array Expr := #[]
      let mut contOrig : Array (FVarId × Name × Expr) := #[]
      for i in [:xs.size] do
        let x := xs[i]!
        let decl ← x.fvarId!.getDecl
        let ty := stripOptParam decl.type
        let bi := bInfos.getD i decl.binderInfo
        lctx := lctx.modifyLocalDecl x.fvarId! fun d => d.setType ty |>.setBinderInfo bi
        let isCont ← isContType ty
        isContParam := isContParam.push isCont
        if isCont then
          contOrig := contOrig.push (x.fvarId!, decl.userName, ty)
        else
          actualRegFVars := actualRegFVars.push x
      withLCtx lctx (← getLocalInstances) do
        let rec buildContPairs (j : Nat) (cPairs : Array Expr)
            (cTriples : Array (FVarId × Expr × Expr)) : MetaM (Expr × Expr) := do
          if h2 : j < contOrig.size then
            let (origId, uname, ty) := contOrig[j]
            withLocalDecl (uname.appendAfter "₁") .implicit ty fun c1 =>
            withLocalDecl (uname.appendAfter "₂") .implicit ty fun c2 =>
              buildContPairs (j + 1) (cPairs.push c1 |>.push c2) (cTriples.push (origId, c1, c2))
          else
            let postTy ← mkArrow (mkConst `MachineState) (mkSort Level.zero)
            withLocalDecl `post₁ .implicit postTy fun post₁ =>
            withLocalDecl `post₂ .implicit postTy fun post₂ => do
              let rec buildContHyps (k : Nat) (hyps : Array Expr)
                  (contMap : Std.HashMap FVarId (Expr × Expr × Expr)) : MetaM (Expr × Expr) := do
                if h3 : k < cTriples.size then
                  let (origId, c1, c2) := cTriples[k]
                  let (_, uname, ty) := contOrig[k]!
                  let hypTy ← forallTelescope ty fun as _ => do
                    let lhs := mkApp2 (mkConst `Effects.All) post₁ (mkAppN c1 as)
                    let rhs := mkApp2 (mkConst `Effects.All) post₂ (mkAppN c2 as)
                    mkForallFVars as (← mkArrow lhs rhs)
                  withLocalDeclD (Name.mkSimple ("h" ++ uname.toString)) hypTy fun hc =>
                    buildContHyps (k + 1) (hyps.push hc) (contMap.insert origId (c1, c2, hc))
                else
                  let mut args₁ := #[]
                  let mut args₂ := #[]
                  for idx in [:xs.size] do
                    if let some (c1, c2, _) := contMap[xs[idx]!.fvarId!]? then
                      args₁ := args₁.push c1
                      args₂ := args₂.push c2
                    else
                      args₁ := args₁.push xs[idx]!
                      args₂ := args₂.push xs[idx]!
                  let lvls := cinfo.levelParams.map mkLevelParam
                  let app₁ := mkAppN (mkConst fnName lvls) args₁
                  let app₂ := mkAppN (mkConst fnName lvls) args₂
                  let goalTy ← mkArrow (mkApp2 (mkConst `Effects.All) post₁ app₁) (mkApp2 (mkConst `Effects.All) post₂ app₂)
                  let prf ← proveMono post₁ post₂ contMap body
                  let allVars := actualRegFVars ++ cPairs ++ #[post₁, post₂] ++ hyps
                  let thmTy ← mkForallFVars allVars goalTy
                  let thmVal ← mkLambdaFVars allVars prf
                  return (thmTy, thmVal)
              buildContHyps 0 #[] {}
        let (thmTy, thmVal) ← buildContPairs 0 #[] #[]
        addAndCompile (.thmDecl {
          name := monoName
          levelParams := cinfo.levelParams
          type := thmTy
          value := thmVal
        })

elab "#gen_mono " ids:ident+ : command => do
  for id in ids do
    let fnName ← resolveGlobalConstNoOverload id
    genMonoFor fnName

end MonoGen

