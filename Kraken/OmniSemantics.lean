/-
Common Kraken Temporal Logic and OmniSemantics.
-/

import Kraken.Layout
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

class OmniSemantics (Directive : Type) (MachineData : Type) (Effects : outParam (Type 1)) [Kraken.Layout Directive] where
  All : (MachineData × Int64 → Prop) → Effects → Prop
  done : MachineData × Int64 → Effects
  step : Kraken.Executable Directive → MachineData × Int64 → (MachineData × Int64 → Effects) → Effects
  straightline : Kraken.Executable Directive → MachineData × Int64 → (MachineData × Int64 → Effects) → Effects
  interpDirectives : Kraken.Executable Directive → List (Directive × Nat) → MachineData → Int64 → (Int64 → MachineData → Effects) → Effects
  interpDirective : Kraken.Executable Directive → Directive → MachineData → Std.Rco Int64 → (MachineData → Effects) → (Int64 → MachineData → Effects) → Effects
  all_done : ∀ post st, All post (done st) = post st := by intros; rfl
  step_eq : ∀ e st ret, step e st ret = interpDirectives e (e.directivesAtAddress st.2) st.1 st.2 (fun pc s => ret (s, pc)) := by intros; rfl
  straightline_eq : ∀ e st ret, straightline e st ret = interpDirectives e (e.directivesFromAddress st.2) st.1 st.2 (fun pc s => ret (s, pc)) := by intros; rfl
  interp_nil : ∀ e s pc ret, interpDirectives e [] s pc ret = ret pc s := by intros; rfl
  interp_cons : ∀ e d sz ds s pc ret,
    interpDirectives e ((d, sz) :: ds) s pc ret =
      interpDirective e d s (.mk pc (pc + Int64.ofNat sz)) (fun s' => interpDirectives e ds s' (pc + Int64.ofNat sz) ret) ret := by intros; rfl
  interpDirective_mono : ∀ e d s p {next₁ next₂ : MachineData → Effects} {jmp₁ jmp₂ : Int64 → MachineData → Effects} {post₁ post₂},
    (∀ s', All post₁ (next₁ s') → All post₂ (next₂ s')) →
    (∀ pc' s', All post₁ (jmp₁ pc' s') → All post₂ (jmp₂ pc' s')) →
    All post₁ (interpDirective e d s p next₁ jmp₁) →
    All post₂ (interpDirective e d s p next₂ jmp₂)

namespace OmniSemantics

variable {Directive MachineData : Type} {Effects : Type 1} [Kraken.Layout Directive] [os : OmniSemantics Directive MachineData Effects]

def step1 (e : Kraken.Executable Directive) (s : MachineData × Int64) (post : @Post (MachineData × Int64)) : Prop :=
  os.All post (os.step e s os.done)

def straightlineStep (e : Kraken.Executable Directive) (s : MachineData × Int64) (post : @Post (MachineData × Int64)) : Prop :=
  os.All post (os.straightline e s os.done)

theorem interpDirectives_mono (e : Kraken.Executable Directive)
    (ds : List (Directive × Nat)) (s : MachineData) (pc : Int64)
    {ret₁ ret₂ : Int64 → MachineData → Effects}
    {post₁ post₂ : MachineData × Int64 → Prop}
    (hret : ∀ pc' s', os.All post₁ (ret₁ pc' s') → os.All post₂ (ret₂ pc' s'))
    (h : os.All post₁ (os.interpDirectives e ds s pc ret₁)) :
    os.All post₂ (os.interpDirectives e ds s pc ret₂) := by
  induction ds generalizing s pc with
  | nil =>
    rw [os.interp_nil] at h ⊢
    exact hret pc s h
  | cons head tail ih =>
    obtain ⟨d, sz⟩ := head
    rw [os.interp_cons] at h ⊢
    exact os.interpDirective_mono e d s (.mk pc (pc + Int64.ofNat sz))
      (fun s' => ih s' (pc + Int64.ofNat sz)) hret h

theorem interpDirectives_split (e : Kraken.Executable Directive)
    (ds1 ds2 : List (Directive × Nat)) (s : MachineData) (pc : Int64)
    (ret₁ ret₂ : Int64 → MachineData → Effects)
    {post₁ post₂ : MachineData × Int64 → Prop}
    (hjmp : ∀ pc' s', os.All post₁ (ret₁ pc' s') → os.All post₂ (ret₂ pc' s'))
    (hnext : ∀ s',
      os.All post₁ (os.interpDirectives e ds2 s' (ds1.foldl (fun p (_, sz) => p + Int64.ofNat sz) pc) ret₁) →
      os.All post₂ (ret₂ (ds1.foldl (fun p (_, sz) => p + Int64.ofNat sz) pc) s'))
    (h : os.All post₁ (os.interpDirectives e (ds1 ++ ds2) s pc ret₁)) :
    os.All post₂ (os.interpDirectives e ds1 s pc ret₂) := by
  induction ds1 generalizing s pc with
  | nil =>
    rw [os.interp_nil, List.nil_append] at *
    exact hnext s h
  | cons head tail ih =>
    obtain ⟨d, sz⟩ := head
    rw [List.cons_append, os.interp_cons] at h
    rw [os.interp_cons]
    exact os.interpDirective_mono e d s (.mk pc (pc + Int64.ofNat sz))
      (fun s' => ih s' (pc + Int64.ofNat sz) hnext) hjmp h

theorem eventually_step (e : Kraken.Executable Directive) (hwf : e.WellFormed)
    (st : MachineData × Int64) (post : @Post (MachineData × Int64)) :
    straightlineStep e st post →
    Eventually (step1 e) post st := by
  intro h
  let s := st.1
  let pc := st.2
  apply step_cps (step1 e) post (s, pc)
  dsimp [step1, straightlineStep] at *
  rw [os.step_eq, os.straightline_eq] at *
  rw [Kraken.directivesAtFromPrefix e pc] at h
  apply interpDirectives_split e (e.directivesAtAddress pc) _ s pc
    (fun pc' s' => os.done (s', pc'))
    (fun pc' s' => os.done (s', pc'))
    (fun pc' s' hp => by rw [os.all_done] at hp ⊢; exact Eventually.done (s', pc') hp)
    _ h
  intro s' h_after
  rw [os.all_done]
  generalize h_drop : (e.withAddresses.dropWhile (·.1 ≠ pc)).dropWhile (·.1 = pc) = after_pc at h_after
  cases after_pc with
  | nil =>
    rw [List.map_nil, os.interp_nil, os.all_done] at h_after
    exact Eventually.done _ h_after
  | cons y ys =>
    have h_starts_ne : e.withAddresses.dropWhile (·.1 ≠ pc) ≠ [] := by
      intro h_nil; rw [h_nil] at h_drop; contradiction
    obtain ⟨x, xs, h_starts⟩ := List.exists_cons_of_ne_nil h_starts_ne
    have h_starts' : (Kraken.Executable.withAddresses (e.1, e.2)).dropWhile (·.1 ≠ pc) = x :: xs := h_starts
    obtain ⟨hx_eq, ds', h_ds'⟩ := Kraken.withAddresses_dropWhile_eq e.1 e.2 (·.1 ≠ pc) h_starts'
    have hx_pc : x.1 = pc := by simpa using hx_eq
    rw [hx_pc] at h_ds'
    have h_fold : (e.directivesAtAddress pc).foldl (fun p (_, sz) => p + .ofNat sz) pc = y.1 := by
      dsimp [Kraken.Executable.directivesAtAddress]
      rw [h_starts, h_ds'] at h_drop ⊢
      exact Kraken.withAddresses_takeWhile_foldl pc ds' (·.1 = pc) h_drop
    rw [h_fold] at h_after ⊢
    have h_next_from : e.withAddresses.dropWhile (·.1 ≠ y.1) = y :: ys := hwf pc y ys h_drop
    have h_straightline_next : straightlineStep e (s', y.1) post := by
      dsimp [straightlineStep]
      rw [os.straightline_eq]
      dsimp [Kraken.Executable.directivesFromAddress]
      rw [h_next_from]
      exact h_after
    have h_len : (e.withAddresses.dropWhile (·.1 ≠ y.1)).length < (e.withAddresses.dropWhile (·.1 ≠ pc)).length := by
      rw [h_next_from]
      have h_split := List.takeWhile_append_dropWhile (p := (·.1 = pc)) (l := e.withAddresses.dropWhile (·.1 ≠ pc))
      have h_len_eq := congrArg List.length h_split
      rw [List.length_append, h_drop] at h_len_eq
      have h_take_pos : 0 < ((e.withAddresses.dropWhile (·.1 ≠ pc)).takeWhile (·.1 = pc)).length := by
        rw [h_starts, List.takeWhile_cons]
        simp [hx_pc]
      omega
    exact eventually_step e hwf (s', y.1) post h_straightline_next
termination_by (e.withAddresses.dropWhile (·.1 ≠ st.2)).length
decreasing_by exact h_len

theorem eventually_step_cps (e : Kraken.Executable Directive) (hwf : e.WellFormed)
    (st : MachineData × Int64) (post : @Post (MachineData × Int64)) :
    straightlineStep e st (fun mid => Eventually (step1 e) post mid) →
    Eventually (step1 e) post st := by
  intro h
  exact eventually_trans (step1 e) (fun mid => Eventually (step1 e) post mid) post st
    (eventually_step e hwf st _ h) (fun _ => id)

theorem straightlineStep_mono (e : Kraken.Executable Directive) (st : MachineData × Int64)
    {p q : @Post (MachineData × Int64)} (hpq : ∀ s, p s → q s) :
    straightlineStep e st p → straightlineStep e st q := by
  dsimp [straightlineStep]
  rw [os.straightline_eq]
  exact interpDirectives_mono e _ _ _ (fun pc' s' h => by rw [os.all_done] at h ⊢; exact hpq (s', pc') h)

theorem tailrec_loop_straightline (e : Kraken.Executable Directive) (hwf : e.WellFormed)
    (post : @Post (MachineData × Int64)) (initial : MachineData × Int64)
    (P : Nat → @Post (MachineData × Int64)) (v0 : Nat) (hP : P v0 initial)
    (hbody : ∀ v state, P v state →
      straightlineStep e state (fun mid_s => post mid_s ∨ ∃ v', P v' mid_s ∧ v' < v)) :
    straightlineStep e initial (fun mid => Eventually (step1 e) post mid) := by
  refine straightlineStep_mono e initial ?_ (hbody v0 initial hP)
  rintro mid_s (hpost | ⟨v', hP', _⟩)
  · exact .done mid_s hpost
  · refine tailrec_loop (step1 e) post mid_s (fun v () => P v) (fun _ _ => post)
      (· < ·) Nat.lt_wfRel.wf v' () hP' (fun v _ st hst => eventually_step e hwf st _ ?_) (fun _ => id)
    refine straightlineStep_mono e st ?_ (hbody v st hst)
    rintro s (hp | ⟨v'', hp', hlt⟩)
    · exact .inl hp
    · exact .inr ⟨v'', (), hp', hlt, fun _ => id⟩

end OmniSemantics


