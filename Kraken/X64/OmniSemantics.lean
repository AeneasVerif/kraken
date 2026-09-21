/-
Omnisemantics for x64.
-/

import Kraken.Attribute
import Kraken.OmniSemantics
import Kraken.X64.Semantics

@[kstep] def Effects.All (post : MachineState → Prop) : Effects → Prop
  | .done a => post a
  | .unimplemented _ => False
  | .gp_unaligned .. => False
  | .nonmem_load .. => False
  | .nonmem_store .. => False
  | @Effects.undefined α _ cont => ∀ v: α, (cont v).All post
  | .require_read_access _ _ cont => (cont ()).All post
  | .require_write_access _ _ cont => (cont ()).All post
  | .require_exec_access _ cont => (cont ()).All post

theorem Effects.All_of_false {_e₁ e₂ : Effects} {_post₁ post₂ : MachineState → Prop}
    (h : False) : e₂.All post₂ := False.elim h

theorem Effects.All_undefined {α : Type} [NondetSupportingType α]
    {cont₁ cont₂ : α → Effects} {post₁ post₂ : MachineState → Prop}
    (hcont : ∀ v, (cont₁ v).All post₁ → (cont₂ v).All post₂)
    (h : (@Effects.undefined α _ cont₁).All post₁) :
    (@Effects.undefined α _ cont₂).All post₂ :=
  fun v => hcont v (h v)

theorem Effects.All_ite {c : Prop} [Decidable c] {t₁ t₂ e₁ e₂ : Effects} {post₁ post₂ : MachineState → Prop}
    (ht : t₁.All post₁ → t₂.All post₂) (he : e₁.All post₁ → e₂.All post₂) :
    (if c then t₁ else e₁).All post₁ → (if c then t₂ else e₂).All post₂ := by
  split
  · exact ht
  · exact he

theorem Effects.All_dite {c : Prop} [Decidable c] {t₁ t₂ : c → Effects} {e₁ e₂ : ¬c → Effects} {post₁ post₂ : MachineState → Prop}
    (ht : ∀ h, (t₁ h).All post₁ → (t₂ h).All post₂) (he : ∀ h, (e₁ h).All post₁ → (e₂ h).All post₂) :
    (if h : c then t₁ h else e₁ h).All post₁ → (if h : c then t₂ h else e₂ h).All post₂ := by
  split
  · exact ht ‹_›
  · exact he ‹_›

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
    return body.isConstOf ``Effects

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
        let goal ← mkArrow (mkApp2 (mkConst ``Effects.All) post₁ e₁_xs) (mkApp2 (mkConst ``Effects.All) post₂ e₂_xs)
        mkLambdaFVars xs goal
      let discrTy ← whnf (← inferType ma.discrs[0]!)
      if let .inductInfo indInfo ← getConstInfo discrTy.getAppFn.constName! then
        if ma.alts.size < indInfo.numCtors then
          let indLevels := discrTy.getAppFn.constLevels!
          let indParams := discrTy.getAppArgs.take indInfo.numParams
          let mut ctorAlts := #[]
          for ctorName in indInfo.ctors do
            let ctorInfo ← getConstInfoCtor ctorName
            let ctorFn := mkAppN (mkConst ctorName indLevels) indParams
            let ctorAlt ← forallBoundedTelescope (← inferType ctorFn) (some ctorInfo.numFields) fun fieldVars _ => do
              let ctorApp := mkAppN ctorFn fieldVars
              let reduced ← whnfCore ({ ma with discrs := #[ctorApp] }.toExpr)
              let prf ← proveMono post₁ post₂ contMap reduced
              mkLambdaFVars fieldVars prf
            ctorAlts := ctorAlts.push ctorAlt
          let casesOnFn := mkConst (indInfo.name ++ `casesOn) (Level.zero :: indLevels)
          return mkAppN casesOnFn (indParams ++ #[newMotive, ma.discrs[0]!] ++ ctorAlts)
      let mut newAlts := #[]
      for i in [:ma.alts.size] do
        let alt := ma.alts[i]!
        let numParams := ma.altNumParams[i]!
        let newAlt ← forallBoundedTelescope (← inferType alt) (some numParams) fun patVars _ => do
          let altPrf ← proveMono post₁ post₂ contMap (mkAppN (alt.beta patVars) ma.remaining).headBeta
          mkLambdaFVars patVars altPrf
        newAlts := newAlts.push newAlt
      return { ma₁ with matcherLevels := levels, motive := newMotive, alts := newAlts, remaining := #[] }.toExpr
    let fn := e.getAppFn
    let args := e.getAppArgs
    if fn.isFVar then
      if let some (_, _, hc) := contMap[fn.fvarId!]? then
        return mkAppN hc args
    if fn.isConstOf ``Effects.unimplemented || fn.isConstOf ``Effects.gp_unaligned ||
       fn.isConstOf ``Effects.nonmem_load || fn.isConstOf ``Effects.nonmem_store then
      return mkApp4 (mkConst ``Effects.All_of_false) (replaceConts false e) (replaceConts true e) post₁ post₂
    if fn.isConstOf ``Effects.require_read_access || fn.isConstOf ``Effects.require_write_access then
      return ← proveMono post₁ post₂ contMap (mkApp args[2]! (mkConst ``Unit.unit)).headBeta
    if fn.isConstOf ``Effects.require_exec_access then
      return ← proveMono post₁ post₂ contMap (mkApp args[1]! (mkConst ``Unit.unit)).headBeta
    if fn.isConstOf ``Effects.undefined then
      let α := args[0]!
      let inst := args[1]!
      let cont := args[2]!
      let hcont ← withLocalDeclD `v α fun v => do
        let prf ← proveMono post₁ post₂ contMap (mkApp cont v).headBeta
        mkLambdaFVars #[v] prf
      return mkAppN (mkConst ``Effects.All_undefined)
        #[α, inst, replaceConts false cont, replaceConts true cont, post₁, post₂, hcont]
    if fn.isConstOf ``ite && args.size == 5 then
      let c := args[1]!
      let inst := args[2]!
      let t := args[3]!
      let el := args[4]!
      let ht ← proveMono post₁ post₂ contMap t
      let he ← proveMono post₁ post₂ contMap el
      return mkAppN (mkConst ``Effects.All_ite)
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
      return mkAppN (mkConst ``Effects.All_dite)
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
            let postTy ← mkArrow (mkConst ``MachineState) (mkSort Level.zero)
            withLocalDecl `post₁ .implicit postTy fun post₁ =>
            withLocalDecl `post₂ .implicit postTy fun post₂ => do
              let rec buildContHyps (k : Nat) (hyps : Array Expr)
                  (contMap : Std.HashMap FVarId (Expr × Expr × Expr)) : MetaM (Expr × Expr) := do
                if h3 : k < cTriples.size then
                  let (origId, c1, c2) := cTriples[k]
                  let (_, uname, ty) := contOrig[k]!
                  let hypTy ← forallTelescope ty fun as _ => do
                    let lhs := mkApp2 (mkConst ``Effects.All) post₁ (mkAppN c1 as)
                    let rhs := mkApp2 (mkConst ``Effects.All) post₂ (mkAppN c2 as)
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
                  let goalTy ← mkArrow (mkApp2 (mkConst ``Effects.All) post₁ app₁) (mkApp2 (mkConst ``Effects.All) post₂ app₂)
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

#gen_mono
  Reg.interp
  MachineData.load
  MachineData.loadAvx
  MachineData.store
  MachineData.storeAvx
  RegOrMem.interp
  AvxRegOrMem.interp
  MachineData.set
  MachineData.setAvx
  MachineData.setAvxLegacy
  Operand.interp
  AvxOperand.interp
  RelRegOrMem.interp
  AvxOperation.interp
  Operation.interp
  Instr.interp
  Directive.interp

theorem Directives.interp_mono [Labels]
    (ds : List (Directive × Nat)) (s : MachineData) (pc : Int64)
    {ret₁ ret₂ : Int64 → MachineData → Effects}
    {post₁ post₂ : MachineState → Prop}
    (hret : ∀ pc' s', (ret₁ pc' s').All post₁ → (ret₂ pc' s').All post₂)
    (h : (Directives.interp ds s pc ret₁).All post₁) :
    (Directives.interp ds s pc ret₂).All post₂ := by
  induction ds generalizing s pc with
  | nil =>
    exact hret pc s h
  | cons head tail ih =>
    obtain ⟨d, sz⟩ := head
    dsimp [Directives.interp] at *
    exact Directive.interp_mono d s (.mk pc (pc + .ofNat sz))
      (fun s' => ih s' (pc + .ofNat sz))
      hret
      h

def step1 [Layout] (e: Executable) (s: MachineState) (post: @Post MachineState) : Prop :=
  (Executable.step e s .done).All post

def straightlineStep [Layout] (e: Executable) (s: MachineState) (post: @Post MachineState) : Prop :=
  (Executable.straightline e s .done).All post

theorem Directives.interp_split [Labels]
    (ds1 ds2 : List (Directive × Nat)) (s : MachineData) (pc : Int64)
    (ret₁ ret₂ : Int64 → MachineData → Effects)
    {post₁ post₂ : MachineState → Prop}
    (hjmp : ∀ pc' s', (ret₁ pc' s').All post₁ → (ret₂ pc' s').All post₂)
    (hnext : ∀ s',
      (Directives.interp ds2 s' (ds1.foldl (fun p (_, sz) => p + .ofNat sz) pc) ret₁).All post₁ →
      (ret₂ (ds1.foldl (fun p (_, sz) => p + .ofNat sz) pc) s').All post₂)
    (h : (Directives.interp (ds1 ++ ds2) s pc ret₁).All post₁) :
    (Directives.interp ds1 s pc ret₂).All post₂ := by
  induction ds1 generalizing s pc with
  | nil =>
    dsimp [Directives.interp] at *
    exact hnext s h
  | cons head tail ih =>
    obtain ⟨d, sz⟩ := head
    dsimp [Directives.interp] at *
    exact Directive.interp_mono d s (.mk pc (pc + .ofNat sz))
      (fun s' => ih s' (pc + .ofNat sz) hnext)
      hjmp
      h

theorem eventually_step [Layout] (e: Executable) (hwf : e.WellFormed) (st: MachineState) (post: @Post MachineState):
    straightlineStep e st post →
    Eventually (step1 e) post st
    := by
  intro h
  let _ : Labels := Executable.labels e
  let s := st.1
  let pc := st.2
  apply step_cps (step1 e) post (s, pc)
  dsimp [step1, straightlineStep, Executable.step, Executable.straightline] at *
  rw [Kraken.directivesAtFromPrefix e pc] at h
  apply Directives.interp_split (e.directivesAtAddress pc) _ s pc
    (fun pc' s' => Effects.done (s', pc'))
    (fun pc' s' => Effects.done (s', pc'))
    (fun pc' s' hp => Eventually.done (s', pc') hp)
    _ h
  intro s' h_after
  dsimp [Effects.All]
  generalize h_drop : (e.withAddresses.dropWhile (·.1 ≠ pc)).dropWhile (·.1 = pc) = after_pc at h_after
  cases after_pc with
  | nil =>
    dsimp [Directives.interp, Effects.All] at h_after
    exact Eventually.done _ h_after
  | cons y ys =>
    have h_starts_ne : e.withAddresses.dropWhile (·.1 ≠ pc) ≠ [] := by
      intro h_nil
      rw [h_nil] at h_drop
      contradiction
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
      dsimp [straightlineStep, Executable.straightline, Kraken.Executable.directivesFromAddress]
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

theorem eventually_step_cps [Layout] (e : Executable) (hwf : e.WellFormed)
    (st : MachineState) (post : @Post MachineState) :
    straightlineStep e st (fun mid => Eventually (step1 e) post mid) →
    Eventually (step1 e) post st := by
  intro h
  exact eventually_trans (step1 e) (fun mid => Eventually (step1 e) post mid) post st
    (eventually_step e hwf st _ h) (fun _ => id)


theorem straightlineStep_mono [Layout] (e : Executable) (st : MachineState)
    {p q : @Post MachineState} (hpq : ∀ s, p s → q s) :
    straightlineStep e st p → straightlineStep e st q :=
  let _ := e.labels
  Directives.interp_mono _ _ _ (fun _ _ => hpq _)

theorem tailrec_loop_straightline [Layout] (e : Executable) (hwf : e.WellFormed)
    (post : @Post MachineState) (initial : MachineState)
    (P : Nat → @Post MachineState) (v0 : Nat) (hP : P v0 initial)
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

