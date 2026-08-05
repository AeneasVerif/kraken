import Kraken.X64.Syntax
import Kraken.X64.Semantics
import Kraken.X64.OmniSemantics
import Kraken.X64.PrintIntel
import Lean

theorem Executable.withAddresses_map_snd (ds : List (Directive × Nat)) (a : Int64) :
    (Executable.withAddresses (a, ds)).map (·.2) = ds := by
  induction ds generalizing a with
  | nil =>
    unfold Executable.withAddresses
    rfl
  | cons d ds ih =>
    unfold Executable.withAddresses
    dsimp
    rw [ih (a + .ofNat d.2)]

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

open Lean Meta Sym Sym.DSimp PrettyPrinter Delaborator SubExpr
open Elab Tactic

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

    if f.isConstOf ``Effects.All && args[1]!.isApp && args[1]!.getAppFn'.isConstOf ``Directives.interp then
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

def gimmick {p: Prop} (h: gimmickId p): p := by
  simp [gimmickId] at h
  assumption

def gimmickInv {p: Prop} (h: p): gimmickId p := by
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


syntax (name := symKStep) "kstep " : grind

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
  unless e.isApp && e.getAppFn'.isConstOf ``Effects.All do return .rfl

  let (es, st) ← ExtractLets.extract #[e] |>.run {} |>.run' {} |>.run { givenNames := [] }
  unless st.decls.size > 0 do return .rfl

  let e' := Meta.ExtractLets.mkLetDecls st.decls es[0]!
  let e' ← Sym.share e'
  /- logInfo m!"liftLets produces {e'}" -/
  return .step e'

-- TODO: make our tactic take an optional config to aid debugging
@[grind_tactic symKStep]
def evalSymKStep : Grind.GrindTactic :=
  fun _stx : Syntax => do
  -- A `sym` tactic operates over a pair of the grind state and an MVarId
  let gGoal : Grind.Goal ← Grind.getMainGoal
  let mvarId := gGoal.mvarId

  -- Apply the debug gimmick. We actually *do* expect the goal to be in this form (see comment in
  -- kdeltaBetaOnly).
  let gimmickRule ← mkBackwardRuleFromDecl ``gimmick
  let mvarId ← Grind.liftGrindM (do
    let .goals [mvarId] ← gimmickRule.apply mvarId | failure
    pure mvarId
  )

  let goal ← mvarId.getType

  let decls := [
    ``Reg.interp, ``Reg64s.get, ``Reg.base, ``Reg.offset, ``MachineData.set,
    ``MachineData.setReg, ``Reg64s.set, ``Width.type, ``Width.bits,
    ``Width.bytes,
    ``Width.bytesv,
    ``Reg64s.get64, ``Reg64s.set64, ``BitVec.drop, ``BitVec.take,
    ``BitVec.extractLsb', ``BitVec.truncate, ``ConstExpr.interp,

    -- We INTENTIONALLY do not include Directives.interp -- this serves as our
    -- special marker, and one that determines whether know we can resume.
    ``Directive.interp, ``Instr.interp, ``Operation.interp,
    ``Operand.interp, ``Effects.All,
    ``ConstExpr.interp, ``RegOrMem.interp, ``Reg.interp,
    ``ShiftCountExpr.interp, ``CondCode.interp,
    ``ShiftCountExpr.interpMasked,

    -- We also do not include MachineData.store/load as we intend for those to
    -- be destructed with rw-lemmas.

    ``StatusFlags.from_result
  ]

  let goal ← Grind.liftGrindM (do
    Sym.dsimp
      (config := { maxSteps := 1000000 })
      (methods := { pre := klog >> kdeltaBetaOnly decls >> kdsimpMatch >> kdsimpProj >> kbeta})
      goal)

  -- TEMPORARY: trying to simplify binders in the goal
  /- let goal ← Meta.letToHave goal -/
  /- let goal ← Grind.liftGrindM $ shareCommon goal -/
  /- let mvarId ← mvarId.replaceTargetDefEq goal -/

  /- let simpMethods: Sym.Simp.Methods ← mkSimpMethods4 #[ ``Nat.shiftRight_zero ] -/
  /- let simpResult ← Grind.liftGrindM (Sym.simpGoal mvarId simpMethods) -/
  /- let mvarId ← Grind.liftGrindM (match simpResult with -/
  /-   | .noProgress => pure mvarId -/
  /-   | .goal mvarId => pure mvarId -/
  /-   | .closed => throwError "unexpected") -/

  let mvarId ← mvarId.replaceTargetDefEq goal

  -- Remove the gimmick debug marker.
  let gimmickRule ← mkBackwardRuleFromDecl ``gimmickInv
  let mvarId ← Grind.liftGrindM (do
    let .goals [mvarId] ← gimmickRule.apply mvarId | failure
    pure mvarId
  )

  Grind.setGoals [ { gGoal with mvarId } ]

--------------------------------------------------------------------------------
-- 1. Define custom syntax representations for the Goal View (with Explicit Names)
--------------------------------------------------------------------------------

-- Explicitly named so we can construct them manually and safely
syntax (name := asmSym) "[asm|" ppIndent((ppLine str)*) "]" : term
syntax (name := asmLayoutSym) "[asm_layout|" ppIndent((ppLine term)*) "]" : term

-- Standard fallback syntax for general open lists
syntax "[asm| " term,* " ]" : term

--------------------------------------------------------------------------------
-- 2. Define safe helpers to identify types & navigate arrays
--------------------------------------------------------------------------------

-- Fully compiler-independent indexing helper using core GetElem
def getArg (args : Array Expr) (i : Nat) : Expr :=
  if h : i < args.size then
    GetElem.getElem args i h
  else
    Expr.bvar 0

def isDirectiveType (e : Expr) : MetaM Bool :=
  return Expr.isConstOf e ``Directive

def isNatType (e : Expr) : MetaM Bool :=
  return Expr.isConstOf e ``Nat

def isDirectiveNatType (e : Expr) : MetaM Bool :=
  match e.getAppFn with
  | Expr.const ``Prod _ =>
    let args := e.getAppArgs
    if args.size >= 2 then
      return Expr.isConstOf (getArg args 0) ``Directive && Expr.isConstOf (getArg args 1) ``Nat
    else return false
  | _ => return false

-- Version-independent helper with fully-qualified constructors
def getNatVal? (e : Expr) : Option Nat :=
  match e with
  | Expr.lit (Literal.natVal n) => some n
  | Expr.app (Expr.app (Expr.app (Expr.const ``OfNat.ofNat _) _) (Expr.lit (Literal.natVal n))) _ => some n
  | _ => none

--------------------------------------------------------------------------------
-- 3. Define the consolidated Delaborator (Unsafe, getArg & Explicit Namespaces)
--------------------------------------------------------------------------------

-- Delaborates individual (Directive × Nat) pairs beautifully as "@N: instruction"
@[app_delab Prod.mk]
unsafe def delabDirectiveNatPair : Delab := do
  let e ← getExpr
  let args := e.getAppArgs
  if args.size >= 4 then
    let alpha := getArg args 0
    let beta := getArg args 1
    if (← isDirectiveType alpha) && (← isNatType beta) then
      let dExpr := getArg args 2
      let nExpr := getArg args 3

      -- 1. Evaluates closed Directive parts to their authentic ToString assembly format
      let dStr ← if !dExpr.hasFVar && !dExpr.hasMVar then
        let typeExpr ← Meta.inferType dExpr
        let d ← Meta.evalExpr Directive typeExpr dExpr
        pure s!"{d}"
      else
        pure "<symbolic_directive>"

      -- 2. Extract the Nat index/offset from nExpr using fully-qualified matches
      let idxStr ← match nExpr with
        | Expr.app _ arg =>
          if let some n := getNatVal? arg then
            pure s!"{n}"
          else
            -- If it's a symbolic index (e.g. `layout.size 0`), navigate inside to get the index term
            let idxStx ← withAppArg (withAppArg delab)
            let fmt ← PrettyPrinter.ppTerm idxStx
            pure s!"{fmt}"
        | _ =>
          if let some n := getNatVal? nExpr then
            pure s!"{n}"
          else
            let idxStx ← withAppArg delab
            let fmt ← PrettyPrinter.ppTerm idxStx
            pure s!"{fmt}"

      let combinedStr := s!"@{idxStr}: {dStr}"
      return Syntax.mkStrLit combinedStr
  failure

-- Recursive helper to process Lists of symbolic pairs
unsafe def delabDirectiveNatListGo : DelabM (List Term) := do
  let curr ← getExpr
  if curr.isAppOfArity ``List.cons 3 then
    let head ← withAppFn (withAppArg delab)
    let tail ← withAppArg delabDirectiveNatListGo
    return head :: tail
  else if curr.isAppOfArity ``List.nil 1 then
    return []
  else
    let tail ← delab
    return [tail]

-- Standalone helper for List Directive (Program)
unsafe def delabProgramListGo : DelabM (List Term) := do
  let curr ← getExpr
  if curr.isAppOfArity ``List.cons 3 then
    let head ← withAppFn (withAppArg delab)
    let tail ← withAppArg delabProgramListGo
    return head :: tail
  else if curr.isAppOfArity ``List.nil 1 then
    return []
  else
    let tail ← delab
    return [tail]

@[app_delab List.cons]
unsafe def delabProgramList : Delab := do
  let e ← getExpr
  let args := e.getAppArgs
  if args.size >= 3 then
    let alpha := getArg args 0

    -- ==========================================
    -- Case A: List Directive (Program)
    -- ==========================================
    if ← isDirectiveType alpha then
      if !e.hasFVar && !e.hasMVar then
        let typeExpr ← Meta.inferType e
        let prog ← Meta.evalExpr (List Directive) typeExpr e
        let lines := prog.map (fun d => s!"{d}")
        let linesStx : Array Syntax := lines.map (fun line => Syntax.mkStrLit line) |>.toArray

        -- Manually build raw Syntax node and coerce to Term with anonymous constructor ⟨...⟩
        let node := Syntax.node SourceInfo.none ``asmSym #[
          Syntax.atom SourceInfo.none "[asm|",
          Syntax.node SourceInfo.none nullKind linesStx,
          Syntax.atom SourceInfo.none "]"
        ]
        return ⟨node⟩
      else
        let elems ← delabProgramListGo
        let elemsArr := elems.toArray
        return ← `([asm| $elemsArr,* ])

    -- ==========================================
    -- Case B: List (Directive × Nat) (Layout)
    -- ==========================================
    else if ← isDirectiveNatType alpha then
      if !e.hasFVar && !e.hasMVar then
        let typeExpr ← Meta.inferType e
        let prog ← Meta.evalExpr (List (Directive × Nat)) typeExpr e
        let lines := prog.map (fun (d, sz) => s!"{d}  [size: {sz}]")
        let linesStx : Array Syntax := lines.map (fun line => Syntax.mkStrLit line) |>.toArray

        -- Manually build raw Syntax node and coerce to Term with anonymous constructor ⟨...⟩
        let node := Syntax.node SourceInfo.none ``asmSym #[
          Syntax.atom SourceInfo.none "[asm|",
          Syntax.node SourceInfo.none nullKind linesStx,
          Syntax.atom SourceInfo.none "]"
        ]
        return ⟨node⟩
      else
        -- Fallback: Manually build raw Syntax node and coerce to Term with anonymous constructor ⟨...⟩
        let elems ← delabDirectiveNatListGo
        let elemsArr : Array Syntax := elems.map (·.raw) |>.toArray
        let node := Syntax.node SourceInfo.none ``asmLayoutSym #[
          Syntax.atom SourceInfo.none "[asm_layout|",
          Syntax.node SourceInfo.none nullKind elemsArr,
          Syntax.atom SourceInfo.none "]"
        ]
        return ⟨node⟩

  failure
