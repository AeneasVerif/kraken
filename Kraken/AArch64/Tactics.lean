import Kraken.AArch64.Syntax
import Kraken.AArch64.Semantics
import Kraken.AArch64.OmniSemantics

--------------------------------------------------------------------------------

open Lean Meta Sym Sym.DSimp
open Elab Tactic

partial def peelLambdaLetsAArch64 (f : Expr) (args : Array Expr) (fvars : Array Expr) (k : Expr → Array Expr → DSimpM Result) : DSimpM Result := do
  match f with
  | .lam binderName binderType body binderInfo =>
    match body with
    | .letE letName letType letVal letBody _ =>
      if !letType.hasLooseBVar 0 && !letVal.hasLooseBVar 0 then
        withLetDecl letName letType letVal fun fvarLet => do
          let instBody : Expr := letBody.instantiate1 fvarLet
          let newLambda := .lam binderName binderType instBody binderInfo
          peelLambdaLetsAArch64 newLambda args (fvars.push fvarLet) k
      else
        k (mkAppN f args) fvars
    | _ => k (mkAppN f args) fvars
  | _ => k (mkAppN f args) fvars

partial def peelLetsAArch64 (e : Expr) (fvars : Array Expr) (k : Expr → Array Expr → DSimpM Result) : DSimpM Result := do
  match e with
  | .letE name type val body _ =>
    withLetDecl name type val fun fvar =>
      peelLetsAArch64 (body.instantiate1 fvar) (fvars.push fvar) k
  | _ =>
    if e.isApp && e.getAppFn.isLambda then
      peelLambdaLetsAArch64 e.getAppFn e.getAppArgs fvars k
    else
      k e fvars

partial def peelArgsLetsAArch64 (args : Array Expr) (i : Nat) (peeled : Array Expr) (fvars : Array Expr) (k : Array Expr → Array Expr → DSimpM Result) : DSimpM Result := do
  if h : i < args.size then
    let arg := args[i]
    peelLetsAArch64 arg fvars fun arg' fvars' =>
      peelArgsLetsAArch64 args (i + 1) (peeled.push arg') fvars' k
  else
    k peeled fvars

def kdeltaBetaOnlyAArch64 (targets: List Name) : DSimproc := fun e => do
  unless e.isApp && targets.any e.getAppFn'.isConstOf do return .rfl

  let f := e.getAppFn'
  let args := e.getAppArgs

  peelArgsLetsAArch64 args 0 #[] #[] fun (args : Array Expr) (fvars : Array Expr) => do
    if f.isConstOf ``Effects.All && args[1]!.isApp && args[1]!.getAppFn'.isConstOf ``Directives.interp then
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

def gimmickIdAArch64 (p: Prop): Prop := p

def gimmickAArch64 {p: Prop} (h: gimmickIdAArch64 p): p := by
  simp [gimmickIdAArch64] at h
  assumption

def gimmickInvAArch64 {p: Prop} (h: p): gimmickIdAArch64 p := by
  simp [gimmickIdAArch64]
  assumption

def klogAArch64 : DSimproc := fun e => do
  let s := (← get).numSteps
  if e.isApp && e.getAppFn'.isConstOf ``gimmickIdAArch64 then
    logInfo m!"klog: step {s} visiting\n{e.getAppRevArgs[0]!}"
  return .rfl

syntax (name := symKStepAArch64) "kstep_aarch64 " : grind

def kdsimpMatchAArch64: DSimproc := fun e => do
  let some e' ← reduceRecMatcher? e | return .rfl
  let e'' ← Sym.foldProjs e'
  if isSameExpr e e'' then
    return .rfl
  else
    return .step (← share e'')

def kbetaAArch64: DSimproc := fun e => do
  unless e.isApp do return .rfl
  let f := e.getAppFn
  if f.isHeadBetaTargetFn false then
    let e' ← betaRevS f e.getAppRevArgs
    return .step e'
  else
    return .rfl

def kdsimpProjAArch64 : DSimproc := fun e => do
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

@[grind_tactic symKStepAArch64]
def evalSymKStepAArch64 : Grind.GrindTactic :=
  fun _stx : Syntax => do
  let gGoal : Grind.Goal ← Grind.getMainGoal
  let mvarId := gGoal.mvarId

  let gimmickRule ← mkBackwardRuleFromDecl ``gimmickAArch64
  let mvarId ← Grind.liftGrindM (do
    let .goals [mvarId] ← gimmickRule.apply mvarId | failure
    pure mvarId
  )

  let goal ← mvarId.getType

  let decls := [
    ``MachineData.setRegOrSp, ``MachineData.setRegOrZr,
    ``Reg64s.getRegOrSp, ``Reg64s.getRegOrZr, ``Reg64s.setRegOrSp, ``Reg64s.setRegOrZr,
    ``RegOrSp.base, ``RegOrZr.base,
    ``Reg64s.getRegOrSp64, ``Reg64s.getRegOrZr64, ``Reg64s.setRegOrSp64, ``Reg64s.setRegOrZr64,
    ``Reg64s.getXReg, ``Reg64s.setXReg,
    ``AddrExpr.checkSPAlignment, ``AddrExpr.eval, ``AddrExpr.interp, ``Literal.interp, ``AddrOrLit.interp,
    ``ExtOrImmReg.interp, ``ShiftRegExpr.interp, ``ExtRegExpr.interp, ``MemExtRegExpr.interp, ``ConstExpr.interp, ``ConstExpr.evalBranchTarget,
    ``BitVec.apply_extend, ``BitVec.apply_mem_extend,
    ``Directive.interp, ``Instr.interp, ``Operation.interp,
    ``Executable.directivesFromAddress, ``Executable.directivesAtAddress, ``Executable.withAddresses, ``Executable.labels,
    ``Effects.All, ``CondCode.interp, ``StatusFlags.from_result, ``StatusFlags.adds, ``StatusFlags.subs,
    ``Width.type, ``Width.bits, ``Width.bytes, ``Width.bytesv,
    ``BitVec.drop, ``BitVec.take, ``BitVec.extractLsb', ``BitVec.truncate
  ]

  let goal ← Grind.liftGrindM (do
    Sym.dsimp
      (config := { maxSteps := 1000000 })
      (methods := { pre := klogAArch64 >> kdeltaBetaOnlyAArch64 decls >> kdsimpMatchAArch64 >> kdsimpProjAArch64 >> kbetaAArch64})
      goal)

  let mvarId ← mvarId.replaceTargetDefEq goal

  let gimmickRule ← mkBackwardRuleFromDecl ``gimmickInvAArch64
  let mvarId ← Grind.liftGrindM (do
    let .goals [mvarId] ← gimmickRule.apply mvarId | failure
    pure mvarId
  )

  Grind.setGoals [ { gGoal with mvarId } ]
