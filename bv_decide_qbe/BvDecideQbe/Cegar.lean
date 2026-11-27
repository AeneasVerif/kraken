module

public import BvDecideQbe.Prover
public import Lean.Meta.Tactic.BVDecide.Prover.Cegar
public import Lean.Meta.Tactic.BVDecide.Normalize
public import Lean.Meta.Tactic.BVDecide.TacticContext

/-!
# Single-Solve Phase-1 CEGAR Wrapper for `bv_decide_qbe` (`BB-07`)

Reuses upstream `Cegar.checkUf` + `Cegar.processNewHyps` solely for untrusted congruence-lemma
discovery (every UF congruence lemma is kernel-checked and conjoined into `satExpr`), and checks
every BitVec abstraction directly via `probeBVExpr` (`bv_solve_bytes` in-process):
- Intermediate SAT rounds emit zero axioms (`witness.addAxiom` is never called) and feed the
  `evalEfficient`-validated counterexample directly into `Cegar.checkUf`.
- On final UNSAT, `commitUnsatWitness` emits a single `_leanqbe.bv_solve.ax` axiom and closes the
  goal immediately with zero CaDiCaL invocations and zero double-solve.
-/

set_option autoImplicit false

public section

namespace BvDecideQbe

open Lean
open Lean.Meta
open Lean.Meta.Tactic.BVDecide
open Std.Tactic.BVDecide

/-- Result returned by `BvDecideQbe.cegarBlaster` (`lemmas` from CEGAR + optional `ProveResult`). -/
structure CegarResult where
  lemmas : Array CegarHyp := #[]
  proveResult? : Option ProveResult := none
  deriving Inhabited

private def checkBitVecQbe (qbeCtx : QbeContext) :
    CegarM (Except (Array (Expr × Bool × BVExpr.PackedBitVec)) ProveResult) := do
  withTraceNode `Meta.Tactic.bv (fun _ => return m!"Checking BitVec abstraction") do
    let bvExpr := (← get).satExpr.bvExpr
    match ← probeBVExpr bvExpr qbeCtx with
    | .ok (witness, workUsed, attempts) =>
      CegarM.clearCaches
      let reflRes ← CegarM.getReflectionResult
      let proveRes ← commitUnsatWitness (← read).goal reflRes witness workUsed attempts
        qbeCtx.axiomDeclRange?
      return .ok proveRes
    | .error eqs =>
      return .error eqs

/-- Trust-pure single-solve Phase-1 CEGAR wrapper: uses `unsatProver` directly unless
`ctx.config.needsIncremental` is enabled, in which case incremental CEGAR discovers kernel-proved
congruence lemmas via zero-axiom `bv_solve_bytes` probes and commits once on UNSAT. -/
def cegarBlaster (ctx : TacticContext) (qbeCtx : QbeContext := {}) : UnsatProver CegarResult :=
  if ctx.config.needsIncremental then
    cegarLoop
  else
    (unsatProver qbeCtx).map fun proveRes => { lemmas := #[], proveResult? := some proveRes }
where
  checkTermination : CegarM Unit := do
    checkSystem "bv_decide_qbe"
    if (← CegarM.getRounds) == 0 then
      throwError m!"bv_decide_qbe reached its round limit, consider increasing it via the `cegarRounds` config option"
    CegarM.consumeRound

  cegarLoop : UnsatProver CegarResult := CegarM.run ctx do
    let mut lastCex := #[]
    CegarM.setDidChange true
    while ← CegarM.getDidChange do
      checkTermination
      match ← checkBitVecQbe qbeCtx with
      | .ok proveRes =>
        return .ok { lemmas := ← CegarM.getUsedHyps, proveResult? := some proveRes }
      | .error cex =>
        lastCex := cex
        let cex ← CegarM.CounterExample.ofArray cex
        discard <| Cegar.checkUf cex

      match ← Cegar.processNewHyps with
      | .solved =>
        return .ok { lemmas := ← CegarM.getUsedHyps, proveResult? := none }
      | .newHyps => CegarM.setDidChange true
      | .none => CegarM.setDidChange false

    let equations := lastCex.filterMap fun (lhs, synth, rhs) =>
      if synth then none else some (lhs, rhs)
    let funState := (← getThe Lean.Meta.Tactic.BVDecide.State).theoryState.funState
    return .error {
      goal := (← read).goal
      unusedHypotheses := (← read).unusedHypotheses
      equations := equations
      functionAtoms := funState.atoms.map (·.funExpr)
    }

/-- Reflect and solve a preprocessed `BitVec` goal `g` with hypotheses `hypotheses`. -/
def bvUnsatQbe (g : MVarId) (hypotheses : Array Normalize.Hyp) (ctx : TacticContext)
    (qbeCtx : QbeContext := {}) : Grind.GrindM (Except CounterExample CegarResult) :=
  ReifyM.run (hypotheses := hypotheses) (cfg := ctx.config) do
    closeWithBVReflection g (cegarBlaster ctx qbeCtx)

/-- Default node visit cap for bounded `BitVec` multiplication detection. -/
def defaultBvMulMaxVisits : Nat := 16384

private partial def stripTermParens (stx : Syntax) : Syntax :=
  match stx with
  | `(($t:term)) => stripTermParens t
  | _ => stx

private def structInstHasExplicitAcNf (val : Syntax) : Bool :=
  let val := stripTermParens val
  if val.isOfKind ``Lean.Parser.Term.structInst then
    -- `{ src with ... }` explicitly supplies `acNf` via `src`.
    if !val[1].isNone then
      true
    else
      val[2][0].getSepArgs.any fun field =>
        match field[0] with
        | `(Lean.Parser.Term.structInstLVal| $id:ident) =>
          id.getId.eraseMacroScopes == `acNf
        | _ => false
  else
    -- Opaque `BVDecideConfig` expression: preserve its `acNf`.
    true

/-- Return `true` iff `cfgStx` explicitly specifies `acNf` (via `+acNf`, `-acNf`, `(acNf := ...)`,
or `(config := ...)` setting `acNf` or passing an opaque `BVDecideConfig`). -/
partial def hasExplicitAcNf (cfgStx : Syntax) : Bool :=
  if cfgStx.isOfKind nullKind then
    cfgStx.getArgs.any hasExplicitAcNf
  else if cfgStx.getNumArgs == 1 then
    hasExplicitAcNf (cfgStx.getArg 0)
  else if cfgStx.getNumArgs ≥ 1 then
    match cfgStx.getArg 0 with
    | .atom _ val =>
      if (val == "+" || val == "-") && cfgStx.getNumArgs == 2 then
        identName? (cfgStx.getArg 1) == some `acNf
      else if val == "(" && cfgStx.getNumArgs ≤ 5 then
        match identName? (cfgStx.getArg 1) with
        | some `acNf => true
        | some `config => structInstHasExplicitAcNf (cfgStx.getArg 3)
        | _ => false
      else
        false
    | _ => false
  else if let .atom _ val := cfgStx then
    val == "acNf"
  else
    false
where
  identName? : Syntax → Option Name
    | .ident _ _ n _ => some n.eraseMacroScopes
    | .atom _ val =>
      some (if val.contains '.' then String.toName val else Name.mkSimple val)
    | _ => none

private def isBvMulType (fixedInt : Bool) (ty : Expr) : Bool :=
  match ty.consumeMData.getAppFn.consumeMData with
  | .const n _ =>
    if n == ``BitVec then
      true
    else if fixedInt then
      n == ``UInt8 || n == ``UInt16 || n == ``UInt32 || n == ``UInt64 || n == ``USize ||
      n == ``Int8 || n == ``Int16 || n == ``Int32 || n == ``Int64 || n == ``ISize
    else
      false
  | _ => false

private def isBvMulConst (fixedInt : Bool) (n : Name) : Bool :=
  if n == ``BitVec.mul || n == ``BitVec.instMul then
    true
  else if fixedInt then
    n == ``UInt8.mul || n == ``instMulUInt8 ||
    n == ``UInt16.mul || n == ``instMulUInt16 ||
    n == ``UInt32.mul || n == ``instMulUInt32 ||
    n == ``UInt64.mul || n == ``instMulUInt64 ||
    n == ``USize.mul || n == ``instMulUSize ||
    n == ``Int8.mul || n == ``instMulInt8 ||
    n == ``Int16.mul || n == ``instMulInt16 ||
    n == ``Int32.mul || n == ``instMulInt32 ||
    n == ``Int64.mul || n == ``instMulInt64 ||
    n == ``ISize.mul || n == ``instMulISize
  else
    false

private def bvMulConstNames (fixedInt : Bool) : Array Name :=
  if fixedInt then
    #[``BitVec.mul, ``BitVec.instMul,
      ``UInt8.mul, ``instMulUInt8, ``UInt16.mul, ``instMulUInt16,
      ``UInt32.mul, ``instMulUInt32, ``UInt64.mul, ``instMulUInt64,
      ``USize.mul, ``instMulUSize,
      ``Int8.mul, ``instMulInt8, ``Int16.mul, ``instMulInt16,
      ``Int32.mul, ``instMulInt32, ``Int64.mul, ``instMulInt64,
      ``ISize.mul, ``instMulISize]
  else
    #[``BitVec.mul, ``BitVec.instMul]

private def isBvMulApp (fixedInt : Bool) (e : Expr) : Bool :=
  match e with
  | .app (.app (.app (.app f α) _) γ) _ =>
    f.consumeMData.isConstOf ``HMul.hMul &&
      (isBvMulType fixedInt α || isBvMulType fixedInt γ)
  | .app (.app f α) _ =>
    f.consumeMData.isConstOf ``Mul.mul && isBvMulType fixedInt α
  | _ => false

/-- Fast, bounded DAG scan detecting any `BitVec` (or fixed-width int when `fixedInt := true`)
multiplication (`HMul.hMul`, `Mul.mul`, `BitVec.mul`, `BitVec.instMul`, etc.) in `roots`. -/
def hasBvMulExprs (fixedInt : Bool) (roots : Array Expr)
    (maxVisits : Nat := defaultBvMulMaxVisits) : Bool := Id.run do
  let mut stack := roots
  let mut visited : Std.HashSet Sym.ExprPtr := {}
  let mut remaining := maxVisits
  while remaining > 0 && !stack.isEmpty do
    let e := stack.back!
    stack := stack.pop
    match e with
    | .const n _ =>
      remaining := remaining - 1
      if isBvMulConst fixedInt n then
        return true
    | .bvar _ | .fvar _ | .mvar _ | .sort _ | .lit _ =>
      pure ()
    | .mdata _ b =>
      remaining := remaining - 1
      stack := stack.push b
    | .proj _ _ b =>
      if !visited.contains ⟨e⟩ then
        remaining := remaining - 1
        visited := visited.insert ⟨e⟩
        stack := stack.push b
    | .app f a =>
      if !visited.contains ⟨e⟩ then
        remaining := remaining - 1
        visited := visited.insert ⟨e⟩
        if isBvMulApp fixedInt e then
          return true
        stack := stack.push a
        stack := stack.push f
    | .forallE _ d b _ | .lam _ d b _ =>
      if !visited.contains ⟨e⟩ then
        remaining := remaining - 1
        visited := visited.insert ⟨e⟩
        stack := stack.push d
        stack := stack.push b
    | .letE _ t v b _ =>
      if !visited.contains ⟨e⟩ then
        remaining := remaining - 1
        visited := visited.insert ⟨e⟩
        stack := stack.push t
        stack := stack.push v
        stack := stack.push b
  return false

/-- Bounded check for `BitVec` (or fixed-width int) multiplication in goal `g` and its local
context (scanning `g`'s target first). -/
def hasBvMulInGoal (fixedInt : Bool) (g : MVarId)
    (maxVisits : Nat := defaultBvMulMaxVisits) : MetaM Bool :=
  g.withContext do
    let mut roots : Array Expr := #[]
    for ldecl in ← getLCtx do
      if !ldecl.isImplementationDetail then
        if let some val := ldecl.value? then
          roots := roots.push (← instantiateMVars val)
        roots := roots.push (← instantiateMVars ldecl.type)
    roots := roots.push (← instantiateMVars (← g.getType))
    return hasBvMulExprs fixedInt roots maxVisits

/-- Bounded check for `BitVec` (or fixed-width int) multiplication in a `grind` goal's e-graph
and underlying `MVarId`. -/
def hasBvMulInGrindGoal (fixedInt : Bool) (g : Grind.Goal)
    (maxVisits : Nat := defaultBvMulMaxVisits) : MetaM Bool := do
  if (bvMulConstNames fixedInt).any fun n => g.indicesFound.contains (.const n) then
    return true
  let mut appRoots : Array Expr := #[]
  if let some apps := g.appMap.find? (.const ``HMul.hMul) then
    for app in apps do
      appRoots := appRoots.push app
      if appRoots.size ≥ 256 then break
  if let some apps := g.appMap.find? (.const ``Mul.mul) then
    for app in apps do
      appRoots := appRoots.push app
      if appRoots.size ≥ 512 then break
  if !appRoots.isEmpty && hasBvMulExprs fixedInt appRoots maxVisits then
    return true
  hasBvMulInGoal fixedInt g.mvarId maxVisits

/-- Resolve the effective `BVDecideConfig` for `g`: honor any explicit `acNf` setting in `cfgStx`,
otherwise enable `acNf` iff `g` contains a `BitVec` (or fixed-width int) multiplication. -/
def resolveAutoAcNf (cfgStx : Syntax) (cfg : Lean.Elab.Tactic.BVDecide.BVDecideConfig)
    (g : MVarId) (maxVisits : Nat := defaultBvMulMaxVisits) :
    MetaM Lean.Elab.Tactic.BVDecide.BVDecideConfig := do
  if cfg.acNf || hasExplicitAcNf cfgStx then
    return cfg
  if ← hasBvMulInGoal cfg.fixedInt g maxVisits then
    return { cfg with acNf := true }
  return cfg

/-- Resolve the effective `BVDecideConfig` for a `grind`/`sym` goal `g` (respecting explicit
`acNf` in `cfgStx` and gating automatic `acNf` strictly on `BitVec` multiplication presence). -/
def resolveAutoAcNfGrind (cfgStx : Syntax) (cfg : Lean.Elab.Tactic.BVDecide.BVDecideConfig)
    (g : Grind.Goal) (fixedInt : Bool := cfg.fixedInt)
    (maxVisits : Nat := defaultBvMulMaxVisits) :
    MetaM Lean.Elab.Tactic.BVDecide.BVDecideConfig := do
  if cfg.acNf || hasExplicitAcNf cfgStx then
    return cfg
  if ← hasBvMulInGrindGoal fixedInt g maxVisits then
    return { cfg with acNf := true }
  return cfg

/-- Build a `TacticContext` without invoking external `cadical` discovery or temp files. -/
def mkQbeTacticContext (config : Lean.Elab.Tactic.BVDecide.BVDecideConfig)
    (restrictedTypes : Option (Array Name) := none) : TacticContext :=
  {
    exprDef := .anonymous
    certDef := .anonymous
    reflectionDef := .anonymous
    solver := ""
    lratPath := ""
    config := config
    restrictedTypes := restrictedTypes
  }

/-- Run `bv_decide_qbe` on `target`, returning either a `CounterExample` or `CegarResult`. -/
def bvDecideQbe' (target : Normalize.Target) (ctx : TacticContext)
    (qbeCtx : QbeContext := {}) : Grind.GrindM (Except CounterExample CegarResult) := do
  Normalize.PreProcessM.run' ctx.preProcessContext target do
    let solved ← Normalize.bvNormalize
    if solved then return .ok { lemmas := #[], proveResult? := none }
    bvUnsatQbe (← Normalize.PreProcessM.getTargetMVarId)
      (← Normalize.PreProcessM.getHyps) ctx qbeCtx

/-- Run `bv_decide_qbe'` and throw a formatted counterexample error on SAT. -/
def bvDecideQbe (target : Normalize.Target) (ctx : TacticContext)
    (qbeCtx : QbeContext := {}) : Grind.GrindM CegarResult := do
  match ← bvDecideQbe' target ctx qbeCtx with
  | .ok res => return res
  | .error counterExample => throwCounterExample counterExample

end BvDecideQbe
