module

public import BvDecideQbe.Prover
public import Lean.Meta.Tactic.BVDecide.Prover.Cegar
public import Lean.Meta.Tactic.BVDecide.Normalize
public import Lean.Meta.Tactic.BVDecide.TacticContext
import Lean.Meta.Tactic.BVDecide.External

/-!
# Phase-1 CEGAR Wrapper for `bv_decide_qbe` (`S3d`)

Reuses upstream incremental CaDiCaL (`BvSolverM` + `Cegar.checkUf` + `Cegar.processNewHyps`)
solely for untrusted congruence-lemma discovery (every UF congruence lemma is kernel-checked and
conjoined into `satExpr`), and swaps the final bitblaster check (`Cegar/BitVec.lean`) to the
trust-pure `BvDecideQbe.unsatProver`!

When `uf == false` (`!ctx.config.needsIncremental`), `cegarBlaster` bypasses CaDiCaL entirely and
calls `BvDecideQbe.unsatProver` directly.
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

private def liftBvSolverM {α : Type} (x : BvSolverM α) : CegarM α := do
  let ctx ← CegarM.getTacticContext
  let state ← modifyGet fun s =>
    let state : BitVecSolverState := {
      bitvecState := s.theoryState.bitvecState
      satSolver := s.theoryState.satSolver
      solverTimeBudgetMs := s.solverTimeBudgetMs
      assumptions := #[]
    }
    (state, { s with theoryState.bitvecState := {} })
  let (x, state) ← BvSolverM.run ctx state x
  modify fun s =>
    { s with
        theoryState.bitvecState := state.bitvecState
        solverTimeBudgetMs := state.solverTimeBudgetMs
    }
  return x

private def checkBitVecQbe (qbeCtx : QbeContext) :
    CegarM (Except (Array (Expr × Bool × BVExpr.PackedBitVec)) ProveResult) := do
  withTraceNode `Meta.Tactic.bv (fun _ => return m!"Checking BitVec abstraction") do
    let bvExpr := (← get).satExpr.bvExpr
    let res ← liftBvSolverM do
      BvSolverM.push #[bvExpr]
      BvSolverM.solve
    match res with
    | .ok .. =>
      CegarM.clearCaches
      let reflRes ← CegarM.getReflectionResult
      let proverRes ← unsatProver qbeCtx (← read).goal reflRes
      match proverRes with
      | .ok proveRes => return .ok proveRes
      | .error _ => throwError m!"Error during trust-pure QBE proof recovery"
    | .error assignment =>
      let atomsAssignment ← ReifyM.atomsAssignmentMap
      let aig := (← CegarM.getTheoryState).bitvecState.aig
      let equations := reconstructCounterExample aig assignment atomsAssignment
      return .error equations

/-- Trust-pure Phase-1 CEGAR wrapper: uses `unsatProver` directly unless `ctx.config.uf` is
enabled, in which case incremental CEGAR discovers kernel-proved congruence lemmas and closes
the final UNSAT goal via `unsatProver`. -/
def cegarBlaster (ctx : TacticContext) (qbeCtx : QbeContext := {}) : UnsatProver CegarResult :=
  if ctx.config.needsIncremental then
    cegarLoop
  else
    (unsatProver qbeCtx).map fun proveRes => { lemmas := #[], proveResult? := some proveRes }
where
  checkTermination : CegarM Unit := do
    checkSystem "bv_decide_qbe"
    if (← CegarM.getRounds) == 0 then
      throwError m!"bv_decide_qbe reached its round limit; increase `cegarRounds` if needed"
    CegarM.consumeRound

  configureSolver : CegarM Unit := do
    let solver ← CegarM.getSatSolver
    let opts := External.SatOptions.ofMode (← CegarM.getTacticContext).config.solverMode
    let opts := opts.addIncremental
    opts.configureSolver solver

  cegarLoop : UnsatProver CegarResult := CegarM.run ctx do
    let mut lastCex := #[]
    CegarM.setDidChange true
    configureSolver
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
