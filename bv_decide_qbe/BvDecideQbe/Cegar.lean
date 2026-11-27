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
      throwError m!"bv_decide_qbe reached its round limit; increase `cegarRounds` if needed"
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
