module

public import BvDecideQbe.Config
public import BvDecideQbe.FFI
public import BvDecideQbe.Encode
public import BvDecideQbe.Counterexample
public import Std.Tactic.BVDecide.Reflect
public import Lean.Meta.Tactic.BVDecide.Prover.Basic
public import Lean.Meta.Tactic.BVDecide.Counterexample
public import Lean.Meta.Tactic.BVDecide.Reflect

/-!
# Trust-Pure `UnsatProver` (`Step 2`)

1. Encodes `bvExpr` via `BvDecideQbe.encodeForProver` and sizes the scratch workspace upfront via
   `estimateWorkSize` (with `2x` retry on `.workTooSmall` inside `FFI.solveBVProgArrayWithStats`
   up to `1 GiB`).
2. Calls **ONLY** the verified in-process `bv_solve_bytes` entry point via
   `FFI.solveBVProgArrayWithStats` (no public injectable `solveFn`, no `solveDimacsBackend`
   fallback).
3. On `.unsat witness`: guards no `FVar`/`MVar`, adds `_expr_def : BVLogicalExpr` via `Lean.addDecl`
   ONLY (no `compileDecl`), invokes `witness.addAxiomWithWsExpr` to emit `_leanqbe.bv_solve.ax` and
   reuse the single `wsExpr`, proves `BVProg.parseWords witness.words = some _expr_def` by pure
   kernel `Eq.refl`, applies `BVProg.unsat_of_bv_solve_words`, and closes via `satExpr.proveFalse`.
4. On `.sat model`: decodes via `Counterexample.lean` (`evalEfficient`-validated) and returns
   counterexample equations (zero axioms emitted).
-/

set_option autoImplicit false

public section

namespace BvDecideQbe

open Lean
open Lean.Meta
open Lean.Meta.Tactic.BVDecide
open Std.Sat
open Std.Tactic.BVDecide

private def bvProgUnsatOfWordsName : Name :=
  `LeanQbe.T.Examples.Bitblast.Ref.BVProg.unsat_of_bv_solve_words

register_option bv_decide_qbe.mode : String := {
  defValue := "enhanced"
  descr := "Preset mode for `bv_decide_qbe`: \"enhanced\" (default) or \"upstream\"."
}

/-- Parse a `bv_decide_qbe.mode` string (`"enhanced"` or `"upstream"`), throwing a clean error
on invalid values. -/
def parseQbeMode (raw : String) : CoreM QbeMode :=
  match raw with
  | "enhanced" => return .enhanced
  | "upstream" => return .upstream
  | _ =>
    throwError "Invalid value `{raw}` for option `bv_decide_qbe.mode` \
      (expected \"enhanced\" or \"upstream\")"

/-- Resolve the active `QbeMode`, validating `bv_decide_qbe.mode` and preferring explicit `mode?`.
-/
def resolveQbeMode (mode? : Option QbeMode) : CoreM QbeMode := do
  let envMode ← parseQbeMode (bv_decide_qbe.mode.get (← getOptions))
  return mode?.getD envMode

/-- Configuration for `BvDecideQbe`'s trust-pure `UnsatProver`. -/
structure QbeContext where
  fuel : UInt64 := defaultFuel
  initWorkOverride? : Option Nat := none
  maxWorkBytes : Nat := BvDecideQbe.maxWorkBytes
  axiomDeclRange? : Option Syntax := none
  acNf : Bool := false
  features : QbeFeatures := {}

/-- Construct a `QbeContext` from an effective `BVDecideConfig` and resolved `QbeFeatures`. -/
def mkQbeContext (cfg : Lean.Elab.Tactic.BVDecide.BVDecideConfig)
    (features : QbeFeatures := {}) (axiomDeclRange? : Option Syntax := none) : QbeContext :=
  {
    fuel := fuelOfTimeout cfg.timeout
    axiomDeclRange? := axiomDeclRange?
    acNf := cfg.acNf
    features := features
  }

/-- Metadata returned when `unsatProver` closes a goal. -/
structure ProveResult where
  auxAxiomName : Name
  exprDefName : Name
  workBytesUsed : Nat
  attempts : Nat
  deriving Repr, BEq, Inhabited

/-- Format and throw a `CounterExample` error using `explainCounterExampleQuality`. -/
def throwCounterExample {α : Type} (cex : CounterExample) : MetaM α :=
  cex.goal.withContext do
    let err ← explainCounterExampleQuality cex
    throwError (← addMessageContextFull err)

/-- Add `_expr_def` (`Lean.addDecl` only, NO `compileDecl`), commit `witness.addAxiom`,
prove `BVProg.parseWords witness.words = some _expr_def` by pure kernel `Eq.refl`,
and close via `BVProg.unsat_of_bv_solve_words` + `satExpr.proveFalse`. -/
def mkUnsatProof (reflectionResult : ReflectionResult) (witness : UnsatWitness)
    (axiomDeclRange? : Option Syntax := none) : ReifyM (Name × Name × Expr) := do
  let expr ← instantiateMVars reflectionResult.satExpr.expr
  if expr.hasFVar then
    throwError
      m!"Tactic `bv_decide_qbe` failed: reflected expr has free variables:{indentExpr expr}"
  if expr.hasMVar then
    throwError
      m!"Tactic `bv_decide_qbe` failed: reflected expr has metavariables:{indentExpr expr}"
  let exprDefName ← Lean.mkAuxDeclName `_expr_def
  withTraceNode `Meta.Tactic.sat (fun _ => return "Adding _expr_def without compilation") do
    Lean.addDecl <| .defnDecl {
      name := exprDefName
      levelParams := []
      type := mkConst ``BVLogicalExpr
      value := expr
      hints := .abbrev
      safety := .safe
    }
  let (auxAxiomName, wsExpr) ← witness.addAxiomWithWsExpr axiomDeclRange?
  let bvLogTy := mkConst ``BVLogicalExpr
  let optBvLogTy := mkApp (mkConst ``Option [0]) bvLogTy
  let reflectedExpr := mkConst exprDefName
  let someExpr := mkApp2 (mkConst ``Option.some [0]) bvLogTy reflectedExpr
  let hparse := mkApp2 (mkConst ``Eq.refl [1]) optBvLogTy someExpr
  let unsatPrf := mkApp4 (mkConst bvProgUnsatOfWordsName)
    wsExpr reflectedExpr (mkConst auxAxiomName) hparse
  let falsePrf ←
    withTraceNode `Meta.Tactic.sat (fun _ => return "Kernel-checking BVProg.parseWords") do
      reflectionResult.satExpr.proveFalse unsatPrf
  return (auxAxiomName, exprDefName, falsePrf)

/-- Encode `bvExpr` into `BVP1` and solve in-process via `FFI.solveBVProgArrayWithStats` without
emitting any axioms. Shared by `unsatProver` and `+uf` CEGAR probing. -/
def probeBVExpr (bvExpr : BVLogicalExpr) (ctx : QbeContext := {}) :
    ReifyM (Except (Array (Expr × Bool × BVExpr.PackedBitVec)) (UnsatWitness × Nat × Nat)) := do
  let some enc := BvDecideQbe.encodeForProver bvExpr
    | throwError "Tactic `bv_decide_qbe` failed: BVLogicalExpr exceeds BVP1 32-bit limits"
  let initWork := ctx.initWorkOverride?.getD (estimateWorkSize enc.stats).toNat
  let outcome ←
    withTraceNode `Meta.Tactic.sat (fun _ => return "Solving BVP1 problem in-process") do
      (solveBVProgArrayWithStats enc.words initWork.toUInt64
        ctx.maxWorkBytes.toUInt64 ctx.fuel : IO SolveOutcome)
  match outcome.result with
  | .unsat witness =>
    return .ok (witness, outcome.workBytesUsed, outcome.attempts)
  | .sat model =>
    let atomsAssignment ← ReifyM.atomsAssignmentMap
    match reconstructValidatedCounterExampleCore bvExpr enc.varTable enc.atomBase model
        atomsAssignment with
    | .error err =>
      throwError m!"Tactic `bv_decide_qbe` internal error: {err}"
    | .ok (_, eqs) =>
      return .error eqs
  | .workTooSmall =>
    throwError m!"Tactic `bv_decide_qbe` failed: workspace limit ({ctx.maxWorkBytes} B) exceeded"
  | .timeout =>
    let mut err := m!"The SAT solver timed out while solving the problem.\n\
      Consider increasing the timeout with the `timeout` config option."
    if !ctx.acNf then
      err := err ++ m!"\nIf solving your problem relies inherently on using associativity or \
        commutativity, consider enabling the `acNf` config option."
    throwError err
  | .unknown =>
    throwError "Tactic `bv_decide_qbe` failed: solver returned unknown"

/-- Commit an `UnsatWitness` into a kernel proof and assign `goal`. -/
def commitUnsatWitness (goal : MVarId) (reflectionResult : ReflectionResult)
    (witness : UnsatWitness) (workBytesUsed attempts : Nat)
    (axiomDeclRange? : Option Syntax := none) : ReifyM ProveResult := do
  let (auxAxiomName, exprDefName, falsePrf) ←
    mkUnsatProof reflectionResult witness axiomDeclRange?
  goal.assign falsePrf
  return {
    auxAxiomName := auxAxiomName
    exprDefName := exprDefName
    workBytesUsed := workBytesUsed
    attempts := attempts
  }

/-- Trust-pure `UnsatProver` invoking `FFI.solveBVProgWithStats` in-process via `bv_solve_bytes`. -/
def unsatProver (ctx : QbeContext := {}) : UnsatProver ProveResult :=
  fun (goal : MVarId) (reflectionResult : ReflectionResult) => do
    match ← probeBVExpr reflectionResult.satExpr.bvExpr ctx with
    | .ok (witness, workUsed, attempts) =>
      let res ← commitUnsatWitness goal reflectionResult witness workUsed attempts
        ctx.axiomDeclRange?
      return .ok res
    | .error eqs =>
      let equations := eqs.filterMap fun (lhs, synth, rhs) =>
        if synth then none else some (lhs, rhs)
      return .error {
        goal := goal
        unusedHypotheses := reflectionResult.unusedHypotheses
        equations := equations
        functionAtoms := #[]
      }

end BvDecideQbe
