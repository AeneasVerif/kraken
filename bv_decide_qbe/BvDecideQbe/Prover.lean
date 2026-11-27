module

public import BvDecideQbe.FFI
public import BvDecideQbe.Encode
public import BvDecideQbe.Counterexample
public import LeanQbe.T.Examples.Bitblast.Ref.BVProg
public import Std.Tactic.BVDecide.Reflect
public import Lean.Meta.Tactic.BVDecide.Prover.Basic
public import Lean.Meta.Tactic.BVDecide.Counterexample
public import Lean.Meta.Tactic.BVDecide.Reflect

/-!
# Trust-Pure `UnsatProver` (`Step 2`)

1. Encodes `bvExpr` via `BvDecideQbe.encode` and sizes the scratch workspace upfront via
   `estimateWorkSize` (with `2x` retry on `.workTooSmall` inside `FFI.solveBVProgWithStats` up to
   `512 MiB`).
2. Calls **ONLY** the verified in-process `bv_solve_bytes` entry point via
   `FFI.solveBVProgWithStats` (no public injectable `solveFn`, no `solveDimacsBackend` fallback).
3. On `.unsat witness`: guards no `FVar`/`MVar`, adds `_expr_def : BVLogicalExpr` via `Lean.addDecl`
   ONLY (no `compileDecl`), invokes `witness.addAxiom` to emit `_leanqbe.bv_solve.ax`, proves
   `BVProg.parseWords witness.words = some _expr_def` by pure kernel `Eq.refl`, applies
   `BVProg.unsat_of_bv_solve_words`, and closes via `satExpr.proveFalse`.
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
open LeanQbe.T.Examples.Bitblast.Ref

/-- Verify `FFI.lean`'s name constants match `BVProg.wordsToBytesLE` and `BVProg.parse`. -/
example : ``BVProg.wordsToBytesLE = `LeanQbe.T.Examples.Bitblast.Ref.BVProg.wordsToBytesLE := rfl
example : ``BVProg.parse = `LeanQbe.T.Examples.Bitblast.Ref.BVProg.parse := rfl

/-- Configuration for `BvDecideQbe`'s trust-pure `UnsatProver`. -/
structure QbeContext where
  fuel : UInt64 := defaultFuel
  initWorkOverride? : Option Nat := none
  maxWorkBytes : Nat := BvDecideQbe.maxWorkBytes
  axiomDeclRange? : Option Syntax := none

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
  let auxAxiomName ← witness.addAxiom axiomDeclRange?
  let wsExpr := mkNatListExpr witness.words
  let bvLogTy := mkConst ``BVLogicalExpr
  let optBvLogTy := mkApp (mkConst ``Option [0]) bvLogTy
  let reflectedExpr := mkConst exprDefName
  let someExpr := mkApp2 (mkConst ``Option.some [0]) bvLogTy reflectedExpr
  let hparse := mkApp2 (mkConst ``Eq.refl [1]) optBvLogTy someExpr
  let unsatPrf := mkApp4 (mkConst ``BVProg.unsat_of_bv_solve_words)
    wsExpr reflectedExpr (mkConst auxAxiomName) hparse
  let falsePrf ←
    withTraceNode `Meta.Tactic.sat (fun _ => return "Kernel-checking BVProg.parseWords") do
      reflectionResult.satExpr.proveFalse unsatPrf
  return (auxAxiomName, exprDefName, falsePrf)

/-- Encode `bvExpr` into `BVP1` and solve in-process via `FFI.solveBVProgWithStats` without
emitting any axioms. Shared by `unsatProver` and `+uf` CEGAR probing. -/
def probeBVExpr (bvExpr : BVLogicalExpr) (ctx : QbeContext := {}) :
    ReifyM (Except (Array (Expr × Bool × BVExpr.PackedBitVec)) (UnsatWitness × Nat × Nat)) := do
  let some enc := BvDecideQbe.encode bvExpr
    | throwError "Tactic `bv_decide_qbe` failed: BVLogicalExpr exceeds BVP1 32-bit limits"
  let initWork := ctx.initWorkOverride?.getD (estimateWorkSize enc.stats).toNat
  let outcome ←
    withTraceNode `Meta.Tactic.sat (fun _ => return "Solving BVP1 problem in-process") do
      (solveBVProgWithStats enc.words initWork.toUInt64
        ctx.maxWorkBytes.toUInt64 ctx.fuel : IO SolveOutcome)
  match outcome.result with
  | .unsat witness =>
    return .ok (witness, outcome.workBytesUsed, outcome.attempts)
  | .sat model =>
    let atomsAssignment ← ReifyM.atomsAssignmentMap
    match reconstructValidatedCounterExample bvExpr enc model atomsAssignment with
    | .error err =>
      throwError m!"Tactic `bv_decide_qbe` internal error: {err}"
    | .ok (_, eqs) =>
      return .error eqs
  | .workTooSmall =>
    throwError m!"Tactic `bv_decide_qbe` failed: workspace limit ({ctx.maxWorkBytes} B) exceeded"
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
