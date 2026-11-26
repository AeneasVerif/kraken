module

public import BvDecideQbe.FFI
public import BvDecideQbe.Encode
public import BvDecideQbe.Counterexample
public import LeanQbe.T.Examples.Bitblast.Ref.BVProg
public import Std.Tactic.BVDecide.Reflect
public import Lean.Meta.Tactic.BVDecide.Prover.Basic
public import Lean.Meta.Tactic.BVDecide.Counterexample
public import Lean.Meta.Tactic.BVDecide.Reflect
public import Lean.Elab.DeclarationRange

/-!
# Trust-Pure `UnsatProver` (`S3d`)

Implements §2.1 of `bv_decide_v1_next_steps_plan.md`:
1. Encodes `satExpr.bvExpr` via `BvDecideQbe.encode` / `wordsToByteArrayLE` and sizes the scratch
   workspace upfront via `estimateWorkSize` (with `2x` retry on `.workTooSmall` up to `512 MiB`
   strictly as fallback).
2. Parameterizes the solver backend (`SolveFn := ByteArray → Nat → UInt64 → SolveResult`),
   providing `solveDimacsBackend` (until `Bitblast/Build/` `LinkedCert.append` `bv_solve_bytes`
   lands) as well as clean dependency injection for deterministic testing.
3. On `.unsat`: guards no `FVar`/`MVar`, adds `_expr_def : BVLogicalExpr` via `Lean.addDecl` ONLY
   (no `compileDecl`), builds closed `wsExpr : List Nat`, emits one per-goal axiom
   `_leanqbe.bv_solve.ax`, proves `BVProg.parseWords ws = some _expr_def` by pure kernel
   `Eq.refl`, applies `BVProg.unsat_of_bv_solve_words`, and closes via `satExpr.proveFalse`.
4. On `.sat model`: decodes via `Counterexample.lean` (`evalEfficient`-validated) and returns a
   `CounterExample` (or throws a formatted counterexample error via `throwCounterExample`).
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

/-- Pluggable solver backend: `(progBytes, workBytes, fuel) -> SolveResult`. -/
abbrev SolveFn := ByteArray → Nat → UInt64 → SolveResult

private def dimacsBound : Nat := 2 ^ 28

private def readU32LE (ba : ByteArray) (wordIdx : Nat) : Nat :=
  let i := wordIdx * 4
  let b0 := ba[i]!.toNat
  let b1 := ba[i + 1]!.toNat
  let b2 := ba[i + 2]!.toNat
  let b3 := ba[i + 3]!.toNat
  b0 + 256 * (b1 + 256 * (b2 + 256 * b3))

private def decodeHeaderVarLayout (progBA : ByteArray) :
    Option (Array (Nat × Nat) × Array Nat × Nat) := do
  if progBA.size < 32 || progBA.size % 4 != 0 then none
  let magic := readU32LE progBA 0
  let ver := readU32LE progBA 1
  let nVars := readU32LE progBA 2
  let nNodes := readU32LE progBA 3
  let nCwords := readU32LE progBA 4
  let root := readU32LE progBA 5
  if magic != bvpMagic || ver != bvpVersion || nNodes == 0 || root >= nNodes then none
  let expectedWords := 8 + 2 * nVars + nCwords + 5 * nNodes
  if progBA.size != expectedWords * 4 then none
  let mut varTable : Array (Nat × Nat) := Array.emptyWithCapacity nVars
  let mut atomBase : Array Nat := Array.emptyWithCapacity nVars
  let mut curAtom := 1
  for k in [0:nVars] do
    let wIdx := 8 + 2 * k
    let bvIdx := readU32LE progBA wIdx
    let width := readU32LE progBA (wIdx + 1)
    varTable := varTable.push (bvIdx, width)
    atomBase := atomBase.push curAtom
    curAtom := curAtom + width
  return (varTable, atomBase, curAtom - 1)

private def cnfMaxVar (cnf : CNF Nat) : Nat :=
  cnf.clauses.foldl (fun m cl => cl.literals.foldl (fun m' l => Nat.max m' l.1) m) 0

private def validDimacsB (cnf : CNF Nat) : Bool :=
  decide (cnfMaxVar cnf < dimacsBound) &&
  decide (cnf.clauses.size < dimacsBound) &&
  cnf.clauses.toList.all (fun cl => cl.literals.all (fun l => decide (1 ≤ l.1)))

private def pushNatAscii (ba : ByteArray) (n : Nat) : ByteArray :=
  if n == 0 then
    ba.push 48
  else
    let digits := go (n + 1) n []
    digits.foldl ByteArray.push ba
where
  go : Nat → Nat → List UInt8 → List UInt8
    | 0, _, acc => acc
    | fuel + 1, k, acc =>
      let d : UInt8 := (48 + k % 10).toUInt8
      if k < 10 then d :: acc else go fuel (k / 10) (d :: acc)

private def encodeDimacsBA (cnf : CNF Nat) : ByteArray := Id.run do
  let mut ba := "p cnf ".toUTF8
  ba := pushNatAscii ba (cnfMaxVar cnf)
  ba := ba.push 32
  ba := pushNatAscii ba cnf.clauses.size
  ba := ba.push 10
  for cl in cnf.clauses do
    for (v, pol) in cl.literals do
      if !pol then
        ba := ba.push 45
      ba := pushNatAscii ba v
      ba := ba.push 32
    ba := (ba.push 48).push 10
  return ba

private def remapDimacsModelToBVP1 (entry : AIG.Entrypoint BVBit)
    (varTable : Array (Nat × Nat)) (atomBase : Array Nat) (totalAtomBits : Nat)
    (dimacsModel : ByteArray) : ByteArray := Id.run do
  let mut bitVals : Std.HashMap (Nat × Nat × Nat) UInt8 := {}
  for (decl, idx) in entry.aig.decls.zipIdx do
    if let .atom bvBit := decl then
      let bit : UInt8 :=
        if h : idx < dimacsModel.size then
          if dimacsModel[idx] != 0 then 1 else 0
        else 0
      bitVals := bitVals.insert (bvBit.var, bvBit.w, bvBit.idx.val) bit
  let mut bvpArr := Array.replicate (totalAtomBits + 1) (0 : UInt8)
  let n := min varTable.size atomBase.size
  for h : k in [0:n] do
    have hk1 : k < varTable.size := Nat.lt_of_lt_of_le h.upper (Nat.min_le_left _ _)
    have hk2 : k < atomBase.size := Nat.lt_of_lt_of_le h.upper (Nat.min_le_right _ _)
    let (bvIdx, w) := varTable[k]
    let base := atomBase[k]
    for j in [0:w] do
      if let some b := bitVals.get? (bvIdx, w, j) then
        let pos := base + j
        if pos < bvpArr.size then
          bvpArr := bvpArr.set! pos b
  return ByteArray.mk bvpArr

/-- Fallback `SolveFn` bridging `BVP1` bytes through `BVProg.parse` + `Std` bitblaster +
`FFI.solveDimacsWith` until `Bitblast/Build/` `LinkedCert.append` `bv_solve_bytes` lands. -/
def solveDimacsBackend (progBA : ByteArray) (workBytes : Nat) (fuel : UInt64) : SolveResult :=
  match decodeHeaderVarLayout progBA, BVProg.parse progBA.data.toList with
  | some (varTable, atomBase, totalAtomBits), some bvExpr =>
    let entry := bvExpr.bitblast
    let cnf := (AIG.toCNF entry.relabelNat).relabel (· + 1)
    if !validDimacsB cnf then
      .unknown
    else
      let dimacsBA := encodeDimacsBA cnf
      let wb := workBytes.toUInt64
      match solveDimacsWith dimacsBA wb wb fuel with
      | .sat dimacsModel =>
        .sat (remapDimacsModelToBVP1 entry varTable atomBase totalAtomBits dimacsModel)
      | other => other
  | _, _ => .unknown

/-- Default `bv_decide_qbe` solver backend (1-line swap to `FFI.solveBVProg` once
`Bitblast/Build/` `LinkedCert.append` lands). -/
def defaultSolveFn : SolveFn := solveDimacsBackend

/-- Configuration for `BvDecideQbe`'s trust-pure `UnsatProver`. -/
structure QbeContext where
  fuel : UInt64 := defaultFuel
  solveFn : SolveFn := defaultSolveFn
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

/-- Deterministic `2x` retry loop on `.workTooSmall`, capped at `min 512MiB maxWorkBytes`. -/
def solveWithRetry (solveFn : SolveFn) (progBA : ByteArray)
    (initWorkBytes maxWorkBytes : Nat) (fuel : UInt64) : SolveResult × Nat × Nat :=
  let clampedMax := min BvDecideQbe.maxWorkBytes (max 1 maxWorkBytes)
  let clampedInit := min clampedMax (max 1 initWorkBytes)
  go clampedMax 32 clampedInit 1
where
  go (clampedMax : Nat) : Nat → Nat → Nat → SolveResult × Nat × Nat
    | 0, curWork, attempts => (.workTooSmall, curWork, attempts)
    | steps + 1, curWork, attempts =>
      match solveFn progBA curWork fuel with
      | .workTooSmall =>
        if curWork < clampedMax then
          let doubled := curWork * 2
          let nextWork := if doubled > clampedMax then clampedMax else doubled
          if nextWork <= curWork then (.workTooSmall, curWork, attempts)
          else go clampedMax steps nextWork (attempts + 1)
        else
          (.workTooSmall, curWork, attempts)
      | res => (res, curWork, attempts)

/-- Build a closed `List Nat` expression using tail-recursive folding and raw `Nat` literals. -/
def mkNatListExpr (ws : List Nat) : Expr :=
  let natTy := mkConst ``Nat
  let nil := mkApp (mkConst ``List.nil [0]) natTy
  let cons := mkApp (mkConst ``List.cons [0]) natTy
  ws.reverse.foldl (fun acc w => mkApp2 cons (mkNatLit w) acc) nil

/-- Build the `Prop` matching the `LinkedCert` conclusion word-for-word:
`∃ e : BVLogicalExpr, BVProg.parse (BVProg.wordsToBytesLE ws) = some e ∧ e.Unsat`. -/
def mkBvSolveAxiomType (wsExpr : Expr) : Expr :=
  let bvLogTy := mkConst ``BVLogicalExpr
  let optBvLogTy := mkApp (mkConst ``Option [0]) bvLogTy
  let bytesExpr := mkApp (mkConst ``BVProg.wordsToBytesLE) wsExpr
  let parsedExpr := mkApp (mkConst ``BVProg.parse) bytesExpr
  let eqExpr := mkApp3 (mkConst ``Eq [1]) optBvLogTy parsedExpr
    (mkApp2 (mkConst ``Option.some [0]) bvLogTy (mkBVar 0))
  let unsatExpr := mkApp (mkConst ``BVLogicalExpr.Unsat) (mkBVar 0)
  let pred := mkLambda `e .default bvLogTy (mkApp2 (mkConst ``And) eqExpr unsatExpr)
  mkApp2 (mkConst ``Exists [1]) bvLogTy pred

/-- Format and throw a `CounterExample` error using `explainCounterExampleQuality`. -/
def throwCounterExample {α : Type} (cex : CounterExample) : MetaM α :=
  cex.goal.withContext do
    let err ← explainCounterExampleQuality cex
    throwError (← addMessageContextFull err)

/-- Add `_expr_def` (`Lean.addDecl` only, NO `compileDecl`), emit one per-goal axiom
`_leanqbe.bv_solve.ax`, prove `BVProg.parseWords ws = some _expr_def` by pure kernel `Eq.refl`,
and close via `BVProg.unsat_of_bv_solve_words` + `satExpr.proveFalse`. -/
def mkUnsatProof (reflectionResult : ReflectionResult) (ws : List Nat)
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
  let wsExpr := mkNatListExpr ws
  let axType := mkBvSolveAxiomType wsExpr
  let auxAxiomName ← Lean.mkAuxDeclName `_leanqbe.bv_solve.ax
  Lean.addDecl <| .axiomDecl {
    name := auxAxiomName
    levelParams := []
    type := axType
    isUnsafe := false
  }
  if let some ref := axiomDeclRange? then
    Elab.addDeclarationRangesFromSyntax auxAxiomName ref
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

/-- Trust-pure `UnsatProver` implementing §2.1 of `bv_decide_v1_next_steps_plan.md`. -/
def unsatProver (ctx : QbeContext := {}) : UnsatProver ProveResult :=
  fun (goal : MVarId) (reflectionResult : ReflectionResult) => do
    let bvExpr := reflectionResult.satExpr.bvExpr
    let some enc := BvDecideQbe.encode bvExpr
      | throwError "Tactic `bv_decide_qbe` failed: BVLogicalExpr exceeds BVP1 32-bit limits"
    let progBA := wordsToByteArrayLE enc.words
    let initWork := ctx.initWorkOverride?.getD (estimateWorkSize enc.stats).toNat
    let (res, workUsed, attempts) ←
      withTraceNode `Meta.Tactic.sat (fun _ => return "Solving BVP1 problem in-process") do
        IO.lazyPure fun _ =>
          solveWithRetry ctx.solveFn progBA initWork ctx.maxWorkBytes ctx.fuel
    match res with
    | .unsat =>
      let (auxAxiomName, exprDefName, falsePrf) ←
        mkUnsatProof reflectionResult enc.words ctx.axiomDeclRange?
      goal.assign falsePrf
      return .ok {
        auxAxiomName := auxAxiomName
        exprDefName := exprDefName
        workBytesUsed := workUsed
        attempts := attempts
      }
    | .sat model =>
      let atomsAssignment ← ReifyM.atomsAssignmentMap
      match reconstructValidatedCounterExample bvExpr enc model atomsAssignment with
      | .error err =>
        throwError m!"Tactic `bv_decide_qbe` internal error: {err}"
      | .ok (_, eqs) =>
        let equations := eqs.filterMap fun (lhs, synth, rhs) =>
          if synth then none else some (lhs, rhs)
        return .error {
          goal := goal
          unusedHypotheses := reflectionResult.unusedHypotheses
          equations := equations
          functionAtoms := #[]
        }
    | .workTooSmall =>
      throwError m!"Tactic `bv_decide_qbe` failed: workspace limit ({ctx.maxWorkBytes} B) exceeded"
    | .unknown =>
      throwError "Tactic `bv_decide_qbe` failed: solver returned unknown"

end BvDecideQbe
