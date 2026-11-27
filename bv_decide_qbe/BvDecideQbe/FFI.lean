module

public import Lean.Meta.Basic
public import Lean.Elab.DeclarationRange
public import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic

/-!
# Encapsulated Trusted FFI Boundary for `bv_solve_bytes` (`Step 2`)

Only module allowed to invoke `leanqbe_solve_bv_bytes` (`bv_solve_bytes`) or emit
`_leanqbe.bv_solve.ax` axioms:
- `RawSolveResult`, `allocWorkBuf`, and `solveBVBytesRaw` are strictly `private`.
- `UnsatWitness` has a `private mk ::` constructor so no outside module can forge a witness.
- `solveBVProg` / `solveBVProgWithStats` pack `words : List Nat` directly inside this trusted
  boundary, invoke `bv_solve_bytes` with `2x` workspace doubling on `.workTooSmall`, and on `.unsat`
  return a witness whose `addAxiom` continuation emits one per-invocation
  `Lean.addDecl (.axiomDecl ...)` matching `BVProg.unsat_of_bv_solve_words`.
- Probing (e.g. during `+uf` CEGAR) emits zero axioms until `witness.addAxiom` is called on commit.
-/

set_option autoImplicit false

public section

namespace BvDecideQbe

open Lean
open Lean.Meta
open Std.Tactic.BVDecide

private def bvProgWordsToBytesLEName : Name :=
  `LeanQbe.T.Examples.Bitblast.Ref.BVProg.wordsToBytesLE

private def bvProgParseName : Name :=
  `LeanQbe.T.Examples.Bitblast.Ref.BVProg.parse

private def bvProgU32Bound : Nat := 4294967296

/-- Private FFI result matching `leanqbe_solve_bv_bytes` C constructor layout. -/
private inductive RawSolveResult where
  | unsat
  | sat (model : ByteArray)
  | unknown
  | workTooSmall
  deriving BEq, Inhabited

@[extern "leanqbe_alloc_work_buf"]
private opaque allocWorkBuf (n : UInt64) : ByteArray

@[extern "leanqbe_solve_bv_bytes"]
private opaque solveBVBytesRaw (prog : @& ByteArray) (work : ByteArray) (fuel : UInt64) :
    RawSolveResult

/-- Default initial scratch workspace size (`256 KiB`). -/
def defaultInitWorkBytes : UInt64 := 256 * 1024

/-- Default maximum scratch workspace size (`512 MiB`). -/
def defaultMaxWorkBytes : UInt64 := 512 * 1024 * 1024

/-- Default Kissat fuel budget. -/
def defaultFuel : UInt64 := 100000000

/-- Unforgeable UNSAT witness produced only when in-process `bv_solve_bytes` returns `20`.
Constructor `UnsatWitness.mk` is `private` to `BvDecideQbe.FFI`. -/
structure UnsatWitness where
  private mk ::
  words : List Nat
  addAxiom : (axiomDeclRange? : Option Syntax := none) → MetaM Name

/-- Outcome of an in-process verified `bv_solve_bytes` invocation. -/
inductive VerifiedSolveResult where
  | unsat (witness : UnsatWitness)
  | sat (model : ByteArray)
  | unknown
  | workTooSmall

instance : Inhabited VerifiedSolveResult := ⟨.unknown⟩

/-- Full outcome + resource accounting returned by `solveBVProgWithStats`. -/
structure SolveOutcome where
  result : VerifiedSolveResult
  workBytesUsed : Nat
  attempts : Nat
  deriving Inhabited

/-- Build a closed `List Nat` expression using tail-recursive folding and raw `Nat` literals. -/
def mkNatListExpr (ws : List Nat) : Expr :=
  let natTy := mkConst ``Nat
  let nil := mkApp (mkConst ``List.nil [0]) natTy
  let cons := mkApp (mkConst ``List.cons [0]) natTy
  ws.reverse.foldl (fun acc w => mkApp2 cons (mkNatLit w) acc) nil

/-- Build the `Prop` matching `LinkedCert` conclusion word-for-word:
`∃ e : BVLogicalExpr, BVProg.parse (BVProg.wordsToBytesLE ws) = some e ∧ e.Unsat`. -/
private def mkBvSolveAxiomType (wsExpr : Expr) : Expr :=
  let bvLogTy := mkConst ``BVLogicalExpr
  let optBvLogTy := mkApp (mkConst ``Option [0]) bvLogTy
  let bytesExpr := mkApp (mkConst bvProgWordsToBytesLEName) wsExpr
  let parsedExpr := mkApp (mkConst bvProgParseName) bytesExpr
  let eqExpr := mkApp3 (mkConst ``Eq [1]) optBvLogTy parsedExpr
    (mkApp2 (mkConst ``Option.some [0]) bvLogTy (mkBVar 0))
  let unsatExpr := mkApp (mkConst ``BVLogicalExpr.Unsat) (mkBVar 0)
  let pred := mkLambda `e .default bvLogTy (mkApp2 (mkConst ``And) eqExpr unsatExpr)
  mkApp2 (mkConst ``Exists [1]) bvLogTy pred

/-- Pack `words : List Nat` into canonical little-endian 32-bit words inside the trusted boundary
so the solved bytes match `BVProg.wordsToBytesLE words` 1:1. Returns `none` if any word `≥ 2^32`. -/
private def packWordsU32LE (words : List Nat) : Option ByteArray :=
  go words (ByteArray.emptyWithCapacity (words.length * 4))
where
  go : List Nat → ByteArray → Option ByteArray
    | [], ba => some ba
    | w :: ws, ba =>
      if w < bvProgU32Bound then
        let u := w.toUInt32
        let b0 := u.toUInt8
        let b1 := (u >>> 8).toUInt8
        let b2 := (u >>> 16).toUInt8
        let b3 := (u >>> 24).toUInt8
        go ws ((((ba.push b0).push b1).push b2).push b3)
      else
        none

private def mkUnsatWitness (words : List Nat) : UnsatWitness :=
  {
    words := words
    addAxiom := fun axiomDeclRange? => do
      let wsExpr := mkNatListExpr words
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
      return auxAxiomName
  }

/-- Solve a `BVP1` 32-bit word stream in-process via verified `bv_solve_bytes`, with deterministic
`2x` workspace retry on `.workTooSmall` up to `min 512MiB maxWorkBytes`, returning `SolveOutcome`.
Zero axioms are emitted until `witness.addAxiom` is explicitly invoked. -/
def solveBVProgWithStats (words : List Nat)
    (initWorkBytes : UInt64 := defaultInitWorkBytes)
    (maxWorkBytes : UInt64 := defaultMaxWorkBytes)
    (fuel : UInt64 := defaultFuel) : IO SolveOutcome := do
  let some progBA := packWordsU32LE words
    | return { result := .unknown, workBytesUsed := 0, attempts := 0 }
  let clampedMax := min defaultMaxWorkBytes (max 1 maxWorkBytes)
  let clampedInit := min clampedMax (max 1 initWorkBytes)
  go progBA clampedMax 32 clampedInit 1
where
  go (progBA : ByteArray) (clampedMax : UInt64) :
      Nat → UInt64 → Nat → IO SolveOutcome
    | 0, curWork, attempts =>
      return { result := .workTooSmall, workBytesUsed := curWork.toNat, attempts := attempts }
    | steps + 1, curWork, attempts => do
      let work := allocWorkBuf curWork
      match solveBVBytesRaw progBA work fuel with
      | .unsat =>
        return {
          result := .unsat (mkUnsatWitness words)
          workBytesUsed := curWork.toNat
          attempts := attempts
        }
      | .sat model =>
        return {
          result := .sat model
          workBytesUsed := curWork.toNat
          attempts := attempts
        }
      | .unknown =>
        return {
          result := .unknown
          workBytesUsed := curWork.toNat
          attempts := attempts
        }
      | .workTooSmall =>
        if curWork < clampedMax then
          let nextWork :=
            if curWork > clampedMax / 2 then clampedMax else curWork * 2
          if nextWork <= curWork then
            return { result := .workTooSmall, workBytesUsed := curWork.toNat, attempts := attempts }
          else
            go progBA clampedMax steps nextWork (attempts + 1)
        else
          return { result := .workTooSmall, workBytesUsed := curWork.toNat, attempts := attempts }

/-- Solve a `BVP1` 32-bit word stream in-process via verified `bv_solve_bytes`. -/
def solveBVProg (words : List Nat)
    (initWorkBytes : UInt64 := defaultInitWorkBytes)
    (maxWorkBytes : UInt64 := defaultMaxWorkBytes)
    (fuel : UInt64 := defaultFuel) : IO VerifiedSolveResult := do
  return (← solveBVProgWithStats words initWorkBytes maxWorkBytes fuel).result

end BvDecideQbe
