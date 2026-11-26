/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public meta import Lean
public meta import LeanQbe.T.MainCertElab
public meta import LeanQbe.T.MainFlat
public meta import LeanQbe.T.MainCertFlatDecode

/-!
# First-Order Meta Chunk & Prefix-Bound Evaluators (`MainCertFlatElab`)

Separate meta leaf imported only by flat cert slices (`meta import LeanQbe.T.MainCertFlatElab`)
so `MainCertElab` and upstream `*Inl*` chunks never depend on `OptFlat*`/`RegaFlat`/`MainFlat`.
Bound by name from `MainCertElab` when `(flat := true)` is active.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

meta section

/-- Independent per-function flat meta prepass (`wfCheck → earlyOptFlat → supportsSource →
`midStageFlat → Spill.hints → TFlat.ext`), matching `compileModuleFlat`. -/
def evalOneFnStage1Flat (I : Isa) (lt : LegalTarget) (f : TFlatFn) :
    Except String (Sym × I.Hints × TFlatFn × Rega.Ext) :=
  if !f.wfCheck then .error s!"{f.name}: flat wfCheck failed"
  else
    let ef := earlyOptFlat f
    if !ef.supportsSource lt then .error s!"{f.name}: unsupported source op for target"
    else
      let mf := midStageFlat lt ef
      .ok (f.name, Spill.hints I mf.toFn, mf, TFlat.ext mf.body)

/-- Bound-only flat stage-1 prepass (drops `TFlatFn` body immediately). -/
def evalOneFnBoundStage1Flat (I : Isa) (lt : LegalTarget) (f : TFlatFn) :
    Except String (Sym × I.Hints × Rega.Ext × SigEntry) :=
  match evalOneFnStage1Flat I lt f with
  | .error e => .error e
  | .ok (nm, h, mf, ext) => .ok (nm, h, ext, mf.sig)

/-- Spawn flat stage-1 + `Rega.lowerFlatFn` across worker tasks and collect in source order. -/
def spawnLowerFlatItems {α β : Type _} (I : Isa) (lt : LegalTarget) (xs : List α)
    (getFn : α → TFlatFn)
    (mkOut : Sym → I.Hints → List I.Directive → TFlatFn → Rega.Ext → α → β) :
    Except String (List β) :=
  let tasks := xs.map fun x => Task.spawn fun () =>
    match evalOneFnStage1Flat I lt (getFn x) with
    | .error e => .error e
    | .ok (nm, h, mf, ext) =>
      match Rega.lowerFlatFn I h ext mf with
      | .ok c => .ok (mkOut nm h c mf ext x)
      | .error e => .error s!"{nm}: {e}"
  let rec collect : List (Task (Except String β)) → Except String (List β)
    | [] => .ok []
    | t :: ts => do let v ← t.get; .ok (v :: (← collect ts))
  collect tasks

/-- First-order meta chunk evaluator over decoded `List TFlatFn`, delegating chunk grouping and
pruned-`ext` table assembly to `evalLinkedChunksCore`. -/
def evalLinkedChunksFlat (I : Isa) (lt : LegalTarget) (raBytes : Nat)
    (ext0 : List (SigEntry × Nat)) (exits : List Sym) (nX : Nat)
    (fs : List TFlatFn) (chunkSize maxBound maxDirs : Nat)
    (pruneExt : Bool := false)
    [Lean.ToExpr (List I.Hints)] [Lean.ToExpr (List I.Directive)] :
    Except String EvalModuleData := do
  let lowered ← spawnLowerFlatItems I lt fs id fun nm h c mf ext _ => (nm, h, c, ext, mf.sig)
  evalLinkedChunksCore I raBytes ext0 exits nX chunkSize maxBound maxDirs pruneExt lowered

/-- Curried flat meta chunk evaluator bound by name from `MainCertElab`. -/
def makeChunkEvaluatorFlat (I : Isa) (lt : LegalTarget) (raBytes : Nat)
    (ext0 : List (SigEntry × Nat)) (exits : List Sym)
    (nX chunkSize maxBound maxDirs : Nat) (pruneExt : Bool := false)
    [Lean.ToExpr (List I.Hints)] [Lean.ToExpr (List I.Directive)] :
    List TFlatFn → Except String EvalModuleData :=
  fun fs =>
    evalLinkedChunksFlat I lt raBytes ext0 exits nX fs chunkSize maxBound maxDirs pruneExt

/-- Curried flat meta prefix-bound evaluator over decoded `List TFlatFn`. -/
def makePrefixExtEvaluatorFlat (I : Isa) (lt : LegalTarget) (raBytes : Nat)
    (ext0 : List (SigEntry × Nat)) (exits : List Sym) (nX maxBound : Nat)
    (pruneFor? : Option (List Fn) := none) :
    List TFlatFn → Except String (Nat × Lean.Expr) :=
  fun fs =>
    let tasks := fs.map fun f => Task.spawn fun () => evalOneFnBoundStage1Flat I lt f
    let pruneTasks? := pruneFor?.map fun targetFns =>
      targetFns.map fun f => Task.spawn fun () => evalOneFnBoundStage1 I lt f
    evalPrefixExtFromTasks I raBytes ext0 exits nX maxBound tasks pruneTasks?

/-- Curried flat meta prefix-bound evaluator when `fns` and `pruneFor` are `TFlatFn`-decoded. -/
def makePrefixExtPrunedEvaluatorFlat (I : Isa) (lt : LegalTarget) (raBytes : Nat)
    (ext0 : List (SigEntry × Nat)) (exits : List Sym) (nX maxBound : Nat) :
    List TFlatFn → List TFlatFn → Except String (Nat × Lean.Expr) :=
  fun fs pfs =>
    let tasks := fs.map fun f => Task.spawn fun () => evalOneFnBoundStage1Flat I lt f
    let pruneTasks := pfs.map fun f => Task.spawn fun () => evalOneFnBoundStage1Flat I lt f
    evalPrefixExtFromTasks I raBytes ext0 exits nX maxBound tasks (some pruneTasks)

end

end LeanQbe.T
