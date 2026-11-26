module

public import LeanQbe.T.Main
public import LeanQbe.T.Inline

/-!
# Fail-Closed Pure Compilation Preflight Guard (`CompileGuard`)

Runs the exact pure compilation and certifiability pipeline (`checkAcyclic`,
`checkLegalSigAll`, `fnNameOk`, `stringsNodup`, `inlinePolicy` + `Fn.renorm`,
`Task.spawn`-parallelized `earlyOpt` -> `supportsSource` -> `Fn.midFromEarly` ->
`Spill.hints` -> `Rega.lowerFn`, sequential `checkAndBoundExt` <= `maxBound`,
and `progSmall`) in compiled `IO` for leaf `#eval` check modules.
Imports ZERO `*Lemmas*`, ZERO `Lean` meta, and ZERO architecture crates.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.CompileGuard

open LeanQbe.T

/-- Configuration for a fail-closed module certifiability preflight guard. -/
structure GuardConfig where
  label : String
  maxBound : Nat := 2048
  entryFn? : Option Sym := some "kissat_solve_bytes"
  maxInlFnSize? : Option Nat := none
  extCallees : List (SigEntry × Nat) := []
  exits : List Sym := []
  nX : Nat := 0
  workers : Nat := 8

/-- Per-function compilation artifact produced in parallel before sequential linking. -/
private structure FnCheckOut (I : Isa) where
  name : Sym
  sig : SigEntry
  hints : I.Hints
  ext : Rega.Ext
  dirBytes : Nat
  inlSize : Nat

/-- Mirror of `MainCertCore.checkLegalSigAll` without importing `MainCertCore`. -/
def checkLegalSigAllPure (lt : LegalTarget) (fs : List Fn) : Option (List Sym) :=
  let bad := fs.filterMap fun f =>
    if (lt.legalSig f.as == f.as) && (lt.legalSig f.rs == f.rs) then none else some f.name
  if bad.isEmpty then none else some bad

/-- Mirror of `Module.optInlinePolicy` (`MainInline.lean`) without importing `MainLemmas`. -/
def optInlinePolicyPure (M : Module) (policy : InlinePolicy) : Module :=
  let M' := M.inlinePolicy policy
  { M' with fns := M'.fns.map Fn.renorm }

private def checkOneFn (I : Isa) (lt : LegalTarget) (dirSize : I.Directive → Nat)
    (maxInlFnSize? : Option Nat) (f : Fn) : Except String (FnCheckOut I) := do
  let sz := f.size
  if let some cap := maxInlFnSize? then
    if sz > cap then
      throw s!"{f.name}: post-inline IR size {sz} exceeds budget {cap}"
  let ef := f.earlyOpt
  if !ef.body.supportsSource lt then
    throw s!"{f.name}: unsupported source op for target after earlyOpt"
  let mf := Fn.midFromEarly lt ef
  let ext := mf.ext
  let h := Spill.hints I mf
  match Rega.lowerFn I h ext mf with
  | .error e => throw s!"{f.name}: Rega.lowerFn failed: {e}"
  | .ok dirs =>
    let dirBytes := dirs.foldl (fun acc d => acc + dirSize d) 0
    pure { name := f.name, sig := mf.sig, hints := h, ext := ext,
           dirBytes := dirBytes, inlSize := sz }

private def chunkList.{u} {α : Type u} (n : Nat) (xs : List α) : List (List α) :=
  let k := max 1 ((xs.length + n - 1) / max 1 n)
  let rec go (hk : 0 < k) : List α → List (List α)
    | [] => []
    | y :: rest =>
      let ys := y :: rest
      let hd := ys.take k
      let tl := ys.drop k
      hd :: go hk tl
  termination_by ys => ys.length
  decreasing_by
    simp only [List.length_drop, List.length_cons]
    omega
  go (Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 _)) xs

/-- Run full certifiability preflight on `M` under `policy`, `I`, and `lt`.
Silent (`pure ()`) on pass; throws `IO.userError` naming the exact failing function on failure. -/
def runModuleGuard (I : Isa) (lt : LegalTarget) (dirSize : I.Directive → Nat)
    (M : Module) (policy : InlinePolicy) (cfg : GuardConfig) : IO Unit := do
  -- 1. Acyclicity & symbol/label hygiene (mirrors ModuleOk + checkCompileResult)
  if !M.checkAcyclic then
    throw <| IO.userError s!"[{cfg.label}] Module.checkAcyclic failed"
  if let some bad := checkLegalSigAllPure lt M.fns then
    throw <| IO.userError s!"[{cfg.label}] checkLegalSigAll failed on: {bad.take 10}"
  let fnNames := M.fns.map Fn.name
  let badNames := (fnNames ++ cfg.exits).filter (fun s => !fnNameOk s)
  if !badNames.isEmpty then
    throw <| IO.userError s!"[{cfg.label}] fnNameOk failed (contains '.L'): {badNames.take 10}"
  if !stringsNodup (fnNames ++ cfg.exits) then
    throw <| IO.userError s!"[{cfg.label}] duplicate symbol in fnNames ++ exits"

  -- 2. Inlining + renormalization (exact definition of Module.optInlinePolicy)
  let mInl := optInlinePolicyPure M policy
  if mInl.fns.map Fn.name != fnNames then
    throw <| IO.userError s!"[{cfg.label}] optInlinePolicy changed function name list"

  -- 3. Parallel per-function earlyOpt + supportsSource + midFromEarly + Spill.hints + Rega.lowerFn
  let batches := chunkList cfg.workers mInl.fns
  let tasks := batches.map fun batch =>
    Task.spawn fun () => batch.mapM (checkOneFn I lt dirSize cfg.maxInlFnSize?)
  let mut outs : List (FnCheckOut I) := []
  for t in tasks do
    match t.get with
    | .error err => throw <| IO.userError s!"[{cfg.label}] {err}"
    | .ok chunkOuts => outs := outs ++ chunkOuts

  -- 4. Sequential callee-first stack bound checking + maxBound + progSmall
  let mut acc : List (SigEntry × Nat) := cfg.extCallees
  let mut totalBytes : Nat :=
    cfg.exits.foldl (fun sum g => sum + dirSize (I.frame.label g)) 0
  let mut seenEntry : Bool := false
  for o in outs do
    match checkAndBoundExt I I.frame.raBytes cfg.exits cfg.nX acc o.hints o.ext with
    | none =>
      throw <| IO.userError
        s!"[{cfg.label}] {o.name}: checkAndBoundExt failed (callee/exit/stack overflow)"
    | some b =>
      if b > cfg.maxBound then
        throw <| IO.userError
          s!"[{cfg.label}] {o.name}: stack bound {b} exceeds maxBound {cfg.maxBound}"
      acc := (o.sig, b) :: acc
      totalBytes := totalBytes + o.dirBytes
      if cfg.entryFn? == some o.name then
        seenEntry := true

  if totalBytes ≥ 2 ^ 64 then
    throw <| IO.userError s!"[{cfg.label}] progSmall failed: code size {totalBytes} >= 2^64"
  if let some entry := cfg.entryFn? then
    if !seenEntry then
      throw <| IO.userError s!"[{cfg.label}] entry function '{entry}' not found in module"

end LeanQbe.T.CompileGuard
