/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Main
public import LeanQbe.T.Inline

/-!
# Pure Per-Function Bounds JSON Dumper (`KissatBoundsDumpCommon`)

Runs the exact `evalOneFnBoundStage1` + `checkAndBoundExt` pipeline once in compiled `IO`
(parallel stage-1 `earlyOpt → supportsSource → midFromEarly → Spill.hints → ext`, sequential
callee-first `checkAndBoundExt ≤ maxBound`) and serializes per-function
`{"name", "as", "rs", "bound", "callees"}` JSON rows for `scripts/gen_cert_slices.py --bounds-json`.

Imports ZERO `*Lemmas*`, ZERO `*Proof*`, ZERO `Lean` meta, and ZERO architecture crates.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.BoundsDump

open LeanQbe.T

/-- Configuration for a single-pass module bounds JSON dump. -/
structure DumpConfig where
  label : String
  maxBound : Nat := 2048
  extCallees : List (SigEntry × Nat) := []
  exits : List Sym := []
  nX : Nat := 0
  workers : Nat := 8
  outEnvVar : String := "LEANQBE_BOUNDS_JSON_OUT"

/-- Per-function bound and direct-callee record matching `gen_cert_slices.py --bounds-json`. -/
structure FnBoundRow where
  name : Sym
  as : List Ty
  rs : List Ty
  bound : Nat
  callees : List Sym

private structure Stage1Out (I : Isa) where
  name : Sym
  sig : SigEntry
  hints : I.Hints
  ext : Rega.Ext

private def matFn (f : Fn) : Fn :=
  ⟨f.name, f.as, f.rs, denoteFunc (reifyFunc f.body)⟩

private def optInlinePolicyPure (M : Module) (policy : InlinePolicy) : Module :=
  let M' := M.inlinePolicy policy
  { M' with fns := M'.fns.map Fn.renorm }

private def stage1OneFn (I : Isa) (lt : LegalTarget) (f : Fn) :
    Except String (Stage1Out I) := do
  let ef := matFn f.earlyOpt
  if !ef.body.supportsSource lt then
    throw s!"{f.name}: unsupported source op for target after earlyOpt"
  let mf := Fn.midFromEarly lt ef
  pure { name := f.name, sig := mf.sig, hints := Spill.hints I mf, ext := mf.ext }

private def chunkList.{u} {α : Type u} (n : Nat) (xs : List α) : List (List α) :=
  let k := max 1 ((xs.length + n - 1) / max 1 n)
  let rec go (hk : 0 < k) : List α → List (List α)
    | [] => []
    | y :: rest =>
      let ys := y :: rest
      ys.take k :: go hk (ys.drop k)
  termination_by ys => ys.length
  decreasing_by
    simp only [List.length_drop, List.length_cons]
    omega
  go (Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 _)) xs

/-- Format a `Ty` token accepted by `scripts/gen_cert_slices.py`'s `_format_lean_ty`. -/
def formatTy : Ty → String
  | .bool => "bool"
  | .bits 8 => "i8"
  | .bits 16 => "i16"
  | .bits 32 => "i32"
  | .bits 64 => "i64"
  | .bits n => s!"(.bits {n})"
  | .float .h => "f16"
  | .float .s => "f32"
  | .float .d => "f64"
  | .float .q => "f128"
  | .pair a b => s!"(.pair {formatTy a} {formatTy b})"

private def escapeJsonString (s : String) : String :=
  s.foldl (fun acc c =>
    match c with
    | '"' => acc ++ "\\\""
    | '\\' => acc ++ "\\\\"
    | '\n' => acc ++ "\\n"
    | '\r' => acc ++ "\\r"
    | '\t' => acc ++ "\\t"
    | _ => acc.push c) ""

private def quoteJson (s : String) : String :=
  "\"" ++ escapeJsonString s ++ "\""

private def formatJsonStringList (xs : List String) : String :=
  "[" ++ String.intercalate ", " (xs.map quoteJson) ++ "]"

/-- Format one `FnBoundRow` as a single deterministic JSON object line. -/
def formatRowJson (r : FnBoundRow) : String :=
  let asJson := formatJsonStringList (r.as.map formatTy)
  let rsJson := formatJsonStringList (r.rs.map formatTy)
  let csJson := formatJsonStringList r.callees
  s!"\{\"name\": {quoteJson r.name}, \"as\": {asJson}, \"rs\": {rsJson}, " ++
    s!"\"bound\": {r.bound}, \"callees\": {csJson}}"

/-- Format a module's ordered `FnBoundRow` list as deterministic JSON text. -/
def formatRowsJson (rows : List FnBoundRow) : String :=
  if rows.isEmpty then "[]\n"
  else
    let body := String.intercalate ",\n" (rows.map fun r => "  " ++ formatRowJson r)
    "[\n" ++ body ++ "\n]\n"

/-- Compute per-function legalized signatures, stack bounds, and direct callees in one pass. -/
def computeModuleBounds (I : Isa) (lt : LegalTarget) (M : Module)
    (policy? : Option InlinePolicy) (cfg : DumpConfig) : IO (List FnBoundRow) := do
  let fns := match policy? with
    | some p => (optInlinePolicyPure M p).fns
    | none => M.fns
  let batches := chunkList cfg.workers fns
  let tasks := batches.map fun batch =>
    Task.spawn fun () => batch.mapM (stage1OneFn I lt)
  let mut outs : List (Stage1Out I) := []
  for t in tasks do
    match t.get with
    | .error err => throw <| IO.userError s!"[{cfg.label}] {err}"
    | .ok chunkOuts => outs := outs ++ chunkOuts
  let mut acc : List (SigEntry × Nat) := cfg.extCallees
  let mut rowsRev : List FnBoundRow := []
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
      rowsRev :=
        { name := o.name
          as := o.sig.2.1
          rs := o.sig.2.2
          bound := b
          callees := o.ext.callees.map Prod.fst } :: rowsRev
  pure rowsRev.reverse

/-- Compute bounds for `M`, verify row count, and write JSON if `cfg.outEnvVar` is set. -/
def runModuleBoundsDump (I : Isa) (lt : LegalTarget) (M : Module)
    (policy? : Option InlinePolicy) (cfg : DumpConfig) : IO Unit := do
  let rows ← computeModuleBounds I lt M policy? cfg
  if rows.length != M.fns.length then
    throw <| IO.userError
      s!"[{cfg.label}] row count mismatch: got {rows.length}, expected {M.fns.length}"
  let json := formatRowsJson rows
  match ← IO.getEnv cfg.outEnvVar with
  | some outPath =>
    if !outPath.isEmpty then
      let p : System.FilePath := outPath
      if let some dir := p.parent then
        if !dir.toString.isEmpty then
          IO.FS.createDirAll dir
      IO.FS.writeFile p json
  | none => pure ()

end LeanQbeTest.T.BoundsDump
