module

/-
Kraken ForLean - General-Purpose Lean Helpers

Definitions that are not specific to Kraken and could equally live in Lean itself.
-/

public import Lean
public meta import Lean

open Lean Meta

namespace Lean.Elab.Term

public meta section

/-- Parse `input` as the syntax category `cat` with `Lean.Parser.runParserCategory` and elaborate the
    resulting syntax tree with `elabStx`. -/
def elabCategory (cat : Name) (elabStx : TSyntax cat → TermElabM Expr) (input : String) : TermElabM Expr := do
  match Parser.runParserCategory (← getEnv) cat input with
  | .ok stx    => elabStx ⟨stx⟩
  | .error err => throwError err

end

public section

/-- Cache of imported environments keyed by module name, used by `evalElabString`. -/
private initialize importedEnvCache : IO.Ref (NameMap Environment) ← IO.mkRef {}

private unsafe def evalElabStringImpl (α : Type) (mod elabFnName : Name) (input : String) : Except String α :=
  match unsafeIO do
    let env ← match (← importedEnvCache.get).find? mod with
      | some env => pure env
      | none =>
        enableInitializersExecution
        if (← searchPathRef.get).isEmpty then
          initSearchPath (← findSysroot) [".lake/build/lib/lean", (← IO.appDir) / ".." / "lib" / "lean"]
        let env ← importModules #[{ module := mod }, { module := mod, isMeta := true }] {} (loadExts := true)
        importedEnvCache.modify (·.insert mod env)
        pure env
    let ctx : Core.Context := { fileName := "<input>", fileMap := default }
    let state : Core.State := { env }
    let go : TermElabM (Except String α) :=
      try
        withoutModifyingEnv do
          let elabFn ← evalConst (String → TermElabM Expr) elabFnName
          let value ← instantiateMVars (← elabFn input)
          if (← Core.getMessageLog).hasErrors then
            return .error ("\n".intercalate (← (← Core.getMessageLog).toList.mapM (·.toString)))
          if value.hasMVar then
            throwError "failed to evaluate expression, it contains metavariables{indentExpr value}"
          let type ← inferType value
          let name ← mkAuxDeclName `_eval
          let decl := Declaration.defnDecl {
            name, levelParams := [], type, value, hints := .opaque, safety := .unsafe
          }
          modifyEnv (markMeta · name)
          withOptions (Elab.async.set · false) do
            addAndCompile decl
            .ok <$> evalConst α name
      catch e =>
        .error <$> e.toMessageData.toString
    let (res, _, _) ← go.run'.toIO ctx state
    return res
  with
  | .ok res => res
  | .error e => .error (toString e)

/-- Run the string elaborator `elabFnName` (of type `String → TermElabM Expr`) in an environment
    importing `mod` (cached across calls) and evaluate the resulting closed expression into a value
    of type `α`. -/
@[implemented_by evalElabStringImpl]
opaque evalElabString (α : Type) (mod elabFnName : Name) (input : String) : Except String α

end

end Lean.Elab.Term

namespace Int64

public meta section

variable {m : Type → Type} [Monad m] [MonadError m]

/-- Convert a signed arbitrary-precision `Int` into `Int64`, enforcing 64-bit signed/unsigned range. -/
def ofIntNoOverflow (v : Int) : m Int64 := do
  unless Int64.minValue.toInt ≤ v && v < UInt64.size do throwError "integer {v} out of 64-bit range"
  pure (Int64.ofInt v)

/-- Convert an arbitrary-precision `Nat` into `Int64`, enforcing 64-bit signed/unsigned range. -/
def ofNatNoOverflow (v : Nat) : m Int64 := do
  unless v < UInt64.size do throwError "number {v} out of 64-bit range"
  pure (Int64.ofInt v)

end

end Int64
