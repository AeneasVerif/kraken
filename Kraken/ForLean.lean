module

/-
Kraken ForLean - General-Purpose Lean Helpers

Definitions that are not specific to Kraken and could equally live in Lean itself.
-/

public import Lean
public meta import Lean

open Lean Meta

namespace Lean.Elab.Term

public section

/-- Parse `input` as the syntax category `cat` with `Lean.Parser.runParserCategory` and elaborate the
    resulting syntax tree with `elabStx`. -/
def elabCategory (cat : Name) (elabStx : TSyntax cat → TermElabM Expr) (input : String) : TermElabM Expr := do
  match Parser.runParserCategory (← getEnv) cat input with
  | .ok stx    => elabStx ⟨stx⟩
  | .error err => throwError err

end

end Lean.Elab.Term

namespace Int64

public section

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

namespace Lean

initialize environmentForElabModuleExt : IO.Ref (NameMap Environment) ← IO.mkRef ∅

/--
  Construct a `Lean.Evironment` which has `elabModule` imported, running its initializers.

  This function is unsafe because it mimicks parts of the Lean frontend to build
  the relevant `Lean.Environment`. The unsafe operations are:
   · `enableInitializersExecution`.
   · `importModules mods` with `loadExts := true`.

  The purpose of `enableInitializersExecution` is to opt-in to the unsafe
  behaviour of `importModules (loadExts := true)`. Its only safety condition
  is that it must not be run concurrently (there is no mutex wrapping the
  reference it updates).

  As for `importModules mods`, using `loadExts := true` opts in to running initializer
  functions. Some safety conditions must be met to consider this safe:
   1. The file contents of `mods` correspond with those originally imported by the elaborator (and therefore can be executed).
   2. The resulting environment memory regions are not manually freed (we keep them globally).

  For the purposes of producing `Syntax` objects, it is crucial that initializers run,
  since parsing information is found in `Parser.parserExtension`, which is by default
  empty (`ParserExtension.mkInitial`), and is only populated by running the initializers
  of files defining extra `syntax`. A similar situation happens with elaborators and the
  `Lean.Elab.Term.termElabAttribute` extension.
-/
public unsafe def getEnvironmentForElabModule (elabModule : Name) : IO Environment := do
  match (← environmentForElabModuleExt.get).find? elabModule with
  | some env => pure env
  | none =>
      enableInitializersExecution
      initSearchPath (← findSysroot) [← getLibDir (← getBuildDir)]
      let env ← importModules #[{ module := elabModule }] {} (loadExts := true)
      environmentForElabModuleExt.modify (·.insert elabModule env)
      pure env

end Lean

public section

theorem List.mem_takeWhile {α : Type _} {p : α → Bool} {l : List α} {x : α}
    (hx : x ∈ l.takeWhile p) : p x = true := by
  induction l <;> grind [List.takeWhile_cons, List.takeWhile_nil]

theorem Int64.add_ofNat_inj {a : Int64} {m n : Nat} (hm : m < UInt64.size) (hn : n < UInt64.size)
    (h : a + .ofNat m = a + .ofNat n) : m = n := by
  have : (Int64.ofNat m).toBitVec = OfNat.ofNat m := Int64.toBitVec_ofNat'
  have : (Int64.ofNat n).toBitVec = OfNat.ofNat n := Int64.toBitVec_ofNat'
  grind

end
