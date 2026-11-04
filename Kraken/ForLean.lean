module

/-
Kraken ForLean - General-Purpose Lean Helpers

Definitions that are not specific to Kraken and could equally live in Lean itself.
-/

public import Lean
public meta import Lean

open Lean

namespace Lean.Elab.Term

public meta section

/-- Parse `input` as the syntax category `cat` with `Lean.Parser.runParserCategory` and elaborate the
    resulting syntax tree with `elabStx`. -/
def elabCategory (cat : Name) (elabStx : TSyntax cat → TermElabM Expr) (input : String) : TermElabM Expr := do
  match Parser.runParserCategory (← getEnv) cat input with
  | .ok stx    => elabStx ⟨stx⟩
  | .error err => throwError err

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
