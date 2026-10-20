module

/-
Kraken ForLean - General-Purpose Lean Helpers

Definitions that are not specific to Kraken and could equally live in Lean itself.
-/

public import Lean
public meta import Lean

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
