module

/-
Kraken Parser - Shared Assembly Syntax Infrastructure

Building blocks shared by the embedded assembly syntax categories (`Kraken.X64.Parser`,
`Kraken.AArch64.Parser`): the identifier token, together with the keyword-family commands of
`Kraken.SyntaxAffixed`.
-/

public import Lean
public meta import Lean
public import Kraken.SyntaxAffixed
public meta import Kraken.SyntaxAffixed

open Lean

namespace Kraken.Parser

-- ============================================================================
-- Assembly Identifier Token
-- ============================================================================

public meta section

open Lean.Parser in
/-- Assembly identifier (`[a-zA-Z_.][a-zA-Z0-9_.]*`), defined via Lean's character combinators. -/
def asmIdentToken : Parser := {
  fn := rawFn (satisfyFn (fun c => c.isAlpha || c == '_' || c == '.') "identifier" >>
               takeWhileFn (fun c => c.isAlphanum || c == '_' || c == '.'))
              (trailingWs := true)
}

@[combinator_formatter asmIdentToken]
def asmIdentToken.formatter : PrettyPrinter.Formatter := PrettyPrinter.Formatter.visitAtom Name.anonymous

@[combinator_parenthesizer asmIdentToken]
def asmIdentToken.parenthesizer : PrettyPrinter.Parenthesizer := PrettyPrinter.Parenthesizer.visitToken

end

end Kraken.Parser
