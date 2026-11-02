module

/-
Kraken Parser - Shared Assembly Syntax Infrastructure

Building blocks shared by the embedded assembly syntax categories and their elaborators
(`Kraken.X64.Parser`, `Kraken.AArch64.Parser`): the identifier token, elaboration helpers and assembly
preprocessing, together with the keyword-family commands of `Kraken.SyntaxAffixed`.
-/

public import Lean
public meta import Lean
public import Kraken.ForLean
public meta import Kraken.ForLean
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

/-- Extract the raw assembly identifier string from an `asmIdentToken` syntax node. -/
def getAsmIdent (stx : Syntax) : Elab.TermElabM String := withRef stx do
  match stx with
  | .node _ _ #[.atom _ s] => pure s
  | _ => throwError "expected assembly identifier"

end

-- ============================================================================
-- Assembly Preprocessing
-- ============================================================================

/-- Replace line comments introduced by `marker` with Lean `--` comments, so that they are preserved
    as trivia in the parsed `Syntax`. -/
public def replaceLineComments (marker : String) (input : String) : String :=
  "\n".intercalate <| input.splitOn "\n" |>.map fun line =>
    match line.splitOn marker with
    | [] => ""
    | code :: rest => if rest.isEmpty then code else code ++ "--" ++ marker.intercalate rest

/-- Drop assembler directives (lines starting with `.`, other than labels such as `.LBB0_1:`), which
    Kraken does not model, so that compiler-generated `.S` files can be parsed as-is. -/
public def stripDirectives (content : String) : String :=
  "\n".intercalate <| content.splitOn "\n" |>.filter fun line =>
    let line := line.trimAsciiStart.toString
    !line.startsWith "." || line.any (· == ':')

end Kraken.Parser
