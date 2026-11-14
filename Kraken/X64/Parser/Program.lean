module

public import Kraken.X64.Parser.Delab
public meta import Kraken.X64.Parser.Delab
public meta import Lean

/-!
Programs: a sequence of directives, each ended by a line break or a `;`. Written with `syntax`
(issue 4 of `Kraken/X64/Parser/design.md`). A program elaborates to a list literal of its
directives and prints as one (issue 7).
-/

open Lean Elab Term Kraken.Parser

public meta section

/-- A directive ended by a line break (nothing but a new directive may follow on its line) or by
a `;`. -/
syntax x64_line := withPosition(x64_directive notFollowedBy(lineEq ("," <|> x64_operand64))) (";")?

/-- X64 assembly program (sequence of directives). -/
declare_syntax_cat x64_prog
syntax ppDedent((ppLine x64_line)*) : x64_prog

/-- Inline unquoted X64 assembly block (`⸨prog| ...⸩`). -/
syntax "⸨prog|" x64_prog "⸩" : term

macro_rules
  | `(⸨prog| $[$ds $[;]?]* ⸩) => do
    let ds ← ds.mapM fun d => `(⸨dir| $d ⸩)
    `(([$ds,*] : List _root_.Directive))

namespace Kraken.X64.Parser

/-- Parse and elaborate an X64 assembly string (with `# ...` line comments) into a `Lean.Expr`
representing a Kraken `Program`. -/
public def elabX64 (s : String) : TermElabM Expr :=
  elabCategory `x64_prog (fun p => do elabTerm (← `(⸨prog| $p ⸩)) none) (replaceLineComments "#" s)

/-- Read an X64 assembly file, strip assembler directives, parse via `runParserCategory`,
and elaborate into a Kraken `Program`. -/
elab "include_x64" path:str : term => do
  let content ← IO.FS.readFile path.getString
  withRef path <| elabX64 (stripDirectives content)

end Kraken.X64.Parser

/-- Embedding of sized directives -/
syntax "⸨dir " term "| " x64_directive " ⸩" : term

macro_rules
  | `(⸨dir $n | $dir:x64_directive ⸩) =>
    `({directive := ⸨dir| $dir ⸩, size := Kraken.Layout.size _root_.Instr _root_.ConstExpr $n : Kraken.Sized _root_.Directive})

end
