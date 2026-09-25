module

public import Kraken.X64.Parser.Basic
public meta import Kraken.X64.Parser.Basic
public meta import Lean

namespace Kraken.X64.Parser

/-- A version of `parse` that runs at compile-time. -/
elab "parse(" s:str ")" : term => do
  match parse s.getString with
  | .ok p => return Lean.toExpr p
  | .error e => throwErrorAt s e

-- ============================================================================
-- File Parsing Elaborators
-- ============================================================================

open Lean Elab Term

/-- Read a file at elaboration time and return its contents as a string literal. -/
elab "fileAsString(" path:str ")" : term => do
  let pathStr := path.getString
  let contents ← IO.FS.readFile pathStr
  return mkStrLit contents

/-- Parse an assembly file, stripping directives first.
    Throws error on parse failure. -/
elab "parseFile(" path:str ")" : term => do
  let pathStr := path.getString
  let content ← IO.FS.readFile pathStr
  let stripped := stripDirectives content
  match parse stripped with
  | .ok p => return Lean.toExpr p
  | .error e => throwErrorAt path e

end Kraken.X64.Parser
