module

public import Kraken.AArch64.Parser.Basic
public meta import Kraken.AArch64.Parser.Basic
public meta import Lean

namespace Kraken.AArch64.Parser

/-- A version of `parse` that runs at compile-time. -/
scoped elab "parse(" s:str ")" : term => do
  match parse s.getString with
  | .ok p => return Lean.toExpr p
  | .error e => throwErrorAt s e

elab "parseAArch64(" s:str ")" : term => do
  match parse s.getString with
  | .ok p => return Lean.toExpr p
  | .error e => throwErrorAt s e

-- ============================================================================
-- File Parsing Elaborators
-- ============================================================================

open Lean Elab Term

/-- Read a file at elaboration time and return its contents as a string literal. -/
elab "fileAsStringAArch64(" path:str ")" : term => do
  let pathStr := path.getString
  let contents ← IO.FS.readFile pathStr
  return mkStrLit contents

/-- Parse an AArch64 assembly file, stripping directives first.
    Throws error on parse failure. -/
elab "parseFileAArch64(" path:str ")" : term => do
  let pathStr := path.getString
  let content ← IO.FS.readFile pathStr
  let stripped := stripDirectives content
  match parse stripped with
  | .ok p => return Lean.toExpr p
  | .error e => throwErrorAt path e

end Kraken.AArch64.Parser
