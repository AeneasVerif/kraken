/-
Kraken - Effectful Parser Helpers

Provides `parse!`, a panicking wrapper around `Parser.parse`
for convenient use in `#eval` and `eval%` contexts.
-/

import Kraken.Parser

open Kraken.Parser

/-- Parse an assembly string, panicking on failure (for use in #eval). -/
def parse! (input : String) : Program :=
  match parse input with
  | .ok prog => prog
  | .error msg => panic! s!"parse error: {msg}"
