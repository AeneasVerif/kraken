/-
Kraken - x86_64 Assembly Parser

Re-exports the parsing infrastructure for x86_64 AT&T syntax assembly.

Usage:
```lean
import Parsing
open Parsing

-- Parse a function from assembly text
def result := parseFunction asmText "bn_mul_mont_nohw"

-- With custom config (e.g., error on unsupported instructions)
def result := parseFunction asmText "bn_mul_mont_nohw" { skipUnsupported := false }
```
-/

import Parsing.Config
import Parsing.Parser
