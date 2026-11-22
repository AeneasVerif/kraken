module

public import LeanQbe.T.Driver
public import LeanQbe.T.Amd64.Isa
public import Kraken.X64.PrintATT

/-!
`leanqbe`: the command-line driver (`LeanQbe.T.Driver`) for x64. `leanqbe <program>` prints GNU
assembler input for one of the built-in programs (`LeanQbe.T.programs`), compiled with
`LeanQbe.T.Amd64.x64Isa` and printed by Kraken's AT&T printer; `leanqbe --il <program>`
its QBE IL text (for stock QBE); `leanqbe --list` lists them.
-/

set_option autoImplicit false

public def main : List String → IO UInt32 :=
  LeanQbe.T.Driver.main "leanqbe" LeanQbe.T.Amd64.x64Isa LeanQbe.T.Amd64.x64LegalTarget
    fun code => Kraken.X64.toATT code ++ "\n"
