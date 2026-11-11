module

public import LeanQbe.Driver
public import LeanQbe.Amd64.Targ
public import Kraken.X64.PrintATT

/-!
`leanqbe`: the command-line driver (`LeanQbe.Driver`) for x64. `leanqbe <program>` prints GNU
assembler input for one of the built-in programs (`LeanQbe.programs`), compiled with the fast
instruction selection `Amd64.fastIsa` and printed by Kraken's AT&T printer; `leanqbe --il <program>`
its QBE IL text (for stock QBE); `leanqbe --list` lists them.
-/

public def main : List String → IO UInt32 :=
  LeanQbe.Driver.main "leanqbe" LeanQbe.Amd64.fastIsa fun code => Kraken.X64.toATT code ++ "\n"
