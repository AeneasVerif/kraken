module

public import LeanQbe.T.Driver
public import LeanQbe.T.Amd64.Isa
public import LeanQbe.T.Amd64.PrintATTAlign
public import Kraken.X64.PrintATT

/-!
`leanqbe`: the command-line driver (`LeanQbe.T.Driver`) for x64. `leanqbe <program>` prints GNU
assembler input for one of the built-in programs (`LeanQbe.T.programs`), compiled with
`LeanQbe.T.Amd64.x64Isa` and printed with backward-branch loop-header `.p2align 5,,12` alignment
(`--no-loop-align` disables loop alignment); `leanqbe --il <program>` prints QBE IL text (for
stock QBE); `leanqbe --list` lists them.
-/

set_option autoImplicit false

public def main (args : List String) : IO UInt32 :=
  let align := !args.contains "--no-loop-align"
  let rest := args.filter (· != "--no-loop-align")
  let printer := if align then LeanQbe.T.Amd64.toATTAligned else Kraken.X64.toATT
  LeanQbe.T.Driver.main "leanqbe" LeanQbe.T.Amd64.x64Isa LeanQbe.T.Amd64.x64LegalTarget
    (fun code => printer code ++ "\n") rest
