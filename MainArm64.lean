module

public import LeanQbe.Driver
public import LeanQbe.Arm64.Isel
public import Kraken.AArch64.Print

/-!
`leanqbe-arm64`: the command-line driver (`LeanQbe.Driver`) for AArch64, with the interface of
`leanqbe`. `leanqbe-arm64 <program>` prints GNU assembler input for one of the built-in programs
(`LeanQbe.programs`), compiled with `Arm64.isa` and printed by Kraken's AArch64 printer after a
`.p2align 2`; `leanqbe-arm64 --il <program>` its QBE IL text (for stock QBE); `leanqbe-arm64 --list`
lists them.
-/

public def main : List String → IO UInt32 :=
  LeanQbe.Driver.main "leanqbe-arm64" LeanQbe.Arm64.isa fun code =>
    ".p2align 2\n" ++ String.intercalate "\n" (code.map Kraken.AArch64.Print.directive) ++ "\n"
