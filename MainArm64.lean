module

public import LeanQbe.T.Driver
public import LeanQbe.T.Arm64.Isa
public import Kraken.AArch64.Print

/-!
`leanqbe-arm64`: the command-line driver (`LeanQbe.T.Driver`) for AArch64, with the interface of
`leanqbe`. `leanqbe-arm64 <program>` prints GNU assembler input for one of the built-in programs
(`LeanQbe.T.programs`), compiled with `LeanQbe.T.Arm64.armIsa` and printed by Kraken's
AArch64 printer after a `.p2align 2`; `leanqbe-arm64 --il <program>` its QBE IL text (for stock
QBE); `leanqbe-arm64 --list` lists them.
-/

set_option autoImplicit false

public def main : List String → IO UInt32 :=
  LeanQbe.T.Driver.main "leanqbe-arm64" LeanQbe.T.Arm64.armIsa
    LeanQbe.T.Arm64.armLegalTarget fun code =>
      ".p2align 2\n" ++ String.intercalate "\n" (code.map Kraken.AArch64.Print.directive) ++ "\n"
