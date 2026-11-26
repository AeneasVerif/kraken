module

public import LeanQbe.T.Driver
public import LeanQbe.T.Arm64.Isa
public import LeanQbe.T.Arm64.PrintAlign

/-!
`leanqbe-arm64`: the command-line driver (`LeanQbe.T.Driver`) for AArch64, with the interface of
`leanqbe`. `leanqbe-arm64 <program>` prints GNU assembler input for one of the built-in programs
(`LeanQbe.T.programs`), compiled with `LeanQbe.T.Arm64.armIsa` and printed with backward-branch
loop-header `.p2align 4` alignment (`--no-loop-align` disables loop alignment) after a
`.p2align 2`; `leanqbe-arm64 --il <program>` its QBE IL text (for stock QBE);
`leanqbe-arm64 --list` lists them.
-/

set_option autoImplicit false

public def main (args : List String) : IO UInt32 :=
  let align := !args.contains "--no-loop-align"
  let rest := args.filter (· != "--no-loop-align")
  let printer := if align then LeanQbe.T.Arm64.toAsmAligned else LeanQbe.T.Arm64.toAsm
  LeanQbe.T.Driver.main "leanqbe-arm64" LeanQbe.T.Arm64.armIsa
    LeanQbe.T.Arm64.armLegalTarget (fun code => ".p2align 2\n" ++ printer code ++ "\n") rest
