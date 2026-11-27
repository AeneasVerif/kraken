import LeanQbeTest.T.BitblastCertCommon
import LeanQbe.T.Driver
import LeanQbe.T.Arm64.Isa
import Kraken.AArch64.Print

set_option autoImplicit false

private def solverFns : List LeanQbe.T.Fn :=
  LeanQbeTest.T.BitblastCertCommon.bitblastLinkedMod.fns

private def solverGlobals : List String := ["bv_solve_bytes"]

def main (args : List String) : IO Unit := do
  let [outPath] := args | throw (IO.userError "usage: emit_asm_arm64.lean <out.s>")
  let dirs ← match LeanQbe.T.Driver.compileFns
      LeanQbe.T.Arm64.armIsa LeanQbe.T.Arm64.armLegalTarget solverFns with
    | .ok d => pure d
    | .error e => throw (IO.userError e)
  let globls := String.join (solverGlobals.map fun s => s!".globl {s}\n")
  let body := ".p2align 2\n" ++
    String.intercalate "\n" (dirs.map Kraken.AArch64.Print.directive) ++ "\n"
  let asm := ".text\n" ++ globls ++ body ++ ".section .note.GNU-stack,\"\",@progbits\n"
  IO.FS.writeFile outPath asm
