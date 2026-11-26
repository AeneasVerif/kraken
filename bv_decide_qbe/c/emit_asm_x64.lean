import LeanQbe.T.Examples.Kissat.FullM7FidelityAssembly
import LeanQbe.T.Examples.Kissat.FullM7InlPolicy
import LeanQbe.T.MainInline
import LeanQbe.T.Driver
import LeanQbe.T.Amd64.Isa
import LeanQbe.T.Amd64.PrintATTAlign

set_option autoImplicit false

-- 1-line swap target once Step-12 KissatFidelity / Bitblast/Build/Amd64/Cert lands:
private def solverFns : List LeanQbe.T.Fn :=
  (LeanQbe.T.Examples.Kissat.FullM7Fidelity.m7FidelityModule.optInlinePolicy
    LeanQbe.T.Examples.Kissat.FullM7InlPolicy.m7InlPolicy).fns

private def solverGlobals : List String := ["kissat_solve_bytes"]

def main (args : List String) : IO Unit := do
  let [outPath] := args | throw (IO.userError "usage: emit_asm_x64.lean <out.s>")
  let dirs ← match LeanQbe.T.Driver.compileFns
      LeanQbe.T.Amd64.x64Isa LeanQbe.T.Amd64.x64LegalTarget solverFns with
    | .ok d => pure d
    | .error e => throw (IO.userError e)
  let globls := String.join (solverGlobals.map fun s => s!".globl {s}\n")
  let asm := ".text\n" ++ globls ++ LeanQbe.T.Amd64.toATTAligned dirs ++
    "\n.section .note.GNU-stack,\"\",@progbits\n"
  IO.FS.writeFile outPath asm
