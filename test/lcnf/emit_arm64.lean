import LeanQbe.T.LeanLCNF.Lower1
import LeanQbe.T.LeanLCNF.Demo
import LeanQbe.T.Driver
import LeanQbe.T.Arm64.Targ
import Kraken.AArch64.Print

/-! `emit_arm64 <out.s>`: lower the spliced impure-LCNF demo program (`Demo.lcnfProgram`) to
`LeanQbe.T`, compile it with `armTarget`, and print GNU assembler input. -/

open LeanQbe.T LeanQbe.T.LeanLCNF LeanQbe.T.Arm64

def main (args : List String) : IO Unit := do
  let out : System.FilePath := args.headD "lcnf_arm64.s"
  let t0 ← IO.monoMsNow
  let tfs ← IO.ofExcept (lowerModule Demo.lcnfProgram)
  let fns := LeanLRC.tflatFnsToFns tfs
  let hints := fns.map (Fn.computeHints armTarget.toIsa armLegalTarget)
  let dirs ← IO.ofExcept (LeanQbe.T.compile armTarget.toIsa armLegalTarget fns hints)
  let pp := fun c =>
    ".p2align 2\n" ++ String.intercalate "\n" (c.map Kraken.AArch64.Print.directive)
  IO.FS.writeFile out (Driver.emitAsm (fun c => pp c ++ "\n") fns dirs)
  IO.eprintln s!"emit_arm64: {fns.length} functions in {(← IO.monoMsNow) - t0} ms"
