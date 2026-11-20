import LeanQbe.T.LeanLCNF.Lower1
import LeanQbe.T.LeanLCNF.Demo
import LeanQbe.T.Driver
import LeanQbe.T.Amd64.Targ
import Kraken.X64.PrintATT

/-! `emit_x64 <out.s>`: lower the spliced impure-LCNF demo program (`Demo.lcnfProgram`) to
`LeanQbe.T`, compile it with `x64Target`, and print GNU assembler input. -/

open LeanQbe.T LeanQbe.T.LeanLCNF LeanQbe.T.Amd64

def main (args : List String) : IO Unit := do
  let out : System.FilePath := args.headD "lcnf_x64.s"
  let t0 ← IO.monoMsNow
  let tfs ← IO.ofExcept (lowerModule Demo.lcnfProgram)
  let fns := LeanLRC.tflatFnsToFns tfs
  let hints := fns.map (Fn.computeHints x64Target.toIsa x64LegalTarget)
  let dirs ← IO.ofExcept (LeanQbe.T.compile x64Target.toIsa x64LegalTarget fns hints)
  IO.FS.writeFile out (Driver.emitAsm (fun c => Kraken.X64.toATT c ++ "\n") fns dirs)
  IO.eprintln s!"emit_x64: {fns.length} functions in {(← IO.monoMsNow) - t0} ms"
