import LeanQbe.T.LeanLCNF.Lower1
import LeanQbe.T.LeanLCNF.Demo
import LeanQbe.T.LeanLCNF.Coverage
import LeanQbe.T.Driver
import LeanQbe.T.Amd64.Targ
import LeanQbe.T.Amd64.PrintATTAlign

/-! `emit_x64 <out.s> [cov_out.s]`: lower the spliced impure-LCNF demo and coverage programs
to `LeanQbe.T`, compile with `x64Target`, and print GNU assembler input. -/

set_option autoImplicit false

open LeanQbe.T LeanQbe.T.LeanLCNF LeanQbe.T.Amd64

private def emitOne (tag : String) (m : LcModule) (out : System.FilePath) : IO Unit := do
  let t0 ← IO.monoMsNow
  let tfs ← IO.ofExcept (lowerModule m)
  let fns := LeanLRC.tflatFnsToFns tfs
  let hints := fns.map (Fn.computeHints x64Target.toIsa x64LegalTarget)
  let dirs ← IO.ofExcept (LeanQbe.T.compile x64Target.toIsa x64LegalTarget fns hints)
  IO.FS.writeFile out (Driver.emitAsm (fun c => toATTAligned c ++ "\n") fns dirs)
  IO.eprintln s!"emit_x64 ({tag}): {fns.length} functions in {(← IO.monoMsNow) - t0} ms"

def main (args : List String) : IO Unit := do
  let out : System.FilePath := args.headD "lcnf_x64.s"
  emitOne "demo" Demo.lcnfProgram out
  match args with
  | _ :: covOut :: _ => emitOne "cov" Coverage.covProgram covOut
  | _ => pure ()
