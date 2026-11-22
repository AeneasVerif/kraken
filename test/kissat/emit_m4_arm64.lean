import LeanQbe.T.Examples.Kissat.FullM4
import LeanQbe.T.Opt
import LeanQbe.T.Driver
import LeanQbe.T.Arm64.Targ
import Kraken.AArch64.Print

set_option autoImplicit false

open LeanQbe.T LeanQbe.T.Examples.Kissat.FullM4 LeanQbe.T.Arm64

public def main (args : List String) : IO Unit := do
  let outPath : System.FilePath := match args with
    | p :: _ => p
    | [] => "/tmp/kissat_m4_arm64.s"
  let fns := (m4Module.optInline 40).fns
  let hints := fns.map (Fn.computeHints armTarget.toIsa armLegalTarget)
  let dirs ← match LeanQbe.T.compile armTarget.toIsa armLegalTarget fns hints with
    | .ok d => pure d
    | .error e => throw (IO.userError e)
  let pp := fun c =>
    ".p2align 2\n" ++ String.intercalate "\n" (c.map Kraken.AArch64.Print.directive)
  IO.FS.writeFile outPath (Driver.emitAsm (fun c => pp c ++ "\n") fns dirs)
