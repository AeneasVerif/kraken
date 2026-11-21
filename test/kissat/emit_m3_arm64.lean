import LeanQbe.T.Examples.Kissat.FullM3
import LeanQbe.T.Driver
import LeanQbe.T.Arm64.Targ
import Kraken.AArch64.Print

open LeanQbe.T LeanQbe.T.Examples.Kissat.FullM3 LeanQbe.T.Arm64

public def main (args : List String) : IO Unit := do
  let outPath : System.FilePath := match args with
    | p :: _ => p
    | [] => "/tmp/kissat_m3_arm64.s"
  let hints := m3Fns.map (Fn.computeHints armTarget.toIsa armLegalTarget)
  let dirs ← match LeanQbe.T.compile armTarget.toIsa armLegalTarget m3Fns hints with
    | .ok d => pure d
    | .error e => throw (IO.userError e)
  let pp := fun c =>
    ".p2align 2\n" ++ String.intercalate "\n" (c.map Kraken.AArch64.Print.directive)
  IO.FS.writeFile outPath (Driver.emitAsm (fun c => pp c ++ "\n") m3Fns dirs)
