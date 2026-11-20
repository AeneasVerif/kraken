import LeanQbe.T.Examples.Kissat.Plain
import LeanQbe.T.Driver
import LeanQbe.T.Amd64.Targ
import Kraken.X64.PrintATT

open LeanQbe.T LeanQbe.T.Examples.Kissat.Plain LeanQbe.T.Amd64

public def main (args : List String) : IO Unit := do
  let outPath : System.FilePath := match args with
    | p :: _ => p
    | [] => "/tmp/plain_x64.s"
  let hints := plainFns.map (Fn.computeHints x64Target.toIsa x64LegalTarget)
  let dirs ← match LeanQbe.T.compile x64Target.toIsa x64LegalTarget plainFns hints with
    | .ok d => pure d
    | .error e => throw (IO.userError e)
  let asm := Driver.emitAsm (fun c => Kraken.X64.toATT c ++ "\n") plainFns dirs
  IO.FS.writeFile outPath asm
