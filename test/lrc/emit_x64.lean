import LeanQbe.T.LeanLRC.ToT
import LeanQbe.T.Driver
import LeanQbe.T.Amd64.Targ
import Kraken.X64.PrintATT

open LeanQbe.T LeanQbe.T.LeanLRC LeanQbe.T.Amd64

public def main (args : List String) : IO Unit := do
  let outPath : System.FilePath := match args with
    | p :: _ => p
    | [] => "/tmp/lrc_x64.s"
  let tfs ← match lowerLrcProgram allBenchLrcMod with
    | .ok x => pure x | .error e => throw (IO.userError e)
  let allFns := rtBase_fns ++ tflatFnsToFns tfs
  let hints := allFns.map (Fn.computeHints x64Target.toIsa x64LegalTarget)
  let dirs ← match LeanQbe.T.compile x64Target.toIsa x64LegalTarget allFns hints with
    | .ok d => pure d | .error e => throw (IO.userError e)
  let asm := Driver.emitAsm (fun c => Kraken.X64.toATT c ++ "\n") allFns dirs
  IO.FS.writeFile outPath asm
