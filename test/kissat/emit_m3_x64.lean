import LeanQbe.T.Examples.Kissat.FullM3
import LeanQbe.T.PrintCpp
import LeanQbe.T.Driver
import LeanQbe.T.Amd64.Targ
import Kraken.X64.PrintATT

set_option autoImplicit false

open LeanQbe.T LeanQbe.T.PrintCpp LeanQbe.T.Examples.Kissat.FullM3 LeanQbe.T.Amd64

public def main (args : List String) : IO Unit := do
  let (outPath, cppPath?) : System.FilePath × Option System.FilePath := match args with
    | p :: c :: _ => (p, some c)
    | [p] => (p, none)
    | [] => ("/tmp/kissat_m3_x64.s", none)
  let fns := m3Module.fns
  let hints := fns.map (Fn.computeHints x64Target.toIsa x64LegalTarget)
  let dirs ← match LeanQbe.T.compile x64Target.toIsa x64LegalTarget fns hints with
    | .ok d => pure d
    | .error e => throw (IO.userError e)
  let asm := Driver.emitAsm (fun c => Kraken.X64.toATT c ++ "\n") fns dirs
  IO.FS.writeFile outPath asm
  if let some cppPath := cppPath? then
    let cpp ← match ppTModule m3Module with
      | .ok s => pure s
      | .error e => throw (IO.userError e)
    IO.FS.writeFile cppPath cpp
