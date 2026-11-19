import LeanQbe.T.Amd64.Bignum
import Kraken.X64.PrintATT

open LeanQbe.T.Amd64.Bignum

private def emitFn (name body : String) : String :=
  ".text\n.globl " ++ name ++ "\n" ++ body ++ "\n"

/-- Emit SysV x64 GNU assembly files for `mul4x4`, `addMod25519`, and `subMod25519`. -/
def main (args : List String) : IO UInt32 := do
  let outDir := args.headD "/tmp/leanqbe-tbignum"
  IO.FS.writeFile s!"{outDir}/mul4x4_x64.s"
    (emitFn "mul4x4" (Kraken.X64.toATT mul4x4Compiled.code))
  IO.FS.writeFile s!"{outDir}/addMod25519_x64.s"
    (emitFn "addMod25519" (Kraken.X64.toATT addMod25519Compiled.code))
  IO.FS.writeFile s!"{outDir}/subMod25519_x64.s"
    (emitFn "subMod25519" (Kraken.X64.toATT subMod25519Compiled.code))
  return 0
