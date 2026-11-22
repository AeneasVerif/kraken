import LeanQbe.T.Amd64.ChaCha
import LeanQbe.T.Amd64.PrintATTAlign

set_option autoImplicit false

open LeanQbe.T.Amd64.ChaCha

/-- Emit SysV x64 GNU assembly for `chacha20Block`. -/
def main (args : List String) : IO UInt32 := do
  let outDir := args.headD "/tmp/leanqbe-tchacha"
  let asm := ".text\n.globl chacha20Block\n" ++
    LeanQbe.T.Amd64.toATTAligned compiled.code ++ "\n"
  IO.FS.writeFile s!"{outDir}/chacha_x64.s" asm
  return 0
