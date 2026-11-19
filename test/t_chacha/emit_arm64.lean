import LeanQbe.T.Arm64.ChaCha
import Kraken.AArch64.Print

open LeanQbe.T.Arm64.ChaCha

/-- Emit AAPCS64 GNU assembly for `chacha20Block`. -/
def main (args : List String) : IO UInt32 := do
  let outDir := args.headD "/tmp/leanqbe-tchacha"
  let asm :=
    ".text\n.globl chacha20Block\n.p2align 2\n" ++
      String.intercalate "\n" (compiled.code.map Kraken.AArch64.Print.directive) ++ "\n"
  IO.FS.writeFile s!"{outDir}/chacha_arm64.s" asm
  return 0
