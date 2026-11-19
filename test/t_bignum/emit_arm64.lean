import LeanQbe.T.Arm64.Bignum
import Kraken.AArch64.Print

open LeanQbe.T.Arm64.Bignum

private def emitFn (name : String) (lines : List String) : String :=
  ".text\n.globl " ++ name ++ "\n.p2align 2\n" ++ String.intercalate "\n" lines ++ "\n"

/-- Emit AAPCS64 GNU assembly files for `mul4x4`, `addMod25519`, and `subMod25519`. -/
def main (args : List String) : IO UInt32 := do
  let outDir := args.headD "/tmp/leanqbe-tbignum"
  IO.FS.writeFile s!"{outDir}/mul4x4_arm64.s"
    (emitFn "mul4x4" (mul4x4Compiled.code.map Kraken.AArch64.Print.directive))
  IO.FS.writeFile s!"{outDir}/addMod25519_arm64.s"
    (emitFn "addMod25519" (addMod25519Compiled.code.map Kraken.AArch64.Print.directive))
  IO.FS.writeFile s!"{outDir}/subMod25519_arm64.s"
    (emitFn "subMod25519" (subMod25519Compiled.code.map Kraken.AArch64.Print.directive))
  return 0
