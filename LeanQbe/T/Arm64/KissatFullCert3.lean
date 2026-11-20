module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Kissat.Full
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.Full

/-!
# Stage 4 (`D-Full`) Kissat Native Certificate Slice 3/7 on AAPCS64 Arm64

Kernel-checked native compilation certificate (`cert3`) for slice `[67, 88)` (`21` functions) of
`LeanQbe.T.Examples.Kissat.Full.fullFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatFullCert3

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.Full

/-- Exported stack bounds for `[0, 67)` verified against `cert1..2` by `KissatFullCert`. -/
def slice2Bounds : List Nat :=
  [16, 16, 48, 64, 80, 128, 112, 176, 16, 16, 16, 16, 16, 16, 80, 176, 16, 32, 32, 64, 16, 48, 48,
   16, 64, 16, 16, 16, 32, 16, 160, 240, 16, 112, 16, 16, 16, 64, 16, 16, 80, 208, 144, 304, 352,
   16, 16, 384, 432, 448, 16, 16, 16, 80, 128, 16, 16, 112, 208, 288, 448, 544, 16, 80, 16, 128,
   288]

/-- Exported callee signatures and stack bounds for prefix `[0, 67)`. -/
def ext2 : List (SigEntry × Nat) :=
  (fullFns.take 67).zipWith (fun f b => (⟨f.name, f.as, f.rs⟩, b)) slice2Bounds

/-- Slice 3 sub-module (`[67, 88)`, `21` functions). -/
def slice3Mod : Module := { fns := (fullFns.drop 67).take 21 }

compile_linked_chunks! cert3 armTarget armLayout armLegalTarget armLabelClean
  slice3Mod 4 (ext := ext2) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatFullCert3
