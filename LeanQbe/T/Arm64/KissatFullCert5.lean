module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Kissat.Full
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.Full

/-!
# Stage 4 (`D-Full`) Kissat Native Certificate Slice 5/7 on AAPCS64 Arm64

Kernel-checked native compilation certificate (`cert5`) for slice `[111, 128)` (`17` functions) of
`LeanQbe.T.Examples.Kissat.Full.fullFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatFullCert5

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.Full

/-- Exported stack bounds for `[0, 111)` verified against `cert1..4` by `KissatFullCert`. -/
def slice4Bounds : List Nat :=
  [16, 16, 48, 64, 80, 128, 112, 176, 16, 16, 16, 16, 16, 16, 80, 176, 16, 32, 32, 64, 16, 48, 48,
   16, 64, 16, 16, 16, 32, 16, 160, 240, 16, 112, 16, 16, 16, 64, 16, 16, 80, 208, 144, 304, 352,
   16, 16, 384, 432, 448, 16, 16, 16, 80, 128, 16, 16, 112, 208, 288, 448, 544, 16, 80, 16, 128,
   288, 256, 16, 16, 128, 16, 80, 128, 160, 336, 432, 16, 272, 448, 80, 624, 672, 112, 128, 528,
   64, 16, 96, 208, 256, 80, 16, 176, 16, 16, 16, 16, 224, 16, 48, 16, 192, 800, 96, 880, 48, 368,
   400, 496, 800]

/-- Exported callee signatures and stack bounds for prefix `[0, 111)`. -/
def ext4 : List (SigEntry × Nat) :=
  (fullFns.take 111).zipWith (fun f b => (⟨f.name, f.as, f.rs⟩, b)) slice4Bounds

/-- Slice 5 sub-module (`[111, 128)`, `17` functions). -/
def slice5Mod : Module := { fns := (fullFns.drop 111).take 17 }

compile_linked_chunks! cert5 armTarget armLayout armLegalTarget armLabelClean
  slice5Mod 4 (ext := ext4) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatFullCert5
