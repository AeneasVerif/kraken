module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Kissat.Full
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.Full

/-!
# Stage 4 (`D-Full`) Kissat Native Certificate Slice 7/7 on AAPCS64 Arm64

Kernel-checked native compilation certificate (`cert7`) for slice `[147, 166)` (`19` functions) of
`LeanQbe.T.Examples.Kissat.Full.fullFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatFullCert7

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.Full

/-- Exported stack bounds for `[0, 147)` verified against `cert1..6` by `KissatFullCert`. -/
def slice6Bounds : List Nat :=
  [16, 16, 48, 64, 80, 128, 112, 176, 16, 16, 16, 16, 16, 16, 80, 176, 16, 32, 32, 64, 16, 48, 48,
   16, 64, 16, 16, 16, 32, 16, 160, 240, 16, 112, 16, 16, 16, 64, 16, 16, 80, 208, 144, 304, 352,
   16, 16, 384, 432, 448, 16, 16, 16, 80, 128, 16, 16, 112, 208, 288, 448, 544, 16, 80, 16, 128,
   288, 256, 16, 16, 128, 16, 96, 144, 160, 336, 432, 16, 272, 448, 80, 624, 672, 112, 128, 528,
   64, 16, 96, 208, 256, 80, 16, 176, 16, 16, 16, 16, 224, 16, 48, 16, 192, 800, 96, 880, 48, 368,
   400, 496, 800, 880, 336, 512, 336, 16, 96, 336, 528, 608, 32, 208, 512, 320, 336, 560, 512,
   480, 16, 272, 32, 16, 128, 16, 224, 336, 432, 560, 16, 144, 144, 16, 208, 352, 576, 256, 352]

/-- Exported callee signatures and stack bounds for prefix `[0, 147)`. -/
def ext6 : List (SigEntry × Nat) :=
  (fullFns.take 147).zipWith (fun f b => (⟨f.name, f.as, f.rs⟩, b)) slice6Bounds

/-- Slice 7 sub-module (`[147, 166)`, `19` functions). -/
def slice7Mod : Module := { fns := fullFns.drop 147 }

compile_linked_chunks! cert7 armTarget armLayout armLegalTarget armLabelClean
  slice7Mod 4 (ext := ext6) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatFullCert7
