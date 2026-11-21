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
  [16, 16, 48, 64, 80, 112, 112, 160, 16, 16, 16, 16, 16, 16, 80, 176, 16, 32, 32, 64, 16, 48,
   32, 16, 64, 16, 16, 16, 32, 16, 144, 240, 16, 80, 16, 16, 16, 64, 16, 16, 80, 192, 144, 304,
   352, 16, 16, 368, 400, 416, 16, 16, 16, 80, 128, 16, 16, 96, 208, 288, 432, 528, 16, 80, 16,
   112, 288, 256, 16, 16, 112, 16, 80, 128, 144, 336, 416, 16, 272, 416, 64, 592, 640, 112, 128,
   464, 64, 16, 96, 208, 256, 64, 16, 160, 16, 16, 16, 16, 224, 16, 48, 16, 176, 736, 96, 800,
   32, 368, 400, 464, 736, 800, 320, 464, 336, 16, 80, 336, 496, 576, 16, 160, 480, 320, 352,
   512, 512, 464, 16, 272, 16, 16, 128, 16, 224, 336, 448, 560, 16, 160, 144, 16, 208, 352, 576,
   240, 336]

/-- Exported callee signatures and stack bounds for prefix `[0, 147)`. -/
def ext6 : List (SigEntry × Nat) :=
  (fullFns.take 147).zipWith (fun f b => (⟨f.name, f.as, f.rs⟩, b)) slice6Bounds

/-- Slice 7 sub-module (`[147, 166)`, `19` functions). -/
def slice7Mod : Module := { fns := fullFns.drop 147 }

compile_linked_chunks! cert7 armTarget armLayout armLegalTarget armLabelClean
  slice7Mod 4 (ext := ext6) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatFullCert7
