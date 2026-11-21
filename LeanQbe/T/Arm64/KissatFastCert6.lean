module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Kissat.FullFast
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.FullFast

/-!
# Kissat M2 Unified Fast (`FullFast`) Certificate Slice 6/9 on AAPCS64 Arm64

Kernel-checked native compilation certificate (`cert6`) for slice `[122, 144)` (`22`
functions) of `LeanQbe.T.Examples.Kissat.FullFast.fastFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatFastCert6

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.FullFast

/-- Exported stack bounds for `[0, 122)` verified against `cert1..5` by `KissatFastCert`. -/
def slice5Bounds : List Nat :=
  [16, 16, 48, 64, 80, 128, 112, 176, 16, 16, 16, 16, 16, 16, 80, 176, 16, 32, 32, 64, 16, 48, 48,
   16, 80, 16, 16, 16, 32, 16, 160, 240, 16, 96, 16, 16, 16, 64, 16, 16, 80, 208, 144, 304, 352,
   16, 16, 480, 560, 576, 16, 16, 16, 80, 128, 16, 16, 128, 208, 288, 448, 672, 16, 80, 16, 144,
   288, 256, 16, 16, 128, 16, 80, 128, 160, 336, 432, 16, 272, 448, 80, 752, 800, 112, 128, 656,
   64, 16, 96, 208, 256, 80, 16, 176, 16, 16, 16, 16, 224, 16, 48, 16, 192, 928, 96, 1008, 48, 368,
   400, 624, 928, 1008, 336, 640, 336, 16, 96, 336, 656, 736, 32, 208]

/-- Exported callee signatures and stack bounds for prefix `[0, 122)`. -/
def ext5 : List (SigEntry × Nat) :=
  (fastFns.take 122).zipWith (fun f b => (⟨f.name, f.as, f.rs⟩, b)) slice5Bounds

/-- Slice 6 sub-module (`[122, 144)`, `22` functions). -/
def slice6Mod : Module := { fns := (fastFns.drop 122).take 22 }

compile_linked_chunks! cert6 armTarget armLayout armLegalTarget armLabelClean
  slice6Mod 4 (ext := ext5) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatFastCert6
