module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Kissat.FullFast
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.FullFast

/-!
# Kissat M2 Unified Fast (`FullFast`) Certificate Slice 9/9 on AAPCS64 Arm64

Kernel-checked native compilation certificate (`cert9`) for slice `[184, 196)` (`12`
functions) of `LeanQbe.T.Examples.Kissat.FullFast.fastFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatFastCert9

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.FullFast

/-- Exported stack bounds for `[0, 184)` verified against `cert1..8` by `KissatFastCert`. -/
def slice8Bounds : List Nat :=
  [16, 16, 48, 64, 80, 128, 112, 176, 16, 16, 16, 16, 16, 16, 80, 176, 16, 32, 32, 64, 16, 48, 48,
   16, 80, 16, 16, 16, 32, 16, 160, 240, 16, 96, 16, 16, 16, 64, 16, 16, 80, 208, 144, 304, 352,
   16, 16, 480, 560, 576, 16, 16, 16, 80, 128, 16, 16, 128, 208, 288, 448, 672, 16, 80, 16, 144,
   288, 256, 16, 16, 128, 16, 80, 128, 160, 336, 432, 16, 272, 448, 80, 752, 800, 112, 128, 656,
   64, 16, 96, 208, 256, 80, 16, 176, 16, 16, 16, 16, 224, 16, 48, 16, 192, 928, 96, 1008, 48, 368,
   400, 624, 928, 1008, 336, 640, 336, 16, 96, 336, 656, 736, 32, 208, 640, 320, 336, 688, 640,
   608, 16, 16, 32, 16, 16, 16, 16, 80, 16, 96, 16, 160, 16, 64, 16, 16, 272, 32, 16, 128, 16, 224,
   352, 432, 480, 176, 16, 384, 448, 256, 352, 416, 16, 16, 320, 432, 32, 128, 16, 304, 16, 576,
   32, 64, 224, 368, 16, 144, 496, 176, 400, 592, 16, 16, 720, 32]

/-- Exported callee signatures and stack bounds for prefix `[0, 184)`. -/
def ext8 : List (SigEntry × Nat) :=
  (fastFns.take 184).zipWith (fun f b => (⟨f.name, f.as, f.rs⟩, b)) slice8Bounds

/-- Slice 9 sub-module (`[184, 196)`, `12` functions). -/
def slice9Mod : Module := { fns := fastFns.drop 184 }

compile_linked_chunks! cert9 armTarget armLayout armLegalTarget armLabelClean
  slice9Mod 4 (ext := ext8) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatFastCert9
