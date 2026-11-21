module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Kissat.FullM3
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.FullM3

/-!
# Kissat M3 (`FullM3`) Certificate Slice 16/17 on AAPCS64 Arm64

Kernel-checked native compilation certificate (`cert16`) for slice `[183, 195)` (`12`
functions) of `LeanQbe.T.Examples.Kissat.FullM3.m3Fns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM3Cert16

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.FullM3

/-- Exported stack bounds for `[0, 183)` verified against `cert1..15` by `KissatM3Cert`. -/
def slice15Bounds : List Nat :=
  [16, 16, 48, 64, 80, 128, 112, 176, 16, 16, 16, 16, 16, 16, 80, 176, 16, 32, 32, 64, 16, 48, 48,
   16, 80, 16, 16, 16, 32, 16, 160, 240, 16, 96, 16, 16, 16, 64, 16, 16, 80, 208, 144, 304, 352, 16,
   16, 480, 592, 672, 688, 16, 16, 16, 80, 128, 16, 16, 128, 208, 288, 448, 784, 16, 80, 16, 144,
   288, 256, 16, 16, 128, 16, 80, 128, 160, 336, 432, 16, 272, 448, 80, 864, 912, 112, 128, 768, 64,
   16, 96, 208, 256, 80, 16, 176, 16, 16, 16, 16, 224, 16, 48, 16, 192, 1040, 96, 1120, 48, 368,
   400, 736, 1040, 1136, 336, 752, 336, 16, 96, 336, 768, 848, 32, 208, 752, 320, 336, 800, 752,
   720, 16, 16, 32, 16, 16, 16, 16, 80, 16, 96, 16, 160, 16, 64, 16, 16, 272, 32, 16, 128, 16, 224,
   352, 80, 224, 368, 96, 576, 704, 176, 16, 384, 448, 256, 352, 416, 16, 16, 320, 432, 32, 128, 16,
   304, 16, 576, 32, 64, 224, 368, 16, 144, 496, 176]

/-- Exported callee signatures and stack bounds for prefix `[0, 183)`. -/
def ext15 : List (SigEntry × Nat) :=
  (m3Fns.take 183).zipWith (fun f b => (⟨f.name, f.as, f.rs⟩, b)) slice15Bounds

/-- Slice 16 sub-module (`[183, 195)`, `12` functions). -/
def slice16Mod : Module := { fns := (m3Fns.drop 183).take 12 }

compile_linked_chunks! cert16 armTarget armLayout armLegalTarget armLabelClean
  slice16Mod 4 (ext := ext15) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatM3Cert16
