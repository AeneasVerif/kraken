module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Kissat.FullM3
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.FullM3

/-!
# Kissat M3 (`FullM3`) Certificate Slice 13/17 on AAPCS64 Arm64

Kernel-checked native compilation certificate (`cert13`) for slice `[158, 167)` (`9`
functions) of `LeanQbe.T.Examples.Kissat.FullM3.m3Fns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM3Cert13

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.FullM3

/-- Exported stack bounds for `[0, 158)` verified against `cert1..12` by `KissatM3Cert`. -/
def slice12Bounds : List Nat :=
  [16, 16, 48, 64, 80, 128, 112, 176, 16, 16, 16, 16, 16, 16, 80, 176, 16, 32, 32, 64, 16, 48, 48,
   16, 80, 16, 16, 16, 32, 16, 160, 240, 16, 96, 16, 16, 16, 64, 16, 16, 80, 208, 144, 304, 352, 16,
   16, 480, 592, 672, 688, 16, 16, 16, 80, 128, 16, 16, 128, 208, 288, 448, 784, 16, 80, 16, 144,
   288, 256, 16, 16, 128, 16, 80, 128, 160, 336, 432, 16, 272, 448, 80, 864, 912, 112, 128, 768, 64,
   16, 96, 208, 256, 80, 16, 176, 16, 16, 16, 16, 224, 16, 48, 16, 192, 1040, 96, 1120, 48, 368,
   400, 736, 1040, 1136, 336, 752, 336, 16, 96, 336, 768, 848, 32, 208, 752, 320, 336, 800, 752,
   720, 16, 16, 32, 16, 16, 16, 16, 80, 16, 96, 16, 160, 16, 64, 16, 16, 272, 32, 16, 128, 16, 224,
   352, 80, 224, 368, 96, 576, 704]

/-- Exported callee signatures and stack bounds for prefix `[0, 158)`. -/
def ext12 : List (SigEntry × Nat) :=
  (m3Fns.take 158).zipWith (fun f b => (⟨f.name, f.as, f.rs⟩, b)) slice12Bounds

/-- Slice 13 sub-module (`[158, 167)`, `9` functions). -/
def slice13Mod : Module := { fns := (m3Fns.drop 158).take 9 }

compile_linked_chunks! cert13 armTarget armLayout armLegalTarget armLabelClean
  slice13Mod 4 (ext := ext12) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatM3Cert13
