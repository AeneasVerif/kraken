module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Kissat.FullM3
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.FullM3

/-!
# Kissat M3 (`FullM3`) Certificate Slice 6/17 on AAPCS64 Arm64

Kernel-checked native compilation certificate (`cert6`) for slice `[91, 103)` (`12`
functions) of `LeanQbe.T.Examples.Kissat.FullM3.m3Fns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM3Cert6

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.FullM3

/-- Exported stack bounds for `[0, 91)` verified against `cert1..5` by `KissatM3Cert`. -/
def slice5Bounds : List Nat :=
  [16, 16, 48, 64, 80, 112, 112, 160, 16, 16, 16, 16, 16, 16, 80, 176, 16, 32, 32, 64, 16, 48,
   32, 16, 64, 16, 16, 16, 32, 16, 144, 240, 16, 80, 16, 16, 16, 64, 16, 16, 80, 192, 144, 304,
   352, 16, 16, 464, 576, 624, 640, 16, 16, 16, 80, 128, 16, 16, 112, 208, 288, 432, 736, 16, 80,
   16, 112, 288, 256, 16, 16, 112, 16, 80, 128, 144, 336, 416, 16, 272, 416, 64, 800, 848, 112,
   128, 688, 64, 16, 96, 208]

/-- Exported callee signatures and stack bounds for prefix `[0, 91)`. -/
def ext5 : List (SigEntry × Nat) :=
  (m3Fns.take 91).zipWith (fun f b => (⟨f.name, f.as, f.rs⟩, b)) slice5Bounds

/-- Slice 6 sub-module (`[91, 103)`, `12` functions). -/
def slice6Mod : Module := { fns := (m3Fns.drop 91).take 12 }

compile_linked_chunks! cert6 armTarget armLayout armLegalTarget armLabelClean
  slice6Mod 4 (ext := ext5) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatM3Cert6
