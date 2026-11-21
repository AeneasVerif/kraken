module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Kissat.FullM3
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.FullM3

/-!
# Kissat M3 (`FullM3`) Certificate Slice 14/17 on AAPCS64 Arm64

Kernel-checked native compilation certificate (`cert14`) for slice `[167, 175)` (`8`
functions) of `LeanQbe.T.Examples.Kissat.FullM3.m3Fns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM3Cert14

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.FullM3

/-- Exported stack bounds for `[0, 167)` verified against `cert1..13` by `KissatM3Cert`. -/
def slice13Bounds : List Nat :=
  [16, 16, 48, 64, 80, 112, 112, 160, 16, 16, 16, 16, 16, 16, 80, 176, 16, 32, 32, 64, 16, 48,
   32, 16, 64, 16, 16, 16, 32, 16, 144, 240, 16, 80, 16, 16, 16, 64, 16, 16, 80, 192, 144, 304,
   352, 16, 16, 464, 576, 624, 640, 16, 16, 16, 80, 128, 16, 16, 112, 208, 288, 432, 736, 16, 80,
   16, 112, 288, 256, 16, 16, 112, 16, 80, 128, 144, 336, 416, 16, 272, 416, 64, 800, 848, 112,
   128, 688, 64, 16, 96, 208, 256, 64, 16, 160, 16, 16, 16, 16, 224, 16, 48, 16, 176, 944, 96,
   1008, 32, 368, 400, 688, 944, 1024, 320, 688, 336, 16, 80, 336, 720, 816, 16, 160, 704, 320,
   352, 736, 720, 672, 16, 16, 32, 16, 16, 16, 16, 80, 16, 64, 16, 128, 16, 64, 16, 16, 272, 16,
   16, 128, 16, 224, 368, 80, 208, 352, 96, 576, 704, 192, 16, 368, 432, 240, 336, 400, 16, 16]

/-- Exported callee signatures and stack bounds for prefix `[0, 167)`. -/
def ext13 : List (SigEntry × Nat) :=
  (m3Fns.take 167).zipWith (fun f b => (⟨f.name, f.as, f.rs⟩, b)) slice13Bounds

/-- Slice 14 sub-module (`[167, 175)`, `8` functions). -/
def slice14Mod : Module := { fns := (m3Fns.drop 167).take 8 }

compile_linked_chunks! cert14 armTarget armLayout armLegalTarget armLabelClean
  slice14Mod 4 (ext := ext13) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatM3Cert14
