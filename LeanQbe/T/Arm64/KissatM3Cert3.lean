module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Kissat.FullM3
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.FullM3

/-!
# Kissat M3 (`FullM3`) Certificate Slice 3/17 on AAPCS64 Arm64

Kernel-checked native compilation certificate (`cert3`) for slice `[59, 68)` (`9`
functions) of `LeanQbe.T.Examples.Kissat.FullM3.m3Fns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM3Cert3

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.FullM3

/-- Exported stack bounds for `[0, 59)` verified against `cert1..2` by `KissatM3Cert`. -/
def slice2Bounds : List Nat :=
  [16, 16, 48, 64, 80, 112, 112, 160, 16, 16, 16, 16, 16, 16, 80, 176, 16, 32, 32, 64, 16, 48,
   32, 16, 64, 16, 16, 16, 32, 16, 144, 240, 16, 80, 16, 16, 16, 64, 16, 16, 80, 192, 144, 304,
   352, 16, 16, 464, 576, 624, 640, 16, 16, 16, 80, 128, 16, 16, 112]

/-- Exported callee signatures and stack bounds for prefix `[0, 59)`. -/
def ext2 : List (SigEntry × Nat) :=
  (m3Fns.take 59).zipWith (fun f b => (⟨f.name, f.as, f.rs⟩, b)) slice2Bounds

/-- Slice 3 sub-module (`[59, 68)`, `9` functions). -/
def slice3Mod : Module := { fns := (m3Fns.drop 59).take 9 }

compile_linked_chunks! cert3 armTarget armLayout armLegalTarget armLabelClean
  slice3Mod 4 (ext := ext2) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatM3Cert3
