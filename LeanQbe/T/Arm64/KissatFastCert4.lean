module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Kissat.FullFast
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.FullFast

/-!
# Kissat M2 Unified Fast (`FullFast`) Certificate Slice 4/9 on AAPCS64 Arm64

Kernel-checked native compilation certificate (`cert4`) for slice `[78, 100)` (`22`
functions) of `LeanQbe.T.Examples.Kissat.FullFast.fastFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatFastCert4

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.FullFast

/-- Exported stack bounds for `[0, 78)` verified against `cert1..3` by `KissatFastCert`. -/
def slice3Bounds : List Nat :=
  [16, 16, 48, 64, 80, 112, 112, 160, 16, 16, 16, 16, 16, 16, 80, 176, 16, 32, 32, 64, 16, 48,
   32, 16, 64, 16, 16, 16, 32, 16, 144, 240, 16, 80, 16, 16, 16, 64, 16, 16, 80, 192, 144, 304,
   352, 16, 16, 464, 512, 528, 16, 16, 16, 80, 128, 16, 16, 112, 208, 288, 432, 624, 16, 80, 16,
   112, 288, 256, 16, 16, 112, 16, 80, 128, 144, 336, 416, 16]

/-- Exported callee signatures and stack bounds for prefix `[0, 78)`. -/
def ext3 : List (SigEntry × Nat) :=
  (fastFns.take 78).zipWith (fun f b => (⟨f.name, f.as, f.rs⟩, b)) slice3Bounds

/-- Slice 4 sub-module (`[78, 100)`, `22` functions). -/
def slice4Mod : Module := { fns := (fastFns.drop 78).take 22 }

compile_linked_chunks! cert4 armTarget armLayout armLegalTarget armLabelClean
  slice4Mod 4 (ext := ext3) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatFastCert4
