module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Kissat.FullFast
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.FullFast

/-!
# Kissat M2 Unified Fast (`FullFast`) Certificate Slice 5/9 on AAPCS64 Arm64

Kernel-checked native compilation certificate (`cert5`) for slice `[100, 122)` (`22`
functions) of `LeanQbe.T.Examples.Kissat.FullFast.fastFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatFastCert5

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.FullFast

/-- Exported stack bounds for `[0, 100)` verified against `cert1..4` by `KissatFastCert`. -/
def slice4Bounds : List Nat :=
  [16, 16, 48, 64, 80, 112, 112, 160, 16, 16, 16, 16, 16, 16, 80, 176, 16, 32, 32, 64, 16, 48,
   32, 16, 64, 16, 16, 16, 32, 16, 144, 240, 16, 80, 16, 16, 16, 64, 16, 16, 80, 192, 144, 304,
   352, 16, 16, 464, 512, 528, 16, 16, 16, 80, 128, 16, 16, 112, 208, 288, 432, 624, 16, 80, 16,
   112, 288, 256, 16, 16, 112, 16, 80, 128, 144, 336, 416, 16, 272, 416, 64, 688, 736, 112, 128,
   576, 64, 16, 96, 208, 256, 64, 16, 160, 16, 16, 16, 16, 224, 16]

/-- Exported callee signatures and stack bounds for prefix `[0, 100)`. -/
def ext4 : List (SigEntry × Nat) :=
  (fastFns.take 100).zipWith (fun f b => (⟨f.name, f.as, f.rs⟩, b)) slice4Bounds

/-- Slice 5 sub-module (`[100, 122)`, `22` functions). -/
def slice5Mod : Module := { fns := (fastFns.drop 100).take 22 }

compile_linked_chunks! cert5 armTarget armLayout armLegalTarget armLabelClean
  slice5Mod 4 (ext := ext4) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatFastCert5
