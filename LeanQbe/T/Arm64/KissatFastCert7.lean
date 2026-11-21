module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Kissat.FullFast
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.FullFast

/-!
# Kissat M2 Unified Fast (`FullFast`) Certificate Slice 7/9 on AAPCS64 Arm64

Kernel-checked native compilation certificate (`cert7`) for slice `[144, 166)` (`22`
functions) of `LeanQbe.T.Examples.Kissat.FullFast.fastFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatFastCert7

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.FullFast

/-- Exported stack bounds for `[0, 144)` verified against `cert1..6` by `KissatFastCert`. -/
def slice6Bounds : List Nat :=
  [16, 16, 48, 64, 80, 112, 112, 160, 16, 16, 16, 16, 16, 16, 80, 176, 16, 32, 32, 64, 16, 48,
   32, 16, 64, 16, 16, 16, 32, 16, 144, 240, 16, 80, 16, 16, 16, 64, 16, 16, 80, 192, 144, 304,
   352, 16, 16, 464, 512, 528, 16, 16, 16, 80, 128, 16, 16, 112, 208, 288, 432, 624, 16, 80, 16,
   112, 288, 256, 16, 16, 112, 16, 80, 128, 144, 336, 416, 16, 272, 416, 64, 688, 736, 112, 128,
   576, 64, 16, 96, 208, 256, 64, 16, 160, 16, 16, 16, 16, 224, 16, 48, 16, 176, 832, 96, 896,
   32, 368, 400, 576, 832, 896, 320, 576, 336, 16, 80, 336, 608, 688, 16, 160, 592, 320, 352,
   624, 608, 560, 16, 16, 32, 16, 16, 16, 16, 80, 16, 64, 16, 128, 16, 64, 16, 16]

/-- Exported callee signatures and stack bounds for prefix `[0, 144)`. -/
def ext6 : List (SigEntry × Nat) :=
  (fastFns.take 144).zipWith (fun f b => (⟨f.name, f.as, f.rs⟩, b)) slice6Bounds

/-- Slice 7 sub-module (`[144, 166)`, `22` functions). -/
def slice7Mod : Module := { fns := (fastFns.drop 144).take 22 }

compile_linked_chunks! cert7 armTarget armLayout armLegalTarget armLabelClean
  slice7Mod 4 (ext := ext6) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatFastCert7
