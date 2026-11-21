module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Kissat.FullFastSched
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.FullFastSched

/-!
# Kissat M2 Fast-Scheduler (`FullFastSched`) Certificate Slice 6/7 on AAPCS64 Arm64

Kernel-checked native compilation certificate (`cert6`) for slice `[130, 152)` (`22`
functions) of `LeanQbe.T.Examples.Kissat.FullFastSched.schedSplicedFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatFastSchedCert6

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.FullFastSched

/-- Exported stack bounds for `[0, 130)` verified against `cert1..5` by
`KissatFastSchedCert`. -/
def slice5Bounds : List Nat :=
  [16, 16, 48, 64, 80, 128, 112, 176, 16, 16, 16, 16, 16, 16, 80, 176, 16, 32, 32, 64, 16, 48, 48,
   16, 80, 16, 16, 16, 32, 16, 160, 240, 16, 96, 16, 16, 16, 64, 16, 16, 80, 208, 144, 304, 352, 16,
   16, 384, 432, 448, 16, 16, 16, 80, 128, 16, 16, 128, 208, 288, 448, 544, 16, 80, 16, 144, 288,
   256, 16, 16, 128, 16, 80, 128, 160, 336, 432, 16, 272, 448, 80, 624, 672, 112, 128, 528, 64, 16,
   96, 208, 256, 80, 16, 176, 16, 16, 16, 16, 224, 16, 48, 16, 192, 800, 96, 880, 48, 368, 400, 496,
   800, 880, 336, 512, 336, 16, 96, 336, 528, 608, 32, 208, 512, 320, 336, 560, 512, 480, 16, 272]

/-- Exported callee signatures and stack bounds for prefix `[0, 130)`. -/
def ext5 : List (SigEntry × Nat) :=
  (schedSplicedFns.take 130).zipWith (fun f b => (⟨f.name, f.as, f.rs⟩, b)) slice5Bounds

/-- Slice 6 sub-module (`[130, 152)`, `22` functions). -/
def slice6Mod : Module := { fns := (schedSplicedFns.drop 130).take 22 }

compile_linked_chunks! cert6 armTarget armLayout armLegalTarget armLabelClean
  slice6Mod 4 (ext := ext5) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatFastSchedCert6
