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
  [16, 16, 48, 64, 80, 112, 112, 160, 16, 16, 16, 16, 16, 16, 80, 176, 16, 32, 32, 64, 16, 48,
   32, 16, 64, 16, 16, 16, 32, 16, 144, 240, 16, 80, 16, 16, 16, 64, 16, 16, 80, 192, 144, 304,
   352, 16, 16, 368, 400, 416, 16, 16, 16, 80, 128, 16, 16, 112, 208, 288, 432, 528, 16, 80, 16,
   112, 288, 256, 16, 16, 112, 16, 80, 128, 144, 336, 416, 16, 272, 416, 64, 592, 640, 112, 128,
   464, 64, 16, 96, 208, 256, 64, 16, 160, 16, 16, 16, 16, 224, 16, 48, 16, 176, 736, 96, 800,
   32, 368, 400, 464, 736, 800, 320, 464, 336, 16, 80, 336, 496, 576, 16, 160, 480, 320, 352,
   512, 512, 464, 16, 272]

/-- Exported callee signatures and stack bounds for prefix `[0, 130)`. -/
def ext5 : List (SigEntry × Nat) :=
  (schedSplicedFns.take 130).zipWith (fun f b => (⟨f.name, f.as, f.rs⟩, b)) slice5Bounds

/-- Slice 6 sub-module (`[130, 152)`, `22` functions). -/
def slice6Mod : Module := { fns := (schedSplicedFns.drop 130).take 22 }

compile_linked_chunks! cert6 armTarget armLayout armLegalTarget armLabelClean
  slice6Mod 4 (ext := ext5) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatFastSchedCert6
