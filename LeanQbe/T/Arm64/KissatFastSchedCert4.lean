module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Kissat.FullFastSched
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.FullFastSched

/-!
# Kissat M2 Fast-Scheduler (`FullFastSched`) Certificate Slice 4/7 on AAPCS64 Arm64

Kernel-checked native compilation certificate (`cert4`) for slice `[84, 107)` (`23`
functions) of `LeanQbe.T.Examples.Kissat.FullFastSched.schedSplicedFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatFastSchedCert4

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.FullFastSched

/-- Exported stack bounds for `[0, 84)` verified against `cert1..3` by
`KissatFastSchedCert`. -/
def slice3Bounds : List Nat :=
  [16, 16, 48, 64, 80, 112, 112, 160, 16, 16, 16, 16, 16, 16, 80, 176, 16, 32, 32, 64, 16, 48,
   32, 16, 64, 16, 16, 16, 32, 16, 144, 240, 16, 80, 16, 16, 16, 64, 16, 16, 80, 192, 144, 304,
   352, 16, 16, 368, 400, 416, 16, 16, 16, 80, 128, 16, 16, 112, 208, 288, 432, 528, 16, 80, 16,
   112, 288, 256, 16, 16, 112, 16, 80, 128, 144, 336, 416, 16, 272, 416, 64, 592, 640, 112]

/-- Exported callee signatures and stack bounds for prefix `[0, 84)`. -/
def ext3 : List (SigEntry × Nat) :=
  (schedSplicedFns.take 84).zipWith (fun f b => (⟨f.name, f.as, f.rs⟩, b)) slice3Bounds

/-- Slice 4 sub-module (`[84, 107)`, `23` functions). -/
def slice4Mod : Module := { fns := (schedSplicedFns.drop 84).take 23 }

compile_linked_chunks! cert4 armTarget armLayout armLegalTarget armLabelClean
  slice4Mod 4 (ext := ext3) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatFastSchedCert4
