module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Kissat.FullFastSched
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.FullFastSched

/-!
# Kissat M2 Fast-Scheduler (`FullFastSched`) Certificate Slice 2/7 on AAPCS64 Arm64

Kernel-checked native compilation certificate (`cert2`) for slice `[38, 61)` (`23`
functions) of `LeanQbe.T.Examples.Kissat.FullFastSched.schedSplicedFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatFastSchedCert2

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.FullFastSched

/-- Exported stack bounds for `[0, 38)` verified against `cert1` by
`KissatFastSchedCert`. -/
def slice1Bounds : List Nat :=
  [16, 16, 48, 64, 80, 112, 112, 160, 16, 16, 16, 16, 16, 16, 80, 176, 16, 32, 32, 64, 16, 48,
   32, 16, 64, 16, 16, 16, 32, 16, 144, 240, 16, 80, 16, 16, 16, 64]

/-- Exported callee signatures and stack bounds for prefix `[0, 38)`. -/
def ext1 : List (SigEntry × Nat) :=
  (schedSplicedFns.take 38).zipWith (fun f b => (⟨f.name, f.as, f.rs⟩, b)) slice1Bounds

/-- Slice 2 sub-module (`[38, 61)`, `23` functions). -/
def slice2Mod : Module := { fns := (schedSplicedFns.drop 38).take 23 }

compile_linked_chunks! cert2 armTarget armLayout armLegalTarget armLabelClean
  slice2Mod 4 (ext := ext1) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatFastSchedCert2
