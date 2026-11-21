module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Kissat.FullFast
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.FullFast

/-!
# Kissat M2 Unified Fast (`FullFast`) Certificate Slice 2/9 on AAPCS64 Arm64

Kernel-checked native compilation certificate (`cert2`) for slice `[36, 56)` (`20`
functions) of `LeanQbe.T.Examples.Kissat.FullFast.fastFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatFastCert2

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.FullFast

/-- Exported stack bounds for `[0, 36)` verified against `cert1..1` by `KissatFastCert`. -/
def slice1Bounds : List Nat :=
  [16, 16, 48, 64, 80, 112, 112, 160, 16, 16, 16, 16, 16, 16, 80, 176, 16, 32, 32, 64, 16, 48,
   32, 16, 64, 16, 16, 16, 32, 16, 144, 240, 16, 80, 16, 16]

/-- Exported callee signatures and stack bounds for prefix `[0, 36)`. -/
def ext1 : List (SigEntry × Nat) :=
  (fastFns.take 36).zipWith (fun f b => (⟨f.name, f.as, f.rs⟩, b)) slice1Bounds

/-- Slice 2 sub-module (`[36, 56)`, `20` functions). -/
def slice2Mod : Module := { fns := (fastFns.drop 36).take 20 }

compile_linked_chunks! cert2 armTarget armLayout armLegalTarget armLabelClean
  slice2Mod 4 (ext := ext1) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatFastCert2
