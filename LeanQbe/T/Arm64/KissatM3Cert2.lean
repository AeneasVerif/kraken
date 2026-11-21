module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Kissat.FullM3
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.FullM3

/-!
# Kissat M3 (`FullM3`) Certificate Slice 2/17 on AAPCS64 Arm64

Kernel-checked native compilation certificate (`cert2`) for slice `[47, 59)` (`12`
functions) of `LeanQbe.T.Examples.Kissat.FullM3.m3Fns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM3Cert2

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.FullM3

/-- Exported stack bounds for `[0, 47)` verified against `cert1..1` by `KissatM3Cert`. -/
def slice1Bounds : List Nat :=
  [16, 16, 48, 64, 80, 112, 112, 160, 16, 16, 16, 16, 16, 16, 80, 176, 16, 32, 32, 64, 16, 48,
   32, 16, 64, 16, 16, 16, 32, 16, 144, 240, 16, 80, 16, 16, 16, 64, 16, 16, 80, 192, 144, 304,
   352, 16, 16]

/-- Exported callee signatures and stack bounds for prefix `[0, 47)`. -/
def ext1 : List (SigEntry × Nat) :=
  (m3Fns.take 47).zipWith (fun f b => (⟨f.name, f.as, f.rs⟩, b)) slice1Bounds

/-- Slice 2 sub-module (`[47, 59)`, `12` functions). -/
def slice2Mod : Module := { fns := (m3Fns.drop 47).take 12 }

compile_linked_chunks! cert2 armTarget armLayout armLegalTarget armLabelClean
  slice2Mod 4 (ext := ext1) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatM3Cert2
