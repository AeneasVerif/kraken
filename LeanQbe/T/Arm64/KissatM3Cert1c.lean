module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Kissat.FullM3
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.FullM3

/-!
# Kissat M3 (`FullM3`) Certificate Slice 1c/19 on AAPCS64 Arm64

Kernel-checked native compilation certificate (`cert1c`) for slice `[32, 47)` (`15`
functions) of `LeanQbe.T.Examples.Kissat.FullM3.m3Fns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM3Cert1c

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.FullM3

/-- Exported stack bounds for `[0, 32)` verified against `pref1bCert` by `KissatM3Cert`. -/
def slice1bBounds : List Nat :=
  [16, 16, 48, 64, 80, 112, 112, 160, 16, 16, 16, 16, 16, 16, 80, 176, 16, 32, 32, 64, 16, 48,
   32, 16, 64, 16, 16, 16, 32, 16, 144, 240]

/-- Exported callee signatures and stack bounds for prefix `[0, 32)`. -/
def ext1b : List (SigEntry × Nat) :=
  (m3Fns.take 32).zipWith (fun f b => (⟨f.name, f.as, f.rs⟩, b)) slice1bBounds

/-- Slice 1c sub-module (`[32, 47)`, `15` functions). -/
def slice1cMod : Module := { fns := (m3Fns.drop 32).take 15 }

compile_linked_chunks! cert1c armTarget armLayout armLegalTarget armLabelClean
  slice1cMod 4 (ext := ext1b) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatM3Cert1c
