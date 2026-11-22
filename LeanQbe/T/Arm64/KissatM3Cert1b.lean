module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Kissat.FullM3
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.FullM3

/-!
# Kissat M3 (`FullM3`) Certificate Slice 1b/19 on AAPCS64 Arm64

Kernel-checked native compilation certificate (`cert1b`) for slice `[16, 32)` (`16`
functions) of `LeanQbe.T.Examples.Kissat.FullM3.m3Fns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM3Cert1b

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.FullM3

/-- Exported stack bounds for `[0, 16)` verified against `cert1a` by `KissatM3Cert`. -/
def slice1aBounds : List Nat :=
  [16, 16, 48, 64, 80, 112, 112, 160, 16, 16, 16, 16, 16, 16, 80, 176]

/-- Exported callee signatures and stack bounds for prefix `[0, 16)`. -/
def ext1a : List (SigEntry × Nat) :=
  (m3Fns.take 16).zipWith (fun f b => (⟨f.name, f.as, f.rs⟩, b)) slice1aBounds

/-- Slice 1b sub-module (`[16, 32)`, `16` functions). -/
def slice1bMod : Module := { fns := (m3Fns.drop 16).take 16 }

compile_linked_chunks! cert1b armTarget armLayout armLegalTarget armLabelClean
  slice1bMod 4 (ext := ext1a) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatM3Cert1b
