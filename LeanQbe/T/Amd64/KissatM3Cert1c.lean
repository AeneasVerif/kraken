module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Examples.Kissat.FullM3
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Kissat.FullM3

/-!
# Kissat M3 (`FullM3`) Certificate Slice 1c/19 on SysV x64

Kernel-checked native compilation certificate (`cert1c`) for slice `[32, 47)` (`15`
functions) of `LeanQbe.T.Examples.Kissat.FullM3.m3Fns` on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatM3Cert1c

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Examples.Kissat.FullM3

/-- Exported stack bounds for `[0, 32)` verified against `pref1bCert` by `KissatM3Cert`. -/
def slice1bBounds : List Nat :=
  [8, 8, 40, 56, 72, 104, 104, 152, 8, 8, 8, 8, 8, 8, 72, 168, 40, 88, 56, 120, 8, 72, 24, 8,
   88, 8, 8, 56, 72, 24, 168, 232]

/-- Exported callee signatures and stack bounds for prefix `[0, 32)`. -/
def ext1b : List (SigEntry × Nat) :=
  (m3Fns.take 32).zipWith (fun f b => (⟨f.name, f.as, f.rs⟩, b)) slice1bBounds

/-- Slice 1c sub-module (`[32, 47)`, `15` functions). -/
def slice1cMod : Module := { fns := (m3Fns.drop 32).take 15 }

compile_linked_chunks! cert1c x64Target x64Layout x64LegalTarget x64LabelClean
  slice1cMod 4 (ext := ext1b) (maxDirs := 450)

end LeanQbe.T.Amd64.KissatM3Cert1c
