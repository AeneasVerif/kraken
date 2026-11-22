module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Examples.Kissat.FullM3
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Kissat.FullM3

/-!
# Kissat M3 (`FullM3`) Certificate Slice 1b/19 on SysV x64

Kernel-checked native compilation certificate (`cert1b`) for slice `[16, 32)` (`16`
functions) of `LeanQbe.T.Examples.Kissat.FullM3.m3Fns` on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatM3Cert1b

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Examples.Kissat.FullM3

/-- Exported stack bounds for `[0, 16)` verified against `cert1a` by `KissatM3Cert`. -/
def slice1aBounds : List Nat :=
  [8, 8, 40, 56, 72, 104, 104, 152, 8, 8, 8, 8, 8, 8, 72, 168]

/-- Exported callee signatures and stack bounds for prefix `[0, 16)`. -/
def ext1a : List (SigEntry × Nat) :=
  (m3Fns.take 16).zipWith (fun f b => (⟨f.name, f.as, f.rs⟩, b)) slice1aBounds

/-- Slice 1b sub-module (`[16, 32)`, `16` functions). -/
def slice1bMod : Module := { fns := (m3Fns.drop 16).take 16 }

compile_linked_chunks! cert1b x64Target x64Layout x64LegalTarget x64LabelClean
  slice1bMod 4 (ext := ext1a) (maxDirs := 450)

end LeanQbe.T.Amd64.KissatM3Cert1b
