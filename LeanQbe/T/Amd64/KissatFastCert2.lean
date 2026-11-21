module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Examples.Kissat.FullFast
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Kissat.FullFast

/-!
# Kissat M2 Unified Fast (`FullFast`) Certificate Slice 2/9 on SysV x64

Kernel-checked native compilation certificate (`cert2`) for slice `[36, 56)` (`20`
functions) of `LeanQbe.T.Examples.Kissat.FullFast.fastFns` on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatFastCert2

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Examples.Kissat.FullFast

/-- Exported stack bounds for `[0, 36)` verified against `cert1..1` by `KissatFastCert`. -/
def slice1Bounds : List Nat :=
  [8, 8, 40, 56, 72, 104, 104, 152, 8, 8, 8, 8, 8, 8, 72, 168, 40, 88, 56, 120, 8, 72, 24, 8, 88,
   8, 8, 56, 72, 24, 168, 232, 56, 152, 8, 8]

/-- Exported callee signatures and stack bounds for prefix `[0, 36)`. -/
def ext1 : List (SigEntry × Nat) :=
  (fastFns.take 36).zipWith (fun f b => (⟨f.name, f.as, f.rs⟩, b)) slice1Bounds

/-- Slice 2 sub-module (`[36, 56)`, `20` functions). -/
def slice2Mod : Module := { fns := (fastFns.drop 36).take 20 }

compile_linked_chunks! cert2 x64Target x64Layout x64LegalTarget x64LabelClean
  slice2Mod 4 (ext := ext1) (maxDirs := 450)

end LeanQbe.T.Amd64.KissatFastCert2
