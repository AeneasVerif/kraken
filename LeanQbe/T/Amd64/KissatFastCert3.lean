module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Examples.Kissat.FullFast
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Kissat.FullFast

/-!
# Kissat M2 Unified Fast (`FullFast`) Certificate Slice 3/9 on SysV x64

Kernel-checked native compilation certificate (`cert3`) for slice `[56, 78)` (`22`
functions) of `LeanQbe.T.Examples.Kissat.FullFast.fastFns` on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatFastCert3

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Examples.Kissat.FullFast

/-- Exported stack bounds for `[0, 56)` verified against `cert1..2` by `KissatFastCert`. -/
def slice2Bounds : List Nat :=
  [8, 8, 40, 56, 72, 104, 104, 152, 8, 8, 8, 8, 8, 8, 72, 168, 40, 88, 56, 120, 8, 72, 24, 8, 88,
   8, 8, 56, 72, 24, 168, 232, 56, 152, 8, 8, 8, 56, 8, 8, 72, 232, 136, 296, 344, 24, 8, 504,
   552, 568, 24, 40, 8, 72, 120, 8]

/-- Exported callee signatures and stack bounds for prefix `[0, 56)`. -/
def ext2 : List (SigEntry × Nat) :=
  (fastFns.take 56).zipWith (fun f b => (⟨f.name, f.as, f.rs⟩, b)) slice2Bounds

/-- Slice 3 sub-module (`[56, 78)`, `22` functions). -/
def slice3Mod : Module := { fns := (fastFns.drop 56).take 22 }

compile_linked_chunks! cert3 x64Target x64Layout x64LegalTarget x64LabelClean
  slice3Mod 4 (ext := ext2) (maxDirs := 450)

end LeanQbe.T.Amd64.KissatFastCert3
