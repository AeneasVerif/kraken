module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Examples.Kissat.FullFast
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Kissat.FullFast

/-!
# Kissat M2 Unified Fast (`FullFast`) Certificate Slice 4/9 on SysV x64

Kernel-checked native compilation certificate (`cert4`) for slice `[78, 100)` (`22`
functions) of `LeanQbe.T.Examples.Kissat.FullFast.fastFns` on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatFastCert4

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Examples.Kissat.FullFast

/-- Exported stack bounds for `[0, 78)` verified against `cert1..3` by `KissatFastCert`. -/
def slice3Bounds : List Nat :=
  [8, 8, 40, 56, 72, 120, 104, 168, 24, 8, 8, 8, 24, 40, 120, 232, 56, 104, 88, 152, 8, 88, 40, 24,
   136, 56, 24, 72, 88, 40, 216, 296, 72, 168, 8, 40, 8, 56, 8, 8, 104, 248, 136, 360, 408, 40, 40,
   600, 680, 696, 40, 56, 8, 72, 120, 8, 56, 232, 312, 344, 504, 792, 72, 136, 8, 264, 344, 312,
   24, 24, 168, 8, 72, 120, 200, 376, 472, 8]

/-- Exported callee signatures and stack bounds for prefix `[0, 78)`. -/
def ext3 : List (SigEntry × Nat) :=
  (fastFns.take 78).zipWith (fun f b => (⟨f.name, f.as, f.rs⟩, b)) slice3Bounds

/-- Slice 4 sub-module (`[78, 100)`, `22` functions). -/
def slice4Mod : Module := { fns := (fastFns.drop 78).take 22 }

compile_linked_chunks! cert4 x64Target x64Layout x64LegalTarget x64LabelClean
  slice4Mod 4 (ext := ext3) (maxDirs := 450)

end LeanQbe.T.Amd64.KissatFastCert4
