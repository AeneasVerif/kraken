module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Examples.Kissat.FullFast
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Kissat.FullFast

/-!
# Kissat M2 Unified Fast (`FullFast`) Certificate Slice 8/9 on SysV x64

Kernel-checked native compilation certificate (`cert8`) for slice `[166, 184)` (`18`
functions) of `LeanQbe.T.Examples.Kissat.FullFast.fastFns` on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatFastCert8

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Examples.Kissat.FullFast

/-- Exported stack bounds for `[0, 166)` verified against `cert1..7` by `KissatFastCert`. -/
def slice7Bounds : List Nat :=
  [8, 8, 40, 56, 72, 120, 104, 168, 24, 8, 8, 8, 24, 40, 120, 232, 56, 104, 88, 152, 8, 88, 40, 24,
   136, 56, 24, 72, 88, 40, 216, 296, 72, 168, 8, 40, 8, 56, 8, 8, 104, 248, 136, 360, 408, 40, 40,
   600, 680, 696, 40, 56, 8, 72, 120, 8, 56, 232, 312, 344, 504, 792, 72, 136, 8, 264, 344, 312,
   24, 24, 168, 8, 72, 120, 200, 376, 472, 8, 328, 504, 136, 872, 920, 216, 264, 776, 104, 24, 88,
   216, 280, 168, 8, 264, 24, 40, 24, 24, 280, 56, 88, 8, 248, 1048, 104, 1128, 120, 424, 456, 744,
   1048, 1128, 440, 760, 392, 40, 168, 392, 776, 856, 104, 312, 760, 408, 392, 808, 760, 728, 24,
   24, 104, 24, 40, 40, 88, 200, 56, 168, 40, 264, 40, 88, 88, 8, 328, 104, 24, 200, 8, 296, 424,
   488, 536, 264, 40, 440, 504, 344, 472, 536, 40, 72, 456, 568, 88, 168]

/-- Exported callee signatures and stack bounds for prefix `[0, 166)`. -/
def ext7 : List (SigEntry × Nat) :=
  (fastFns.take 166).zipWith (fun f b => (⟨f.name, f.as, f.rs⟩, b)) slice7Bounds

/-- Slice 8 sub-module (`[166, 184)`, `18` functions). -/
def slice8Mod : Module := { fns := (fastFns.drop 166).take 18 }

compile_linked_chunks! cert8 x64Target x64Layout x64LegalTarget x64LabelClean
  slice8Mod 4 (ext := ext7) (maxDirs := 450)

end LeanQbe.T.Amd64.KissatFastCert8
