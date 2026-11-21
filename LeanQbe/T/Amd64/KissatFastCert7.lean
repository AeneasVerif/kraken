module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Examples.Kissat.FullFast
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Kissat.FullFast

/-!
# Kissat M2 Unified Fast (`FullFast`) Certificate Slice 7/9 on SysV x64

Kernel-checked native compilation certificate (`cert7`) for slice `[144, 166)` (`22`
functions) of `LeanQbe.T.Examples.Kissat.FullFast.fastFns` on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatFastCert7

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Examples.Kissat.FullFast

/-- Exported stack bounds for `[0, 144)` verified against `cert1..6` by `KissatFastCert`. -/
def slice6Bounds : List Nat :=
  [8, 8, 40, 56, 72, 104, 104, 152, 8, 8, 8, 8, 8, 8, 72, 168, 40, 88, 56, 120, 8, 72, 24, 8, 88,
   8, 8, 56, 72, 24, 168, 232, 56, 152, 8, 8, 8, 56, 8, 8, 72, 232, 136, 296, 344, 24, 8, 504,
   552, 568, 24, 40, 8, 72, 120, 8, 40, 184, 232, 280, 424, 664, 40, 104, 8, 200, 280, 248, 8, 8,
   120, 8, 72, 120, 152, 360, 440, 8, 264, 408, 120, 728, 776, 168, 184, 616, 88, 8, 88, 200,
   248, 136, 8, 200, 8, 24, 8, 8, 216, 40, 72, 8, 200, 872, 88, 936, 104, 360, 392, 616, 872,
   936, 376, 616, 328, 24, 152, 328, 648, 728, 72, 248, 632, 344, 344, 664, 648, 600, 8, 8, 56,
   8, 8, 8, 56, 152, 40, 104, 24, 200, 24, 56, 72, 8]

/-- Exported callee signatures and stack bounds for prefix `[0, 144)`. -/
def ext6 : List (SigEntry × Nat) :=
  (fastFns.take 144).zipWith (fun f b => (⟨f.name, f.as, f.rs⟩, b)) slice6Bounds

/-- Slice 7 sub-module (`[144, 166)`, `22` functions). -/
def slice7Mod : Module := { fns := (fastFns.drop 144).take 22 }

compile_linked_chunks! cert7 x64Target x64Layout x64LegalTarget x64LabelClean
  slice7Mod 4 (ext := ext6) (maxDirs := 450)

end LeanQbe.T.Amd64.KissatFastCert7
