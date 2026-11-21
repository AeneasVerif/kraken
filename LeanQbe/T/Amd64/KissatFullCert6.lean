module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Examples.Kissat.Full
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Kissat.Full

/-!
# Stage 4 (`D-Full`) Kissat Native Certificate Slice 6/7 on SysV x64

Kernel-checked native compilation certificate (`cert6`) for slice `[128, 147)` (`19` functions) of
`LeanQbe.T.Examples.Kissat.Full.fullFns` on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatFullCert6

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Examples.Kissat.Full

/-- Exported stack bounds for `[0, 128)` verified against `cert1..5` by `KissatFullCert`. -/
def slice5Bounds : List Nat :=
  [8, 8, 40, 56, 72, 104, 104, 152, 8, 8, 8, 8, 8, 8, 72, 168, 40, 88, 56, 120, 8, 72, 24, 8, 88,
   8, 8, 56, 72, 24, 168, 232, 56, 152, 8, 8, 8, 56, 8, 8, 72, 232, 136, 296, 344, 24, 8, 376,
   408, 424, 24, 40, 8, 72, 120, 8, 40, 168, 232, 280, 424, 520, 40, 104, 8, 200, 280, 248, 8, 8,
   120, 8, 72, 120, 152, 360, 440, 8, 264, 408, 120, 584, 632, 168, 184, 472, 88, 8, 88, 200,
   248, 136, 8, 200, 8, 24, 8, 8, 216, 40, 72, 8, 200, 728, 88, 792, 104, 360, 392, 472, 728,
   792, 376, 472, 328, 24, 152, 328, 504, 584, 72, 248, 488, 344, 344, 520, 504, 456]

/-- Exported callee signatures and stack bounds for prefix `[0, 128)`. -/
def ext5 : List (SigEntry × Nat) :=
  (fullFns.take 128).zipWith (fun f b => (⟨f.name, f.as, f.rs⟩, b)) slice5Bounds

/-- Slice 6 sub-module (`[128, 147)`, `19` functions). -/
def slice6Mod : Module := { fns := (fullFns.drop 128).take 19 }

compile_linked_chunks! cert6 x64Target x64Layout x64LegalTarget x64LabelClean
  slice6Mod 4 (ext := ext5) (maxDirs := 450)

end LeanQbe.T.Amd64.KissatFullCert6
