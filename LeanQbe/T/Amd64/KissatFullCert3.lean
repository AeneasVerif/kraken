module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Examples.Kissat.Full
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Kissat.Full

/-!
# Stage 4 (`D-Full`) Kissat Native Certificate Slice 3/7 on SysV x64

Kernel-checked native compilation certificate (`cert3`) for slice `[67, 88)` (`21` functions) of
`LeanQbe.T.Examples.Kissat.Full.fullFns` on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatFullCert3

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Examples.Kissat.Full

/-- Exported stack bounds for `[0, 67)` verified against `cert1..2` by `KissatFullCert`. -/
def slice2Bounds : List Nat :=
  [8, 8, 40, 56, 72, 120, 104, 168, 24, 8, 8, 8, 24, 40, 120, 232, 56, 104, 88, 152, 8, 88, 40, 24,
   136, 56, 24, 72, 88, 40, 216, 296, 72, 168, 8, 40, 8, 56, 8, 8, 104, 248, 136, 360, 408, 40, 40,
   440, 488, 504, 40, 56, 8, 72, 120, 8, 56, 232, 312, 344, 504, 600, 72, 136, 8, 264, 344]

/-- Exported callee signatures and stack bounds for prefix `[0, 67)`. -/
def ext2 : List (SigEntry × Nat) :=
  (fullFns.take 67).zipWith (fun f b => (⟨f.name, f.as, f.rs⟩, b)) slice2Bounds

/-- Slice 3 sub-module (`[67, 88)`, `21` functions). -/
def slice3Mod : Module := { fns := (fullFns.drop 67).take 21 }

compile_linked_chunks! cert3 x64Target x64Layout x64LegalTarget x64LabelClean
  slice3Mod 4 (ext := ext2) (maxDirs := 450)

end LeanQbe.T.Amd64.KissatFullCert3
