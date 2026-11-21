module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Examples.Kissat.Full
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Kissat.Full

/-!
# Stage 4 (`D-Full`) Kissat Native Certificate Slice 2/7 on SysV x64

Kernel-checked native compilation certificate (`cert2`) for slice `[38, 67)` (`29` functions) of
`LeanQbe.T.Examples.Kissat.Full.fullFns` on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatFullCert2

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Examples.Kissat.Full

/-- Exported stack bounds for `[0, 38)` verified against `cert1` by `KissatFullCert`. -/
def slice1Bounds : List Nat :=
  [8, 8, 40, 56, 72, 120, 104, 168, 24, 8, 8, 8, 24, 40, 120, 232, 56, 104, 88, 152, 8, 88, 40,
   24, 120, 56, 24, 72, 88, 40, 216, 296, 72, 168, 8, 40, 8, 56]

/-- Exported callee signatures and stack bounds for prefix `[0, 38)`. -/
def ext1 : List (SigEntry × Nat) :=
  (fullFns.take 38).zipWith (fun f b => (⟨f.name, f.as, f.rs⟩, b)) slice1Bounds

/-- Slice 2 sub-module (`[38, 67)`, `29` functions). -/
def slice2Mod : Module := { fns := (fullFns.drop 38).take 29 }

compile_linked_chunks! cert2 x64Target x64Layout x64LegalTarget x64LabelClean
  slice2Mod 4 (ext := ext1) (maxDirs := 450)

end LeanQbe.T.Amd64.KissatFullCert2
