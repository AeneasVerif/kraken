module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Kissat.Full
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.Full

/-!
# Stage 4 (`D-Full`) Kissat Native Certificate Slice 2/7 on AAPCS64 Arm64

Kernel-checked native compilation certificate (`cert2`) for slice `[38, 67)` (`29` functions) of
`LeanQbe.T.Examples.Kissat.Full.fullFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatFullCert2

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.Full

/-- Exported stack bounds for `[0, 38)` verified against `cert1` by `KissatFullCert`. -/
def slice1Bounds : List Nat :=
  [16, 16, 48, 64, 80, 128, 112, 176, 16, 16, 16, 16, 16, 16, 80, 176, 16, 32, 32, 64, 16, 48, 48,
   16, 64, 16, 16, 16, 32, 16, 160, 240, 16, 112, 16, 16, 16, 64]

/-- Exported callee signatures and stack bounds for prefix `[0, 38)`. -/
def ext1 : List (SigEntry × Nat) :=
  (fullFns.take 38).zipWith (fun f b => (⟨f.name, f.as, f.rs⟩, b)) slice1Bounds

/-- Slice 2 sub-module (`[38, 67)`, `29` functions). -/
def slice2Mod : Module := { fns := (fullFns.drop 38).take 29 }

compile_linked_chunks! cert2 armTarget armLayout armLegalTarget armLabelClean
  slice2Mod 4 (ext := ext1) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatFullCert2
