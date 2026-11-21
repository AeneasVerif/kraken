module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Kissat.Full
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.Full

/-!
# Stage 4 (`D-Full`) Kissat Native Certificate Slice 4/7 on AAPCS64 Arm64

Kernel-checked native compilation certificate (`cert4`) for slice `[88, 111)` (`23` functions) of
`LeanQbe.T.Examples.Kissat.Full.fullFns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatFullCert4

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.Full

/-- Exported stack bounds for `[0, 88)` verified against `cert1..3` by `KissatFullCert`. -/
def slice3Bounds : List Nat :=
  [16, 16, 48, 64, 80, 128, 112, 176, 16, 16, 16, 16, 16, 16, 80, 176, 16, 32, 32, 64, 16, 48, 48,
   16, 80, 16, 16, 16, 32, 16, 160, 240, 16, 96, 16, 16, 16, 64, 16, 16, 80, 208, 144, 304, 352, 16,
   16, 384, 432, 448, 16, 16, 16, 80, 128, 16, 16, 112, 208, 288, 448, 544, 16, 80, 16, 144, 288,
   256, 16, 16, 128, 16, 80, 128, 160, 336, 432, 16, 272, 448, 80, 624, 672, 112, 128, 528, 64, 16]

/-- Exported callee signatures and stack bounds for prefix `[0, 88)`. -/
def ext3 : List (SigEntry × Nat) :=
  (fullFns.take 88).zipWith (fun f b => (⟨f.name, f.as, f.rs⟩, b)) slice3Bounds

/-- Slice 4 sub-module (`[88, 111)`, `23` functions). -/
def slice4Mod : Module := { fns := (fullFns.drop 88).take 23 }

compile_linked_chunks! cert4 armTarget armLayout armLegalTarget armLabelClean
  slice4Mod 4 (ext := ext3) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatFullCert4
