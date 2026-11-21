module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Kissat.FullM3
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.FullM3

/-!
# Kissat M3 (`FullM3`) Certificate Slice 9/17 on AAPCS64 Arm64

Kernel-checked native compilation certificate (`cert9`) for slice `[119, 129)` (`10`
functions) of `LeanQbe.T.Examples.Kissat.FullM3.m3Fns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM3Cert9

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.FullM3

/-- Exported stack bounds for `[0, 119)` verified against `cert1..8` by `KissatM3Cert`. -/
def slice8Bounds : List Nat :=
  [16, 16, 48, 64, 80, 128, 112, 176, 16, 16, 16, 16, 16, 16, 80, 176, 16, 32, 32, 64, 16, 48, 48,
   16, 80, 16, 16, 16, 32, 16, 160, 240, 16, 96, 16, 16, 16, 64, 16, 16, 80, 208, 144, 304, 352, 16,
   16, 480, 592, 672, 688, 16, 16, 16, 80, 128, 16, 16, 128, 208, 288, 448, 784, 16, 80, 16, 144,
   288, 256, 16, 16, 128, 16, 80, 128, 160, 336, 432, 16, 272, 448, 80, 864, 912, 112, 128, 768, 64,
   16, 96, 208, 256, 80, 16, 176, 16, 16, 16, 16, 224, 16, 48, 16, 192, 1040, 96, 1120, 48, 368,
   400, 736, 1040, 1136, 336, 752, 336, 16, 96, 336]

/-- Exported callee signatures and stack bounds for prefix `[0, 119)`. -/
def ext8 : List (SigEntry × Nat) :=
  (m3Fns.take 119).zipWith (fun f b => (⟨f.name, f.as, f.rs⟩, b)) slice8Bounds

/-- Slice 9 sub-module (`[119, 129)`, `10` functions). -/
def slice9Mod : Module := { fns := (m3Fns.drop 119).take 10 }

compile_linked_chunks! cert9 armTarget armLayout armLegalTarget armLabelClean
  slice9Mod 4 (ext := ext8) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatM3Cert9
