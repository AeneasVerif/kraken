module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Kissat.FullM3
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.FullM3

/-!
# Kissat M3 (`FullM3`) Certificate Slice 5/17 on AAPCS64 Arm64

Kernel-checked native compilation certificate (`cert5`) for slice `[80, 91)` (`11`
functions) of `LeanQbe.T.Examples.Kissat.FullM3.m3Fns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM3Cert5

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.FullM3

/-- Exported stack bounds for `[0, 80)` verified against `cert1..4` by `KissatM3Cert`. -/
def slice4Bounds : List Nat :=
  [16, 16, 48, 64, 80, 128, 112, 176, 16, 16, 16, 16, 16, 16, 80, 176, 16, 32, 32, 64, 16, 48, 48,
   16, 80, 16, 16, 16, 32, 16, 160, 240, 16, 96, 16, 16, 16, 64, 16, 16, 80, 208, 144, 304, 352, 16,
   16, 480, 592, 672, 688, 16, 16, 16, 80, 128, 16, 16, 128, 208, 288, 448, 784, 16, 80, 16, 144,
   288, 256, 16, 16, 128, 16, 80, 128, 160, 336, 432, 16, 272]

/-- Exported callee signatures and stack bounds for prefix `[0, 80)`. -/
def ext4 : List (SigEntry × Nat) :=
  (m3Fns.take 80).zipWith (fun f b => (⟨f.name, f.as, f.rs⟩, b)) slice4Bounds

/-- Slice 5 sub-module (`[80, 91)`, `11` functions). -/
def slice5Mod : Module := { fns := (m3Fns.drop 80).take 11 }

compile_linked_chunks! cert5 armTarget armLayout armLegalTarget armLabelClean
  slice5Mod 4 (ext := ext4) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatM3Cert5
