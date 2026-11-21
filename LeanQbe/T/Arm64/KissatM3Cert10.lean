module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Arm64.TargLemmas
public import LeanQbe.T.Examples.Kissat.FullM3
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.FullM3

/-!
# Kissat M3 (`FullM3`) Certificate Slice 10/17 on AAPCS64 Arm64

Kernel-checked native compilation certificate (`cert10`) for slice `[129, 140)` (`11`
functions) of `LeanQbe.T.Examples.Kissat.FullM3.m3Fns` on `armTarget`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64.KissatM3Cert10

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.FullM3

/-- Exported stack bounds for `[0, 129)` verified against `cert1..9` by `KissatM3Cert`. -/
def slice9Bounds : List Nat :=
  [16, 16, 48, 64, 80, 112, 112, 160, 16, 16, 16, 16, 16, 16, 80, 176, 16, 32, 32, 64, 16, 48,
   32, 16, 64, 16, 16, 16, 32, 16, 144, 240, 16, 80, 16, 16, 16, 64, 16, 16, 80, 192, 144, 304,
   352, 16, 16, 464, 576, 624, 640, 16, 16, 16, 80, 128, 16, 16, 112, 208, 288, 432, 736, 16, 80,
   16, 112, 288, 256, 16, 16, 112, 16, 80, 128, 144, 336, 416, 16, 272, 416, 64, 800, 848, 112,
   128, 688, 64, 16, 96, 208, 256, 64, 16, 160, 16, 16, 16, 16, 224, 16, 48, 16, 176, 944, 96,
   1008, 32, 368, 400, 688, 944, 1024, 320, 688, 336, 16, 80, 336, 720, 816, 16, 160, 704, 320,
   352, 736, 720, 672]

/-- Exported callee signatures and stack bounds for prefix `[0, 129)`. -/
def ext9 : List (SigEntry × Nat) :=
  (m3Fns.take 129).zipWith (fun f b => (⟨f.name, f.as, f.rs⟩, b)) slice9Bounds

/-- Slice 10 sub-module (`[129, 140)`, `11` functions). -/
def slice10Mod : Module := { fns := (m3Fns.drop 129).take 11 }

compile_linked_chunks! cert10 armTarget armLayout armLegalTarget armLabelClean
  slice10Mod 4 (ext := ext9) (maxDirs := 450)

end LeanQbe.T.Arm64.KissatM3Cert10
