module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Examples.Kissat.FullM3
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Kissat.FullM3

/-!
# Kissat M3 (`FullM3`) Certificate Slice 8/17 on SysV x64

Kernel-checked native compilation certificate (`cert8`) for slice `[111, 119)` (`8`
functions) of `LeanQbe.T.Examples.Kissat.FullM3.m3Fns` on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatM3Cert8

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Examples.Kissat.FullM3

/-- Exported stack bounds for `[0, 111)` verified against `cert1..7` by `KissatM3Cert`. -/
def slice7Bounds : List Nat :=
  [8, 8, 40, 56, 72, 120, 104, 168, 24, 8, 8, 8, 24, 40, 120, 232, 56, 104, 88, 152, 8, 88, 40, 24,
   136, 56, 24, 72, 88, 40, 216, 296, 72, 168, 8, 40, 8, 56, 8, 8, 104, 248, 136, 360, 408, 40, 40,
   600, 728, 808, 824, 40, 56, 8, 72, 120, 8, 56, 232, 312, 344, 504, 920, 72, 184, 8, 264, 344,
   312, 24, 24, 168, 8, 72, 120, 200, 376, 472, 8, 328, 504, 136, 1000, 1048, 216, 264, 904, 104,
   24, 88, 216, 280, 168, 8, 264, 24, 40, 24, 24, 280, 56, 88, 8, 248, 1176, 104, 1256, 120, 424,
   456, 872]

/-- Exported callee signatures and stack bounds for prefix `[0, 111)`. -/
def ext7 : List (SigEntry × Nat) :=
  (m3Fns.take 111).zipWith (fun f b => (⟨f.name, f.as, f.rs⟩, b)) slice7Bounds

/-- Slice 8 sub-module (`[111, 119)`, `8` functions). -/
def slice8Mod : Module := { fns := (m3Fns.drop 111).take 8 }

compile_linked_chunks! cert8 x64Target x64Layout x64LegalTarget x64LabelClean
  slice8Mod 4 (ext := ext7) (maxDirs := 450)

end LeanQbe.T.Amd64.KissatM3Cert8
