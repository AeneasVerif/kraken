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
  [8, 8, 40, 56, 72, 104, 104, 152, 8, 8, 8, 8, 8, 8, 72, 168, 40, 88, 56, 120, 8, 72, 24, 8, 88,
   8, 8, 56, 72, 24, 168, 232, 56, 152, 8, 8, 8, 56, 8, 8, 72, 232, 136, 296, 344, 24, 8, 504,
   616, 664, 680, 24, 40, 8, 72, 120, 8, 40, 184, 232, 280, 424, 776, 40, 136, 8, 200, 280, 248,
   8, 8, 120, 8, 72, 120, 152, 360, 440, 8, 264, 408, 120, 840, 888, 168, 184, 728, 88, 8, 88,
   200, 248, 136, 8, 200, 8, 24, 8, 8, 216, 40, 72, 8, 200, 984, 88, 1048, 104, 360, 392, 728]

/-- Exported callee signatures and stack bounds for prefix `[0, 111)`. -/
def ext7 : List (SigEntry × Nat) :=
  (m3Fns.take 111).zipWith (fun f b => (⟨f.name, f.as, f.rs⟩, b)) slice7Bounds

/-- Slice 8 sub-module (`[111, 119)`, `8` functions). -/
def slice8Mod : Module := { fns := (m3Fns.drop 111).take 8 }

compile_linked_chunks! cert8 x64Target x64Layout x64LegalTarget x64LabelClean
  slice8Mod 4 (ext := ext7) (maxDirs := 450)

end LeanQbe.T.Amd64.KissatM3Cert8
