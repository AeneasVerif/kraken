module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Examples.Kissat.FullM3
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Kissat.FullM3

/-!
# Kissat M3 (`FullM3`) Certificate Slice 12/17 on SysV x64

Kernel-checked native compilation certificate (`cert12`) for slice `[152, 158)` (`6`
functions) of `LeanQbe.T.Examples.Kissat.FullM3.m3Fns` on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatM3Cert12

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Examples.Kissat.FullM3

/-- Exported stack bounds for `[0, 152)` verified against `cert1..11` by `KissatM3Cert`. -/
def slice11Bounds : List Nat :=
  [8, 8, 40, 56, 72, 104, 104, 152, 8, 8, 8, 8, 8, 8, 72, 168, 40, 88, 56, 120, 8, 72, 24, 8, 88,
   8, 8, 56, 72, 24, 168, 232, 56, 152, 8, 8, 8, 56, 8, 8, 72, 232, 136, 296, 344, 24, 8, 504,
   616, 664, 680, 24, 40, 8, 72, 120, 8, 40, 184, 232, 280, 424, 776, 40, 136, 8, 200, 280, 248,
   8, 8, 120, 8, 72, 120, 152, 360, 440, 8, 264, 408, 120, 840, 888, 168, 184, 728, 88, 8, 88,
   200, 248, 136, 8, 200, 8, 24, 8, 8, 216, 40, 72, 8, 200, 984, 88, 1048, 104, 360, 392, 728,
   984, 1064, 376, 728, 328, 24, 152, 328, 760, 856, 72, 248, 744, 344, 344, 776, 760, 712, 8, 8,
   56, 8, 8, 8, 56, 152, 40, 104, 24, 200, 24, 56, 72, 8, 264, 88, 8, 200, 8, 296, 440]

/-- Exported callee signatures and stack bounds for prefix `[0, 152)`. -/
def ext11 : List (SigEntry × Nat) :=
  (m3Fns.take 152).zipWith (fun f b => (⟨f.name, f.as, f.rs⟩, b)) slice11Bounds

/-- Slice 12 sub-module (`[152, 158)`, `6` functions). -/
def slice12Mod : Module := { fns := (m3Fns.drop 152).take 6 }

compile_linked_chunks! cert12 x64Target x64Layout x64LegalTarget x64LabelClean
  slice12Mod 4 (ext := ext11) (maxDirs := 450)

end LeanQbe.T.Amd64.KissatM3Cert12
