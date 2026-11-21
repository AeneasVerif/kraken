module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Examples.Kissat.FullM3
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Kissat.FullM3

/-!
# Kissat M3 (`FullM3`) Certificate Slice 9/17 on SysV x64

Kernel-checked native compilation certificate (`cert9`) for slice `[119, 129)` (`10`
functions) of `LeanQbe.T.Examples.Kissat.FullM3.m3Fns` on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatM3Cert9

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Examples.Kissat.FullM3

/-- Exported stack bounds for `[0, 119)` verified against `cert1..8` by `KissatM3Cert`. -/
def slice8Bounds : List Nat :=
  [8, 8, 40, 56, 72, 104, 104, 152, 8, 8, 8, 8, 8, 8, 72, 168, 40, 88, 56, 120, 8, 72, 24, 8, 88,
   8, 8, 56, 72, 24, 168, 232, 56, 152, 8, 8, 8, 56, 8, 8, 72, 232, 136, 296, 344, 24, 8, 504,
   616, 664, 680, 24, 40, 8, 72, 120, 8, 40, 184, 232, 280, 424, 776, 40, 136, 8, 200, 280, 248,
   8, 8, 120, 8, 72, 120, 152, 360, 440, 8, 264, 408, 120, 840, 888, 168, 184, 728, 88, 8, 88,
   200, 248, 136, 8, 200, 8, 24, 8, 8, 216, 40, 72, 8, 200, 984, 88, 1048, 104, 360, 392, 728,
   984, 1064, 376, 728, 328, 24, 152, 328]

/-- Exported callee signatures and stack bounds for prefix `[0, 119)`. -/
def ext8 : List (SigEntry × Nat) :=
  (m3Fns.take 119).zipWith (fun f b => (⟨f.name, f.as, f.rs⟩, b)) slice8Bounds

/-- Slice 9 sub-module (`[119, 129)`, `10` functions). -/
def slice9Mod : Module := { fns := (m3Fns.drop 119).take 10 }

compile_linked_chunks! cert9 x64Target x64Layout x64LegalTarget x64LabelClean
  slice9Mod 4 (ext := ext8) (maxDirs := 450)

end LeanQbe.T.Amd64.KissatM3Cert9
