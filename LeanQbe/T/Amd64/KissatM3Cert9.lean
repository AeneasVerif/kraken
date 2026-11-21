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
  [8, 8, 40, 56, 72, 120, 104, 168, 24, 8, 8, 8, 24, 40, 120, 232, 56, 104, 88, 152, 8, 88, 40, 24,
   136, 56, 24, 72, 88, 40, 216, 296, 72, 168, 8, 40, 8, 56, 8, 8, 104, 248, 136, 360, 408, 40, 40,
   600, 728, 808, 824, 40, 56, 8, 72, 120, 8, 56, 232, 312, 344, 504, 920, 72, 184, 8, 264, 344,
   312, 24, 24, 168, 8, 72, 120, 200, 376, 472, 8, 328, 504, 136, 1000, 1048, 216, 264, 904, 104,
   24, 88, 216, 280, 168, 8, 264, 24, 40, 24, 24, 280, 56, 88, 8, 248, 1176, 104, 1256, 120, 424,
   456, 872, 1176, 1272, 440, 888, 392, 40, 168, 392]

/-- Exported callee signatures and stack bounds for prefix `[0, 119)`. -/
def ext8 : List (SigEntry × Nat) :=
  (m3Fns.take 119).zipWith (fun f b => (⟨f.name, f.as, f.rs⟩, b)) slice8Bounds

/-- Slice 9 sub-module (`[119, 129)`, `10` functions). -/
def slice9Mod : Module := { fns := (m3Fns.drop 119).take 10 }

compile_linked_chunks! cert9 x64Target x64Layout x64LegalTarget x64LabelClean
  slice9Mod 4 (ext := ext8) (maxDirs := 450)

end LeanQbe.T.Amd64.KissatM3Cert9
