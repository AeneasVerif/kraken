module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Examples.Kissat.FullM3
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Kissat.FullM3

/-!
# Kissat M3 (`FullM3`) Certificate Slice 10/17 on SysV x64

Kernel-checked native compilation certificate (`cert10`) for slice `[129, 140)` (`11`
functions) of `LeanQbe.T.Examples.Kissat.FullM3.m3Fns` on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatM3Cert10

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Examples.Kissat.FullM3

/-- Exported stack bounds for `[0, 129)` verified against `cert1..9` by `KissatM3Cert`. -/
def slice9Bounds : List Nat :=
  [8, 8, 40, 56, 72, 104, 104, 152, 8, 8, 8, 8, 8, 8, 72, 168, 40, 88, 56, 120, 8, 72, 24, 8, 88,
   8, 8, 56, 72, 24, 168, 232, 56, 152, 8, 8, 8, 56, 8, 8, 72, 232, 136, 296, 344, 24, 8, 504,
   616, 664, 680, 24, 40, 8, 72, 120, 8, 40, 184, 232, 280, 424, 776, 40, 136, 8, 200, 280, 248,
   8, 8, 120, 8, 72, 120, 152, 360, 440, 8, 264, 408, 120, 840, 888, 168, 184, 728, 88, 8, 88,
   200, 248, 136, 8, 200, 8, 24, 8, 8, 216, 40, 72, 8, 200, 984, 88, 1048, 104, 360, 392, 728,
   984, 1064, 376, 728, 328, 24, 152, 328, 760, 856, 72, 248, 744, 344, 344, 776, 760, 712]

/-- Exported callee signatures and stack bounds for prefix `[0, 129)`. -/
def ext9 : List (SigEntry × Nat) :=
  (m3Fns.take 129).zipWith (fun f b => (⟨f.name, f.as, f.rs⟩, b)) slice9Bounds

/-- Slice 10 sub-module (`[129, 140)`, `11` functions). -/
def slice10Mod : Module := { fns := (m3Fns.drop 129).take 11 }

compile_linked_chunks! cert10 x64Target x64Layout x64LegalTarget x64LabelClean
  slice10Mod 4 (ext := ext9) (maxDirs := 450)

end LeanQbe.T.Amd64.KissatM3Cert10
