module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Examples.Kissat.FullM3
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Kissat.FullM3

/-!
# Kissat M3 (`FullM3`) Certificate Slice 3/17 on SysV x64

Kernel-checked native compilation certificate (`cert3`) for slice `[59, 68)` (`9`
functions) of `LeanQbe.T.Examples.Kissat.FullM3.m3Fns` on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatM3Cert3

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Examples.Kissat.FullM3

/-- Exported stack bounds for `[0, 59)` verified against `cert1..2` by `KissatM3Cert`. -/
def slice2Bounds : List Nat :=
  [8, 8, 40, 56, 72, 104, 104, 152, 8, 8, 8, 8, 8, 8, 72, 168, 40, 88, 56, 120, 8, 72, 24, 8, 88,
   8, 8, 56, 72, 24, 168, 232, 56, 152, 8, 8, 8, 56, 8, 8, 72, 232, 136, 296, 344, 24, 8, 504,
   616, 664, 680, 24, 40, 8, 72, 120, 8, 40, 184]

/-- Exported callee signatures and stack bounds for prefix `[0, 59)`. -/
def ext2 : List (SigEntry × Nat) :=
  (m3Fns.take 59).zipWith (fun f b => (⟨f.name, f.as, f.rs⟩, b)) slice2Bounds

/-- Slice 3 sub-module (`[59, 68)`, `9` functions). -/
def slice3Mod : Module := { fns := (m3Fns.drop 59).take 9 }

compile_linked_chunks! cert3 x64Target x64Layout x64LegalTarget x64LabelClean
  slice3Mod 4 (ext := ext2) (maxDirs := 450)

end LeanQbe.T.Amd64.KissatM3Cert3
