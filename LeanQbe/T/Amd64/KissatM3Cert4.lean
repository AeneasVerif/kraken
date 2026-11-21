module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Examples.Kissat.FullM3
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Kissat.FullM3

/-!
# Kissat M3 (`FullM3`) Certificate Slice 4/17 on SysV x64

Kernel-checked native compilation certificate (`cert4`) for slice `[68, 80)` (`12`
functions) of `LeanQbe.T.Examples.Kissat.FullM3.m3Fns` on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatM3Cert4

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Examples.Kissat.FullM3

/-- Exported stack bounds for `[0, 68)` verified against `cert1..3` by `KissatM3Cert`. -/
def slice3Bounds : List Nat :=
  [8, 8, 40, 56, 72, 104, 104, 152, 8, 8, 8, 8, 8, 8, 72, 168, 40, 88, 56, 120, 8, 72, 24, 8, 88,
   8, 8, 56, 72, 24, 168, 232, 56, 152, 8, 8, 8, 56, 8, 8, 72, 232, 136, 296, 344, 24, 8, 504,
   616, 664, 680, 24, 40, 8, 72, 120, 8, 40, 184, 232, 280, 424, 776, 40, 136, 8, 200, 280]

/-- Exported callee signatures and stack bounds for prefix `[0, 68)`. -/
def ext3 : List (SigEntry × Nat) :=
  (m3Fns.take 68).zipWith (fun f b => (⟨f.name, f.as, f.rs⟩, b)) slice3Bounds

/-- Slice 4 sub-module (`[68, 80)`, `12` functions). -/
def slice4Mod : Module := { fns := (m3Fns.drop 68).take 12 }

compile_linked_chunks! cert4 x64Target x64Layout x64LegalTarget x64LabelClean
  slice4Mod 4 (ext := ext3) (maxDirs := 450)

end LeanQbe.T.Amd64.KissatM3Cert4
