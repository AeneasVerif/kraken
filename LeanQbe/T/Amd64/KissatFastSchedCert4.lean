module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Examples.Kissat.FullFastSched
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Kissat.FullFastSched

/-!
# Kissat M2 Fast-Scheduler (`FullFastSched`) Certificate Slice 4/7 on SysV x64

Kernel-checked native compilation certificate (`cert4`) for slice `[84, 107)` (`23`
functions) of `LeanQbe.T.Examples.Kissat.FullFastSched.schedSplicedFns` on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatFastSchedCert4

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Examples.Kissat.FullFastSched

/-- Exported stack bounds for `[0, 84)` verified against `cert1..3` by
`KissatFastSchedCert`. -/
def slice3Bounds : List Nat :=
  [8, 8, 40, 56, 72, 120, 104, 168, 24, 8, 8, 8, 24, 40, 120, 232, 56, 104, 88, 152, 8, 88, 40, 24,
   136, 56, 24, 72, 88, 40, 216, 296, 72, 168, 8, 40, 8, 56, 8, 8, 104, 248, 136, 360, 408, 40, 40,
   440, 488, 504, 40, 56, 8, 72, 120, 8, 56, 232, 312, 344, 504, 600, 72, 136, 8, 264, 344, 312, 24,
   24, 168, 8, 72, 120, 200, 376, 472, 8, 328, 504, 136, 680, 728, 216]

/-- Exported callee signatures and stack bounds for prefix `[0, 84)`. -/
def ext3 : List (SigEntry × Nat) :=
  (schedSplicedFns.take 84).zipWith (fun f b => (⟨f.name, f.as, f.rs⟩, b)) slice3Bounds

/-- Slice 4 sub-module (`[84, 107)`, `23` functions). -/
def slice4Mod : Module := { fns := (schedSplicedFns.drop 84).take 23 }

compile_linked_chunks! cert4 x64Target x64Layout x64LegalTarget x64LabelClean
  slice4Mod 4 (ext := ext3) (maxDirs := 450)

end LeanQbe.T.Amd64.KissatFastSchedCert4
