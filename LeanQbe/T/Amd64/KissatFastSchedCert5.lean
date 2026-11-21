module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Examples.Kissat.FullFastSched
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Kissat.FullFastSched

/-!
# Kissat M2 Fast-Scheduler (`FullFastSched`) Certificate Slice 5/7 on SysV x64

Kernel-checked native compilation certificate (`cert5`) for slice `[107, 130)` (`23`
functions) of `LeanQbe.T.Examples.Kissat.FullFastSched.schedSplicedFns` on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatFastSchedCert5

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Examples.Kissat.FullFastSched

/-- Exported stack bounds for `[0, 107)` verified against `cert1..4` by
`KissatFastSchedCert`. -/
def slice4Bounds : List Nat :=
  [8, 8, 40, 56, 72, 104, 104, 152, 8, 8, 8, 8, 8, 8, 72, 168, 40, 88, 56, 120, 8, 72, 24, 8, 88,
   8, 8, 56, 72, 24, 168, 232, 56, 152, 8, 8, 8, 56, 8, 8, 72, 232, 136, 296, 344, 24, 8, 376,
   408, 424, 24, 40, 8, 72, 120, 8, 40, 184, 232, 280, 424, 520, 40, 104, 8, 200, 280, 248, 8, 8,
   120, 8, 72, 120, 152, 360, 440, 8, 264, 408, 120, 584, 632, 168, 184, 472, 88, 8, 88, 200,
   248, 136, 8, 200, 8, 24, 8, 8, 216, 40, 72, 8, 200, 728, 88, 792, 104]

/-- Exported callee signatures and stack bounds for prefix `[0, 107)`. -/
def ext4 : List (SigEntry × Nat) :=
  (schedSplicedFns.take 107).zipWith (fun f b => (⟨f.name, f.as, f.rs⟩, b)) slice4Bounds

/-- Slice 5 sub-module (`[107, 130)`, `23` functions). -/
def slice5Mod : Module := { fns := (schedSplicedFns.drop 107).take 23 }

compile_linked_chunks! cert5 x64Target x64Layout x64LegalTarget x64LabelClean
  slice5Mod 4 (ext := ext4) (maxDirs := 450)

end LeanQbe.T.Amd64.KissatFastSchedCert5
