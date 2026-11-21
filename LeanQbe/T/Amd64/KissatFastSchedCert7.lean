module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Examples.Kissat.FullFastSched
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Kissat.FullFastSched

/-!
# Kissat M2 Fast-Scheduler (`FullFastSched`) Certificate Slice 7/7 on SysV x64

Kernel-checked native compilation certificate (`cert7`) for slice `[152, 173)` (`21`
functions) of `LeanQbe.T.Examples.Kissat.FullFastSched.schedSplicedFns` on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatFastSchedCert7

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Examples.Kissat.FullFastSched

/-- Exported stack bounds for `[0, 152)` verified against `cert1..6` by
`KissatFastSchedCert`. -/
def slice6Bounds : List Nat :=
  [8, 8, 40, 56, 72, 120, 104, 168, 24, 8, 8, 8, 24, 40, 120, 232, 56, 104, 88, 152, 8, 88, 40, 24,
   136, 56, 24, 72, 88, 40, 216, 296, 72, 168, 8, 40, 8, 56, 8, 8, 104, 248, 136, 360, 408, 40, 40,
   440, 488, 504, 40, 56, 8, 72, 120, 8, 56, 232, 312, 344, 504, 600, 72, 136, 8, 264, 344, 312, 24,
   24, 168, 8, 72, 120, 200, 376, 472, 8, 328, 504, 136, 680, 728, 216, 264, 584, 104, 24, 88, 216,
   280, 168, 8, 264, 24, 40, 24, 24, 280, 56, 88, 8, 248, 856, 104, 936, 120, 424, 456, 552, 856,
   936, 440, 568, 392, 40, 168, 392, 584, 664, 104, 312, 568, 408, 392, 616, 568, 536, 8, 328, 104,
   24, 200, 8, 296, 408, 488, 616, 40, 200, 168, 40, 232, 408, 632, 344, 472, 536, 40, 56, 152, 88]

/-- Exported callee signatures and stack bounds for prefix `[0, 152)`. -/
def ext6 : List (SigEntry × Nat) :=
  (schedSplicedFns.take 152).zipWith (fun f b => (⟨f.name, f.as, f.rs⟩, b)) slice6Bounds

/-- Slice 7 sub-module (`[152, 173)`, `21` functions). -/
def slice7Mod : Module := { fns := schedSplicedFns.drop 152 }

compile_linked_chunks! cert7 x64Target x64Layout x64LegalTarget x64LabelClean
  slice7Mod 4 (ext := ext6) (maxDirs := 450)

end LeanQbe.T.Amd64.KissatFastSchedCert7
