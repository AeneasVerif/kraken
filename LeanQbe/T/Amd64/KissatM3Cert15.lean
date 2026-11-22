module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Examples.Kissat.FullM3
public import LeanQbe.T.Amd64.KissatM3Bounds
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Kissat.FullM3
meta import LeanQbe.T.Amd64.KissatM3Bounds

/-!
# Kissat M3 (`FullM3`) Certificate Slice 15/21 on SysV x64

Kernel-checked native compilation certificate (`cert15`) for slice `[175, 183)` (`8`
functions) of `LeanQbe.T.Examples.Kissat.FullM3.m3Fns` on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatM3Cert15

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Examples.Kissat.FullM3
open LeanQbe.T.Amd64.KissatM3Bounds

/-- Slice 15 sub-module (`[175, 183)`, `8` functions). -/
def slice15Mod : Module := { fns := (m3Fns.drop 175).take 8 }

compile_linked_chunks! cert15 x64Target x64Layout x64LegalTarget x64LabelClean
  slice15Mod 4 (ext := m3ExtPrefix 175) (maxDirs := 450)

end LeanQbe.T.Amd64.KissatM3Cert15
