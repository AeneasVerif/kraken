module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Examples.Kissat.FullM3
public import LeanQbe.T.Amd64.KissatM3Bounds
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Kissat.FullM3
meta import LeanQbe.T.Amd64.KissatM3Bounds

/-!
# Kissat M3 (`FullM3`) Certificate Slice 8/21 on SysV x64

Kernel-checked native compilation certificate (`cert8`) for slice `[111, 119)` (`8`
functions) of `LeanQbe.T.Examples.Kissat.FullM3.m3Fns` on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatM3Cert8

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Examples.Kissat.FullM3
open LeanQbe.T.Amd64.KissatM3Bounds

/-- Slice 8 sub-module (`[111, 119)`, `8` functions). -/
def slice8Mod : Module := { fns := (m3Fns.drop 111).take 8 }

compile_linked_chunks! cert8 x64Target x64Layout x64LegalTarget x64LabelClean
  slice8Mod 4 (ext := m3ExtPrefix 111) (maxDirs := 450)

end LeanQbe.T.Amd64.KissatM3Cert8
