module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Amd64.KissatM4Bounds
public import LeanQbe.T.Examples.Kissat.FullM4
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Amd64.KissatM4Bounds
meta import LeanQbe.T.Examples.Kissat.FullM4

/-!
# KissatM4 Certificate Slice 19/27 on SysV x64

Kernel-checked compilation cert (`cert19`) for slice `[164, 170)` (`6` functions) of
`LeanQbe.T.Examples.Kissat.FullM4.m4Fns` on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatM4Cert19

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Amd64.KissatM4Bounds LeanQbe.T.Examples.Kissat.FullM4

/-- Slice 19 sub-module (`[164, 170)`, `6` functions). -/
def slice19Mod : Module := { fns := (m4Fns.drop 164).take 6 }

compile_linked_chunks! cert19 x64Target x64Layout x64LegalTarget x64LabelClean
  slice19Mod 4 (ext := m4ExtPrefix 164) (maxDirs := 450)

end LeanQbe.T.Amd64.KissatM4Cert19
