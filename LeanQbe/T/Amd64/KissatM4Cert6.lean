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
# KissatM4 Certificate Slice 6/27 on SysV x64

Kernel-checked compilation cert (`cert6`) for slice `[48, 60)` (`12` functions) of
`LeanQbe.T.Examples.Kissat.FullM4.m4Fns` on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatM4Cert6

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Amd64.KissatM4Bounds LeanQbe.T.Examples.Kissat.FullM4

/-- Slice 6 sub-module (`[48, 60)`, `12` functions). -/
def slice6Mod : Module := { fns := (m4Fns.drop 48).take 12 }

compile_linked_chunks! cert6 x64Target x64Layout x64LegalTarget x64LabelClean
  slice6Mod 4 (ext := m4ExtPrefix 48) (maxDirs := 450)

end LeanQbe.T.Amd64.KissatM4Cert6
