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
# KissatM4 Certificate Slice 22/27 on SysV x64

Kernel-checked compilation cert (`cert22`) for slice `[183, 184)` (`1` functions) of
`LeanQbe.T.Examples.Kissat.FullM4.m4Fns` on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatM4Cert22

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Amd64.KissatM4Bounds LeanQbe.T.Examples.Kissat.FullM4

/-- Slice 22 sub-module (`[183, 184)`, `1` functions). -/
def slice22Mod : Module := { fns := (m4Fns.drop 183).take 1 }

compile_linked_chunks! cert22 x64Target x64Layout x64LegalTarget x64LabelClean
  slice22Mod 4 (ext := m4ExtPrefix 183) (maxDirs := 450)

end LeanQbe.T.Amd64.KissatM4Cert22
