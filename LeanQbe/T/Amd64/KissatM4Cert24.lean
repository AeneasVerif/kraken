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
# KissatM4 Certificate Slice 24/27 on SysV x64

Kernel-checked compilation cert (`cert24`) for slice `[188, 197)` (`9` functions) of
`LeanQbe.T.Examples.Kissat.FullM4.m4Fns` on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatM4Cert24

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Amd64.KissatM4Bounds LeanQbe.T.Examples.Kissat.FullM4

/-- Slice 24 sub-module (`[188, 197)`, `9` functions). -/
def slice24Mod : Module := { fns := (m4Fns.drop 188).take 9 }

compile_linked_chunks! cert24 x64Target x64Layout x64LegalTarget x64LabelClean
  slice24Mod 4 (ext := m4ExtPrefix 188) (maxDirs := 450)

end LeanQbe.T.Amd64.KissatM4Cert24
