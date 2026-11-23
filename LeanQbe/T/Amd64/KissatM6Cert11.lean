module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Amd64.KissatM6Bounds
public import LeanQbe.T.Examples.Kissat.FullM6Inl
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Amd64.KissatM6Bounds
meta import LeanQbe.T.Examples.Kissat.FullM6Inl

/-!
# KissatM6 Certificate Slice 11/51 on SysV x64

Kernel-checked compilation cert (`cert11`) for slice `[93, 102)` (`9` functions) of
`LeanQbe.T.Examples.Kissat.FullM6Inl.m6InlFns` on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatM6Cert11

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Amd64.KissatM6Bounds LeanQbe.T.Examples.Kissat.FullM6Inl

/-- Slice 11 sub-module (`[93, 102)`, `9` functions). -/
def slice11Mod : Module := { fns := (m6InlFns.drop 93).take 9 }

compile_linked_chunks! cert11 x64Target x64Layout x64LegalTarget x64LabelClean
  slice11Mod 4 (ext := m6ExtPrefix 93) (maxDirs := 600)

end LeanQbe.T.Amd64.KissatM6Cert11
