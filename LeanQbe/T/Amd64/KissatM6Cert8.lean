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
# KissatM6 Certificate Slice 8/51 on SysV x64

Kernel-checked compilation cert (`cert8`) for slice `[80, 81)` (`1` functions) of
`LeanQbe.T.Examples.Kissat.FullM6Inl.m6InlFns` on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatM6Cert8

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Amd64.KissatM6Bounds LeanQbe.T.Examples.Kissat.FullM6Inl

/-- Slice 8 sub-module (`[80, 81)`, `1` functions). -/
def slice8Mod : Module := { fns := (m6InlFns.drop 80).take 1 }

compile_linked_chunks! cert8 x64Target x64Layout x64LegalTarget x64LabelClean
  slice8Mod 4 (ext := m6ExtPrefix 80) (maxDirs := 600)

end LeanQbe.T.Amd64.KissatM6Cert8
