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
# KissatM6 Certificate Slice 14/51 on SysV x64

Kernel-checked compilation cert (`cert14`) for slice `[114, 120)` (`6` functions) of
`LeanQbe.T.Examples.Kissat.FullM6Inl.m6InlFns` on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatM6Cert14

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Amd64.KissatM6Bounds LeanQbe.T.Examples.Kissat.FullM6Inl

/-- Slice 14 sub-module (`[114, 120)`, `6` functions). -/
def slice14Mod : Module := { fns := (m6InlFns.drop 114).take 6 }

compile_linked_chunks! cert14 x64Target x64Layout x64LegalTarget x64LabelClean
  slice14Mod 4 (ext := m6ExtPrefix 114) (maxDirs := 600)

end LeanQbe.T.Amd64.KissatM6Cert14
