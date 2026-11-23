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
# KissatM6 Certificate Slice 17/51 on SysV x64

Kernel-checked compilation cert (`cert17`) for slice `[133, 144)` (`11` functions) of
`LeanQbe.T.Examples.Kissat.FullM6Inl.m6InlFns` on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatM6Cert17

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Amd64.KissatM6Bounds LeanQbe.T.Examples.Kissat.FullM6Inl

/-- Slice 17 sub-module (`[133, 144)`, `11` functions). -/
def slice17Mod : Module := { fns := (m6InlFns.drop 133).take 11 }

compile_linked_chunks! cert17 x64Target x64Layout x64LegalTarget x64LabelClean
  slice17Mod 4 (ext := m6ExtPrefix 133) (maxDirs := 600)

end LeanQbe.T.Amd64.KissatM6Cert17
