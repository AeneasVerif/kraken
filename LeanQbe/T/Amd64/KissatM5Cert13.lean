module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Amd64.KissatM5Bounds
public import LeanQbe.T.Examples.Kissat.FullM5InlB5
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Amd64.KissatM5Bounds
meta import LeanQbe.T.Examples.Kissat.FullM5InlB5

/-!
# KissatM5 Certificate Slice 13/34 on SysV x64

Kernel-checked compilation cert (`cert13`) for slice `[104, 115)` (`11` functions) of
`LeanQbe.T.Examples.Kissat.FullM5InlB5.m5InlB5Fns` on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatM5Cert13

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Amd64.KissatM5Bounds LeanQbe.T.Examples.Kissat.FullM5InlB5

/-- Slice 13 sub-module (`[104, 115)`, `11` functions). -/
noncomputable def slice13Mod : Module := { fns := (m5InlB5Fns.drop 104).take 11 }

compile_linked_chunks! cert13 x64Target x64Layout x64LegalTarget x64LabelClean
  slice13Mod 4 (ext := m5ExtPrefix 104) (maxDirs := 450)

end LeanQbe.T.Amd64.KissatM5Cert13
