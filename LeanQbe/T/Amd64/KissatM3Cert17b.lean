module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Examples.Kissat.FullM3
public import LeanQbe.T.Amd64.KissatM3Bounds
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Kissat.FullM3
meta import LeanQbe.T.Amd64.KissatM3Bounds

/-!
# Kissat M3 (`FullM3`) Certificate Slice 17b/21 on SysV x64

Kernel-checked native compilation certificate (`cert17b`) for slice `[199, 204)` (`5`
functions) of `LeanQbe.T.Examples.Kissat.FullM3.m3Fns` on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatM3Cert17b

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Examples.Kissat.FullM3
open LeanQbe.T.Amd64.KissatM3Bounds

/-- Slice 17b sub-module (`[199, 204)`, `5` functions). -/
def slice17bMod : Module := { fns := m3Fns.drop 199 }

compile_linked_chunks! cert17b x64Target x64Layout x64LegalTarget x64LabelClean
  slice17bMod 4 (ext := m3ExtPrefix 199) (maxDirs := 450)

end LeanQbe.T.Amd64.KissatM3Cert17b
