module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Bootstrap0.Mod0
public import LeanQbe.T.Bootstrap0.CertBounds
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Bootstrap0.Mod0
meta import LeanQbe.T.Bootstrap0.CertBounds

/-!
# `leanqbe0` Kernel Compilation Certificate Slice 5/12 on SysV x64

Kernel-checked native compilation certificate (`cert5`) for slice `[45, 55)` (`10` functions,
`1,334` directives) of `LeanQbe.T.Bootstrap0.leanqbe0Mod0.fns` on `x64Target`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Bootstrap0

open LeanQbe.T LeanQbe.T.LeanLCNF LeanQbe.T.Amd64

/-- Slice 5 sub-module (`[45, 55)`, `10` functions). -/
@[expose] def slice5Mod : Module := { fns := (leanqbe0Mod0.fns.drop 45).take 10 }

compile_linked_chunks! cert5 x64Target x64Layout x64LegalTarget x64LabelClean
  slice5Mod 4 (ext := extBefore0 45) (exits := rtExitSyms) (nX := 64) (maxDirs := 250)

end LeanQbe.T.Bootstrap0
