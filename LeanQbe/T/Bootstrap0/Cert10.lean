module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Bootstrap0.Mod0
public import LeanQbe.T.Bootstrap0.CertBounds
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Bootstrap0.Mod0
meta import LeanQbe.T.Bootstrap0.CertBounds

/-!
# `leanqbe0` Kernel Compilation Certificate Slice 10/12 on SysV x64

Kernel-checked native compilation certificate (`cert10`) for slice `[95, 105)` (`10` functions,
`1,486` directives) of `LeanQbe.T.Bootstrap0.leanqbe0Mod0.fns` on `x64Target`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Bootstrap0

open LeanQbe.T LeanQbe.T.LeanLCNF LeanQbe.T.Amd64

/-- Slice 10 sub-module (`[95, 105)`, `10` functions). -/
@[expose] def slice10Mod : Module := { fns := (leanqbe0Mod0.fns.drop 95).take 10 }

compile_linked_chunks! cert10 x64Target x64Layout x64LegalTarget x64LabelClean
  slice10Mod 4 (ext := extBefore0 95) (exits := rtExitSyms) (nX := 64) (maxDirs := 250)

end LeanQbe.T.Bootstrap0
