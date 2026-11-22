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
# `leanqbe0` Kernel Compilation Certificate Slice 7/12 on SysV x64

Kernel-checked native compilation certificate (`cert7`) for slice `[66, 75)` (`9` functions,
`1,473` directives) of `LeanQbe.T.Bootstrap0.leanqbe0Mod0.fns` on `x64Target`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Bootstrap0

open LeanQbe.T LeanQbe.T.LeanLCNF LeanQbe.T.Amd64

/-- Slice 7 sub-module (`[66, 75)`, `9` functions). -/
@[expose] def slice7Mod : Module := { fns := (leanqbe0Mod0.fns.drop 66).take 9 }

compile_linked_chunks! cert7 x64Target x64Layout x64LegalTarget x64LabelClean
  slice7Mod 4 (ext := extBefore0 66) (exits := rtExitSyms) (nX := 64) (maxDirs := 250)

end LeanQbe.T.Bootstrap0
