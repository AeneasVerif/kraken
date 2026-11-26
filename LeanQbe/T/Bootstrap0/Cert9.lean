module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.MainCertFlat
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Bootstrap0.Mod0
public import LeanQbe.T.Bootstrap0.CertBounds
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.MainCertFlatElab
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Bootstrap0.Mod0
meta import LeanQbe.T.Bootstrap0.CertBounds

/-!
# `leanqbe0` Kernel Compilation Certificate Slice 9/12 on SysV x64

Kernel-checked native compilation certificate (`cert9`) for slice `[86, 95)` (`9` functions,
`1,361` directives) of `LeanQbe.T.Bootstrap0.leanqbe0Mod0.fns` on `x64Target`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Bootstrap0

open LeanQbe.T LeanQbe.T.LeanLCNF LeanQbe.T.Amd64

/-- Slice 9 sub-module (`[86, 95)`, `9` functions). -/
@[expose] def slice9Mod : Module := { fns := (leanqbe0Mod0.fns.drop 86).take 9 }

compile_linked_chunks! cert9 x64Target x64Layout x64LegalTarget x64LabelClean
  slice9Mod 4 (ext := extBefore0 86) (exits := rtExitSyms) (nX := 64) (maxDirs := 250)
  (flat := true)

end LeanQbe.T.Bootstrap0
