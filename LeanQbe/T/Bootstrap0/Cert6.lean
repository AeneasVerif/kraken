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
# `leanqbe0` Kernel Compilation Certificate Slice 6/12 on SysV x64

Kernel-checked native compilation certificate (`cert6`) for slice `[55, 66)` (`11` functions,
`1,492` directives) of `LeanQbe.T.Bootstrap0.leanqbe0Mod0.fns` on `x64Target`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Bootstrap0

open LeanQbe.T LeanQbe.T.LeanLCNF LeanQbe.T.Amd64

/-- Slice 6 sub-module (`[55, 66)`, `11` functions). -/
@[expose] def slice6Mod : Module := { fns := (leanqbe0Mod0.fns.drop 55).take 11 }

compile_linked_chunks! cert6 x64Target x64Layout x64LegalTarget x64LabelClean
  slice6Mod 4 (ext := extBefore0 55) (exits := rtExitSyms) (nX := 64) (maxDirs := 250)
  (flat := true)

end LeanQbe.T.Bootstrap0
