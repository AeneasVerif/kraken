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
# `leanqbe0` Kernel Compilation Certificate Slice 8/12 on SysV x64

Kernel-checked native compilation certificate (`cert8`) for slice `[75, 86)` (`11` functions,
`1,496` directives) of `LeanQbe.T.Bootstrap0.leanqbe0Mod0.fns` on `x64Target`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Bootstrap0

open LeanQbe.T LeanQbe.T.LeanLCNF LeanQbe.T.Amd64

/-- Slice 8 sub-module (`[75, 86)`, `11` functions). -/
@[expose] def slice8Mod : Module := { fns := (leanqbe0Mod0.fns.drop 75).take 11 }

compile_linked_chunks! cert8 x64Target x64Layout x64LegalTarget x64LabelClean
  slice8Mod 4 (ext := extBefore0 75) (exits := rtExitSyms) (nX := 64) (maxDirs := 250)

end LeanQbe.T.Bootstrap0
