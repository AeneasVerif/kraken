module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.MainCertFlat
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Amd64.LcnfC0FullCertX64Bounds
public import LeanQbe.T.Bootstrap0.Mod0
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.MainCertFlatElab
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Amd64.LcnfC0FullCertX64Bounds
meta import LeanQbe.T.Bootstrap0.Mod0

/-!
# `leanqbe0` Kernel Compilation Certificate Slice 1/12 on SysV x64

Kernel-checked native compilation certificate (`cert1`) for slice `[0, 13)` (`13` functions,
`1,336` directives) of `LeanQbe.T.Bootstrap0.leanqbe0Mod0.fns` on `x64Target`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Bootstrap0

open LeanQbe.T LeanQbe.T.LeanLCNF LeanQbe.T.Amd64

/-- Slice 1 sub-module (`[0, 13)`, `13` functions). -/
@[expose] def slice1Mod : Module := { fns := leanqbe0Mod0.fns.take 13 }

compile_linked_chunks! cert1 x64Target x64Layout x64LegalTarget x64LabelClean
  slice1Mod 4 (ext := rtC0CoreAllExt) (exits := rtExitSyms) (nX := 64) (maxDirs := 250)
  (flat := true)

end LeanQbe.T.Bootstrap0
