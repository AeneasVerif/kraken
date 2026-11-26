module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.LeanLCNF.LcnfC0Full
public import LeanQbe.T.Amd64.LcnfC0FullCertX64Bounds
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.LeanLCNF.LcnfC0Full
meta import LeanQbe.T.Amd64.LcnfC0FullCertX64Bounds

/-!
# `rtC0CoreMod` SysV x64 Certificate Slice 3/7 (`[30, 35)`)

Kernel-checked native compilation certificate (`rtC0CertS3`) for `[30, 35)` (`5` functions,
`1,002` directives) of `LeanQbe.T.LeanLCNF.rtC0CoreMod.fns` on `x64Target`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64

open LeanQbe.T LeanQbe.T.LeanLCNF

/-- Slice 3 sub-module (`[30, 35)`, `5` functions). -/
@[expose] def rtC0Slice3Mod : Module :=
  { fns := (rtC0CoreMod.fns.drop 30).take 5, exits := rtExitSyms }

compile_linked_chunks! rtC0CertS3 x64Target x64Layout x64LegalTarget x64LabelClean
  rtC0Slice3Mod 10 (ext := rtC0ExtBefore 30) (exits := rtExitSyms) (nX := 64)
  (maxDirs := 1500)

end LeanQbe.T.Amd64
