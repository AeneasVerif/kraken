module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.MainCertFlat
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.LeanLCNF.LcnfC0FullFlat
public import LeanQbe.T.Amd64.LcnfC0FullCertX64Bounds
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.MainCertFlatElab
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.LeanLCNF.LcnfC0Full
meta import LeanQbe.T.Amd64.LcnfC0FullCertX64Bounds

/-!
# `rtC0CoreMod` SysV x64 Certificate Slice 4/7 (`[35, 39)`)

Kernel-checked native compilation certificate (`rtC0CertS4`) for `[35, 39)` (`4` functions,
`733` directives) of `LeanQbe.T.LeanLCNF.rtC0CoreMod.fns` on `x64Target`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64

open LeanQbe.T LeanQbe.T.LeanLCNF

/-- Slice 4 sub-module (`[35, 39)`, `4` functions). -/
@[expose] noncomputable def rtC0Slice4Mod : Module :=
  { fns := (rtC0CoreFlatMod.fns.drop 35).take 4, exits := rtExitSyms }

compile_linked_chunks! rtC0CertS4 x64Target x64Layout x64LegalTarget x64LabelClean
  rtC0Slice4Mod 4 (ext := rtC0ExtBefore 35) (exits := rtExitSyms) (nX := 64)
  (maxDirs := 800) (flat := true)

end LeanQbe.T.Amd64
