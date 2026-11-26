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
# `rtC0CoreMod` SysV x64 Certificate Slice 5/7 (`[39, 61)`)

Kernel-checked native compilation certificate (`rtC0CertS5`) for `[39, 61)` (`22` functions,
`841` directives, full R2 container slice) of `LeanQbe.T.LeanLCNF.rtC0CoreMod.fns` on `x64Target`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64

open LeanQbe.T LeanQbe.T.LeanLCNF

/-- Slice 5 sub-module (`[39, 61)`, `22` functions). -/
@[expose] noncomputable def rtC0Slice5Mod : Module :=
  { fns := (rtC0CoreFlatMod.fns.drop 39).take 22, exits := rtExitSyms }

compile_linked_chunks! rtC0CertS5 x64Target x64Layout x64LegalTarget x64LabelClean
  rtC0Slice5Mod 11 (ext := rtC0ExtBefore 39) (exits := rtExitSyms) (nX := 64)
  (maxDirs := 500) (flat := true)

end LeanQbe.T.Amd64
