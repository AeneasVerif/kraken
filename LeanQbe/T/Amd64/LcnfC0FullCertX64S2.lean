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
# `rtC0CoreMod` SysV x64 Certificate Slice 2/7 (`[15, 30)`)

Kernel-checked native compilation certificate (`rtC0CertS2`) for `[15, 30)` (`15` functions,
`814` directives) of `LeanQbe.T.LeanLCNF.rtC0CoreMod.fns` on `x64Target`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64

open LeanQbe.T LeanQbe.T.LeanLCNF

/-- Slice 2 sub-module (`[15, 30)`, `15` functions). -/
@[expose] noncomputable def rtC0Slice2Mod : Module :=
  { fns := (rtC0CoreFlatMod.fns.drop 15).take 15, exits := rtExitSyms }

compile_linked_chunks! rtC0CertS2 x64Target x64Layout x64LegalTarget x64LabelClean
  rtC0Slice2Mod 8 (ext := rtC0ExtBefore 15) (exits := rtExitSyms) (nX := 64)
  (maxDirs := 600) (flat := true)

end LeanQbe.T.Amd64
