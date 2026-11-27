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
# `rtC0CoreMod` SysV x64 Certificate Slice 6/7 (`[61, 72)`)

Kernel-checked native compilation certificate (`rtC0CertS6`) for `[61, 72)` (`11` functions)
of `LeanQbe.T.LeanLCNF.rtC0CoreMod.fns` on `x64Target`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64

open LeanQbe.T LeanQbe.T.LeanLCNF

/-- Slice 6 sub-module (`[61, 72)`, `11` functions). -/
@[expose] noncomputable def rtC0Slice6Mod : Module :=
  { fns := (rtC0CoreFlatMod.fns.drop 61).take 11, exits := rtExitSyms }

compile_linked_chunks! rtC0CertS6 x64Target x64Layout x64LegalTarget x64LabelClean
  rtC0Slice6Mod 9 (ext := rtC0ExtBefore 61) (exits := rtExitSyms) (nX := 64)
  (maxDirs := 500) (flat := true)

end LeanQbe.T.Amd64
