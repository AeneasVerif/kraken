module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.LeanLCNF.LcnfC0Full
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.LeanLCNF.LcnfC0Full

/-!
# `rtC0CoreMod` SysV x64 Certificate Slice 1/7 (`[0, 15)`)

Kernel-checked native compilation certificate (`rtC0CertS1`) for `[0, 15)` (`15` functions,
`708` directives) of `LeanQbe.T.LeanLCNF.rtC0CoreMod.fns` on `x64Target`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64

open LeanQbe.T LeanQbe.T.LeanLCNF

/-- Slice 1 sub-module (`[0, 15)`, `15` functions). -/
@[expose] def rtC0Slice1Mod : Module :=
  { fns := rtC0CoreMod.fns.take 15, exits := rtExitSyms }

compile_linked_chunks! rtC0CertS1 x64Target x64Layout x64LegalTarget x64LabelClean
  rtC0Slice1Mod 8 (exits := rtExitSyms) (nX := 64) (maxDirs := 600)

end LeanQbe.T.Amd64
