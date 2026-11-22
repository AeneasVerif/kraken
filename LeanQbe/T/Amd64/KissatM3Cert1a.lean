module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Examples.Kissat.FullM3
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Kissat.FullM3

/-!
# Kissat M3 (`FullM3`) Certificate Slice 1a/19 on SysV x64

Kernel-checked native compilation certificate (`cert1a`) for slice `[0, 16)` (`16`
functions) of `LeanQbe.T.Examples.Kissat.FullM3.m3Fns` on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatM3Cert1a

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Examples.Kissat.FullM3

/-- Slice 1a sub-module (`[0, 16)`, `16` functions). -/
def slice1aMod : Module := { fns := m3Fns.take 16 }

compile_linked_chunks! cert1a x64Target x64Layout x64LegalTarget x64LabelClean
  slice1aMod 4 (maxDirs := 450)

end LeanQbe.T.Amd64.KissatM3Cert1a
