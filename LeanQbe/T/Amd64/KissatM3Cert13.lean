module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Examples.Kissat.FullM3
public import LeanQbe.T.Amd64.KissatM3Bounds
meta import Lean
meta import LeanQbe.T.MainCertElab
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Kissat.FullM3
meta import LeanQbe.T.Amd64.KissatM3Bounds

/-!
# Kissat M3 (`FullM3`) Certificate Slice 13/21 on SysV x64

Kernel-checked native compilation certificate (`cert13`) for slice `[158, 167)` (`9`
functions) of `LeanQbe.T.Examples.Kissat.FullM3.m3Fns` on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatM3Cert13

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Examples.Kissat.FullM3
open LeanQbe.T.Amd64.KissatM3Bounds

/-- Slice 13 sub-module (`[158, 167)`, `9` functions). -/
def slice13Mod : Module := { fns := (m3Fns.drop 158).take 9 }

compile_linked_chunks! cert13 x64Target x64Layout x64LegalTarget x64LabelClean
  slice13Mod 4 (ext := m3ExtPrefix 158) (maxDirs := 450)

end LeanQbe.T.Amd64.KissatM3Cert13
