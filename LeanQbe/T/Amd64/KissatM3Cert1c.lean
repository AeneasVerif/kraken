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
# Kissat M3 (`FullM3`) Certificate Slice 1c/21 on SysV x64

Kernel-checked native compilation certificate (`cert1c`) for slice `[32, 47)` (`15`
functions) of `LeanQbe.T.Examples.Kissat.FullM3.m3Fns` on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatM3Cert1c

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Examples.Kissat.FullM3
open LeanQbe.T.Amd64.KissatM3Bounds

/-- Slice 1c sub-module (`[32, 47)`, `15` functions). -/
def slice1cMod : Module := { fns := (m3Fns.drop 32).take 15 }

compile_linked_chunks! cert1c x64Target x64Layout x64LegalTarget x64LabelClean
  slice1cMod 4 (ext := m3ExtPrefix 32) (maxDirs := 450)

end LeanQbe.T.Amd64.KissatM3Cert1c
