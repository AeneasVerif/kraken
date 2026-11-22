module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Examples.Kissat.FullM3
public import LeanQbe.T.Amd64.KissatM3Bounds
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Kissat.FullM3
meta import LeanQbe.T.Amd64.KissatM3Bounds

/-!
# Kissat M3 (`FullM3`) Certificate Slice 2a/21 on SysV x64

Kernel-checked native compilation certificate (`cert2a`) for slice `[47, 48)` (`1` heavy
function: `full_prop_lit_raw`) of `LeanQbe.T.Examples.Kissat.FullM3.m3Fns` on `x64Target`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatM3Cert2a

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Examples.Kissat.FullM3
open LeanQbe.T.Amd64.KissatM3Bounds

/-- Slice 2a sub-module (`[47, 48)`, `1` function: `full_prop_lit_raw`). -/
def slice2aMod : Module := { fns := (m3Fns.drop 47).take 1 }

compile_linked_chunks! cert2a x64Target x64Layout x64LegalTarget x64LabelClean
  slice2aMod 4 (ext := m3ExtPrefix 47) (maxDirs := 450)

end LeanQbe.T.Amd64.KissatM3Cert2a
