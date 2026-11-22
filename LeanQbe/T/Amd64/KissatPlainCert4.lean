module

public import LeanQbe.T.MainCert
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Examples.Kissat.Plain
meta import Lean
meta import LeanQbe.T.MainCert
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Kissat.Dimacs
meta import LeanQbe.T.Examples.Kissat.Plain1
meta import LeanQbe.T.Examples.Kissat.Plain

/-!
# Kissat `D-Plain` Certificate Slice 4/6 on SysV x64

Kernel-checked native compilation certificate (`cert4`) for slice `[40, 47)` (`7` functions)
of `LeanQbe.T.Examples.Kissat.Plain.plainFns` on `x64Target`, with prefix bounds computed via
`eval_prefix_ext!`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatPlainCert4

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Examples.Kissat.Plain

open scoped LeanQbe.T in
eval_prefix_ext! ext4 x64Target x64LegalTarget (plainFns.take 40)

/-- Slice 4 sub-module (`[40, 47)`, `7` functions). -/
def slice4Mod : Module :=
  { fns := (plainFns.drop 40).take 7, externs := [], exits := [] }

open scoped LeanQbe.T in
compile_linked_chunks! cert4
  x64Target x64Layout x64LegalTarget x64LabelClean slice4Mod 4
  (ext := ext4) (maxDirs := 450)

end LeanQbe.T.Amd64.KissatPlainCert4
