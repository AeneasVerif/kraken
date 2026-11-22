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
# Kissat `D-Plain` Certificate Slice 6/6 on SysV x64

Kernel-checked native compilation certificate (`cert6`) for slice `[52, 59)` (`7` functions)
of `LeanQbe.T.Examples.Kissat.Plain.plainFns` on `x64Target`, with prefix bounds computed via
`eval_prefix_ext!`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64.KissatPlainCert6

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Examples.Kissat.Plain

open scoped LeanQbe.T in
eval_prefix_ext! ext6 x64Target x64LegalTarget (plainFns.take 52)

/-- Slice 6 sub-module (`[52, 59)`, `7` functions). -/
def slice6Mod : Module :=
  { fns := plainFns.drop 52, externs := [], exits := [] }

open scoped LeanQbe.T in
compile_linked_chunks! cert6
  x64Target x64Layout x64LegalTarget x64LabelClean slice6Mod 4
  (ext := ext6) (maxDirs := 450)

end LeanQbe.T.Amd64.KissatPlainCert6
