module

public import LeanQbe.T.MainCertCore
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbeTest.T.Common.Fixtures
import LeanQbe.T.FlatLemmas
public meta import Lean
public meta import LeanQbe.T.MainCertElab
public meta import LeanQbe.T.Amd64.Targ
public meta import LeanQbeTest.T.Common.Fixtures

/-!
# Auto-Computed Prefix Bounds (`eval_prefix_ext!`) Test on SysV x64

Tests `LeanQbe.T.eval_prefix_ext!` across multi-slice `compile_linked_chunks!` calls with zero
hardcoded stack bounds, linking all slices via `LinkedCert.append` and checking
`checkLinkList x64Layout [] fullCert.chunks = true` with zero `Kraken.AArch64` co-imports.
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.CertAutoExtTest

open LeanQbe.T LeanQbe.T.Amd64 LeanQbeTest.T.Common.Fixtures

compile_linked_chunks! cert1
  x64Target x64Layout x64LegalTarget x64LabelClean slice1Mod 1

eval_prefix_ext! ext1 x64Target x64LegalTarget (autoFns.take 2)

compile_linked_chunks! cert2
  x64Target x64Layout x64LegalTarget x64LabelClean slice2Mod 2 (ext := ext1)

eval_prefix_ext! ext2 x64Target x64LegalTarget ((autoFns.drop 2).take 2)
  (ext := ext1) (maxBound := 1024)

compile_linked_chunks! cert3
  x64Target x64Layout x64LegalTarget x64LabelClean slice3Mod 1
  (ext := ext2) (maxBound := 1024)

noncomputable def pref2Cert :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean pref2Mod [] [] 0 2048 :=
  cert1.append cert2 (by exact List.take_add (l := autoFns) (i := 2) (j := 2))
    (by t_kernel_rfl)

noncomputable def fullCert :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean fullMod [] [] 0 2048 :=
  pref2Cert.append cert3 (by exact (List.take_append_drop 4 autoFns).symm)
    (by t_kernel_rfl)

theorem link_check_ok :
    checkLinkList x64Layout [] fullCert.chunks = true := by
  t_kernel_rfl

theorem ext1_len : ext1.length = 2 := rfl
theorem ext2_len : ext2.length = 4 := rfl
theorem fullCert_chunks : fullCert.numChunks = 5 := rfl
theorem fullCert_bound_pos : 0 < fullCert.bound "main_entry" := by decide

#print axioms fullCert
#print axioms link_check_ok

end LeanQbeTest.T.CertAutoExtTest
