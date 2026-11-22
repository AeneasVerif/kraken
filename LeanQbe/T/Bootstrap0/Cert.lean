module

public import LeanQbe.T.Bootstrap0.CertA
public import LeanQbe.T.Bootstrap0.CertB
public import LeanQbe.T.Bootstrap0.CertC
meta import Lean
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Bootstrap0.Mod0

/-!
# Whole-Module Kernel Compilation Certificate (`leanqbe0Cert`) on SysV x64

Combines the three group certificates (`CertA` `[0, 45)`, `CertB` `[45, 86)`, `CertC` `[86, 124)`)
via two balanced `LinkedCert.append` steps into `leanqbe0Cert` over the complete lowered
`leanqbe0Compile` module (`leanqbe0Mod0`, `124` functions, `16,447` directives) on `x64Target`, plus
`leanqbe0Mod0_legalSig`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Bootstrap0

open LeanQbe.T LeanQbe.T.LeanLCNF LeanQbe.T.Amd64

/-- Prefix sub-module `[0, 86)`. -/
def pref8Mod : Module := { fns := leanqbe0Mod0.fns.take 86 }

/-- Linked certificate for prefix `[0, 86)`. -/
noncomputable def pref8Cert :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean
      pref8Mod rtExtBounds0 rtExitSyms 64 2048 :=
  certA.append certB (by exact List.take_add (l := leanqbe0Mod0.fns) (i := 45) (j := 41))
    (by t_kernel_rfl)

/-- Complete kernel-checked native x64 compilation certificate for all `124` functions of
`leanqbe0Compile` (`leanqbe0Mod0`). -/
noncomputable def leanqbe0Cert :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean
      leanqbe0Mod0 rtExtBounds0 rtExitSyms 64 2048 :=
  pref8Cert.append certC (by exact (List.take_append_drop 86 leanqbe0Mod0.fns).symm)
    (by t_kernel_rfl)

private theorem leanqbe0_legalSig_check :
    checkLegalSigAll x64LegalTarget leanqbe0Mod0.fns = true := by
  t_kernel_rfl

/-- Every function signature in `leanqbe0Mod0.fns` satisfies `x64LegalTarget.legalSig`. -/
theorem leanqbe0Mod0_legalSig : LegalSigAll x64LegalTarget leanqbe0Mod0.fns :=
  legalSigAll_of_check leanqbe0_legalSig_check

/-- Kernel check that `leanqbe0Cert.bounds` covers all `124` functions. -/
theorem leanqbe0Cert_bounds_len : leanqbe0Cert.bounds.length = 124 := by
  t_kernel_rfl

/-- Kernel check that `leanqbe0Cert` has positive chunk count. -/
theorem leanqbe0Cert_numChunks_pos : leanqbe0Cert.numChunks > 0 := by
  decide

/-- Kernel check that every stack bound in `leanqbe0Cert` is at most `2048` bytes. -/
theorem leanqbe0Cert_bounds_le :
    leanqbe0Cert.bounds.all (fun p => Nat.ble p.2 2048) = true := by
  t_kernel_rfl

/-- Kernel check that `leanqbe0Cert.code` is non-empty. -/
theorem leanqbe0Cert_code_nonempty : (!leanqbe0Cert.code.isEmpty) = true := by
  t_kernel_rfl

end LeanQbe.T.Bootstrap0
