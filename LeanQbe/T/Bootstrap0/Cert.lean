module

public import LeanQbe.T.Bootstrap0.CertA
public import LeanQbe.T.Bootstrap0.CertB
public import LeanQbe.T.Bootstrap0.CertC
public import LeanQbe.T.Amd64.LcnfC0FullCertX64
public import LeanQbe.T.Amd64.LcnfC0FullCertX64Bounds
meta import Lean
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Bootstrap0.Mod0

/-!
# Whole-Module Kernel Compilation Certificate (`leanqbe0Cert` & `leanqbe0LinkedCert`) on SysV x64

Combines the three group certificates (`CertA` `[0, 45)`, `CertB` `[45, 86)`, `CertC` `[86, 124)`)
via two balanced `LinkedCert.append` steps into `leanqbe0Cert` over `leanqbe0Mod0` (`124` functions)
parameterized by real verified `rtC0CoreAllExt` stack bounds (`≤ 272` B), and links `leanqbe0Cert`
onto `rtC0CoreCert` (`86` pure-C0 runtime functions) via `rtC0CoreCert.append` into the closed
`210`-function `0`-extern certificate `leanqbe0LinkedCert` over `leanqbe0LinkedMod`.
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
      pref8Mod rtC0CoreAllExt rtExitSyms 64 2048 :=
  certA.append certB (by exact List.take_add (l := leanqbe0Mod0.fns) (i := 45) (j := 41))
    (by t_kernel_rfl)

/-- Complete kernel-checked native x64 compilation certificate for all `124` functions of
`leanqbe0Compile` (`leanqbe0Mod0`) using verified `rtC0CoreAllExt` runtime stack bounds. -/
noncomputable def leanqbe0Cert :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean
      leanqbe0Mod0 rtC0CoreAllExt rtExitSyms 64 2048 :=
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

/-- Kernel check that every stack bound in `leanqbe0Cert` is at most `1136` bytes. -/
theorem leanqbe0Cert_bounds_le_max :
    leanqbe0Cert.bounds.all (fun p => Nat.ble p.2 1136) = true := by
  t_kernel_rfl

/-- Kernel check that `leanqbe0Cert.code` is non-empty. -/
theorem leanqbe0Cert_code_nonempty : (!leanqbe0Cert.code.isEmpty) = true := by
  t_kernel_rfl

/-- Closed `210`-function native x64 compilation certificate linking `rtC0CoreCert` (`86` fns)
and `leanqbe0Cert` (`124` fns) over `leanqbe0LinkedMod` (`0` externs, `rtExitSyms`, `nX = 64`). -/
noncomputable def leanqbe0LinkedCert :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean
      leanqbe0LinkedMod [] rtExitSyms 64 2048 :=
  rtC0CoreCert.append leanqbe0Cert rfl (by t_kernel_rfl)

/-- Every function signature in `leanqbe0LinkedMod.fns` (`210` fns) satisfies `x64LegalTarget`. -/
theorem leanqbe0LinkedMod_legalSig : LegalSigAll x64LegalTarget leanqbe0LinkedMod.fns := by
  intro f hf
  rcases List.mem_append.mp hf with hrt | huser
  · exact rtC0CoreMod_legalSig f hrt
  · exact leanqbe0Mod0_legalSig f huser

/-- Kernel check that `leanqbe0LinkedCert.bounds` covers all `210` linked functions. -/
theorem leanqbe0LinkedCert_bounds_len : leanqbe0LinkedCert.bounds.length = 210 := by
  t_kernel_rfl

/-- Kernel check that `leanqbe0LinkedCert` has positive chunk count. -/
theorem leanqbe0LinkedCert_numChunks_pos : leanqbe0LinkedCert.numChunks > 0 := by
  decide

/-- Kernel check that every stack bound in `leanqbe0LinkedCert` is at most `2048` bytes. -/
theorem leanqbe0LinkedCert_bounds_le :
    leanqbe0LinkedCert.bounds.all (fun p => Nat.ble p.2 2048) = true := by
  t_kernel_rfl

/-- Kernel check that every stack bound in `leanqbe0LinkedCert` is at most `1136` bytes. -/
theorem leanqbe0LinkedCert_bounds_le_max :
    leanqbe0LinkedCert.bounds.all (fun p => Nat.ble p.2 1136) = true := by
  t_kernel_rfl

/-- Kernel check that `leanqbe0LinkedCert.code` is non-empty. -/
theorem leanqbe0LinkedCert_code_nonempty : (!leanqbe0LinkedCert.code.isEmpty) = true := by
  t_kernel_rfl

end LeanQbe.T.Bootstrap0
