module

public import LeanQbe.T.Bootstrap0.Cert1
public import LeanQbe.T.Bootstrap0.Cert2
public import LeanQbe.T.Bootstrap0.Cert3
public import LeanQbe.T.Bootstrap0.Cert4
meta import Lean
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Bootstrap0.Mod0

/-!
# Linked Certificate Group A (`Cert1`..`Cert4`, `[0, 45)`) for `leanqbe0Mod0`

Links slices `1`..`4` (`45` functions) into `certA` over `[0, 45)`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Bootstrap0

open LeanQbe.T LeanQbe.T.LeanLCNF LeanQbe.T.Amd64

/-- Prefix sub-module `[0, 25)`. -/
@[expose] def pref2Mod : Module := { fns := leanqbe0Mod0.fns.take 25 }

/-- Prefix sub-module `[0, 34)`. -/
@[expose] def pref3Mod : Module := { fns := leanqbe0Mod0.fns.take 34 }

/-- Group A sub-module `[0, 45)`. -/
@[expose] def certAMod : Module := { fns := leanqbe0Mod0.fns.take 45 }

/-- Linked certificate for `[0, 25)`. -/
@[expose] noncomputable def pref2Cert :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean
      pref2Mod rtExtBounds0 rtExitSyms 64 2048 :=
  cert1.append cert2 (by exact List.take_add (l := leanqbe0Mod0.fns) (i := 13) (j := 12))
    (by t_kernel_rfl)

/-- Linked certificate for `[0, 34)`. -/
@[expose] noncomputable def pref3Cert :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean
      pref3Mod rtExtBounds0 rtExitSyms 64 2048 :=
  pref2Cert.append cert3 (by exact List.take_add (l := leanqbe0Mod0.fns) (i := 25) (j := 9))
    (by t_kernel_rfl)

/-- Linked certificate `certA` covering `[0, 45)` (`45` functions). -/
@[expose] noncomputable def certA :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean
      certAMod rtExtBounds0 rtExitSyms 64 2048 :=
  pref3Cert.append cert4 (by exact List.take_add (l := leanqbe0Mod0.fns) (i := 34) (j := 11))
    (by t_kernel_rfl)

end LeanQbe.T.Bootstrap0
