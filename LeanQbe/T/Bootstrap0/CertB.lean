module

public import LeanQbe.T.Bootstrap0.Cert5
public import LeanQbe.T.Bootstrap0.Cert6
public import LeanQbe.T.Bootstrap0.Cert7
public import LeanQbe.T.Bootstrap0.Cert8
meta import Lean
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Bootstrap0.Mod0

/-!
# Linked Certificate Group B (`Cert5`..`Cert8`, `[45, 86)`) for `leanqbe0Mod0`

Links slices `5`..`8` (`41` functions) into `certB` over `[45, 86)`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Bootstrap0

open LeanQbe.T LeanQbe.T.LeanLCNF LeanQbe.T.Amd64

private theorem drop_take_addB {l : List Fn} {a b c : Nat} :
    (l.drop a).take (b + c) = (l.drop a).take b ++ (l.drop (a + b)).take c := by
  have h := List.take_add (l := l.drop a) (i := b) (j := c)
  rwa [List.drop_drop] at h

/-- Slice `[45, 66)`. -/
@[expose] def mid56Mod : Module := { fns := (leanqbe0Mod0.fns.drop 45).take 21 }

/-- Slice `[45, 75)`. -/
@[expose] def mid57Mod : Module := { fns := (leanqbe0Mod0.fns.drop 45).take 30 }

/-- Group B sub-module `[45, 86)`. -/
@[expose] def certBMod : Module := { fns := (leanqbe0Mod0.fns.drop 45).take 41 }

/-- Linked certificate for `[45, 66)`. -/
@[expose] noncomputable def mid56Cert :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean
      mid56Mod (extBefore0 45) rtExitSyms 64 2048 :=
  cert5.append cert6 (by exact drop_take_addB (l := leanqbe0Mod0.fns) (a := 45) (b := 10) (c := 11))
    (by t_kernel_rfl)

/-- Linked certificate for `[45, 75)`. -/
@[expose] noncomputable def mid57Cert :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean
      mid57Mod (extBefore0 45) rtExitSyms 64 2048 :=
  mid56Cert.append cert7
    (by exact drop_take_addB (l := leanqbe0Mod0.fns) (a := 45) (b := 21) (c := 9))
    (by t_kernel_rfl)

/-- Linked certificate `certB` covering `[45, 86)` (`41` functions). -/
@[expose] noncomputable def certB :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean
      certBMod (extBefore0 45) rtExitSyms 64 2048 :=
  mid57Cert.append cert8
    (by exact drop_take_addB (l := leanqbe0Mod0.fns) (a := 45) (b := 30) (c := 11))
    (by t_kernel_rfl)

end LeanQbe.T.Bootstrap0
