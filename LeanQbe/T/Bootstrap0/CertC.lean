module

public import LeanQbe.T.Bootstrap0.Cert9
public import LeanQbe.T.Bootstrap0.Cert10
public import LeanQbe.T.Bootstrap0.Cert11
public import LeanQbe.T.Bootstrap0.Cert12
meta import Lean
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Bootstrap0.Mod0

/-!
# Linked Certificate Group C (`Cert9`..`Cert12`, `[86, 124)`) for `leanqbe0Mod0`

Links slices `9`..`12` (`38` functions) into `certC` over `[86, 124)`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Bootstrap0

open LeanQbe.T LeanQbe.T.LeanLCNF LeanQbe.T.Amd64

private theorem drop_take_addC {l : List Fn} {a b c : Nat} :
    (l.drop a).take (b + c) = (l.drop a).take b ++ (l.drop (a + b)).take c := by
  have h := List.take_add (l := l.drop a) (i := b) (j := c)
  rwa [List.drop_drop] at h

private theorem drop_take_dropC {l : List Fn} {a b : Nat} :
    l.drop a = (l.drop a).take b ++ l.drop (a + b) := by
  have h := (List.take_append_drop b (l.drop a)).symm
  rwa [List.drop_drop] at h

/-- Slice `[86, 105)`. -/
@[expose] def tail910Mod : Module := { fns := (leanqbe0Mod0.fns.drop 86).take 19 }

/-- Slice `[86, 116)`. -/
@[expose] def tail911Mod : Module := { fns := (leanqbe0Mod0.fns.drop 86).take 30 }

/-- Group C sub-module `[86, 124)`. -/
@[expose] def certCMod : Module := { fns := leanqbe0Mod0.fns.drop 86 }

/-- Linked certificate for `[86, 105)`. -/
@[expose] noncomputable def tail910Cert :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean
      tail910Mod (extBefore0 86) rtExitSyms 64 2048 :=
  cert9.append cert10
    (by exact drop_take_addC (l := leanqbe0Mod0.fns) (a := 86) (b := 9) (c := 10))
    (by t_kernel_rfl)

/-- Linked certificate for `[86, 116)`. -/
@[expose] noncomputable def tail911Cert :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean
      tail911Mod (extBefore0 86) rtExitSyms 64 2048 :=
  tail910Cert.append cert11
    (by exact drop_take_addC (l := leanqbe0Mod0.fns) (a := 86) (b := 19) (c := 11))
    (by t_kernel_rfl)

/-- Linked certificate `certC` covering `[86, 124)` (`38` functions). -/
@[expose] noncomputable def certC :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean
      certCMod (extBefore0 86) rtExitSyms 64 2048 :=
  tail911Cert.append cert12
    (by exact drop_take_dropC (l := leanqbe0Mod0.fns) (a := 86) (b := 30))
    (by t_kernel_rfl)

end LeanQbe.T.Bootstrap0
