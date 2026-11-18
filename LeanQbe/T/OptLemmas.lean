module

public import LeanQbe.T.Opt
public import LeanQbe.T.FoldLemmas
public import LeanQbe.T.CopyLemmas
public import LeanQbe.T.GvnLemmas
public import LeanQbe.T.DceLemmas

/-!
# Correctness of the Typed-IR Mid-End Pipeline (`T6`)

Composes relational well-formedness (`*_wf`) and WP refinement (`*_spec`) across
`Fold → Copy → Gvn → Copy → Fold → Dce`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-- The mid-end pipeline preserves well-formedness across every pass. -/
theorem Func.opt_wf {as rs : List Ty} {f : Func as rs} (hf : f.Wf) : (Func.opt f).Wf :=
  Func.dce_wf (Func.fold_wf (Func.copy_wf (Func.gvn_wf (Func.copy_wf (Func.fold_wf hf)))))

/-- The mid-end pipeline refines function contracts across every pass. -/
theorem Func.opt_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.opt f) xs m Q X := by
  have hf1 := Func.fold_wf hf
  have hs1 := Func.fold_spec hf h
  have hf2 := Func.copy_wf hf1
  have hs2 := Func.copy_spec hf1 hs1
  have hf3 := Func.gvn_wf hf2
  have hs3 := Func.gvn_spec hf2 hs2
  have hf4 := Func.copy_wf hf3
  have hs4 := Func.copy_spec hf3 hs3
  have hf5 := Func.fold_wf hf4
  have hs5 := Func.fold_spec hf4 hs4
  exact Func.dce_spec hf5 hs5

end LeanQbe.T
