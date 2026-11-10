module

public import LeanQbe.Opt
public import LeanQbe.FoldLemmas
public import LeanQbe.GvnLemmas

/-! # Correctness of the mid-end pipeline -/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe

/-- The pipeline keeps functions well-formed (so the lowering can take its output). -/
theorem Func.opt_wf {f : Func} (hf : f.Wf) : (Func.opt f).Wf :=
  Func.fold_wf (Func.gvn_wf (Func.fold_wf hf))

/-- The pipeline refines contracts: whatever the source satisfies, the output satisfies. -/
theorem Func.opt_spec {f : Func} (hf : f.Wf) {Γ : Env} {args : List Val} {m : Mem 64}
    {Q : Post} {X : XPost} (h : Func.spec Γ f args m Q X) : Func.spec Γ (Func.opt f) args m Q X :=
  Func.fold_spec (Func.gvn_wf (Func.fold_wf hf))
    (Func.gvn_spec (Func.fold_wf hf) (Func.fold_spec hf h))

end LeanQbe
