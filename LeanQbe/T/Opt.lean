module

public import LeanQbe.T.Fold
public import LeanQbe.T.Copy
public import LeanQbe.T.Gvn
public import LeanQbe.T.Dce

/-!
# The Typed-IR Mid-End Pipeline (`T6`)

`Func.opt`: initial constant folding & algebraic simplification (`Func.fold`), copy and
`mkpair`/`unpair` projection propagation (`Func.copy`), lexical GVN/CSE (`Func.gvn`), a second
copy/pair pass (`Func.copy`, eliminating `mkpair (fst p) (snd p) → p` newly exposed after GVN
merges duplicate `unpair`s), a second folding pass (`Func.fold`, which simplifies newly exposed
identities such as `sub x x` after CSE/copy propagation and eliminates dead branches), and
dead-code elimination (`Func.dce`).

Correctness (`LeanQbe/T/OptLemmas.lean`): `Func.opt_wf`, `Func.opt_spec`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-- Run the combined `T6` mid-end optimization pipeline on a closed typed function. -/
def Func.opt {as rs : List Ty} (f : Func as rs) : Func as rs :=
  Func.dce (Func.fold (Func.copy (Func.gvn (Func.copy (Func.fold f)))))

end LeanQbe.T
