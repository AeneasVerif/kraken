module

public import LeanQbe.Fold
public import LeanQbe.Gvn

/-!
# The mid-end pipeline

`Func.opt`: constant folding and copy propagation, then common-subexpression elimination, then folding
again (CSE turns repeated operations into copies of earlier results, which can make further operations
constant or copies). Correctness: `OptLemmas` (`Func.opt_spec`, `Func.opt_wf`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe

def Func.opt (f : Func) : Func := Func.fold (Func.gvn (Func.fold f))

end LeanQbe
