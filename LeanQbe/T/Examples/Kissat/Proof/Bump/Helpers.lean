/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Bump.Spec

/-!
# Spec Helper Lemmas for `Kissat.Proof.Bump` (`Proof.Bump.Helpers`)

Houses pure lemmas over `Bump.Spec.FullBumpPre` outside `Bump/Spec.lean`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Bump.Spec

open LeanQbe.T.Examples.Kissat.Proof.Spec

theorem fullBumpPre_of_cov (allow_reasons : Bool) {c : FullCfg} {s : FullState}
    (hcov : FullAnaMarksCov c s) : FullBumpPre allow_reasons c s := by
  unfold FullBumpPre
  cases allow_reasons
  · exact ⟨hcov.1, fun k hk => (hcov.2.2.1 k hk).1⟩
  · exact hcov

theorem fullBumpPre_false_of {c : FullCfg} {s : FullState}
    (hmcl : s.core.min_clr_len ≤ s.core.cur_vars)
    (hlt : ∀ k < s.core.min_clr_len, (s.scratch.work_stk1[k]?.getD 0#32).toNat < s.core.cur_vars) :
    FullBumpPre false c s := by
  unfold FullBumpPre; exact ⟨hmcl, hlt⟩

end LeanQbe.T.Examples.Kissat.Proof.Bump.Spec
