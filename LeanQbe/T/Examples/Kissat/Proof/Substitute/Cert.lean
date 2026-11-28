/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Substitute.Spec
public import LeanQbe.T.Examples.Kissat.Src.Substitute
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Substitute.WpTarjanPop
import LeanQbe.T.Examples.Kissat.Proof.Substitute.WpTarjanScc
import LeanQbe.T.Examples.Kissat.Proof.Substitute.WpElimVars
import LeanQbe.T.Examples.Kissat.Proof.Substitute.WpRewriteBins
import LeanQbe.T.Examples.Kissat.Proof.Substitute.WpRewriteAr
import LeanQbe.T.Examples.Kissat.Proof.Substitute.WpSubstitute

/-!
# Canonical `SegCert` Assembly for `Kissat.Src.Substitute` (`6` Functions)

Proves `SegCert Spec.deps Src.Substitute.fns Spec.specs` using `Spec.deps_has_*`, `Spec.has_*`,
and the WP proofs in `WpTarjanPop`, `WpTarjanScc`, `WpElimVars`, `WpRewriteBins`, `WpRewriteAr`,
and `WpSubstitute`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Substitute

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src.Substitute

public section

theorem cert : SegCert Spec.deps Src.Substitute.fns Spec.specs := by
  intro Γ hDeps hOwn
  simp only [TableImpl, Src.Substitute.fns, Src.Substitute.substitute_fns, Spec.specs]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, full_tarjan_pop_scc_wp Γ⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, full_tarjan_scc_wp Γ (Spec.has_full_tarjan_pop_scc hOwn)⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, full_subst_elim_vars_wp Γ
      (Spec.deps_has_full_add_unit hDeps)
      (Spec.deps_has_full_propagate hDeps)
      (Spec.deps_has_full_extend_push2 hDeps)
      (Spec.deps_has_full_set_inactive hDeps)⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, full_subst_rewrite_bins_wp Γ
      (Spec.deps_has_full_add_unit hDeps)
      (Spec.deps_has_full_add_bin hDeps)⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, full_subst_rewrite_ar_wp Γ
      (Spec.deps_has_full_arena_next hDeps)
      (Spec.deps_has_full_add_unit hDeps)
      (Spec.deps_has_full_add_bin hDeps)⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, full_substitute_wp Γ
      (Spec.deps_has_full_backtrack hDeps)
      (Spec.has_full_tarjan_scc hOwn)
      (Spec.has_full_subst_elim_vars hOwn)
      (Spec.has_full_subst_rewrite_bins hOwn)
      (Spec.has_full_subst_rewrite_ar hOwn)
      (Spec.deps_has_full_arena_sweep hDeps)
      (Spec.deps_has_full_propagate hDeps)⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Substitute
