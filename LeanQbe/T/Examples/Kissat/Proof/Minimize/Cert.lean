/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Minimize.Spec
public import LeanQbe.T.Examples.Kissat.Src.Minimize
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Minimize.WpMark
import LeanQbe.T.Examples.Kissat.Proof.Minimize.WpSort
import LeanQbe.T.Examples.Kissat.Proof.Minimize.WpMinDfs
import LeanQbe.T.Examples.Kissat.Proof.Minimize.WpShrinkLower
import LeanQbe.T.Examples.Kissat.Proof.Minimize.WpShrinkBlk
import LeanQbe.T.Examples.Kissat.Proof.Minimize.WpMinShrink

/-!
# Segment Certificate for `Kissat.Src.Minimize`

Assembles the closed-segment `SegCert [] Src.Minimize.fns Spec.specs` from the six canonical
WP proofs (`full_min_mark_wp`, `full_sort_tmp_wp`, `full_min_lit_dfs_m8_wp`,
`full_shrink_lower_m8_wp`, `full_shrink_blk_bool_m8_wp`, `full_min_shrink_m6_wp`).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Minimize

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Src.Minimize

private theorem mem_specs_has {Γ : Env} (hSat : Γ.Sat Spec.specs)
    {nm : Sym} {as bs : List Ty} {sp : Spec as bs}
    (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ Spec.specs) (hx : sp.XFree) :
    Γ.Has nm sp :=
  Env.Sat.has hSat hmem hx

public section

theorem cert : SegCert [] Src.Minimize.fns Spec.specs := by
  intro Γ _ hSat
  have hMm : Γ.Has "full_min_mark" Spec.fullMinMarkSpec :=
    mem_specs_has hSat (by simp [Spec.specs]) (by xfree)
  have hST : Γ.Has "full_sort_tmp" Spec.fullSortTmpSpec :=
    mem_specs_has hSat (by simp [Spec.specs]) (by xfree)
  have hDfs : Γ.Has "full_min_lit_dfs_m8" Spec.fullMinLitDfsSpec :=
    mem_specs_has hSat (by simp [Spec.specs]) (by xfree)
  have hSL : Γ.Has "full_shrink_lower_m8" Spec.fullShrinkLowerSpec :=
    mem_specs_has hSat (by simp [Spec.specs]) (by xfree)
  have hSB : Γ.Has "full_shrink_blk_bool_m8" Spec.fullShrinkBlkBoolSpec :=
    mem_specs_has hSat (by simp [Spec.specs]) (by xfree)
  simp only [Src.Minimize.fns, Spec.specs]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, full_min_mark_wp Γ⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, full_sort_tmp_wp Γ⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, full_min_lit_dfs_m8_wp Γ hMm⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, full_shrink_lower_m8_wp Γ hMm hDfs⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, full_shrink_blk_bool_m8_wp Γ hMm hSL⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, full_min_shrink_m6_wp Γ hST hMm hSB hDfs⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Minimize
