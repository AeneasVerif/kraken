/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Minimize.Spec
public import LeanQbe.T.Examples.Kissat.Src.Minimize
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Lib.ContractLemmas
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
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Lib
open LeanQbe.T.Examples.Kissat.Src.Minimize

public section

theorem specs_sigs : Spec.specs.map SpecEntry.sig = Src.Minimize.fns.map Fn.sig := rfl

theorem specs_nodup : (Spec.specs.map SpecEntry.name).Nodup := by decide

theorem specs_noExit : ∀ e ∈ Spec.specs, e.noExit = true := by
  intro e he
  simp only [Spec.specs, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem cert : SegCert [] Src.Minimize.fns Spec.specs := by
  intro Γ _ hSat
  have hMm : Γ.Has "full_min_mark" Spec.minMarkSpec :=
    SpecTable.has_at hSat 0 rfl (by unfold Spec.minMarkSpec; exact FullContract.toSpec_xfree _)
  have hST : Γ.Has "full_sort_tmp" Spec.sortTmpSpec :=
    SpecTable.has_at hSat 1 rfl (by unfold Spec.sortTmpSpec; exact FullContract.toSpec_xfree _)
  have hDfs : Γ.Has "full_min_lit_dfs_m8" Spec.minLitDfsSpec :=
    SpecTable.has_at hSat 2 rfl (by unfold Spec.minLitDfsSpec; exact FullContract.toSpec_xfree _)
  have hSL : Γ.Has "full_shrink_lower_m8" Spec.shrinkLowerSpec :=
    SpecTable.has_at hSat 3 rfl (by unfold Spec.shrinkLowerSpec; exact FullContract.toSpec_xfree _)
  have hSB : Γ.Has "full_shrink_blk_bool_m8" Spec.shrinkBlkSpec :=
    SpecTable.has_at hSat 4 rfl (by unfold Spec.shrinkBlkSpec; exact FullContract.toSpec_xfree _)
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
