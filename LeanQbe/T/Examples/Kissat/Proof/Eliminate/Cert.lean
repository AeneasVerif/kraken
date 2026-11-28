/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Logic.CanonicalEnv
public import LeanQbe.T.Examples.Kissat.Src.Eliminate
public import LeanQbe.T.Examples.Kissat.Proof.Eliminate.Spec

import LeanQbe.T.Examples.Kissat.Proof.Eliminate.Wp0
import LeanQbe.T.Examples.Kissat.Proof.Eliminate.Wp0b
import LeanQbe.T.Examples.Kissat.Proof.Eliminate.Wp1
import LeanQbe.T.Examples.Kissat.Proof.Eliminate.Wp2
import LeanQbe.T.Examples.Kissat.Proof.Eliminate.Wp3
import LeanQbe.T.Examples.Kissat.Proof.Eliminate.Wp4

/-!
# Kissat Eliminate L5 Segment Certificate (`Proof/Eliminate/Cert`)

Assembles all `16` flat `CanonicalEnv` WP proofs for `Src.Eliminate.fns` into
`theorem cert : SegCert Spec.deps Src.Eliminate.fns Spec.specs`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Eliminate

open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.Examples.Kissat

private theorem impl_of_noExit_wp {Γ : Env} {nm : Sym} {as rs : List Ty}
    {body : Func as rs} {S : Spec as rs}
    (hwp : ∀ xs m Q X, S xs m Q X → Func.wp Γ body xs m Q X) :
    SpecEntry.Impl Γ ⟨nm, as, rs, body⟩ ⟨nm, as, rs, S, true⟩ :=
  ⟨⟨rfl, rfl, rfl⟩, fun xs m Q _X hs =>
    wp_mono (fun _ _ h => h) (fun _ _ _ _ h => h.elim) _ m (hwp xs m Q _ hs)⟩

public section

/-- Canonical `L5` segment certificate for all `16` functions of `Src.Eliminate.fns`. -/
theorem cert : SegCert Spec.deps Src.Eliminate.fns Spec.specs := by
  intro Γ hD hΓ
  dsimp only [Src.Eliminate.fns, Spec.specs, TableImpl]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · exact impl_of_noExit_wp (full_bve_collect_m7_wp Γ)
  · exact impl_of_noExit_wp (full_bve_resolve_pair_wp Γ)
  · exact impl_of_noExit_wp (full_bve_weaken_wp Γ
      (Spec.deps_has_full_extend_push2 hD)
      (Spec.deps_has_full_extend_push_cl hD)
      (Spec.deps_has_full_delete_binary hD))
  · exact impl_of_noExit_wp (full_bve_commit_res_wp Γ
      (Spec.deps_has_full_add_unit hD)
      (Spec.deps_has_full_add_bin hD)
      (Spec.deps_has_full_alloc_cl hD)
      (Spec.deps_has_full_watch_push hD))
  · exact impl_of_noExit_wp (full_bve_ext_need_wp Γ)
  · exact impl_of_noExit_wp (full_bve_weaken_unit_fid_wp Γ
      (Spec.deps_has_full_delete_binary hD))
  · exact impl_of_noExit_wp (full_bve_var_m7_wp Γ
      (Spec.has_full_bve_collect_m7 hΓ)
      (Spec.has_full_bve_ext_need hΓ)
      (Spec.has_full_bve_weaken_unit_fid hΓ)
      (Spec.deps_has_full_set_inactive hD)
      (Spec.deps_has_full_bve_gates_fid hD)
      (Spec.deps_has_full_bve_gates_m7 hD)
      (Spec.has_full_bve_resolve_pair hΓ)
      (Spec.deps_has_full_assign_lvl hD)
      (Spec.deps_has_full_wstack_defrag hD)
      (Spec.has_full_bve_weaken hΓ)
      (Spec.has_full_bve_commit_res hΓ)
      (Spec.deps_has_full_dense_flush_units_m7 hD))
  · exact impl_of_noExit_wp (full_bve_var_key_m7_wp Γ
      (Spec.deps_has_full_dense_occ_cnt_fid hD)
      (Spec.deps_has_f64u_to_u64 hD))
  · exact impl_of_noExit_wp (full_bve_heap_up_m7_wp Γ)
  · exact impl_of_noExit_wp (full_bve_heap_down_m7_wp Γ)
  · exact impl_of_noExit_wp (full_bve_heap_push_m7_wp Γ
      (Spec.has_full_bve_var_key_m7 hΓ)
      (Spec.has_full_bve_heap_up_m7 hΓ)
      (Spec.has_full_bve_heap_down_m7 hΓ))
  · exact impl_of_noExit_wp (full_bve_heap_pop_m7_wp Γ
      (Spec.has_full_bve_heap_down_m7 hΓ))
  · exact impl_of_noExit_wp (full_bve_collect_nbrs_m7_wp Γ)
  · exact impl_of_noExit_wp (full_elim_bve_m7_wp Γ
      (Spec.deps_has_full_dense_flush_units_m7 hD)
      (Spec.has_full_bve_heap_push_m7 hΓ)
      (Spec.has_full_bve_heap_pop_m7 hΓ)
      (Spec.has_full_bve_collect_nbrs_m7 hΓ)
      (Spec.has_full_bve_var_m7 hΓ))
  · exact impl_of_noExit_wp (full_has_elim_cands_fid_wp Γ)
  · exact impl_of_noExit_wp (full_eliminate_m6_wp Γ
      (Spec.deps_has_full_elim_dticks hD)
      (Spec.deps_has_f64u_nlogpown hD)
      (Spec.deps_has_f64u_mul hD)
      (Spec.deps_has_f64u_to_u64 hD)
      (Spec.deps_has_full_scale_delta hD)
      (Spec.has_full_has_elim_cands_fid hΓ)
      (Spec.deps_has_full_enter_dense_ex_fid hD)
      (Spec.deps_has_full_forward_sub_m7 hD)
      (Spec.deps_has_full_rebuild_watches hD)
      (Spec.has_full_elim_bve_m7 hΓ)
      (Spec.deps_has_full_update_classify_fid hD))

end

end LeanQbe.T.Examples.Kissat.Proof.Eliminate
