/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Logic.CanonicalEnv
public import LeanQbe.T.Examples.Kissat.Src.Factor
public import LeanQbe.T.Examples.Kissat.Proof.Factor.Spec

import LeanQbe.T.Examples.Kissat.Proof.Factor.Wp0
import LeanQbe.T.Examples.Kissat.Proof.Factor.WpConnect
import LeanQbe.T.Examples.Kissat.Proof.Factor.WpScan1
import LeanQbe.T.Examples.Kissat.Proof.Factor.WpPickUpd
import LeanQbe.T.Examples.Kissat.Proof.Factor.WpFilter1
import LeanQbe.T.Examples.Kissat.Proof.Factor.WpCommit3
import LeanQbe.T.Examples.Kissat.Proof.Factor.WpTop
import LeanQbe.T.Examples.Kissat.Proof.Factor.WpFactor

/-!
# Kissat Factor L5 Segment Certificate (`Proof/Factor/Cert`)

Assembles all `15` zero-legacy `CanonicalEnv` WP proofs for `Src.Factor.fns` into
`theorem cert : SegCert Spec.deps Src.Factor.fns Spec.specs`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Factor

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

/-- Canonical `L5` segment certificate for all `15` functions of `Src.Factor.fns`. -/
theorem cert : SegCert Spec.deps Src.Factor.fns Spec.specs := by
  intro Γ hDeps hΓ
  dsimp only [Src.Factor.fns, Src.Factor.factor_fns, Spec.specs, TableImpl]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · exact impl_of_noExit_wp (full_bva_steps_cap_fid_wp Γ)
  · exact impl_of_noExit_wp (full_bva_clines_fid_wp Γ)
  · exact impl_of_noExit_wp (full_fheap_up_fid_wp Γ)
  · exact impl_of_noExit_wp (full_fheap_down_fid_wp Γ)
  · exact impl_of_noExit_wp (full_bva_count_lit_deg_fid_wp Γ)
  · exact impl_of_noExit_wp (full_bva_connect_clauses_fid_wp Γ
      (Spec.deps_has_full_fwd_flush_large_m7 hDeps)
      (Spec.deps_has_full_arena_next hDeps)
      (Spec.deps_has_full_watch_push hDeps)
      (Spec.has_full_bva_count_lit_deg_fid hΓ))
  · exact impl_of_noExit_wp (full_bva_match_large_bva_fid_wp Γ)
  · exact impl_of_noExit_wp (full_bva_scan_cands_wp Γ (Spec.has_full_bva_clines_fid hΓ))
  · exact impl_of_noExit_wp (full_bva_pick_cand_wp Γ)
  · exact impl_of_noExit_wp (full_bva_filter_row_wp Γ
      (Spec.has_full_bva_clines_fid hΓ)
      (Spec.has_full_bva_match_large_bva_fid hΓ))
  · exact impl_of_noExit_wp (full_bva_commit_wp Γ
      (Spec.has_full_bva_steps_cap_fid hΓ)
      (Spec.deps_has_full_wstack_defrag hDeps)
      (Spec.deps_has_full_fill_u64_m7 hDeps)
      (Spec.deps_has_full_init_fresh_var hDeps)
      (Spec.deps_has_full_add_bin hDeps)
      (Spec.deps_has_full_alloc_cl hDeps)
      (Spec.deps_has_full_watch_push hDeps)
      (Spec.deps_has_full_unwatch_large hDeps)
      (Spec.deps_has_full_delete_binary hDeps))
  · exact impl_of_noExit_wp (full_bva_try_lit_wp Γ
      (Spec.has_full_bva_steps_cap_fid hΓ)
      (Spec.has_full_bva_scan_cands hΓ)
      (Spec.has_full_bva_pick_cand hΓ)
      (Spec.has_full_bva_filter_row hΓ)
      (Spec.has_full_bva_commit hΓ))
  · exact impl_of_noExit_wp (full_bva_upd_lit_fid_wp Γ
      (Spec.has_full_bva_count_lit_deg_fid hΓ)
      (Spec.has_full_fheap_up_fid hΓ)
      (Spec.has_full_fheap_down_fid hΓ))
  · exact impl_of_noExit_wp (full_factor_wp Γ
      (Spec.has_full_bva_steps_cap_fid hΓ)
      (Spec.has_full_bva_connect_clauses_fid hΓ)
      (Spec.has_full_fheap_up_fid hΓ)
      (Spec.has_full_fheap_down_fid hΓ)
      (Spec.has_full_bva_try_lit hΓ)
      (Spec.has_full_bva_upd_lit_fid hΓ))
  · exact impl_of_noExit_wp (full_has_factor_cands_fid_wp Γ)

end

end LeanQbe.T.Examples.Kissat.Proof.Factor
