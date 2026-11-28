/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Logic.CanonicalEnv
public import LeanQbe.T.Examples.Kissat.Src.Watch
public import LeanQbe.T.Examples.Kissat.Proof.Watch.Spec

import LeanQbe.T.Examples.Kissat.Proof.Watch.Wp0
import LeanQbe.T.Examples.Kissat.Proof.Watch.Wp1
import LeanQbe.T.Examples.Kissat.Proof.Watch.Wp2
import LeanQbe.T.Examples.Kissat.Proof.Watch.Wp3
import LeanQbe.T.Examples.Kissat.Proof.Watch.Wp4
import LeanQbe.T.Examples.Kissat.Proof.Watch.Wp5
import LeanQbe.T.Examples.Kissat.Proof.Watch.Wp6
import LeanQbe.T.Examples.Kissat.Proof.Watch.Wp7a
import LeanQbe.T.Examples.Kissat.Proof.Watch.Wp7

/-!
# Kissat Watch L0 Segment Certificate (`Proof/Watch/Cert`)

Assembles all `15` `CanonicalEnv` WP proofs for `Src.Watch.fns` into
`theorem cert : SegCert [] Src.Watch.fns Spec.specs`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Watch

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

/-- Canonical `L0` segment certificate for all `15` functions of `Src.Watch.fns`. -/
theorem cert : SegCert [] Src.Watch.fns Spec.specs := by
  intro Γ _ hΓ
  dsimp only [Src.Watch.fns, Src.Watch.watch_fns, Spec.specs, TableImpl]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · exact impl_of_noExit_wp (full_wsort_sift_wp Γ)
  · exact impl_of_noExit_wp (full_wstack_radix_sort_m6_wp Γ)
  · exact impl_of_noExit_wp (full_wstack_defrag_m6_wp Γ hΓ)
  · exact impl_of_noExit_wp (full_watch_push_slow_m6_wp Γ hΓ)
  · exact impl_of_noExit_wp (full_watch_push_m6_wp Γ hΓ)
  · exact impl_of_noExit_wp (full_wstack_defrag_wp Γ hΓ)
  · exact impl_of_noExit_wp (full_watch_push_wp Γ hΓ)
  · exact impl_of_noExit_wp (full_watch_pop_c0_wp Γ hΓ)
  · exact impl_of_noExit_wp (full_unwatch_large_wp Γ hΓ)
  · exact impl_of_noExit_wp (full_has_bin_wp Γ hΓ)
  · exact impl_of_noExit_wp (full_delete_bin_side_wp Γ hΓ)
  · exact impl_of_noExit_wp (full_delete_binary_wp Γ hΓ)
  · exact impl_of_noExit_wp (full_prioritize_binaries_m6_wp Γ hΓ)
  · exact impl_of_noExit_wp (full_sort_bin_watches_fid_wp Γ hΓ)
  · exact impl_of_noExit_wp (full_has_ternary_wp Γ hΓ)

end

end LeanQbe.T.Examples.Kissat.Proof.Watch
