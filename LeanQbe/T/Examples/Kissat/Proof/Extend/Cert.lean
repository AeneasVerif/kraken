/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Extend.Spec
public import LeanQbe.T.Examples.Kissat.Src.Extend
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Extend.WpPush
import LeanQbe.T.Examples.Kissat.Proof.Extend.WpExtend

/-!
# Canonical `SegCert` Assembly for `Kissat.Src.Extend` (`5` Functions)

Proves `SegCert [] Src.Extend.fns Spec.specs` using `Env.Sat.has`, `TableImpl`,
and the WP proofs in `Proof.Extend.WpPush` and `Proof.Extend.WpExtend`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Extend

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src.Extend

public section

private theorem mem_specs_has {Γ : Env} (hSat : Γ.Sat Spec.specs)
    {nm : Sym} {as bs : List Ty} {sp : Spec as bs}
    (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ Spec.specs) (hx : sp.XFree) :
    Γ.Has nm sp :=
  Env.Sat.has hSat hmem hx

theorem cert : SegCert [] Src.Extend.fns Spec.specs := by
  intro Γ _ hOwn
  have hCore : Γ.Has "full_extend_core_fid" Spec.fullExtendCoreFidSpec :=
    mem_specs_has hOwn (by simp [Spec.specs]) Spec.fullExtendCoreFidSpec_xfree
  have hUnperm : Γ.Has "full_unperm_fid" Spec.fullUnpermFidSpec :=
    mem_specs_has hOwn (by simp [Spec.specs]) Spec.fullUnpermFidSpec_xfree
  simp only [TableImpl, Src.Extend.fns, Src.Extend.extend_fns, Spec.specs]
  refine ⟨?_, ?_, ?_, ?_, ?_, trivial⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, full_extend_push2_wp Γ⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, full_extend_push_cl_wp Γ⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, full_extend_core_fid_wp Γ⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, full_unperm_fid_wp Γ⟩
  · exact ⟨⟨rfl, rfl, rfl⟩, full_extend_wp Γ hCore hUnperm⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Extend
