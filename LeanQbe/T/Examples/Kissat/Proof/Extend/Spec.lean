/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts3
public import LeanQbe.T.Examples.Kissat.Src.Extend
public import LeanQbe.T.Logic.CanonicalEnv

/-!
# Canonical Specifications for `Kissat.Src.Extend` (`5` Functions)

Defines one canonical `Spec` per function in `Src.Extend.fns`, proves `Spec.XFree`, provides
`Spec.Le` adapters to `Proof.Spec.fullExtendPush{2,Cl}Spec` when downstream callers only need
the base slice, and aligns `Spec.specs` 1:1 with `Src.Extend.fns`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Extend.Spec

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Src.Extend

public section

/-- Canonical specification for `full_extend_push2` (strengthened with `tarjan_mark`
preservation for `Eliminate` callers). -/
@[expose] def fullExtendPush2Spec : Spec [i64, i32, i32] [.bool] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _blk, _ot, ()) s => h = c.hdr ∧ s.scratch.extend_len ≤ c.extend_cap)
    (fun c _ _ s s' =>
      s'.scratch.last_learned = s.scratch.last_learned ∧
      s'.scratch.extend_len ≤ c.extend_cap ∧
      s'.scratch.scratch_buf = s.scratch.scratch_buf ∧
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark)

/-- Canonical specification for `full_extend_push_cl` (strengthened with `tarjan_mark`
preservation for `Eliminate` callers). -/
@[expose] def fullExtendPushClSpec : Spec [i64, i32, i32] [.bool] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _blk, _cref, ()) s => h = c.hdr ∧ s.scratch.extend_len ≤ c.extend_cap)
    (fun c _ _ s s' =>
      s'.scratch.last_learned = s.scratch.last_learned ∧
      s'.scratch.extend_len ≤ c.extend_cap ∧
      s'.scratch.scratch_buf = s.scratch.scratch_buf ∧
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark)

/-- Canonical specification for `full_extend_core_fid`. -/
abbrev fullExtendCoreFidSpec : Spec [i64] [] :=
  Proof.Spec.fullExtendSpec

/-- Canonical specification for `full_unperm_fid`. -/
abbrev fullUnpermFidSpec : Spec [i64] [] :=
  Proof.Spec.fullExtendSpec

/-- Canonical specification for `full_extend`. -/
abbrev fullExtendSpec : Spec [i64] [] :=
  Proof.Spec.fullExtendSpec

/-- Weakening adapter from canonical `fullExtendPush2Spec` to base
`Proof.Spec.fullExtendPush2Spec`. -/
theorem base_le_fullExtendPush2Spec :
    Proof.Spec.fullExtendPush2Spec.Le fullExtendPush2Spec := by
  rintro ⟨h_ptr, blk, ot, ⟨⟩⟩ m Q X ⟨c, s, R, hpre, hlen, hm, hQ⟩
  exact ⟨c, s, R, hpre, hlen, hm,
    fun r s' m' hcore hlen' ⟨h1, h2, h3, _⟩ hm' => hQ r s' m' hcore hlen' ⟨h1, h2, h3⟩ hm'⟩

/-- Weakening adapter from canonical `fullExtendPushClSpec` to base
`Proof.Spec.fullExtendPushClSpec`. -/
theorem base_le_fullExtendPushClSpec :
    Proof.Spec.fullExtendPushClSpec.Le fullExtendPushClSpec := by
  rintro ⟨h_ptr, blk, cref, ⟨⟩⟩ m Q X ⟨c, s, R, hpre, hlen, hm, hQ⟩
  exact ⟨c, s, R, hpre, hlen, hm,
    fun r s' m' hcore hlen' ⟨h1, h2, h3, _⟩ hm' => hQ r s' m' hcore hlen' ⟨h1, h2, h3⟩ hm'⟩

theorem fullExtendPush2Spec_xfree : fullExtendPush2Spec.XFree := by xfree
theorem fullExtendPushClSpec_xfree : fullExtendPushClSpec.XFree := by xfree
theorem fullExtendCoreFidSpec_xfree : fullExtendCoreFidSpec.XFree := by xfree
theorem fullUnpermFidSpec_xfree : fullUnpermFidSpec.XFree := by xfree
theorem fullExtendSpec_xfree : fullExtendSpec.XFree := by xfree

/-- Canonical `SpecEntry` list matching `Src.Extend.fns` order 1:1. -/
@[expose] def specs : List SpecEntry :=
  [ { name := "full_extend_push2", as := [i64, i32, i32], rs := [.bool],
      spec := fullExtendPush2Spec, noExit := true }
  , { name := "full_extend_push_cl", as := [i64, i32, i32], rs := [.bool],
      spec := fullExtendPushClSpec, noExit := true }
  , { name := "full_extend_core_fid", as := [i64], rs := [],
      spec := fullExtendCoreFidSpec, noExit := true }
  , { name := "full_unperm_fid", as := [i64], rs := [],
      spec := fullUnpermFidSpec, noExit := true }
  , { name := "full_extend", as := [i64], rs := [],
      spec := fullExtendSpec, noExit := true } ]

theorem specs_xfree : ∀ e ∈ specs, e.spec.XFree := by
  intro e he
  simp only [specs, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · exact fullExtendPush2Spec_xfree
  · exact fullExtendPushClSpec_xfree
  · exact fullExtendCoreFidSpec_xfree
  · exact fullUnpermFidSpec_xfree
  · exact fullExtendSpec_xfree

theorem specs_sigs : specs.map SpecEntry.sig = Src.Extend.fns.map Fn.sig := rfl

end

end LeanQbe.T.Examples.Kissat.Proof.Extend.Spec
