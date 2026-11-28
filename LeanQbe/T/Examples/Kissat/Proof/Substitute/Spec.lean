/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Arena.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Clause.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Collect.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Extend.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Internal.Spec
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts3
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
public import LeanQbe.T.Examples.Kissat.Src.Substitute
public import LeanQbe.T.Logic.CanonicalEnv

/-!
# Canonical Specifications for `Kissat.Src.Substitute` (`6` Functions)

Defines `deps`, the canonical per-function contracts (`Spec`) for all `6` functions in
`Src.Substitute.fns`, `Spec.XFree` lemmas, `SpecEntry` list `specs` matching `Src.Substitute.fns`
order 1:1, and `Env.Sat` capability projections (`deps_has_*` and `has_*`).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Substitute.Spec

open Std.Sat
open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Src.Substitute

public section

/-! ## 1. External Dependencies & Canonical Per-Function Specs -/

/-- Canonical upstream callee environment required by `Src.Substitute`. -/
@[expose] def deps : List SpecEntry :=
  Arena.Spec.specs ++ Backtrack.Spec.specs ++ Clause.Spec.specs ++ Collect.Spec.specs ++
  Extend.Spec.specs ++ Internal.Spec.specs ++ PropSearch.Spec.specs

/-- Canonical contract for `full_tarjan_pop_scc`. -/
abbrev fullTarjanPopSccSpec : Spec [i64, i32, i32, i32] [.bool] :=
  Proof.Spec.fullTarjanPopSccSpec

/-- Canonical contract for `full_tarjan_scc`. -/
abbrev fullTarjanSccSpec : Spec [i64] [i64] :=
  Proof.Spec.fullTarjanSccSpec

/-- Canonical `FullM6HdrMem`-threaded contract for `full_subst_elim_vars`. -/
@[expose] def fullSubstElimVarsM6Spec : Spec [i64, i64] [.bool] :=
  fun (h, ucnt, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (ext : List (BitVec 64))
      (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrInvW c F0 F_cur ext s ∧ s.core.cur_level = 0 ∧
      FullReprEquiv F_cur s ∧ ucnt.toNat ≤ c.max_vars ∧
      (∀ k < ucnt.toNat,
        (s.scratch.shrink_stk[k]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause [(s.scratch.shrink_stk[k]?.getD 0#32).toNat])) ∧
      (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ (ok : Bool) ext' s' m',
        FullM6HdrInvW c F0 F_cur ext' s' → s'.core.cur_level = 0 →
        s'.core.cur_vars = s.core.cur_vars → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
        FullReprEquiv F_cur s' → (ok = false → F0.Unsat) →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q (ok, ()) m'

/-- Canonical contract for `full_subst_rewrite_bins`. -/
abbrev fullSubstRewriteBinsSpec : Spec [i64] [.bool] :=
  Proof.Spec.fullSubstRewriteBinsSpec

/-- Canonical contract for `full_subst_rewrite_ar`. -/
abbrev fullSubstRewriteArSpec : Spec [i64] [.bool] :=
  Proof.Spec.fullSubstRewriteArSpec

/-- Canonical `FullM6HdrMem`-threaded contract for `full_substitute`. -/
@[expose] def fullSubstituteM6Spec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrInv c F0 ext s ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ r ext' s' m',
      FullM6HdrInv c F0 ext' s' → s'.core.cur_level = 0 →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

/-! ## 2. Canonical `SpecEntry` Table & Structural Theorems -/

/-- Canonical `SpecEntry` table matching `Src.Substitute.fns` 1:1. -/
@[expose] def specs : List SpecEntry :=
  [ { name := "full_tarjan_pop_scc", as := [i64, i32, i32, i32], rs := [.bool],
      spec := fullTarjanPopSccSpec, noExit := true }
  , { name := "full_tarjan_scc", as := [i64], rs := [i64],
      spec := fullTarjanSccSpec, noExit := true }
  , { name := "full_subst_elim_vars", as := [i64, i64], rs := [.bool],
      spec := fullSubstElimVarsM6Spec, noExit := true }
  , { name := "full_subst_rewrite_bins", as := [i64], rs := [.bool],
      spec := fullSubstRewriteBinsSpec, noExit := true }
  , { name := "full_subst_rewrite_ar", as := [i64], rs := [.bool],
      spec := fullSubstRewriteArSpec, noExit := true }
  , { name := "full_substitute", as := [i64], rs := [i64],
      spec := fullSubstituteM6Spec, noExit := true } ]

theorem fullTarjanPopSccSpec_xfree : Spec.XFree fullTarjanPopSccSpec := by xfree
theorem fullTarjanSccSpec_xfree : Spec.XFree fullTarjanSccSpec := by xfree
theorem fullSubstElimVarsM6Spec_xfree : Spec.XFree fullSubstElimVarsM6Spec := by xfree
theorem fullSubstRewriteBinsSpec_xfree : Spec.XFree fullSubstRewriteBinsSpec := by xfree
theorem fullSubstRewriteArSpec_xfree : Spec.XFree fullSubstRewriteArSpec := by xfree
theorem fullSubstituteM6Spec_xfree : Spec.XFree fullSubstituteM6Spec := by xfree

theorem specs_sigs : specs.map SpecEntry.sig = Src.Substitute.fns.map Fn.sig := rfl

theorem specs_nodup : (specs.map SpecEntry.name).Nodup := by decide

theorem specs_noExit : specs.all SpecEntry.noExit = true := rfl

theorem specs_xfree : ∀ e ∈ specs, Spec.XFree e.spec := by
  intro e he
  simp only [specs, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  · exact fullTarjanPopSccSpec_xfree
  · exact fullTarjanSccSpec_xfree
  · exact fullSubstElimVarsM6Spec_xfree
  · exact fullSubstRewriteBinsSpec_xfree
  · exact fullSubstRewriteArSpec_xfree
  · exact fullSubstituteM6Spec_xfree

/-! ## 3. `Env.Sat` Projections (`deps` and `specs`) -/

theorem deps_has_full_arena_next {Γ : Env} (h : Γ.Sat deps) :
    Γ.Has "full_arena_next" fullArenaNextSpec :=
  Arena.Spec.has_full_arena_next h.left.left.left.left.left.left

theorem deps_has_full_backtrack {Γ : Env} (h : Γ.Sat deps) :
    Γ.Has "full_backtrack" fullBacktrackSpec :=
  Backtrack.Spec.has_full_backtrack h.left.left.left.left.left.right

theorem deps_has_full_add_bin {Γ : Env} (h : Γ.Sat deps) :
    Γ.Has "full_add_bin" fullAddBinSpec :=
  Clause.Spec.has_full_add_bin h.left.left.left.left.right

theorem deps_has_full_add_unit {Γ : Env} (h : Γ.Sat deps) :
    Γ.Has "full_add_unit" fullAddUnitSpec :=
  Clause.Spec.has_full_add_unit h.left.left.left.left.right

theorem deps_has_full_arena_sweep {Γ : Env} (h : Γ.Sat deps) :
    Γ.Has "full_arena_sweep" fullArenaSweepSpec :=
  Collect.Spec.has_full_arena_sweep h.left.left.left.right

theorem deps_has_full_extend_push2 {Γ : Env} (h : Γ.Sat deps) :
    Γ.Has "full_extend_push2" fullExtendPush2Spec :=
  Env.Has.of_le
    (Env.Sat.has h.left.left.right
      (List.getElem_mem (l := Extend.Spec.specs) (n := 0) (by decide))
      Extend.Spec.fullExtendPush2Spec_xfree)
    Extend.Spec.base_le_fullExtendPush2Spec

theorem deps_has_full_set_inactive {Γ : Env} (h : Γ.Sat deps) :
    Γ.Has "full_set_inactive" Internal.Spec.fullSetInactiveSpec :=
  Internal.Spec.has_full_set_inactive h.left.right

theorem deps_has_full_propagate {Γ : Env} (h : Γ.Sat deps) :
    Γ.Has "full_propagate" PropSearch.Spec.propagateM6Spec :=
  PropSearch.Spec.has_full_propagate h.right

theorem has_full_tarjan_pop_scc {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_tarjan_pop_scc" fullTarjanPopSccSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 0) (by decide))
    fullTarjanPopSccSpec_xfree

theorem has_full_tarjan_scc {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_tarjan_scc" fullTarjanSccSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 1) (by decide))
    fullTarjanSccSpec_xfree

theorem has_full_subst_elim_vars {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_subst_elim_vars" fullSubstElimVarsM6Spec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 2) (by decide))
    fullSubstElimVarsM6Spec_xfree

theorem has_full_subst_rewrite_bins {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_subst_rewrite_bins" fullSubstRewriteBinsSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 3) (by decide))
    fullSubstRewriteBinsSpec_xfree

theorem has_full_subst_rewrite_ar {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_subst_rewrite_ar" fullSubstRewriteArSpec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 4) (by decide))
    fullSubstRewriteArSpec_xfree

theorem has_full_substitute {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_substitute" fullSubstituteM6Spec :=
  Env.Sat.has h (List.getElem_mem (l := specs) (n := 5) (by decide))
    fullSubstituteM6Spec_xfree

end

end LeanQbe.T.Examples.Kissat.Proof.Substitute.Spec
