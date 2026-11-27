/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Heap.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Limits.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Tiers.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts3
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
public import LeanQbe.T.Examples.Kissat.Src.Decide
public import LeanQbe.T.Logic.CanonicalEnv

/-!
# Canonical Specification Table for `Kissat.Src.Decide` (`Proof.Decide.Spec`)

Reuses `Proof.Spec.fullNextDecVarSpec`, `Proof.Spec.fullDecideSpec`, and
`Proof.Spec.m6HdrDecideSpec` directly, defines `fullRandecVarLvlSpec` and `fullRandecVarSpec`,
and aligns `Spec.specs` 1:1 with `Src.Decide.fns` (`0` legacy imports, `0` `@[expose]` on
theorems/lemmas/sections).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Decide.Spec

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Limits.Spec
open LeanQbe.T.Examples.Kissat.Src

/-- Canonical contract for `full_randec_var_lvl_fid(h, max_lvl)`. -/
@[expose] def fullRandecVarLvlSpec : Spec [i64, i64] [i64] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _ml, ()) _ => h = c.hdr)
    (fun _ _ (r, ()) s s' =>
      FullExtScratchPres s s' ∧ M7GuPrefixPres s s' ∧
      (r = 0xFFFFFFFFFFFFFFFF#64 ∨
        (r.toNat < s.core.cur_vars ∧
          (s.core.flags[r.toNat]?.getD 0#32 &&& 1#32) ≠ 0#32 ∧
          s.core.vals[2 * r.toNat]?.getD 0#8 = 0#8)))

/-- Canonical contract for `full_randec_var_m7(h)`. -/
@[expose] def fullRandecVarSpec : Spec [i64] [i64] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, ()) _ => h = c.hdr)
    (fun _ _ (r, ()) s s' =>
      FullExtScratchPres s s' ∧ M7GuPrefixPres s s' ∧
      (r = 0xFFFFFFFFFFFFFFFF#64 ∨
        (r.toNat < s.core.cur_vars ∧
          (s.core.flags[r.toNat]?.getD 0#32 &&& 1#32) ≠ 0#32 ∧
          s.core.vals[2 * r.toNat]?.getD 0#8 = 0#8)))

theorem fullNextDecVarSpec_xfree : Spec.XFree fullNextDecVarSpec := by xfree

theorem fullRandecVarLvlSpec_xfree : Spec.XFree fullRandecVarLvlSpec := by xfree

theorem fullRandecVarSpec_xfree : Spec.XFree fullRandecVarSpec := by xfree

theorem fullDecideSpec_xfree : Spec.XFree fullDecideSpec := by xfree

theorem m6HdrDecideSpec_xfree : Spec.XFree m6HdrDecideSpec :=
  fun _ _ _ _ _ h => m6HdrDecideSpec_monoX h

theorem fullNextDecVarSpec_le_fullRandecVarSpec :
    fullNextDecVarSpec.Le fullRandecVarSpec := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, hc, hlen, hm, hQ⟩
  exact ⟨c, s, R, hc, hlen, hm, fun ⟨r, ⟨⟩⟩ s' m' hcore hlen' ⟨hp, _, hr⟩ hm' =>
    hQ (r, ()) s' m' hcore hlen' ⟨hp, hr.imp id fun h2 => ⟨h2.1, h2.2.2⟩⟩ hm'⟩

/-- Upstream capability dependencies for `Src.Decide`. -/
@[expose] def deps : List SpecEntry :=
  Backtrack.Spec.specs ++ Float64.Spec.specs ++ Heap.Spec.specs ++
  Limits.Spec.specs ++ Tiers.Spec.specs

/-- Canonical `SpecEntry` table matching `Src.Decide.fns` 1-to-1. -/
@[expose] def specs : List SpecEntry :=
  [ ⟨"full_next_dec_var",      [i64],      [i64], fullNextDecVarSpec,   true⟩
  , ⟨"full_randec_var_lvl_fid", [i64, i64], [i64], fullRandecVarLvlSpec, true⟩
  , ⟨"full_randec_var_m7",      [i64],      [i64], fullRandecVarSpec,    true⟩
  , ⟨"full_decide_m7",          [i64],      [i64], fullDecideSpec,       true⟩
  , ⟨"m6_hdr_decide_fid",       [i64],      [i64], m6HdrDecideSpec,      true⟩ ]

theorem specs_xfree : ∀ e ∈ specs, Spec.XFree e.spec := by
  intro e he
  simp only [specs, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · exact fullNextDecVarSpec_xfree
  · exact fullRandecVarLvlSpec_xfree
  · exact fullRandecVarSpec_xfree
  · exact fullDecideSpec_xfree
  · exact m6HdrDecideSpec_xfree

theorem specs_sigs : specs.map SpecEntry.sig = Decide.fns.map Fn.sig := rfl

theorem specs_nodup : (specs.map SpecEntry.name).Nodup := by decide

theorem specs_noExit : specs.all SpecEntry.noExit = true := rfl

theorem has_full_next_dec_var {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_next_dec_var" fullNextDecVarSpec :=
  Env.Sat.has h List.mem_cons_self fullNextDecVarSpec_xfree

theorem has_full_randec_var_lvl_fid {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_randec_var_lvl_fid" fullRandecVarLvlSpec :=
  Env.Sat.has h (.tail _ List.mem_cons_self) fullRandecVarLvlSpec_xfree

theorem has_full_randec_var_m7 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_randec_var_m7" fullRandecVarSpec :=
  Env.Sat.has h (.tail _ (.tail _ List.mem_cons_self)) fullRandecVarSpec_xfree

theorem has_full_decide_m7 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_decide_m7" fullDecideSpec :=
  Env.Sat.has h (.tail _ (.tail _ (.tail _ List.mem_cons_self))) fullDecideSpec_xfree

theorem has_m6_hdr_decide_fid {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "m6_hdr_decide_fid" m6HdrDecideSpec :=
  Env.Sat.has h (.tail _ (.tail _ (.tail _ (.tail _ List.mem_cons_self))))
    m6HdrDecideSpec_xfree

end LeanQbe.T.Examples.Kissat.Proof.Decide.Spec
