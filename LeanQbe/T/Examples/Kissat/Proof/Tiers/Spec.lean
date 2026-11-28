/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
public import LeanQbe.T.Examples.Kissat.Src.Tiers
public import LeanQbe.T.Logic.CanonicalEnv

/-!
# Canonical `Spec` Table for `Kissat/Src/Tiers.lean` (`18` fns)

Single canonical `Spec` per function of `Src.Tiers.fns` (`18` functions, `0` local externs other
than `Float64`), `Spec.XFree` proofs, `specs` table matching `Src.Tiers.fns` 1:1 (`noExit := true`),
`specs_sigs`, `specs_nodup`, and `Env.Has` projections.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Tiers.Spec

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Src.Tiers

@[expose] public section

/-- `FullM6Hdr` tick-accounting spec for `m6_hdr_add_ticks`: strengthens `m6HdrW2aSpec [i64] []`
with `red_refs` and `delayed_len` scratch framing for probing/vivification BCP. -/
def m6HdrAddTicksSpec : Spec [i64, i64] [] :=
  fun (h, _ticks, ()) m Q _ =>
    ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
      (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
        s'.core = s.core → s'.LengthsOk c → M6HdrScratchPres s s' →
        s'.scratch.red_refs = s.scratch.red_refs →
        s'.scratch.delayed_len = s.scratch.delayed_len →
        M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m'

/-- Read-only `FullM6Hdr` watermark lookup spec for `m6_hdr_get_watermark`: strengthens
`m6HdrW2aSpec [i64] [i64]` with `s'.scratch.red_refs = s.scratch.red_refs`. -/
def m6HdrGetWatermarkSpec : Spec [i64, i64] [i64] :=
  fun (h, _kind, ()) m Q _ =>
    ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
      (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ (r : BitVec 64) (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
        s'.core = s.core → s'.LengthsOk c → M6HdrScratchPres s s' →
        s'.scratch.red_refs = s.scratch.red_refs →
        M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

/-- Canonical `18`-row specification table aligned 1:1 with `Src.Tiers.fns`. -/
def specs : List SpecEntry :=
  [ ⟨"m6_hdr_init",                 [i64],           [],      m6HdrInitSpec,             true⟩
  , ⟨"m6_ext_ensure_init",          [i64],           [],      m6ExtEnsureInitSpec,       true⟩
  , ⟨"m6_hdr_add_ticks",            [i64, i64],      [],      m6HdrAddTicksSpec,         true⟩
  , ⟨"m6_hdr_sync_legacy_tiers",    [i64],           [],      m6HdrW2aSpec [] [],        true⟩
  , ⟨"m6_hdr_recompute_tiers_mode", [i64, i64],      [],      m6HdrW2aSpec [i64] [],     true⟩
  , ⟨"m6_hdr_recompute_tiers",      [i64],           [],      m6HdrW2aSpec [] [],        true⟩
  , ⟨"m6_hdr_update_tier_limits",   [i64],           [],      m6HdrW2aSpec [] [],        true⟩
  , ⟨"m6_hdr_record_used",          [i64, i64],      [],      m6HdrW2aSpec [i64] [],     true⟩
  , ⟨"m6_hdr_get_tier1",            [i64, .bool],    [i64],   m6HdrW2aSpec [.bool] [i64], true⟩
  , ⟨"m6_hdr_get_tier2",            [i64, .bool],    [i64],   m6HdrW2aSpec [.bool] [i64], true⟩
  , ⟨"m6_hdr_delaying",             [i64, i64],      [.bool], m6HdrW2aSpec [i64] [.bool], true⟩
  , ⟨"m6_hdr_bump_delay",           [i64, i64],      [],      m6HdrW2aSpec [i64] [],     true⟩
  , ⟨"m6_hdr_reduce_delay",         [i64, i64],      [],      m6HdrW2aSpec [i64] [],     true⟩
  , ⟨"m6_hdr_get_watermark",        [i64, i64],      [i64],   m6HdrGetWatermarkSpec,     true⟩
  , ⟨"m6_hdr_set_watermark",        [i64, i64, i64], [],      m6HdrW2aSpec [i64, i64] [], true⟩
  , ⟨"m6_hdr_dr_init",              [i64],           [],      m6HdrDrMutSpec,            true⟩
  , ⟨"m6_hdr_dr_update",            [i64],           [],      m6HdrDrMutSpec,            true⟩
  , ⟨"m6_hdr_dr_allow",             [i64],           [.bool], m6HdrDrAllowSpec,          true⟩
  ]

end

public section

/-! ## `Spec.XFree` Proofs & Table Invariants -/

theorem m6HdrInitSpec_xfree : Spec.XFree m6HdrInitSpec := by xfree

theorem m6ExtEnsureInitSpec_xfree : Spec.XFree m6ExtEnsureInitSpec := by xfree

theorem m6HdrAddTicksSpec_monoX {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post []}
    {X X' : XPost} (h : m6HdrAddTicksSpec xs m Q X) : m6HdrAddTicksSpec xs m Q X' := by
  rcases xs with ⟨_, _, ⟨⟩⟩; exact h

theorem m6HdrAddTicksSpec_xfree : Spec.XFree m6HdrAddTicksSpec :=
  fun _ _ _ _ _ h => m6HdrAddTicksSpec_monoX h

theorem m6HdrW2a_le_addTicks : (m6HdrW2aSpec [i64] []).Le m6HdrAddTicksSpec := by
  rintro ⟨h, t, ⟨⟩⟩ m Q X hW
  obtain ⟨c, ext, s, R, hc, hcfg, hext, hlen, hm, hQ⟩ := m6HdrW2aSpec_elim hW
  exact ⟨c, ext, s, R, hc, hcfg, hext, hlen, hm,
    fun ext' s' m' hco hl hm6 _ _ => hQ () ext' s' m' hco hl hm6⟩

theorem m6HdrGetWatermarkSpec_monoX {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post [i64]}
    {X X' : XPost} (h : m6HdrGetWatermarkSpec xs m Q X) :
    m6HdrGetWatermarkSpec xs m Q X' := by
  rcases xs with ⟨_, _, ⟨⟩⟩; exact h

theorem m6HdrGetWatermarkSpec_xfree : Spec.XFree m6HdrGetWatermarkSpec :=
  fun _ _ _ _ _ h => m6HdrGetWatermarkSpec_monoX h

theorem m6HdrW2a_le_getWatermark :
    (m6HdrW2aSpec [i64] [i64]).Le m6HdrGetWatermarkSpec := by
  rintro ⟨h, k, ⟨⟩⟩ m Q X hW
  obtain ⟨c, ext, s, R, hc, hcfg, hext, hlen, hm, hQ⟩ := m6HdrW2aSpec_elim hW
  exact ⟨c, ext, s, R, hc, hcfg, hext, hlen, hm,
    fun r ext' s' m' hco hl hm6 _ => hQ (r, ()) ext' s' m' hco hl hm6⟩

theorem m6HdrW2aSpec_xfree (ea rs : List Ty) : Spec.XFree (m6HdrW2aSpec ea rs) :=
  fun _ _ _ _ _ h => m6HdrW2aSpec_monoX h

theorem m6HdrDrMutSpec_xfree : Spec.XFree m6HdrDrMutSpec :=
  fun _ _ _ _ _ h => m6HdrDrMutSpec_monoX h

theorem m6HdrDrAllowSpec_xfree : Spec.XFree m6HdrDrAllowSpec :=
  fun _ _ _ _ _ h => m6HdrDrAllowSpec_monoX h

theorem specs_xfree : ∀ e ∈ specs, Spec.XFree e.spec := by
  intro e he
  simp only [specs, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  · exact m6HdrInitSpec_xfree
  · exact m6ExtEnsureInitSpec_xfree
  · exact m6HdrAddTicksSpec_xfree
  · exact m6HdrW2aSpec_xfree _ _
  · exact m6HdrW2aSpec_xfree _ _
  · exact m6HdrW2aSpec_xfree _ _
  · exact m6HdrW2aSpec_xfree _ _
  · exact m6HdrW2aSpec_xfree _ _
  · exact m6HdrW2aSpec_xfree _ _
  · exact m6HdrW2aSpec_xfree _ _
  · exact m6HdrW2aSpec_xfree _ _
  · exact m6HdrW2aSpec_xfree _ _
  · exact m6HdrW2aSpec_xfree _ _
  · exact m6HdrGetWatermarkSpec_xfree
  · exact m6HdrW2aSpec_xfree _ _
  · exact m6HdrDrMutSpec_xfree
  · exact m6HdrDrMutSpec_xfree
  · exact m6HdrDrAllowSpec_xfree

theorem specs_sigs : specs.map SpecEntry.sig = Src.Tiers.fns.map Fn.sig := rfl

theorem specs_nodup : (specs.map SpecEntry.name).Nodup := by decide

/-! ## `Env.Sat specs` Projections -/

private theorem mem_has {Γ : Env} (h : Γ.Sat specs) {nm : Sym} {as bs : List Ty}
    {sp : Spec as bs} (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ specs)
    (hx : sp.XFree) : Γ.Has nm sp :=
  Env.Sat.has h hmem hx

theorem has_m6_hdr_init {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "m6_hdr_init" m6HdrInitSpec :=
  mem_has h (by simp [specs]) m6HdrInitSpec_xfree

theorem has_m6_ext_ensure_init {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "m6_ext_ensure_init" m6ExtEnsureInitSpec :=
  mem_has h (by simp [specs]) m6ExtEnsureInitSpec_xfree

theorem has_m6_hdr_add_ticks {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "m6_hdr_add_ticks" m6HdrAddTicksSpec :=
  mem_has h (by simp [specs]) m6HdrAddTicksSpec_xfree

theorem has_m6_hdr_sync_legacy_tiers {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "m6_hdr_sync_legacy_tiers" (m6HdrW2aSpec [] []) :=
  mem_has h (by simp [specs]) (m6HdrW2aSpec_xfree _ _)

theorem has_m6_hdr_recompute_tiers_mode {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "m6_hdr_recompute_tiers_mode" (m6HdrW2aSpec [i64] []) :=
  mem_has h (by simp [specs]) (m6HdrW2aSpec_xfree _ _)

theorem has_m6_hdr_recompute_tiers {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "m6_hdr_recompute_tiers" (m6HdrW2aSpec [] []) :=
  mem_has h (by simp [specs]) (m6HdrW2aSpec_xfree _ _)

theorem has_m6_hdr_update_tier_limits {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "m6_hdr_update_tier_limits" (m6HdrW2aSpec [] []) :=
  mem_has h (by simp [specs]) (m6HdrW2aSpec_xfree _ _)

theorem has_m6_hdr_record_used {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "m6_hdr_record_used" (m6HdrW2aSpec [i64] []) :=
  mem_has h (by simp [specs]) (m6HdrW2aSpec_xfree _ _)

theorem has_m6_hdr_get_tier1 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "m6_hdr_get_tier1" (m6HdrW2aSpec [.bool] [i64]) :=
  mem_has h (by simp [specs]) (m6HdrW2aSpec_xfree _ _)

theorem has_m6_hdr_get_tier2 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "m6_hdr_get_tier2" (m6HdrW2aSpec [.bool] [i64]) :=
  mem_has h (by simp [specs]) (m6HdrW2aSpec_xfree _ _)

theorem has_m6_hdr_delaying {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "m6_hdr_delaying" (m6HdrW2aSpec [i64] [.bool]) :=
  mem_has h (by simp [specs]) (m6HdrW2aSpec_xfree _ _)

theorem has_m6_hdr_bump_delay {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "m6_hdr_bump_delay" (m6HdrW2aSpec [i64] []) :=
  mem_has h (by simp [specs]) (m6HdrW2aSpec_xfree _ _)

theorem has_m6_hdr_reduce_delay {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "m6_hdr_reduce_delay" (m6HdrW2aSpec [i64] []) :=
  mem_has h (by simp [specs]) (m6HdrW2aSpec_xfree _ _)

theorem has_m6_hdr_get_watermark_ro {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "m6_hdr_get_watermark" m6HdrGetWatermarkSpec :=
  mem_has h (by simp [specs]) m6HdrGetWatermarkSpec_xfree

theorem has_m6_hdr_get_watermark {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "m6_hdr_get_watermark" (m6HdrW2aSpec [i64] [i64]) :=
  Env.Has.of_le (has_m6_hdr_get_watermark_ro h) m6HdrW2a_le_getWatermark

theorem has_m6_hdr_set_watermark {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "m6_hdr_set_watermark" (m6HdrW2aSpec [i64, i64] []) :=
  mem_has h (by simp [specs]) (m6HdrW2aSpec_xfree _ _)

theorem has_m6_hdr_dr_init {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "m6_hdr_dr_init" m6HdrDrMutSpec :=
  mem_has h (by simp [specs]) m6HdrDrMutSpec_xfree

theorem has_m6_hdr_dr_update {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "m6_hdr_dr_update" m6HdrDrMutSpec :=
  mem_has h (by simp [specs]) m6HdrDrMutSpec_xfree

theorem has_m6_hdr_dr_allow {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "m6_hdr_dr_allow" m6HdrDrAllowSpec :=
  mem_has h (by simp [specs]) m6HdrDrAllowSpec_xfree

/-! ## Shared `M6HdrExt` Non-Interference Helpers -/

theorem w2a_pres_of_init {ext ext1 ext' : List (BitVec 64)}
    (h1 : M6HdrExtInitOk ext → ext1 = ext) (h2 : M6HdrExtInitOk ext')
    (h3 : M6ExtW2bPres ext1 ext') :
    M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext' :=
  fun hi => ⟨h2, (h1 hi) ▸ h3⟩

theorem w2b_pres_of_init {ext ext1 ext' : List (BitVec 64)}
    (h1 : M6HdrExtInitOk ext → ext1 = ext) (h2 : M6ExtW2aPres ext1 ext') :
    M6HdrExtInitOk ext → M6ExtW2aPres ext ext' :=
  fun hi => (h1 hi) ▸ h2

end

end LeanQbe.T.Examples.Kissat.Proof.Tiers.Spec
