/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
public import LeanQbe.T.Examples.Kissat.Src.Config
public import LeanQbe.T.Logic.CanonicalEnv

/-!
# Canonical `Spec` Table for `Kissat/Src/Config.lean` (`17` fns)

Single canonical `Spec` per function of `Src.Config.fns` (`17` functions; externs
`m6_hdr_get_watermark` and `m6_hdr_set_watermark` resolved by `Proof.Tiers.Spec`),
`Spec.XFree` proofs, `specs` table matching `Src.Config.fns` 1:1 (`noExit := true`),
`specs_sigs`, `specs_nodup`, `.Le` adapters to `m6HdrW2aSpec`, and `Env.Sat` projections.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Config.Spec

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Src.Config

@[expose] public section

/-- Pure memory-preserving contract returning a fixed `BitVec 64` configuration constant. -/
def cfgMaskSpec (v : BitVec 64) : Spec [] [i64] :=
  fun () m Q _ => Q (v, ()) m

/-- Pure contract for `kissat_config_has_id(cfg_id)`: checks `cfg_id ≤ cfgIdUnsat`. -/
def cfgHasIdSpec : Spec [i64] [.bool] :=
  fun (cfg_id, ()) m Q _ => Q (decide (cfg_id ≤ cfgIdUnsat), ()) m

/-- `FullM6HdrMem` configuration contract extending `m6HdrW2aSpec` with a pure postcondition
`postR` on the extra arguments and return tuple. -/
def configW2aSpec (extraArgs rs : List Ty)
    (postR : Tup Val extraArgs → Tup Val rs → Prop) : Spec (i64 :: extraArgs) rs :=
  fun args m Q _ =>
    ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
      args.1 = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
      (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ (r : Tup Val rs) (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
        s'.core = s.core → s'.LengthsOk c → M6HdrScratchPres s s' →
        M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
        postR args.2 r →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q r m'

/-- Canonical contract for `kissat_config_get`: guarantees `cfgFlagInit` is set in the result. -/
abbrev cfgGetSpec : Spec [i64] [i64] :=
  configW2aSpec [] [i64] (fun _ (r, ()) => (r &&& cfgFlagInit) ≠ 0#64)

/-- Canonical contract for `kissat_config_flag`. -/
abbrev cfgFlagSpec : Spec [i64, i64] [.bool] :=
  m6HdrW2aSpec [i64] [.bool]

/-- Canonical contract for `kissat_config_stable`: guarantees `r ∈ {0, 1, 2}`. -/
abbrev cfgStableSpec : Spec [i64] [i64] :=
  configW2aSpec [] [i64]
    (fun _ (r, ()) => r = cfgStableUnsatVal ∨ r = cfgStableDefaultVal ∨ r = cfgStablePlainVal)

/-- Canonical contract for `kissat_config_target`: guarantees `r ∈ {1, 2}`. -/
abbrev cfgTargetSpec : Spec [i64] [i64] :=
  configW2aSpec [] [i64] (fun _ (r, ()) => r = cfgTargetDefault ∨ r = cfgTargetSatVal)

/-- Canonical contract for `kissat_config_restartint`: guarantees `r ∈ {1, 50}`. -/
abbrev cfgRestartintSpec : Spec [i64] [i64] :=
  configW2aSpec [] [i64] (fun _ (r, ()) => r = cfgRestartintDefault ∨ r = cfgRestartintSatVal)

/-- Canonical contract for `kissat_config_{default,plain,basic,sat,unsat}`. -/
abbrev cfgPresetSetSpec : Spec [i64] [] :=
  m6HdrW2aSpec [] []

/-- Canonical contract for `kissat_set_configuration`: returns `decide (cfg_id ≤ cfgIdUnsat)`. -/
abbrev cfgSetConfigSpec : Spec [i64, i64] [.bool] :=
  configW2aSpec [i64] [.bool] (fun (cfg_id, ()) (ok, ()) => ok = decide (cfg_id ≤ cfgIdUnsat))

/-- Canonical `17`-row specification table aligned 1:1 with `Src.Config.fns`. -/
def specs : List SpecEntry :=
  [ ⟨"kissat_config_mask_default", [],         [i64],   cfgMaskSpec cfgDefault, true⟩
  , ⟨"kissat_config_mask_plain",   [],         [i64],   cfgMaskSpec cfgPlain,   true⟩
  , ⟨"kissat_config_mask_basic",   [],         [i64],   cfgMaskSpec cfgBasic,   true⟩
  , ⟨"kissat_config_mask_sat",     [],         [i64],   cfgMaskSpec cfgSat,     true⟩
  , ⟨"kissat_config_mask_unsat",   [],         [i64],   cfgMaskSpec cfgUnsat,   true⟩
  , ⟨"kissat_config_get",          [i64],      [i64],   cfgGetSpec,           true⟩
  , ⟨"kissat_config_flag",         [i64, i64], [.bool], cfgFlagSpec,          true⟩
  , ⟨"kissat_config_stable",       [i64],      [i64],   cfgStableSpec,        true⟩
  , ⟨"kissat_config_target",       [i64],      [i64],   cfgTargetSpec,        true⟩
  , ⟨"kissat_config_restartint",   [i64],      [i64],   cfgRestartintSpec,    true⟩
  , ⟨"kissat_config_default",      [i64],      [],      cfgPresetSetSpec,     true⟩
  , ⟨"kissat_config_plain",        [i64],      [],      cfgPresetSetSpec,     true⟩
  , ⟨"kissat_config_basic",        [i64],      [],      cfgPresetSetSpec,     true⟩
  , ⟨"kissat_config_sat",          [i64],      [],      cfgPresetSetSpec,     true⟩
  , ⟨"kissat_config_unsat",        [i64],      [],      cfgPresetSetSpec,     true⟩
  , ⟨"kissat_config_has_id",       [i64],      [.bool], cfgHasIdSpec,         true⟩
  , ⟨"kissat_set_configuration",   [i64, i64], [.bool], cfgSetConfigSpec,     true⟩
  ]

end

public section

/-! ## `configW2aSpec` Constructors, Eliminators & `.Le` Adapters -/

theorem configW2aSpec_of {extraArgs rs : List Ty} {postR : Tup Val extraArgs → Tup Val rs → Prop}
    {args : Tup Val (i64 :: extraArgs)} {c : FullCfg} {ext : List (BitVec 64)}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post rs} {X : XPost}
    (hh : args.1 = c.hdr) (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext)
    (hlen : s.LengthsOk c) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ (r : Tup Val rs) (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
      s'.core = s.core → s'.LengthsOk c → M6HdrScratchPres s s' →
      M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
      postR args.2 r → (FullM6HdrMem c ext' s' ⋆ R) m' → Q r m') :
    configW2aSpec extraArgs rs postR args m Q X :=
  ⟨c, ext, s, R, hh, hcfg, hext, hlen, hm, hQ⟩

theorem configW2aSpec_elim {extraArgs rs : List Ty} {postR : Tup Val extraArgs → Tup Val rs → Prop}
    {args : Tup Val (i64 :: extraArgs)} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : configW2aSpec extraArgs rs postR args m Q X) :
    ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
      args.1 = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
      (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ (r : Tup Val rs) (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
        s'.core = s.core → s'.LengthsOk c → M6HdrScratchPres s s' →
        M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
        postR args.2 r → (FullM6HdrMem c ext' s' ⋆ R) m' → Q r m' := h

theorem m6HdrW2a_le_configW2a {extraArgs rs : List Ty}
    {postR : Tup Val extraArgs → Tup Val rs → Prop} :
    (m6HdrW2aSpec extraArgs rs).Le (configW2aSpec extraArgs rs postR) := by
  intro args m Q X hW
  obtain ⟨c, ext, s, R, hh, hcfg, hext, hlen, hm, hQ⟩ := m6HdrW2aSpec_elim hW
  exact ⟨c, ext, s, R, hh, hcfg, hext, hlen, hm,
    fun r ext' s' m' hc hl hs he hw _ hm' => hQ r ext' s' m' hc hl hs he hw hm'⟩

/-! ## `Spec.XFree` Proofs & Table Invariants -/

theorem cfgMaskSpec_xfree (v : BitVec 64) : Spec.XFree (cfgMaskSpec v) := by xfree

theorem cfgHasIdSpec_xfree : Spec.XFree cfgHasIdSpec := by xfree

theorem configW2aSpec_xfree (extraArgs rs : List Ty)
    (postR : Tup Val extraArgs → Tup Val rs → Prop) :
    Spec.XFree (configW2aSpec extraArgs rs postR) := by xfree

theorem m6HdrW2aSpec_xfree (extraArgs rs : List Ty) :
    Spec.XFree (m6HdrW2aSpec extraArgs rs) :=
  fun _ _ _ _ _ h => m6HdrW2aSpec_monoX h

theorem cfgGetSpec_xfree : Spec.XFree cfgGetSpec := by xfree

theorem cfgStableSpec_xfree : Spec.XFree cfgStableSpec := by xfree

theorem cfgTargetSpec_xfree : Spec.XFree cfgTargetSpec := by xfree

theorem cfgRestartintSpec_xfree : Spec.XFree cfgRestartintSpec := by xfree

theorem cfgSetConfigSpec_xfree : Spec.XFree cfgSetConfigSpec := by xfree

theorem specs_xfree : ∀ e ∈ specs, Spec.XFree e.spec := by
  intro e he
  simp only [specs, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · exact cfgMaskSpec_xfree _
  · exact cfgMaskSpec_xfree _
  · exact cfgMaskSpec_xfree _
  · exact cfgMaskSpec_xfree _
  · exact cfgMaskSpec_xfree _
  · exact cfgGetSpec_xfree
  · exact m6HdrW2aSpec_xfree _ _
  · exact cfgStableSpec_xfree
  · exact cfgTargetSpec_xfree
  · exact cfgRestartintSpec_xfree
  · exact m6HdrW2aSpec_xfree _ _
  · exact m6HdrW2aSpec_xfree _ _
  · exact m6HdrW2aSpec_xfree _ _
  · exact m6HdrW2aSpec_xfree _ _
  · exact m6HdrW2aSpec_xfree _ _
  · exact cfgHasIdSpec_xfree
  · exact cfgSetConfigSpec_xfree

theorem specs_sigs : specs.map SpecEntry.sig = Src.Config.fns.map Fn.sig := rfl

theorem specs_nodup : (specs.map SpecEntry.name).Nodup := by decide

/-! ## `Env.Sat specs` Projections -/

private theorem mem_has {Γ : Env} (h : Γ.Sat specs) {nm : Sym} {as bs : List Ty}
    {sp : Spec as bs} (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ specs)
    (hx : sp.XFree) : Γ.Has nm sp :=
  Env.Sat.has h hmem hx

theorem has_kissat_config_mask_default {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "kissat_config_mask_default" (cfgMaskSpec cfgDefault) :=
  mem_has h (by simp [specs]) (cfgMaskSpec_xfree _)

theorem has_kissat_config_mask_plain {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "kissat_config_mask_plain" (cfgMaskSpec cfgPlain) :=
  mem_has h (by simp [specs]) (cfgMaskSpec_xfree _)

theorem has_kissat_config_mask_basic {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "kissat_config_mask_basic" (cfgMaskSpec cfgBasic) :=
  mem_has h (by simp [specs]) (cfgMaskSpec_xfree _)

theorem has_kissat_config_mask_sat {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "kissat_config_mask_sat" (cfgMaskSpec cfgSat) :=
  mem_has h (by simp [specs]) (cfgMaskSpec_xfree _)

theorem has_kissat_config_mask_unsat {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "kissat_config_mask_unsat" (cfgMaskSpec cfgUnsat) :=
  mem_has h (by simp [specs]) (cfgMaskSpec_xfree _)

theorem has_kissat_config_get {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "kissat_config_get" cfgGetSpec :=
  mem_has h (by simp [specs]) cfgGetSpec_xfree

theorem has_kissat_config_flag {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "kissat_config_flag" cfgFlagSpec :=
  mem_has h (by simp [specs]) (m6HdrW2aSpec_xfree _ _)

theorem has_kissat_config_stable {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "kissat_config_stable" cfgStableSpec :=
  mem_has h (by simp [specs]) cfgStableSpec_xfree

theorem has_kissat_config_target {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "kissat_config_target" cfgTargetSpec :=
  mem_has h (by simp [specs]) cfgTargetSpec_xfree

theorem has_kissat_config_restartint {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "kissat_config_restartint" cfgRestartintSpec :=
  mem_has h (by simp [specs]) cfgRestartintSpec_xfree

theorem has_kissat_config_default {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "kissat_config_default" cfgPresetSetSpec :=
  mem_has h (by simp [specs]) (m6HdrW2aSpec_xfree _ _)

theorem has_kissat_config_plain {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "kissat_config_plain" cfgPresetSetSpec :=
  mem_has h (by simp [specs]) (m6HdrW2aSpec_xfree _ _)

theorem has_kissat_config_basic {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "kissat_config_basic" cfgPresetSetSpec :=
  mem_has h (by simp [specs]) (m6HdrW2aSpec_xfree _ _)

theorem has_kissat_config_sat {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "kissat_config_sat" cfgPresetSetSpec :=
  mem_has h (by simp [specs]) (m6HdrW2aSpec_xfree _ _)

theorem has_kissat_config_unsat {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "kissat_config_unsat" cfgPresetSetSpec :=
  mem_has h (by simp [specs]) (m6HdrW2aSpec_xfree _ _)

theorem has_kissat_config_has_id {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "kissat_config_has_id" cfgHasIdSpec :=
  mem_has h (by simp [specs]) cfgHasIdSpec_xfree

theorem has_kissat_set_configuration {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "kissat_set_configuration" cfgSetConfigSpec :=
  mem_has h (by simp [specs]) cfgSetConfigSpec_xfree

theorem has_kissat_config_get_to_w2a {Γ : Env} (h : Γ.Has "kissat_config_get" cfgGetSpec) :
    Γ.Has "kissat_config_get" (m6HdrW2aSpec [] [i64]) :=
  h.of_le m6HdrW2a_le_configW2a

theorem has_kissat_config_stable_to_w2a {Γ : Env}
    (h : Γ.Has "kissat_config_stable" cfgStableSpec) :
    Γ.Has "kissat_config_stable" (m6HdrW2aSpec [] [i64]) :=
  h.of_le m6HdrW2a_le_configW2a

theorem has_kissat_config_target_to_w2a {Γ : Env}
    (h : Γ.Has "kissat_config_target" cfgTargetSpec) :
    Γ.Has "kissat_config_target" (m6HdrW2aSpec [] [i64]) :=
  h.of_le m6HdrW2a_le_configW2a

theorem has_kissat_config_restartint_to_w2a {Γ : Env}
    (h : Γ.Has "kissat_config_restartint" cfgRestartintSpec) :
    Γ.Has "kissat_config_restartint" (m6HdrW2aSpec [] [i64]) :=
  h.of_le m6HdrW2a_le_configW2a

theorem has_kissat_set_configuration_to_w2a {Γ : Env}
    (h : Γ.Has "kissat_set_configuration" cfgSetConfigSpec) :
    Γ.Has "kissat_set_configuration" (m6HdrW2aSpec [i64] [.bool]) :=
  h.of_le m6HdrW2a_le_configW2a

end

end LeanQbe.T.Examples.Kissat.Proof.Config.Spec
