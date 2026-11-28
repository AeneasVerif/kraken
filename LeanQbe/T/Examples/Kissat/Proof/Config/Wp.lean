/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Config.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Lib.ContractLemmas
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
public import LeanQbe.T.Examples.Kissat.Src.Config
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
meta import LeanQbe.T.Logic.C0Step
meta import LeanQbe.T.Logic.C0HeadStep

/-!
# Canonical WP Proofs for `Kissat/Src/Config.lean` (`17` fns)

Self-contained `CanonicalEnv` `Func.wp` proofs for all `17` functions of `Src.Config.fns`,
depending only on `Proof.Spec.Header` and `Proof.Tiers.Spec` watermark contracts (`0` legacy
`Full*` imports).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Config

open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Src
open LeanQbe.T.Examples.Kissat.Src.Config
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Config.Spec
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.M6HdrTactics

local macro "cfg_mask_wp" body:ident : tactic =>
  `(tactic| (
    rintro ⟨⟩ m Q X hs
    obtain ⟨_, hQ⟩ := PureContract.elim (X := X) hs
    unfold Func.wp $body
    c0_hsteps
    refine hQ _ ?_
    decide))

local macro "cfg_preset_set_wp" body:ident hSetWm:ident : tactic =>
  `(tactic| (
    rintro ⟨h, ⟨⟩⟩ m Q X hs
    unfold presetSetSpec hdrContract at hs
    obtain ⟨c, ext, s, ⟨⟩, R, rfl, hcfg, hext, hlen, _, hm, hQ⟩ := M6HdrContract.elim hs
    unfold Func.wp $body
    c0_hsteps_nogrp
    m6h_call $hSetWm
    refine m6HdrW2aSpec_of rfl hcfg hext hlen hm
      fun () ext1 s1 m1 hcore1 hlen1 hsc1 hext1 hw1 hm1 => ?_
    c0_hsteps
    exact hQ () ext1 s1 m1 hext1 hw1 hlen1
      ⟨hcore1, hsc1.probePres, trivial⟩ hm1))

local macro "cfg_set_branch" hFn:ident cfg_id:ident hcfg:ident hext:ident hlen:ident hm:ident
    hQ:ident cid:term : tactic =>
  `(tactic| (
    m6h_call $hFn
    dsimp only [presetSetSpec]
    refine M6HdrContract.intro (w := PUnit.unit) $hcfg $hext $hlen trivial $hm
      fun () ext1 s1 m1 hext1 hw1 hlen1 hpost1 hm1 => ?_
    rcases hpost1 with ⟨hcore1, hsc1, _⟩
    c0_hsteps
    refine $hQ (true, ()) ext1 s1 m1 hext1 hw1 hlen1 ⟨hcore1, hsc1, ?_⟩ hm1
    have hid : $cfg_id = $cid := by assumption
    subst hid; dsimp only; decide))

/-! ## 1. Pure Preset Mask Accessors (`5` Functions) -/

theorem kissat_config_mask_default_wp (Γ : Env) :
    ∀ a m Q X, maskSpec cfgDefault a m Q X →
      Func.wp Γ kissat_config_mask_default_body a m Q X := by
  cfg_mask_wp kissat_config_mask_default_body

theorem kissat_config_mask_plain_wp (Γ : Env) :
    ∀ a m Q X, maskSpec cfgPlain a m Q X →
      Func.wp Γ kissat_config_mask_plain_body a m Q X := by
  cfg_mask_wp kissat_config_mask_plain_body

theorem kissat_config_mask_basic_wp (Γ : Env) :
    ∀ a m Q X, maskSpec cfgBasic a m Q X →
      Func.wp Γ kissat_config_mask_basic_body a m Q X := by
  cfg_mask_wp kissat_config_mask_basic_body

theorem kissat_config_mask_sat_wp (Γ : Env) :
    ∀ a m Q X, maskSpec cfgSat a m Q X →
      Func.wp Γ kissat_config_mask_sat_body a m Q X := by
  cfg_mask_wp kissat_config_mask_sat_body

theorem kissat_config_mask_unsat_wp (Γ : Env) :
    ∀ a m Q X, maskSpec cfgUnsat a m Q X →
      Func.wp Γ kissat_config_mask_unsat_body a m Q X := by
  cfg_mask_wp kissat_config_mask_unsat_body

/-! ## 2. Configuration Word Readers (`5` Functions) -/

theorem kissat_config_get_wp (Γ : Env)
    (hGetWm : Γ.Has "m6_hdr_get_watermark" (m6HdrW2aSpec [i64] [i64])) :
    ∀ a m Q X, getSpec a m Q X →
      Func.wp Γ kissat_config_get_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  unfold getSpec hdrContract at hs
  obtain ⟨c, ext, s, ⟨⟩, R, rfl, hcfg, hext, hlen, _, hm, hQ⟩ := M6HdrContract.elim hs
  unfold Func.wp kissat_config_get_body
  c0_hsteps_nogrp
  m6h_call hGetWm
  refine m6HdrW2aSpec_of rfl hcfg hext hlen hm
    fun (w, ()) ext1 s1 m1 hcore1 hlen1 hsc1 hext1 hw1 hm1 => ?_
  c0_hsteps
  · refine hQ (cfgDefault, ()) ext1 s1 m1 hext1 hw1 hlen1
      ⟨hcore1, hsc1.probePres, ?_⟩ hm1
    decide
  · refine hQ (w, ()) ext1 s1 m1 hext1 hw1 hlen1
      ⟨hcore1, hsc1.probePres, ?_⟩ hm1
    rwa [show cfgFlagInit = 1#64 <<< (63 : Nat) from by decide]

theorem kissat_config_flag_wp (Γ : Env)
    (hGet : Γ.Has "kissat_config_get" getSpec) :
    ∀ a m Q X, flagSpec a m Q X →
      Func.wp Γ kissat_config_flag_body a m Q X := by
  rintro ⟨h, mask, ⟨⟩⟩ m Q X hs
  unfold flagSpec hdrContract at hs
  obtain ⟨c, ext, s, ⟨⟩, R, rfl, hcfg, hext, hlen, _, hm, hQ⟩ := M6HdrContract.elim hs
  unfold Func.wp kissat_config_flag_body
  c0_hsteps_nogrp
  m6h_call hGet
  dsimp only [getSpec]
  refine M6HdrContract.intro (w := PUnit.unit) hcfg hext hlen trivial hm
    fun (w, ()) ext1 s1 m1 hext1 hw1 hlen1 ⟨hcore1, hsc1, _⟩ hm1 => ?_
  c0_hsteps
  all_goals exact hQ _ ext1 s1 m1 hext1 hw1 hlen1 ⟨hcore1, hsc1, trivial⟩ hm1

theorem kissat_config_stable_wp (Γ : Env)
    (hGet : Γ.Has "kissat_config_get" getSpec) :
    ∀ a m Q X, stableSpec a m Q X →
      Func.wp Γ kissat_config_stable_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  unfold stableSpec hdrContract at hs
  obtain ⟨c, ext, s, ⟨⟩, R, rfl, hcfg, hext, hlen, _, hm, hQ⟩ := M6HdrContract.elim hs
  unfold Func.wp kissat_config_stable_body
  c0_hsteps_nogrp
  m6h_call hGet
  dsimp only [getSpec]
  refine M6HdrContract.intro (w := PUnit.unit) hcfg hext hlen trivial hm
    fun (w, ()) ext1 s1 m1 hext1 hw1 hlen1 ⟨hcore1, hsc1, _⟩ hm1 => ?_
  c0_hsteps
  · exact hQ (cfgStablePlainVal, ()) ext1 s1 m1 hext1 hw1 hlen1
      ⟨hcore1, hsc1, Or.inr (Or.inr rfl)⟩ hm1
  · exact hQ (cfgStableUnsatVal, ()) ext1 s1 m1 hext1 hw1 hlen1
      ⟨hcore1, hsc1, Or.inl rfl⟩ hm1
  · exact hQ (cfgStableDefaultVal, ()) ext1 s1 m1 hext1 hw1 hlen1
      ⟨hcore1, hsc1, Or.inr (Or.inl rfl)⟩ hm1

theorem kissat_config_target_wp (Γ : Env)
    (hGet : Γ.Has "kissat_config_get" getSpec) :
    ∀ a m Q X, targetSpec a m Q X →
      Func.wp Γ kissat_config_target_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  unfold targetSpec hdrContract at hs
  obtain ⟨c, ext, s, ⟨⟩, R, rfl, hcfg, hext, hlen, _, hm, hQ⟩ := M6HdrContract.elim hs
  unfold Func.wp kissat_config_target_body
  c0_hsteps_nogrp
  m6h_call hGet
  dsimp only [getSpec]
  refine M6HdrContract.intro (w := PUnit.unit) hcfg hext hlen trivial hm
    fun (w, ()) ext1 s1 m1 hext1 hw1 hlen1 ⟨hcore1, hsc1, _⟩ hm1 => ?_
  c0_hsteps
  · exact hQ (cfgTargetSatVal, ()) ext1 s1 m1 hext1 hw1 hlen1 ⟨hcore1, hsc1, Or.inr rfl⟩ hm1
  · exact hQ (cfgTargetDefault, ()) ext1 s1 m1 hext1 hw1 hlen1 ⟨hcore1, hsc1, Or.inl rfl⟩ hm1

theorem kissat_config_restartint_wp (Γ : Env)
    (hGet : Γ.Has "kissat_config_get" getSpec) :
    ∀ a m Q X, restartintSpec a m Q X →
      Func.wp Γ kissat_config_restartint_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  unfold restartintSpec hdrContract at hs
  obtain ⟨c, ext, s, ⟨⟩, R, rfl, hcfg, hext, hlen, _, hm, hQ⟩ := M6HdrContract.elim hs
  unfold Func.wp kissat_config_restartint_body
  c0_hsteps_nogrp
  m6h_call hGet
  dsimp only [getSpec]
  refine M6HdrContract.intro (w := PUnit.unit) hcfg hext hlen trivial hm
    fun (w, ()) ext1 s1 m1 hext1 hw1 hlen1 ⟨hcore1, hsc1, _⟩ hm1 => ?_
  c0_hsteps
  · exact hQ (cfgRestartintSatVal, ()) ext1 s1 m1 hext1 hw1 hlen1
      ⟨hcore1, hsc1, Or.inr rfl⟩ hm1
  · exact hQ (cfgRestartintDefault, ()) ext1 s1 m1 hext1 hw1 hlen1
      ⟨hcore1, hsc1, Or.inl rfl⟩ hm1

/-! ## 3. Preset Writers (`5` Functions) -/

theorem kissat_config_default_wp (Γ : Env)
    (hSetWm : Γ.Has "m6_hdr_set_watermark" (m6HdrW2aSpec [i64, i64] [])) :
    ∀ a m Q X, presetSetSpec a m Q X →
      Func.wp Γ kissat_config_default_body a m Q X := by
  cfg_preset_set_wp kissat_config_default_body hSetWm

theorem kissat_config_plain_wp (Γ : Env)
    (hSetWm : Γ.Has "m6_hdr_set_watermark" (m6HdrW2aSpec [i64, i64] [])) :
    ∀ a m Q X, presetSetSpec a m Q X →
      Func.wp Γ kissat_config_plain_body a m Q X := by
  cfg_preset_set_wp kissat_config_plain_body hSetWm

theorem kissat_config_basic_wp (Γ : Env)
    (hSetWm : Γ.Has "m6_hdr_set_watermark" (m6HdrW2aSpec [i64, i64] [])) :
    ∀ a m Q X, presetSetSpec a m Q X →
      Func.wp Γ kissat_config_basic_body a m Q X := by
  cfg_preset_set_wp kissat_config_basic_body hSetWm

theorem kissat_config_sat_wp (Γ : Env)
    (hSetWm : Γ.Has "m6_hdr_set_watermark" (m6HdrW2aSpec [i64, i64] [])) :
    ∀ a m Q X, presetSetSpec a m Q X →
      Func.wp Γ kissat_config_sat_body a m Q X := by
  cfg_preset_set_wp kissat_config_sat_body hSetWm

theorem kissat_config_unsat_wp (Γ : Env)
    (hSetWm : Γ.Has "m6_hdr_set_watermark" (m6HdrW2aSpec [i64, i64] [])) :
    ∀ a m Q X, presetSetSpec a m Q X →
      Func.wp Γ kissat_config_unsat_body a m Q X := by
  cfg_preset_set_wp kissat_config_unsat_body hSetWm

/-! ## 4. Runtime Preset Dispatch (`2` Functions) -/

theorem kissat_config_has_id_wp (Γ : Env) :
    ∀ a m Q X, hasIdSpec a m Q X →
      Func.wp Γ kissat_config_has_id_body a m Q X := by
  rintro ⟨cfg_id, ⟨⟩⟩ m Q X hs
  obtain ⟨_, hQ⟩ := PureContract.elim (X := X) hs
  unfold Func.wp kissat_config_has_id_body
  c0_hsteps
  exact hQ _ rfl

theorem kissat_set_configuration_wp (Γ : Env)
    (hDef : Γ.Has "kissat_config_default" presetSetSpec)
    (hPlain : Γ.Has "kissat_config_plain" presetSetSpec)
    (hBasic : Γ.Has "kissat_config_basic" presetSetSpec)
    (hSat : Γ.Has "kissat_config_sat" presetSetSpec)
    (hUnsat : Γ.Has "kissat_config_unsat" presetSetSpec) :
    ∀ a m Q X, setConfigurationSpec a m Q X →
      Func.wp Γ kissat_set_configuration_body a m Q X := by
  rintro ⟨h, cfg_id, ⟨⟩⟩ m Q X hs
  unfold setConfigurationSpec hdrContract at hs
  obtain ⟨c, ext, s, ⟨⟩, R, rfl, hcfg, hext, hlen, _, hm, hQ⟩ := M6HdrContract.elim hs
  unfold Func.wp kissat_set_configuration_body
  c0_hsteps_nogrp
  · cfg_set_branch hDef cfg_id hcfg hext hlen hm hQ 0#64
  · cfg_set_branch hPlain cfg_id hcfg hext hlen hm hQ 1#64
  · cfg_set_branch hBasic cfg_id hcfg hext hlen hm hQ 2#64
  · cfg_set_branch hSat cfg_id hcfg hext hlen hm hQ 3#64
  · cfg_set_branch hUnsat cfg_id hcfg hext hlen hm hQ 4#64
  · refine hQ (false, ()) ext s m hext (fun hi => ⟨hi, M6ExtW2bPres.refl ext⟩) hlen
      ⟨CorePres.refl s, ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩ hm
    have hgt : 4 < cfg_id.toNat := by
      have h0 : cfg_id ≠ 0#64 := by assumption
      have h1 : cfg_id ≠ 1#64 := by assumption
      have h2 : cfg_id ≠ 2#64 := by assumption
      have h3 : cfg_id ≠ 3#64 := by assumption
      have h4 : cfg_id ≠ 4#64 := by assumption
      have hn0 : cfg_id.toNat ≠ 0 := fun h => h0 (BitVec.eq_of_toNat_eq h)
      have hn1 : cfg_id.toNat ≠ 1 := fun h => h1 (BitVec.eq_of_toNat_eq h)
      have hn2 : cfg_id.toNat ≠ 2 := fun h => h2 (BitVec.eq_of_toNat_eq h)
      have hn3 : cfg_id.toNat ≠ 3 := fun h => h3 (BitVec.eq_of_toNat_eq h)
      have hn4 : cfg_id.toNat ≠ 4 := fun h => h4 (BitVec.eq_of_toNat_eq h)
      omega
    have hnle : ¬ cfg_id ≤ cfgIdUnsat := by
      change ¬ cfg_id.toNat ≤ (4#64 : BitVec 64).toNat
      have : (4#64 : BitVec 64).toNat = 4 := rfl
      omega
    simpa using hnle

end LeanQbe.T.Examples.Kissat.Proof.Config
