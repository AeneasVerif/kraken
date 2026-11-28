/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Spec.Core
public import LeanQbe.T.Examples.Kissat.Src.Config

/-!
# Canonical Pure Specifications for `Kissat.Src.Config` (`17` functions)

Pure contract definitions and `specs : List SpecEntry` matching `Src.Config.fns` 1:1.
Zero theorems, zero tactics, zero `deps`, zero cross-subsystem `Spec` imports.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Config.Spec

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src.Config
open LeanQbe.T.Examples.Kissat.Proof.Spec

/-- Helper for `FullM6HdrMem` configuration contracts that preserve `core`, `probePres` scratch,
and the `w2aOnly` extension frame while establishing a pure postcondition `postR`. -/
@[expose] def hdrContract (extraArgs rs : List Ty)
    (postR : Tup Val extraArgs → Tup Val rs → Prop) :
    M6HdrContract extraArgs rs PUnit where
  extFrame := .w2aOnly
  pre  := fun _ _ _ _ _ => True
  post := fun _ _ s args _ r _ s' =>
    CorePres s s' ∧ ScratchModifies.probePres s s' ∧ postR args r

/-- Pure contract returning a fixed `BitVec 64` preset bitmask (`kissat_config_mask_*`). -/
@[expose] def maskSpec (v : BitVec 64) : Spec [] [i64] :=
  PureContract.det (fun () => (v, ()))

/-- `kissat_config_get`: guarantees `cfgFlagInit` is set in the returned bitmask. -/
@[expose] def getSpec : Spec [i64] [i64] :=
  (hdrContract [] [i64] (fun _ (r, ()) => (r &&& cfgFlagInit) ≠ 0#64)).toSpec

/-- `kissat_config_flag`: queries a single configuration flag bit. -/
@[expose] def flagSpec : Spec [i64, i64] [.bool] :=
  (hdrContract [i64] [.bool] (fun _ _ => True)).toSpec

/-- `kissat_config_stable`: returns a valid stable-mode code (`0`, `1`, or `2`). -/
@[expose] def stableSpec : Spec [i64] [i64] :=
  (hdrContract [] [i64] (fun _ (r, ()) =>
    r = cfgStableUnsatVal ∨ r = cfgStableDefaultVal ∨ r = cfgStablePlainVal)).toSpec

/-- `kissat_config_target`: returns a valid target-phase code (`1` or `2`). -/
@[expose] def targetSpec : Spec [i64] [i64] :=
  (hdrContract [] [i64] (fun _ (r, ()) => r = cfgTargetDefault ∨ r = cfgTargetSatVal)).toSpec

/-- `kissat_config_restartint`: returns a valid restart interval (`1` or `50`). -/
@[expose] def restartintSpec : Spec [i64] [i64] :=
  (hdrContract [] [i64] (fun _ (r, ()) =>
    r = cfgRestartintDefault ∨ r = cfgRestartintSatVal)).toSpec

/-- Deduplicated contract for preset setters `kissat_config_{default,plain,basic,sat,unsat}`. -/
@[expose] def presetSetSpec : Spec [i64] [] :=
  (hdrContract [] [] (fun _ _ => True)).toSpec

/-- Pure contract for `kissat_config_has_id`: checks `cfgId ≤ cfgIdUnsat`. -/
@[expose] def hasIdSpec : Spec [i64] [.bool] :=
  PureContract.det (fun (cfgId, ()) => (decide (cfgId ≤ cfgIdUnsat), ()))

/-- `kissat_set_configuration`: installs preset `cfgId` and returns
`decide (cfgId ≤ cfgIdUnsat)`. -/
@[expose] def setConfigurationSpec : Spec [i64, i64] [.bool] :=
  (hdrContract [i64] [.bool] (fun (cfgId, ()) (ok, ()) =>
    ok = decide (cfgId ≤ cfgIdUnsat))).toSpec

/-- Canonical `17`-row specification table aligned 1:1 with `Src.Config.fns`. -/
@[expose] def specs : List SpecEntry :=
  [ ⟨"kissat_config_mask_default", [],         [i64],   maskSpec cfgDefault,   true⟩
  , ⟨"kissat_config_mask_plain",   [],         [i64],   maskSpec cfgPlain,     true⟩
  , ⟨"kissat_config_mask_basic",   [],         [i64],   maskSpec cfgBasic,     true⟩
  , ⟨"kissat_config_mask_sat",     [],         [i64],   maskSpec cfgSat,       true⟩
  , ⟨"kissat_config_mask_unsat",   [],         [i64],   maskSpec cfgUnsat,     true⟩
  , ⟨"kissat_config_get",          [i64],      [i64],   getSpec,              true⟩
  , ⟨"kissat_config_flag",         [i64, i64], [.bool], flagSpec,             true⟩
  , ⟨"kissat_config_stable",       [i64],      [i64],   stableSpec,           true⟩
  , ⟨"kissat_config_target",       [i64],      [i64],   targetSpec,           true⟩
  , ⟨"kissat_config_restartint",   [i64],      [i64],   restartintSpec,       true⟩
  , ⟨"kissat_config_default",      [i64],      [],      presetSetSpec,        true⟩
  , ⟨"kissat_config_plain",        [i64],      [],      presetSetSpec,        true⟩
  , ⟨"kissat_config_basic",        [i64],      [],      presetSetSpec,        true⟩
  , ⟨"kissat_config_sat",          [i64],      [],      presetSetSpec,        true⟩
  , ⟨"kissat_config_unsat",        [i64],      [],      presetSetSpec,        true⟩
  , ⟨"kissat_config_has_id",       [i64],      [.bool], hasIdSpec,            true⟩
  , ⟨"kissat_set_configuration",   [i64, i64], [.bool], setConfigurationSpec, true⟩
  ]

end LeanQbe.T.Examples.Kissat.Proof.Config.Spec
