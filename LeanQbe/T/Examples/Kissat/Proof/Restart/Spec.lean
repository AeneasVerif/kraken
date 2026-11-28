/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Spec.Core

/-!
# Canonical Pure Specifications for `Kissat.Src.Restart` (`3` functions)

Pure contract definitions and `specs : List SpecEntry` matching `Src.Restart.fns` 1:1.
Zero theorems, zero tactics, zero `deps`, zero cross-subsystem `Spec` imports.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Restart.Spec

open Std.Sat
open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Proof.Spec

/-- `full_restart_due(h)`: checks EMA/Reluctant restart schedule (`0` or `1`). -/
@[expose] def restartDueSpec : Spec [i64] [i64] :=
  FullContract.toSpec (extraArgs := []) (rs := [i64]) (W := Unit) {
    pre := fun _ _ () () => True
    post := fun _ s () () (r, ()) s' =>
      CorePres s s' ∧
      (r = 0#64 ∨ r = 1#64) ∧
      ScratchModifies.extPres s s'
  }

/-- `full_restart(h)`: reuses trail prefix and backtracks to `cur_level' ≤ cur_level`,
preserving `FullCoreInv` and `extPres`. -/
@[expose] def restartSpec : Spec [i64] [] :=
  FullContract.toSpec (extraArgs := []) (rs := []) (W := CNF Nat) {
    pre := fun c s () F0 => FullCoreInv c F0 s
    post := fun c s () F0 () s' =>
      s'.core = { s.core with
        vals := s'.core.vals, lvl := s'.core.lvl, rsns := s'.core.rsns,
        trl := s'.core.trl, trail_pos := s'.core.trail_pos, trail_end := s'.core.trail_end,
        propagated := s'.core.propagated, cur_level := s'.core.cur_level,
        unassigned := s'.core.unassigned } ∧
      FullCoreInv c F0 s' ∧
      s'.core.cur_level ≤ s.core.cur_level ∧
      ScratchModifies.extPres s s'
  }

/-- `full_switch_mode_m7(h)`: toggles focused/stable search mode and updates `M6HdrExt`
mode limits, preserving `s.core` and `extPres`. -/
@[expose] def switchModeSpec : Spec [i64] [] :=
  M6HdrContract.toSpec (extraArgs := []) (rs := []) (W := Unit) {
    extFrame := .any
    pre := fun _ _ _ () () => True
    post := fun _ _ s () () () _ s' =>
      CorePres s s' ∧
      ScratchModifies.extPres s s'
  }

/-- Canonical specification table aligned 1:1 with `Src.Restart.fns` (`3` entries). -/
@[expose] def specs : List SpecEntry :=
  [ ⟨"full_restart_due",    [i64], [i64], restartDueSpec, true⟩
  , ⟨"full_restart",        [i64], [],    restartSpec,    true⟩
  , ⟨"full_switch_mode_m7", [i64], [],    switchModeSpec, true⟩
  ]

end LeanQbe.T.Examples.Kissat.Proof.Restart.Spec
