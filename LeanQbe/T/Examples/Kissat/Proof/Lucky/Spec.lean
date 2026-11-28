/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Spec.Core

/-!
# Canonical Pure Specifications for `Kissat.Src.Lucky` (`4` functions)

Pure contract definitions and `specs : List SpecEntry` matching `Src.Lucky.fns` 1:1.
Zero theorems, zero tactics, zero `deps`, zero cross-subsystem `Spec` imports.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Lucky.Spec

open Std.Sat
open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Proof.Spec

/-- `full_lucky_ord_fid(h)`: collects up to `cur_vars` active unassigned variables into
`tarjan_reach`, preserving `s.core` and `extPres`. -/
@[expose] def luckyOrdSpec : Spec [i64] [i64] :=
  FullContract.toSpec (extraArgs := []) (rs := [i64]) (W := Unit) {
    pre := fun _ _ () () => True
    post := fun _ s () () (n, ()) s' =>
      CorePres s s' ∧
      n.toNat ≤ s.core.cur_vars ∧
      ScratchModifies.extPres s s'
  }

/-- `full_lucky_scan(h, pos, fwd)`: single lucky-assignment trial scan from level `0`
(`0`/`2`: inconclusive at level `0`, `10`: candidate model ready for extend, `20`: `F0.Unsat`). -/
@[expose] def luckyScanSpec : Spec [i64, .bool, .bool] [i64] :=
  M6HdrContract.toSpec (extraArgs := [.bool, .bool]) (rs := [i64]) (W := CNF Nat) {
    extFrame := .any
    pre := fun c _ s _ F0 => FullSparseInv c F0 s ∧ s.core.cur_level = 0
    post := fun c _ s _ F0 (r, ()) _ s' =>
      (r = 0#64 ∨ r = 2#64 ∨ r = 10#64 ∨ r = 20#64) ∧
      s'.core.fuel.toNat ≤ s.core.fuel.toNat ∧
      (r = 20#64 → F0.Unsat) ∧
      (r = 0#64 ∨ r = 2#64 → FullSparseInv c F0 s' ∧ s'.core.cur_level = 0) ∧
      (r = 10#64 → s'.scratch.extend_len ≤ c.extend_cap)
  }

/-- `full_lucky_polar_m7(h)`: read-only horn/polarity quick check returning `0`, `1`, or `2`. -/
@[expose] def luckyPolarSpec : Spec [i64] [i64] :=
  FullContract.toSpec (extraArgs := []) (rs := [i64]) (W := CNF Nat) {
    pre := fun c s () F0 => FullCoreInv c F0 s
    post := fun _ s () _ (r, ()) s' =>
      s' = s ∧ (r = 0#64 ∨ r = 1#64 ∨ r = 2#64)
  }

/-- `full_lucky_late_m7(h)`: top-level lucky-assignment pass (any entry level; clears
`probing = 0#64`; `0`/`2`: level-0 `FullSparseInv`, `10`: extend-ready, `20`: `F0.Unsat`). -/
@[expose] def luckySpec : Spec [i64] [i64] :=
  M6HdrContract.toSpec (extraArgs := []) (rs := [i64]) (W := CNF Nat) {
    extFrame := .any
    pre := fun c _ s () F0 => FullSparseInv c F0 s
    post := fun c _ s () F0 (r, ()) _ s' =>
      (r = 0#64 ∨ r = 2#64 ∨ r = 10#64 ∨ r = 20#64) ∧
      s'.core.fuel.toNat ≤ s.core.fuel.toNat ∧
      s'.core.probing = 0#64 ∧
      (r = 20#64 → F0.Unsat) ∧
      (r = 0#64 ∨ r = 2#64 → FullSparseInv c F0 s' ∧ s'.core.cur_level = 0) ∧
      (r = 10#64 → s'.scratch.extend_len ≤ c.extend_cap)
  }

/-- Canonical specification table aligned 1:1 with `Src.Lucky.fns` (`4` entries). -/
@[expose] def specs : List SpecEntry :=
  [ ⟨"full_lucky_ord_fid",  [i64],               [i64], luckyOrdSpec,   true⟩
  , ⟨"full_lucky_scan",     [i64, .bool, .bool], [i64], luckyScanSpec,  true⟩
  , ⟨"full_lucky_polar_m7", [i64],               [i64], luckyPolarSpec, true⟩
  , ⟨"full_lucky_late_m7",  [i64],               [i64], luckySpec,      true⟩
  ]

end LeanQbe.T.Examples.Kissat.Proof.Lucky.Spec
