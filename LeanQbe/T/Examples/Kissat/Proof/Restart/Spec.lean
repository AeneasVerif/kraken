/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Decide.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Heap.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Limits.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Tiers.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts3
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
public import LeanQbe.T.Examples.Kissat.Src.Restart
public import LeanQbe.T.Logic.CanonicalEnv

/-!
# Canonical Specifications for `Kissat.Src.Restart` (`3` Functions)

Defines the external dependency bundle `deps`, the canonical specification `fullSwitchModeM7Spec`
(alongside `Proof.Spec.fullRestartDueSpec` and `Proof.Spec.fullRestartSpec`), `Spec.XFree`
proofs, and the 1:1 `specs : List SpecEntry` table matching `Src.Restart.fns`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Restart.Spec

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Proof.Spec
open Kraken.Bedrock2.Test

public section

/-- Canonical specification for `full_switch_mode_m7`: updates `M6HdrExt` fields and `stable`,
switching search mode (`focused <-> stable`), preserving `s.core`, `LengthsOk`, and
`FullExtScratchPres`. -/
@[expose] def fullSwitchModeM7Spec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
    (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ ext' s' m',
      s'.core = s.core → s'.LengthsOk c → FullExtScratchPres s s' → M6HdrExtOk ext' →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m'

theorem fullRestartDueSpec_xfree : Spec.XFree fullRestartDueSpec := by xfree

theorem fullRestartSpec_xfree : Spec.XFree fullRestartSpec := by xfree

theorem fullSwitchModeM7Spec_xfree : Spec.XFree fullSwitchModeM7Spec := by xfree

/-- External specifications required by `Kissat.Src.Restart`. -/
@[expose] def deps : List SpecEntry :=
  Proof.Backtrack.Spec.specs ++ Proof.Decide.Spec.specs ++ Proof.Float64.Spec.specs ++
  Proof.Heap.Spec.specs ++ Proof.Limits.Spec.specs ++ Proof.Tiers.Spec.specs

/-- Canonical `SpecEntry` list matching `Src.Restart.fns` order 1:1. -/
@[expose] def specs : List SpecEntry :=
  [ ⟨"full_restart_due", [i64], [i64], fullRestartDueSpec, true⟩
  , ⟨"full_restart", [i64], [], fullRestartSpec, true⟩
  , ⟨"full_switch_mode_m7", [i64], [], fullSwitchModeM7Spec, true⟩ ]

theorem specs_xfree : ∀ e ∈ specs, e.spec.XFree := by
  intro e he
  simp only [specs, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · exact fullRestartDueSpec_xfree
  · exact fullRestartSpec_xfree
  · exact fullSwitchModeM7Spec_xfree

theorem specs_sigs : specs.map SpecEntry.sig = Src.Restart.fns.map Fn.sig := rfl

theorem specs_nodup : (specs.map SpecEntry.name).Nodup := by decide

theorem specs_noExit : specs.all SpecEntry.noExit = true := rfl

theorem has_full_restart_due {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_restart_due" fullRestartDueSpec :=
  Env.Sat.has h List.mem_cons_self fullRestartDueSpec_xfree

theorem has_full_restart {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_restart" fullRestartSpec :=
  Env.Sat.has h (.tail _ List.mem_cons_self) fullRestartSpec_xfree

theorem has_full_switch_mode_m7 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_switch_mode_m7" fullSwitchModeM7Spec :=
  Env.Sat.has h (.tail _ (.tail _ List.mem_cons_self)) fullSwitchModeM7Spec_xfree

end

end LeanQbe.T.Examples.Kissat.Proof.Restart.Spec
