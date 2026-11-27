/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Heap.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
public import LeanQbe.T.Examples.Kissat.Src.Backtrack
public import LeanQbe.T.Logic.CanonicalEnv

/-!
# Canonical Specification Table for `Kissat.Src.Backtrack` (`Proof.Backtrack.Spec`)

Reuses `Proof.Spec.fullAssignLvlSpec`, `fullAssignSpec`, `fullSaveTargetBestSpec`, and
`fullBacktrackSpec` directly, defines `fullBacktrackRawSpec` (helper for `full_backtrack_raw_m5`),
and ties `deps` to `Heap.Spec.specs` (`0` legacy imports, `0` `@[expose]` on theorems/lemmas).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec

open Std.Sat
open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Src
open Kraken.Bedrock2.Test

/-- Internal backtrack helper contract: identical to `fullBacktrackSpec` plus pointwise
preservation of `lvl[v]` for all variables with `lvl[v] ≤ target_lvl` (needed for composing
1-level unwind + target/best phase save + remaining unwind in `full_backtrack_ac_fid`). -/
@[expose] def fullBacktrackRawSpec : Spec [i64, i64] [] := fun (h, target_lvl, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ s.core.cur_level < 2 ^ 64 ∧
    (target_lvl.toNat < s.core.cur_level → target_lvl.toNat < c.max_vars) ∧
    (∀ i < s.core.trail_end, (s.core.trl[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m',
      let s' : FullState :=
        { s with
          core := { s.core with vals := vals', lvl := lvl', rsns := rsns', trl := trl',
                                trail_pos := tp', trail_end := te', propagated := prop',
                                cur_level := cl', unassigned := unass' }
          scratch := sc' }
      s'.LengthsOk c → te' ≤ s.core.trail_end → prop' ≤ te' →
      cl' = min s.core.cur_level target_lvl.toNat → FullProbeScratchPres s s' →
      (∃ ta' ba' pt' pb' hp' ps' hl' qsi' qss', sc' = { s.scratch with
        target_assigned := ta', best_assigned := ba', phases_target := pt', phases_best := pb',
        heap := hp', pos := ps', heap_len := hl',
        q_search_idx := qsi', q_search_stamp := qss' }) →
      (∀ i < te', (trl'[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) →
      (∀ v < s.core.cur_vars, (s.core.lvl[v]?.getD 0#32).toNat ≤ target_lvl.toNat →
        lvl'[v]?.getD 0#32 = s.core.lvl[v]?.getD 0#32) →
      ((∃ F0 F_cur, FullWitnessInv c F0 F_cur s.core ∨ FullOtfsWitnessInv c F0 F_cur s.core) →
        (∀ l < 2 * s.core.cur_vars, vals'[l]?.getD 0#8 =
          if (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ target_lvl.toNat then
            s.core.vals[l]?.getD 0#8 else 0#8) ∧
        (∀ i < s.core.trail_end, let v := (s.core.trl[i]?.getD 0#32).toNat / 2
          lvl'[v]?.getD 0#32 = if (s.core.lvl[v]?.getD 0#32).toNat ≤ target_lvl.toNat then
            s.core.lvl[v]?.getD 0#32 else 0#32)) →
      (∀ F0 F_cur, FullWitnessInv c F0 F_cur s.core → target_lvl.toNat ≤ s.core.cur_level →
        FullWitnessInv c F0 F_cur s'.core) →
      (∀ F0 F_cur, FullOtfsWitnessInv c F0 F_cur s.core → target_lvl.toNat < s.core.cur_level →
        FullWitnessInv c F0 F_cur s'.core) →
      (FullMem c s' ⋆ R) m' → Q () m'

theorem fullAssignLvlSpec_xfree : Spec.XFree fullAssignLvlSpec := by xfree

theorem fullAssignSpec_xfree : Spec.XFree fullAssignSpec := by xfree

theorem fullSaveTargetBestSpec_xfree : Spec.XFree fullSaveTargetBestSpec := by xfree

theorem fullBacktrackRawSpec_xfree : Spec.XFree fullBacktrackRawSpec := by xfree

theorem fullBacktrackSpec_xfree : Spec.XFree fullBacktrackSpec := by xfree

/-- Upstream capability dependencies for `Src.Backtrack` (`full_heap_push` via `Heap`). -/
@[expose] def deps : List SpecEntry := Heap.Spec.specs

/-- Canonical `SpecEntry` table matching `Src.Backtrack.fns` 1-to-1. -/
@[expose] def specs : List SpecEntry :=
  [ ⟨"full_assign_lvl", [i64, i32, i32, i32], [], fullAssignLvlSpec, true⟩
  , ⟨"full_assign", [i64, i32, i32], [], fullAssignSpec, true⟩
  , ⟨"full_save_target_best", [i64], [], fullSaveTargetBestSpec, true⟩
  , ⟨"full_backtrack_raw_m5", [i64, i64], [], fullBacktrackRawSpec, true⟩
  , ⟨"full_backtrack", [i64, i64], [], fullBacktrackSpec, true⟩
  , ⟨"full_backtrack_ac_fid", [i64, i64], [], fullBacktrackSpec, true⟩ ]

theorem specs_sigs : specs.map SpecEntry.sig = Backtrack.fns.map Fn.sig := rfl

theorem specs_nodup : (specs.map SpecEntry.name).Nodup := by decide

theorem specs_noExit : specs.all SpecEntry.noExit = true := rfl

theorem has_full_assign_lvl {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_assign_lvl" fullAssignLvlSpec :=
  Env.Sat.has h List.mem_cons_self fullAssignLvlSpec_xfree

theorem has_full_assign {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_assign" fullAssignSpec :=
  Env.Sat.has h (.tail _ List.mem_cons_self) fullAssignSpec_xfree

theorem has_full_save_target_best {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_save_target_best" fullSaveTargetBestSpec :=
  Env.Sat.has h (.tail _ (.tail _ List.mem_cons_self)) fullSaveTargetBestSpec_xfree

theorem has_full_backtrack_raw_m5 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_backtrack_raw_m5" fullBacktrackRawSpec :=
  Env.Sat.has h (.tail _ (.tail _ (.tail _ List.mem_cons_self))) fullBacktrackRawSpec_xfree

theorem has_full_backtrack {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_backtrack" fullBacktrackSpec :=
  Env.Sat.has h (.tail _ (.tail _ (.tail _ (.tail _ List.mem_cons_self))))
    fullBacktrackSpec_xfree

theorem has_full_backtrack_ac_fid {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_backtrack_ac_fid" fullBacktrackSpec :=
  Env.Sat.has h (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ List.mem_cons_self)))))
    fullBacktrackSpec_xfree

end LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
