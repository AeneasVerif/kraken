/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Reduce
public import LeanQbe.T.Examples.Kissat.Proof.Arena.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Collect.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Compact.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Internal.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Limits.Spec
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Tiers.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts2
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
public import LeanQbe.T.Logic.CanonicalEnv

/-!
# Canonical Env Specs for `Kissat/Src/Reduce.lean` (`Proof.Reduce.Spec`)

Defines `CanonicalEnv` contracts and `specs` / `deps` for the 5 clause-reduction functions of
`Src.Reduce`: `full_red_less`, `full_red_sift`, `full_sort_reds`, `full_reduce_m6`, and
`full_reduce_purge_c0`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Reduce.Spec

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src
open LeanQbe.T.Examples.Kissat.Src.Reduce
open LeanQbe.T.Examples.Kissat.Proof.Spec
open Kraken.Bedrock2.Test

@[expose] def deps : List SpecEntry :=
  Arena.Spec.specs ++ Backtrack.Spec.specs ++ Float64.Spec.specs ++
  Internal.Spec.specs ++ Limits.Spec.specs ++ Tiers.Spec.specs ++
  Collect.Spec.specs ++ Compact.Spec.specs ++ PropSearch.Spec.specs

@[expose] def fullSortRedsSpec : Spec [i64, i64] [] := fun (h, n, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ n.toNat ≤ c.red_cap ∧
    (∀ k < n.toNat, (s.scratch.red_refs[k]?.getD 0#32).toNat + 2 < c.arena_cap) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ rr' sb' m', rr'.length = c.red_cap → sb'.length = c.scratch_cap →
      (∀ k < n.toNat, ∃ j < n.toNat, rr'[k]? = s.scratch.red_refs[j]?) →
      (FullMem c { s with scratch := { s.scratch with red_refs := rr', scratch_buf := sb' } } ⋆ R)
        m' →
      Q () m'

@[expose] def fullReduceM6Spec : Spec [i64, .bool] [i64] := fun (h, force, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (ext : List (BitVec 64))
      (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrInvW c F0 F_cur ext s ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ r c' ext' s' m',
      FullCfgCompat c c' → FullM6HdrInv c' F0 ext' s' →
      (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.cur_vars ≤ s.core.cur_vars →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 20#64 → F0.Unsat) →
      (r = 1#64 → s'.core.cur_level ≤ s.core.cur_level) →
      (force = true →
        c' = c ∧ FullM6HdrInvW c F0 F_cur ext' s' ∧
        s'.core.cur_level ≤ s.core.cur_level ∧
        s'.core.cur_vars = s.core.cur_vars ∧
        s'.core.tmp = s.core.tmp ∧ s'.core.tmp_len = s.core.tmp_len ∧
        s'.core.probing = s.core.probing ∧ s'.core.min_clr_len = s.core.min_clr_len ∧
        s'.scratch.work_stk1 = s.scratch.work_stk1 ∧
        s'.scratch.work_stk2 = s.scratch.work_stk2 ∧
        (r = 1#64 → s.core.oom = 0#64 → s'.core.oom = 0#64) ∧
        (0 < s'.core.cur_level →
          s'.core.cur_level = s.core.cur_level ∧ s'.core.vals = s.core.vals ∧
          s'.core.lvl = s.core.lvl ∧ s'.core.trl = s.core.trl ∧
          s'.core.trail_pos = s.core.trail_pos ∧ s'.core.trail_end = s.core.trail_end)) →
      (FullM6HdrMem c' ext' s' ⋆ R) m' → Q (r, ()) m'

@[expose] def fullReducePurgeC0Spec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (ext : List (BitVec 64))
      (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrInvW c F0 F_cur ext s ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ r ext' s' m',
      FullM6HdrInvW c F0 F_cur ext' s' →
      (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.cur_level ≤ s.core.cur_level →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      s'.core.cur_vars = s.core.cur_vars →
      s'.core.tmp = s.core.tmp →
      s'.core.tmp_len = s.core.tmp_len →
      s'.core.probing = s.core.probing →
      s'.core.min_clr_len = s.core.min_clr_len →
      s'.scratch.work_stk1 = s.scratch.work_stk1 →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (r = 20#64 → F0.Unsat) →
      (r = 1#64 → s.core.oom = 0#64 → s'.core.oom = 0#64) →
      (0 < s'.core.cur_level →
        s'.core.cur_level = s.core.cur_level ∧ s'.core.vals = s.core.vals ∧
        s'.core.lvl = s.core.lvl ∧ s'.core.trl = s.core.trl ∧
        s'.core.trail_pos = s.core.trail_pos ∧ s'.core.trail_end = s.core.trail_end) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

theorem fullRedLessSpec_xfree : Spec.XFree fullRedLessSpec := fun _ _ _ _ _ h => h
theorem fullRedSiftSpec_xfree : Spec.XFree fullRedSiftSpec := fun _ _ _ _ _ h => h
theorem fullSortRedsSpec_xfree : Spec.XFree fullSortRedsSpec := fun _ _ _ _ _ h => h
theorem fullReduceM6Spec_xfree : Spec.XFree fullReduceM6Spec := fun _ _ _ _ _ h => h
theorem fullReducePurgeC0Spec_xfree : Spec.XFree fullReducePurgeC0Spec := fun _ _ _ _ _ h => h

@[expose] def specs : List SpecEntry :=
  [ { name := "full_red_less", as := [i64, i32, i32], rs := [.bool],
      spec := fullRedLessSpec, noExit := true }
  , { name := "full_red_sift", as := [i64, i64, i64, i64], rs := [],
      spec := fullRedSiftSpec, noExit := true }
  , { name := "full_sort_reds", as := [i64, i64], rs := [],
      spec := fullSortRedsSpec, noExit := true }
  , { name := "full_reduce_m6", as := [i64, .bool], rs := [i64],
      spec := fullReduceM6Spec, noExit := true }
  , { name := "full_reduce_purge_c0", as := [i64], rs := [i64],
      spec := fullReducePurgeC0Spec, noExit := true }
  ]

theorem specs_sigs : specs.map SpecEntry.sig = fns.map Fn.sig := by decide

theorem specs_nodup : (specs.map SpecEntry.name).Nodup := by decide

theorem specs_noExit : ∀ e ∈ specs, e.noExit = true := by decide

theorem specs_xfree : ∀ e ∈ specs, e.spec.XFree := by
  intro e he
  rcases List.mem_cons.mp he with rfl | he
  · exact fullRedLessSpec_xfree
  · rcases List.mem_cons.mp he with rfl | he
    · exact fullRedSiftSpec_xfree
    · rcases List.mem_cons.mp he with rfl | he
      · exact fullSortRedsSpec_xfree
      · rcases List.mem_cons.mp he with rfl | he
        · exact fullReduceM6Spec_xfree
        · rcases List.mem_cons.mp he with rfl | he
          · exact fullReducePurgeC0Spec_xfree
          · contradiction

section EnvHas
variable {Γ : Env}

theorem has_full_red_less (hΓ : Γ.Sat specs) :
    Γ.Has "full_red_less" fullRedLessSpec :=
  hΓ.has (List.getElem_mem (l := specs) (n := 0) (by decide)) fullRedLessSpec_xfree

theorem has_full_red_sift (hΓ : Γ.Sat specs) :
    Γ.Has "full_red_sift" fullRedSiftSpec :=
  hΓ.has (List.getElem_mem (l := specs) (n := 1) (by decide)) fullRedSiftSpec_xfree

theorem has_full_sort_reds (hΓ : Γ.Sat specs) :
    Γ.Has "full_sort_reds" fullSortRedsSpec :=
  hΓ.has (List.getElem_mem (l := specs) (n := 2) (by decide)) fullSortRedsSpec_xfree

theorem has_full_reduce_m6 (hΓ : Γ.Sat specs) :
    Γ.Has "full_reduce_m6" fullReduceM6Spec :=
  hΓ.has (List.getElem_mem (l := specs) (n := 3) (by decide)) fullReduceM6Spec_xfree

theorem has_full_reduce_purge_c0 (hΓ : Γ.Sat specs) :
    Γ.Has "full_reduce_purge_c0" fullReducePurgeC0Spec :=
  hΓ.has (List.getElem_mem (l := specs) (n := 4) (by decide)) fullReducePurgeC0Spec_xfree

end EnvHas

end LeanQbe.T.Examples.Kissat.Proof.Reduce.Spec
