/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Spec.Core
public import LeanQbe.T.Logic.CanonicalEnv

/-!
# Canonical Specifications for `Kissat.Src.Reduce` (`5` C0 Functions)

Pure declarative specifications (`0` theorems, `0` tactics, `0` cross-subsystem `Spec` imports)
aligned 1:1 with `Src.Reduce.fns`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Reduce.Spec

open Std.Sat
open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Proof.Spec
open Kraken.Bedrock2.Test

/-! ## 1. Shared Postcondition Packages -/

/-- Trail preservation whenever `full_reduce_{m6,purge_c0}` returns at positive decision level. -/
@[expose] def ReduceTrailPres (s s' : FullState) : Prop :=
  0 < s'.core.cur_level →
    s'.core.cur_level = s.core.cur_level ∧ s'.core.vals = s.core.vals ∧
    s'.core.lvl = s.core.lvl ∧ s'.core.trl = s.core.trl ∧
    s'.core.trail_pos = s.core.trail_pos ∧ s'.core.trail_end = s.core.trail_end

/-- Shared preservation package for `full_reduce_purge_c0` and `full_reduce_m6 (force = true)`
(`11` fields). -/
structure ReduceForcePost (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (ext' : List (BitVec 64)) (s s' : FullState) (r : BitVec 64) : Prop where
  invW : FullM6HdrInvW c F0 F_cur ext' s'
  cur_level_le : s'.core.cur_level ≤ s.core.cur_level
  cur_vars_eq : s'.core.cur_vars = s.core.cur_vars
  tmp_eq : s'.core.tmp = s.core.tmp
  tmp_len_eq : s'.core.tmp_len = s.core.tmp_len
  probing_eq : s'.core.probing = s.core.probing
  min_clr_len_eq : s'.core.min_clr_len = s.core.min_clr_len
  work_stk1_eq : s'.scratch.work_stk1 = s.scratch.work_stk1
  work_stk2_eq : s'.scratch.work_stk2 = s.scratch.work_stk2
  oom_pres : r = 1#64 → s.core.oom = 0#64 → s'.core.oom = 0#64
  trail_pres : ReduceTrailPres s s'

/-! ## 2. Canonical Per-Function Specifications (`5` Distinct Specs for `5` C0 Functions) -/

/-- `full_red_less(ar, a, b)`: read-only comparator ordering redundant clause refs by
`(glue, size)`. -/
@[expose] def redLessSpec : Spec [i64, i32, i32] [.bool] :=
  FnContract.toSpec (W := List (BitVec 32)) (W' := Unit)
    { pre := fun (_, a, b, ()) ar => a.toNat + 2 < ar.length ∧ b.toNat + 2 < ar.length
      mem := fun (arp, _, _, ()) ar => array (t := i32) arp ar
      post := fun _ _ _ () => True
      postMem := fun (arp, _, _, ()) ar _ () => array (t := i32) arp ar }

/-- `full_red_sift(ar, rr, start, n)`: heap sift-down of redundant clause refs `rr[0 ..< n)`. -/
@[expose] def redSiftSpec : Spec [i64, i64, i64, i64] [] :=
  FnContract.toSpec (W := List (BitVec 32) × List (BitVec 32)) (W' := List (BitVec 32))
    { pre := fun (_, _, start, n, ()) (ar, rr) =>
        start.toNat ≤ n.toNat ∧ n.toNat ≤ rr.length ∧ n.toNat < 2 ^ 62 ∧
        (∀ k < n.toNat, (rr[k]?.getD 0#32).toNat + 2 < ar.length)
      mem := fun (arp, rrp, _, _, ()) (ar, rr) =>
        array (t := i32) arp ar ⋆ array (t := i32) rrp rr
      post := fun (_, _, _, n, ()) (_, rr) () rr' =>
        rr'.length = rr.length ∧ (∀ k, n.toNat ≤ k → rr'[k]? = rr[k]?) ∧
        (∀ k < n.toNat, ∃ j < n.toNat, rr'[k]? = rr[j]?)
      postMem := fun (arp, rrp, _, _, ()) (ar, _) () rr' =>
        array (t := i32) arp ar ⋆ array (t := i32) rrp rr' }

/-- `full_sort_reds(h, n)`: sorts `red_refs[0 ..< n)` using `scratch_buf`, preserving `core` and
all other scratch fields. -/
@[expose] def sortRedsSpec : Spec [i64, i64] [] :=
  FullContract.toSpec (W := Unit)
    { pre := fun c s (n, ()) () =>
        n.toNat ≤ c.red_cap ∧
        (∀ k < n.toNat, (s.scratch.red_refs[k]?.getD 0#32).toNat + 2 < c.arena_cap)
      post := fun _ s (n, ()) () () s' =>
        CorePres s s' ∧ ScratchModifies [.red_refs, .scratch_buf] s s' ∧
        (∀ k < n.toNat, ∃ j < n.toNat, s'.scratch.red_refs[k]? = s.scratch.red_refs[j]?) }

/-- `full_reduce_m6(h, force)`: clause-database reduction (with optional root-level compaction
when `force = false`, or witnessed in-place `ReduceForcePost` when `force = true`). -/
@[expose] def reduceSpec : Spec [i64, .bool] [i64] :=
  M6HdrCfgContract.toSpec (W := CNF Nat × List (List Nat))
    { extFrame := .any
      pre := fun c ext s _ (F0, F_cur) => FullM6HdrInvW c F0 F_cur ext s
      post := fun c _ s (force, ()) (F0, F_cur) (r, ()) c' ext' s' =>
        FullM6HdrInv c' F0 ext' s' ∧ (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) ∧
        s'.core.cur_vars ≤ s.core.cur_vars ∧ s'.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        (r = 20#64 → F0.Unsat) ∧ (r = 1#64 → s'.core.cur_level ≤ s.core.cur_level) ∧
        (force = true → c' = c ∧ ReduceForcePost c F0 F_cur ext' s s' r) }

/-- `full_reduce_purge_c0(h)`: forced non-compacting clause purge preserving `c`, `F_cur`, and
`ReduceForcePost`. -/
@[expose] def reducePurgeSpec : Spec [i64] [i64] :=
  M6HdrContract.toSpec (W := CNF Nat × List (List Nat))
    { extFrame := .any
      pre := fun c ext s () (F0, F_cur) => FullM6HdrInvW c F0 F_cur ext s
      post := fun c _ s () (F0, F_cur) (r, ()) ext' s' =>
        (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) ∧ s'.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        (r = 20#64 → F0.Unsat) ∧ ReduceForcePost c F0 F_cur ext' s s' r }

/-- Canonical `5`-row specification table aligned 1:1 with `Src.Reduce.fns`. -/
@[expose] def specs : List SpecEntry :=
  [ ⟨"full_red_less",        [i64, i32, i32],      [.bool], redLessSpec,     true⟩
  , ⟨"full_red_sift",        [i64, i64, i64, i64], [],      redSiftSpec,     true⟩
  , ⟨"full_sort_reds",       [i64, i64],           [],      sortRedsSpec,    true⟩
  , ⟨"full_reduce_m6",       [i64, .bool],         [i64],   reduceSpec,      true⟩
  , ⟨"full_reduce_purge_c0", [i64],                [i64],   reducePurgeSpec, true⟩
  ]

end LeanQbe.T.Examples.Kissat.Proof.Reduce.Spec
