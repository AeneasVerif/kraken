/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Spec.Core
public import LeanQbe.T.Logic.CanonicalEnv

/-!
# Canonical Specifications for `Kissat.Src.Learn` (`4` C0 Functions)

Pure declarative specifications (`0` theorems, `0` tactics, `0` cross-subsystem `Spec` imports)
aligned 1:1 with `Src.Learn.fns`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Learn.Spec

open Std.Sat
open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open Kraken.Bedrock2.Test

/-! ## 1. `AgreesExcept` Mask & Factored `Pre` / `Post` Packages -/

/-- `AgreesExcept` core mask for `full_eager_subsume`. -/
@[expose] def eagerSubsumeCoreMask (k : FullCoreState) : FullCoreState :=
  { k with arena := [], arena_garbage := 0#64, num_redundant := 0#64 }

/-- Postcondition package for `full_one_lit_confl` (`8` fields). -/
structure OneLitConflPost (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s s' : FullState) (r : BitVec 64) : Prop where
  ret_cases : r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64
  cur_vars_eq : s'.core.cur_vars = s.core.cur_vars
  fuel_eq : s'.core.fuel = s.core.fuel
  work_stk2_eq : s'.scratch.work_stk2 = s.scratch.work_stk2
  on_20 : r = 20#64 → F0.Unsat ∧ FullOtfsInvW c F0 F_cur s' ∧
    s'.core.cur_level ≤ s.core.cur_level ∧ s'.core.dense_mode = s.core.dense_mode
  on_1 : r = 1#64 → FullSparseInvW c F0 F_cur s' ∧ s'.core.cur_level < s.core.cur_level
  on_2 : r = 2#64 → FullOtfsInvW c F0 F_cur s'
  on_0 : r = 0#64 → ∃ cut' ≤ s'.core.trail_end,
    FullCutInvW c F0 F_cur cut' s' ∧ 0 < s'.core.cur_level ∧
    s'.core.cur_level ≤ s.core.cur_level ∧ FullConflictOkCut F_cur cut' s'

/-- Precondition package for `full_learn_clause_m6` (`7` fields). -/
structure LearnClausePre (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s : FullState) : Prop where
  otfs_inv : FullOtfsInvW c F0 F_cur s
  level_pos : 0 < s.core.cur_level
  tmp_len_bounds : 1 ≤ s.core.tmp_len ∧ s.core.tmp_len ≤ s.core.cur_vars
  vars_nodup : ((s.core.tmp.take s.core.tmp_len).map fun x => x.toNat / 2).Nodup
  lits_falsified : ∀ k < s.core.tmp_len,
    let l := (s.core.tmp[k]?.getD 0#32).toNat
    l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8
  tail_levels : ∀ k, 1 ≤ k → k < s.core.tmp_len →
    let lv := (s.core.lvl[(s.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
    0 < lv ∧ lv < s.core.cur_level
  entails : (cnfOfClauses F_cur).EntailsClause
    (cnfClause ((s.core.tmp.take s.core.tmp_len).map BitVec.toNat))

/-- Postcondition package for `full_learn_clause_m6` (`10` fields). -/
structure LearnClausePost (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s s' : FullState) (r : BitVec 64) : Prop where
  ret_cases : r = 0#64 ∨ r = 1#64 ∨ r = 20#64
  cur_vars_eq : s'.core.cur_vars = s.core.cur_vars
  fuel_le : s'.core.fuel.toNat ≤ s.core.fuel.toNat
  probing_eq : s'.core.probing = s.core.probing
  min_clr_len_eq : s'.core.min_clr_len = s.core.min_clr_len
  work_stk1_eq : s'.scratch.work_stk1 = s.scratch.work_stk1
  work_stk2_eq : s'.scratch.work_stk2 = s.scratch.work_stk2
  on_20 : r = 20#64 → F0.Unsat ∧ FullSparseInvW c F0 F_cur s' ∧
    s'.core.cur_level < s.core.cur_level
  on_0 : r = 0#64 → FullSparseInvW c F0 F_cur s'
  on_1 : r = 1#64 → FullSparseInvW c F0 F_cur s' ∧ s'.core.cur_level < s.core.cur_level

/-! ## 2. Canonical Per-Function Specifications (`4` Distinct Specs for `4` C0 Functions) -/

/-- `full_det_new_level(h, jump)`: read-only chronological/non-chronological backtrack target
level selection. -/
@[expose] def detNewLevelSpec : Spec [i64, i64] [i64] :=
  FullContract.toSpec (W := Unit)
    { pre := fun _ s _ () => s.core.cur_level < 2 ^ 64
      post := fun _ s (jump, ()) () (r, ()) s' =>
        s' = s ∧ (s.core.cur_level = 0 → r = 0#64) ∧
        (0 < s.core.cur_level → jump.toNat < s.core.cur_level →
          jump.toNat ≤ r.toNat ∧ r.toNat < s.core.cur_level) }

/-- `full_one_lit_confl(h)`: chronological-backtracking fast path for conflicts with at most one
literal at `cur_level`. -/
@[expose] def oneLitConflSpec : Spec [i64] [i64] :=
  FullContract.toSpec (W := CNF Nat × List (List Nat) × Nat)
    { pre := fun c s () (F0, F_cur, cut) =>
        FullCutInvW c F0 F_cur cut s ∧ FullConflictOkCut F_cur cut s
      post := fun c s () (F0, F_cur, _) (r, ()) s' => OneLitConflPost c F0 F_cur s s' r }

/-- `full_eager_subsume(h, new_ref)`: marks recently learned clauses subsumed by
`tmp[0 ..< tmp_len)` as garbage while preserving `FullSparseInvW` and `work_stk1`/`work_stk2`. -/
@[expose] def eagerSubsumeSpec : Spec [i64, i64] [] :=
  FullContract.toSpec (W := CNF Nat × List (List Nat))
    { pre := fun c s (new_ref, ()) (F0, F_cur) =>
        FullSparseInvW c F0 F_cur s ∧
        (∀ k < s.core.tmp_len, (s.core.tmp[k]?.getD 0#32).toNat < 2 * c.max_vars) ∧
        (new_ref.toNat < 0x80000000 → new_ref.toNat ∈ fullArenaClauseRefs s)
      post := fun c s _ (F0, F_cur) () s' =>
        AgreesExcept eagerSubsumeCoreMask s.core s'.core ∧ FullSparseInvW c F0 F_cur s' ∧
        s'.scratch.work_stk1 = s.scratch.work_stk1 ∧
        s'.scratch.work_stk2 = s.scratch.work_stk2 }

/-- `full_learn_clause_m6(h, glue)`: backtracks, installs the learned unit/binary/large clause
(triggering forced purge if arena is full), and assigns the 1UIP literal. -/
@[expose] def learnClauseSpec : Spec [i64, i64] [i64] :=
  M6HdrContract.toSpec (W := CNF Nat × List (List Nat))
    { extFrame := .any
      pre := fun c _ s _ (F0, F_cur) => LearnClausePre c F0 F_cur s
      post := fun c _ s _ (F0, F_cur) (r, ()) _ s' => LearnClausePost c F0 F_cur s s' r }

/-- Canonical `4`-row specification table aligned 1:1 with `Src.Learn.fns`. -/
@[expose] def specs : List SpecEntry :=
  [ ⟨"full_det_new_level",   [i64, i64], [i64], detNewLevelSpec,  true⟩
  , ⟨"full_one_lit_confl",   [i64],      [i64], oneLitConflSpec,  true⟩
  , ⟨"full_eager_subsume",   [i64, i64], [],    eagerSubsumeSpec, true⟩
  , ⟨"full_learn_clause_m6", [i64, i64], [i64], learnClauseSpec,  true⟩
  ]

end LeanQbe.T.Examples.Kissat.Proof.Learn.Spec
