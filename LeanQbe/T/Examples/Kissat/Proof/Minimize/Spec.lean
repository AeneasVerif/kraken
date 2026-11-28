/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Spec.Core
public import LeanQbe.T.Logic.CanonicalEnv

/-!
# Canonical Specifications for `Kissat.Src.Minimize` (`6` C0 Functions)

Pure declarative specifications (`0` theorems, `0` tactics, `0` cross-subsystem `Spec` imports)
aligned 1:1 with `Src.Minimize.fns`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Minimize.Spec

open Std.Sat
open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open Kraken.Bedrock2.Test

/-! ## 1. Pure Helpers & `AgreesExcept` Masks -/

/-- Active (non-deleted `≠ 0xFFFFFFFF`) literal indices in `tmp[0 ..< len)`. -/
@[expose] def activeTmpLits (tmp : List (BitVec 32)) (len : Nat) : List Nat :=
  ((tmp.take len).filter (· ≠ 0xFFFFFFFF#32)).map BitVec.toNat

/-- `AgreesExcept` mask for `full_sort_tmp`. -/
@[expose] def sortTmpMask (s : FullState) : FullState :=
  { s with core := { s.core with tmp := [] }, scratch := { s.scratch with wsort := [] } }

/-- `AgreesExcept` mask shared by `full_min_lit_dfs_m8` and `full_shrink_lower_m8`. -/
@[expose] def minLitDfsMask (s : FullState) : FullState :=
  { s with
    core := { s.core with mrk := [], min_clr := [], min_clr_len := 0, min_clr_full := 0#64 }
    scratch := { s.scratch with wsort := [], search_ticks := 0#64 } }

/-- `AgreesExcept` mask for `full_shrink_blk_bool_m8`. -/
@[expose] def shrinkBlkMask (s : FullState) : FullState :=
  { s with
    core := { s.core with
      tmp := [], mrk := [], min_clr := [], min_clr_len := 0, min_clr_full := 0#64 }
    scratch := { s.scratch with shrink_stk := [], wsort := [], search_ticks := 0#64 } }

/-- `AgreesExcept` mask for `full_min_shrink_m6`. -/
@[expose] def minShrinkMask (s : FullState) : FullState :=
  { s with
    core := { s.core with
      tmp := [], tmp_len := 0, mrk := [], min_clr := [], min_clr_len := 0, min_clr_full := 0#64 }
    scratch := { s.scratch with
      conflicts := 0#64, learned_lits := 0#64, min_removed := 0#64,
      shrink_stk := [], wsort := [], search_ticks := 0#64, work_stk1 := [], res_sz := 0#64 } }

/-! ## 2. Factored `Pre` / `Post` Packages -/

/-- Postcondition package for `full_sort_tmp` (`7` fields). -/
structure SortTmpPost (s s' : FullState) : Prop where
  frame : AgreesExcept sortTmpMask s s'
  small_wsort_pres : s.core.tmp_len ≤ 32 → s'.scratch.wsort = s.scratch.wsort
  perm : (s'.core.tmp.take s.core.tmp_len).Perm (s.core.tmp.take s.core.tmp_len)
  head_pres : 0 < s.core.tmp_len → s'.core.tmp[0]? = s.core.tmp[0]?
  fwd_mem : ∀ j, 1 ≤ j → j < s.core.tmp_len →
    ∃ i, 1 ≤ i ∧ i < s.core.tmp_len ∧ s'.core.tmp[j]? = s.core.tmp[i]?
  bwd_mem : ∀ i, 1 ≤ i → i < s.core.tmp_len →
    ∃ j, 1 ≤ j ∧ j < s.core.tmp_len ∧ s.core.tmp[i]? = s'.core.tmp[j]?
  levels_sorted : ∀ i j, 1 ≤ i → i ≤ j → j < s.core.tmp_len →
    (s.core.lvl[(s'.core.tmp[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
    (s.core.lvl[(s'.core.tmp[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat

/-- Shared precondition for `full_min_lit_dfs_m8` and `full_shrink_lower_m8` (`6` fields). -/
structure MinLitBasePre (c : FullCfg) (F0 : CNF Nat) (s : FullState)
    (keepSet : List Nat) (lit : BitVec 32) : Prop where
  core_inv : FullOtfsCoreInv c F0 s
  min_inv : FullMinMarkInv s.core keepSet
  lit_lt : lit.toNat < 2 * s.core.cur_vars
  lit_false : s.core.vals[lit.toNat]?.getD 0#8 = 0xFF#8
  lvl_lt : (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat < s.core.cur_level
  no_bit8 : ∀ v < s.core.cur_vars,
    (s.core.lvl[v]?.getD 0#32).toNat ≤ (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat →
    (s.core.mrk[v]?.getD 0#8 &&& 8#8) = 0#8

/-- Shared mark-preservation postcondition for `full_min_lit_dfs_m8` and
`full_shrink_lower_m8` (`5` fields). -/
structure MinMarkPost (s s' : FullState) (keepSet : List Nat) : Prop where
  frame : AgreesExcept minLitDfsMask s s'
  mrk_hi_pres : ∀ v, s.core.cur_vars ≤ v → s'.core.mrk[v]? = s.core.mrk[v]?
  bit2_mono : ∀ v < s.core.cur_vars,
    (s.core.mrk[v]?.getD 0#8 &&& 2#8) ≠ 0#8 → (s'.core.mrk[v]?.getD 0#8 &&& 2#8) ≠ 0#8
  bit8_pres : ∀ v < s.core.cur_vars,
    (s'.core.mrk[v]?.getD 0#8 &&& 8#8) = (s.core.mrk[v]?.getD 0#8 &&& 8#8)
  min_inv : FullMinMarkInv s'.core keepSet

/-- Precondition package for `full_shrink_blk_bool_m8` (`10` fields). -/
structure ShrinkBlkPre (c : FullCfg) (F0 : CNF Nat) (s : FullState) (keepLen : Nat)
    (beg end_b max_tr : BitVec 64) (blvl : BitVec 32) : Prop where
  core_inv : FullOtfsCoreInv c F0 s
  min_inv : FullMinMarkInv s.core (activeTmpLits s.core.tmp keepLen)
  no_bit8 : ∀ v < s.core.cur_vars, (s.core.mrk[v]?.getD 0#8 &&& 8#8) = 0#8
  beg_pos : 1 ≤ beg.toNat
  beg_lt_end : beg.toNat < end_b.toNat
  end_le_keep : end_b.toNat ≤ keepLen
  keep_le_vars : keepLen ≤ s.core.cur_vars
  blvl_bounds : 0 < blvl.toNat ∧ blvl.toNat < s.core.cur_level
  blk_ok : ∀ k, beg.toNat ≤ k → k < end_b.toNat →
    let l := (s.core.tmp[k]?.getD 0#32).toNat
    l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
    (s.core.lvl[l / 2]?.getD 0#32).toNat = blvl.toNat ∧
    (s.core.trail_pos[l / 2]?.getD 0#32).toNat ≤ max_tr.toNat
  keep_ok : ∀ k < keepLen, s.core.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
    let l := (s.core.tmp[k]?.getD 0#32).toNat
    l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
    (s.core.mrk[l / 2]?.getD 0#8 &&& 2#8) ≠ 0#8

/-- Postcondition package for `full_shrink_blk_bool_m8` (`12` fields). -/
structure ShrinkBlkPost (c : FullCfg) (F0 : CNF Nat) (s s' : FullState) (keepLen : Nat)
    (beg end_b : BitVec 64) (blvl : BitVec 32) (ok : Bool) : Prop where
  frame : AgreesExcept shrinkBlkMask s s'
  core_inv : FullOtfsCoreInv c F0 s'
  min_inv : FullMinMarkInv s'.core (activeTmpLits s'.core.tmp keepLen)
  mrk_hi_pres : ∀ v, s.core.cur_vars ≤ v → s'.core.mrk[v]? = s.core.mrk[v]?
  no_bit8 : ∀ v < s.core.cur_vars, (s'.core.mrk[v]?.getD 0#8 &&& 8#8) = 0#8
  bit2_mono : ∀ v < s.core.cur_vars,
    (s.core.mrk[v]?.getD 0#8 &&& 2#8) ≠ 0#8 → (s'.core.mrk[v]?.getD 0#8 &&& 2#8) ≠ 0#8
  false_tmp_eq : ok = false → s'.core.tmp = s.core.tmp
  outside_tmp_eq : ∀ k < keepLen, (k < beg.toNat ∨ end_b.toNat ≤ k) →
    s'.core.tmp[k]? = s.core.tmp[k]?
  blk_lvl_ok : ∀ k, beg.toNat ≤ k → k < end_b.toNat →
    s'.core.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
    (s.core.lvl[(s'.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = blvl.toNat
  nodup_pres : ((activeTmpLits s.core.tmp keepLen).map (· / 2)).Nodup →
    (∀ k < keepLen, (k < beg.toNat ∨ end_b.toNat ≤ k) →
      s.core.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
      (s.core.lvl[(s.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≠ blvl.toNat) →
    ((activeTmpLits s'.core.tmp keepLen).map (· / 2)).Nodup
  entails_pres : ∀ F_cur, FullOtfsWitnessInv c F0 F_cur s.core →
    (cnfOfClauses F_cur).EntailsClause (cnfClause (activeTmpLits s.core.tmp keepLen)) →
    FullOtfsWitnessInv c F0 F_cur s'.core ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause (activeTmpLits s'.core.tmp keepLen))
  keep_ok : ∀ k < keepLen, s'.core.tmp[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
    let l := (s'.core.tmp[k]?.getD 0#32).toNat
    l < 2 * s.core.cur_vars ∧ s'.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
    (s'.core.mrk[l / 2]?.getD 0#8 &&& 2#8) ≠ 0#8

/-- Precondition package for `full_min_shrink_m6` (`9` fields). -/
structure MinShrinkPre (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s : FullState) : Prop where
  otfs_inv : FullOtfsWitnessInv c F0 F_cur s.core
  marks_clear : FullLitMarksClear c s
  tmp_len_pos : 1 ≤ s.core.tmp_len
  tmp_len_le : s.core.tmp_len ≤ s.core.cur_vars
  vars_nodup : ((s.core.tmp.take s.core.tmp_len).map fun x => x.toNat / 2).Nodup
  entails : (cnfOfClauses F_cur).EntailsClause
    (cnfClause ((s.core.tmp.take s.core.tmp_len).map BitVec.toNat))
  lits_falsified : ∀ k < s.core.tmp_len,
    let l := (s.core.tmp[k]?.getD 0#32).toNat
    l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8
  tail_levels : ∀ k, 1 ≤ k → k < s.core.tmp_len →
    let lv := (s.core.lvl[(s.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
    0 < lv ∧ lv < s.core.cur_level
  uip_level : (s.core.lvl[(s.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
    s.core.cur_level

/-- Postcondition package for `full_min_shrink_m6` (`9` fields). -/
structure MinShrinkPost (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s s' : FullState) : Prop where
  frame : AgreesExcept minShrinkMask s s'
  otfs_inv : FullOtfsWitnessInv c F0 F_cur s'.core
  marks_clear : FullLitMarksClear c s'
  tl_pos : 1 ≤ s'.core.tmp_len
  tl_le : s'.core.tmp_len ≤ s.core.tmp_len
  head_eq : s'.core.tmp[0]? = s.core.tmp[0]?
  vars_nodup : ((s'.core.tmp.take s'.core.tmp_len).map fun x => x.toNat / 2).Nodup
  tail_ok : ∀ j, 1 ≤ j → j < s'.core.tmp_len →
    let l := (s'.core.tmp[j]?.getD 0#32).toNat
    let lv := (s.core.lvl[l / 2]?.getD 0#32).toNat
    l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧ 0 < lv ∧ lv < s.core.cur_level
  entails : (cnfOfClauses F_cur).EntailsClause
    (cnfClause ((s'.core.tmp.take s'.core.tmp_len).map BitVec.toNat))

/-! ## 3. Canonical Per-Function Specifications (`6` Distinct Specs for `6` C0 Functions) -/

/-- `full_min_mark(h, v, tag)`: marks variable `v` with `tag` and records newly marked variables
in `min_clr` (or sets `min_clr_full := 1`). -/
@[expose] def minMarkSpec : Spec [i64, i32, i8] [] :=
  FullContract.toSpec (W := Unit)
    { pre := fun _ _ _ () => True
      post := fun _ s (v, tag, ()) () () s' =>
        let cur := s.core.mrk[v.toNat]?.getD 0#8
        s' = if s.core.cur_vars ≤ v.toNat ∨ (cur &&& tag) ≠ 0#8 then s
             else fullMinMarkState s v.toNat tag }

/-- `full_sort_tmp(h)`: level-only sort of `tmp[1 ..< tmp_len)` keeping `tmp[0]` fixed. -/
@[expose] def sortTmpSpec : Spec [i64] [] :=
  FullContract.toSpec (W := Unit)
    { pre := fun c s () () =>
        s.core.tmp_len ≤ c.max_vars ∧
        (∀ k, 1 ≤ k → k < s.core.tmp_len → (s.core.tmp[k]?.getD 0#32).toNat < 2 * c.max_vars)
      post := fun _ s () () () s' => SortTmpPost s s' }

/-- `full_min_lit_dfs_m8(h, root_lit, minimizing, check_used)`: iterative DFS
minimization check for `root_lit`. -/
@[expose] def minLitDfsSpec : Spec [i64, i32, .bool, .bool] [.bool] :=
  FullContract.toSpec (W := CNF Nat × List Nat)
    { pre := fun c s (root_lit, _, _, ()) (F0, keepSet) =>
        MinLitBasePre c F0 s keepSet root_lit
      post := fun _ s (root_lit, _, _, ()) (_, keepSet) (ok, ()) s' =>
        MinMarkPost s s' keepSet ∧
        (ok = true →
          (∀ keep', (∀ l ∈ keepSet, l = root_lit.toNat ∨ l ∈ keep') →
            FullMinMarkInv s'.core keep') ∧
          FullMinMarkInv (fullMinMarkCore s'.core (root_lit.toNat / 2) 2#8) keepSet) }

/-- `full_shrink_lower_m8(h, ot, ov)`: lower-level antecedent check during block shrinking. -/
@[expose] def shrinkLowerSpec : Spec [i64, i32, i32] [.bool] :=
  FullContract.toSpec (W := CNF Nat × List Nat)
    { pre := fun c s (ot, ov, ()) (F0, keepSet) =>
        ov.toNat = ot.toNat / 2 ∧ MinLitBasePre c F0 s keepSet ot
      post := fun _ s (_, ov, ()) (_, keepSet) (ok, ()) s' =>
        MinMarkPost s s' keepSet ∧ (ok = true → (s'.core.mrk[ov.toNat]?.getD 0#8 &&& 2#8) ≠ 0#8) }

/-- `full_shrink_blk_bool_m8(h, beg, end_b, blvl, max_tr)`: block-level UIP shrinking of
`tmp[beg ..< end_b)` at decision level `blvl`. -/
@[expose] def shrinkBlkSpec : Spec [i64, i64, i64, i32, i64] [.bool] :=
  FullContract.toSpec (W := CNF Nat × Nat)
    { pre := fun c s (beg, end_b, blvl, max_tr, ()) (F0, keepLen) =>
        ShrinkBlkPre c F0 s keepLen beg end_b max_tr blvl
      post := fun c s (beg, end_b, blvl, _, ()) (F0, keepLen) (ok, ()) s' =>
        ShrinkBlkPost c F0 s s' keepLen beg end_b blvl ok }

/-- `full_min_shrink_m6(h)`: top-level clause minimization + block shrinking of
`tmp[0 ..< tmp_len)`. -/
@[expose] def minShrinkSpec : Spec [i64] [] :=
  FullContract.toSpec (W := CNF Nat × List (List Nat))
    { pre := fun c s () (F0, F_cur) => MinShrinkPre c F0 F_cur s
      post := fun c s () (F0, F_cur) () s' => MinShrinkPost c F0 F_cur s s' }

/-- Canonical `6`-row specification table aligned 1:1 with `Src.Minimize.fns`. -/
@[expose] def specs : List SpecEntry :=
  [ ⟨"full_min_mark",           [i64, i32, i8],            [],      minMarkSpec,     true⟩
  , ⟨"full_sort_tmp",           [i64],                     [],      sortTmpSpec,     true⟩
  , ⟨"full_min_lit_dfs_m8",     [i64, i32, .bool, .bool],  [.bool], minLitDfsSpec,   true⟩
  , ⟨"full_shrink_lower_m8",    [i64, i32, i32],           [.bool], shrinkLowerSpec, true⟩
  , ⟨"full_shrink_blk_bool_m8", [i64, i64, i64, i32, i64], [.bool], shrinkBlkSpec,   true⟩
  , ⟨"full_min_shrink_m6",      [i64],                     [],      minShrinkSpec,   true⟩
  ]

end LeanQbe.T.Examples.Kissat.Proof.Minimize.Spec
