module

public import LeanQbe.T.Examples.Kissat.FullM7AnalyzeSort
public import LeanQbe.T.Examples.Kissat.FullMinLemmas1
public import LeanQbe.T.Examples.Kissat.FullCongLemmas1
public import LeanQbe.T.Examples.Kissat.FullM5SchedLemmas
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Wave 4G Proof Shard 0: `full_sort_u32_m7`, `full_log10_q16_m7`, `full_rephase_m7`

M1-clean UNSAT-only `Func.wp` proofs (`public section`, `0 @[expose]`, `0 import all`):
1. Public Wave-4G specifications (`m7SortU32SortedSpec`, `m7SortTmpHeapSpec`, `m7SortTmpSpec`,
   `m7Log10Q16Spec`) with `_of`, `_elim`, `_monoX`, `toCanonical`, and `SafetySlice` bridges.
2. `full_sort_u32_m7_wp`: proves Shellsort against `m7SortU32SortedSpec` (`Perm`, length, suffix,
   ascending `u32` order) and derives canonical `Full.fullSortU32Spec`.
3. `full_log10_q16_m7_wp` & `full_rephase_m7_wp`: proves 6-step focused `(B,W,I,B,W,O)`
   `full_rephase_m7` against exact `FullM5Sched.m5RephaseSpec` (and `Full.fullRephaseSpec`
   on `stable ≠ 0`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7AnalyzeSort

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Full.FullMinTactics
open Kraken.Bedrock2.Test

/-! ## 1. Wave-4G Public Spec Definitions & Constructors (Opaque M1) -/

/-- Monotonic non-decreasing predicate on `arr[0 ..< n)` in `u32` numeric order. -/
def M7SortedU32 (arr : List (BitVec 32)) (n : Nat) : Prop :=
  ∀ i j, i ≤ j → j < n → (arr[i]?.getD 0#32).toNat ≤ (arr[j]?.getD 0#32).toNat

/-- Strengthened `u32` sort contract establishing both `Perm` and ascending order on `arr[0..n)`. -/
def m7SortU32SortedSpec : Spec [i64, i32] [] := fun (arr_ptr, n, ()) m Q _ =>
  ∃ (arr : List (BitVec 32)) (R : Mem 64 → Prop),
    n.toNat ≤ arr.length ∧ (array (t := i32) arr_ptr arr ⋆ R) m ∧
    ∀ arr' m', arr'.length = arr.length →
      (arr'.take n.toNat).Perm (arr.take n.toNat) →
      (∀ k, n.toNat ≤ k → arr'[k]? = arr[k]?) →
      M7SortedU32 arr' n.toNat →
      (array (t := i32) arr_ptr arr' ⋆ R) m' → Q () m'

theorem m7SortU32SortedSpec_of {arr_ptr : BitVec 64} {n : BitVec 32}
    {arr : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post []} {X : XPost}
    (hle : n.toNat ≤ arr.length) (hm : (array (t := i32) arr_ptr arr ⋆ R) m)
    (hQ : ∀ arr' m', arr'.length = arr.length →
      (arr'.take n.toNat).Perm (arr.take n.toNat) →
      (∀ k, n.toNat ≤ k → arr'[k]? = arr[k]?) →
      M7SortedU32 arr' n.toNat →
      (array (t := i32) arr_ptr arr' ⋆ R) m' → Q () m') :
    m7SortU32SortedSpec (arr_ptr, n, ()) m Q X :=
  ⟨arr, R, hle, hm, hQ⟩

theorem m7SortU32SortedSpec_elim {a : Tup Val [i64, i32]} {m : Mem 64} {Q : Post []} {X : XPost}
    (h : m7SortU32SortedSpec a m Q X) :
    ∃ (arr : List (BitVec 32)) (R : Mem 64 → Prop),
      a.2.1.toNat ≤ arr.length ∧ (array (t := i32) a.1 arr ⋆ R) m ∧
      ∀ arr' m', arr'.length = arr.length →
        (arr'.take a.2.1.toNat).Perm (arr.take a.2.1.toNat) →
        (∀ k, a.2.1.toNat ≤ k → arr'[k]? = arr[k]?) →
        M7SortedU32 arr' a.2.1.toNat →
        (array (t := i32) a.1 arr' ⋆ R) m' → Q () m' :=
  h

theorem m7SortU32SortedSpec_monoX {a : Tup Val [i64, i32]} {m : Mem 64}
    {Q : Post []} {X₁ X₂ : XPost} (h : m7SortU32SortedSpec a m Q X₁) :
    m7SortU32SortedSpec a m Q X₂ := h

theorem fullSortU32Spec_to_m7Sorted {a : Tup Val [i64, i32]} {m : Mem 64}
    {Q : Post []} {X : XPost} (h : Full.fullSortU32Spec a m Q X) :
    m7SortU32SortedSpec a m Q X := by
  rcases a with ⟨arr_ptr, n, ⟨⟩⟩
  rcases h with ⟨arr, R, hle, hm, hQ⟩
  exact ⟨arr, R, hle, hm, fun arr' m' hl hp hs _ hm' => hQ arr' m' hl hp hs hm'⟩

/-- Base-pointer `(lvl, tpos)` heapsort contract for `full_sort_tmp_heap_m7(tmp, lvl, tpos, lim)`.
Sorts `tmp[1 ..< lim)` in place by ascending `fullTmpLe lvl tpos`, preserving `tmp[0]` and suffix.
-/
def m7SortTmpHeapSpec : Spec [i64, i64, i64, i64] [] :=
  fun (tmp_ptr, lvl_ptr, tpos_ptr, tlen, ()) m Q _ =>
    ∃ (tmp lvl tpos : List (BitVec 32)) (R : Mem 64 → Prop),
      tlen.toNat ≤ tmp.length ∧ tlen.toNat < 2 ^ 60 ∧
      (∀ k, 1 ≤ k → k < tlen.toNat →
        (tmp[k]?.getD 0#32).toNat / 2 < lvl.length ∧
        (tmp[k]?.getD 0#32).toNat / 2 < tpos.length) ∧
      (array (t := i32) tmp_ptr tmp ⋆ array (t := i32) lvl_ptr lvl ⋆
        array (t := i32) tpos_ptr tpos ⋆ R) m ∧
      ∀ tmp' m',
        tmp'.length = tmp.length →
        (tmp'.take tlen.toNat).Perm (tmp.take tlen.toNat) →
        (0 < tlen.toNat → tmp'[0]? = tmp[0]?) →
        (∀ k, tlen.toNat ≤ k → tmp'[k]? = tmp[k]?) →
        Full.FullSortSliceEq tmp' tmp tlen.toNat →
        (∀ i j, 1 ≤ i → i ≤ j → j < tlen.toNat →
          Full.fullTmpLe lvl tpos (tmp'[i]?.getD 0#32) (tmp'[j]?.getD 0#32)) →
        (array (t := i32) tmp_ptr tmp' ⋆ array (t := i32) lvl_ptr lvl ⋆
          array (t := i32) tpos_ptr tpos ⋆ R) m' → Q () m'

theorem m7SortTmpHeapSpec_of {tmp_ptr lvl_ptr tpos_ptr tlen : BitVec 64}
    {tmp lvl tpos : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post []} {X : XPost}
    (htlen : tlen.toNat ≤ tmp.length) (htlen60 : tlen.toNat < 2 ^ 60)
    (hbd : ∀ k, 1 ≤ k → k < tlen.toNat →
      (tmp[k]?.getD 0#32).toNat / 2 < lvl.length ∧
      (tmp[k]?.getD 0#32).toNat / 2 < tpos.length)
    (hm : (array (t := i32) tmp_ptr tmp ⋆ array (t := i32) lvl_ptr lvl ⋆
      array (t := i32) tpos_ptr tpos ⋆ R) m)
    (hQ : ∀ tmp' m', tmp'.length = tmp.length →
      (tmp'.take tlen.toNat).Perm (tmp.take tlen.toNat) →
      (0 < tlen.toNat → tmp'[0]? = tmp[0]?) →
      (∀ k, tlen.toNat ≤ k → tmp'[k]? = tmp[k]?) →
      Full.FullSortSliceEq tmp' tmp tlen.toNat →
      (∀ i j, 1 ≤ i → i ≤ j → j < tlen.toNat →
        Full.fullTmpLe lvl tpos (tmp'[i]?.getD 0#32) (tmp'[j]?.getD 0#32)) →
      (array (t := i32) tmp_ptr tmp' ⋆ array (t := i32) lvl_ptr lvl ⋆
        array (t := i32) tpos_ptr tpos ⋆ R) m' → Q () m') :
    m7SortTmpHeapSpec (tmp_ptr, lvl_ptr, tpos_ptr, tlen, ()) m Q X :=
  ⟨tmp, lvl, tpos, R, htlen, htlen60, hbd, hm, hQ⟩

theorem m7SortTmpHeapSpec_elim {a : Tup Val [i64, i64, i64, i64]} {m : Mem 64}
    {Q : Post []} {X : XPost} (h : m7SortTmpHeapSpec a m Q X) :
    ∃ (tmp lvl tpos : List (BitVec 32)) (R : Mem 64 → Prop),
      a.2.2.2.1.toNat ≤ tmp.length ∧ a.2.2.2.1.toNat < 2 ^ 60 ∧
      (∀ k, 1 ≤ k → k < a.2.2.2.1.toNat →
        (tmp[k]?.getD 0#32).toNat / 2 < lvl.length ∧
        (tmp[k]?.getD 0#32).toNat / 2 < tpos.length) ∧
      (array (t := i32) a.1 tmp ⋆ array (t := i32) a.2.1 lvl ⋆
        array (t := i32) a.2.2.1 tpos ⋆ R) m ∧
      ∀ tmp' m',
        tmp'.length = tmp.length →
        (tmp'.take a.2.2.2.1.toNat).Perm (tmp.take a.2.2.2.1.toNat) →
        (0 < a.2.2.2.1.toNat → tmp'[0]? = tmp[0]?) →
        (∀ k, a.2.2.2.1.toNat ≤ k → tmp'[k]? = tmp[k]?) →
        Full.FullSortSliceEq tmp' tmp a.2.2.2.1.toNat →
        (∀ i j, 1 ≤ i → i ≤ j → j < a.2.2.2.1.toNat →
          Full.fullTmpLe lvl tpos (tmp'[i]?.getD 0#32) (tmp'[j]?.getD 0#32)) →
        (array (t := i32) a.1 tmp' ⋆ array (t := i32) a.2.1 lvl ⋆
          array (t := i32) a.2.2.1 tpos ⋆ R) m' → Q () m' :=
  h

theorem m7SortTmpHeapSpec_monoX {a : Tup Val [i64, i64, i64, i64]} {m : Mem 64}
    {Q : Post []} {X₁ X₂ : XPost} (h : m7SortTmpHeapSpec a m Q X₁) :
    m7SortTmpHeapSpec a m Q X₂ := h

/-- Wave-4G `sort_deduced_clause` contract (`full_sort_tmp_m7`). Strengthens `Full.fullSortTmpSpec`
with exact `(level, trail_pos)` `fullTmpLe` order while isolating scratch mutation strictly to
idle `wsort` when `17 ≤ tmp_len` (leaving `work_stk2` and all other scratch unchanged). -/
def m7SortTmpSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ s.core.tmp_len ≤ c.max_vars ∧
    (∀ k, 1 ≤ k → k < s.core.tmp_len → (s.core.tmp[k]?.getD 0#32).toNat < 2 * c.max_vars) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ tmp' wsort' m',
      let s' : FullState :=
        { core := { s.core with tmp := tmp' }
          scratch := { s.scratch with wsort := wsort' } }
      s'.LengthsOk c →
      tmp'.length = c.max_vars →
      (s.core.tmp_len ≤ 16 → wsort' = s.scratch.wsort) →
      (tmp'.take s.core.tmp_len).Perm (s.core.tmp.take s.core.tmp_len) →
      (0 < s.core.tmp_len → tmp'[0]? = s.core.tmp[0]?) →
      (∀ j, 1 ≤ j → j < s.core.tmp_len →
        ∃ i, 1 ≤ i ∧ i < s.core.tmp_len ∧ tmp'[j]? = s.core.tmp[i]?) →
      (∀ i, 1 ≤ i → i < s.core.tmp_len →
        ∃ j, 1 ≤ j ∧ j < s.core.tmp_len ∧ s.core.tmp[i]? = tmp'[j]?) →
      (∀ i j, 1 ≤ i → i ≤ j → j < s.core.tmp_len →
        Full.fullTmpLe s.core.lvl s.core.trail_pos
          (tmp'[i]?.getD 0#32) (tmp'[j]?.getD 0#32)) →
      (∀ i j, 1 ≤ i → i ≤ j → j < s.core.tmp_len →
        (s.core.lvl[(tmp'[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
        (s.core.lvl[(tmp'[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
      Full.FullExtScratchPres s s' →
      (FullMem c s' ⋆ R) m' → Q () m'

theorem m7SortTmpSpec_of {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post []} {X : XPost} (hlen : s.LengthsOk c) (htl : s.core.tmp_len ≤ c.max_vars)
    (hbd : ∀ k, 1 ≤ k → k < s.core.tmp_len →
      (s.core.tmp[k]?.getD 0#32).toNat < 2 * c.max_vars)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ tmp' wsort' m',
      let s' : FullState :=
        { core := { s.core with tmp := tmp' }
          scratch := { s.scratch with wsort := wsort' } }
      s'.LengthsOk c → tmp'.length = c.max_vars →
      (s.core.tmp_len ≤ 16 → wsort' = s.scratch.wsort) →
      (tmp'.take s.core.tmp_len).Perm (s.core.tmp.take s.core.tmp_len) →
      (0 < s.core.tmp_len → tmp'[0]? = s.core.tmp[0]?) →
      (∀ j, 1 ≤ j → j < s.core.tmp_len →
        ∃ i, 1 ≤ i ∧ i < s.core.tmp_len ∧ tmp'[j]? = s.core.tmp[i]?) →
      (∀ i, 1 ≤ i → i < s.core.tmp_len →
        ∃ j, 1 ≤ j ∧ j < s.core.tmp_len ∧ s.core.tmp[i]? = tmp'[j]?) →
      (∀ i j, 1 ≤ i → i ≤ j → j < s.core.tmp_len →
        Full.fullTmpLe s.core.lvl s.core.trail_pos
          (tmp'[i]?.getD 0#32) (tmp'[j]?.getD 0#32)) →
      (∀ i j, 1 ≤ i → i ≤ j → j < s.core.tmp_len →
        (s.core.lvl[(tmp'[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
        (s.core.lvl[(tmp'[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
      Full.FullExtScratchPres s s' →
      (FullMem c s' ⋆ R) m' → Q () m') :
    m7SortTmpSpec (c.hdr, ()) m Q X :=
  ⟨c, s, R, rfl, hlen, htl, hbd, hm, hQ⟩

theorem m7SortTmpSpec_elim {a : Tup Val [i64]} {m : Mem 64} {Q : Post []} {X : XPost}
    (h : m7SortTmpSpec a m Q X) :
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      a.1 = c.hdr ∧ s.LengthsOk c ∧ s.core.tmp_len ≤ c.max_vars ∧
      (∀ k, 1 ≤ k → k < s.core.tmp_len → (s.core.tmp[k]?.getD 0#32).toNat < 2 * c.max_vars) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ tmp' wsort' m',
        let s' : FullState :=
          { core := { s.core with tmp := tmp' }
            scratch := { s.scratch with wsort := wsort' } }
        s'.LengthsOk c → tmp'.length = c.max_vars →
        (s.core.tmp_len ≤ 16 → wsort' = s.scratch.wsort) →
        (tmp'.take s.core.tmp_len).Perm (s.core.tmp.take s.core.tmp_len) →
        (0 < s.core.tmp_len → tmp'[0]? = s.core.tmp[0]?) →
        (∀ j, 1 ≤ j → j < s.core.tmp_len →
          ∃ i, 1 ≤ i ∧ i < s.core.tmp_len ∧ tmp'[j]? = s.core.tmp[i]?) →
        (∀ i, 1 ≤ i → i < s.core.tmp_len →
          ∃ j, 1 ≤ j ∧ j < s.core.tmp_len ∧ s.core.tmp[i]? = tmp'[j]?) →
        (∀ i j, 1 ≤ i → i ≤ j → j < s.core.tmp_len →
          Full.fullTmpLe s.core.lvl s.core.trail_pos
            (tmp'[i]?.getD 0#32) (tmp'[j]?.getD 0#32)) →
        (∀ i j, 1 ≤ i → i ≤ j → j < s.core.tmp_len →
          (s.core.lvl[(tmp'[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
          (s.core.lvl[(tmp'[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
        Full.FullExtScratchPres s s' →
        (FullMem c s' ⋆ R) m' → Q () m' :=
  h

theorem m7SortTmpSpec_monoX {a : Tup Val [i64]} {m : Mem 64} {Q : Post []} {X₁ X₂ : XPost}
    (h : m7SortTmpSpec a m Q X₁) : m7SortTmpSpec a m Q X₂ := h

theorem m7SortTmpSpec_preserves_work_stk2 (s : FullState) (tmp' wsort' : List (BitVec 32)) :
    ({ core := { s.core with tmp := tmp' }
       scratch := { s.scratch with wsort := wsort' } } : FullState).scratch.work_stk2 =
      s.scratch.work_stk2 := rfl

theorem fullLengthsOk_with_tmp_wsort {c : FullCfg} {s : FullState}
    {tmp' wsort' : List (BitVec 32)} (hl : s.LengthsOk c)
    (htmp : tmp'.length = c.max_vars) (hwsort : wsort'.length = 2 * c.max_vars) :
    ({ core := { s.core with tmp := tmp' }
       scratch := { s.scratch with wsort := wsort' } } : FullState).LengthsOk c :=
  ⟨{ hl.core_ok with tmp_len_arr := htmp }, { hl.scratch_ok with wsort_len := hwsort }⟩

theorem fullLitMarksClear_with_tmp_wsort {c : FullCfg} {s : FullState}
    {tmp' wsort' : List (BitVec 32)} (h : Full.FullLitMarksClear c s) :
    Full.FullLitMarksClear c
      { core := { s.core with tmp := tmp' }, scratch := { s.scratch with wsort := wsort' } } :=
  h

theorem fullMinMarkInv_with_tmp {k : FullCoreState} {keep : List Nat}
    {tmp' : List (BitVec 32)} (h : Full.FullMinMarkInv k keep) :
    Full.FullMinMarkInv { k with tmp := tmp' } keep := by
  rcases h with ⟨a, b, c⟩
  refine ⟨a, b, fun idx hi => ?_⟩
  simpa [Full.fullArenaClauseRefsCore, Full.fullArenaClauseGarbCore,
    Full.fullArenaClauseLitsCore, Full.fullArenaClauseSizeCore, Full.fullArenaHdrCore]
    using c idx hi

theorem fullOtfsWitnessInv_with_tmp {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} {tmp' : List (BitVec 32)} (h : Full.FullOtfsWitnessInv c F0 F_cur k) :
    Full.FullOtfsWitnessInv c F0 F_cur { k with tmp := tmp' } :=
  { h with
    arena := { h.arena with len_ok := h.arena.len_ok }
    watches := h.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }

theorem fullWitnessInv_with_tmp {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} {tmp' : List (BitVec 32)} (h : Full.FullWitnessInv c F0 F_cur k) :
    Full.FullWitnessInv c F0 F_cur { k with tmp := tmp' } :=
  { h with
    arena := { h.arena with len_ok := h.arena.len_ok }
    watches := h.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }

theorem fullOtfsInvW_with_tmp_wsort {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {tmp' wsort' : List (BitVec 32)} (h : Full.FullOtfsInvW c F0 F_cur s)
    (htmp : tmp'.length = c.max_vars) (hwsort : wsort'.length = 2 * c.max_vars) :
    Full.FullOtfsInvW c F0 F_cur
      { core := { s.core with tmp := tmp' }, scratch := { s.scratch with wsort := wsort' } } :=
  ⟨fullLengthsOk_with_tmp_wsort h.1 htmp hwsort, fullOtfsWitnessInv_with_tmp h.2.1,
    h.2.2.1, by
      unfold Full.FullArenaVarsNodup Full.fullArenaClauseRefs Full.fullArenaClauseRefsCore
        Full.fullArenaClauseGarb Full.fullArenaClauseGarbCore Full.fullArenaHdrCore
        Full.fullArenaClauseLits Full.fullArenaClauseLitsCore Full.fullArenaClauseSizeCore at *
      exact h.2.2.2.1,
    ⟨fun i hi => by
      have hll := h.2.2.2.2.1.1 i hi
      dsimp only [Full.fullArenaClauseRefs, Full.fullArenaClauseRefsCore] at hll ⊢
      exact hll,
      h.2.2.2.2.1.2⟩,
    h.2.2.2.2.2⟩

theorem fullSparseInvW_with_tmp_wsort {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {tmp' wsort' : List (BitVec 32)} (h : Full.FullSparseInvW c F0 F_cur s)
    (htmp : tmp'.length = c.max_vars) (hwsort : wsort'.length = 2 * c.max_vars) :
    Full.FullSparseInvW c F0 F_cur
      { core := { s.core with tmp := tmp' }, scratch := { s.scratch with wsort := wsort' } } :=
  ⟨fullLengthsOk_with_tmp_wsort h.1 htmp hwsort, fullWitnessInv_with_tmp h.2.1,
    h.2.2.1, by
      unfold Full.FullArenaVarsNodup Full.fullArenaClauseRefs Full.fullArenaClauseRefsCore
        Full.fullArenaClauseGarb Full.fullArenaClauseGarbCore Full.fullArenaHdrCore
        Full.fullArenaClauseLits Full.fullArenaClauseLitsCore Full.fullArenaClauseSizeCore at *
      exact h.2.2.2.1,
    ⟨fun i hi => by
      have hll := h.2.2.2.2.1.1 i hi
      dsimp only [Full.fullArenaClauseRefs, Full.fullArenaClauseRefsCore] at hll ⊢
      exact hll,
      h.2.2.2.2.1.2⟩,
    h.2.2.2.2.2⟩

theorem m7SortTmpSpec_of_small {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post []} {X : XPost} (hlen : s.LengthsOk c) (htl : s.core.tmp_len ≤ c.max_vars)
    (h16 : s.core.tmp_len ≤ 16)
    (hbd : ∀ k, 1 ≤ k → k < s.core.tmp_len →
      (s.core.tmp[k]?.getD 0#32).toNat < 2 * c.max_vars)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ tmp' m', tmp'.length = c.max_vars →
      (tmp'.take s.core.tmp_len).Perm (s.core.tmp.take s.core.tmp_len) →
      (0 < s.core.tmp_len → tmp'[0]? = s.core.tmp[0]?) →
      (∀ j, 1 ≤ j → j < s.core.tmp_len →
        ∃ i, 1 ≤ i ∧ i < s.core.tmp_len ∧ tmp'[j]? = s.core.tmp[i]?) →
      (∀ i, 1 ≤ i → i < s.core.tmp_len →
        ∃ j, 1 ≤ j ∧ j < s.core.tmp_len ∧ s.core.tmp[i]? = tmp'[j]?) →
      (∀ i j, 1 ≤ i → i ≤ j → j < s.core.tmp_len →
        (s.core.lvl[(tmp'[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
        (s.core.lvl[(tmp'[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
      (FullMem c { s with core := { s.core with tmp := tmp' } } ⋆ R) m' → Q () m') :
    m7SortTmpSpec (c.hdr, ()) m Q X := by
  refine m7SortTmpSpec_of hlen htl hbd hm ?_
  intro tmp' wsort' m' _ _ hlen_t hw_le16 hp h0 hji hij _ hlvl _ hm'
  have hw_eq : wsort' = s.scratch.wsort := hw_le16 h16
  have hs_eq : ({ core := { s.core with tmp := tmp' }
                  scratch := { s.scratch with wsort := wsort' } } : FullState) =
      { s with core := { s.core with tmp := tmp' } } := by
    cases s; simp [hw_eq]
  exact hQ tmp' m' hlen_t hp h0 hji hij hlvl (hs_eq ▸ hm')

theorem m7SortTmpSpec_of_canonical_small {a : Tup Val [i64]} {m : Mem 64} {Q : Post []}
    {X : XPost} (h : Full.fullSortTmpSpec a m Q X)
    (h16 : ∀ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      a.1 = c.hdr → s.LengthsOk c → (FullMem c s ⋆ R) m → s.core.tmp_len ≤ 16) :
    m7SortTmpSpec a m Q X := by
  rcases a with ⟨hdr, ⟨⟩⟩
  rcases h with ⟨c, s, R, rfl, hlen, htl, hbd, hm, hQ⟩
  exact m7SortTmpSpec_of_small hlen htl (h16 c s R rfl hlen hm) hbd hm hQ

/-- Witness helper showing `fullTmpLe` implies non-decreasing `level`. -/
theorem fullTmpLe_lvl_le {lvl tpos : List (BitVec 32)} {a b : BitVec 32}
    (h : Full.fullTmpLe lvl tpos a b) :
    (lvl[a.toNat / 2]?.getD 0#32).toNat ≤ (lvl[b.toNat / 2]?.getD 0#32).toNat := by
  unfold Full.fullTmpLe Full.fullTmpLt Full.fullTmpKey at h
  simp only at h
  omega

/-- Pure read-only spec for Q16 base-10 logarithm helper `full_log10_q16_m7`
(`= FullM5Sched.m5Log10Q16Spec`). -/
def m7Log10Q16Spec : Spec [i64] [i64] := fun (n, ()) m Q _ =>
  ∀ r : BitVec 64, r.toNat < 20 * 65536 → (10 ≤ n.toNat → 65536 ≤ r.toNat) → Q (r, ()) m

theorem m7Log10Q16Spec_of {n : BitVec 64} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hQ : ∀ r : BitVec 64, r.toNat < 20 * 65536 → (10 ≤ n.toNat → 65536 ≤ r.toNat) →
      Q (r, ()) m) :
    m7Log10Q16Spec (n, ()) m Q X := hQ

theorem m7Log10Q16Spec_elim {a : Tup Val [i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : m7Log10Q16Spec a m Q X) :
    ∀ r : BitVec 64, r.toNat < 20 * 65536 → (10 ≤ a.1.toNat → 65536 ≤ r.toNat) → Q (r, ()) m :=
  h

theorem m7Log10Q16Spec_monoX {a : Tup Val [i64]} {m : Mem 64} {Q : Post [i64]} {X₁ X₂ : XPost}
    (h : m7Log10Q16Spec a m Q X₁) : m7Log10Q16Spec a m Q X₂ := h

theorem m7Log10Q16Spec_eq_m5 : m7Log10Q16Spec = FullM5Sched.m5Log10Q16Spec := by
  funext x m Q X; cases x; rfl

/-- Bridge from `FullM5Sched.m5RephaseSpec` (`= FullM6Tiers.m6RephaseSpec`) to
`Full.fullRephaseSpec` when in focused/stable mode. -/
theorem m7RephaseSpec_of_stable (h : BitVec 64) (m : Mem 64) (Q : Post []) (X : XPost)
    (hc : ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.scratch.stable ≠ 0#64 ∧ FullCoreInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
      ∀ vals' lvl' rsns' trl' tp' te' prop' unass' fuel' sc' m',
        let s' : FullState :=
          { core := { s.core with vals := vals', lvl := lvl', rsns := rsns', trl := trl',
                                  trail_pos := tp', trail_end := te', propagated := prop',
                                  cur_level := 0, unassigned := unass', fuel := fuel' }
            scratch := sc' }
        FullCoreInv c F0 s' → fuel'.toNat ≤ s.core.fuel.toNat →
        Full.FullExtScratchPres s s' → (FullMem c s' ⋆ R) m' → Q () m') :
    FullM5Sched.m5RephaseSpec (h, ()) m Q X :=
  FullM5Sched.m5RephaseSpec_of_stable hc

/-! ## 2. Shared Array, BitVector, List & Sift Helpers -/

theorem m7_arr_load_i32 {a i : BitVec 64} {xs : List (BitVec 32)} {F : Mem 64 → Prop}
    {m : Mem 64} (hi : i.toNat < xs.length) (h : (array (t := i32) a xs ⋆ F) m) :
    loadVal m i32 (a + i * 4) = some xs[i.toNat] := by
  rw [show a + i * 4 = a + BitVec.ofNat 64 (4 * i.toNat) from by
    rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]]
  exact loadVal_array (t := i32) (by decide) hi h

theorem m7_arr_store_i32 {a i : BitVec 64} {xs : List (BitVec 32)} {F : Mem 64 → Prop}
    {m : Mem 64} (v : BitVec 32) (hi : i.toNat < xs.length)
    (h : (array (t := i32) a xs ⋆ F) m) :
    storeOk m i32 (a + i * 4) ∧
      (array (t := i32) a (xs.set i.toNat v) ⋆ F) (storeMem m i32 (a + i * 4) v) := by
  rw [show a + i * 4 = a + BitVec.ofNat 64 (4 * i.toNat) from by
    rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]]
  exact store_array (t := i32) v (by decide) hi h

private theorem wp_let_udiv64_m7 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {a b : Arg Val i64} {k : Tup Val [i64] → Expr Val Cont rs}
    (hb : b.val ≠ 0#64) :
    wp Γ Q X (.let_ (Op.mk (.udiv 64) (a, b, ())) k) m ↔
      wp Γ Q X (k (a.val / b.val, ())) m := by
  rw [wp_let_udiv_eq]; exact ⟨fun h => h.2, fun h => ⟨hb, h⟩⟩

private theorem wp_let_udiv64_var_m7 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {a : Arg Val i64} {vb : BitVec 64} {k : Tup Val [i64] → Expr Val Cont rs}
    (hb : vb ≠ 0#64) :
    wp Γ Q X (.let_ (Op.mk (.udiv 64) (a, .var vb, ())) k) m ↔
      wp Γ Q X (k (a.val / vb, ())) m :=
  wp_let_udiv64_m7 hb

private theorem wp_let_udiv64_imm_m7 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {a : Arg Val i64} {ib : BitVec 64} {k : Tup Val [i64] → Expr Val Cont rs}
    (hb : ib ≠ 0#64) :
    wp Γ Q X (.let_ (Op.mk (.udiv 64) (a, .imm ib, ())) k) m ↔
      wp Γ Q X (k (a.val / ib, ())) m :=
  wp_let_udiv64_m7 hb

theorem m7_bv64_add1 {x : BitVec 64} (hx : x.toNat + 1 < 2 ^ 64) :
    (x + 1).toNat = x.toNat + 1 := by bv_omega

theorem m7_bv64_sub1 {x : BitVec 64} (hx : 1 ≤ x.toNat) :
    (x - 1).toNat = x.toNat - 1 := by bv_omega

theorem m7_bv64_sub {a b : BitVec 64} (h : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat := by bv_omega

theorem m7_bv64_add {a b : BitVec 64} (h : a.toNat + b.toNat < 2 ^ 64) :
    (a + b).toNat = a.toNat + b.toNat := by bv_omega

theorem m7_bv64_zext32_ushr1 (x : BitVec 32) :
    ((x.setWidth 64) >>> (BitVec.signExtend 64 (1 : BitVec 32)).toNat).toNat = x.toNat / 2 := by
  have h1 : (BitVec.signExtend 64 (1 : BitVec 32)).toNat = 1 := rfl
  rw [h1]; bv_omega

private theorem m7_perm_middle {α : Type _} (a : α) (l₁ l₂ : List α) :
    (l₁ ++ a :: l₂).Perm (a :: (l₁ ++ l₂)) := by
  induction l₁ with
  | nil => exact List.Perm.refl _
  | cons b bs ih =>
    simpa [List.cons_append] using (List.Perm.cons b ih).trans (List.Perm.swap a b _)

theorem m7_list_swap_perm {α : Type _} (xs : List α) {i j : Nat}
    (hij : i < j) (hj : j < xs.length) :
    ((xs.set i (xs[j]'hj)).set j (xs[i]'(by omega))).Perm xs := by
  have hi : i < xs.length := by omega
  have heq : xs = xs.take i ++ xs[i] ::
      ((xs.drop (i + 1)).take (j - i - 1) ++ xs[j] :: xs.drop (j + 1)) := by
    have hs1 := List.take_append_drop i xs
    have hd1 : xs.drop i = xs[i] :: xs.drop (i + 1) := List.drop_eq_getElem_cons hi
    have hj_d : j - i - 1 < (xs.drop (i + 1)).length := by simp; omega
    have hs2 := List.take_append_drop (j - i - 1) (xs.drop (i + 1))
    have hd2 : (xs.drop (i + 1)).drop (j - i - 1) =
        xs[j] :: xs.drop (j + 1) := by
      rw [List.drop_drop, show i + 1 + (j - i - 1) = j by omega]
      exact List.drop_eq_getElem_cons hj
    rw [← hs2, hd2] at hd1
    conv => lhs; rw [← hs1, hd1]
  have hsw : ((xs.set i (xs[j]'hj)).set j (xs[i]'hi)) =
      xs.take i ++ xs[j] ::
        ((xs.drop (i + 1)).take (j - i - 1) ++ xs[i] :: xs.drop (j + 1)) := by
    apply List.ext_getElem
    · simp; omega
    · intro k hk1 hk2
      have hmid_len : ((xs.drop (i + 1)).take (j - i - 1)).length = j - i - 1 := by
        simp; omega
      have hti_len : (xs.take i).length = i := by simp; omega
      by_cases hki : k < i
      · rw [List.getElem_set_ne (by omega), List.getElem_set_ne (by omega)]
        rw [List.getElem_append_left (by omega), List.getElem_take]
      · have hti_le : (xs.take i).length ≤ k := by rw [hti_len]; omega
        by_cases hkei : k = i
        · subst hkei
          rw [List.getElem_set_ne (by omega), List.getElem_set_self]
          simp only [List.getElem_append_right hti_le, hti_len, Nat.sub_self,
            List.getElem_cons_zero]
        · simp only [List.getElem_append_right hti_le, hti_len]
          rcases Nat.exists_eq_succ_of_ne_zero (by omega : k - i ≠ 0) with ⟨d0, hd0⟩
          simp only [hd0, List.getElem_cons_succ]
          by_cases hkj : k = j
          · subst k
            rw [List.getElem_set_self]
            have hmid_le : ((xs.drop (i + 1)).take (j - i - 1)).length ≤ d0 := by
              rw [hmid_len]; omega
            have h0 : d0 - (j - i - 1) = 0 := by omega
            simp only [List.getElem_append_right hmid_le, hmid_len, h0, List.getElem_cons_zero]
          · rw [List.getElem_set_ne (Ne.symm hkj), List.getElem_set_ne (Ne.symm hkei)]
            by_cases hk_lt_j : k < j
            · have hmid_lt : d0 < ((xs.drop (i + 1)).take (j - i - 1)).length := by
                rw [hmid_len]; omega
              simp only [List.getElem_append_left hmid_lt, List.getElem_take, List.getElem_drop]
              congr 1; omega
            · have hmid_le : ((xs.drop (i + 1)).take (j - i - 1)).length ≤ d0 := by
                rw [hmid_len]; omega
              have hk_sub : d0 - (j - i - 1) = k - j := by omega
              simp only [List.getElem_append_right hmid_le, hmid_len, hk_sub]
              rcases Nat.exists_eq_succ_of_ne_zero (by omega : k - j ≠ 0) with ⟨d, hd⟩
              simp only [hd, List.getElem_cons_succ, List.getElem_drop]
              congr 1; omega
  rw [hsw]
  conv => rhs; rw [heq]
  apply List.Perm.append_left
  let mid := (xs.drop (i + 1)).take (j - i - 1)
  have hp1 : (xs[j]'hj :: (mid ++ xs[i]'hi :: xs.drop (j + 1))).Perm
      (xs[j]'hj :: xs[i]'hi :: (mid ++ xs.drop (j + 1))) :=
    List.Perm.cons _ (m7_perm_middle (xs[i]'hi) mid (xs.drop (j + 1)))
  have hp2 : (xs[j]'hj :: xs[i]'hi :: (mid ++ xs.drop (j + 1))).Perm
      (xs[i]'hi :: xs[j]'hj :: (mid ++ xs.drop (j + 1))) :=
    List.Perm.swap _ _ _
  have hp3 : (xs[i]'hi :: xs[j]'hj :: (mid ++ xs.drop (j + 1))).Perm
      (xs[i]'hi :: (mid ++ xs[j]'hj :: xs.drop (j + 1))) :=
    List.Perm.cons _ (m7_perm_middle (xs[j]'hj) mid (xs.drop (j + 1))).symm
  simpa [mid, List.append_assoc] using (hp1.trans hp2).trans hp3

private theorem m7_list_swap_take {α : Type _} (xs : List α) {n i j : Nat}
    (hi : i < j) (hj : j < n) (hn : n ≤ xs.length) :
    let vi := xs[i]'(by omega)
    let vj := xs[j]'(by omega)
    (((xs.set i vj).set j vi).take n).Perm (xs.take n) := by
  intro vi vj
  have hij : ((xs.set i vj).set j vi).take n =
      (((xs.take n).set i vj).set j vi) := by
    rw [List.take_set, List.take_set]
  rw [hij]
  have hvi : (xs.take n)[i]'(by simp; omega) = vi := List.getElem_take
  have hvj : (xs.take n)[j]'(by simp; omega) = vj := List.getElem_take
  simpa [hvi, hvj] using
    m7_list_swap_perm (xs.take n) (i := i) (j := j) hi (by simp; omega)

private theorem m7_shift_set_perm {α : Type _} (xs : List α) {n j j' : Nat} (x : α)
    (hj' : j' < j) (hj : j < n) (hn : n ≤ xs.length) :
    (((xs.set j (xs[j']'(by omega))).set j' x).take n).Perm ((xs.set j x).take n) := by
  let ys := xs.set j x
  have hyl : ys.length = xs.length := by simp [ys]
  have hyj' : ys[j']'(by rw [hyl]; omega) = xs[j']'(by omega) := by
    dsimp [ys]; rw [List.getElem_set_ne (Nat.ne_of_gt hj')]
  have hys_j : ys[j]'(by rw [hyl]; omega) = x := by
    dsimp [ys]; rw [List.getElem_set_self]
  have heq : (xs.set j (xs[j']'(by omega))).set j' x =
      (ys.set j' (ys[j]'(by rw [hyl]; omega))).set j (ys[j']'(by rw [hyl]; omega)) := by
    apply List.ext_getElem
    · simp [ys]
    · intro k hk1 hk2
      by_cases hkj' : k = j'
      · subst hkj'
        rw [List.getElem_set_self, List.getElem_set_ne (Nat.ne_of_gt hj'),
          List.getElem_set_self, hys_j]
      · by_cases hkj : k = j
        · subst hkj
          rw [List.getElem_set_ne (Nat.ne_of_lt hj'), List.getElem_set_self,
            List.getElem_set_self, hyj']
        · rw [List.getElem_set_ne (Ne.symm hkj'), List.getElem_set_ne (Ne.symm hkj),
            List.getElem_set_ne (Ne.symm hkj), List.getElem_set_ne (Ne.symm hkj')]
          dsimp [ys]; rw [List.getElem_set_ne (Ne.symm hkj)]
  rw [heq]
  exact m7_list_swap_take ys hj' hj (by rw [hyl]; exact hn)

/-! ## 3. Knuth Shellsort Proof (`full_sort_u32_m7_wp`) -/

private inductive GapPos : Nat → Prop
  | one : GapPos 1
  | step {g : Nat} : GapPos g → GapPos (3 * g + 1)

private theorem gapPos_pos {g : Nat} (h : GapPos g) : 1 ≤ g := by
  cases h with
  | one => exact le_refl _
  | step _ => omega

private theorem perm_swap2_u32 (arr : List (BitVec 32)) (h2 : 2 ≤ arr.length) :
    let a := arr[0]'(by omega)
    let b := arr[1]'(by omega)
    (((arr.set 0 b).set 1 a).take 2).Perm (arr.take 2) :=
  m7_list_swap_take arr (by decide) (by decide) h2

private theorem sortedU32_of_one {arr : List (BitVec 32)} {n : Nat} (hn : n ≤ 1) :
    M7SortedU32 arr n := fun i j hij hj => by
  have hi0 : i = 0 := by omega
  have hj0 : j = 0 := by omega
  subst hi0 hj0; exact le_refl _

private theorem sortedU32_swap2 {arr : List (BitVec 32)} (h2 : 2 ≤ arr.length)
    (hlt : (arr[1]'(by omega)).toNat < (arr[0]'(by omega)).toNat) :
    M7SortedU32 ((arr.set 0 (arr[1]'(by omega))).set 1 (arr[0]'(by omega))) 2 := by
  intro i j hij hj
  have h10 : ((arr.set 0 (arr[1]'(by omega))).set 1 (arr[0]'(by omega)))[0]? =
      some (arr[1]'(by omega)) := by
    rw [List.getElem?_set_ne (by decide), List.getElem?_set_self (by omega)]
  have h11 : ((arr.set 0 (arr[1]'(by omega))).set 1 (arr[0]'(by omega)))[1]? =
      some (arr[0]'(by omega)) := by
    rw [List.getElem?_set_self (by simp; omega)]
  rcases Nat.lt_or_eq_of_le (show j ≤ 1 by omega) with hj0 | hj1
  · have hi0 : i = 0 := by omega
    have hj0' : j = 0 := by omega
    subst hi0 hj0'; exact le_refl _
  · subst hj1
    rcases Nat.lt_or_eq_of_le (show i ≤ 1 by omega) with hi0 | hi1
    · have hi0' : i = 0 := by omega
      subst hi0'; rw [h10, h11]; exact Nat.le_of_lt hlt
    · subst hi1; exact le_refl _

private structure ShellInsInv (arr_i arr_j : List (BitVec 32))
    (n i j : Nat) (x : BitVec 32) (gap : Nat) (go : Bool) : Prop where
  len_eq : arr_j.length = arr_i.length
  perm_hole : ((arr_j.set j x).take n).Perm (arr_i.take n)
  suf_eq : ∀ k, n ≤ k → arr_j[k]? = arr_i[k]?
  j_le : j ≤ i
  gap_eq1_below : gap = 1 → ∀ a b, a ≤ b → b < j →
    (arr_j[a]?.getD 0#32).toNat ≤ (arr_j[b]?.getD 0#32).toNat
  gap_eq1_above : gap = 1 → ∀ a b, j < a → a ≤ b → b ≤ i →
    (arr_j[a]?.getD 0#32).toNat ≤ (arr_j[b]?.getD 0#32).toNat
  gap_eq1_cross : gap = 1 → ∀ a b, a < j → j < b → b ≤ i →
    (arr_j[a]?.getD 0#32).toNat ≤ (arr_j[b]?.getD 0#32).toNat
  gap_eq1_gt_x : gap = 1 → ∀ b, j < b → b ≤ i →
    x.toNat < (arr_j[b]?.getD 0#32).toNat
  gap_eq1_stop : gap = 1 → go = false → 0 < j →
    (arr_j[j - 1]?.getD 0#32).toNat ≤ x.toNat

private theorem shellInsInv_init {arr_i : List (BitVec 32)} {n i gap : Nat}
    (hi : i < n) (hn : n ≤ arr_i.length)
    (hsrt : gap = 1 → M7SortedU32 arr_i i) :
    ShellInsInv arr_i arr_i n i i (arr_i[i]'(by omega)) gap true := by
  refine ⟨rfl, ?_, fun _ _ => rfl, le_refl _, ?_, ?_, ?_, ?_, fun _ h => by cases h⟩
  · have hself : arr_i.set i (arr_i[i]'(by omega)) = arr_i := by
      apply List.ext_getElem (by simp)
      intro k hk1 hk2
      by_cases hki : k = i
      · subst hki; rw [List.getElem_set_self]
      · rw [List.getElem_set_ne (Ne.symm hki)]
    rw [hself]
  · intro hg a b hab hbi; exact (hsrt hg) a b hab hbi
  · intro _ a b ha hab hbi; omega
  · intro _ a b ha hjb hbi; omega
  · intro _ b hjb hbi; omega

private theorem shellInsInv_shift {arr_i arr_j : List (BitVec 32)}
    {n i j gap : Nat} {x : BitVec 32} (hinv : ShellInsInv arr_i arr_j n i j x gap true)
    (hj_ge : gap ≤ j) (hgap_pos : 1 ≤ gap) (hi : i < n) (hn : n ≤ arr_i.length)
    (hprev : x.toNat < (arr_j[j - gap]'(by have := hinv.j_le; rw [hinv.len_eq]; omega)).toNat) :
    let prev := arr_j[j - gap]'(by have := hinv.j_le; rw [hinv.len_eq]; omega)
    ShellInsInv arr_i (arr_j.set j prev) n i (j - gap) x gap true := by
  intro prev
  have hjl : arr_j.length = arr_i.length := hinv.len_eq
  have hj_lt_n : j < n := Nat.lt_of_le_of_lt hinv.j_le hi
  have hj_gt : j - gap < j := by omega
  have hperm : (((arr_j.set j prev).set (j - gap) x).take n).Perm (arr_i.take n) :=
    (m7_shift_set_perm arr_j x hj_gt hj_lt_n (by omega)).trans hinv.perm_hole
  refine ⟨by simp [hjl], hperm, fun k hk => ?_, Nat.le_trans (Nat.sub_le _ _) hinv.j_le,
    ?_, ?_, ?_, ?_, fun _ h => by cases h⟩
  · rw [List.getElem?_set_ne (by omega)]; exact hinv.suf_eq k hk
  · intro hg a b hab hbj
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    exact hinv.gap_eq1_below hg a b hab (by omega)
  · intro hg a b hja hab hbi
    subst hg
    have ha' : j ≤ a := by omega
    rcases Nat.lt_or_eq_of_le ha' with hja2 | rfl
    · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      exact hinv.gap_eq1_above rfl a b hja2 hab hbi
    · rw [List.getElem?_set_self (by rw [hjl]; omega)]
      rcases Nat.lt_or_eq_of_le hab with hj2b | rfl
      · rw [List.getElem?_set_ne (by omega)]
        have hp_get : prev = arr_j[j - 1]'(by have := hinv.j_le; rw [hjl]; omega) := rfl
        rw [hp_get]
        have hcross := hinv.gap_eq1_cross rfl (j - 1) b (by omega) hj2b hbi
        have hlt_jm1 : j - 1 < arr_j.length := by have := hinv.j_le; rw [hjl]; omega
        rw [List.getElem?_eq_getElem hlt_jm1] at hcross
        exact hcross
      · rw [List.getElem?_set_self (by rw [hjl]; omega)]; exact le_refl _
  · intro hg a b ha hjb hbi
    subst hg
    rw [List.getElem?_set_ne (by omega)]
    by_cases hbj : b = j
    · subst b
      rw [List.getElem?_set_self (by rw [hjl]; omega)]
      have hp_get : prev = arr_j[j - 1]'(by have := hinv.j_le; rw [hjl]; omega) := rfl
      rw [hp_get]
      have hbel := hinv.gap_eq1_below rfl a (j - 1) (by omega) (by omega)
      have hlt_jm1 : j - 1 < arr_j.length := by have := hinv.j_le; rw [hjl]; omega
      rw [List.getElem?_eq_getElem hlt_jm1] at hbel
      exact hbel
    · rw [List.getElem?_set_ne (Ne.symm hbj)]
      exact hinv.gap_eq1_cross rfl a b (by omega) (by omega) hbi
  · intro hg b hjb hbi
    subst hg
    by_cases hbj : b = j
    · subst b
      rw [List.getElem?_set_self (by rw [hjl]; omega)]
      exact hprev
    · rw [List.getElem?_set_ne (Ne.symm hbj)]
      exact hinv.gap_eq1_gt_x rfl b (by omega) hbi

private theorem shellInsInv_finish_sorted {arr_i arr_j : List (BitVec 32)}
    {n i j : Nat} {x : BitVec 32} (hinv : ShellInsInv arr_i arr_j n i j x 1 false)
    (hn : n ≤ arr_i.length) (hi : i < n) :
    M7SortedU32 (arr_j.set j x) (i + 1) := by
  intro a b hab hbi
  have hjl : arr_j.length = arr_i.length := hinv.len_eq
  have hj_lt : j < arr_j.length := by have := hinv.j_le; omega
  by_cases haj : a = j
  · subst a
    by_cases hbj : b = j
    · subst b; exact le_refl _
    · rw [List.getElem?_set_self hj_lt, List.getElem?_set_ne (Ne.symm hbj)]
      exact Nat.le_of_lt (hinv.gap_eq1_gt_x rfl b (by omega) (by omega))
  · rw [List.getElem?_set_ne (Ne.symm haj)]
    by_cases hbj : b = j
    · subst b
      rw [List.getElem?_set_self hj_lt]
      have hj0 : 0 < j := by omega
      have h1 := hinv.gap_eq1_below rfl a (j - 1) (by omega) (by omega)
      have h2 := hinv.gap_eq1_stop rfl rfl hj0
      exact Nat.le_trans h1 h2
    · rw [List.getElem?_set_ne (Ne.symm hbj)]
      by_cases ha_lt : a < j
      · by_cases hb_lt : b < j
        · exact hinv.gap_eq1_below rfl a b hab hb_lt
        · exact hinv.gap_eq1_cross rfl a b ha_lt (by omega) (by omega)
      · exact hinv.gap_eq1_above rfl a b (by omega) hab (by omega)

theorem full_sort_u32_m7_wp (Γ : Env) :
    ∀ args m Q X, m7SortU32SortedSpec args m Q X →
      Func.wp Γ full_sort_u32_m7_body args m Q X := by
  rintro ⟨arr_ptr, n, ⟨⟩⟩ m0 Q X ⟨arr, R, hlen, hm0, hQ⟩
  unfold Func.wp full_sort_u32_m7_body
  have hlen32 : n.toNat < 2 ^ 32 := n.isLt
  have hn64 : (n.setWidth 64).toNat = n.toNat := by bv_omega
  c0_hsteps_nogrp
  · have hn1 : n.toNat ≤ 1 := by c0_cond hc; bv_omega
    exact hQ arr m0 rfl (List.Perm.refl _) (fun _ _ => rfl) (sortedU32_of_one hn1) hm0
  · have hn2 : n.toNat = 2 := by bv_omega
    have ha0 : 0 < arr.length := by omega
    have ha1 : 1 < arr.length := by omega
    have h0' := m7_arr_load_i32 (a := arr_ptr) (i := 0#64) ha0 hm0
    have h1' := m7_arr_load_i32 (a := arr_ptr) (i := 1#64) ha1 hm0
    c0_hsteps_nogrp
    refine wp_join_group (ts := []) (fun () m1 => Q () m1) ?_ ?_
    · rintro _ ⟨⟩ m1 hm1; c0_steps; exact hm1
    · intro Js hJs
      c0_hsteps_nogrp
      · have hgt : (arr[1]'ha1).toNat < (arr[0]'ha0).toNat := by
          c0_cond hc
          try simp only [show (0#64).toNat = 0 from rfl, show (1#64).toNat = 1 from rfl] at hc
          bv_omega
        let arr' := (arr.set 0 (arr[1]'ha1)).set 1 (arr[0]'ha0)
        refine hJs () _ (hQ arr' _ (by simp [arr']) ?_ (fun k hk => ?_) (by
          rw [hn2]; exact sortedU32_swap2 (by omega) hgt) (by
            simpa [arr', show (0#64).toNat = 0 from rfl, show (1#64).toNat = 1 from rfl] using hm))
        · rw [hn2]; exact perm_swap2_u32 arr (by omega)
        · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      · have hle : (arr[0]'ha0).toNat ≤ (arr[1]'ha1).toNat := by
          c0_cond hc
          have hc' : ¬ (arr[1]'ha1).toNat < (arr[0]'ha0).toNat := hc
          omega
        refine hJs () m0 (hQ arr m0 rfl (List.Perm.refl _) (fun _ _ => rfl) ?_ hm0)
        intro i j hij hj
        rw [hn2] at hj
        rcases Nat.lt_or_eq_of_le (show j ≤ 1 by omega) with hj0 | rfl
        · have : i = 0 := by omega
          have : j = 0 := by omega
          subst i j; exact le_refl _
        · rcases Nat.lt_or_eq_of_le (show i ≤ 1 by omega) with hi0 | rfl
          · have : i = 0 := by omega
            subst i; simp [List.getElem?_eq_getElem ha0, List.getElem?_eq_getElem ha1, hle]
          · exact le_refl _
  · have hn_ge3 : 3 ≤ n.toNat := by
      have hn_nle1 : ¬ n.toNat ≤ 1 := by c0_cond hc; bv_omega
      have hn_ne2 : n.toNat ≠ 2 := by c0_cond hc; bv_omega
      omega
    refine wp_join_group (ts := [i64])
      (fun (gap0, ()) m1 => m1 = m0 ∧ GapPos gap0.toNat ∧ gap0.toNat ≤ n.toNat)
      ?_ ?_
    · rintro _ ⟨gap0, ⟨⟩⟩ m1 ⟨hm1_eq, hgp0, hgle0⟩
      refine wp_loop_inv
        (fun (gap, ()) m1 =>
          ∃ arr1 : List (BitVec 32), arr1.length = arr.length ∧
            (arr1.take n.toNat).Perm (arr.take n.toNat) ∧
            (∀ k, n.toNat ≤ k → arr1[k]? = arr[k]?) ∧
            ((gap = 0#64 ∧ M7SortedU32 arr1 n.toNat) ∨
              (1 ≤ gap.toNat ∧ GapPos gap.toNat ∧ gap.toNat ≤ n.toNat)) ∧
            (array (t := i32) arr_ptr arr1 ⋆ R) m1)
        (fun (gap, ()) _ => gap.toNat)
        (fun J hJ => by
          c0_steps
          exact hJ (gap0, ()) m1 ⟨arr, rfl, List.Perm.refl _, fun _ _ => rfl,
            Or.inr ⟨gapPos_pos hgp0, hgp0, hgle0⟩, hm1_eq ▸ hm0⟩)
        (fun J (gap, ()) m1 ⟨arr1, hlen1, hperm1, hsuf1, hgap_st, hm1⟩ ih => ?_)
      c0_hsteps_nogrp
      · have hg_pos : 1 ≤ gap.toNat := by c0_cond hc; bv_omega
        rcases hgap_st with ⟨rfl, _⟩ | ⟨_, hgp, hgle⟩
        · simp at hg_pos
        · refine wp_loop_inv
            (fun (i, ()) m2 =>
              ∃ arr2 : List (BitVec 32),
                gap.toNat ≤ i.toNat ∧ i.toNat ≤ n.toNat ∧ arr2.length = arr.length ∧
                (arr2.take n.toNat).Perm (arr.take n.toNat) ∧
                (∀ k, n.toNat ≤ k → arr2[k]? = arr[k]?) ∧
                (gap.toNat = 1 → M7SortedU32 arr2 i.toNat) ∧
                (array (t := i32) arr_ptr arr2 ⋆ R) m2)
            (fun (i, ()) _ => n.toNat - i.toNat)
            (fun Ji hJi => by
              c0_steps
              exact hJi (gap, ()) m1 ⟨arr1, le_refl _, hgle, hlen1, hperm1, hsuf1,
                fun hg1 => by rw [hg1]; exact sortedU32_of_one (le_refl _), hm1⟩)
            (fun Ji (i, ()) m2 ⟨arr2, hgi, hin, hlen2, hperm2, hsuf2, hsrt2, hm2⟩ ihi => ?_)
          clear hm1
          c0_hsteps_nogrp
          · have hilt : i.toNat < n.toNat := by c0_cond hc; bv_omega
            have hi_arr : i.toNat < arr2.length := by omega
            have hld_x := m7_arr_load_i32 hi_arr hm2
            let x := arr2[i.toNat]'hi_arr
            refine wp_loop_inv
              (fun (j, go, ()) mj =>
                ∃ arr_j : List (BitVec 32),
                  ShellInsInv arr2 arr_j n.toNat i.toNat j.toNat x gap.toNat go ∧
                  (array (t := i32) arr_ptr arr_j ⋆ R) mj)
              (fun (j, go, ()) _ => 2 * j.toNat + if go then 1 else 0)
              (fun Jj hJj => by
                c0_steps
                exact hJj (i, true, ()) m2
                  ⟨arr2, shellInsInv_init hilt (by omega) hsrt2, hm2⟩)
              (fun Jj (j, go, ()) mj ⟨arr_j, hinv_j, hmj⟩ ihj => ?_)
            clear hm2
            have hj_le_i : j.toNat ≤ i.toNat := hinv_j.j_le
            have hj_lt_n : j.toNat < n.toNat := Nat.lt_of_le_of_lt hj_le_i hilt
            have hjl : arr_j.length = arr.length := hinv_j.len_eq.trans hlen2
            have hj_arr : j.toNat < arr_j.length := by omega
            c0_hsteps_nogrp
            · have hgo_t : go = true := by c0_cond hc; exact hc
              subst hgo_t; clear hc
              c0_hsteps
              · have hlt_gap : j.toNat < gap.toNat := by c0_cond hc; bv_omega
                exact ihj (j, false, ()) mj (by simp)
                  ⟨arr_j, { hinv_j with gap_eq1_stop := (fun hg1 _ _ => by
                    exfalso; rw [hg1] at hlt_gap; omega) }, hmj⟩
              · have hge_gap : gap.toNat ≤ j.toNat := by
                  have : ¬ j.toNat < gap.toNat := by assumption
                  omega
                have hjg_lt : j.toNat - gap.toNat < arr_j.length := by omega
                have hidx : (2 ^ 64 - gap.toNat + j.toNat) % 2 ^ 64 = j.toNat - gap.toNat := by
                  omega
                have hle_px : (arr_j[j.toNat - gap.toNat]'hjg_lt).toNat ≤ x.toNat := by
                  simp only [hidx] at hc
                  exact hc
                exact ihj (j, false, ()) mj (by simp)
                  ⟨arr_j, { hinv_j with gap_eq1_stop := (fun hg1 _ _ => by
                    have hj1_lt : j.toNat - 1 < arr_j.length := by omega
                    rw [List.getElem?_eq_getElem hj1_lt, Option.getD_some]
                    simpa [hg1] using hle_px) }, hmj⟩
              · have hge_gap : gap.toNat ≤ j.toNat := by
                  have : ¬ j.toNat < gap.toNat := by assumption
                  omega
                have hjg_lt : j.toNat - gap.toNat < arr_j.length := by omega
                have hjg_nat : (j - gap).toNat = j.toNat - gap.toNat := m7_bv64_sub (by omega)
                have hidx : (2 ^ 64 - gap.toNat + j.toNat) % 2 ^ 64 = j.toNat - gap.toNat := by
                  omega
                have hgt_px : x.toNat < (arr_j[j.toNat - gap.toNat]'hjg_lt).toNat := by
                  simp only [hidx] at hc
                  change ¬ _ ≤ x.toNat at hc
                  omega
                have hinv' := shellInsInv_shift hinv_j hge_gap hg_pos hilt (by omega) hgt_px
                have hdec : 2 * (j - gap).toNat + 1 < 2 * j.toNat + 1 := by
                  rw [hjg_nat]; omega
                refine ihj (j - gap, true, ()) m hdec
                  ⟨arr_j.set j.toNat (arr_j[j.toNat - gap.toNat]'hjg_lt), ?_, ?_⟩
                · rw [hjg_nat]; exact hinv'
                · simpa only [hjg_nat] using hm
            · have hgo_f : go = false := by c0_cond hc; exact hc
              subst hgo_f
              let arr_next := arr_j.set j.toNat x
              have hl_next : arr_next.length = arr.length := by simp [arr_next, hjl]
              have hp_next : (arr_next.take n.toNat).Perm (arr.take n.toNat) :=
                hinv_j.perm_hole.trans hperm2
              have hs_next : ∀ k, n.toNat ≤ k → arr_next[k]? = arr[k]? := fun k hk => by
                dsimp [arr_next]
                rw [List.getElem?_set_ne (by omega)]
                exact (hinv_j.suf_eq k hk).trans (hsuf2 k hk)
              have hsrt_next : gap.toNat = 1 → M7SortedU32 arr_next (i.toNat + 1) := fun hg1 =>
                shellInsInv_finish_sorted (hg1 ▸ hinv_j) (by omega) hilt
              have hi1 : (i + 1#64).toNat = i.toNat + 1 := m7_bv64_add1 (by omega)
              refine ihi (i + 1#64, ()) _ (by simp only; rw [hi1]; omega)
                ⟨arr_next, by rw [hi1]; omega, by rw [hi1]; omega, hl_next, hp_next, hs_next,
                  fun hg1 => by rw [hi1]; exact hsrt_next hg1, hm⟩
          · have hi_ge : n.toNat ≤ i.toNat := by c0_cond hc; rw [← hn64]; bv_omega
            have hi_eq : i.toNat = n.toNat := Nat.le_antisymm hin hi_ge
            have hsrt_full : gap.toNat = 1 → M7SortedU32 arr2 n.toNat := fun hg1 => by
              rw [← hi_eq]; exact hsrt2 hg1
            have hdiv : (gap / 3#64).toNat = gap.toNat / 3 := by bv_omega
            have hdec : (gap / 3#64).toNat < gap.toNat := by rw [hdiv]; omega
            generalize hgn : gap.toNat = gn at hgp
            cases hgp with
            | one =>
              have hdiv0 : gap / 3#64 = 0#64 := by
                apply BitVec.eq_of_toNat_eq; rw [hdiv, hgn]; rfl
              exact ih (gap / 3#64, ()) _ hdec
                ⟨arr2, hlen2, hperm2, hsuf2, Or.inl ⟨hdiv0, hsrt_full hgn⟩, hm2⟩
            | step hgg =>
              rename_i g
              have hdiv_eq : (gap / 3#64).toNat = g := by rw [hdiv, hgn]; omega
              have hgg1 : 1 ≤ g := gapPos_pos hgg
              exact ih (gap / 3#64, ()) _ hdec ⟨arr2, hlen2, hperm2, hsuf2,
                Or.inr ⟨by rw [hdiv_eq]; exact hgg1, by rw [hdiv_eq]; exact hgg,
                  by rw [hdiv_eq]; omega⟩, hm2⟩
      · have hg0 : gap = 0#64 := by
          apply BitVec.eq_of_toNat_eq
          c0_cond hc; bv_omega
        rcases hgap_st with ⟨_, hsrt_all⟩ | ⟨hg1, _, _⟩
        · exact hQ arr1 m1 hlen1 hperm1 hsuf1 hsrt_all hm1
        · subst hg0; simp at hg1
    · intro J hJ
      c0_hsteps_nogrp
      · have hn_gt16 : 16 < n.toNat := by
          c0_cond hc; rw [← hn64]; bv_omega
        have hlim_eq : (n.setWidth 64 / 3#64).toNat = n.toNat / 3 := by
          rw [← hn64]; bv_omega
        refine wp_loop_inv
          (fun (gap, ()) m1 =>
            m1 = m0 ∧ GapPos gap.toNat ∧ gap.toNat ≤ n.toNat)
          (fun (gap, ()) _ => n.toNat - gap.toNat)
          (fun Jl hJl => by
            c0_steps
            exact hJl (1#64, ()) m0
              ⟨rfl, GapPos.one, by simp only [show (1#64).toNat = 1 from rfl]; omega⟩)
          (fun Jl (gap, ()) m1 ⟨hm1_eq, hgp, hgle⟩ ih => ?_)
        c0_hsteps_nogrp
        · have hlt_lim : gap.toNat < n.toNat / 3 := by c0_cond hc; rw [← hlim_eq]; bv_omega
          have h3p1 : (gap * 3#64 + 1#64).toNat = 3 * gap.toNat + 1 := by bv_omega
          have hgp1 := gapPos_pos hgp
          exact ih (gap * 3#64 + 1#64, ()) m1 (by dsimp only; rw [h3p1]; omega)
            ⟨hm1_eq, by rw [h3p1]; exact GapPos.step hgp, by rw [h3p1]; omega⟩
        · exact hJ (gap, ()) m1 ⟨hm1_eq, hgp, hgle⟩
      · exact hJ (1#64, ()) m0
          ⟨rfl, GapPos.one, by simp only [show (1#64).toNat = 1 from rfl]; omega⟩

theorem full_sort_u32_m7_canonical_wp (Γ : Env) :
    ∀ args m Q X, Full.fullSortU32Spec args m Q X →
      Func.wp Γ full_sort_u32_m7_body args m Q X :=
  fun _ _ _ _ h => full_sort_u32_m7_wp Γ _ _ _ _ (fullSortU32Spec_to_m7Sorted h)

/-! ## 4. Local `full_log10_q16_m7` & 6-Step Focused `full_rephase_m7` Proofs -/

open Lean Elab Tactic in
local elab "m7_to_div_or_ctrl" : tactic => do
  for _ in [:120] do
    let g ← getMainGoal
    let rawTy ← Lean.instantiateMVars (← g.getType)
    let ty := rawTy.consumeMData
    if rawTy.isMData then
      let g' ← g.change ty (checkDefEq := false)
      replaceMainGoal [g']
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 then
      let e := (ty.getArg! 4).headBeta
      if e.isAppOf ``LeanQbe.T.Expr.group || e.isAppOf ``LeanQbe.T.Expr.jnz then break
      let st ← saveState
      let isDiv ← try
        evalTactic (← `(tactic| refine wp_udiv_of ?_ ?_))
        pure true
      catch _ => pure false
      st.restore
      if isDiv then break
      let isRem ← try
        evalTactic (← `(tactic| refine wp_urem_of ?_ ?_))
        pure true
      catch _ => pure false
      st.restore
      if isRem then break
    if !(← LeanQbe.T.C0Step.stepOnce) then break

private theorem pow10_lt_64_m7 {d : Nat} (hd : d ≤ 18) : 10 ^ d < 2 ^ 64 :=
  Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) hd) (by decide)

theorem full_log10_q16_m7_wp (Γ : Env) :
    ∀ a m Q X, m7Log10Q16Spec a m Q X →
      Func.wp Γ full_log10_q16_m7_body a m Q X := by
  rintro ⟨n, ⟨⟩⟩ m0 Q X hQ
  unfold Func.wp full_log10_q16_m7_body
  c0_hsteps_nogrp
  · exact hQ 0#64 (by decide) (fun h10 => by bv_omega)
  · have hn2 : 2 ≤ n.toNat := by bv_omega
    refine wp_loop_inv
      (fun (d, p, ()) ml =>
        ml = m0 ∧ d.toNat ≤ 18 ∧ p.toNat = 10 ^ d.toNat ∧ p.toNat ≤ n.toNat)
      (fun (d, _, ()) _ => 18 - d.toNat)
      (fun J hJ => by
        c0_steps
        exact hJ (0#64, 1#64, ()) m0
          ⟨rfl, by decide, by decide, by rw [show (1#64).toNat = 1 from rfl]; omega⟩)
      (fun J (d, p, ()) ml ⟨hml0, hd18, hp_eq, hpn⟩ ih => ?_)
    subst ml
    c0_let_simp
    have hp_ub : p.toNat ≤ 1000000000000000000 :=
      hp_eq ▸ Nat.pow_le_pow_right (by decide) hd18
    have hp1 : 1 ≤ p.toNat := by rw [hp_eq]; exact Nat.one_le_pow _ 10 (by decide)
    have hspan_nat : ((9 : BitVec 64) * p).toNat = 9 * p.toNat := by bv_omega
    have hspan_nz : (9 : BitVec 64) * p ≠ 0#64 := by
      intro h0
      have ht := congrArg BitVec.toNat h0
      rw [hspan_nat] at ht
      change 9 * p.toNat = 0 at ht
      omega
    refine wp_join_group (ts := [])
      (fun () ml => ml = m0 ∧ d.toNat ≤ 18 ∧ p.toNat = 10 ^ d.toNat ∧ p.toNat ≤ n.toNat ∧
        (d.toNat < 18 → n.toNat < 10 * p.toNat) ∧ (10 ≤ n.toNat → 1 ≤ d.toNat))
      ?_ ?_
    · rintro _ ⟨⟩ ml1 ⟨hml1, hd18', hp_eq', hpn', hn_ub, h10_d⟩
      subst ml1
      c0_hsteps_nogrp
      refine wp_join_group (ts := [i64]) (fun (frac, ()) ml2 => ml2 = m0 ∧ frac.toNat < 65536)
        ?_ ?_
      · rintro _ ⟨frac, ⟨⟩⟩ ml2 ⟨hml2, hfr_lt⟩
        subst ml2; c0_hsteps
        have hdr : (d <<< 16).toNat = d.toNat * 65536 := by
          rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
            show d.toNat * 2 ^ 16 = d.toNat * 65536 from rfl, Nat.mod_eq_of_lt (by omega)]
        have hsum : (d <<< 16 + frac).toNat = d.toNat * 65536 + frac.toNat := by
          rw [BitVec.toNat_add, hdr, Nat.mod_eq_of_lt (by omega)]
        exact hQ _ (by rw [hsum]; omega) (fun h10 => by have := h10_d h10; rw [hsum]; omega)
      · intro _ hJf
        c0_hsplit
        · c0_hsplit
          · m7_to_div_or_ctrl
            rw [wp_let_udiv64_var_m7 hspan_nz]
            c0_hsteps
            have hdiv : ((n - p) <<< 16#64 / ((9 : BitVec 64) * p)).toNat =
                ((n - p) <<< 16).toNat / (9 * p.toNat) := by
              rw [BitVec.toNat_udiv, hspan_nat]; rfl
            have hfrac_lt : ((n - p) <<< 16#64 / ((9 : BitVec 64) * p)).toNat < 65536 := by
              rw [hdiv]
              by_cases hd13 : d.toNat ≤ 13
              · have hp13 : p.toNat ≤ 10 ^ 13 :=
                  hp_eq' ▸ Nat.pow_le_pow_right (by decide) hd13
                have hn_lt : n.toNat < 10 * p.toNat := hn_ub (by omega)
                have hnp_le : p ≤ n := BitVec.le_def.mpr hpn'
                have hnp_sub : (n - p).toNat = n.toNat - p.toNat := BitVec.toNat_sub_of_le hnp_le
                have hnp_lt : (n - p).toNat < 9 * p.toNat := by omega
                have h13 : 10 ^ 13 = 10000000000000 := by decide
                have hsh : ((n - p) <<< 16).toNat = (n - p).toNat * 65536 := by
                  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
                    show (n - p).toNat * 2 ^ 16 = (n - p).toNat * 65536 from rfl,
                    Nat.mod_eq_of_lt (by omega)]
                rw [hsh]
                exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm (9 * p.toNat) 65536]; omega)
              · have hp14 : 10 ^ 14 ≤ p.toNat :=
                  hp_eq' ▸ Nat.pow_le_pow_right (by decide) (by omega)
                have hnum : ((n - p) <<< 16).toNat < 2 ^ 64 := BitVec.isLt _
                have hmul : 2 ^ 64 ≤ (9 * p.toNat) * 65536 := by
                  have h14 : 10 ^ 14 = 100000000000000 := by decide
                  omega
                exact Nat.div_lt_of_lt_mul (lt_of_lt_of_le hnum hmul)
            exact hJf _ m0 ⟨rfl, hfrac_lt⟩
          · c0_hsteps; exact hJf _ m0 ⟨rfl, by decide⟩
        · c0_hsteps; exact hJf _ m0 ⟨rfl, by decide⟩
    · intro _ hJexit
      c0_hsplit
      · have hd_lt : d.toNat < 18 := by bv_omega
        m7_to_div_or_ctrl
        rw [wp_let_udiv64_imm_m7 (by decide : (10 : BitVec 64) ≠ 0#64)]
        c0_hsplit
        · simp only [Arg.val] at *
          have hp10_eq : p.toNat * 10 = 10 ^ (d.toNat + 1) := by
            rw [Nat.pow_succ, hp_eq]
          have hp10_lt64 : p.toNat * 10 < 2 ^ 64 :=
            hp10_eq ▸ pow10_lt_64_m7 (by omega)
          have hp10 : (p * 10#64).toNat = p.toNat * 10 := by
            rw [BitVec.toNat_mul, show (10#64).toNat = 10 from rfl,
              Nat.mod_eq_of_lt hp10_lt64]
          have hd1 : (d + 1#64).toNat = d.toNat + 1 := m7_bv64_add1 (by omega)
          have hpn1 : p.toNat * 10 ≤ n.toNat := by
            have hle_div : p.toNat ≤ n.toNat / 10 := by
              have hc' : p.toNat ≤ (n / 10#64).toNat := by bv_omega
              rwa [BitVec.toNat_udiv, show (10#64).toNat = 10 from rfl] at hc'
            exact Nat.le_trans (Nat.mul_le_mul_right 10 hle_div) (Nat.div_mul_le_self n.toNat 10)
          c0_hsteps
          exact ih (d + 1#64, p * 10#64, ()) m0 (by simp only; omega)
            ⟨rfl, by rw [hd1]; omega, by rw [hd1, hp10, hp10_eq], by rw [hp10]; exact hpn1⟩
        · simp only [Arg.val] at *
          have hn_lt : n.toNat < 10 * p.toNat := by
            have hgt : n.toNat / 10 < p.toNat := by
              have hc' : (n / 10#64).toNat < p.toNat := by bv_omega
              rwa [BitVec.toNat_udiv, show (10#64).toNat = 10 from rfl] at hc'
            omega
          have h10_d : 10 ≤ n.toNat → 1 ≤ d.toNat := by
            intro h10
            by_cases hd0 : d.toNat = 0
            · have hp0 : p.toNat = 1 := by rw [hp_eq, hd0]
              omega
            · omega
          c0_hsteps
          exact hJexit () m0 ⟨rfl, hd18, hp_eq, hpn, fun _ => hn_lt, h10_d⟩
      · have hd18_eq : d.toNat = 18 := by bv_omega
        c0_hsteps
        exact hJexit () m0
          ⟨rfl, hd18, hp_eq, hpn, fun hlt => absurd hd18_eq (Nat.ne_of_lt hlt), fun _ => by omega⟩

private theorem m7_core_upd_self (c : FullCoreState) (h0 : c.cur_level = 0) :
    ({ c with vals := c.vals, lvl := c.lvl, rsns := c.rsns, trl := c.trl,
              trail_pos := c.trail_pos, trail_end := c.trail_end,
              propagated := c.propagated, cur_level := 0,
              unassigned := c.unassigned } : FullCoreState) = c := by
  cases c; dsimp only at h0; simp [h0]

private theorem m7_core_upd_id (c : FullCoreState) :
    ({ c with vals := c.vals, lvl := c.lvl, rsns := c.rsns, trl := c.trl,
              trail_pos := c.trail_pos, trail_end := c.trail_end,
              propagated := c.propagated, cur_level := c.cur_level,
              unassigned := c.unassigned } : FullCoreState) = c := by
  cases c; rfl

theorem full_rephase_m7_wp (Γ : Env)
    (hBack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hWalk : ∀ a m Q X, Full.fullWalkSpec a m Q X →
      Γ "full_walk" [i64] [] a m Q X)
    (hLog : ∀ a m Q X, m7Log10Q16Spec a m Q X →
      Γ "full_log10_q16_m7" [i64] [i64] a m Q X) :
    ∀ a m Q X, FullM5Sched.m5RephaseSpec a m Q X →
      Func.wp Γ full_rephase_m7_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m0 Q X ⟨c, F0, s, R, rfl, hinv, hm0, hQ⟩
  unfold Func.wp full_rephase_m7_body
  have hmax := c.hmaxv; unfold dimacsBound at hmax
  obtain ⟨F_cur, hw0⟩ := hinv.witness
  have hco0 := hinv.lengths.core_ok
  c0_hsteps_nogrp
  · have hst0 : s.scratch.stable = 0#64 := by c0_cond hc; exact hc
    let sc' : FullScratch := { s.scratch with rephase_limit := s.scratch.mode_confl_lim }
    have hsc' : sc'.LengthsOk c :=
      { hinv.lengths.scratch_ok with wsort_len := hinv.lengths.scratch_ok.wsort_len }
    have hinv' : FullCoreInv c F0 { s with scratch := sc' } :=
      hinv.with_fuel_scratch_spec ⟨hco0, hsc'⟩ rfl
    have hinv'' := hinv'
    have hce := m7_core_upd_id s.core
    exact hQ s.core.vals s.core.lvl s.core.rsns s.core.trl s.core.trail_pos
      s.core.trail_end s.core.propagated s.core.cur_level s.core.unassigned s.core.fuel sc' _
      (by simpa [hce] using hinv'') (fun hnz => absurd hst0 hnz) (le_refl _) (le_refl _)
      ⟨rfl, rfl⟩ (by simpa [sc'] using hm)
  · have hst_nz0 : s.scratch.stable ≠ 0#64 := by c0_cond hc; exact hc
    have hcl_lt64 : s.core.cur_level < 2 ^ 64 := by
      have := hw0.cur_level_le; have := hco0.trail_end_le; have := hco0.cur_vars_le; omega
    have hmaxv_pos : (0 : BitVec 64).toNat < s.core.cur_level →
        (0 : BitVec 64).toNat < c.max_vars := by
      intro _; have := hw0.cur_level_le; have := hco0.trail_end_le
      have := hco0.cur_vars_le; omega
    refine wp_join_group (ts := [])
      (fun () m1 => ∃ vals1 lvl1 rsns1 trl1 tp1 te1 prop1 unass1 sc1,
        let st1 : FullState :=
          { core := { s.core with vals := vals1, lvl := lvl1, rsns := rsns1, trl := trl1,
                                  trail_pos := tp1, trail_end := te1, propagated := prop1,
                                  cur_level := 0, unassigned := unass1 }
            scratch := sc1 }
        FullCoreInv c F0 st1 ∧ Full.FullExtScratchPres s st1 ∧ (FullMem c st1 ⋆ R) m1)
      ?_ ?_
    · rintro _ ⟨⟩ m1 ⟨vals1, lvl1, rsns1, trl1, tp1, te1, prop1, unass1, sc1,
        hinv1, hpres1, hm1⟩
      clear hm0
      let st1 : FullState :=
        { core := { s.core with vals := vals1, lvl := lvl1, rsns := rsns1, trl := trl1,
                                trail_pos := tp1, trail_end := te1, propagated := prop1,
                                cur_level := 0, unassigned := unass1 }
          scratch := sc1 }
      have hinv1' : FullCoreInv c F0 st1 := hinv1
      have hm1' : (FullMem c st1 ⋆ R) m1 := hm1
      have hcv_le1 : st1.core.cur_vars ≤ c.max_vars := hinv1'.lengths.core_ok.cur_vars_le
      let sc2 : FullScratch := { sc1 with rephased := sc1.rephased + 1#64 }
      have hsc2_ok : sc2.LengthsOk c :=
        { hinv1'.lengths.scratch_ok with walk_vals_len := hinv1'.lengths.scratch_ok.walk_vals_len }
      let st2 : FullState := { st1 with scratch := sc2 }
      have hinv2 : FullCoreInv c F0 st2 :=
        hinv1'.with_fuel_scratch_spec ⟨hinv1'.lengths.core_ok, hsc2_ok⟩ rfl
      c0_hsteps_nogrp
      refine wp_join_group (ts := [])
        (fun () m2 => ∃ (fuel' : BitVec 64) (sc3 : FullScratch),
          sc3.LengthsOk c ∧ fuel'.toNat ≤ s.core.fuel.toNat ∧
          sc3.last_learned = s.scratch.last_learned ∧ sc3.extend_len = s.scratch.extend_len ∧
          (FullMem c { core := { st1.core with fuel := fuel' }, scratch := sc3 } ⋆ R) m2)
        ?_ ?_
      · rintro _ ⟨⟩ m2 ⟨fuel', sc3, hsc3, hfl3, hll3, hext3, hm2⟩
        c0_hsteps_nogrp
        refine wp_loop_inv
          (fun (k, ()) m3 => ∃ ptgt' : List (BitVec 8),
            k.toNat ≤ st1.core.cur_vars ∧ ptgt'.length = c.max_vars ∧
            (FullMem c
              { core := { st1.core with fuel := fuel' }
                scratch := { sc3 with phases_target := ptgt' } } ⋆ R) m3)
          (fun (k, ()) _ => st1.core.cur_vars - k.toNat)
          (fun Jl hJl => by
            c0_steps
            exact hJl (0#64, ()) m2 ⟨sc3.phases_target, Nat.zero_le _, hsc3.phases_target_len, hm2⟩)
          (fun Jl (k, ()) m3 ⟨ptgt', hk_le, hpt_len, hm3⟩ ihk => ?_)
        clear hm2
        have hph3 := hsc3.phases_len
        c0_hsteps_nogrp
        · have hk_lt : k.toNat < st1.core.cur_vars := by c0_bound
          have hk1 : (k + 1#64).toNat = k.toNat + 1 := m7_bv64_add1 (by omega)
          exact ihk (k + 1#64, ()) _ (by dsimp only; omega)
            ⟨ptgt'.set k.toNat (sc3.phases[k.toNat]'(by omega)), by omega, by simp [hpt_len], hm⟩
        · let st3 : FullState :=
            { core := { st1.core with fuel := fuel' }
              scratch := { sc3 with phases_target := ptgt', target_assigned := 0#64 } }
          refine wp_join_group (ts := [i64]) (fun _ m4 => (FullMem c st3 ⋆ R) m4) ?_ ?_
          · rintro _ ⟨nc, ⟨⟩⟩ m4 hm4
            c0_hsteps_nogrp
            c0_call hLog
            intro q _ _
            c0_hsteps_nogrp
            refine wp_join_group (ts := [i64]) (fun _ m5 => (FullMem c st3 ⋆ R) m5) ?_ ?_
            · rintro _ ⟨scaled, ⟨⟩⟩ m5 hm5
              clear hm4
              c0_steps
              let sc4 : FullScratch :=
                { sc3 with phases_target := ptgt', target_assigned := 0#64,
                           rephase_limit := sc3.conflicts + scaled }
              have hsc4 : sc4.LengthsOk c := { hsc3 with phases_target_len := hpt_len }
              have hco4 : FullCoreState.LengthsOk c { st1.core with fuel := fuel' } :=
                { hinv1'.lengths.core_ok with vals_len := hinv1'.lengths.core_ok.vals_len }
              have hinv4 : FullCoreInv c F0
                  { core := { st1.core with fuel := fuel' }, scratch := sc4 } :=
                hinv1'.with_fuel_scratch_spec ⟨hco4, hsc4⟩ rfl
              exact hQ vals1 lvl1 rsns1 trl1 tp1 te1 prop1 0 unass1 fuel' sc4 _
                hinv4 (fun _ => rfl) (Nat.zero_le _) hfl3 ⟨hll3, hext3⟩
                (by simpa [st3, sc4] using hm)
            · intro _ hJsc
              c0_hsteps_nogrp
              · exact hJsc (_, ()) m4 hm4
              · refine wp_join_group (ts := [i64]) (fun _ m5 => (FullMem c st3 ⋆ R) m5) ?_ ?_
                · rintro _ ⟨nlim, ⟨⟩⟩ m5 hm5; c0_steps; exact hJsc (_, ()) m5 hm5
                · intro _ hJnl; c0_steps
                  · exact hJnl (100000000#64, ()) m4 hm4
                  · exact hJnl (_, ()) m4 hm4
          · intro _ hJnc; c0_steps
            · exact hJnc (_, ()) m hm
            · exact hJnc (1000000000000#64, ()) m hm
      · intro Jsel hJsel
        have hll1 : sc2.last_learned = s.scratch.last_learned := hpres1.1
        have hext1 : sc2.extend_len = s.scratch.extend_len := hpres1.2
        have hfl1 : st1.core.fuel.toNat ≤ s.core.fuel.toNat := le_refl _
        let RetP : Tup Val [] → Mem 64 → Prop := fun () m2 =>
          ∃ (fuel' : BitVec 64) (sc3 : FullScratch),
            sc3.LengthsOk c ∧ fuel'.toNat ≤ s.core.fuel.toNat ∧
            sc3.last_learned = s.scratch.last_learned ∧
            sc3.extend_len = s.scratch.extend_len ∧
            (FullMem c { core := { st1.core with fuel := fuel' }, scratch := sc3 } ⋆ R) m2
        refine wp_join_group (fun () m_in => m_in = m) ?_ ?_
        · rintro _ ⟨⟩ m_in hm_eq
          subst m_in
          have hm_base := hm
          clear hm
          refine wp_loop_inv
            (fun (k, ()) m3 => ∃ ph' : List (BitVec 8),
              k.toNat ≤ st1.core.cur_vars ∧ ph'.length = c.max_vars ∧
              (FullMem c { st2 with scratch := { sc2 with phases := ph' } } ⋆ R) m3)
            (fun (k, ()) _ => st1.core.cur_vars - k.toNat)
            (fun L hL => by
              c0_hsteps
              exact hL (0#64, ()) m ⟨sc2.phases, Nat.zero_le _, hsc2_ok.phases_len, hm_base⟩)
            (fun L (k, ()) m3 ⟨ph', hk_le, hph_l, hm3⟩ ihk => ?_)
          have hpb_l := hsc2_ok.phases_best_len
          c0_hsteps_nogrp
          · have hk_lt : k.toNat < st1.core.cur_vars := by c0_bound
            have hk1 : (k + 1#64).toNat = k.toNat + 1 := m7_bv64_add1 (by omega)
            refine wp_join_group (ts := [])
              (fun () m4 => ∃ ph'' : List (BitVec 8), ph''.length = c.max_vars ∧
                (FullMem c { st2 with scratch := { sc2 with phases := ph'' } } ⋆ R) m4)
              ?_ ?_
            · rintro _ ⟨⟩ m4 ⟨ph'', hph'', hm4⟩
              c0_steps
              exact ihk (k + 1#64, ()) m4 (by dsimp only; omega) ⟨ph'', by omega, hph'', hm4⟩
            · intro _ hJif
              c0_hsteps_nogrp
              · c0_hsteps
                exact hJif () _
                  ⟨ph'.set k.toNat (sc2.phases_best[k.toNat]'(by omega)),
                    by simp [hph_l], by assumption⟩
              · exact hJif () m3 ⟨ph', hph_l, hm3⟩
          · exact hJsel () _ ⟨st1.core.fuel, { sc2 with phases := ph', best_assigned := 0#64 },
              { hsc2_ok with phases_len := hph_l }, hfl1, hll1, hext1, by assumption⟩
        · intro Jbest hJbest
          c0_hsteps_nogrp
          · exact hJbest () m rfl
          · exact hJbest () m rfl
          · refine wp_join_group (ts := []) RetP ?_ ?_
            · rintro _ ⟨⟩ m_out hret
              c0_steps
              exact hJsel () m_out hret
            · intro J_after hJ_after
              refine wp_join_group (ts := []) (fun () m_in => m_in = m) ?_ ?_
              · rintro _ ⟨⟩ m_in hm_eq
                subst m_in
                c0_call hWalk
                refine ⟨c, F0, st2, R, rfl, hinv2, hm,
                  fun fuel' sc3 m3 hlen3 hfl3 hpres3 hm3 => ?_⟩
                c0_hsteps
                exact hJ_after () m3 ⟨fuel', sc3, hlen3.scratch_ok, Nat.le_trans hfl3 hfl1,
                  hpres3.1.trans hll1, hpres3.2.trans hext1, hm3⟩
              · intro Jwalk hJwalk
                c0_hsteps_nogrp
                · exact hJwalk () m rfl
                · exact hJwalk () m rfl
                · refine wp_join_group (ts := []) RetP ?_ ?_
                  · rintro _ ⟨⟩ m_out hret
                    c0_steps
                    exact hJ_after () m_out hret
                  · intro J2 hJ2
                    c0_hsteps_nogrp
                    · refine wp_loop_inv
                        (fun (k, ()) m3 => ∃ ph' : List (BitVec 8),
                          k.toNat ≤ st1.core.cur_vars ∧ ph'.length = c.max_vars ∧
                          (FullMem c { st2 with scratch := { sc2 with phases := ph' } } ⋆ R) m3)
                        (fun (k, ()) _ => st1.core.cur_vars - k.toNat)
                        (fun L hL => by
                          c0_hsteps
                          exact hL (0#64, ()) m
                            ⟨sc2.phases, Nat.zero_le _, hsc2_ok.phases_len, hm⟩)
                        (fun L (k, ()) m3 ⟨ph', hk_le, hph_l, hm3⟩ ihk => ?_)
                      c0_hsteps
                      · have hk_lt : k.toNat < st1.core.cur_vars := by c0_bound
                        have hk1 : (k + 1#64).toNat = k.toNat + 1 := m7_bv64_add1 (by omega)
                        exact ihk (k + 1#64, ()) _ (by dsimp only; omega)
                          ⟨ph'.set k.toNat _, by omega, by simp [hph_l], hm⟩
                      · exact hJ2 () m3 ⟨st1.core.fuel, { sc2 with phases := ph' },
                          { hsc2_ok with phases_len := hph_l }, hfl1, hll1, hext1, hm3⟩
                    · refine wp_loop_inv
                        (fun (k, ()) m3 => ∃ ph' : List (BitVec 8),
                          k.toNat ≤ st1.core.cur_vars ∧ ph'.length = c.max_vars ∧
                          (FullMem c { st2 with scratch := { sc2 with phases := ph' } } ⋆ R) m3)
                        (fun (k, ()) _ => st1.core.cur_vars - k.toNat)
                        (fun L hL => by
                          c0_hsteps
                          exact hL (0#64, ()) m
                            ⟨sc2.phases, Nat.zero_le _, hsc2_ok.phases_len, hm⟩)
                        (fun L (k, ()) m3 ⟨ph', hk_le, hph_l, hm3⟩ ihk => ?_)
                      c0_hsteps
                      · have hk_lt : k.toNat < st1.core.cur_vars := by c0_bound
                        have hk1 : (k + 1#64).toNat = k.toNat + 1 := m7_bv64_add1 (by omega)
                        exact ihk (k + 1#64, ()) _ (by dsimp only; omega)
                          ⟨ph'.set k.toNat _, by omega, by simp [hph_l], hm⟩
                      · exact hJ2 () m3 ⟨st1.core.fuel, { sc2 with phases := ph' },
                          { hsc2_ok with phases_len := hph_l }, hfl1, hll1, hext1, hm3⟩
    · intro Jbt hJbt
      c0_hsteps_nogrp
      · c0_call hBack
        refine ⟨c, s, R, rfl, hinv.lengths, hcl_lt64, hmaxv_pos, hw0.trail_lits_lt, hm0,
          fun vals1 lvl1 rsns1 trl1 tp1 te1 prop1 cl1 unass1 sc1 m1
            hlen1 _ _ hcl1 _ hsc_eq _ _ hwinv1 _ hm1 => ?_⟩
        rcases hsc_eq with ⟨_, _, _, _, _, _, _, _, _, hsc_eq⟩
        have hpres1 : Full.FullExtScratchPres s
            { core := { s.core with vals := vals1, lvl := lvl1, rsns := rsns1, trl := trl1,
                                    trail_pos := tp1, trail_end := te1, propagated := prop1,
                                    cur_level := 0, unassigned := unass1 }
              scratch := sc1 } := ⟨by rw [hsc_eq], by rw [hsc_eq]⟩
        have hcl1_eq : cl1 = 0 := by rw [hcl1]; exact Nat.min_zero _
        have hw1 := hwinv1 F0 F_cur hw0 (Nat.zero_le _)
        rw [hcl1_eq] at hlen1 hw1 hm1
        exact hJbt () m1 ⟨vals1, lvl1, rsns1, trl1, tp1, te1, prop1, unass1, sc1,
          ⟨hlen1, F_cur, hw1⟩, hpres1, hm1⟩
      · have hcl0 : s.core.cur_level = 0 := by c0_cond hc; bv_omega
        have hcore_eq := m7_core_upd_self s.core hcl0
        exact hJbt () m0 ⟨s.core.vals, s.core.lvl, s.core.rsns, s.core.trl, s.core.trail_pos,
          s.core.trail_end, s.core.propagated, s.core.unassigned, s.scratch,
          ⟨by simpa [hcore_eq] using hinv.lengths, F_cur, by simpa [hcore_eq] using hw0⟩,
          ⟨rfl, rfl⟩, by simpa [hcore_eq] using hm0⟩

end LeanQbe.T.Examples.Kissat.FullM7AnalyzeSort
