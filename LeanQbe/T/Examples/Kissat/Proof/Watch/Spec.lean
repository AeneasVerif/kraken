/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts3
public import LeanQbe.T.Examples.Kissat.Src.Watch
public import LeanQbe.T.Logic.CanonicalEnv

/-!
# Kissat Flat `Watch` Canonical `Spec` Table (`Proof.Watch.Spec`)

Canonical UNSAT-only `Spec` contracts (`1` per function in `Src.Watch.fns`, `15` rows), `XFree`
witnesses (`by xfree`), `SpecEntry` membership/env projections, and literal `sigs := rfl` alignment
against `Src.Watch.fns`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Watch.Spec

open Std Std.Sat
open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src
open LeanQbe.T.Examples.Kissat.Proof.Spec

/-! ## 1. Auxiliary Watch-Sort Predicates & Missing Canonical `Spec` Definitions -/

/-- Read `i`-th `u32` entry of `ws` as `Nat`, defaulting to `0`. -/
@[expose] def wsVal (ws : List (BitVec 32)) (i : Nat) : Nat :=
  (ws[i]?.getD 0#32).toNat

/-- Non-decreasing `key (wsVal ws i)` across indices `[lo ..< hi)`. -/
@[expose] def SortedRange (key : Nat → Nat) (ws : List (BitVec 32)) (lo hi : Nat) : Prop :=
  ∀ i j, lo ≤ i → i ≤ j → j < hi → key (wsVal ws i) ≤ key (wsVal ws j)

/-- Watch-vector offset `wvec[2 * l]` as `Nat` (for `full_wstack_radix_sort_m6`). -/
@[expose] def fullWvecOff (wvec : List (BitVec 32)) (l : Nat) : Nat :=
  (wvec[2 * l]?.getD 0#32).toNat

/-- Canonical contract for `full_wstack_radix_sort_m6` (in-place 256-bucket LSB radix sort on
`ws[0 ..< n)` keyed by `fullWvecOff wvec`). -/
@[expose] def fullWstackRadixSortSpec : Spec [i64, i64, i64, i64, i64, i64] [] :=
  fun (wvec_ptr, ws_ptr, tmp_ptr, cnt_ptr, n, max_off, ()) m Q _ =>
    ∃ (wvec ws tmp cnt : List (BitVec 32)) (R : Mem 64 → Prop),
      n.toNat ≤ ws.length ∧ n.toNat ≤ tmp.length ∧ 256 ≤ cnt.length ∧
      n.toNat < 2 ^ 31 ∧ max_off.toNat < 2 ^ 32 ∧
      (∀ j < n.toNat,
        2 * wsVal ws j + 1 < wvec.length ∧ fullWvecOff wvec (wsVal ws j) ≤ max_off.toNat) ∧
      (array (t := i32) wvec_ptr wvec ⋆ array (t := i32) ws_ptr ws ⋆
        array (t := i32) tmp_ptr tmp ⋆ array (t := i32) cnt_ptr cnt ⋆ R) m ∧
      ∀ ws' tmp' cnt' m',
        ws'.length = ws.length → tmp'.length = tmp.length → cnt'.length = cnt.length →
        (ws'.take n.toNat).Perm (ws.take n.toNat) →
        SortedRange (fullWvecOff wvec) ws' 0 n.toNat →
        (∀ i, n.toNat ≤ i → ws'[i]? = ws[i]?) →
        (array (t := i32) wvec_ptr wvec ⋆ array (t := i32) ws_ptr ws' ⋆
          array (t := i32) tmp_ptr tmp' ⋆ array (t := i32) cnt_ptr cnt' ⋆ R) m' → Q () m'

/-- Canonical contract for `full_watch_pop_c0`: drops the trailing `cnt` watch words from `lit`'s
slice, filling them with `0xFFFFFFFF#32` and keeping all other watch slices verbatim. -/
@[expose] def fullWatchPopC0Spec : Spec [i64, i32, i32] [] :=
  fun (h, lit, cnt, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ WatchStackLayout s.core ∧
      lit.toNat < 2 * s.core.cur_vars ∧
      0 < cnt.toNat ∧ cnt.toNat ≤ fullWatchSize s lit.toNat ∧
      (FullMem c s ⋆ R) m ∧
      ∀ wvec' wstk' wusable' m',
        let s' : FullState :=
          { s with core :=
            { s.core with wvec := wvec', wstk := wstk', wusable := wusable' } }
        s'.LengthsOk c → WatchStackLayout s'.core →
        (∀ l < 2 * s.core.cur_vars, l ≠ lit.toNat →
          fullWatchOff s' l = fullWatchOff s l ∧
          fullWatchSize s' l = fullWatchSize s l ∧
          ∀ k < fullWatchSize s l,
            s'.core.wstk[fullWatchOff s' l + k]? = s.core.wstk[fullWatchOff s l + k]?) →
        fullWatchOff s' lit.toNat = fullWatchOff s lit.toNat →
        fullWatchSize s' lit.toNat = fullWatchSize s lit.toNat - cnt.toNat →
        (∀ k < fullWatchSize s lit.toNat - cnt.toNat,
          s'.core.wstk[fullWatchOff s' lit.toNat + k]? =
            s.core.wstk[fullWatchOff s lit.toNat + k]?) →
        (FullMem c s' ⋆ R) m' → Q () m'

/-- Step-13 canonical contract for `full_delete_binary`: removes both sides `(a, b)` and `(b, a)`,
updates elimination/factor `flags` bits, and decrements `num_binary`. -/
@[expose] def fullDeleteBinarySpec : Spec [i64, i32, i32] [] :=
  fun (h, a, b, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ WatchStackLayout s.core ∧
      a.toNat < 2 * c.max_vars ∧ b.toNat < 2 * c.max_vars ∧ (FullMem c s ⋆ R) m ∧
      ∀ flags' wvec' wstk' wu' nb' m',
        let s' : FullState :=
          { s with core := { s.core with flags := flags', wvec := wvec', wstk := wstk',
                                         wusable := wu', num_binary := nb' } }
        s'.LengthsOk c → WatchStackLayout s'.core →
        (∀ F_cur, ModeWatchesInv F_cur s.core → ModeWatchesInv F_cur s'.core) →
        (FullMem c s' ⋆ R) m' → Q () m'

/-- Canonical contract for `full_prioritize_binaries_m6`: partitions every literal's sparse watch
slice in place using `scratch_buf`, preserving `FullSparseInvW` and all non-watch core fields. -/
@[expose] def fullPrioritizeBinariesM6Spec : Spec [i64] [.bool] :=
  fun (h, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) wstk' scr' m',
        let s' : FullState :=
          { s with
            core := { s.core with wstk := wstk' }
            scratch := { s.scratch with scratch_buf := scr' } }
        FullSparseInvW c F0 F_cur s' → (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-- Canonical Step-13 contract for `full_sort_bin_watches_fid`: preserves `FullSparseInvW`,
`WatchesInv`, and all core fields other than `wstk`. -/
@[expose] def fullSortBinWatchesSpec : Spec [i64] [] :=
  fun (h, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ (FullMem c s ⋆ R) m ∧
      ∀ (wstk' : List (BitVec 32)) (m' : Mem 64),
        let s' : FullState := { s with core := { s.core with wstk := wstk' } }
        wstk'.length = c.wcap →
        FullSparseInvW c F0 F_cur s' →
        WatchesInv F_cur s'.core →
        (FullMem c s' ⋆ R) m' → Q () m'

/-! ## 2. Canonical `SpecEntry` Rows & Table (`specs : List SpecEntry`) -/

@[expose] def e_full_wsort_sift : SpecEntry :=
  ⟨"full_wsort_sift", [i64, i64, i64, i64], [], Proof.Spec.fullWsortSiftSpec, true⟩

@[expose] def e_full_wstack_radix_sort_m6 : SpecEntry :=
  ⟨"full_wstack_radix_sort_m6", [i64, i64, i64, i64, i64, i64], [], fullWstackRadixSortSpec, true⟩

@[expose] def e_full_wstack_defrag_m6 : SpecEntry :=
  ⟨"full_wstack_defrag_m6", [i64], [], Proof.Spec.fullWstackDefragSpec, true⟩

@[expose] def e_full_watch_push_slow_m6 : SpecEntry :=
  ⟨"full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool],
    Proof.Spec.fullWatchPushSpec, true⟩

@[expose] def e_full_watch_push_m6 : SpecEntry :=
  ⟨"full_watch_push_m6", [i64, i32, i32, i32, i32], [.bool], Proof.Spec.fullWatchPushSpec, true⟩

@[expose] def e_full_wstack_defrag : SpecEntry :=
  ⟨"full_wstack_defrag", [i64], [], Proof.Spec.fullWstackDefragSpec, true⟩

@[expose] def e_full_watch_push : SpecEntry :=
  ⟨"full_watch_push", [i64, i32, i32, i32, i32], [.bool], Proof.Spec.fullWatchPushSpec, true⟩

@[expose] def e_full_watch_pop_c0 : SpecEntry :=
  ⟨"full_watch_pop_c0", [i64, i32, i32], [], fullWatchPopC0Spec, true⟩

@[expose] def e_full_unwatch_large : SpecEntry :=
  ⟨"full_unwatch_large", [i64, i32, i32], [], Proof.Spec.fullUnwatchLargeSpec, true⟩

@[expose] def e_full_has_bin : SpecEntry :=
  ⟨"full_has_bin", [i64, i32, i32], [.bool], Proof.Spec.fullHasBinSpec, true⟩

@[expose] def e_full_delete_bin_side : SpecEntry :=
  ⟨"full_delete_bin_side", [i64, i32, i32], [], Proof.Spec.fullDeleteBinSideSpec, true⟩

@[expose] def e_full_delete_binary : SpecEntry :=
  ⟨"full_delete_binary", [i64, i32, i32], [], fullDeleteBinarySpec, true⟩

@[expose] def e_full_prioritize_binaries_m6 : SpecEntry :=
  ⟨"full_prioritize_binaries_m6", [i64], [.bool], fullPrioritizeBinariesM6Spec, true⟩

@[expose] def e_full_sort_bin_watches_fid : SpecEntry :=
  ⟨"full_sort_bin_watches_fid", [i64], [], fullSortBinWatchesSpec, true⟩

@[expose] def e_full_has_ternary : SpecEntry :=
  ⟨"full_has_ternary", [i64, i32, i32, i32], [.bool], Proof.Spec.fullHasTernarySpec, true⟩

/-- Canonical `15`-row contract table matching `Src.Watch.fns` 1:1. -/
@[expose] def specs : List SpecEntry :=
  [ e_full_wsort_sift
  , e_full_wstack_radix_sort_m6
  , e_full_wstack_defrag_m6
  , e_full_watch_push_slow_m6
  , e_full_watch_push_m6
  , e_full_wstack_defrag
  , e_full_watch_push
  , e_full_watch_pop_c0
  , e_full_unwatch_large
  , e_full_has_bin
  , e_full_delete_bin_side
  , e_full_delete_binary
  , e_full_prioritize_binaries_m6
  , e_full_sort_bin_watches_fid
  , e_full_has_ternary ]

theorem specs_sigs : specs.map SpecEntry.sig = Watch.fns.map Fn.sig := rfl

theorem specs_names_nodup : (specs.map SpecEntry.name).Nodup := by
  decide

/-! ## 3. `Spec.XFree` Proofs & `Env.Sat.has` Projections -/

theorem fullWsortSiftSpec_xfree : Spec.XFree Proof.Spec.fullWsortSiftSpec := by xfree
theorem fullWstackRadixSortSpec_xfree : Spec.XFree fullWstackRadixSortSpec := by xfree
theorem fullWstackDefragSpec_xfree : Spec.XFree Proof.Spec.fullWstackDefragSpec := by xfree
theorem fullWatchPushSpec_xfree : Spec.XFree Proof.Spec.fullWatchPushSpec := by xfree
theorem fullWatchPopC0Spec_xfree : Spec.XFree fullWatchPopC0Spec := by xfree
theorem fullUnwatchLargeSpec_xfree : Spec.XFree Proof.Spec.fullUnwatchLargeSpec := by xfree
theorem fullHasBinSpec_xfree : Spec.XFree Proof.Spec.fullHasBinSpec := by xfree
theorem fullDeleteBinSideSpec_xfree : Spec.XFree Proof.Spec.fullDeleteBinSideSpec := by xfree
theorem fullDeleteBinarySpec_xfree : Spec.XFree fullDeleteBinarySpec := by xfree
theorem fullPrioritizeBinariesM6Spec_xfree : Spec.XFree fullPrioritizeBinariesM6Spec := by xfree
theorem fullSortBinWatchesSpec_xfree : Spec.XFree fullSortBinWatchesSpec := by xfree
theorem fullHasTernarySpec_xfree : Spec.XFree Proof.Spec.fullHasTernarySpec := by xfree

theorem mem_full_wsort_sift : e_full_wsort_sift ∈ specs := by simp [specs]
theorem mem_full_wstack_radix_sort_m6 : e_full_wstack_radix_sort_m6 ∈ specs := by simp [specs]
theorem mem_full_wstack_defrag_m6 : e_full_wstack_defrag_m6 ∈ specs := by simp [specs]
theorem mem_full_watch_push_slow_m6 : e_full_watch_push_slow_m6 ∈ specs := by simp [specs]
theorem mem_full_watch_push_m6 : e_full_watch_push_m6 ∈ specs := by simp [specs]
theorem mem_full_wstack_defrag : e_full_wstack_defrag ∈ specs := by simp [specs]
theorem mem_full_watch_push : e_full_watch_push ∈ specs := by simp [specs]
theorem mem_full_watch_pop_c0 : e_full_watch_pop_c0 ∈ specs := by simp [specs]
theorem mem_full_unwatch_large : e_full_unwatch_large ∈ specs := by simp [specs]
theorem mem_full_has_bin : e_full_has_bin ∈ specs := by simp [specs]
theorem mem_full_delete_bin_side : e_full_delete_bin_side ∈ specs := by simp [specs]
theorem mem_full_delete_binary : e_full_delete_binary ∈ specs := by simp [specs]
theorem mem_full_prioritize_binaries_m6 : e_full_prioritize_binaries_m6 ∈ specs := by simp [specs]
theorem mem_full_sort_bin_watches_fid : e_full_sort_bin_watches_fid ∈ specs := by simp [specs]
theorem mem_full_has_ternary : e_full_has_ternary ∈ specs := by simp [specs]

theorem has_full_wsort_sift {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_wsort_sift" Proof.Spec.fullWsortSiftSpec :=
  h.has mem_full_wsort_sift fullWsortSiftSpec_xfree

theorem has_full_wstack_radix_sort_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_wstack_radix_sort_m6" fullWstackRadixSortSpec :=
  h.has mem_full_wstack_radix_sort_m6 fullWstackRadixSortSpec_xfree

theorem has_full_wstack_defrag_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_wstack_defrag_m6" Proof.Spec.fullWstackDefragSpec :=
  h.has mem_full_wstack_defrag_m6 fullWstackDefragSpec_xfree

theorem has_full_watch_push_slow_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_watch_push_slow_m6" Proof.Spec.fullWatchPushSpec :=
  h.has mem_full_watch_push_slow_m6 fullWatchPushSpec_xfree

theorem has_full_watch_push_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_watch_push_m6" Proof.Spec.fullWatchPushSpec :=
  h.has mem_full_watch_push_m6 fullWatchPushSpec_xfree

theorem has_full_wstack_defrag {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_wstack_defrag" Proof.Spec.fullWstackDefragSpec :=
  h.has mem_full_wstack_defrag fullWstackDefragSpec_xfree

theorem has_full_watch_push {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_watch_push" Proof.Spec.fullWatchPushSpec :=
  h.has mem_full_watch_push fullWatchPushSpec_xfree

theorem has_full_watch_pop_c0 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_watch_pop_c0" fullWatchPopC0Spec :=
  h.has mem_full_watch_pop_c0 fullWatchPopC0Spec_xfree

theorem has_full_unwatch_large {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_unwatch_large" Proof.Spec.fullUnwatchLargeSpec :=
  h.has mem_full_unwatch_large fullUnwatchLargeSpec_xfree

theorem has_full_has_bin {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_has_bin" Proof.Spec.fullHasBinSpec :=
  h.has mem_full_has_bin fullHasBinSpec_xfree

theorem has_full_delete_bin_side {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_delete_bin_side" Proof.Spec.fullDeleteBinSideSpec :=
  h.has mem_full_delete_bin_side fullDeleteBinSideSpec_xfree

theorem has_full_delete_binary {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_delete_binary" fullDeleteBinarySpec :=
  h.has mem_full_delete_binary fullDeleteBinarySpec_xfree

theorem has_full_prioritize_binaries_m6 {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_prioritize_binaries_m6" fullPrioritizeBinariesM6Spec :=
  h.has mem_full_prioritize_binaries_m6 fullPrioritizeBinariesM6Spec_xfree

theorem has_full_sort_bin_watches_fid {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_sort_bin_watches_fid" fullSortBinWatchesSpec :=
  h.has mem_full_sort_bin_watches_fid fullSortBinWatchesSpec_xfree

theorem has_full_has_ternary {Γ : Env} (h : Γ.Sat specs) :
    Γ.Has "full_has_ternary" Proof.Spec.fullHasTernarySpec :=
  h.has mem_full_has_ternary fullHasTernarySpec_xfree

end LeanQbe.T.Examples.Kissat.Proof.Watch.Spec
