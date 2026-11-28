/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Bump
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
public import LeanQbe.T.Examples.Kissat.Proof.Bump.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Bump.WpSortHelpers
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
meta import LeanQbe.T.Logic.C0Step
meta import LeanQbe.T.Logic.C0HeadStep

/-!
# Sorting Helpers & LSD Radix Sort Branch (`Proof.Bump.WpSortRadix`)

Pure permutation/coverage lemmas, `FullMem` focus/unfocus helpers with opaque-sized tail atoms
(`InsTail`, `RdxTail`, `SiftTail`), shared pack/copy WP helpers (`sort_ana_pack_wp_var`,
`sort_ana_pack_wp`, `sort_ana_copy_wp`), and the `sort_ana_radix_wp` branch (`n >= 32` and
`scratch_cap >= 512`) of `full_sort_ana_qs_m6`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Bump

open Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Src.Bump
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullKissatMath
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open LeanQbe.T.Examples.Kissat.Proof.Bump.Spec
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open Kraken.Bedrock2.Test

public section

/-! ## 1. Pure List, Permutation, Coverage & Memory-Update Helpers -/

theorem list_perm_take_split {α : Type} [BEq α] [LawfulBEq α] (a b : List α)
    {m n : Nat} (hmn : m ≤ n) (hpm : (b.take m).Perm (a.take m))
    (htail : ∀ k, m ≤ k → b[k]? = a[k]?) :
    (b.take n).Perm (a.take n) := by
  have hsplit (xs : List α) : xs.take n = xs.take m ++ (xs.drop m).take (n - m) := by
    rw [← List.take_append_drop m (xs.take n), List.take_take, Nat.min_eq_left hmn, List.drop_take]
  have hdt : (b.drop m).take (n - m) = (a.drop m).take (n - m) := by
    apply List.ext_getElem?; intro k
    by_cases hk : k < n - m
    · rw [List.getElem?_take_of_lt hk, List.getElem?_take_of_lt hk,
        List.getElem?_drop, List.getElem?_drop]
      exact htail (m + k) (by omega)
    · rw [List.getElem?_take, List.getElem?_take]; simp [hk]
  rw [hsplit b, hsplit a, hdt]
  exact hpm.append_right _

theorem ana_cov_of_perm (ana ana' : List (BitVec 32)) {n cv : Nat}
    (hn : n ≤ ana.length) (hn' : n ≤ ana'.length)
    (hperm : (ana'.take n).Perm (ana.take n))
    (hcov : ∀ k < n, (ana[k]?.getD 0#32).toNat < cv) :
    ∀ k < n, (ana'[k]?.getD 0#32).toNat < cv := by
  intro k hk
  have hk_take : k < (ana'.take n).length := by rw [List.length_take_of_le hn']; exact hk
  have hmem : ana'[k]'(by omega) ∈ ana'.take n := by
    rw [← List.getElem_take]
    · exact List.getElem_mem _
    · exact hk_take
  have hmem_a : ana'[k]'(by omega) ∈ ana.take n := hperm.mem_iff.mp hmem
  rw [List.mem_iff_getElem] at hmem_a
  obtain ⟨j, hj, hj_eq⟩ := hmem_a
  rw [List.length_take_of_le hn] at hj
  rw [List.getElem_take] at hj_eq
  have hlt := hcov j hj
  simp only [List.getElem?_eq_getElem (by omega : j < ana.length), Option.getD_some] at hlt
  simp only [List.getElem?_eq_getElem (by omega : k < ana'.length), Option.getD_some, ← hj_eq]
  exact hlt

theorem listSwap_cov {ana : List (BitVec 32)} {i j n cv : Nat}
    (hi : i < n) (hj : j < n) (hn : n ≤ ana.length)
    (hcov : ∀ k < n, (ana[k]?.getD 0#32).toNat < cv) :
    ∀ k < n, ((listSwap ana i j (by omega) (by omega))[k]?.getD 0#32).toNat < cv := by
  apply ana_cov_of_perm ana (listSwap ana i j (by omega) (by omega)) hn
    (by rw [listSwap_length]; exact hn)
  · exact list_take_set_perm_swap ana hi hj hn
  · exact hcov

theorem ins_step_swap_eq {α : Type} (xs : List α) {j : Nat} (hj0 : 0 < j)
    (hj : j < xs.length) (x : α) :
    ((xs.set j xs[j - 1]).set (j - 1) x) =
      listSwap (xs.set j x) (j - 1) j (by simp; omega) (by simp; omega) := by
  apply List.ext_getElem?; intro k
  have hj1 : j - 1 < xs.length := by omega
  have hne : j - 1 ≠ j := by omega
  unfold listSwap
  by_cases hk1 : k = j - 1
  · subst hk1
    rw [List.getElem?_set_self (by simp only [List.length_set]; omega),
      List.getElem?_set_ne (Ne.symm hne),
      List.getElem?_set_self (by simp only [List.length_set]; omega),
      List.getElem_set_self (by simp only [List.length_set]; omega)]
  · by_cases hk2 : k = j
    · subst hk2
      have hk_x : k < (xs.set k x).length := by rw [List.length_set]; exact hj
      have hlen_in : k < ((xs.set k x).set (k - 1) ((xs.set k x)[k]'hk_x)).length := by
        rw [List.length_set, List.length_set]; exact hj
      rw [List.getElem?_set_ne (Ne.symm hk1), List.getElem?_set_self hj,
        List.getElem?_set_self hlen_in, List.getElem_set_ne (Ne.symm hne)]
    · rw [List.getElem?_set_ne (Ne.symm hk1), List.getElem?_set_ne (Ne.symm hk2),
        List.getElem?_set_ne (Ne.symm hk2), List.getElem?_set_ne (Ne.symm hk1),
        List.getElem?_set_ne (Ne.symm hk2)]

private theorem list_take_succ {α : Type} (xs : List α) {i : Nat} (hi : i < xs.length) :
    xs.take (i + 1) = xs.take i ++ [xs[i]] := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i' =>
      simp only [List.take_succ_cons, List.getElem_cons_succ, List.cons_append]
      exact congrArg (x :: ·) (ih (by simp at hi; omega))

private theorem map_setWidth32_take_eq (rk : List (BitVec 64)) (ana : List (BitVec 32))
    {n : Nat} (hrk : n ≤ rk.length) (hana : n ≤ ana.length)
    (h : ∀ k < n, (rk[k]?.getD 0#64).setWidth 32 = ana[k]?.getD 0#32) :
    (rk.take n).map (·.setWidth 32) = ana.take n := by
  apply List.ext_getElem?; intro k
  by_cases hk : k < n
  · rw [List.getElem?_map, List.getElem?_take_of_lt hk, List.getElem?_take_of_lt hk]
    have h1 := h k hk
    simp only [List.getElem?_eq_getElem (by omega : k < rk.length),
      List.getElem?_eq_getElem (by omega : k < ana.length), Option.getD_some] at h1 ⊢
    exact congrArg some h1
  · rw [List.getElem?_map, List.getElem?_take, List.getElem?_take]; simp [hk]

theorem ana_copy_perm_cov (ana0 ana_end : List (BitVec 32))
    (rk0 rk_end : List (BitVec 64)) {n cv : Nat}
    (hna0 : n ≤ ana0.length) (hna1 : ana_end.length = ana0.length)
    (hnrk0 : n ≤ rk0.length) (hrk1 : rk_end.length = rk0.length)
    (hinit : ∀ k < n, (rk0[k]?.getD 0#64).setWidth 32 = ana0[k]?.getD 0#32)
    (hperm : (rk_end.take n).Perm (rk0.take n))
    (hcopy : ∀ k < n, ana_end[k]? = some ((rk_end[k]?.getD 0#64).setWidth 32))
    (hcov0 : ∀ k < n, (ana0[k]?.getD 0#32).toNat < cv) :
    (ana_end.take n).Perm (ana0.take n) ∧
      ∀ k < n, (ana_end[k]?.getD 0#32).toNat < cv := by
  have htake : ana_end.take n = (rk_end.take n).map (·.setWidth 32) := by
    apply List.ext_getElem?; intro k
    by_cases hk : k < n
    · rw [List.getElem?_take_of_lt hk, List.getElem?_map, List.getElem?_take_of_lt hk, hcopy k hk]
      simp [List.getElem?_eq_getElem (by omega : k < rk_end.length)]
    · rw [List.getElem?_take, List.getElem?_map, List.getElem?_take]; simp [hk]
  have hinit_map := map_setWidth32_take_eq rk0 ana0 hnrk0 hna0 hinit
  have hpm : (ana_end.take n).Perm (ana0.take n) := by
    rw [htake, ← hinit_map]; exact hperm.map _
  exact ⟨hpm, ana_cov_of_perm ana0 ana_end hna0 (by omega) hpm hcov0⟩

private theorem pack_rk_step {rk1 : List (BitVec 64)} {ana0 : List (BitVec 32)}
    {i : Nat} (hi_ana : i < ana0.length) (hi_rk1 : i < rk1.length) (q : BitVec 32)
    (hpk1 : ∀ k < i, (rk1[k]?.getD 0#64).setWidth 32 = ana0[k]?.getD 0#32) :
    ∀ k < i + 1,
      ((rk1.set i (packPair64 (ana0[i]'hi_ana) q))[k]?.getD 0#64).setWidth 32 =
        ana0[k]?.getD 0#32 := by
  intro k hk
  by_cases hki : k = i
  · subst hki
    rw [List.getElem?_set_self hi_rk1, Option.getD_some, packPair64_lo]
    simp [List.getElem?_eq_getElem hi_ana]
  · rw [List.getElem?_set_ne (Ne.symm hki)]; exact hpk1 k (by omega)

private theorem copy_ana_step {ana3 : List (BitVec 32)} {s_list : List (BitVec 64)}
    {k : Nat} (hk_sl : k < s_list.length) (hk_ana3 : k < ana3.length)
    (hcp3 : ∀ j < k, ana3[j]? = some ((s_list[j]?.getD 0#64).setWidth 32)) :
    ∀ j < k + 1,
      (ana3.set k ((s_list[k]'hk_sl).setWidth 32))[j]? =
        some ((s_list[j]?.getD 0#64).setWidth 32) := by
  intro j hj
  by_cases hjk : j = k
  · subst hjk
    rw [List.getElem?_set_self hk_ana3]
    simp [List.getElem?_eq_getElem hk_sl]
  · rw [List.getElem?_set_ne (Ne.symm hjk)]; exact hcp3 j (by omega)

private theorem rdx_hist_step_inv {shift i n : Nat} {s_list : List (BitVec 64)}
    {cnt4 : List (BitVec 64)} (hi_sl : i < s_list.length) (hcl4 : cnt4.length = 256)
    (hi_lt : i < n) (hn64 : n < 2 ^ 64)
    (hhist4 : ∀ k < 256, (cnt4[k]?.getD 0#64).toNat = rdxSeen shift s_list i k) :
    let xi := s_list[i]'hi_sl
    let bvi := (xi >>> shift) &&& 255#64
    let cnt4' := cnt4.set bvi.toNat ((cnt4[bvi.toNat]'(by
      have hlt : bvi.toNat < 256 := rdxBkt_lt _ _; omega)) + 1#64)
    ∀ k < 256, (cnt4'[k]?.getD 0#64).toNat = rdxSeen shift s_list (i + 1) k := by
  intro xi bvi cnt4' k hk
  have hbvi_eq : bvi.toNat = rdxBkt shift xi := rfl
  have hbvi_lt : bvi.toNat < 256 := by rw [hbvi_eq]; exact rdxBkt_lt _ _
  have hbvi_c4 : bvi.toNat < cnt4.length := by rw [hcl4]; exact hbvi_lt
  have hcb_val : (cnt4[bvi.toNat]'hbvi_c4).toNat = rdxSeen shift s_list i bvi.toNat := by
    have h1 := hhist4 bvi.toNat hbvi_lt
    simpa [List.getElem?_eq_getElem hbvi_c4] using h1
  have hcb_p1 : ((cnt4[bvi.toNat]'hbvi_c4) + 1#64).toNat =
      (cnt4[bvi.toNat]'hbvi_c4).toNat + 1 := by
    have hseen_le := rdxSeen_le_self shift s_list i bvi.toNat
    rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl, hcb_val,
      Nat.mod_eq_of_lt (by omega)]
  rw [rdxSeen_succ shift s_list hi_sl k]
  by_cases hkb : k = bvi.toNat
  · subst hkb
    dsimp only [cnt4']
    rw [List.getElem?_set_self hbvi_c4, Option.getD_some, hcb_p1, hcb_val]
    simp [show rdxBkt shift (s_list[i]'hi_sl) = bvi.toNat from hbvi_eq.symm]
  · dsimp only [cnt4']
    rw [List.getElem?_set_ne (Ne.symm hkb), hhist4 k hk]
    have hne : ¬ (rdxBkt shift (s_list[i]'hi_sl) = k) := by
      intro heq; exact hkb (by simpa [hbvi_eq, xi] using heq.symm)
    simp [hne]

private theorem rdx_scatter_step_inv {shift i n : Nat} {s_list d_list6 cnt6 : List (BitVec 64)}
    (hi_lt : i < n) (hn_sl : n ≤ s_list.length) (hn_dl : n ≤ d_list6.length)
    (hn64 : n < 2 ^ 64) (hcl6 : cnt6.length = 256)
    (hcnt6 : ∀ k < 256,
      (cnt6[k]?.getD 0#64).toNat = rdxStart (fun b => rdxSeen shift s_list n b) k +
        rdxSeen shift s_list i k)
    (hflat6 : ∀ y, ((List.range 256).flatMap fun b =>
        (d_list6.drop (rdxStart (fun b => rdxSeen shift s_list n b) b)).take
          (rdxSeen shift s_list i b)).count y = (s_list.take i).count y) :
    let tot := fun b => rdxSeen shift s_list n b
    let xi := s_list[i]'(by omega)
    let bvi := (xi >>> shift) &&& 255#64
    let hbvi_c6 : bvi.toNat < cnt6.length := by
      rw [hcl6]; exact rdxBkt_lt _ _
    let p64 := cnt6[bvi.toNat]'hbvi_c6
    let cnt6' := cnt6.set bvi.toNat (p64 + 1#64)
    let d_list6' := d_list6.set p64.toNat xi
    p64.toNat < d_list6.length ∧
      (∀ k < 256, (cnt6'[k]?.getD 0#64).toNat =
        rdxStart tot k + rdxSeen shift s_list (i + 1) k) ∧
      (∀ y, ((List.range 256).flatMap fun b =>
          (d_list6'.drop (rdxStart tot b)).take (rdxSeen shift s_list (i + 1) b)).count y =
        (s_list.take (i + 1)).count y) := by
  intro tot xi bvi hbvi_c6 p64 cnt6' d_list6'
  have hi_sl : i < s_list.length := by omega
  have hbvi_eq : bvi.toNat = rdxBkt shift xi := rfl
  have hbvi_lt : bvi.toNat < 256 := by rw [hbvi_eq]; exact rdxBkt_lt _ _
  have hp_eq : p64.toNat = rdxStart tot bvi.toNat + rdxSeen shift s_list i bvi.toNat := by
    have h1 := hcnt6 bvi.toNat hbvi_lt
    simpa [p64, List.getElem?_eq_getElem hbvi_c6] using h1
  have hseen_lt : rdxSeen shift s_list i bvi.toNat < tot bvi.toNat := by
    have h1 := rdxSeen_succ shift s_list hi_sl bvi.toNat
    have h2 := rdxSeen_mono shift s_list (by omega : i + 1 ≤ n) hn_sl bvi.toNat
    have h3 : rdxBkt shift (s_list[i]'hi_sl) = bvi.toNat := hbvi_eq.symm
    simp only [h3, ↓reduceIte] at h1; dsimp only [tot]; omega
  have hp_lt_n : p64.toNat < n := by
    have h1 := rdxStart_mono tot (by omega : bvi.toNat + 1 ≤ 256)
    rw [rdxStart_succ, rdxStart_sum_all shift s_list hn_sl] at h1
    omega
  refine ⟨by omega, ?_, ?_⟩
  · intro k hk
    have hpp1 : (p64 + 1#64).toNat = p64.toNat + 1 := by
      rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl,
        Nat.mod_eq_of_lt (by omega)]
    rw [rdxSeen_succ shift s_list hi_sl k]
    by_cases hkb : k = bvi.toNat
    · subst hkb
      dsimp only [cnt6']
      rw [List.getElem?_set_self hbvi_c6, Option.getD_some, hpp1, hp_eq]
      simp [show rdxBkt shift (s_list[i]'hi_sl) = bvi.toNat from hbvi_eq.symm]; omega
    · dsimp only [cnt6']
      rw [List.getElem?_set_ne (Ne.symm hkb), hcnt6 k hk]
      have hne : ¬ (rdxBkt shift (s_list[i]'hi_sl) = k) := by
        intro heq; exact hkb (by simpa [hbvi_eq, xi] using heq.symm)
      dsimp only [tot]; simp [hne]
  · intro y
    have hstep := rdx_flatMap_count_step shift s_list d_list6 hi_lt hn_sl hn_dl y
    dsimp only at hstep
    have hd_eq : d_list6' = d_list6.set
        (rdxStart tot (rdxBkt shift (s_list[i]'hi_sl)) +
          rdxSeen shift s_list i (rdxBkt shift (s_list[i]'hi_sl)))
        (s_list[i]'hi_sl) := by
      change d_list6.set p64.toNat xi = _
      rw [hp_eq, hbvi_eq]
    rw [← hd_eq] at hstep
    rw [hstep, hflat6 y, list_take_succ s_list hi_sl, List.count_append, List.count_singleton]

private theorem fullCoreReprRest_upd_repr (c : FullCfg) (k : FullCoreState)
    (rp : List (BitVec 32)) :
    FullCoreReprRest c { k with repr := rp } = FullCoreReprRest c k := rfl

private theorem fullScrSortRest_upd_sort (c : FullCfg) (sc : FullScratch)
    (ws1 ws sb : List (BitVec 32)) :
    FullScrSortRest c { sc with work_stk1 := ws1, wsort := ws, scratch_buf := sb } =
      FullScrSortRest c sc := rfl

private theorem hdrTailWords_upd_sort (c : FullCfg) (s : FullState)
    (rp ws1 ws sb : List (BitVec 32)) :
    hdrTailWords c
      { s with core := { s.core with repr := rp }
               scratch := { s.scratch with
                 work_stk1 := ws1, wsort := ws, scratch_buf := sb } } =
      hdrTailWords c s := rfl

@[expose] def InsTail (c : FullCfg) (s : FullState) (R : Mem 64 → Prop) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (hdrTailWords c s) ⋆
  FullCoreReprRest c s.core ⋆
  array (t := i32) c.pWsort s.scratch.wsort ⋆
  array (t := i32) c.pScratchBuf s.scratch.scratch_buf ⋆
  FullScrSortRest c s.scratch ⋆ c.pad ⋆ R

theorem fullMem_focus_ins (c : FullCfg) (s : FullState) (R : Mem 64 → Prop)
    (hlen : s.LengthsOk c) :
    (FullMem c s ⋆ R) =
      (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
        array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆
        array64 c.pRepr (packPairs64 s.core.repr) ⋆ InsTail c s R) := by
  have hmx : c.max_vars < 2 * Ref.dimacsBound := c.hmaxv
  unfold Ref.dimacsBound at hmx
  have heven : s.core.repr.length % 2 = 0 := by rw [hlen.core_ok.repr_len]; omega
  have hfit : 4 * s.core.repr.length ≤ 2 ^ 64 := by rw [hlen.core_ok.repr_len]; omega
  unfold FullMem InsTail
  rw [fullCoreArrays_focus_repr, fullScratchArrays_focus_sort,
    array32_eq_array64_pack c.pRepr s.core.repr heven hfit]
  ac_rfl

theorem fullMem_unfocus_ins (c : FullCfg) (s : FullState) (R : Mem 64 → Prop)
    {ws1 : List (BitVec 32)} {rk : List (BitVec 64)}
    (hrk : rk.length = c.max_vars) :
    (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
      array (t := i32) c.pWorkStk1 ws1 ⋆
      array64 c.pRepr rk ⋆ InsTail c s R) =
    (FullMem c { s with core := { s.core with repr := unpackPairs32 rk }
                        scratch := { s.scratch with work_stk1 := ws1 } } ⋆ R) := by
  have hmx : c.max_vars < 2 * Ref.dimacsBound := c.hmaxv
  unfold Ref.dimacsBound at hmx
  have h64 : 8 * rk.length ≤ 2 ^ 64 := by rw [hrk]; omega
  unfold FullMem InsTail
  rw [fullCoreArrays_focus_repr, fullScratchArrays_focus_sort,
    array64_eq_array32_unpack c.pRepr rk h64,
    fullCoreReprRest_upd_repr,
    fullScrSortRest_upd_sort c s.scratch ws1 s.scratch.wsort s.scratch.scratch_buf,
    hdrTailWords_upd_sort c s (unpackPairs32 rk) ws1 s.scratch.wsort s.scratch.scratch_buf]
  ac_rfl

@[expose] def RdxTail (c : FullCfg) (s : FullState) (R : Mem 64 → Prop) : Mem 64 → Prop :=
  array (t := i32) (c.pScratchBuf + 2048#64) (s.scratch.scratch_buf.drop 512) ⋆
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (hdrTailWords c s) ⋆
  FullCoreReprRest c s.core ⋆ FullScrSortRest c s.scratch ⋆ c.pad ⋆ R

theorem fullMem_focus_radix (c : FullCfg) (s : FullState) (R : Mem 64 → Prop)
    (hlen : s.LengthsOk c) (hcap : 512 ≤ c.scratch_cap) :
    (FullMem c s ⋆ R) =
      ((array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
         array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆
         array64 c.pRepr (packPairs64 s.core.repr)) ⋆
        (array64 c.pWsort (packPairs64 s.scratch.wsort) ⋆
         array64 c.pScratchBuf (packPairs64 (s.scratch.scratch_buf.take 512)) ⋆
         RdxTail c s R)) := by
  have hmx : c.max_vars < 2 * Ref.dimacsBound := c.hmaxv
  have hsc : c.scratch_cap < Ref.dimacsBound := c.hscr
  unfold Ref.dimacsBound at hmx hsc
  have he_rp : s.core.repr.length % 2 = 0 := by rw [hlen.core_ok.repr_len]; omega
  have hf_rp : 4 * s.core.repr.length ≤ 2 ^ 64 := by rw [hlen.core_ok.repr_len]; omega
  have he_ws : s.scratch.wsort.length % 2 = 0 := by rw [hlen.scratch_ok.wsort_len]; omega
  have hf_ws : 4 * s.scratch.wsort.length ≤ 2 ^ 64 := by rw [hlen.scratch_ok.wsort_len]; omega
  have hsb_len : 512 ≤ s.scratch.scratch_buf.length := by
    rw [hlen.scratch_ok.scratch_buf_len]; exact hcap
  have hsb_fit : 4 * s.scratch.scratch_buf.length ≤ 2 ^ 64 := by
    rw [hlen.scratch_ok.scratch_buf_len]; omega
  unfold FullMem RdxTail
  rw [fullCoreArrays_focus_repr, fullScratchArrays_focus_sort,
    array32_eq_array64_pack c.pRepr s.core.repr he_rp hf_rp,
    array32_eq_array64_pack c.pWsort s.scratch.wsort he_ws hf_ws,
    array32_prefix256_focus c.pScratchBuf s.scratch.scratch_buf hsb_len hsb_fit]
  ac_rfl

theorem fullMem_unfocus_radix (c : FullCfg) (s : FullState) (R : Mem 64 → Prop)
    (hlen : s.LengthsOk c) (hcap : 512 ≤ c.scratch_cap)
    {ws1 : List (BitVec 32)} {rk wsr cnt : List (BitVec 64)}
    (hrk : rk.length = c.max_vars) (hws : wsr.length = c.max_vars) (hcnt : cnt.length = 256) :
    (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
      array (t := i32) c.pWorkStk1 ws1 ⋆
      array64 c.pRepr rk ⋆
      array64 c.pWsort wsr ⋆
      array64 c.pScratchBuf cnt ⋆ RdxTail c s R) =
    (FullMem c
      { s with core := { s.core with repr := unpackPairs32 rk }
               scratch := { s.scratch with
                 work_stk1 := ws1, wsort := unpackPairs32 wsr,
                 scratch_buf := unpackPairs32 cnt ++ s.scratch.scratch_buf.drop 512 } } ⋆ R) := by
  have hmx : c.max_vars < 2 * Ref.dimacsBound := c.hmaxv
  have hsc : c.scratch_cap < Ref.dimacsBound := c.hscr
  unfold Ref.dimacsBound at hmx hsc
  have h64_rp : 8 * rk.length ≤ 2 ^ 64 := by rw [hrk]; omega
  have h64_ws : 8 * wsr.length ≤ 2 ^ 64 := by rw [hws]; omega
  have hsb_len : 512 ≤ s.scratch.scratch_buf.length := by
    rw [hlen.scratch_ok.scratch_buf_len]; exact hcap
  have hsb_fit : 4 * s.scratch.scratch_buf.length ≤ 2 ^ 64 := by
    rw [hlen.scratch_ok.scratch_buf_len]; omega
  have hsb_eq :
      (array64 c.pScratchBuf cnt ⋆
        array (t := i32) (c.pScratchBuf + 2048#64) (s.scratch.scratch_buf.drop 512)) =
      array (t := i32) c.pScratchBuf (unpackPairs32 cnt ++ s.scratch.scratch_buf.drop 512) :=
    array32_prefix256_replace c.pScratchBuf s.scratch.scratch_buf cnt hsb_len hcnt hsb_fit
  let sb' := unpackPairs32 cnt ++ s.scratch.scratch_buf.drop 512
  unfold FullMem RdxTail
  rw [fullCoreArrays_focus_repr, fullScratchArrays_focus_sort,
    array64_eq_array32_unpack c.pRepr rk h64_rp,
    array64_eq_array32_unpack c.pWsort wsr h64_ws,
    fullCoreReprRest_upd_repr,
    fullScrSortRest_upd_sort c s.scratch ws1 (unpackPairs32 wsr) sb',
    hdrTailWords_upd_sort c s (unpackPairs32 rk) ws1 (unpackPairs32 wsr) sb']
  change _ =
    (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
      array64 (c.hdr + 32) (hdrTailWords c s) ⋆
      (array (t := i32) c.pRepr (unpackPairs32 rk) ⋆ FullCoreReprRest c s.core) ⋆
      (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
        array (t := i32) c.pWorkStk1 ws1 ⋆
        array (t := i32) c.pWsort (unpackPairs32 wsr) ⋆
        array (t := i32) c.pScratchBuf sb' ⋆
        FullScrSortRest c s.scratch) ⋆ c.pad ⋆ R)
  rw [← hsb_eq]
  ac_rfl

@[expose] def SiftTail (c : FullCfg) (s : FullState) (R : Mem 64 → Prop) : Mem 64 → Prop :=
  array (t := i32) c.pWsort s.scratch.wsort ⋆
  array (t := i32) c.pScratchBuf s.scratch.scratch_buf ⋆
  FullScrSortRest c s.scratch ⋆
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (hdrTailWords c s) ⋆ FullCoreArrays c s.core ⋆ c.pad ⋆ R

theorem fullMem_focus_qs_ws1 (c : FullCfg) (s : FullState) (R : Mem 64 → Prop) :
    (FullMem c s ⋆ R) =
      (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
        array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆ SiftTail c s R) := by
  unfold FullMem SiftTail
  rw [fullScratchArrays_focus_sort]
  ac_rfl

theorem fullMem_focus_qs_ws1_upd (c : FullCfg) (s : FullState) (R : Mem 64 → Prop)
    (ws1 : List (BitVec 32)) :
    (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1 } } ⋆ R) =
      (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
        array (t := i32) c.pWorkStk1 ws1 ⋆ SiftTail c s R) := by
  rw [fullMem_focus_qs_ws1]
  rfl

/-! ## 2. Shared Pack & Copy WP Helpers -/

theorem sort_ana_pack_wp_var {Γ : Env} {Q : Post []} {X : XPost} {c : FullCfg}
    {s : FullState} {n : BitVec 64} {Frame : Mem 64 → Prop} {rk0 : List (BitVec 64)}
    {m : Mem 64} {next : Tup Val [i64] → Expr Val Cont []}
    (hlen : s.LengthsOk c) (hn_cv : n.toNat ≤ s.core.cur_vars)
    (hrk0 : rk0.length = c.max_vars)
    (hcov0 : ∀ k < n.toNat, (s.scratch.work_stk1[k]?.getD 0#32).toNat < s.core.cur_vars)
    (hm : (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
      array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆ array64 c.pRepr rk0 ⋆ Frame) m)
    (hnext : ∀ rk1 m1, rk1.length = c.max_vars →
      (∀ k < n.toNat, (rk1[k]?.getD 0#64).setWidth 32 = s.scratch.work_stk1[k]?.getD 0#32) →
      (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
        array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆ array64 c.pRepr rk1 ⋆ Frame) m1 →
      wp Γ Q X (next (n, ())) m1) :
    let cv := BitVec.ofNat 64 s.core.cur_vars
    wp Γ Q X
      (.group (sig := [[i64]]) (fun Js => .cons (fun p =>
        .let_ { sig := [i64, i64], code := .cmp .ult i64 .bool (by decide),
                args := (.var p.fst, .var n, ()) } fun p_1 =>
        .jnz (.var p_1.fst)
          (.let_ { sig := [i64, i64], code := .mul i64,
                   args := (.var p.fst, .imm 4, ()) } fun p_2 =>
           .let_ { sig := [i64, i64], code := .add i64,
                   args := (.var c.pWorkStk1, .var p_2.fst, ()) } fun p_3 =>
           .load i32 (.var p_3.fst) fun ld =>
           .group (sig := [[i32]]) (fun _Js_1 => .cons (fun p_4 =>
             .let_ { sig := [i64, i64], code := .mul i64,
                     args := (.var p.fst, .imm 8, ()) } fun p_5 =>
             .let_ { sig := [i64, i64], code := .add i64,
                     args := (.var c.pRepr, .var p_5.fst, ()) } fun p_6 =>
             .let_ { sig := [i32], code := .zext 32 64, args := (.var p_4.fst, ()) } fun p_7 =>
             .let_ { sig := [i32], code := .sext 32 64, args := (.imm 32, ()) } fun p_8 =>
             .let_ { sig := [i64, i64], code := .shl i64,
                     args := (.var p_7.fst, .var p_8.fst, ()) } fun p_9 =>
             .let_ { sig := [i32], code := .zext 32 64, args := (.var ld, ()) } fun p_10 =>
             .let_ { sig := [i64, i64], code := .or i64,
                     args := (.var p_9.fst, .var p_10.fst, ()) } fun p_11 =>
             .store (.var p_11.fst) (.var p_6.fst)
             (.let_ { sig := [i64, i64], code := .add i64,
                      args := (.var p.fst, .imm 1, ()) } fun p =>
              .jump Js.fst (.var p.fst, ()))) .nil)
             fun Js =>
             .let_ { sig := [i32], code := .zext 32 64, args := (.var ld, ()) } fun p =>
             .let_ { sig := [i64, i64], code := .cmp .ult i64 .bool (by decide),
                     args := (.var p.fst, .var cv, ()) } fun p =>
             .jnz (.var p.fst)
               (.let_ { sig := [i32], code := .zext 32 64, args := (.var ld, ()) } fun p =>
                .let_ { sig := [i64, i64], code := .mul i64,
                        args := (.var p.fst, .imm 4, ()) } fun p =>
                .let_ { sig := [i64, i64], code := .add i64,
                        args := (.var c.pQStamp, .var p.fst, ()) } fun p =>
                .load i32 (.var p.fst) fun ld => .jump Js.fst (.var ld, ()))
               (.jump Js.fst (.imm 0, ())))
          (next p)) .nil)
        fun Js => .jump Js.fst (.imm 0, ())) m := by
  have hmaxv : c.max_vars < 2 * Ref.dimacsBound := c.hmaxv
  unfold Ref.dimacsBound at hmaxv
  have hcv_le := hlen.core_ok.cur_vars_le
  have hqs_len := hlen.scratch_ok.q_stamp_len
  have hna_len := hlen.scratch_ok.work_stk1_len
  have hn_max : n.toNat ≤ c.max_vars := by omega
  let ana0 := s.scratch.work_stk1
  refine wp_loop_inv
    (fun (i, ()) m1 => ∃ rk1 : List (BitVec 64),
      rk1.length = c.max_vars ∧ i.toNat ≤ n.toNat ∧
      (∀ k < i.toNat, (rk1[k]?.getD 0#64).setWidth 32 = ana0[k]?.getD 0#32) ∧
      (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
        array (t := i32) c.pWorkStk1 ana0 ⋆ array64 c.pRepr rk1 ⋆ Frame) m1)
    (fun (i, ()) _ => n.toNat - i.toNat)
    (fun Jp hJp => by
      c0_hsteps_nogrp
      exact hJp (0#64, ()) m
        ⟨rk0, hrk0, Nat.zero_le _, fun _ hk => by
          rw [show (0#64 : BitVec 64).toNat = 0 from rfl] at hk; omega, hm⟩)
    (fun Jp (i, ()) m1 ⟨rk1, hrk1, hi_le, hpk1, hm1⟩ ihp => ?_)
  rw [Blocks.get_here]
  c0_hsteps_nogrp
  · have hi_lt : i.toNat < n.toNat := by c0_bound
    have hi_ana : i.toNat < ana0.length := by dsimp [ana0]; omega
    have hi_rk1 : i.toNat < rk1.length := by rw [hrk1]; omega
    have hip1 : (i + 1#64).toNat = i.toNat + 1 := by bv_omega
    c0_hsteps_nogrp
    refine wp_join_group (fun (_ : Tup Val [i32]) m2 => m1 = m2) ?_ ?_
    · intro _ ⟨q, ⟨⟩⟩ m2 hm2
      rcases hm2 with rfl
      rw [Blocks.get_here]
      c0_hsteps_nogrp
      refine ihp (i + 1#64, ()) _ (by dsimp only; omega)
        ⟨rk1.set i.toNat (packPair64 (ana0[i.toNat]'hi_ana) q), by simp [hrk1],
          by rw [hip1]; omega, by rw [hip1]; exact pack_rk_step hi_ana hi_rk1 q hpk1, ?_⟩
      have hmem_eq :
          (array64 c.pRepr (rk1.set i.toNat (packPair64 (ana0[i.toNat]'hi_ana) q)) ⋆
            (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
              (array (t := i32) c.pWorkStk1 ana0 ⋆ (Frame ⋆ emp)))) =
          (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
            array (t := i32) c.pWorkStk1 ana0 ⋆
            array64 c.pRepr (rk1.set i.toNat (packPair64 (ana0[i.toNat]'hi_ana) q)) ⋆
            Frame) := by
        rw [sep_emp Frame]; ac_rfl
      exact hmem_eq ▸ hm
    · intro Jq hJq
      let av := ana0[i.toNat]'hi_ana
      have hav_cv : av.toNat < s.core.cur_vars := by
        have h1 := hcov0 i.toNat hi_lt
        rwa [List.getElem?_eq_getElem hi_ana, Option.getD_some] at h1
      have hav_qs : (BitVec.setWidth 64 av).toNat < s.scratch.q_stamp.length := by
        rw [zext_toNat _ (by decide), hqs_len]; omega
      c0_hsteps_nogrp
      · exact hJq _ m1 rfl
      · exact hJq _ m1 rfl
  · have hneq_nat : i.toNat = n.toNat := by omega
    have hneq : i = n := BitVec.eq_of_toNat_eq hneq_nat
    rw [hneq_nat] at hpk1
    rw [hneq]
    exact hnext rk1 m1 hrk1 hpk1 hm1

theorem sort_ana_pack_wp {Γ : Env} {Q : Post []} {X : XPost} {c : FullCfg}
    {s : FullState} {n : BitVec 64} {Frame : Mem 64 → Prop} {rk0 : List (BitVec 64)}
    {m : Mem 64} {next : Expr Val Cont []}
    (hlen : s.LengthsOk c) (hn_cv : n.toNat ≤ s.core.cur_vars)
    (hrk0 : rk0.length = c.max_vars)
    (hcov0 : ∀ k < n.toNat, (s.scratch.work_stk1[k]?.getD 0#32).toNat < s.core.cur_vars)
    (hm : (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
      array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆ array64 c.pRepr rk0 ⋆ Frame) m)
    (hnext : ∀ rk1 m1, rk1.length = c.max_vars →
      (∀ k < n.toNat, (rk1[k]?.getD 0#64).setWidth 32 = s.scratch.work_stk1[k]?.getD 0#32) →
      (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
        array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆ array64 c.pRepr rk1 ⋆ Frame) m1 →
      wp Γ Q X next m1) :
    let cv := BitVec.ofNat 64 s.core.cur_vars
    wp Γ Q X
      (.group (sig := [[i64]]) (fun Js => .cons (fun p =>
        .let_ { sig := [i64, i64], code := .cmp .ult i64 .bool (by decide),
                args := (.var p.fst, .var n, ()) } fun p_1 =>
        .jnz (.var p_1.fst)
          (.let_ { sig := [i64, i64], code := .mul i64,
                   args := (.var p.fst, .imm 4, ()) } fun p_2 =>
           .let_ { sig := [i64, i64], code := .add i64,
                   args := (.var c.pWorkStk1, .var p_2.fst, ()) } fun p_3 =>
           .load i32 (.var p_3.fst) fun ld =>
           .group (sig := [[i32]]) (fun _Js_1 => .cons (fun p_4 =>
             .let_ { sig := [i64, i64], code := .mul i64,
                     args := (.var p.fst, .imm 8, ()) } fun p_5 =>
             .let_ { sig := [i64, i64], code := .add i64,
                     args := (.var c.pRepr, .var p_5.fst, ()) } fun p_6 =>
             .let_ { sig := [i32], code := .zext 32 64, args := (.var p_4.fst, ()) } fun p_7 =>
             .let_ { sig := [i32], code := .sext 32 64, args := (.imm 32, ()) } fun p_8 =>
             .let_ { sig := [i64, i64], code := .shl i64,
                     args := (.var p_7.fst, .var p_8.fst, ()) } fun p_9 =>
             .let_ { sig := [i32], code := .zext 32 64, args := (.var ld, ()) } fun p_10 =>
             .let_ { sig := [i64, i64], code := .or i64,
                     args := (.var p_9.fst, .var p_10.fst, ()) } fun p_11 =>
             .store (.var p_11.fst) (.var p_6.fst)
             (.let_ { sig := [i64, i64], code := .add i64,
                      args := (.var p.fst, .imm 1, ()) } fun p =>
              .jump Js.fst (.var p.fst, ()))) .nil)
             fun Js =>
             .let_ { sig := [i32], code := .zext 32 64, args := (.var ld, ()) } fun p =>
             .let_ { sig := [i64, i64], code := .cmp .ult i64 .bool (by decide),
                     args := (.var p.fst, .var cv, ()) } fun p =>
             .jnz (.var p.fst)
               (.let_ { sig := [i32], code := .zext 32 64, args := (.var ld, ()) } fun p =>
                .let_ { sig := [i64, i64], code := .mul i64,
                        args := (.var p.fst, .imm 4, ()) } fun p =>
                .let_ { sig := [i64, i64], code := .add i64,
                        args := (.var c.pQStamp, .var p.fst, ()) } fun p =>
                .load i32 (.var p.fst) fun ld => .jump Js.fst (.var ld, ()))
               (.jump Js.fst (.imm 0, ())))
          next) .nil)
        fun Js => .jump Js.fst (.imm 0, ())) m :=
  sort_ana_pack_wp_var (next := fun _ => next) hlen hn_cv hrk0 hcov0 hm hnext

theorem sort_ana_copy_wp {Γ : Env} {Q : Post []} {X : XPost} {c : FullCfg}
    {s : FullState} {n : BitVec 64} {src_ptr : BitVec 64} {src_list : List (BitVec 64)}
    {Frame : Mem 64 → Prop} {m : Mem 64}
    (hlen : s.LengthsOk c) (hn_cv : n.toNat ≤ s.core.cur_vars)
    (hsl : src_list.length = c.max_vars)
    (hm : (array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆
      array64 src_ptr src_list ⋆ Frame) m)
    (hdone : ∀ ana3 m3, ana3.length = 2 * c.max_vars →
      (∀ j < n.toNat, ana3[j]? = some ((src_list[j]?.getD 0#64).setWidth 32)) →
      (∀ j, n.toNat ≤ j → ana3[j]? = s.scratch.work_stk1[j]?) →
      (array (t := i32) c.pWorkStk1 ana3 ⋆ array64 src_ptr src_list ⋆ Frame) m3 →
      Q () m3) :
    wp Γ Q X
      (.group (sig := [[i64]]) (fun Js => .cons (fun p =>
        .let_ { sig := [i64, i64], code := .cmp .ult i64 .bool (by decide),
                args := (.var p.fst, .var n, ()) } fun p_3 =>
        .jnz (.var p_3.fst)
          (.let_ { sig := [i64, i64], code := .mul i64,
                   args := (.var p.fst, .imm 4, ()) } fun p_4 =>
           .let_ { sig := [i64, i64], code := .add i64,
                   args := (.var c.pWorkStk1, .var p_4.fst, ()) } fun p_5 =>
           .let_ { sig := [i64, i64], code := .mul i64,
                   args := (.var p.fst, .imm 8, ()) } fun p_6 =>
           .let_ { sig := [i64, i64], code := .add i64,
                   args := (.var src_ptr, .var p_6.fst, ()) } fun p_7 =>
           .load i64 (.var p_7.fst) fun ld =>
           .let_ { sig := [i64], code := .trunc 64 32, args := (.var ld, ()) } fun p_8 =>
           .store (.var p_8.fst) (.var p_5.fst)
           (.let_ { sig := [i64, i64], code := .add i64,
                    args := (.var p.fst, .imm 1, ()) } fun p =>
            .jump Js.fst (.var p.fst, ())))
          (.ret ())) .nil)
        fun Js => .jump Js.fst (.imm 0, ())) m := by
  have hmaxv : c.max_vars < 2 * Ref.dimacsBound := c.hmaxv
  unfold Ref.dimacsBound at hmaxv
  have hcv_le := hlen.core_ok.cur_vars_le
  have hna_len := hlen.scratch_ok.work_stk1_len
  have hn_max : n.toNat ≤ c.max_vars := by omega
  let ana0 := s.scratch.work_stk1
  refine wp_loop_inv
    (fun (k, ()) m3 => ∃ ana3 : List (BitVec 32),
      ana3.length = 2 * c.max_vars ∧ k.toNat ≤ n.toNat ∧
      (∀ j < k.toNat, ana3[j]? = some ((src_list[j]?.getD 0#64).setWidth 32)) ∧
      (∀ j, k.toNat ≤ j → ana3[j]? = ana0[j]?) ∧
      (array (t := i32) c.pWorkStk1 ana3 ⋆ array64 src_ptr src_list ⋆ Frame) m3)
    (fun (k, ()) _ => n.toNat - k.toNat)
    (fun Jc hJc => by
      c0_hsteps_nogrp
      exact hJc (0#64, ()) m ⟨ana0, hna_len, Nat.zero_le _,
        fun _ hj => by rw [show (0#64 : BitVec 64).toNat = 0 from rfl] at hj; omega,
        fun _ _ => rfl, hm⟩)
    (fun Jc (k, ()) m3 ⟨ana3, hana3, hk_le, hcp3, htl3, hm3⟩ ihc => ?_)
  rw [Blocks.get_here]
  c0_hsteps_nogrp
  · have hk_lt : k.toNat < n.toNat := by c0_bound
    have hk_sl : k.toNat < src_list.length := by rw [hsl]; omega
    have hk_ana3 : k.toNat < ana3.length := by rw [hana3]; omega
    have hkp1 : (k + 1#64).toNat = k.toNat + 1 := by bv_omega
    c0_hsteps_nogrp
    refine ihc (k + 1#64, ()) _ (by dsimp only; omega)
      ⟨ana3.set k.toNat ((src_list[k.toNat]'hk_sl).setWidth 32), by simp [hana3],
        by rw [hkp1]; omega,
        by rw [hkp1]; exact copy_ana_step hk_sl hk_ana3 hcp3,
        fun j hj => by
          rw [hkp1] at hj
          rw [List.getElem?_set_ne (by omega)]
          exact htl3 j (by omega), ?_⟩
    rw [sep_assoc, ← sep_emp Frame]; exact hm
  · have hkeq : k.toNat = n.toNat := by omega
    rw [hkeq] at hcp3 htl3
    c0_hsteps_nogrp
    exact hdone ana3 m3 hana3 hcp3 htl3 hm3

/-! ## 3. 4-Pass LSD Radix Sort Branch (`n ≥ 32`, `scratch_cap ≥ 512`) -/

private theorem sort_ana_radix_finish_cont {Q : Post []} {c : FullCfg}
    {s : FullState} {n : BitVec 64} {R : Mem 64 → Prop}
    {rk1 s_list d_list cnt2 : List (BitVec 64)} {s_arr d_arr : Val i64} {sir : Bool}
    {ana3 : List (BitVec 32)} {m3 : Mem 64}
    (hlen : s.LengthsOk c) (hn_cv : n.toNat ≤ s.core.cur_vars)
    (hcap : 512 ≤ c.scratch_cap)
    (hcv_le : s.core.cur_vars ≤ c.max_vars)
    (hna_len : s.scratch.work_stk1.length = 2 * c.max_vars)
    (hsb_len : s.scratch.scratch_buf.length = c.scratch_cap)
    (hsa : s_arr = if sir then c.pRepr else c.pWsort)
    (hda : d_arr = if sir then c.pWsort else c.pRepr)
    (hsl : s_list.length = c.max_vars) (hdl : d_list.length = c.max_vars)
    (hcl : cnt2.length = 256) (hrk1 : rk1.length = c.max_vars)
    (hpk1 : ∀ k < n.toNat,
      BitVec.setWidth 32 (rk1[k]?.getD 0#64) = s.scratch.work_stk1[k]?.getD 0#32)
    (hpm_s : (s_list.take n.toNat).Perm (rk1.take n.toNat))
    (hcov0 : ∀ k < n.toNat, (s.scratch.work_stk1[k]?.getD 0#32).toNat < s.core.cur_vars)
    (hQ : ∀ ws1' repr' wsort' sbuf' m',
      ws1'.length = 2 * c.max_vars → repr'.length = 2 * c.max_vars →
      wsort'.length = 2 * c.max_vars → sbuf'.length = c.scratch_cap →
      (ws1'.take n.toNat).Perm (s.scratch.work_stk1.take n.toNat) →
      (∀ k, n.toNat ≤ k → ws1'[k]? = s.scratch.work_stk1[k]?) →
      (∀ k < n.toNat, (ws1'[k]?.getD 0#32).toNat < s.core.cur_vars) →
      (FullMem c { s with core := { s.core with repr := repr' }
                          scratch := { s.scratch with
                            work_stk1 := ws1', wsort := wsort', scratch_buf := sbuf' } } ⋆ R)
        m' → Q () m')
    (hana3 : ana3.length = 2 * c.max_vars)
    (hcp3 : ∀ k < n.toNat, ana3[k]? = some (BitVec.setWidth 32 (s_list[k]?.getD 0#64)))
    (htl3 : ∀ k, n.toNat ≤ k → ana3[k]? = s.scratch.work_stk1[k]?)
    (hm3 : (array (t := i32) c.pWorkStk1 ana3 ⋆ array64 s_arr s_list ⋆
        (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
          array64 d_arr d_list ⋆ array64 c.pScratchBuf cnt2 ⋆ RdxTail c s R)) m3) :
    Q () m3 := by
  have hm3_un : (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
      array (t := i32) c.pWorkStk1 ana3 ⋆
      array64 s_arr s_list ⋆ array64 d_arr d_list ⋆
      array64 c.pScratchBuf cnt2 ⋆ RdxTail c s R) m3 := by
    have heq : (array (t := i32) c.pWorkStk1 ana3 ⋆ array64 s_arr s_list ⋆
        (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
          array64 d_arr d_list ⋆ array64 c.pScratchBuf cnt2 ⋆ RdxTail c s R)) =
      (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆ array (t := i32) c.pWorkStk1 ana3 ⋆
        array64 s_arr s_list ⋆ array64 d_arr d_list ⋆
        array64 c.pScratchBuf cnt2 ⋆ RdxTail c s R) := by ac_rfl
    exact heq ▸ hm3
  obtain ⟨hpm_end, hcov_end⟩ := ana_copy_perm_cov s.scratch.work_stk1 ana3 rk1 s_list
    (by omega) (by rw [hana3, hna_len]) (by rw [hrk1]; omega)
    (by rw [hsl, hrk1]) hpk1 hpm_s hcp3 hcov0
  cases sir
  · simp only [Bool.false_eq_true, ↓reduceIte] at hsa hda
    subst hsa; subst hda
    have hm_fin : (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
        array (t := i32) c.pWorkStk1 ana3 ⋆
        array64 c.pRepr d_list ⋆ array64 c.pWsort s_list ⋆
        array64 c.pScratchBuf cnt2 ⋆ RdxTail c s R) m3 := by
      have heq : (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
          array (t := i32) c.pWorkStk1 ana3 ⋆
          array64 c.pWsort s_list ⋆ array64 c.pRepr d_list ⋆
          array64 c.pScratchBuf cnt2 ⋆ RdxTail c s R) =
        (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
          array (t := i32) c.pWorkStk1 ana3 ⋆
          array64 c.pRepr d_list ⋆ array64 c.pWsort s_list ⋆
          array64 c.pScratchBuf cnt2 ⋆ RdxTail c s R) := by ac_rfl
      exact heq ▸ hm3_un
    rw [fullMem_unfocus_radix c s R hlen hcap hdl hsl hcl] at hm_fin
    exact hQ ana3 (unpackPairs32 d_list) (unpackPairs32 s_list)
      (unpackPairs32 cnt2 ++ s.scratch.scratch_buf.drop 512) m3
      hana3 (by rw [unpackPairs32_length, hdl]) (by rw [unpackPairs32_length, hsl])
      (by rw [List.length_append, unpackPairs32_length, hcl, List.length_drop, hsb_len]; omega)
      hpm_end htl3 hcov_end hm_fin
  · simp only [↓reduceIte] at hsa hda
    subst hsa; subst hda
    have hm_fin := hm3_un
    rw [fullMem_unfocus_radix c s R hlen hcap hsl hdl hcl] at hm_fin
    exact hQ ana3 (unpackPairs32 s_list) (unpackPairs32 d_list)
      (unpackPairs32 cnt2 ++ s.scratch.scratch_buf.drop 512) m3
      hana3 (by rw [unpackPairs32_length, hsl]) (by rw [unpackPairs32_length, hdl])
      (by rw [List.length_append, unpackPairs32_length, hcl, List.length_drop, hsb_len]; omega)
      hpm_end htl3 hcov_end hm_fin

theorem sort_ana_radix_wp {Γ : Env} {Q : Post []} {X : XPost} {c : FullCfg}
    {s : FullState} {n : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (hlen : s.LengthsOk c) (hn_cv : n.toNat ≤ s.core.cur_vars)
    (hn_ge32 : 32 ≤ n.toNat) (hcap : 512 ≤ c.scratch_cap)
    (hcov0 : ∀ k < n.toNat, (s.scratch.work_stk1[k]?.getD 0#32).toNat < s.core.cur_vars)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ ws1' repr' wsort' sbuf' m',
      ws1'.length = 2 * c.max_vars → repr'.length = 2 * c.max_vars →
      wsort'.length = 2 * c.max_vars → sbuf'.length = c.scratch_cap →
      (ws1'.take n.toNat).Perm (s.scratch.work_stk1.take n.toNat) →
      (∀ k, n.toNat ≤ k → ws1'[k]? = s.scratch.work_stk1[k]?) →
      (∀ k < n.toNat, (ws1'[k]?.getD 0#32).toNat < s.core.cur_vars) →
      (FullMem c { s with core := { s.core with repr := repr' }
                          scratch := { s.scratch with
                            work_stk1 := ws1', wsort := wsort', scratch_buf := sbuf' } } ⋆ R)
        m' → Q () m') :
    Func.wp Γ full_sort_ana_qs_m6_body (c.hdr, n, ()) m Q X := by
  obtain hok := hlen.core_ok
  obtain hsok := hlen.scratch_ok
  have hmaxv : c.max_vars < 2 * Ref.dimacsBound := c.hmaxv
  have hscr_bd : c.scratch_cap < Ref.dimacsBound := c.hscr
  unfold Ref.dimacsBound at hmaxv hscr_bd
  have hcv_le := hok.cur_vars_le
  have hna_len : s.scratch.work_stk1.length = 2 * c.max_vars := hsok.work_stk1_len
  have hrp_len : s.core.repr.length = 2 * c.max_vars := hok.repr_len
  have hws_len : s.scratch.wsort.length = 2 * c.max_vars := hsok.wsort_len
  have hsb_len : s.scratch.scratch_buf.length = c.scratch_cap := hsok.scratch_buf_len
  have hn_gt1 : ¬ (n ≤ 1#64) := by c0_bound
  have hn_le_cv : ¬ ((BitVec.ofNat 64 s.core.cur_vars) < n) := by c0_bound
  have hn_nlt32 : ¬ (n < 32#64) := by c0_bound
  have hcap_ge : 512#64 ≤ BitVec.ofNat 64 c.scratch_cap := by
    change 512 ≤ (BitVec.ofNat 64 c.scratch_cap).toNat
    rw [bv64_ofNat_toNat (by omega)]; exact hcap
  unfold Func.wp full_sort_ana_qs_m6_body
  dsimp only
  c0_hsteps_nogrp
  let ana0 := s.scratch.work_stk1
  let rk0 := packPairs64 s.core.repr
  let wsr0 := packPairs64 s.scratch.wsort
  let cnt0 := packPairs64 (s.scratch.scratch_buf.take 512)
  have hrk0_len : rk0.length = c.max_vars := by
    dsimp [rk0]; rw [packPairs64_length, hrp_len]; omega
  have hwsr0_len : wsr0.length = c.max_vars := by
    dsimp [wsr0]; rw [packPairs64_length, hws_len]; omega
  have hcnt0_len : cnt0.length = 256 := by
    have h512 : 512 ≤ s.scratch.scratch_buf.length := by rw [hsb_len]; exact hcap
    dsimp [cnt0]; rw [packPairs64_length, List.length_take_of_le h512]
  have hm_rdx := hm
  rw [fullMem_focus_radix c s R hlen hcap] at hm_rdx
  refine sort_ana_pack_wp_var hlen hn_cv hrk0_len hcov0 hm_rdx fun rk1 m1 hrk1 hpk1 hm1 => ?_
  have hm1_full : (FullMem c
      { s with core := { s.core with repr := unpackPairs32 rk1 }
               scratch := { s.scratch with
                 work_stk1 := s.scratch.work_stk1
                 wsort := unpackPairs32 wsr0
                 scratch_buf :=
                   unpackPairs32 cnt0 ++ s.scratch.scratch_buf.drop 512 } } ⋆ R) m1 := by
    rw [← fullMem_unfocus_radix c s R hlen hcap hrk1 hwsr0_len hcnt0_len]
    dsimp only [wsr0, cnt0]
    have heq : ((array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
        array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆ array64 c.pRepr rk1) ⋆
        (array64 c.pWsort (packPairs64 s.scratch.wsort) ⋆
          array64 c.pScratchBuf (packPairs64 (s.scratch.scratch_buf.take 512)) ⋆
          RdxTail c s R)) =
      (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
        array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆ array64 c.pRepr rk1 ⋆
        array64 c.pWsort (packPairs64 s.scratch.wsort) ⋆
        array64 c.pScratchBuf (packPairs64 (s.scratch.scratch_buf.take 512)) ⋆
        RdxTail c s R) := by ac_rfl
    exact heq ▸ hm1
  c0_hsteps_nogrp
  clear hm1_full
  dsimp only
  refine wp_loop_inv (ts := [i64, i64, i64, i64])
    (fun (_iv, s_arr, d_arr, shift, ()) m2 =>
      ∃ (src_is_repr : Bool) (s_list d_list cnt2 : List (BitVec 64)),
        s_arr = (if src_is_repr then c.pRepr else c.pWsort) ∧
        d_arr = (if src_is_repr then c.pWsort else c.pRepr) ∧
        s_list.length = c.max_vars ∧ d_list.length = c.max_vars ∧
        cnt2.length = 256 ∧ 32 ≤ shift.toNat ∧ shift.toNat ≤ 64 ∧ shift.toNat % 8 = 0 ∧
        (s_list.take n.toNat).Perm (rk1.take n.toNat) ∧
        (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
          array (t := i32) c.pWorkStk1 ana0 ⋆
          array64 s_arr s_list ⋆ array64 d_arr d_list ⋆
          array64 c.pScratchBuf cnt2 ⋆ RdxTail c s R) m2)
    (fun (_iv, _s_arr, _d_arr, shift, ()) _ => 64 - shift.toNat)
    ?_ ?_
  · intro Jo hJo
    c0_hsteps_nogrp
    have hm1_r : (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
        array (t := i32) c.pWorkStk1 ana0 ⋆
        array64 c.pRepr rk1 ⋆ array64 c.pWsort wsr0 ⋆
        array64 c.pScratchBuf cnt0 ⋆ RdxTail c s R) m1 := by
      dsimp only [ana0, wsr0, cnt0]
      have heq : ((array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
          array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆ array64 c.pRepr rk1) ⋆
          (array64 c.pWsort (packPairs64 s.scratch.wsort) ⋆
            array64 c.pScratchBuf (packPairs64 (s.scratch.scratch_buf.take 512)) ⋆
            RdxTail c s R)) =
        (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
          array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆
          array64 c.pRepr rk1 ⋆ array64 c.pWsort (packPairs64 s.scratch.wsort) ⋆
          array64 c.pScratchBuf (packPairs64 (s.scratch.scratch_buf.take 512)) ⋆
          RdxTail c s R) := by ac_rfl
      exact heq ▸ hm1
    exact hJo (n, c.pRepr, c.pWsort, 32#64, ()) m1
      ⟨true, rk1, wsr0, cnt0, rfl, rfl, hrk1, hwsr0_len, hcnt0_len,
        by decide, by decide, by decide, List.Perm.refl _, hm1_r⟩
  intro Jo ⟨_iv, s_arr, d_arr, shift, ⟨⟩⟩ m2
    ⟨sir, s_list, d_list, cnt2, hsa, hda, hsl, hdl, hcl, hsh_ge, hsh_le, hsh_m8, hpm_s, hm2⟩ iho
  rw [Blocks.get_here]
  dsimp only
  c0_hsteps_nogrp
  · have hsh_lt : shift.toNat < 64 := by c0_bound
    have hshp8 : (shift + 8#64).toNat = shift.toNat + 8 := by bv_omega
    c0_hsteps_nogrp
    refine wp_loop_inv (ts := [i64])
      (fun (b, ()) m3 => ∃ cnt3 : List (BitVec 64),
        cnt3.length = 256 ∧ b.toNat ≤ 256 ∧
        (∀ k < b.toNat, cnt3[k]? = some 0#64) ∧
        (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
          array (t := i32) c.pWorkStk1 ana0 ⋆
          array64 s_arr s_list ⋆ array64 d_arr d_list ⋆
          array64 c.pScratchBuf cnt3 ⋆ RdxTail c s R) m3)
      (fun (b, ()) _ => 256 - b.toNat)
      (fun Jz hJz => by
        c0_hsteps_nogrp
        exact hJz (0#64, ()) m2
          ⟨cnt2, hcl, Nat.zero_le _,
            fun _ hk => False.elim (Nat.not_lt_zero _ hk), hm2⟩)
      (fun Jz (b, ()) m3 ⟨cnt3, hcl3, hb_le, hzero3, hm3⟩ ihz => ?_)
    rw [Blocks.get_here]
    c0_hsteps_nogrp
    · have hb_lt : b.toNat < 256 := by c0_bound
      have hb_c3 : b.toNat < cnt3.length := by rw [hcl3]; exact hb_lt
      have hbp1 : (b + 1#64).toNat = b.toNat + 1 := by bv_omega
      c0_hsteps_nogrp
      have hzero3' : ∀ k < b.toNat + 1, (cnt3.set b.toNat 0#64)[k]? = some 0#64 := by
        intro k hk
        by_cases hkb : k = b.toNat
        · subst hkb; exact List.getElem?_set_self hb_c3
        · rw [List.getElem?_set_ne (Ne.symm hkb)]; exact hzero3 k (by omega)
      refine ihz (b + 1#64, ()) _ (by dsimp only; rw [hbp1]; omega)
        ⟨cnt3.set b.toNat 0#64, by simp [hcl3], by rw [hbp1]; omega,
          by rw [hbp1]; exact hzero3', ?_⟩
      have hmem_eq :
          (array64 c.pScratchBuf (cnt3.set b.toNat 0#64) ⋆
            (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
              (array (t := i32) c.pWorkStk1 ana0 ⋆
                (array64 s_arr s_list ⋆ (array64 d_arr d_list ⋆ (RdxTail c s R ⋆ emp)))))) =
          (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
            array (t := i32) c.pWorkStk1 ana0 ⋆
            array64 s_arr s_list ⋆ array64 d_arr d_list ⋆
            array64 c.pScratchBuf (cnt3.set b.toNat 0#64) ⋆ RdxTail c s R) := by
        rw [sep_emp (RdxTail c s R)]; ac_rfl
      exact hmem_eq ▸ hm
    · -- Histogram `i = 0 .. n`
      c0_hsteps_nogrp
      refine wp_loop_inv (ts := [i64, i64, i64])
        (fun (i, _lo, _hi, ()) m4 => ∃ cnt4 : List (BitVec 64),
          cnt4.length = 256 ∧ i.toNat ≤ n.toNat ∧
          (∀ k < 256,
            (cnt4[k]?.getD 0#64).toNat = rdxSeen shift.toNat s_list i.toNat k) ∧
          (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
            array (t := i32) c.pWorkStk1 ana0 ⋆
            array64 s_arr s_list ⋆ array64 d_arr d_list ⋆
            array64 c.pScratchBuf cnt4 ⋆ RdxTail c s R) m4)
        (fun (i, _lo, _hi, ()) _ => n.toNat - i.toNat)
        (fun Jh hJh => by
          c0_hsteps_nogrp
          have hb_eq : b.toNat = 256 := by
            have h := ‹¬ b.toNat < (256#64).toNat›
            rw [show (256#64 : BitVec 64).toNat = 256 from rfl] at h
            omega
          exact hJh (0#64, 256#64, 0#64, ()) m3
            ⟨cnt3, hcl3, Nat.zero_le _, fun k hk => by
              rw [show (0#64 : BitVec 64).toNat = 0 from rfl, rdxSeen_zero,
                hzero3 k (by omega)]; rfl,
              hm3⟩)
        (fun Jh (i, lo, hi, ()) m4 ⟨cnt4, hcl4, hi_le, hhist4, hm4⟩ ihh => ?_)
      rw [Blocks.get_here]
      c0_hsteps_nogrp
      · have hi_lt : i.toNat < n.toNat := by c0_bound
        have hi_sl : i.toNat < s_list.length := by rw [hsl]; omega
        have hip1 : (i + 1#64).toNat = i.toNat + 1 := by bv_omega
        have hsh_mod : shift.toNat % 64 = shift.toNat := Nat.mod_eq_of_lt hsh_lt
        let xi := s_list[i.toNat]'hi_sl
        let bvi := (xi >>> shift.toNat) &&& 255#64
        have hbvi_c4 : bvi.toNat < cnt4.length := by
          rw [hcl4]; exact rdxBkt_lt shift.toNat xi
        have hbvi_mod : (xi >>> (shift.toNat % 64) &&& 255#64).toNat < cnt4.length := by
          dsimp only [xi]; rw [hsh_mod]; exact hbvi_c4
        have hhist4' := rdx_hist_step_inv hi_sl hcl4 hi_lt (by omega) hhist4
        let cnt4' := cnt4.set bvi.toNat ((cnt4[bvi.toNat]'hbvi_c4) + 1#64)
        c0_hsteps_nogrp
        refine wp_join_group
          (fun (_ : Tup Val [i64]) m5 =>
            (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
              array (t := i32) c.pWorkStk1 ana0 ⋆
              array64 s_arr s_list ⋆ array64 d_arr d_list ⋆
              array64 c.pScratchBuf cnt4' ⋆ RdxTail c s R) m5)
          ?_ ?_
        · intro _ ⟨lo', ⟨⟩⟩ m5 hm5
          rw [Blocks.get_here]
          c0_hsteps_nogrp
          refine wp_join_group
            (fun (_ : Tup Val [i64]) m6 =>
              (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
                array (t := i32) c.pWorkStk1 ana0 ⋆
                array64 s_arr s_list ⋆ array64 d_arr d_list ⋆
                array64 c.pScratchBuf cnt4' ⋆ RdxTail c s R) m6)
            ?_ ?_
          · intro _ ⟨hi', ⟨⟩⟩ m6 hm6
            rw [Blocks.get_here]
            c0_hsteps_nogrp
            exact ihh (i + 1#64, lo', hi', ()) m6 (by dsimp only; rw [hip1]; omega)
              ⟨cnt4', by simp [cnt4', hcl4], by rw [hip1]; omega,
                by rw [hip1]; exact hhist4', hm6⟩
          · intro _ hJhi
            c0_hsteps_nogrp
            · exact hJhi (_, ()) m5 hm5
            · exact hJhi (_, ()) m5 hm5
        · intro _ hJlo
          rw [sep_emp (RdxTail c s R)] at hm
          simp only [hsh_mod] at hm
          have hm_lo :
              (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
                array (t := i32) c.pWorkStk1 ana0 ⋆
                array64 s_arr s_list ⋆ array64 d_arr d_list ⋆
                array64 c.pScratchBuf cnt4' ⋆ RdxTail c s R) m := by
            have hmem_eq :
                (array64 c.pScratchBuf cnt4' ⋆
                  (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
                    (array (t := i32) c.pWorkStk1 ana0 ⋆
                      (array64 s_arr s_list ⋆ (array64 d_arr d_list ⋆ RdxTail c s R))))) =
                (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
                  array (t := i32) c.pWorkStk1 ana0 ⋆
                  array64 s_arr s_list ⋆ array64 d_arr d_list ⋆
                  array64 c.pScratchBuf cnt4' ⋆ RdxTail c s R) := by ac_rfl
            exact hmem_eq ▸ hm
          c0_hsteps_nogrp
          · exact hJlo (_, ()) m hm_lo
          · exact hJlo (_, ()) m hm_lo
      · -- `if (lo != hi)` prefix sum + scatter + swap (inside `Expr.group`)
        refine wp_join_group (ts := [i64, i64, i64, i64])
          (fun (_iv', s_arr', d_arr', _b', ()) m_next =>
            ∃ (sir' : Bool) (s_list' d_list' cnt' : List (BitVec 64)),
              s_arr' = (if sir' then c.pRepr else c.pWsort) ∧
              d_arr' = (if sir' then c.pWsort else c.pRepr) ∧
              s_list'.length = c.max_vars ∧ d_list'.length = c.max_vars ∧
              cnt'.length = 256 ∧
              (s_list'.take n.toNat).Perm (rk1.take n.toNat) ∧
              (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
                array (t := i32) c.pWorkStk1 ana0 ⋆
                array64 s_arr' s_list' ⋆ array64 d_arr' d_list' ⋆
                array64 c.pScratchBuf cnt' ⋆ RdxTail c s R) m_next)
          ?_ ?_
        · intro _ ⟨iv', s_arr', d_arr', _b', ⟨⟩⟩ m_next
            ⟨sir', s_list', d_list', cnt', hsa', hda', hsl', hdl', hcl', hpm_s', hm_next⟩
          rw [Blocks.get_here]
          dsimp only
          c0_hsteps_nogrp
          exact iho (iv', s_arr', d_arr', shift + 8#64, ()) m_next
            (by dsimp only; rw [hshp8]; omega)
            ⟨sir', s_list', d_list', cnt', hsa', hda', hsl', hdl', hcl',
              by rw [hshp8]; omega, by rw [hshp8]; omega,
              by rw [hshp8, Nat.add_mod_right]; exact hsh_m8, hpm_s', hm_next⟩
        intro Jsw hJsw
        c0_hsteps_nogrp
        · -- `lo != hi`: prefix sum + scatter + swap
          let tot : Nat → Nat := fun b => rdxSeen shift.toNat s_list n.toNat b
          have htot_eq : ∀ k < 256, (cnt4[k]?.getD 0#64).toNat = tot k := by
            intro k hk; have hneq : i.toNat = n.toNat := by omega
            simpa [tot, hneq] using hhist4 k hk
          c0_hsteps_nogrp
          refine wp_loop_inv (ts := [i64, i64])
            (fun (b, pos, ()) m5 => ∃ cnt5 : List (BitVec 64),
              cnt5.length = 256 ∧ b.toNat ≤ 256 ∧ pos.toNat = rdxStart tot b.toNat ∧
              (∀ k < b.toNat, (cnt5[k]?.getD 0#64).toNat = rdxStart tot k) ∧
              (∀ k, b.toNat ≤ k → k < 256 → (cnt5[k]?.getD 0#64).toNat = tot k) ∧
              (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
                array (t := i32) c.pWorkStk1 ana0 ⋆
                array64 s_arr s_list ⋆ array64 d_arr d_list ⋆
                array64 c.pScratchBuf cnt5 ⋆ RdxTail c s R) m5)
            (fun (b, _pos, ()) _ => 256 - b.toNat)
            (fun Jpr hJpr => by
              c0_hsteps_nogrp
              exact hJpr (0#64, 0#64, ()) m4
                ⟨cnt4, hcl4, Nat.zero_le _, rfl,
                  fun _ hk => False.elim (Nat.not_lt_zero _ hk),
                  fun k _ hk => htot_eq k hk, hm4⟩)
            (fun Jpr (b, pos, ()) m5
              ⟨cnt5, hcl5, hb_le, hpos5, hpr5, htl5, hm5⟩ ihpr => ?_)
          rw [Blocks.get_here]
          c0_hsteps_nogrp
          · have hb_lt : b.toNat < 256 := by c0_bound
            have hb_c5 : b.toNat < cnt5.length := by rw [hcl5]; exact hb_lt
            have hbp1 : (b + 1#64).toNat = b.toNat + 1 := by bv_omega
            have hcb_eq : (cnt5[b.toNat]'hb_c5).toNat = tot b.toNat := by
              have h1 := htl5 b.toNat (Nat.le_refl _) hb_lt
              simpa [List.getElem?_eq_getElem hb_c5] using h1
            have hpos_sum_le : rdxStart tot (b.toNat + 1) ≤ n.toNat := by
              have h1 := rdxStart_mono tot (by omega : b.toNat + 1 ≤ 256)
              rwa [rdxStart_sum_all shift.toNat s_list (by rw [hsl]; omega)] at h1
            have hpos_p : (pos + cnt5[b.toNat]'hb_c5).toNat = rdxStart tot (b.toNat + 1) := by
              rw [BitVec.toNat_add, hpos5, hcb_eq, ← rdxStart_succ,
                Nat.mod_eq_of_lt (by omega : rdxStart tot (b.toNat + 1) < 2 ^ 64)]
            c0_hsteps_nogrp
            refine ihpr (b + 1#64, pos + cnt5[b.toNat]'hb_c5, ()) _
              (by dsimp only; rw [hbp1]; omega)
              ⟨cnt5.set b.toNat pos, by simp [hcl5], by rw [hbp1]; omega,
                by rw [hbp1]; exact hpos_p,
                fun k hk => by
                  by_cases hkb : k = b.toNat
                  · subst hkb; rw [List.getElem?_set_self hb_c5, Option.getD_some, hpos5]
                  · rw [List.getElem?_set_ne (Ne.symm hkb)]; exact hpr5 k (by omega),
                fun k hk1 hk2 => by
                  rw [List.getElem?_set_ne (by omega)]; exact htl5 k (by omega) hk2, ?_⟩
            rw [sep_emp (RdxTail c s R)] at hm
            rw [show (array64 c.pScratchBuf (cnt5.set b.toNat pos) ⋆
                  (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
                    (array (t := i32) c.pWorkStk1 ana0 ⋆
                      (array64 s_arr s_list ⋆ (array64 d_arr d_list ⋆ RdxTail c s R))))) =
                (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
                  array (t := i32) c.pWorkStk1 ana0 ⋆
                  array64 s_arr s_list ⋆ array64 d_arr d_list ⋆
                  array64 c.pScratchBuf (cnt5.set b.toNat pos) ⋆ RdxTail c s R)
                from by ac_rfl] at hm
            exact hm
          · -- Scatter loop `i = 0 .. n`
            have hb256 : b.toNat = 256 := by
              have h := ‹¬ b.toNat < (256#64).toNat›
              rw [show (256#64 : BitVec 64).toNat = 256 from rfl] at h
              omega
            c0_hsteps_nogrp
            refine wp_loop_inv (ts := [i64])
              (fun (i, ()) m6 => ∃ (cnt6 d_list6 : List (BitVec 64)),
                cnt6.length = 256 ∧ d_list6.length = c.max_vars ∧ i.toNat ≤ n.toNat ∧
                (∀ k < 256, (cnt6[k]?.getD 0#64).toNat =
                  rdxStart tot k + rdxSeen shift.toNat s_list i.toNat k) ∧
                (∀ y, ((List.range 256).flatMap fun b =>
                    (d_list6.drop (rdxStart tot b)).take
                      (rdxSeen shift.toNat s_list i.toNat b)).count y =
                  (s_list.take i.toNat).count y) ∧
                (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
                  array (t := i32) c.pWorkStk1 ana0 ⋆
                  array64 s_arr s_list ⋆ array64 d_arr d_list6 ⋆
                  array64 c.pScratchBuf cnt6 ⋆ RdxTail c s R) m6)
              (fun (i, ()) _ => n.toNat - i.toNat)
              (fun Jsc hJsc => by
                c0_hsteps_nogrp
                exact hJsc (0#64, ()) m5 ⟨cnt5, d_list, hcl5, hdl, Nat.zero_le _,
                  fun k hk => by
                    rw [show (0#64 : BitVec 64).toNat = 0 from rfl, rdxSeen_zero, Nat.add_zero]
                    exact hpr5 k (by omega),
                  fun y => by
                    rw [show (0#64 : BitVec 64).toNat = 0 from rfl]
                    exact rdx_flatMap_zero_count shift.toNat s_list d_list n.toNat y,
                  hm5⟩)
              (fun Jsc (i, ()) m6 ⟨cnt6, d_list6, hcl6, hdl6, hi_le6, hcnt6, hflat6, hm6⟩
                ihsc => ?_)
            rw [Blocks.get_here]
            c0_hsteps_nogrp
            · have hi_lt6 : i.toNat < n.toNat := by c0_bound
              have hi_sl6 : i.toNat < s_list.length := by rw [hsl]; omega
              have hip1 : (i + 1#64).toNat = i.toNat + 1 := by bv_omega
              have hsh_mod : shift.toNat % 64 = shift.toNat := Nat.mod_eq_of_lt hsh_lt
              have hbvi_c6 :
                  ((s_list[i.toNat]'hi_sl6) >>> (shift.toNat % 64) &&& 255#64).toNat <
                    cnt6.length := by
                rw [hsh_mod, hcl6]; exact rdxBkt_lt _ _
              obtain ⟨hp_dl6, hcnt6', hflat6'⟩ := rdx_scatter_step_inv hi_lt6
                (by rw [hsl]; omega) (by rw [hdl6]; omega) (by omega) hcl6 hcnt6 hflat6
              have hp_dl6_mod :
                  (cnt6[((s_list[i.toNat]'hi_sl6 >>> (shift.toNat % 64) &&& 255#64).toNat)]'
                    hbvi_c6).toNat < d_list6.length := by
                simpa only [hsh_mod, List.getElem?_eq_getElem, Option.getD_some] using hp_dl6
              have hbvi_c6' : ((s_list[i.toNat]'hi_sl6) >>> shift.toNat &&& 255#64).toNat <
                  cnt6.length := by rw [hcl6]; exact rdxBkt_lt _ _
              let bvi6 := (s_list[i.toNat]'hi_sl6) >>> shift.toNat &&& 255#64
              let cnt6' := cnt6.set bvi6.toNat ((cnt6[bvi6.toNat]'hbvi_c6') + 1#64)
              let dl6' := d_list6.set (cnt6[bvi6.toNat]'hbvi_c6').toNat (s_list[i.toNat]'hi_sl6)
              c0_hsteps_nogrp
              rw [sep_emp (RdxTail c s R)] at hm
              simp only [hsh_mod] at hm
              refine ihsc (i + 1#64, ()) _ (by dsimp only; rw [hip1]; omega)
                ⟨cnt6', dl6', by simp [cnt6', hcl6], by simp [dl6', hdl6],
                  by rw [hip1]; omega,
                  by rw [hip1]; exact hcnt6', by rw [hip1]; exact hflat6', ?_⟩
              have hmem_eq :
                  (array64 d_arr dl6' ⋆ (array64 c.pScratchBuf cnt6' ⋆
                    (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
                      (array (t := i32) c.pWorkStk1 ana0 ⋆
                        (array64 s_arr s_list ⋆ RdxTail c s R))))) =
                  (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
                    array (t := i32) c.pWorkStk1 ana0 ⋆
                    array64 s_arr s_list ⋆ array64 d_arr dl6' ⋆
                    array64 c.pScratchBuf cnt6' ⋆ RdxTail c s R) := by ac_rfl
              exact hmem_eq ▸ hm
            · c0_hsteps_nogrp
              have hpass : (d_list6.take n.toNat).Perm (s_list.take n.toNat) := by
                apply radix_pass_perm shift.toNat s_list d_list6
                  (by rw [hsl]; omega) (by rw [hdl6]; omega)
                intro y; have := hflat6 y; have hneq : i.toNat = n.toNat := by omega
                simpa [hneq] using this
              refine hJsw _ _ ⟨!sir, d_list6, s_list, cnt6,
                by cases sir <;> simpa using hda,
                by cases sir <;> simpa using hsa,
                hdl6, hsl, hcl6, hpass.trans hpm_s, ?_⟩
              have heq : (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
                  array (t := i32) c.pWorkStk1 ana0 ⋆
                  array64 s_arr s_list ⋆ array64 d_arr d_list6 ⋆
                  array64 c.pScratchBuf cnt6 ⋆ RdxTail c s R) =
                (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
                  array (t := i32) c.pWorkStk1 ana0 ⋆
                  array64 d_arr d_list6 ⋆ array64 s_arr s_list ⋆
                  array64 c.pScratchBuf cnt6 ⋆ RdxTail c s R) := by ac_rfl
              exact heq ▸ hm6
        · c0_hsteps_nogrp
          exact hJsw _ m4 ⟨sir, s_list, d_list, cnt4, hsa, hda, hsl, hdl, hcl4, hpm_s, hm4⟩
  · have hm2_cp : (array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆
        array64 s_arr s_list ⋆
        (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
          array64 d_arr d_list ⋆ array64 c.pScratchBuf cnt2 ⋆ RdxTail c s R)) m2 := by
      have heq : (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
          array (t := i32) c.pWorkStk1 ana0 ⋆
          array64 s_arr s_list ⋆ array64 d_arr d_list ⋆
          array64 c.pScratchBuf cnt2 ⋆ RdxTail c s R) =
        (array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆
          array64 s_arr s_list ⋆
          (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
            array64 d_arr d_list ⋆ array64 c.pScratchBuf cnt2 ⋆ RdxTail c s R)) := by
        dsimp only [ana0]; ac_rfl
      exact heq ▸ hm2
    exact sort_ana_copy_wp hlen hn_cv hsl hm2_cp fun ana3 m3 hana3 hcp3 htl3 hm3 =>
      sort_ana_radix_finish_cont hlen hn_cv hcap hcv_le hna_len hsb_len hsa hda hsl hdl hcl
        hrk1 hpk1 hpm_s hcov0 hQ hana3 hcp3 htl3 hm3

end

end LeanQbe.T.Examples.Kissat.Proof.Bump
