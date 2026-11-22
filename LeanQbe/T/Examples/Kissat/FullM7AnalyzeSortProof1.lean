module

public import LeanQbe.T.Examples.Kissat.FullM7AnalyzeSortProof0
import LeanQbe.T.Examples.Kissat.FullMinLemmas1
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Wave 4G Proof Shard 1: `full_sort_tmp_sift_m7` & `full_sort_tmp_heap_m7`

M1-clean UNSAT-only `Func.wp` proofs (`public section`, `0 @[expose]`, `0 import all`):
1. `full_sort_tmp_sift_m7_wp`: proves `full_sort_tmp_sift_m7` (with inlined `(lvl, tpos)`
   comparisons) against `Full.FullMinSpecs.fullSortTmpSiftSpec`.
2. `full_sort_tmp_heap_m7_wp`: proves `full_sort_tmp_heap_m7` against `m7SortTmpHeapSpec`,
   establishing `(lvl, tpos)` total order (`Full.fullTmpLe`), `Perm`, slice preservation,
   and `Full.FullSortSliceEq`.
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
open LeanQbe.T.Examples.Kissat.Full.FullMinSpecs
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Full.FullMinTactics
open Kraken.Bedrock2.Test

/-! ## 1. Pure `(lvl, tpos)` Order, `SortSliceEq`, Swap, and `SiftInv` Helpers -/

private theorem m7_tmpLe_refl (lvl tpos : List (BitVec 32)) (a : BitVec 32) :
    tmpLe lvl tpos a a := by
  simp only [tmpLe, tmpLt]; omega

private theorem m7_tmpLt_mono_le {lvl tpos : List (BitVec 32)} {a b : BitVec 32}
    (h : tmpLt lvl tpos a b) : tmpLe lvl tpos a b := by
  simp only [tmpLe, tmpLt] at h ⊢; omega

private theorem m7_tmpLe_trans {lvl tpos : List (BitVec 32)} {a b c : BitVec 32}
    (h1 : tmpLe lvl tpos a b) (h2 : tmpLe lvl tpos b c) : tmpLe lvl tpos a c := by
  simp only [tmpLe, tmpLt] at h1 h2 ⊢; omega

private theorem m7_tmpLe_to_full {lvl tpos : List (BitVec 32)} {a b : BitVec 32}
    (h : tmpLe lvl tpos a b) : Full.fullTmpLe lvl tpos a b := by
  simpa [tmpLe, tmpLt, tmpKey, Full.fullTmpLe, Full.fullTmpLt, Full.fullTmpKey] using h

private theorem m7_tmpLt_of_cmp {lvl tpos : List (BitVec 32)} {a b : BitVec 32}
    (ha_l : a.toNat / 2 < lvl.length) (hb_l : b.toNat / 2 < lvl.length)
    (ha_t : a.toNat / 2 < tpos.length) (hb_t : b.toNat / 2 < tpos.length)
    (hc : (lvl[a.toNat / 2]'ha_l).toNat < (lvl[b.toNat / 2]'hb_l).toNat ∨
      ((lvl[a.toNat / 2]'ha_l).toNat = (lvl[b.toNat / 2]'hb_l).toNat ∧
        (tpos[a.toNat / 2]'ha_t).toNat < (tpos[b.toNat / 2]'hb_t).toNat)) :
    tmpLt lvl tpos a b := by
  simp only [tmpLt, tmpKey, List.getElem?_eq_getElem ha_l, List.getElem?_eq_getElem hb_l,
    List.getElem?_eq_getElem ha_t, List.getElem?_eq_getElem hb_t, Option.getD_some]
  exact hc

private theorem m7_tmpLe_of_ncmp {lvl tpos : List (BitVec 32)} {a b : BitVec 32}
    (ha_l : a.toNat / 2 < lvl.length) (hb_l : b.toNat / 2 < lvl.length)
    (ha_t : a.toNat / 2 < tpos.length) (hb_t : b.toNat / 2 < tpos.length)
    (hnl : ¬ (lvl[b.toNat / 2]'hb_l).toNat < (lvl[a.toNat / 2]'ha_l).toNat)
    (hnt : (lvl[b.toNat / 2]'hb_l).toNat = (lvl[a.toNat / 2]'ha_l).toNat →
      ¬ (tpos[b.toNat / 2]'hb_t).toNat < (tpos[a.toNat / 2]'ha_t).toNat) :
    tmpLe lvl tpos a b := by
  simp only [tmpLe, tmpLt, tmpKey, List.getElem?_eq_getElem ha_l, List.getElem?_eq_getElem hb_l,
    List.getElem?_eq_getElem ha_t, List.getElem?_eq_getElem hb_t, Option.getD_some]
  omega

private theorem m7_sortSliceEq_refl (a : List (BitVec 32)) (hi : Nat) : SortSliceEq a a hi :=
  ⟨fun j h1 h2 => ⟨j, h1, h2, rfl⟩, fun i h1 h2 => ⟨i, h1, h2, rfl⟩⟩

private theorem m7_sortSliceEq_trans {a b c : List (BitVec 32)} {hi : Nat}
    (h1 : SortSliceEq a b hi) (h2 : SortSliceEq b c hi) : SortSliceEq a c hi := by
  refine ⟨fun j hj1 hj2 => ?_, fun i hi1 hi2 => ?_⟩
  · obtain ⟨k, hk1, hk2, hjk⟩ := h1.1 j hj1 hj2
    obtain ⟨i, hi1, hi2, hki⟩ := h2.1 k hk1 hk2
    exact ⟨i, hi1, hi2, hjk.trans hki⟩
  · obtain ⟨k, hk1, hk2, hik⟩ := h2.2 i hi1 hi2
    obtain ⟨j, hj1, hj2, hkj⟩ := h1.2 k hk1 hk2
    exact ⟨j, hj1, hj2, hik.trans hkj⟩

private theorem m7_sortSliceEq_widen {a b : List (BitVec 32)} {lo hi : Nat}
    (hlo : lo ≤ hi) (hsub : SortSliceEq a b lo)
    (hout : ∀ k, lo ≤ k → a[k]? = b[k]?) : SortSliceEq a b hi := by
  refine ⟨fun j hj1 hj2 => ?_, fun i hi1 hi2 => ?_⟩
  · by_cases h : j < lo
    · obtain ⟨i, hi1, hi2, heq⟩ := hsub.1 j hj1 h
      exact ⟨i, hi1, by omega, heq⟩
    · exact ⟨j, hj1, hj2, hout j (by omega)⟩
  · by_cases h : i < lo
    · obtain ⟨j, hj1, hj2, heq⟩ := hsub.2 i hi1 h
      exact ⟨j, hj1, by omega, heq⟩
    · exact ⟨i, hi1, hi2, (hout i (by omega)).symm⟩

private theorem m7_sortSliceEq_to_full {a b : List (BitVec 32)} {hi : Nat}
    (h : SortSliceEq a b hi) : Full.FullSortSliceEq a b hi := h

private def m7SortSwap (xs : List (BitVec 32)) (u v : Nat)
    (hu : u < xs.length) (hv : v < xs.length) : List (BitVec 32) :=
  (xs.set u xs[v]).set v xs[u]

private theorem m7SortSwap_length {xs : List (BitVec 32)} {u v : Nat}
    {hu : u < xs.length} {hv : v < xs.length} :
    (m7SortSwap xs u v hu hv).length = xs.length := by
  simp [m7SortSwap]

private theorem m7SortSwap_perm {xs : List (BitVec 32)} {u v : Nat}
    {hu : u < xs.length} {hv : v < xs.length} :
    (m7SortSwap xs u v hu hv).Perm xs :=
  list_swap_perm xs hu hv

private theorem m7SortSwap_getElem? {xs : List (BitVec 32)} {u v k : Nat}
    {hu : u < xs.length} {hv : v < xs.length} :
    (m7SortSwap xs u v hu hv)[k]? =
      if k = v then some xs[u] else if k = u then some xs[v] else xs[k]? := by
  dsimp only [m7SortSwap]
  by_cases hkv : k = v
  · subst hkv; simp [hv]
  · simp only [hkv, ↓reduceIte, List.getElem?_set_ne (Ne.symm hkv)]
    by_cases hku : k = u
    · subst hku; simp [hu]
    · simp [hku, List.getElem?_set_ne (Ne.symm hku)]

private theorem m7SortSwap_sliceEq {xs : List (BitVec 32)} {hi u v : Nat}
    {hu : u < xs.length} {hv : v < xs.length}
    (hu1 : 1 ≤ u) (hu2 : u < hi) (hv1 : 1 ≤ v) (hv2 : v < hi) :
    SortSliceEq (m7SortSwap xs u v hu hv) xs hi := by
  refine ⟨fun j hj1 hj2 => ?_, fun i hi1 hi2 => ?_⟩
  · rw [m7SortSwap_getElem?]
    by_cases h1 : j = v
    · subst h1; exact ⟨u, hu1, hu2, by simp [List.getElem?_eq_getElem hu]⟩
    · by_cases h2 : j = u
      · subst h2; exact ⟨v, hv1, hv2, by simp [h1, List.getElem?_eq_getElem hv]⟩
      · exact ⟨j, hj1, hj2, by simp [h1, h2]⟩
  · by_cases h1 : i = u
    · subst h1
      refine ⟨v, hv1, hv2, ?_⟩
      rw [m7SortSwap_getElem?, List.getElem?_eq_getElem hu]; simp
    · by_cases h2 : i = v
      · subst h2
        refine ⟨u, hu1, hu2, ?_⟩
        rw [m7SortSwap_getElem?, List.getElem?_eq_getElem hv]; simp [Ne.symm h1]
      · refine ⟨i, hi1, hi2, ?_⟩
        rw [m7SortSwap_getElem?]; simp [h1, h2]

private theorem m7_heap_root_max {lvl tpos tmp : List (BitVec 32)} {lim : Nat}
    (hh : IsMaxHeapFrom lvl tpos tmp 0 lim) :
    ∀ k, k < lim → tmpLe lvl tpos (tmp[1 + k]?.getD 0#32) (tmp[1]?.getD 0#32) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro hk
    rcases k with _ | k'
    · simpa using m7_tmpLe_refl lvl tpos (tmp[1]?.getD 0#32)
    · let p := k' / 2
      have hpr := ih p (by omega) (by omega)
      have hnode := hh p (Nat.zero_le _) (by omega)
      have hchild : tmpLe lvl tpos (tmp[1 + (k' + 1)]?.getD 0#32) (tmp[1 + p]?.getD 0#32) := by
        rcases Nat.mod_two_eq_zero_or_one k' with hm | hm
        · have heq : k' + 1 = 2 * p + 1 := by omega
          simpa [heq] using hnode.1 (by omega)
        · have heq : k' + 1 = 2 * p + 2 := by omega
          simpa [heq] using hnode.2 (by omega)
      exact m7_tmpLe_trans hchild hpr

private def M7SiftInv (lvl tpos tmp_init tmp : List (BitVec 32))
    (r0 lim r : Nat) : Prop :=
  tmp.length = tmp_init.length ∧ tmp.Perm tmp_init ∧
  (∀ k, (k = 0 ∨ 1 + lim ≤ k) → tmp[k]? = tmp_init[k]?) ∧
  SortSliceEq tmp tmp_init (1 + lim) ∧
  (∀ k, 1 ≤ k → k < 1 + lim →
    (tmp[k]?.getD 0#32).toNat / 2 < lvl.length ∧
    (tmp[k]?.getD 0#32).toNat / 2 < tpos.length) ∧
  r < lim ∧ r0 ≤ r ∧
  (∀ i, r0 ≤ i → i < lim → i ≠ r → IsHeapAt lvl tpos tmp i lim) ∧
  (r0 < r → 0 < r ∧
    (2 * r + 1 < lim →
      tmpLe lvl tpos (tmp[1 + (2 * r + 1)]?.getD 0#32)
        (tmp[1 + (r - 1) / 2]?.getD 0#32)) ∧
    (2 * r + 2 < lim →
      tmpLe lvl tpos (tmp[1 + (2 * r + 2)]?.getD 0#32)
        (tmp[1 + (r - 1) / 2]?.getD 0#32)))

private theorem m7SiftInv_done_of_oob {lvl tpos tmp_init tmp : List (BitVec 32)} {r0 lim r : Nat}
    (hi : M7SiftInv lvl tpos tmp_init tmp r0 lim r) (hoob : lim ≤ 2 * r + 1) :
    IsMaxHeapFrom lvl tpos tmp r0 lim := by
  intro i hi1 hi2
  by_cases hir : i = r
  · subst i; exact ⟨fun h => by omega, fun h => by omega⟩
  · exact hi.2.2.2.2.2.2.2.1 i hi1 hi2 hir

private theorem m7SiftInv_done_of_ge {lvl tpos tmp_init tmp : List (BitVec 32)} {r0 lim r ch : Nat}
    (hi : M7SiftInv lvl tpos tmp_init tmp r0 lim r) (_hc : ch < lim)
    (hch_eq : ch = 2 * r + 1 ∨ ch = 2 * r + 2)
    (hge : tmpLe lvl tpos (tmp[1 + ch]?.getD 0#32) (tmp[1 + r]?.getD 0#32))
    (hmax : 2 * r + 2 < lim →
      tmpLe lvl tpos (tmp[1 + (2 * r + 1)]?.getD 0#32) (tmp[1 + ch]?.getD 0#32) ∧
      tmpLe lvl tpos (tmp[1 + (2 * r + 2)]?.getD 0#32) (tmp[1 + ch]?.getD 0#32)) :
    IsMaxHeapFrom lvl tpos tmp r0 lim := by
  intro i hi1 hi2
  by_cases hir : i = r
  · subst i
    constructor
    · intro _
      by_cases h2 : 2 * r + 2 < lim
      · exact m7_tmpLe_trans (hmax h2).1 hge
      · rcases hch_eq with rfl | rfl
        · exact hge
        · omega
    · intro h2; exact m7_tmpLe_trans (hmax h2).2 hge
  · exact hi.2.2.2.2.2.2.2.1 i hi1 hi2 hir

private theorem m7SiftInv_swap {lvl tpos tmp_init tmp : List (BitVec 32)} {r0 lim r ch : Nat}
    (hi : M7SiftInv lvl tpos tmp_init tmp r0 lim r) (hlim_len : 1 + lim ≤ tmp_init.length)
    (hc1 : 2 * r + 1 ≤ ch) (hc2 : ch ≤ 2 * r + 2) (hch_lim : ch < lim)
    (hlt : tmpLt lvl tpos (tmp[1 + r]?.getD 0#32) (tmp[1 + ch]?.getD 0#32))
    (hmax : 2 * r + 2 < lim →
      tmpLe lvl tpos (tmp[1 + (2 * r + 1)]?.getD 0#32) (tmp[1 + ch]?.getD 0#32) ∧
      tmpLe lvl tpos (tmp[1 + (2 * r + 2)]?.getD 0#32) (tmp[1 + ch]?.getD 0#32)) :
    let hlen := hi.1
    let hu : 1 + r < tmp.length := by have := hi.2.2.2.2.2.1; omega
    let hv : 1 + ch < tmp.length := by omega
    M7SiftInv lvl tpos tmp_init (m7SortSwap tmp (1 + r) (1 + ch) hu hv) r0 lim ch := by
  intro hlen hu hv
  let tmp' := m7SortSwap tmp (1 + r) (1 + ch) hu hv
  have hrc_ne : r ≠ ch := by omega
  have hget (idx : Nat) :
      tmp'[idx]?.getD 0#32 =
        if idx = 1 + ch then tmp[1 + r]?.getD 0#32
        else if idx = 1 + r then tmp[1 + ch]?.getD 0#32
        else tmp[idx]?.getD 0#32 := by
    dsimp only [tmp']; rw [m7SortSwap_getElem?]
    by_cases h1 : idx = 1 + ch
    · simp only [h1, ↓reduceIte, List.getElem?_eq_getElem hu, Option.getD_some]
    · by_cases h2 : idx = 1 + r
      · rw [h2]; simp only [show 1 + r ≠ 1 + ch by omega, ↓reduceIte,
          List.getElem?_eq_getElem hv, Option.getD_some]
      · simp only [h1, h2, ↓reduceIte]
  have hpar_ch : (ch - 1) / 2 = r := by omega
  rcases hi with ⟨_, hperm, hout, hseq, hbd, hr_lim, hr0_r, hheap, hgp⟩
  refine ⟨m7SortSwap_length.trans hlen, m7SortSwap_perm.trans hperm, ?_, ?_, ?_, hch_lim,
    by omega, ?_, ?_⟩
  · intro k hk; rw [m7SortSwap_getElem?]
    have h1 : k ≠ 1 + ch := by rcases hk with rfl | h <;> omega
    have h2 : k ≠ 1 + r := by rcases hk with rfl | h <;> omega
    simp only [h1, h2, ↓reduceIte]; exact hout k hk
  · exact m7_sortSliceEq_trans (m7SortSwap_sliceEq (by omega) (by omega) (by omega) (by omega)) hseq
  · intro k hk1 hk2; rw [m7SortSwap_getElem?]
    by_cases h1 : k = 1 + ch
    · simp only [h1, ↓reduceIte]; have := hbd (1 + r) (by omega) (by omega)
      rwa [List.getElem?_eq_getElem hu, Option.getD_some] at this
    · by_cases h2 : k = 1 + r
      · rw [h2]; simp only [show 1 + r ≠ 1 + ch by omega, ↓reduceIte]
        have := hbd (1 + ch) (by omega) (by omega)
        rwa [List.getElem?_eq_getElem hv, Option.getD_some] at this
      · simp only [h1, h2, ↓reduceIte]; exact hbd k hk1 hk2
  · intro i hi1 hi2 hine
    by_cases hir : i = r
    · subst i
      have hrootv : tmp'[1 + r]?.getD 0#32 = tmp[1 + ch]?.getD 0#32 := by
        rw [hget]; simp only [show 1 + r ≠ 1 + ch by omega, ↓reduceIte]
      constructor
      · intro _
        rw [hrootv]
        by_cases hc : 2 * r + 1 = ch
        · rw [hc, hget]; simp only [↓reduceIte]; exact m7_tmpLt_mono_le hlt
        · have h2 : 2 * r + 2 < lim := by omega
          rw [hget]
          simp only [show 1 + (2 * r + 1) ≠ 1 + ch by omega,
            show 1 + (2 * r + 1) ≠ 1 + r by omega, ↓reduceIte]
          exact (hmax h2).1
      · intro h2
        rw [hrootv]
        by_cases hc : 2 * r + 2 = ch
        · rw [hc, hget]; simp only [↓reduceIte]; exact m7_tmpLt_mono_le hlt
        · rw [hget]
          simp only [show 1 + (2 * r + 2) ≠ 1 + ch by omega,
            show 1 + (2 * r + 2) ≠ 1 + r by omega, ↓reduceIte]
          exact (hmax h2).2
    · have hiv : tmp'[1 + i]?.getD 0#32 = tmp[1 + i]?.getD 0#32 := by
        rw [hget]
        simp only [show 1 + i ≠ 1 + ch by omega, show 1 + i ≠ 1 + r by omega, ↓reduceIte]
      have hheap_i := hheap i hi1 hi2 hir
      constructor
      · intro h1
        rw [hiv]
        by_cases hcr : 2 * i + 1 = r
        · have hgt : r0 < r := by omega
          rw [hcr, hget]; simp only [show 1 + r ≠ 1 + ch by omega, ↓reduceIte]
          have hgp' := hgp hgt
          rcases Nat.lt_or_eq_of_le hc1 with _ | hc1_eq
          · have hch2 : ch = 2 * r + 2 := by omega
            rw [hch2]; simpa [show (r - 1) / 2 = i by omega] using hgp'.2.2 (by omega)
          · rw [← hc1_eq]; simpa [show (r - 1) / 2 = i by omega] using hgp'.2.1 (by omega)
        · rw [hget]
          simp only [show 1 + (2 * i + 1) ≠ 1 + ch by omega,
            show 1 + (2 * i + 1) ≠ 1 + r by omega, ↓reduceIte]
          exact hheap_i.1 h1
      · intro h2
        rw [hiv]
        by_cases hcr : 2 * i + 2 = r
        · have hgt : r0 < r := by omega
          rw [hcr, hget]; simp only [show 1 + r ≠ 1 + ch by omega, ↓reduceIte]
          have hgp' := hgp hgt
          rcases Nat.lt_or_eq_of_le hc1 with _ | hc1_eq
          · have hch2 : ch = 2 * r + 2 := by omega
            rw [hch2]; simpa [show (r - 1) / 2 = i by omega] using hgp'.2.2 (by omega)
          · rw [← hc1_eq]; simpa [show (r - 1) / 2 = i by omega] using hgp'.2.1 (by omega)
        · rw [hget]
          simp only [show 1 + (2 * i + 2) ≠ 1 + ch by omega,
            show 1 + (2 * i + 2) ≠ 1 + r by omega, ↓reduceIte]
          exact hheap_i.2 h2
  · intro _; refine ⟨by omega, ?_, ?_⟩
    · intro h1
      have hheap_c := hheap ch (by omega) hch_lim (by omega)
      rw [hget, hget, hpar_ch]
      simp only [show 1 + (2 * ch + 1) ≠ 1 + ch by omega,
        show 1 + (2 * ch + 1) ≠ 1 + r by omega, show 1 + r ≠ 1 + ch by omega, ↓reduceIte]
      exact hheap_c.1 h1
    · intro h2
      have hheap_c := hheap ch (by omega) hch_lim (by omega)
      rw [hget, hget, hpar_ch]
      simp only [show 1 + (2 * ch + 2) ≠ 1 + ch by omega,
        show 1 + (2 * ch + 2) ≠ 1 + r by omega, show 1 + r ≠ 1 + ch by omega, ↓reduceIte]
      exact hheap_c.2 h2

/-! ## 2. `full_sort_tmp_sift_m7_wp` (Inlined `(lvl, tpos)` Sift) -/

theorem full_sort_tmp_sift_m7_wp (Γ : Env) :
    ∀ args m Q X, FullMinSpecs.fullSortTmpSiftSpec args m Q X →
      Func.wp Γ full_sort_tmp_sift_m7_body args m Q X := by
  rintro ⟨tmp_ptr, lvl_ptr, tpos_ptr, start, lim, ⟨⟩⟩ m0 Q X
    ⟨tmp_init, lvl, tpos, R, hst_lt, hlim_len, hlim_60, hbd0, hheap0, hm0, hQ⟩
  unfold Func.wp full_sort_tmp_sift_m7_body
  dsimp only [full_sort_tmp_sift_m7_body]
  let SiftLp : Nat → Tup Val [i64] → Mem 64 → Prop := fun dec (r, ()) m1 =>
    dec = lim.toNat - r.toNat ∧
    ∃ tmp1, M7SiftInv lvl tpos tmp_init tmp1 start.toNat lim.toNat r.toNat ∧
      (array (t := i32) tmp_ptr tmp1 ⋆ array (t := i32) lvl_ptr lvl ⋆
        array (t := i32) tpos_ptr tpos ⋆ R) m1
  refine wp_loop_group (ts := [i64]) SiftLp ?_ ?_
  · rintro J dec ⟨r, ⟨⟩⟩ m1 hJ ⟨rfl, tmp1, hsi, hm1⟩
    rw [Blocks.get_here]
    ml_lets
    have hsi_cp := hsi
    rcases hsi with ⟨htl, hperm, hout, hseq, hbd, hr_lim, hr0_r, hheap, hgp⟩
    have hc1_nat : ((r <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64)) + 1).toNat =
        2 * r.toNat + 1 := by
      have hsh := bv64_shl1_add1_toNat (x := r) (by omega)
      exact hsh
    ml_jnz; refine ⟨fun hch_in => ?_, fun hoob => ?_⟩
    · have hc1_lt : 2 * r.toNat + 1 < lim.toNat := by
        change
          ((r <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64)) + 1).ult lim =
            true at hch_in
        rw [BitVec.ult, decide_eq_true_eq, hc1_nat] at hch_in
        exact hch_in
      let c1 : BitVec 64 := r <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64) + 1
      have hc1_eq : c1.toNat = 2 * r.toNat + 1 := hc1_nat
      have h1c1 : ((1 : BitVec 64) + c1).toNat = 1 + (2 * r.toNat + 1) := by
        have h1 : (1 : BitVec 64).toNat = 1 := rfl
        rw [BitVec.toNat_add, hc1_eq, h1, Nat.mod_eq_of_lt (by omega)]
      have hi1 : ((1 : BitVec 64) + c1).toNat < tmp1.length := by rw [h1c1, htl]; omega
      have hm_tmp : (array (t := i32) tmp_ptr tmp1 ⋆
          (array (t := i32) lvl_ptr lvl ⋆ array (t := i32) tpos_ptr tpos ⋆ R)) m1 :=
        sep_ac hm1
      ml_ld m7_arr_load_i32 hi1 hm_tmp
      let v1 := tmp1[((1 : BitVec 64) + c1).toNat]'hi1
      have hv1_eq : v1 = tmp1[1 + (2 * r.toNat + 1)]'(by rw [htl]; omega) := by
        simp only [v1, h1c1]
      have hv1_bd : v1.toNat / 2 < lvl.length ∧ v1.toNat / 2 < tpos.length := by
        have := hbd (1 + (2 * r.toNat + 1)) (by omega) (by omega)
        rw [List.getElem?_eq_getElem (by rw [htl]; omega), Option.getD_some] at this
        rwa [hv1_eq]
      have h1m : (BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64 =
          (BitVec.signExtend 64 (1 : BitVec 32)).toNat := rfl
      have hv1_sh :
          ((v1.setWidth 64) >>> ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64)).toNat =
            v1.toNat / 2 := by
        rw [h1m]; exact m7_bv64_zext32_ushr1 v1
      have hvb1_l :
          ((v1.setWidth 64) >>> ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64)).toNat <
            lvl.length := by
        rw [hv1_sh]; exact hv1_bd.1
      have hvb1_t :
          ((v1.setWidth 64) >>> ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64)).toNat <
            tpos.length := by
        rw [hv1_sh]; exact hv1_bd.2
      have hm_lvl : (array (t := i32) lvl_ptr lvl ⋆
          (array (t := i32) tmp_ptr tmp1 ⋆ array (t := i32) tpos_ptr tpos ⋆ R)) m1 :=
        sep_ac hm1
      have hm_tp : (array (t := i32) tpos_ptr tpos ⋆
          (array (t := i32) tmp_ptr tmp1 ⋆ array (t := i32) lvl_ptr lvl ⋆ R)) m1 :=
        sep_ac hm1
      ml_ld m7_arr_load_i32 hvb1_l hm_lvl
      ml_ld m7_arr_load_i32 hvb1_t hm_tp
      ml_lets
      let ChJoin : Tup Val [i64, i32, i32, i32] → Mem 64 → Prop :=
        fun (ch, ch_lit, ch_l, ch_t, ()) m2 =>
          m2 = m1 ∧ 2 * r.toNat + 1 ≤ ch.toNat ∧ ch.toNat ≤ 2 * r.toNat + 2 ∧
          ch.toNat < lim.toNat ∧
          ch_lit = tmp1[1 + ch.toNat]?.getD 0#32 ∧
          ch_l = lvl[ch_lit.toNat / 2]?.getD 0#32 ∧
          ch_t = tpos[ch_lit.toNat / 2]?.getD 0#32 ∧
          (2 * r.toNat + 2 < lim.toNat →
            tmpLe lvl tpos (tmp1[1 + (2 * r.toNat + 1)]?.getD 0#32)
              (tmp1[1 + ch.toNat]?.getD 0#32) ∧
            tmpLe lvl tpos (tmp1[1 + (2 * r.toNat + 2)]?.getD 0#32)
              (tmp1[1 + ch.toNat]?.getD 0#32))
      refine wp_join_group (ts := [i64, i32, i32, i32]) ChJoin ?_ ?_
      · rintro _ ⟨ch, ch_lit, ch_l, ch_t, ⟨⟩⟩ m2
          ⟨hm2_eq, hc_lo, hc_hi, hch_lim, hch_lit_q, hch_l_q, hch_t_q, hch_max⟩
        subst m2
        have hch_bd : ch_lit.toNat / 2 < lvl.length ∧ ch_lit.toNat / 2 < tpos.length := by
          rw [hch_lit_q]; exact hbd (1 + ch.toNat) (by omega) (by omega)
        have hch_lit : ch_lit = tmp1[1 + ch.toNat]'(by rw [htl]; omega) := by
          rw [hch_lit_q, List.getElem?_eq_getElem (by rw [htl]; omega), Option.getD_some]
        have hch_l : ch_l = lvl[ch_lit.toNat / 2]'hch_bd.1 := by
          rw [hch_l_q, List.getElem?_eq_getElem hch_bd.1, Option.getD_some]
        have hch_t : ch_t = tpos[ch_lit.toNat / 2]'hch_bd.2 := by
          rw [hch_t_q, List.getElem?_eq_getElem hch_bd.2, Option.getD_some]
        rw [Blocks.get_here]; ml_lets
        have h1r_bv : ((1 : BitVec 64) + r).toNat = 1 + r.toNat := by
          have h1 : (1 : BitVec 64).toNat = 1 := rfl
          rw [BitVec.toNat_add, h1, Nat.mod_eq_of_lt (by omega)]
        have hi_r : ((1 : BitVec 64) + r).toNat < tmp1.length := by rw [h1r_bv, htl]; omega
        ml_ld m7_arr_load_i32 hi_r hm_tmp
        let vr := tmp1[((1 : BitVec 64) + r).toNat]'hi_r
        have hvr_eq : vr = tmp1[1 + r.toNat]'(by rw [htl]; omega) := by simp only [vr, h1r_bv]
        have hvr_bd : vr.toNat / 2 < lvl.length ∧ vr.toNat / 2 < tpos.length := by
          have := hbd (1 + r.toNat) (by omega) (by omega)
          rw [List.getElem?_eq_getElem (by rw [htl]; omega), Option.getD_some] at this
          rwa [hvr_eq]
        have hvr_sh :
            ((vr.setWidth 64) >>> ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64)).toNat =
              vr.toNat / 2 := by
          rw [h1m]; exact m7_bv64_zext32_ushr1 vr
        have hvbr_l :
            ((vr.setWidth 64) >>> ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64)).toNat <
              lvl.length := by
          rw [hvr_sh]; exact hvr_bd.1
        have hvbr_t :
            ((vr.setWidth 64) >>> ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64)).toNat <
              tpos.length := by
          rw [hvr_sh]; exact hvr_bd.2
        ml_ld m7_arr_load_i32 hvbr_l hm_lvl
        ml_ld m7_arr_load_i32 hvbr_t hm_tp
        ml_lets
        let rl := lvl[vr.toNat / 2]'hvr_bd.1
        let rt := tpos[vr.toNat / 2]'hvr_bd.2
        refine wp_join_group (ts := []) (fun () m_sw =>
            m_sw = m1 ∧ (rl.toNat < ch_l.toNat ∨
              (rl.toNat = ch_l.toNat ∧ rt.toNat < ch_t.toNat)))
          ?_ ?_
        · rintro _ ⟨⟩ m_sw ⟨hm_sw, hless⟩
          subst m_sw
          rw [Blocks.get_here]; ml_lets
          have hlt' : tmpLt lvl tpos
              (tmp1[1 + r.toNat]?.getD 0#32) (tmp1[1 + ch.toNat]?.getD 0#32) := by
            rw [List.getElem?_eq_getElem (by rw [htl]; omega),
              List.getElem?_eq_getElem (by rw [htl]; omega), Option.getD_some,
              Option.getD_some, ← hvr_eq, ← hch_lit]
            apply m7_tmpLt_of_cmp hvr_bd.1 hch_bd.1 hvr_bd.2 hch_bd.2
            simpa only [rl, rt, hch_l, hch_t] using hless
          have h1ch_bv : ((1 : BitVec 64) + ch).toNat = 1 + ch.toNat := by
            have h1 : (1 : BitVec 64).toNat = 1 := rfl
            rw [BitVec.toNat_add, h1, Nat.mod_eq_of_lt (by omega)]
          have hi_c : ((1 : BitVec 64) + ch).toNat < tmp1.length := by
            rw [h1ch_bv, htl]; omega
          ml_lets; rw [wp]
          obtain ⟨hok1, hm2⟩ := m7_arr_store_i32 (i := 1 + r) ch_lit hi_r hm_tmp
          refine ⟨hok1, ?_⟩
          ml_lets; rw [wp]
          let tmp1b := tmp1.set ((1 : BitVec 64) + r).toNat ch_lit
          have hi_c' : ((1 : BitVec 64) + ch).toNat < tmp1b.length := by
            simpa [tmp1b] using hi_c
          obtain ⟨hok2, hm3⟩ := m7_arr_store_i32 (i := 1 + ch) vr hi_c' hm2
          refine ⟨hok2, ?_⟩
          let tmp2 := m7SortSwap tmp1 (1 + r.toNat) (1 + ch.toNat)
            (by rw [htl]; omega) (by rw [htl]; omega)
          have hm3' : (array (t := i32) tmp_ptr tmp2 ⋆ array (t := i32) lvl_ptr lvl ⋆
              array (t := i32) tpos_ptr tpos ⋆ R)
              (storeMem (storeMem m1 i32 (tmp_ptr + ((1 : BitVec 64) + r) * 4) ch_lit) i32
                (tmp_ptr + ((1 : BitVec 64) + ch) * 4) vr) := by
            have h3 : (array (t := i32) tmp_ptr tmp2 ⋆ (array (t := i32) lvl_ptr lvl ⋆
                array (t := i32) tpos_ptr tpos ⋆ R))
                (storeMem (storeMem m1 i32 (tmp_ptr + ((1 : BitVec 64) + r) * 4) ch_lit) i32
                  (tmp_ptr + ((1 : BitVec 64) + ch) * 4) vr) := by
              simpa only [tmp2, tmp1b, m7SortSwap, h1r_bv, h1ch_bv, vr, hch_lit] using hm3
            exact sep_ac h3
          exact hJ (lim.toNat - ch.toNat) (ch, ()) _ (by omega)
            ⟨rfl, tmp2, m7SiftInv_swap hsi_cp hlim_len hc_lo hc_hi hch_lim hlt' hch_max, hm3'⟩
        · rintro Jsw hJsw; ml_lets; ml_jnz
          refine ⟨fun hrl_lt => ?_, fun hrl_ge => ?_⟩
          · have hlt_bv : rl.toNat < ch_l.toNat := by
              change BitVec.ult rl ch_l = true at hrl_lt
              rw [BitVec.ult, decide_eq_true_eq] at hrl_lt
              simpa [rl, hch_l, hvr_sh] using hrl_lt
            exact hJsw () m1 ⟨rfl, Or.inl hlt_bv⟩
          · have hrl_nlt : ¬ rl.toNat < ch_l.toNat := by
              change BitVec.ult rl ch_l = false at hrl_ge
              rw [BitVec.ult, decide_eq_false_iff_not] at hrl_ge
              simpa [rl, hch_l, hvr_sh] using hrl_ge
            ml_lets; ml_jnz
            refine ⟨fun hrl_eq => ?_, fun hrl_ne => ?_⟩
            · have hreq : rl.toNat = ch_l.toNat := by
                change (rl == ch_l) = true at hrl_eq
                rw [beq_iff_eq] at hrl_eq
                have := congrArg BitVec.toNat hrl_eq
                simpa [rl, hch_l, hvr_sh] using this
              ml_lets; ml_jnz
              refine ⟨fun hrt_lt => ?_, fun hrt_ge => ?_⟩
              · have hrt_bv : rt.toNat < ch_t.toNat := by
                  change BitVec.ult rt ch_t = true at hrt_lt
                  rw [BitVec.ult, decide_eq_true_eq] at hrt_lt
                  simpa [rt, hch_t, hvr_sh] using hrt_lt
                exact hJsw () m1 ⟨rfl, Or.inr ⟨hreq, hrt_bv⟩⟩
              · have hrt_nlt : ¬ rt.toNat < ch_t.toNat := by
                  change BitVec.ult rt ch_t = false at hrt_ge
                  rw [BitVec.ult, decide_eq_false_iff_not] at hrt_ge
                  simpa [rt, hch_t, hvr_sh] using hrt_ge
                have hge' : tmpLe lvl tpos
                    (tmp1[1 + ch.toNat]?.getD 0#32) (tmp1[1 + r.toNat]?.getD 0#32) := by
                  rw [List.getElem?_eq_getElem (by rw [htl]; omega),
                    List.getElem?_eq_getElem (by rw [htl]; omega), Option.getD_some,
                    Option.getD_some, ← hvr_eq, ← hch_lit]
                  exact m7_tmpLe_of_ncmp hch_bd.1 hvr_bd.1 hch_bd.2 hvr_bd.2
                    (by simpa [rl, hch_l] using hrl_nlt)
                    (fun _ => by simpa [rt, hch_t] using hrt_nlt)
                have hch_eq' : ch.toNat = 2 * r.toNat + 1 ∨ ch.toNat = 2 * r.toNat + 2 := by
                  omega
                ml_lets; rw [wp]
                exact hQ tmp1 m1 htl hperm hout hseq
                  (m7SiftInv_done_of_ge hsi_cp hch_lim hch_eq' hge' hch_max) hm1
            · have hrl_neq : rl.toNat ≠ ch_l.toNat := by
                change (rl == ch_l) = false at hrl_ne
                rw [beq_eq_false_iff_ne] at hrl_ne
                intro hteq
                exact hrl_ne (BitVec.eq_of_toNat_eq (by simpa [rl, hch_l, hvr_sh] using hteq))
              have hge' : tmpLe lvl tpos
                  (tmp1[1 + ch.toNat]?.getD 0#32) (tmp1[1 + r.toNat]?.getD 0#32) := by
                rw [List.getElem?_eq_getElem (by rw [htl]; omega),
                  List.getElem?_eq_getElem (by rw [htl]; omega), Option.getD_some,
                  Option.getD_some, ← hvr_eq, ← hch_lit]
                exact m7_tmpLe_of_ncmp hch_bd.1 hvr_bd.1 hch_bd.2 hvr_bd.2
                  (by simpa [rl, hch_l] using hrl_nlt)
                  (fun h => absurd h (by simpa [rl, hch_l] using hrl_neq))
              have hch_eq' : ch.toNat = 2 * r.toNat + 1 ∨ ch.toNat = 2 * r.toNat + 2 := by
                omega
              ml_lets; rw [wp]
              exact hQ tmp1 m1 htl hperm hout hseq
                (m7SiftInv_done_of_ge hsi_cp hch_lim hch_eq' hge' hch_max) hm1
      · rintro J2 hJ2; ml_lets
        have hc2_bv : (c1 + 1).toNat = 2 * r.toNat + 2 := by
          have h1 : (1 : BitVec 64).toNat = 1 := rfl
          rw [BitVec.toNat_add, hc1_eq, h1, Nat.mod_eq_of_lt (by omega)]
        let l1 := lvl[v1.toNat / 2]'hv1_bd.1
        let t1 := tpos[v1.toNat / 2]'hv1_bd.2
        ml_jnz; refine ⟨fun hc2_lt => ?_, fun hc2_ge => ?_⟩
        · change (c1 + 1).ult lim = true at hc2_lt
          rw [BitVec.ult, decide_eq_true_eq, hc2_bv] at hc2_lt
          have h2c1 : ((1 : BitVec 64) + (c1 + 1)).toNat = 1 + (2 * r.toNat + 2) := by
            have h1 : (1 : BitVec 64).toNat = 1 := rfl
            rw [BitVec.toNat_add, hc2_bv, h1, Nat.mod_eq_of_lt (by omega)]
          have hi2 : ((1 : BitVec 64) + (c1 + 1)).toNat < tmp1.length := by
            rw [h2c1, htl]; omega
          ml_ld m7_arr_load_i32 hi2 hm_tmp
          let v2 := tmp1[((1 : BitVec 64) + (c1 + 1)).toNat]'hi2
          have hv2_eq : v2 = tmp1[1 + (2 * r.toNat + 2)]'(by rw [htl]; omega) := by
            simp only [v2, h2c1]
          have hv2_bd : v2.toNat / 2 < lvl.length ∧ v2.toNat / 2 < tpos.length := by
            have := hbd (1 + (2 * r.toNat + 2)) (by omega) (by omega)
            rw [List.getElem?_eq_getElem (by rw [htl]; omega), Option.getD_some] at this
            rwa [hv2_eq]
          have hv2_sh :
              ((v2.setWidth 64) >>> ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64)).toNat =
                v2.toNat / 2 := by
            rw [h1m]; exact m7_bv64_zext32_ushr1 v2
          have hvb2_l :
              ((v2.setWidth 64) >>> ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64)).toNat <
                lvl.length := by
            rw [hv2_sh]; exact hv2_bd.1
          have hvb2_t :
              ((v2.setWidth 64) >>> ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64)).toNat <
                tpos.length := by
            rw [hv2_sh]; exact hv2_bd.2
          ml_ld m7_arr_load_i32 hvb2_l hm_lvl
          ml_ld m7_arr_load_i32 hvb2_t hm_tp
          ml_lets
          let l2 := lvl[v2.toNat / 2]'hv2_bd.1
          let t2 := tpos[v2.toNat / 2]'hv2_bd.2
          let mkLt : l1.toNat < l2.toNat ∨ (l1.toNat = l2.toNat ∧ t1.toNat < t2.toNat) →
              ChJoin (c1 + 1, v2, l2, t2, ()) m1 := fun h12 => by
            have hlt' : tmpLt lvl tpos
                (tmp1[1 + (2 * r.toNat + 1)]?.getD 0#32)
                (tmp1[1 + (2 * r.toNat + 2)]?.getD 0#32) := by
              rw [List.getElem?_eq_getElem (by rw [htl]; omega),
                List.getElem?_eq_getElem (by rw [htl]; omega), Option.getD_some,
                Option.getD_some, ← hv1_eq, ← hv2_eq]
              exact m7_tmpLt_of_cmp hv1_bd.1 hv2_bd.1 hv1_bd.2 hv2_bd.2 h12
            refine ⟨rfl, by rw [hc2_bv]; omega, by rw [hc2_bv]; omega,
              by rw [hc2_bv]; exact hc2_lt, ?_, ?_, ?_, fun _ => ?_⟩
            · rw [hc2_bv, List.getElem?_eq_getElem (by rw [htl]; omega), Option.getD_some]
              exact hv2_eq
            · rw [List.getElem?_eq_getElem hv2_bd.1, Option.getD_some]
            · rw [List.getElem?_eq_getElem hv2_bd.2, Option.getD_some]
            · rw [hc2_bv]; exact ⟨m7_tmpLt_mono_le hlt', m7_tmpLe_refl _ _ _⟩
          let mkGe : ¬ l1.toNat < l2.toNat →
              (l1.toNat = l2.toNat → ¬ t1.toNat < t2.toNat) →
              ChJoin (c1, v1, l1, t1, ()) m1 := fun hl_nlt ht_nlt => by
            have hge' : tmpLe lvl tpos
                (tmp1[1 + (2 * r.toNat + 2)]?.getD 0#32)
                (tmp1[1 + (2 * r.toNat + 1)]?.getD 0#32) := by
              rw [List.getElem?_eq_getElem (by rw [htl]; omega),
                List.getElem?_eq_getElem (by rw [htl]; omega), Option.getD_some,
                Option.getD_some, ← hv1_eq, ← hv2_eq]
              exact m7_tmpLe_of_ncmp hv2_bd.1 hv1_bd.1 hv2_bd.2 hv1_bd.2
                (by simpa [l1, l2] using hl_nlt)
                (fun h => ht_nlt (by simpa [l1, l2] using h))
            refine ⟨rfl, by rw [hc1_eq]; omega, by rw [hc1_eq]; omega,
              by rw [hc1_eq]; exact hc1_lt, ?_, ?_, ?_, fun _ => ?_⟩
            · rw [hc1_eq, List.getElem?_eq_getElem (by rw [htl]; omega), Option.getD_some]
              exact hv1_eq
            · rw [List.getElem?_eq_getElem hv1_bd.1, Option.getD_some]
            · rw [List.getElem?_eq_getElem hv1_bd.2, Option.getD_some]
            · rw [hc1_eq]; exact ⟨m7_tmpLe_refl _ _ _, hge'⟩
          refine wp_join_group (ts := [i64, i32, i32, i32]) ChJoin ?_ ?_
          · rintro _ ⟨ch, ch_lit, ch_l, ch_t, ⟨⟩⟩ m2 hch
            rw [Blocks.get_here]; ml_lets
            exact hJ2 (ch, ch_lit, ch_l, ch_t, ()) m2 hch
          · rintro Jpick hJpick; ml_lets; ml_jnz
            refine ⟨fun hl_lt => ?_, fun hl_ge => ?_⟩
            · have hl_nat : l1.toNat < l2.toNat := by
                change BitVec.ult l1 l2 = true at hl_lt
                rw [BitVec.ult, decide_eq_true_eq] at hl_lt
                simpa [l1, l2, hv1_sh, hv2_sh] using hl_lt
              exact hJpick (c1 + 1, v2, l2, t2, ()) m1 (mkLt (Or.inl hl_nat))
            · have hl_nlt : ¬ l1.toNat < l2.toNat := by
                change BitVec.ult l1 l2 = false at hl_ge
                rw [BitVec.ult, decide_eq_false_iff_not] at hl_ge
                simpa [l1, l2, hv1_sh, hv2_sh] using hl_ge
              ml_lets; ml_jnz
              refine ⟨fun hl_eq => ?_, fun hl_ne => ?_⟩
              · have hleq : l1.toNat = l2.toNat := by
                  change (l1 == l2) = true at hl_eq
                  rw [beq_iff_eq] at hl_eq
                  have := congrArg BitVec.toNat hl_eq
                  simpa [l1, l2, hv1_sh, hv2_sh] using this
                ml_lets; ml_jnz
                refine ⟨fun ht_lt => ?_, fun ht_ge => ?_⟩
                · have ht_nat : t1.toNat < t2.toNat := by
                    change BitVec.ult t1 t2 = true at ht_lt
                    rw [BitVec.ult, decide_eq_true_eq] at ht_lt
                    simpa [t1, t2, hv1_sh, hv2_sh] using ht_lt
                  exact hJpick (c1 + 1, v2, l2, t2, ()) m1 (mkLt (Or.inr ⟨hleq, ht_nat⟩))
                · have ht_nlt : ¬ t1.toNat < t2.toNat := by
                    change BitVec.ult t1 t2 = false at ht_ge
                    rw [BitVec.ult, decide_eq_false_iff_not] at ht_ge
                    simpa [t1, t2, hv1_sh, hv2_sh] using ht_ge
                  exact hJpick (c1, v1, l1, t1, ()) m1 (mkGe hl_nlt (fun _ => ht_nlt))
              · have hl_neq : l1.toNat ≠ l2.toNat := by
                  change (l1 == l2) = false at hl_ne
                  rw [beq_eq_false_iff_ne] at hl_ne
                  intro hteq
                  exact hl_ne (BitVec.eq_of_toNat_eq
                    (by simpa [l1, l2, hv1_sh, hv2_sh] using hteq))
                exact hJpick (c1, v1, l1, t1, ()) m1 (mkGe hl_nlt (fun h => absurd h hl_neq))
        · change (c1 + 1).ult lim = false at hc2_ge
          rw [BitVec.ult, decide_eq_false_iff_not, hc2_bv] at hc2_ge
          ml_lets; apply hJ2
          change ChJoin (c1, v1, l1, t1, ()) m1
          refine ⟨rfl, by rw [hc1_eq]; omega, by rw [hc1_eq]; omega,
            by rw [hc1_eq]; exact hc1_lt, ?_, ?_, ?_, fun h => by omega⟩
          · rw [hc1_eq, List.getElem?_eq_getElem (by rw [htl]; omega), Option.getD_some]
            exact hv1_eq
          · rw [List.getElem?_eq_getElem hv1_bd.1, Option.getD_some]
          · rw [List.getElem?_eq_getElem hv1_bd.2, Option.getD_some]
    · change
        ((r <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64)) + 1).ult lim =
          false at hoob
      rw [BitVec.ult, decide_eq_false_iff_not, hc1_nat] at hoob
      ml_lets; rw [wp]
      exact hQ tmp1 m1 htl hperm hout hseq
        (m7SiftInv_done_of_oob hsi_cp (by omega)) hm1
  · intro J hJ; wp_unfold
    have hsift0 : M7SiftInv lvl tpos tmp_init tmp_init start.toNat lim.toNat start.toNat :=
      ⟨rfl, List.Perm.refl _, fun _ _ => rfl, m7_sortSliceEq_refl _ _, hbd0, hst_lt,
        le_refl _, fun i hi1 hi2 _ => hheap0 i (by omega) hi2,
        fun hlt => absurd hlt (Nat.lt_irrefl _)⟩
    exact hJ (lim.toNat - start.toNat) (start, ()) m0 ⟨rfl, tmp_init, hsift0, hm0⟩

/-! ## 3. `full_sort_tmp_heap_m7_wp` (Standalone Base-Pointer Heapsort) -/

theorem full_sort_tmp_heap_m7_wp (Γ : Env)
    (hSift : ∀ args m Q X, FullMinSpecs.fullSortTmpSiftSpec args m Q X →
      Γ "full_sort_tmp_sift_m7" [i64, i64, i64, i64, i64] [] args m Q X) :
    ∀ args m Q X, m7SortTmpHeapSpec args m Q X →
      Func.wp Γ full_sort_tmp_heap_m7_body args m Q X := by
  rintro ⟨tmp_ptr, lvl_ptr, tpos_ptr, tlen, ⟨⟩⟩ m0 Q X hspec
  obtain ⟨tmp_init, lvl, tpos, R, htlen_le, htlen60, hbd0, hm0, hQ⟩ :=
    m7SortTmpHeapSpec_elim hspec
  dsimp only at htlen_le htlen60 hbd0
  unfold Func.wp full_sort_tmp_heap_m7_body
  dsimp only [full_sort_tmp_heap_m7_body]
  ml_lets; ml_jnz; refine ⟨fun hle2 => ?_, fun hgt2 => ?_⟩
  · have htl2 : tlen.toNat ≤ 2 := by
      change tlen.ule 2#64 = true at hle2
      rw [BitVec.ule, decide_eq_true_eq] at hle2
      have h2n : (2#64 : BitVec 64).toNat = 2 := rfl
      rw [h2n] at hle2; exact hle2
    ml_lets; rw [wp]
    refine hQ tmp_init m0 rfl (List.Perm.refl _) (fun _ => rfl) (fun _ _ => rfl)
      (m7_sortSliceEq_to_full (m7_sortSliceEq_refl _ _)) (fun i j hi hij hj => ?_) hm0
    dsimp only at hj
    have hij' : i = j := by omega
    subst hij'; exact m7_tmpLe_to_full (m7_tmpLe_refl _ _ _)
  · have htl2 : 2 < tlen.toNat := by
      change tlen.ule 2#64 = false at hgt2
      rw [BitVec.ule, decide_eq_false_iff_not] at hgt2
      have : (2#64 : BitVec 64).toNat = 2 := rfl
      rw [this] at hgt2; omega
    let n : BitVec 64 := tlen - 1
    have hn_eq : n.toNat = tlen.toNat - 1 := by
      dsimp only [n]
      have h1 : (1 : BitVec 64).toNat = 1 := rfl
      rw [BitVec.toNat_sub_of_le (by bv_omega), h1]
    have htlen_m1 : (tlen - 1).toNat = tlen.toNat - 1 := hn_eq
    ml_lets
    let Loop1Inv : Nat → Tup Val [i64] → Mem 64 → Prop := fun dec (start, ()) m1 =>
      dec = start.toNat ∧ start.toNat ≤ (tlen.toNat - 1) / 2 ∧
      ∃ tmp1, tmp1.length = tmp_init.length ∧ tmp1.Perm tmp_init ∧
        (∀ k, tlen.toNat ≤ k → tmp1[k]? = tmp_init[k]?) ∧
        (0 < tlen.toNat → tmp1[0]? = tmp_init[0]?) ∧
        SortSliceEq tmp1 tmp_init tlen.toNat ∧
        (∀ k, 1 ≤ k → k < tlen.toNat →
          (tmp1[k]?.getD 0#32).toNat / 2 < lvl.length ∧
          (tmp1[k]?.getD 0#32).toNat / 2 < tpos.length) ∧
        IsMaxHeapFrom lvl tpos tmp1 start.toNat (tlen.toNat - 1) ∧
        (array (t := i32) tmp_ptr tmp1 ⋆ array (t := i32) lvl_ptr lvl ⋆
          array (t := i32) tpos_ptr tpos ⋆ R) m1
    refine wp_loop_group (ts := [i64]) Loop1Inv ?_ ?_
    · rintro J1 dec ⟨start, ⟨⟩⟩ m1 hJ1
        ⟨rfl, hst_le, tmp1, htl1, hperm1, hout1, h01, hseq1, hbd1, hh1, hm1⟩
      rw [Blocks.get_here]; ml_lets
      ml_jnz; refine ⟨fun hst_pos => ?_, fun hst0 => ?_⟩
      · have hst_gt0 : 0 < start.toNat := by c0_cond hst_pos; bv_omega
        have hst_m1 : (start - 1).toNat = start.toNat - 1 := by
          have h1 : (1 : BitVec 64).toNat = 1 := rfl
          rw [BitVec.toNat_sub_of_le (by bv_omega), h1]
        have htl1_ge : tlen.toNat ≤ tmp1.length := htl1 ▸ htlen_le
        ml_lets
        apply wp_call_of_spec; apply hSift
        dsimp only [FullMinSpecs.fullSortTmpSiftSpec, vals, Arg.val]
        refine ⟨tmp1, lvl, tpos, R, by omega, by omega, by omega,
          fun k hk1 hk2 => hbd1 k hk1 (by omega),
          by rw [hst_m1, Nat.sub_add_cancel hst_gt0, htlen_m1]; exact hh1, hm1, ?_⟩
        intro tmp2 m2 htl2' hperm2 hout2 hseq2 hh2 hm2
        have h02 : 0 < tlen.toNat → tmp2[0]? = tmp_init[0]? := fun hp =>
          (hout2 0 (Or.inl rfl)).trans (h01 hp)
        have hseq2' : SortSliceEq tmp2 tmp_init tlen.toNat := by
          rw [htlen_m1, show 1 + (tlen.toNat - 1) = tlen.toNat by omega] at hseq2
          exact m7_sortSliceEq_trans hseq2 hseq1
        have hbd2 : ∀ k, 1 ≤ k → k < tlen.toNat →
            (tmp2[k]?.getD 0#32).toNat / 2 < lvl.length ∧
            (tmp2[k]?.getD 0#32).toNat / 2 < tpos.length := fun k hk1 hk2 => by
          obtain ⟨j, hj1, hj2, hkj⟩ := hseq2'.1 k hk1 hk2
          rw [hkj]; exact hbd0 j hj1 hj2
        exact hJ1 (start - 1).toNat (start - 1, ()) m2 (by rw [hst_m1]; omega)
          ⟨rfl, by rw [hst_m1]; omega, tmp2, htl2'.trans htl1, hperm2.trans hperm1,
            fun k hk => (hout2 k (Or.inr (by omega))).trans (hout1 k hk), h02, hseq2', hbd2,
            by simpa only [htlen_m1] using hh2, hm2⟩
      · have hst_eq0 : start.toNat = 0 := by
          change (0 : BitVec 64).ult start = false at hst0
          rw [BitVec.ult, decide_eq_false_iff_not] at hst0; bv_omega
        rw [hst_eq0] at hh1
        ml_lets
        let Loop2Inv : Nat → Tup Val [i64] → Mem 64 → Prop := fun dec2 (e, ()) m2 =>
          dec2 = e.toNat ∧ 1 ≤ e.toNat ∧ e.toNat ≤ tlen.toNat - 1 ∧
          ∃ tmp2, tmp2.length = tmp_init.length ∧ tmp2.Perm tmp_init ∧
            (∀ k, tlen.toNat ≤ k → tmp2[k]? = tmp_init[k]?) ∧
            (0 < tlen.toNat → tmp2[0]? = tmp_init[0]?) ∧
            SortSliceEq tmp2 tmp_init tlen.toNat ∧
            (∀ k, 1 ≤ k → k < tlen.toNat →
              (tmp2[k]?.getD 0#32).toNat / 2 < lvl.length ∧
              (tmp2[k]?.getD 0#32).toNat / 2 < tpos.length) ∧
            IsMaxHeapFrom lvl tpos tmp2 0 e.toNat ∧
            (∀ j, e.toNat ≤ j → j < tlen.toNat - 1 → ∀ i, i ≤ j →
              tmpLe lvl tpos (tmp2[1 + i]?.getD 0#32) (tmp2[1 + j]?.getD 0#32)) ∧
            (array (t := i32) tmp_ptr tmp2 ⋆ array (t := i32) lvl_ptr lvl ⋆
              array (t := i32) tpos_ptr tpos ⋆ R) m2
        refine wp_loop_group (ts := [i64]) Loop2Inv ?_ ?_
        · rintro J2 dec2 ⟨e, ⟨⟩⟩ m2 hJ2
            ⟨rfl, he_ge1, he_le, tmp2, htl2', hperm2, hout2, h02, hseq2, hbd2, hh2, hsorted2, hm2⟩
          rw [Blocks.get_here]; ml_lets
          ml_jnz; refine ⟨fun he_gt1 => ?_, fun he_le1 => ?_⟩
          · have he_gt1' : 1 < e.toNat := by
              change (1 : BitVec 64).ult e = true at he_gt1
              rw [BitVec.ult, decide_eq_true_eq] at he_gt1
              have h1n : (1 : BitVec 64).toNat = 1 := rfl
              rw [h1n] at he_gt1; exact he_gt1
            let e1 : BitVec 64 := e - 1
            have he1_nat : e1.toNat = e.toNat - 1 := by
              dsimp only [e1]; have h1 : (1 : BitVec 64).toNat = 1 := rfl
              rw [BitVec.toNat_sub_of_le (by bv_omega), h1]
            have h1n : (1 : BitVec 64).toNat = 1 := rfl
            have h1e_bv : ((1 : BitVec 64) + e1).toNat = 1 + e1.toNat := by
              rw [BitVec.toNat_add, h1n, Nat.mod_eq_of_lt (by omega)]
            have htmp2_ge : tlen.toNat ≤ tmp2.length := htl2' ▸ htlen_le
            have hi1 : (1 : BitVec 64).toNat < tmp2.length := by rw [h1n]; omega
            have hie : ((1 : BitVec 64) + e1).toNat < tmp2.length := by rw [h1e_bv]; omega
            have hm2_tmp : (array (t := i32) tmp_ptr tmp2 ⋆
                (array (t := i32) lvl_ptr lvl ⋆ array (t := i32) tpos_ptr tpos ⋆ R)) m2 :=
              sep_ac hm2
            ml_ld m7_arr_load_i32 hi1 hm2_tmp
            ml_ld m7_arr_load_i32 hie hm2_tmp
            ml_lets; rw [wp]
            obtain ⟨hok1, hm3⟩ := m7_arr_store_i32 (i := (1 : BitVec 64))
              (tmp2[((1 : BitVec 64) + e1).toNat]'hie) hi1 hm2_tmp
            refine ⟨hok1, ?_⟩
            ml_lets; rw [wp]
            let tmp2b := tmp2.set (1 : BitVec 64).toNat
              (tmp2[((1 : BitVec 64) + e1).toNat]'hie)
            have hie' : ((1 : BitVec 64) + e1).toNat < tmp2b.length := by
              simpa [tmp2b] using hie
            obtain ⟨hok2, hm4⟩ := m7_arr_store_i32 (i := 1 + e1)
              (tmp2[(1 : BitVec 64).toNat]'hi1) hie' hm3
            refine ⟨hok2, ?_⟩
            have h1_lt2 : 1 < tmp2.length := by omega
            have h1e_lt2 : 1 + e1.toNat < tmp2.length := by omega
            let tmp3 := m7SortSwap tmp2 1 (1 + e1.toNat) h1_lt2 h1e_lt2
            have hm4' : (array (t := i32) tmp_ptr tmp3 ⋆ array (t := i32) lvl_ptr lvl ⋆
                array (t := i32) tpos_ptr tpos ⋆ R)
                (storeMem (storeMem m2 i32 (tmp_ptr + (1 : BitVec 64) * 4)
                  (tmp2[((1 : BitVec 64) + e1).toNat]'hie)) i32
                  (tmp_ptr + ((1 : BitVec 64) + e1) * 4)
                  (tmp2[(1 : BitVec 64).toNat]'hi1)) := by
              have h4 : (array (t := i32) tmp_ptr tmp3 ⋆ (array (t := i32) lvl_ptr lvl ⋆
                  array (t := i32) tpos_ptr tpos ⋆ R))
                  (storeMem (storeMem m2 i32 (tmp_ptr + (1 : BitVec 64) * 4)
                    (tmp2[((1 : BitVec 64) + e1).toNat]'hie)) i32
                    (tmp_ptr + ((1 : BitVec 64) + e1) * 4)
                    (tmp2[(1 : BitVec 64).toNat]'hi1)) := by
                simpa only [tmp3, tmp2b, m7SortSwap, h1n, h1e_bv] using hm4
              exact sep_ac h4
            have hget3 (idx : Nat) : tmp3[idx]?.getD 0#32 =
                if idx = 1 + e1.toNat then tmp2[1]?.getD 0#32
                else if idx = 1 then tmp2[1 + e1.toNat]?.getD 0#32
                else tmp2[idx]?.getD 0#32 := by
              dsimp only [tmp3]; rw [m7SortSwap_getElem?]
              by_cases h1 : idx = 1 + e1.toNat
              · simp only [h1, ↓reduceIte, List.getElem?_eq_getElem h1_lt2, Option.getD_some]
              · by_cases h2 : idx = 1
                · rw [h2]; simp only [show (1 : Nat) ≠ 1 + e1.toNat by omega, ↓reduceIte,
                    List.getElem?_eq_getElem h1e_lt2, Option.getD_some]
                · simp only [h1, h2, ↓reduceIte]
            have htl3 : tmp3.length = tmp_init.length := m7SortSwap_length.trans htl2'
            have h03 : 0 < tlen.toNat → tmp3[0]? = tmp_init[0]? := fun htp => by
              rw [m7SortSwap_getElem?]
              simp only [show 0 ≠ 1 + e1.toNat by omega, show (0 : Nat) ≠ 1 by omega, ↓reduceIte]
              exact h02 htp
            have hseq3 : SortSliceEq tmp3 tmp_init tlen.toNat :=
              m7_sortSliceEq_trans
                (m7SortSwap_sliceEq (hi := tlen.toNat) (le_refl 1) (by omega)
                  (by omega) (by omega))
                hseq2
            have hbd3 : ∀ k, 1 ≤ k → k < tlen.toNat →
                (tmp3[k]?.getD 0#32).toNat / 2 < lvl.length ∧
                (tmp3[k]?.getD 0#32).toNat / 2 < tpos.length := fun k hk1 hk2 => by
              obtain ⟨j, hj1, hj2, hkj⟩ := hseq3.1 k hk1 hk2
              rw [hkj]; exact hbd0 j hj1 hj2
            have hmax3_tail : ∀ j, e1.toNat ≤ j → j < tlen.toNat - 1 → ∀ i, i ≤ j →
                tmpLe lvl tpos (tmp3[1 + i]?.getD 0#32) (tmp3[1 + j]?.getD 0#32) := by
              intro j hj1 hj2 i hij
              by_cases hje : j = e1.toNat
              · subst hje
                rw [hget3 (1 + e1.toNat)]; simp only [↓reduceIte]
                by_cases hie' : i = e1.toNat
                · subst hie'; rw [hget3 (1 + e1.toNat)]; simp only [↓reduceIte]
                  exact m7_tmpLe_refl _ _ _
                · by_cases hi0 : i = 0
                  · subst hi0; rw [hget3 1]
                    simp only [show (1 : Nat) ≠ 1 + e1.toNat by omega, ↓reduceIte]
                    exact m7_heap_root_max hh2 e1.toNat (by omega)
                  · rw [hget3 (1 + i)]
                    simp only [show 1 + i ≠ 1 + e1.toNat by omega, show 1 + i ≠ 1 by omega,
                      ↓reduceIte]
                    exact m7_heap_root_max hh2 i (by omega)
              · have hje1 : e.toNat ≤ j := by omega
                rw [hget3 (1 + j)]
                simp only [show 1 + j ≠ 1 + e1.toNat by omega, show 1 + j ≠ 1 by omega, ↓reduceIte]
                by_cases hie' : i = e1.toNat
                · subst hie'; rw [hget3 (1 + e1.toNat)]; simp only [↓reduceIte]
                  exact hsorted2 j hje1 hj2 0 (by omega)
                · by_cases hi0 : i = 0
                  · subst hi0; rw [hget3 1]
                    simp only [show (1 : Nat) ≠ 1 + e1.toNat by omega, ↓reduceIte]
                    exact hsorted2 j hje1 hj2 e1.toNat (by omega)
                  · rw [hget3 (1 + i)]
                    simp only [show 1 + i ≠ 1 + e1.toNat by omega, show 1 + i ≠ 1 by omega,
                      ↓reduceIte]
                    exact hsorted2 j hje1 hj2 i hij
            have hheap3 : IsMaxHeapFrom lvl tpos tmp3 1 e1.toNat := by
              intro i hi1 hi2
              have hhi2 := hh2 i (Nat.zero_le _) (by omega)
              have hiv : tmp3[1 + i]?.getD 0#32 = tmp2[1 + i]?.getD 0#32 := by
                rw [hget3]
                simp only [show 1 + i ≠ 1 + e1.toNat by omega, show 1 + i ≠ 1 by omega, ↓reduceIte]
              constructor
              · intro h1; rw [hiv, hget3]
                simp only [show 1 + (2 * i + 1) ≠ 1 + e1.toNat by omega,
                  show 1 + (2 * i + 1) ≠ 1 by omega, ↓reduceIte]
                exact hhi2.1 (by omega)
              · intro h2; rw [hiv, hget3]
                simp only [show 1 + (2 * i + 2) ≠ 1 + e1.toNat by omega,
                  show 1 + (2 * i + 2) ≠ 1 by omega, ↓reduceIte]
                exact hhi2.2 (by omega)
            ml_lets
            apply wp_call_of_spec; apply hSift
            dsimp only [FullMinSpecs.fullSortTmpSiftSpec, vals, Arg.val]
            have he_sub1 : (e - 1).toNat = e1.toNat := rfl
            refine ⟨tmp3, lvl, tpos, R,
              by change 0 < (e - 1).toNat; rw [he_sub1]; omega,
              by rw [htl3]; change 1 + (e - 1).toNat ≤ tmp_init.length
                 rw [he_sub1]; omega,
              by change (e - 1).toNat < 2 ^ 60; rw [he_sub1]; omega,
              fun k hk1 hk2 => hbd3 k hk1 (by
                change k < 1 + (e - 1).toNat at hk2
                rw [he_sub1] at hk2; omega),
              by change IsMaxHeapFrom lvl tpos tmp3 1 (e - 1).toNat
                 rw [he_sub1]; exact hheap3,
              hm4', ?_⟩
            intro tmp4 m4 htl4 hperm4 hout4 hseq4 hh4 hm4_sift'
            rw [he_sub1] at hout4 hh4
            have h04 : 0 < tlen.toNat → tmp4[0]? = tmp_init[0]? := fun hp =>
              (hout4 0 (Or.inl rfl)).trans (h03 hp)
            have hseq4_full : SortSliceEq tmp4 tmp_init tlen.toNat :=
              m7_sortSliceEq_trans
                (m7_sortSliceEq_widen (by omega) hseq4 (fun k hk => hout4 k (Or.inr hk)))
                hseq3
            have hbd4 : ∀ k, 1 ≤ k → k < tlen.toNat →
                (tmp4[k]?.getD 0#32).toNat / 2 < lvl.length ∧
                (tmp4[k]?.getD 0#32).toNat / 2 < tpos.length := fun k hk1 hk2 => by
              obtain ⟨j, hj1, hj2, hkj⟩ := hseq4_full.1 k hk1 hk2
              rw [hkj]; exact hbd0 j hj1 hj2
            have hsorted4 : ∀ j, e1.toNat ≤ j → j < tlen.toNat - 1 → ∀ i, i ≤ j →
                tmpLe lvl tpos (tmp4[1 + i]?.getD 0#32) (tmp4[1 + j]?.getD 0#32) := by
              intro j hj1 hj2 i hij
              rw [hout4 (1 + j) (Or.inr (by omega))]
              by_cases hie_c : i < e1.toNat
              · obtain ⟨k, hk1, hk2, hik⟩ := hseq4.1 (1 + i) (by omega) (by omega)
                rw [hik]
                simpa [show 1 + (k - 1) = k by omega] using
                  hmax3_tail j hj1 hj2 (k - 1) (by omega)
              · rw [hout4 (1 + i) (Or.inr (by omega))]
                exact hmax3_tail j hj1 hj2 i hij
            have hperm3 : tmp3.Perm tmp2 := m7SortSwap_perm
            have hout3 : ∀ k, tlen.toNat ≤ k → tmp3[k]? = tmp2[k]? := fun k hk => by
              dsimp only [tmp3]; rw [m7SortSwap_getElem?]
              simp [show k ≠ 1 + e1.toNat by omega, show k ≠ 1 by omega]
            ml_lets
            exact hJ2 e1.toNat (e1, ()) m4 (by omega)
              ⟨rfl, by omega, by omega, tmp4, htl4.trans htl3,
                hperm4.trans (hperm3.trans hperm2),
                fun k hk => (hout4 k (Or.inr (by omega))).trans ((hout3 k hk).trans (hout2 k hk)),
                h04, hseq4_full, hbd4, hh4, hsorted4, hm4_sift'⟩
          · have he_eq1 : e.toNat = 1 := by
              change (1 : BitVec 64).ult e = false at he_le1
              rw [BitVec.ult, decide_eq_false_iff_not] at he_le1
              have h1n : (1 : BitVec 64).toNat = 1 := rfl
              rw [h1n] at he_le1; omega
            rw [he_eq1] at hsorted2
            ml_lets; rw [wp]
            refine hQ tmp2 m2 htl2' (perm_take_of_drop_eq hperm2 hout2) h02
              (fun k hk => hout2 k (by omega))
              (m7_sortSliceEq_to_full hseq2) (fun i j hi1 hij hj => ?_) hm2
            dsimp only at hj
            by_cases hj1 : j = 1
            · subst hj1
              have hij' : i = 1 := by omega
              subst hij'; exact m7_tmpLe_to_full (m7_tmpLe_refl _ _ _)
            · exact m7_tmpLe_to_full (by
                simpa [show 1 + (i - 1) = i by omega, show 1 + (j - 1) = j by omega] using
                  hsorted2 (j - 1) (by omega) (by omega) (i - 1) (by omega))
        · intro J2 hJ2; wp_unfold
          exact hJ2 (tlen - 1).toNat (tlen - 1, ()) m1 ⟨rfl, by omega, by omega, tmp1, htl1,
            hperm1, hout1, h01, hseq1, hbd1, by rw [htlen_m1]; exact hh1,
            fun j hj1 => by omega, hm1⟩
    · intro J1 hJ1; wp_unfold
      have hsh : (((tlen - 1) >>> ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64))).toNat =
          (tlen.toNat - 1) / 2 := by
        have h1 : BitVec.signExtend 64 (1 : BitVec 32) = (1 : BitVec 64) := rfl
        have hm' : (1 : BitVec 64).toNat % 64 = 1 := rfl
        rw [h1, hm', bv64_lshr_1, htlen_m1]
      have hh0 : IsMaxHeapFrom lvl tpos tmp_init ((tlen.toNat - 1) / 2) (tlen.toNat - 1) := by
        intro i hi1 hi2; exact ⟨fun h => by omega, fun h => by omega⟩
      exact hJ1 _ _ m0 ⟨rfl, by rw [hsh]; exact le_refl _, tmp_init, rfl, List.Perm.refl _,
        fun _ _ => rfl, fun _ => rfl, m7_sortSliceEq_refl _ _, hbd0,
        by rw [hsh]; exact hh0, hm0⟩

end LeanQbe.T.Examples.Kissat.FullM7AnalyzeSort
