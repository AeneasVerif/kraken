module

public import LeanQbe.T.Examples.Kissat.FullM7AnalyzeSortProof1
import LeanQbe.T.Examples.Kissat.FullMinLemmas1
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.MemLemmas
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Wave 4G Proof Shard 2: Helpers for `full_sort_tmp_m7_wp`

M1-clean UNSAT-only `Func.wp` proof (`public section`, `0 @[expose]`, `0 import all`) for
`full_sort_tmp_m7` against `m7SortTmpSpec`:
- Early return for `tlen ≤ 2` and `tlen > max_vars` (vacuous / unreachable).
- `tlen = 3` direct 2-element `(level, trail_pos)` comparator/swap fast path.
- `3 < tlen ≤ 16` `(level, trail_pos)` insertion sort fast path.
- `tlen > 16`: `wsort` copy + `[min_l, max_l]` scan, `full_sort_tmp_heap_m7` fallback for
  single-level / wide-span instances, and O(n) `work_stk2` histogram + prefix-sum + scatter
  followed by equal-level run tie-breaking (`rlen = 2`, `≤ 16` `tpos` insertion sort, and
  shifted `sub` call to `full_sort_tmp_heap_m7` via `array_append`).
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
open scoped LeanQbe.T.Examples.Kissat.Full.FullMinTactics
open Kraken.Bedrock2.Test

/-! ## 1. State Preservation, Memory Focus, and BitVector Helpers -/

theorem m7SortTmp_stateOk (c : FullCfg) (s : FullState)
    (tmp' wsort' : List (BitVec 32)) (hlen : s.LengthsOk c)
    (htmp : tmp'.length = c.max_vars) (hws : wsort'.length = 2 * c.max_vars) :
    let s' : FullState :=
      { core := { s.core with tmp := tmp' }
        scratch := { s.scratch with wsort := wsort' } }
    s'.LengthsOk c ∧ Full.FullExtScratchPres s s' := by
  rcases hlen with ⟨hc, hs⟩
  refine ⟨⟨?_, ?_⟩, rfl, rfl⟩
  · exact { hc with tmp_len_arr := htmp }
  · exact { hs with wsort_len := hws }

theorem m7FullMem_focus_heap {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hm : (FullMem c s ⋆ R) m) :
    ∃ F : Mem 64 → Prop,
      (array (t := i32) c.pTmp s.core.tmp ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
        array (t := i32) c.pTrailPos s.core.trail_pos ⋆ F) m ∧
      ∀ tmp' m',
        (array (t := i32) c.pTmp tmp' ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
          array (t := i32) c.pTrailPos s.core.trail_pos ⋆ F) m' →
        (FullMem c { s with core := { s.core with tmp := tmp' } } ⋆ R) m' := by
  have hm1 := hm
  rw [fullMem_eq_coreU32A] at hm1
  unfold FullCoreU32A at hm1
  refine ⟨array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pReason s.core.rsns ⋆
      array (t := i32) c.pTrail s.core.trl ⋆ array (t := i32) c.pMinClr s.core.min_clr ⋆
      (FullCoreByteArrs c s.core ⋆ FullCoreU32B c s.core ⋆
        FullCoreDynArrs c s.core ⋆ fullCoreOuter c s) ⋆ R,
    sep_ac hm1, fun tmp' m' hm' => ?_⟩
  rw [fullMem_eq_coreU32A]
  unfold FullCoreU32A; dsimp only
  have h1 : FullCoreByteArrs c { s.core with tmp := tmp' } = FullCoreByteArrs c s.core := rfl
  have h2 : FullCoreU32B c { s.core with tmp := tmp' } = FullCoreU32B c s.core := rfl
  have h3 : FullCoreDynArrs c { s.core with tmp := tmp' } = FullCoreDynArrs c s.core := rfl
  have h4 : fullCoreOuter c { s with core := { s.core with tmp := tmp' } } =
      fullCoreOuter c s := rfl
  rw [h1, h2, h3, h4]
  exact sep_ac hm'

theorem m7FullMem_focus_sub_heap {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (off : Nat) (hoff : off ≤ s.core.tmp.length)
    (hm : (FullMem c s ⋆ R) m) :
    ∃ F : Mem 64 → Prop,
      (array (t := i32) (c.pTmp + BitVec.ofNat 64 (4 * off)) (s.core.tmp.drop off) ⋆
        array (t := i32) c.pLevel s.core.lvl ⋆
        array (t := i32) c.pTrailPos s.core.trail_pos ⋆ F) m ∧
      ∀ sub' m',
        (array (t := i32) (c.pTmp + BitVec.ofNat 64 (4 * off)) sub' ⋆
          array (t := i32) c.pLevel s.core.lvl ⋆
          array (t := i32) c.pTrailPos s.core.trail_pos ⋆ F) m' →
        (FullMem c { s with core := { s.core with tmp := s.core.tmp.take off ++ sub' } } ⋆ R)
          m' := by
  obtain ⟨F0, hfocus, hunfocus⟩ := m7FullMem_focus_heap hm
  have hsplit : array (t := i32) c.pTmp s.core.tmp =
      (array (t := i32) c.pTmp (s.core.tmp.take off) ⋆
        array (t := i32) (c.pTmp + BitVec.ofNat 64 (4 * off)) (s.core.tmp.drop off)) := by
    conv => lhs; rw [← List.take_append_drop off s.core.tmp]
    rw [array_append (t := i32), List.length_take_of_le hoff, show (i32 : Ty).bytes = 4 from rfl]
  rw [hsplit] at hfocus
  refine ⟨array (t := i32) c.pTmp (s.core.tmp.take off) ⋆ F0, sep_ac hfocus, fun sub' m' hm' => ?_⟩
  apply hunfocus
  have hjoin : (array (t := i32) c.pTmp (s.core.tmp.take off) ⋆
      array (t := i32) (c.pTmp + BitVec.ofNat 64 (4 * off)) sub') =
      array (t := i32) c.pTmp (s.core.tmp.take off ++ sub') := by
    rw [array_append (t := i32), List.length_take_of_le hoff, show (i32 : Ty).bytes = 4 from rfl]
  rw [← hjoin]
  exact sep_ac hm'

theorem m7_ushr1_mod (x : BitVec 32) :
    ((x.setWidth 64) >>> ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64)).toNat =
      x.toNat / 2 := by
  rw [show (BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64 =
    (BitVec.signExtend 64 (1 : BitVec 32)).toNat from rfl]
  exact m7_bv64_zext32_ushr1 x

theorem m7_shl2_mod {x : BitVec 64} (hx : x.toNat < 2 ^ 60) :
    (x <<< ((BitVec.signExtend 64 (2 : BitVec 32)).toNat % 64)).toNat = 4 * x.toNat := by
  have h2 : (BitVec.signExtend 64 (2 : BitVec 32)).toNat % 64 = 2 := rfl
  rw [h2, BitVec.toNat_shiftLeft, Nat.mod_eq_of_lt (by omega)]
  simp [Nat.shiftLeft_eq]; omega

theorem m7_bv32_trunc64 {y : BitVec 64} (hy : y.toNat < 2 ^ 32) :
    (y.setWidth 32).toNat = y.toNat := by bv_omega

theorem m7_bv32_add1_lt {x : BitVec 32} (hx : x.toNat + 1 < 2 ^ 32) :
    (x + 1#32).toNat = x.toNat + 1 := by bv_omega

theorem m7_sub_ptr (base rb : BitVec 64) (hrb : 1 ≤ rb.toNat) (hrb60 : rb.toNat < 2 ^ 60) :
    base + ((rb - 1) <<< ((BitVec.signExtend 64 (2 : BitVec 32)).toNat % 64)) =
      base + BitVec.ofNat 64 (4 * (rb.toNat - 1)) := by
  congr 1
  apply BitVec.eq_of_toNat_eq
  have hrm : (rb - 1).toNat = rb.toNat - 1 := m7_bv64_sub1 hrb
  rw [m7_shl2_mod (by omega), hrm, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-! ## 2. Pure Slice, Permutation, Order, and Bucket/Scatter Helpers -/

def m7Slice {α : Type _} (xs : List α) (lo hi : Nat) : List α :=
  (xs.take hi).drop lo

theorem m7Slice_length {α : Type _} (xs : List α) (lo hi : Nat) :
    (m7Slice xs lo hi).length = min hi xs.length - lo := by
  simp [m7Slice, List.length_drop, List.length_take]

theorem m7Slice_nil {α : Type _} (xs : List α) {lo hi : Nat} (h : hi ≤ lo) :
    m7Slice xs lo hi = [] := by
  rw [List.eq_nil_iff_length_eq_zero, m7Slice_length]; omega

theorem m7Slice_getElem {α : Type _} (xs : List α) {lo hi k : Nat}
    (hk : k < (m7Slice xs lo hi).length) :
    (m7Slice xs lo hi)[k]'hk = xs[lo + k]'(by rw [m7Slice_length] at hk; omega) := by
  unfold m7Slice at hk ⊢; rw [List.getElem_drop, List.getElem_take]

theorem m7Slice_append_succ {α : Type _} (xs : List α) {lo hi : Nat}
    (h1 : lo ≤ hi) (h2 : hi < xs.length) :
    m7Slice xs lo (hi + 1) = m7Slice xs lo hi ++ [xs[hi]'h2] := by
  apply List.ext_getElem
  · simp [m7Slice_length]; omega
  · intro k hk1 hk2
    rw [m7Slice_getElem]
    by_cases hkl : k < (m7Slice xs lo hi).length
    · rw [List.getElem_append_left hkl, m7Slice_getElem]
    · have hl1 : (m7Slice xs lo hi).length = hi - lo := by rw [m7Slice_length]; omega
      have hk_eq : k = hi - lo := by rw [m7Slice_length] at hk1; omega
      rw [List.getElem_append_right (Nat.le_of_not_lt hkl)]
      have hidx : k - (m7Slice xs lo hi).length = 0 := by omega
      simp only [hidx, List.getElem_singleton]
      congr 1; omega

theorem m7Slice_append_slice {α : Type _} (xs : List α) {a b c : Nat}
    (hab : a ≤ b) (hbc : b ≤ c) (hc : c ≤ xs.length) :
    m7Slice xs a b ++ m7Slice xs b c = m7Slice xs a c := by
  apply List.ext_getElem
  · simp only [List.length_append, m7Slice_length]; omega
  · intro k hk1 hk2
    rw [m7Slice_getElem]
    by_cases hkb : k < (m7Slice xs a b).length
    · rw [List.getElem_append_left hkb, m7Slice_getElem]
    · have hL : (m7Slice xs a b).length = b - a := by rw [m7Slice_length]; omega
      rw [List.getElem_append_right (Nat.le_of_not_lt hkb), m7Slice_getElem]
      congr 1; omega

theorem m7Slice_set_outside {α : Type _} (xs : List α) {lo hi dst : Nat} (v : α)
    (hout : dst < lo ∨ hi ≤ dst) :
    m7Slice (xs.set dst v) lo hi = m7Slice xs lo hi := by
  apply List.ext_getElem
  · simp [m7Slice_length]
  · intro k hk1 hk2
    rw [m7Slice_getElem, m7Slice_getElem, List.getElem_set_ne (by
      rw [m7Slice_length] at hk1; rcases hout with h | h <;> omega)]

theorem m7Slice_set_end {α : Type _} (xs : List α) {lo dst : Nat} (v : α)
    (h1 : lo ≤ dst) (h2 : dst < xs.length) :
    m7Slice (xs.set dst v) lo (dst + 1) = m7Slice xs lo dst ++ [v] := by
  rw [m7Slice_append_succ _ h1 (by simp; omega), List.getElem_set_self,
    m7Slice_set_outside _ _ (Or.inr (le_refl _))]

theorem m7Slice_perm_to_take {α : Type _} {xs ys : List α} {n : Nat}
    (h0 : xs[0]? = ys[0]?) (hperm : (m7Slice xs 1 n).Perm (m7Slice ys 1 n))
    (hpos : 0 < n) (hx : n ≤ xs.length) (hy : n ≤ ys.length) :
    (xs.take n).Perm (ys.take n) := by
  have htx : xs.take n = xs[0]'(by omega) :: m7Slice xs 1 n := by
    apply List.ext_getElem
    · simp [m7Slice_length]; omega
    · intro k hk1 hk2
      rcases k with _ | k'
      · simp
      · simp [m7Slice_getElem, Nat.add_comm]
  have hty : ys.take n = ys[0]'(by omega) :: m7Slice ys 1 n := by
    apply List.ext_getElem
    · simp [m7Slice_length]; omega
    · intro k hk1 hk2
      rcases k with _ | k'
      · simp
      · simp [m7Slice_getElem, Nat.add_comm]
  have heq0 : xs[0]'(by omega) = ys[0]'(by omega) := by
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at h0
    exact Option.some.inj h0
  rw [htx, hty, heq0]
  exact List.Perm.cons _ hperm

theorem m7Slice_perm_bij {xs ys : List (BitVec 32)} {n : Nat}
    (hperm : (m7Slice xs 1 n).Perm (m7Slice ys 1 n)) (hx : n ≤ xs.length) (hy : n ≤ ys.length) :
    (∀ j, 1 ≤ j → j < n → ∃ i, 1 ≤ i ∧ i < n ∧ xs[j]? = ys[i]?) ∧
    (∀ i, 1 ≤ i → i < n → ∃ j, 1 ≤ j ∧ j < n ∧ ys[i]? = xs[j]?) := by
  constructor
  · intro j hj1 hj2
    have hmem : xs[j]'(by omega) ∈ m7Slice xs 1 n := by
      rw [List.mem_iff_getElem]
      exact ⟨j - 1, by rw [m7Slice_length]; omega, by rw [m7Slice_getElem]; congr 1; omega⟩
    rw [hperm.mem_iff, List.mem_iff_getElem] at hmem
    obtain ⟨k, hk, hkeq⟩ := hmem
    rw [m7Slice_getElem] at hkeq
    rw [m7Slice_length] at hk
    refine ⟨1 + k, by omega, by omega, ?_⟩
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega), hkeq]
  · intro i hi1 hi2
    have hmem : ys[i]'(by omega) ∈ m7Slice ys 1 n := by
      rw [List.mem_iff_getElem]
      exact ⟨i - 1, by rw [m7Slice_length]; omega, by rw [m7Slice_getElem]; congr 1; omega⟩
    rw [← hperm.mem_iff, List.mem_iff_getElem] at hmem
    obtain ⟨k, hk, hkeq⟩ := hmem
    rw [m7Slice_getElem] at hkeq
    rw [m7Slice_length] at hk
    refine ⟨1 + k, by omega, by omega, ?_⟩
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega), hkeq]

theorem m7Slice_perm_bd {xs ys : List (BitVec 32)} {n mv : Nat}
    (hperm : (m7Slice xs 1 n).Perm (m7Slice ys 1 n)) (hx : n ≤ xs.length) (hy : n ≤ ys.length)
    (hbd : ∀ k, 1 ≤ k → k < n → (ys[k]?.getD 0#32).toNat < 2 * mv) :
    ∀ k, 1 ≤ k → k < n → (xs[k]?.getD 0#32).toNat < 2 * mv := fun k hk1 hk2 => by
  obtain ⟨i, hi1, hi2, hki⟩ := (m7Slice_perm_bij hperm hx hy).1 k hk1 hk2
  rw [hki]; exact hbd i hi1 hi2

theorem m7_slice_perm_sub {xs ys : List (BitVec 32)} {lo hi n : Nat}
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (hn : hi ≤ n) (hx : n ≤ xs.length) (hy : n ≤ ys.length)
    (hsub : (m7Slice xs lo hi).Perm (m7Slice ys lo hi))
    (hout : ∀ k, (k < lo ∨ hi ≤ k) → xs[k]? = ys[k]?) :
    (m7Slice xs 1 n).Perm (m7Slice ys 1 n) := by
  have h1 := m7Slice_append_slice xs (by omega) hhi (by omega)
  have h2 := m7Slice_append_slice xs (by omega : 1 ≤ hi) hn hx
  have hy1 := m7Slice_append_slice ys (by omega) hhi (by omega)
  have hy2 := m7Slice_append_slice ys (by omega : 1 ≤ hi) hn hy
  have heqL : m7Slice xs 1 lo = m7Slice ys 1 lo := by
    apply List.ext_getElem
    · simp [m7Slice_length]; omega
    · intro k hk1 hk2
      rw [m7Slice_getElem, m7Slice_getElem]
      have ho := hout (1 + k) (Or.inl (by rw [m7Slice_length] at hk1; omega))
      rw [List.getElem?_eq_getElem (by rw [m7Slice_length] at hk1; omega),
        List.getElem?_eq_getElem (by rw [m7Slice_length] at hk2; omega)] at ho
      exact Option.some.inj ho
  have heqR : m7Slice xs hi n = m7Slice ys hi n := by
    apply List.ext_getElem
    · simp [m7Slice_length]; omega
    · intro k hk1 hk2
      rw [m7Slice_getElem, m7Slice_getElem]
      have ho := hout (hi + k) (Or.inr (by omega))
      rw [List.getElem?_eq_getElem (by rw [m7Slice_length] at hk1; omega),
        List.getElem?_eq_getElem (by rw [m7Slice_length] at hk2; omega)] at ho
      exact Option.some.inj ho
  rw [← h2, ← h1, ← hy2, ← hy1, heqL, heqR]
  exact ((List.Perm.refl _).append hsub).append (List.Perm.refl _)

theorem m7_subslice_set_swap_perm {zs : List (BitVec 32)} {lo hi a b : Nat}
    (hlo : lo ≤ a) (hab : a < b) (hb : b < hi) (hhi : hi ≤ zs.length) :
    (m7Slice ((zs.set a (zs[b]'(by omega))).set b (zs[a]'(by omega))) lo hi).Perm
      (m7Slice zs lo hi) := by
  have heqz : m7Slice ((zs.set a zs[b]).set b zs[a]) lo hi =
      ((m7Slice zs lo hi).set (a - lo) ((m7Slice zs lo hi)[b - lo]'(by
          rw [m7Slice_length]; omega))).set
        (b - lo) ((m7Slice zs lo hi)[a - lo]'(by rw [m7Slice_length]; omega)) := by
    apply List.ext_getElem
    · simp [m7Slice_length]
    · intro k hk1 hk2
      rw [m7Slice_getElem]
      have ha_eq : (m7Slice zs lo hi)[a - lo]'(by rw [m7Slice_length]; omega) =
          zs[a]'(by omega) := by rw [m7Slice_getElem]; congr 1; omega
      have hb_eq : (m7Slice zs lo hi)[b - lo]'(by rw [m7Slice_length]; omega) =
          zs[b]'(by omega) := by rw [m7Slice_getElem]; congr 1; omega
      by_cases hk_b : b = lo + k
      · simp only [List.getElem_set, hk_b, Nat.add_sub_cancel_left, ↓reduceIte, ha_eq]
      · have hk_nb2 : ¬ b - lo = k := by omega
        by_cases hk_a : a = lo + k
        · simp only [List.getElem_set, hk_b, hk_nb2, hk_a, Nat.add_sub_cancel_left,
            ↓reduceIte, hb_eq]
        · have hk_na2 : ¬ a - lo = k := by omega
          simp only [List.getElem_set, hk_b, hk_nb2, hk_a, hk_na2, ↓reduceIte, m7Slice_getElem]
  rw [heqz]
  exact m7_list_swap_perm (m7Slice zs lo hi) (by omega) (by rw [m7Slice_length]; omega)

theorem m7_shift_slice_perm {xs : List (BitVec 32)} {lo hi j j' : Nat} (x : BitVec 32)
    (hlo : lo ≤ j') (hj' : j' < j) (hj : j < hi) (hhi : hi ≤ xs.length) :
    (m7Slice ((xs.set j (xs[j']'(by omega))).set j' x) lo hi).Perm
      (m7Slice (xs.set j x) lo hi) := by
  let ys := xs.set j x
  have hyl : ys.length = xs.length := by simp [ys]
  have heq : (xs.set j (xs[j']'(by omega))).set j' x =
      (ys.set j' (ys[j]'(by rw [hyl]; omega))).set j (ys[j']'(by rw [hyl]; omega)) := by
    apply List.ext_getElem
    · simp [ys]
    · intro k hk1 hk2
      by_cases h1 : j' = k
      · have h2 : ¬ j = k := by omega
        simp only [ys, List.getElem_set, h1, h2, ↓reduceIte]
      · by_cases h2 : j = k
        · have hnk : ¬ k = j' := Ne.symm h1
          simp only [ys, List.getElem_set, h1, h2, hnk, ↓reduceIte]
        · simp only [ys, List.getElem_set, h1, h2, ↓reduceIte]
  rw [heq]
  exact m7_subslice_set_swap_perm hlo hj' hj (by rw [hyl]; exact hhi)

theorem m7_swap_slice_perm {xs : List (BitVec 32)} {lo hi u v : Nat}
    (hlo : lo ≤ u) (huv : u < v) (hv : v < hi) (hhi : hi ≤ xs.length) :
    (m7Slice ((xs.set u (xs[v]'(by omega))).set v (xs[u]'(by omega))) lo hi).Perm
      (m7Slice xs lo hi) :=
  m7_subslice_set_swap_perm hlo huv hv hhi

theorem m7_fullTmpLe_refl (lvl tpos : List (BitVec 32)) (a : BitVec 32) :
    Full.fullTmpLe lvl tpos a a := by
  unfold Full.fullTmpLe Full.fullTmpLt; omega

theorem m7_fullTmpLe_trans {lvl tpos : List (BitVec 32)} {a b c : BitVec 32}
    (h1 : Full.fullTmpLe lvl tpos a b) (h2 : Full.fullTmpLe lvl tpos b c) :
    Full.fullTmpLe lvl tpos a c := by
  unfold Full.fullTmpLe Full.fullTmpLt Full.fullTmpKey at h1 h2 ⊢; omega

theorem m7_fullTmpLe_of_cmp {lvl tpos : List (BitVec 32)} {a b : BitVec 32}
    (ha_l : a.toNat / 2 < lvl.length) (hb_l : b.toNat / 2 < lvl.length)
    (ha_t : a.toNat / 2 < tpos.length) (hb_t : b.toNat / 2 < tpos.length)
    (hl_nlt : ¬ (lvl[b.toNat / 2]'hb_l).toNat < (lvl[a.toNat / 2]'ha_l).toNat)
    (ht_nlt : (lvl[b.toNat / 2]'hb_l).toNat = (lvl[a.toNat / 2]'ha_l).toNat →
      ¬ (tpos[b.toNat / 2]'hb_t).toNat < (tpos[a.toNat / 2]'ha_t).toNat) :
    Full.fullTmpLe lvl tpos a b := by
  simp only [Full.fullTmpLe, Full.fullTmpLt, Full.fullTmpKey,
    List.getElem?_eq_getElem ha_l, List.getElem?_eq_getElem hb_l,
    List.getElem?_eq_getElem ha_t, List.getElem?_eq_getElem hb_t, Option.getD_some]
  omega

theorem m7_fullTmpLe_of_lt {lvl tpos : List (BitVec 32)} {a b : BitVec 32}
    (ha_l : a.toNat / 2 < lvl.length) (hb_l : b.toNat / 2 < lvl.length)
    (hlt : (lvl[a.toNat / 2]'ha_l).toNat < (lvl[b.toNat / 2]'hb_l).toNat) :
    Full.fullTmpLe lvl tpos a b := by
  simp only [Full.fullTmpLe, Full.fullTmpLt, Full.fullTmpKey,
    List.getElem?_eq_getElem ha_l, List.getElem?_eq_getElem hb_l, Option.getD_some]
  omega

theorem m7_fullTmpLe_of_eq_lvl_tpos {lvl tpos : List (BitVec 32)} {a b : BitVec 32}
    (ha_l : a.toNat / 2 < lvl.length) (hb_l : b.toNat / 2 < lvl.length)
    (ha_t : a.toNat / 2 < tpos.length) (hb_t : b.toNat / 2 < tpos.length)
    (heq : (lvl[a.toNat / 2]'ha_l).toNat = (lvl[b.toNat / 2]'hb_l).toNat)
    (ht : (tpos[a.toNat / 2]'ha_t).toNat ≤ (tpos[b.toNat / 2]'hb_t).toNat) :
    Full.fullTmpLe lvl tpos a b := by
  simp only [Full.fullTmpLe, Full.fullTmpLt, Full.fullTmpKey,
    List.getElem?_eq_getElem ha_l, List.getElem?_eq_getElem hb_l,
    List.getElem?_eq_getElem ha_t, List.getElem?_eq_getElem hb_t, Option.getD_some]
  omega

def m7Bkt (lvl : List (BitVec 32)) (minL : Nat) (x : BitVec 32) : Nat :=
  (lvl[x.toNat / 2]?.getD 0#32).toNat - minL

def m7BktCnt (lvl : List (BitVec 32)) (minL : Nat) (xs : List (BitVec 32))
    (b : Nat) : Nat :=
  xs.countP (fun x => m7Bkt lvl minL x == b)

theorem m7BktCnt_append (lvl : List (BitVec 32)) (minL : Nat)
    (xs : List (BitVec 32)) (x : BitVec 32) (b : Nat) :
    m7BktCnt lvl minL (xs ++ [x]) b =
      m7BktCnt lvl minL xs b + (if b = m7Bkt lvl minL x then 1 else 0) := by
  simp only [m7BktCnt, List.countP_append, List.countP_cons, List.countP_nil, Nat.zero_add]
  by_cases h : b = m7Bkt lvl minL x
  · subst h; simp
  · simp [h, Ne.symm h]

theorem m7BktCnt_sum_range (lvl : List (BitVec 32)) (minL : Nat)
    (xs : List (BitVec 32)) (m : Nat) (hm : ∀ x ∈ xs, m7Bkt lvl minL x < m) :
    (List.range m).foldl (fun acc b => acc + m7BktCnt lvl minL xs b) 0 = xs.length := by
  induction xs with
  | nil =>
    have h0 : ∀ n init, (List.range n).foldl (fun acc (_ : Nat) => acc + 0) init = init := by
      intro n
      induction n with
      | zero => intro init; rfl
      | succ k ihk => intro init; rw [List.range_succ, List.foldl_append]; exact ihk init
    simpa [m7BktCnt] using h0 m 0
  | cons a t ih =>
    have ha : m7Bkt lvl minL a < m := hm a (by simp)
    have ht : ∀ x ∈ t, m7Bkt lvl minL x < m := fun x hx => hm x (by simp [hx])
    have ih_t := ih ht
    have hstep : ∀ n init,
        (List.range n).foldl (fun acc b =>
          acc + (m7BktCnt lvl minL t b + if m7Bkt lvl minL a == b then 1 else 0)) init =
        (List.range n).foldl (fun acc b => acc + m7BktCnt lvl minL t b) init +
          (if m7Bkt lvl minL a < n then 1 else 0) := by
      intro n
      induction n with
      | zero => intro init; simp
      | succ k ihk =>
        intro init
        rw [List.range_succ, List.foldl_append, List.foldl_append]
        simp only [List.foldl_cons, List.foldl_nil]
        rw [ihk init]
        by_cases h1 : m7Bkt lvl minL a = k
        · subst h1; simp [Nat.add_assoc]
        · by_cases h2 : m7Bkt lvl minL a < k
          · simp [h1, h2, Nat.lt_succ_of_lt h2]; omega
          · simp [h1, h2, show ¬ m7Bkt lvl minL a < k + 1 by omega]
    have hcons : ∀ b, m7BktCnt lvl minL (a :: t) b =
        m7BktCnt lvl minL t b + (if m7Bkt lvl minL a == b then 1 else 0) := by
      intro b; simp [m7BktCnt, List.countP_cons]
    simp only [hcons]
    rw [hstep m 0, ih_t, ite_eq_left_iff.mpr (fun h => absurd ha h), List.length_cons]

theorem m7BktCnt_append_list (lvl : List (BitVec 32)) (minL : Nat)
    (xs ys : List (BitVec 32)) (b : Nat) :
    m7BktCnt lvl minL (xs ++ ys) b = m7BktCnt lvl minL xs b + m7BktCnt lvl minL ys b := by
  simp [m7BktCnt, List.countP_append]

def m7PrefixStart (tot : Nat → Nat) (n : Nat) : Nat :=
  (List.range n).foldl (fun acc b => acc + tot b) 1

theorem m7PrefixStart_zero (tot : Nat → Nat) : m7PrefixStart tot 0 = 1 := by
  simp [m7PrefixStart]

theorem m7PrefixStart_succ (tot : Nat → Nat) (b : Nat) :
    m7PrefixStart tot (b + 1) = m7PrefixStart tot b + tot b := by
  simp only [m7PrefixStart, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem m7PrefixStart_ge1 (tot : Nat → Nat) (b : Nat) : 1 ≤ m7PrefixStart tot b := by
  induction b with
  | zero => simp [m7PrefixStart_zero]
  | succ k ih => rw [m7PrefixStart_succ]; omega

theorem m7PrefixStart_mono {tot : Nat → Nat} {a b : Nat} (h : a ≤ b) :
    m7PrefixStart tot a ≤ m7PrefixStart tot b := by
  induction b with
  | zero => simp [Nat.le_zero.mp h]
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | hlt
    · exact le_refl _
    · exact Nat.le_trans (ih (Nat.lt_succ_iff.mp hlt)) (by rw [m7PrefixStart_succ]; omega)

theorem m7PrefixStart_eq_sum {tot : Nat → Nat} {n : Nat} :
    m7PrefixStart tot n = 1 + (List.range n).foldl (fun acc b => acc + tot b) 0 := by
  have hf : ∀ k init,
      (List.range k).foldl (fun acc b => acc + tot b) init =
        init + (List.range k).foldl (fun acc b => acc + tot b) 0 := by
    intro k
    induction k with
    | zero => intro init; simp
    | succ k' ihk =>
      intro init
      rw [List.range_succ, List.foldl_append, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ihk init, ihk 0]; omega
  induction n with
  | zero => simp [m7PrefixStart_zero]
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      m7PrefixStart_succ, ih]; omega

def m7FlatBkts (tmp : List (BitVec 32)) (spos epos : Nat → Nat) (span : Nat) :
    List (BitVec 32) :=
  (List.range span).flatMap (fun b => m7Slice tmp (spos b) (epos b))

theorem m7FlatBkts_zero (tmp : List (BitVec 32)) (spos epos : Nat → Nat) :
    m7FlatBkts tmp spos epos 0 = [] := by
  simp [m7FlatBkts]

theorem m7FlatBkts_succ (tmp : List (BitVec 32)) (spos epos : Nat → Nat) (b : Nat) :
    m7FlatBkts tmp spos epos (b + 1) =
      m7FlatBkts tmp spos epos b ++ m7Slice tmp (spos b) (epos b) := by
  simp only [m7FlatBkts, List.range_succ, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]

theorem m7FlatBkts_nil (tmp : List (BitVec 32)) (spos epos : Nat → Nat) (span : Nat)
    (he : ∀ b < span, epos b ≤ spos b) :
    m7FlatBkts tmp spos epos span = [] := by
  induction span with
  | zero => rfl
  | succ k ih =>
    rw [m7FlatBkts_succ, ih (fun b hb => he b (by omega)), m7Slice_nil _ (he k (by omega)),
      List.append_nil]

theorem m7FlatBkts_eq_slice (tmp : List (BitVec 32)) (spos : Nat → Nat) (span : Nat)
    (h0 : spos 0 = 1) (hmono : ∀ b < span, spos b ≤ spos (b + 1))
    (hle : spos span ≤ tmp.length) :
    m7FlatBkts tmp spos (fun b => spos (b + 1)) span = m7Slice tmp 1 (spos span) := by
  induction span with
  | zero => simp [m7FlatBkts_zero, h0, m7Slice_nil _ (le_refl 1)]
  | succ k ih =>
    have hsk_le : spos k ≤ spos (k + 1) := hmono k (Nat.lt_succ_self k)
    have hsk_len : spos k ≤ tmp.length := Nat.le_trans hsk_le hle
    have h1_le_k : 1 ≤ spos k := by
      have hsub : ∀ j ≤ k, 1 ≤ spos j := by
        intro j
        induction j with
        | zero => intro _; rw [h0]; exact le_refl _
        | succ j' ihj => intro hj; exact Nat.le_trans (ihj (by omega)) (hmono j' (by omega))
      exact hsub k (le_refl k)
    rw [m7FlatBkts_succ, ih (fun b hb => hmono b (by omega)) hsk_len]
    exact m7Slice_append_slice tmp h1_le_k hsk_le hle

theorem m7FlatBkts_scatter (tmp : List (BitVec 32)) (spos epos : Nat → Nat)
    (span b0 : Nat) (x : BitVec 32) (hb0 : b0 < span) (_h0 : spos 0 = 1)
    (hmono : ∀ b < span, spos b ≤ spos (b + 1))
    (he_lo : ∀ b < span, spos b ≤ epos b) (he_hi : ∀ b < span, epos b ≤ spos (b + 1))
    (hstep : epos b0 < spos (b0 + 1)) (hlen : spos span ≤ tmp.length) :
    let dst := epos b0
    let epos' := fun b => if b = b0 then epos b0 + 1 else epos b
    (m7FlatBkts (tmp.set dst x) spos epos' span).Perm
      (m7FlatBkts tmp spos epos span ++ [x]) := by
  intro dst epos'
  have hs_mono : ∀ {a b}, a ≤ b → b ≤ span → spos a ≤ spos b := by
    intro a b hab hb
    induction b with
    | zero => rw [Nat.le_zero.mp hab]; exact le_refl _
    | succ k ih =>
      rcases Nat.eq_or_lt_of_le hab with rfl | hlt
      · exact le_refl _
      · exact Nat.le_trans (ih (by omega) (by omega)) (hmono k (by omega))
  have hlt_b0 : ∀ m ≤ b0, m7FlatBkts (tmp.set dst x) spos epos' m =
      m7FlatBkts tmp spos epos m := by
    intro m hm
    induction m with
    | zero => rfl
    | succ k ih =>
      have hk : k < b0 := by omega
      have hne : epos' k = epos k := by simp only [epos', Nat.ne_of_lt hk, ↓reduceIte]
      have hdst_ge : spos (k + 1) ≤ dst :=
        Nat.le_trans (hs_mono (by omega) (by omega)) (he_lo b0 hb0)
      have he_le : epos k ≤ dst := Nat.le_trans (he_hi k (by omega)) hdst_ge
      rw [m7FlatBkts_succ, m7FlatBkts_succ, ih (by omega), hne,
        m7Slice_set_outside _ _ (Or.inr he_le)]
  have hgo : ∀ m, b0 < m → m ≤ span →
      (m7FlatBkts (tmp.set dst x) spos epos' m).Perm (m7FlatBkts tmp spos epos m ++ [x]) := by
    intro m hbm hm
    induction m with
    | zero => omega
    | succ k ih =>
      by_cases hkb : k = b0
      · have heq_pre := hlt_b0 k (by omega)
        have he_end : epos' k = dst + 1 := by simp only [epos', hkb, ↓reduceIte]; rfl
        have hdst_lt : dst < tmp.length := by
          have := hs_mono (by omega : b0 + 1 ≤ span) (le_refl span)
          omega
        rw [m7FlatBkts_succ, m7FlatBkts_succ, heq_pre, he_end, hkb,
          m7Slice_set_end tmp x (he_lo b0 hb0) hdst_lt, List.append_assoc]
      · have hk_gt : b0 < k := by omega
        have ihk := ih hk_gt (by omega)
        have hne : epos' k = epos k := by simp only [epos', hkb, ↓reduceIte]
        have hdst_lt : dst < spos k := by
          have := hs_mono (by omega : b0 + 1 ≤ k) (by omega)
          omega
        rw [m7FlatBkts_succ, m7FlatBkts_succ, hne, m7Slice_set_outside _ _ (Or.inl hdst_lt)]
        exact (ihk.append_right _).trans (by
          rw [List.append_assoc, List.append_assoc]
          exact List.Perm.append_left _ List.perm_append_comm)
  exact hgo span hb0 (le_refl span)

theorem m7_find_bkt {tot : Nat → Nat} {span p : Nat} (hp0 : 1 ≤ p)
    (hp1 : p < m7PrefixStart tot span) :
    ∃ b < span, m7PrefixStart tot b ≤ p ∧ p < m7PrefixStart tot (b + 1) := by
  induction span with
  | zero => simp [m7PrefixStart_zero] at hp1; omega
  | succ k ih =>
    by_cases hpk : p < m7PrefixStart tot k
    · obtain ⟨b, hb1, hb2, hb3⟩ := ih hpk
      exact ⟨b, Nat.lt_succ_of_lt hb1, hb2, hb3⟩
    · exact ⟨k, Nat.lt_succ_self k, Nat.le_of_not_lt hpk, hp1⟩

theorem m7_bucket_lvl_le {lvl : List (BitVec 32)} {minL span n : Nat}
    {tot : Nat → Nat} {tmp : List (BitVec 32)}
    (hs1 : m7PrefixStart tot span = n)
    (hm_min : ∀ k, 1 ≤ k → k < n → minL ≤ (lvl[(tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)
    (hm_bkt : ∀ b < span, ∀ p, m7PrefixStart tot b ≤ p → p < m7PrefixStart tot (b + 1) →
      m7Bkt lvl minL (tmp[p]?.getD 0#32) = b) :
    ∀ i j, 1 ≤ i → i ≤ j → j < n →
      (lvl[(tmp[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
      (lvl[(tmp[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat := by
  intro i j hi1 hij hj
  obtain ⟨bi, hbi_lt, hbi_lo, hbi_hi⟩ :=
    m7_find_bkt (tot := tot) (span := span) hi1 (hs1 ▸ by omega)
  obtain ⟨bj, hbj_lt, hbj_lo, hbj_hi⟩ :=
    m7_find_bkt (tot := tot) (span := span) (by omega : 1 ≤ j) (hs1 ▸ by omega)
  have hbi_le_bj : bi ≤ bj := Nat.le_of_not_lt fun hgt => by
    have h2 : m7PrefixStart tot (bj + 1) ≤ m7PrefixStart tot bi := m7PrefixStart_mono hgt
    omega
  have hi_b := hm_bkt bi hbi_lt i hbi_lo hbi_hi
  have hj_b := hm_bkt bj hbj_lt j hbj_lo hbj_hi
  have hi_m := hm_min i hi1 (by omega)
  have hj_m := hm_min j (by omega) hj
  dsimp [m7Bkt] at hi_b hj_b
  omega

theorem m7_ins_shift_inv {ltp : BitVec 32 → BitVec 32 → Prop}
    {xs : List (BitVec 32)} {lo i j : Nat} {x : BitVec 32}
    (hlo : lo < j) (hj_le : j ≤ i) (hi_len : i < xs.length)
    (hsort_hole : ∀ a b, lo ≤ a → a ≤ b → b ≤ i → a ≠ j → b ≠ j →
      ltp (xs[a]?.getD 0#32) (xs[b]?.getD 0#32))
    (hshift_hi : ∀ k, j < k → k ≤ i → ltp x (xs[k]?.getD 0#32))
    (hlt_prev : ltp x (xs[j - 1]?.getD 0#32)) :
    let xs' := xs.set j (xs[j - 1]?.getD 0#32)
    (∀ a b, lo ≤ a → a ≤ b → b ≤ i → a ≠ j - 1 → b ≠ j - 1 →
      ltp (xs'[a]?.getD 0#32) (xs'[b]?.getD 0#32)) ∧
    (∀ k, j - 1 < k → k ≤ i → ltp x (xs'[k]?.getD 0#32)) := by
  intro xs'
  have hget (p : Nat) : xs'[p]?.getD 0#32 =
      if p = j then xs[j - 1]?.getD 0#32 else xs[p]?.getD 0#32 := by
    dsimp [xs']
    by_cases hp : p = j
    · subst hp; rw [List.getElem?_eq_getElem (by simp; omega), List.getElem_set_self]; simp
    · rw [List.getElem?_set_ne (Ne.symm hp)]; simp [hp]
  constructor
  · intro a b ha hab hb haj hbj
    rw [hget a, hget b]
    by_cases ha_j : a = j
    · simp only [ha_j, ↓reduceIte]
      by_cases hb_j : b = j
      · simp only [hb_j, ↓reduceIte]
        exact hsort_hole (j - 1) (j - 1) (by omega) (le_refl _) (by omega) (by omega) (by omega)
      · simp only [hb_j, ↓reduceIte]
        exact hsort_hole (j - 1) b (by omega) (by omega) hb (by omega) hb_j
    · simp only [ha_j, ↓reduceIte]
      by_cases hb_j : b = j
      · simp only [hb_j, ↓reduceIte]
        exact hsort_hole a (j - 1) ha (by omega) (by omega) ha_j (by omega)
      · simp only [hb_j, ↓reduceIte]
        exact hsort_hole a b ha hab hb ha_j hb_j
  · intro k hk1 hk2
    rw [hget k]
    by_cases hkj : k = j
    · simp only [hkj, ↓reduceIte]; exact hlt_prev
    · simp only [hkj, ↓reduceIte]; exact hshift_hi k (by omega) hk2

theorem m7_ins_place_sorted {ltp : BitVec 32 → BitVec 32 → Prop}
    (hrefl : ∀ a, ltp a a) (htrans : ∀ a b c, ltp a b → ltp b c → ltp a c)
    {xs : List (BitVec 32)} {lo i j : Nat} {x : BitVec 32}
    (hlo : lo ≤ j) (hj_le : j ≤ i) (hi_len : i < xs.length)
    (hsort_hole : ∀ a b, lo ≤ a → a ≤ b → b ≤ i → a ≠ j → b ≠ j →
      ltp (xs[a]?.getD 0#32) (xs[b]?.getD 0#32))
    (hge_prev : lo < j → ltp (xs[j - 1]?.getD 0#32) x)
    (hshift_hi : ∀ k, j < k → k ≤ i → ltp x (xs[k]?.getD 0#32)) :
    let xs' := xs.set j x
    ∀ a b, lo ≤ a → a ≤ b → b ≤ i → ltp (xs'[a]?.getD 0#32) (xs'[b]?.getD 0#32) := by
  intro xs' a b ha hab hb
  have hget (p : Nat) : xs'[p]?.getD 0#32 = if p = j then x else xs[p]?.getD 0#32 := by
    dsimp [xs']
    by_cases hp : p = j
    · subst hp; rw [List.getElem?_eq_getElem (by simp; omega), List.getElem_set_self]; simp
    · rw [List.getElem?_set_ne (Ne.symm hp)]; simp [hp]
  rw [hget a, hget b]
  by_cases ha_j : a = j
  · simp only [ha_j, ↓reduceIte]
    by_cases hb_j : b = j
    · simp only [hb_j, ↓reduceIte]; exact hrefl _
    · simp only [hb_j, ↓reduceIte]; exact hshift_hi b (by omega) hb
  · simp only [ha_j, ↓reduceIte]
    by_cases hb_j : b = j
    · simp only [hb_j, ↓reduceIte]
      have hj_gt : lo < j := by omega
      exact htrans _ _ _
        (hsort_hole a (j - 1) ha (by omega) (by omega) ha_j (by omega))
        (hge_prev hj_gt)
    · simp only [hb_j, ↓reduceIte]; exact hsort_hole a b ha hab hb ha_j hb_j


theorem m7_nat_mod64_ushr1 (v : BitVec 32) :
    (v.toNat % 2 ^ 64) >>> 1 = v.toNat / 2 := by
  rw [Nat.mod_eq_of_lt (lt_trans v.isLt (by decide)), Nat.shiftRight_eq_div_pow, Nat.pow_one]

theorem m7_nat_mod64lit_ushr1 (v : BitVec 32) :
    (v.toNat % 18446744073709551616) >>> 1 = v.toNat / 2 :=
  m7_nat_mod64_ushr1 v

theorem m7_load_tmp {c : FullCfg} {s : FullState} {tmp' wsort' : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hi : i.toNat < tmp'.length)
    (hm : (FullMem c { core := { s.core with tmp := tmp' }
                       scratch := { s.scratch with wsort := wsort' } } ⋆ R) m) :
    loadVal m i32 (c.pTmp + i * 4) = some tmp'[i.toNat] :=
  c0_load_full_tmp (s := { core := { s.core with tmp := tmp' }
                           scratch := { s.scratch with wsort := wsort' } }) hi hm

theorem m7_load_wsort {c : FullCfg} {s : FullState} {tmp' wsort' : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hi : i.toNat < wsort'.length)
    (hm : (FullMem c { core := { s.core with tmp := tmp' }
                       scratch := { s.scratch with wsort := wsort' } } ⋆ R) m) :
    loadVal m i32 (c.pWsort + i * 4) = some wsort'[i.toNat] :=
  c0_load_full_wsort (s := { core := { s.core with tmp := tmp' }
                             scratch := { s.scratch with wsort := wsort' } }) hi hm

theorem m7_load_lvl {c : FullCfg} {s : FullState} {tmp' wsort' : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hi : i.toNat < s.core.lvl.length)
    (hm : (FullMem c { core := { s.core with tmp := tmp' }
                       scratch := { s.scratch with wsort := wsort' } } ⋆ R) m) :
    loadVal m i32 (c.pLevel + i * 4) = some s.core.lvl[i.toNat] :=
  c0_load_full_lvl (s := { core := { s.core with tmp := tmp' }
                           scratch := { s.scratch with wsort := wsort' } }) hi hm

theorem m7_load_tpos {c : FullCfg} {s : FullState} {tmp' wsort' : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hi : i.toNat < s.core.trail_pos.length)
    (hm : (FullMem c { core := { s.core with tmp := tmp' }
                       scratch := { s.scratch with wsort := wsort' } } ⋆ R) m) :
    loadVal m i32 (c.pTrailPos + i * 4) = some s.core.trail_pos[i.toNat] :=
  c0_load_full_trail_pos (s := { core := { s.core with tmp := tmp' }
                                 scratch := { s.scratch with wsort := wsort' } }) hi hm

theorem m7Bkt_eq (lvl : List (BitVec 32)) (minL : Nat) (x : BitVec 32) :
    m7Bkt lvl minL x = (lvl[x.toNat / 2]?.getD 0#32).toNat - minL := by
  unfold m7Bkt; rfl

theorem m7BktCnt_nil (lvl : List (BitVec 32)) (minL b : Nat) :
    m7BktCnt lvl minL [] b = 0 := by
  unfold m7BktCnt; rfl

theorem m7Slice_perm_of_take {α : Type _} {xs ys : List α} {n : Nat}
    (h0 : xs[0]? = ys[0]?) (hperm : (xs.take n).Perm (ys.take n))
    (hpos : 0 < n) (hx : n ≤ xs.length) (hy : n ≤ ys.length) :
    (m7Slice xs 1 n).Perm (m7Slice ys 1 n) := by
  have htx : xs.take n = xs[0]'(by omega) :: m7Slice xs 1 n := by
    apply List.ext_getElem
    · simp [m7Slice_length]; omega
    · intro k hk1 hk2
      rcases k with _ | k'
      · simp
      · simp [m7Slice_getElem, Nat.add_comm]
  have hty : ys.take n = ys[0]'(by omega) :: m7Slice ys 1 n := by
    apply List.ext_getElem
    · simp [m7Slice_length]; omega
    · intro k hk1 hk2
      rcases k with _ | k'
      · simp
      · simp [m7Slice_getElem, Nat.add_comm]
  have heq0 : xs[0]'(by omega) = ys[0]'(by omega) := by
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at h0
    exact Option.some.inj h0
  rw [htx, hty, heq0] at hperm
  exact (List.perm_cons _).mp hperm

end LeanQbe.T.Examples.Kissat.FullM7AnalyzeSort
