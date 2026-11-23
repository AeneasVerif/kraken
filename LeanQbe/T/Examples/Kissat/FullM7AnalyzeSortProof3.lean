module

public import LeanQbe.T.Examples.Kissat.FullM7AnalyzeSortProof2
import LeanQbe.T.Examples.Kissat.FullMinLemmas1
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.MemLemmas
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Wave 4G Proof Shard 3: Opaque-State Wrappers & Pure Invariant Helpers

M1-clean helper module (`public section`, `0 @[expose]`, `0 import all`) isolating:
1. Opaque `FullState` packing, load, store, and heap-focus wrappers (`m7_wrap_state`,
   `m7_load_*_of`, `m7_store_*_upd`, `m7_wrap_upd_tmp`) so `whnf`/`isDefEq` never unfold
   `70`-field `FullState` record literals inside WP loop proofs.
2. Extracted pure loop-step and exit invariant lemmas (`Ins`, `Copy`, `Hist`, `Pref`,
   `Scat`, `Scan`, `RIns`, `Run`) consumed by `FullM7AnalyzeSortProof4`.
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
open Kraken.Bedrock2.Test

/-! ## 1. Opaque `FullState` Packing, Load & Store Helpers -/

theorem m7_core_tmp_eq {st s : FullState} {tmp_cur : List (BitVec 32)}
    (hc : st.core = { s.core with tmp := tmp_cur }) : st.core.tmp = tmp_cur := by rw [hc]

theorem m7_core_lvl_eq {st s : FullState} {tmp_cur : List (BitVec 32)}
    (hc : st.core = { s.core with tmp := tmp_cur }) : st.core.lvl = s.core.lvl := by rw [hc]

theorem m7_core_tpos_eq {st s : FullState} {tmp_cur : List (BitVec 32)}
    (hc : st.core = { s.core with tmp := tmp_cur }) :
    st.core.trail_pos = s.core.trail_pos := by rw [hc]

theorem m7_scr_ws_eq {st s : FullState} {ws_cur : List (BitVec 32)}
    (hs : st.scratch = { s.scratch with wsort := ws_cur }) :
    st.scratch.wsort = ws_cur := by rw [hs]

theorem m7_wrap_state {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) :
    ∃ st : FullState,
      st.core = { s.core with tmp := s.core.tmp } ∧
      st.scratch = { s.scratch with wsort := s.scratch.wsort } ∧
      (FullMem c st ⋆ R) m :=
  ⟨s, rfl, rfl, hm⟩

theorem m7_wrap_upd_tmp {c : FullCfg} {st s : FullState} {tmp0 tmp' : List (BitVec 32)}
    {sc0 : FullScratch} {R : Mem 64 → Prop} {m : Mem 64}
    (hc : st.core = { s.core with tmp := tmp0 }) (hs : st.scratch = sc0)
    (hm : (FullMem c { st with core := { st.core with tmp := tmp' } } ⋆ R) m) :
    ∃ st' : FullState,
      st'.core = { s.core with tmp := tmp' } ∧
      st'.scratch = sc0 ∧
      (FullMem c st' ⋆ R) m := by
  refine ⟨{ st with core := { st.core with tmp := tmp' } }, ?_, hs, hm⟩
  rw [hc]

theorem m7_load_tmp_of {c : FullCfg} {st s : FullState} {tmp_cur : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hc : st.core = { s.core with tmp := tmp_cur })
    (hi : i.toNat < tmp_cur.length) (hm : (FullMem c st ⋆ R) m) :
    loadVal m i32 (c.pTmp + i * 4) = some (tmp_cur[i.toNat]'hi) := by
  have hi' : i.toNat < st.core.tmp.length := by rw [hc]; exact hi
  have hld := c0_load_full_tmp (i := i) hi' hm
  rwa [show st.core.tmp[i.toNat]'hi' = tmp_cur[i.toNat]'hi from
    Option.some.inj ((List.getElem?_eq_getElem hi').symm.trans
      (by rw [hc]; exact List.getElem?_eq_getElem hi))] at hld

theorem m7_load_lvl_of {c : FullCfg} {st s : FullState} {tmp_cur : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hc : st.core = { s.core with tmp := tmp_cur })
    (hi : i.toNat < s.core.lvl.length) (hm : (FullMem c st ⋆ R) m) :
    loadVal m i32 (c.pLevel + i * 4) = some (s.core.lvl[i.toNat]'hi) := by
  have hi' : i.toNat < st.core.lvl.length := by rw [hc]; exact hi
  have hld := c0_load_full_lvl (i := i) hi' hm
  rwa [show st.core.lvl[i.toNat]'hi' = s.core.lvl[i.toNat]'hi from
    Option.some.inj ((List.getElem?_eq_getElem hi').symm.trans
      (by rw [hc]; exact List.getElem?_eq_getElem hi))] at hld

theorem m7_load_tpos_of {c : FullCfg} {st s : FullState} {tmp_cur : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hc : st.core = { s.core with tmp := tmp_cur })
    (hi : i.toNat < s.core.trail_pos.length) (hm : (FullMem c st ⋆ R) m) :
    loadVal m i32 (c.pTrailPos + i * 4) = some (s.core.trail_pos[i.toNat]'hi) := by
  have hi' : i.toNat < st.core.trail_pos.length := by rw [hc]; exact hi
  have hld := c0_load_full_trail_pos (i := i) hi' hm
  rwa [show st.core.trail_pos[i.toNat]'hi' = s.core.trail_pos[i.toNat]'hi from
    Option.some.inj ((List.getElem?_eq_getElem hi').symm.trans
      (by rw [hc]; exact List.getElem?_eq_getElem hi))] at hld

theorem m7_load_wsort_of {c : FullCfg} {st s : FullState} {ws_cur : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hs : st.scratch = { s.scratch with wsort := ws_cur })
    (hi : i.toNat < ws_cur.length) (hm : (FullMem c st ⋆ R) m) :
    loadVal m i32 (c.pWsort + i * 4) = some (ws_cur[i.toNat]'hi) := by
  have hi' : i.toNat < st.scratch.wsort.length := by rw [hs]; exact hi
  have hld := c0_load_full_wsort (i := i) hi' hm
  rwa [show st.scratch.wsort[i.toNat]'hi' = ws_cur[i.toNat]'hi from
    Option.some.inj ((List.getElem?_eq_getElem hi').symm.trans
      (by rw [hs]; exact List.getElem?_eq_getElem hi))] at hld

theorem m7_store_tmp_upd {c : FullCfg} {st s : FullState} {tmp_cur : List (BitVec 32)}
    {sc0 : FullScratch} {R : Mem 64 → Prop} {m : Mem 64}
    {i : BitVec 64} (v : BitVec 32)
    (hc : st.core = { s.core with tmp := tmp_cur }) (hs : st.scratch = sc0)
    (hi : i.toNat < tmp_cur.length) (hm : (FullMem c st ⋆ R) m) :
    ∃ st' : FullState,
      st'.core = { s.core with tmp := tmp_cur.set i.toNat v } ∧
      st'.scratch = sc0 ∧
      storeOk m i32 (c.pTmp + i * 4) ∧
      (FullMem c st' ⋆ R) (storeMem m i32 (c.pTmp + i * 4) v) := by
  have hi' : i.toNat < st.core.tmp.length := by rw [hc]; exact hi
  obtain ⟨hok, hm'⟩ := c0_store_full_tmp (i := i) v hi' hm
  refine ⟨{ st with core := { st.core with tmp := st.core.tmp.set i.toNat v } }, ?_, hs, hok, hm'⟩
  rw [hc]

theorem m7_store_wsort_upd {c : FullCfg} {st s : FullState}
    {tmp_cur ws_cur : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    {i : BitVec 64} (v : BitVec 32)
    (hc : st.core = { s.core with tmp := tmp_cur })
    (hs : st.scratch = { s.scratch with wsort := ws_cur })
    (hi : i.toNat < ws_cur.length) (hm : (FullMem c st ⋆ R) m) :
    ∃ st' : FullState,
      st'.core = { s.core with tmp := tmp_cur } ∧
      st'.scratch = { s.scratch with wsort := ws_cur.set i.toNat v } ∧
      storeOk m i32 (c.pWsort + i * 4) ∧
      (FullMem c st' ⋆ R) (storeMem m i32 (c.pWsort + i * 4) v) := by
  have hi' : i.toNat < st.scratch.wsort.length := by rw [hs]; exact hi
  obtain ⟨hok, hm'⟩ := c0_store_full_wsort (i := i) v hi' hm
  refine ⟨{ st with scratch := { st.scratch with wsort := st.scratch.wsort.set i.toNat v } },
    hc, ?_, hok, hm'⟩
  rw [hs]

/-! ## 2. Pure 3-Element & Insertion Sort Helpers -/

theorem m7_three_sorted_step {lvl tpos : List (BitVec 32)} {xs : List (BitVec 32)}
    (h12 : Full.fullTmpLe lvl tpos (xs[1]?.getD 0#32) (xs[2]?.getD 0#32)) :
    ∀ i j, 1 ≤ i → i ≤ j → j < 3 →
      Full.fullTmpLe lvl tpos (xs[i]?.getD 0#32) (xs[j]?.getD 0#32) := by
  intro i j hi hij hj
  have hcs : (i = 1 ∧ j = 1) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 2) := by omega
  rcases hcs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact m7_fullTmpLe_refl _ _ _
  · exact h12
  · exact m7_fullTmpLe_refl _ _ _

theorem m7_swap12_perm {xs : List (BitVec 32)} (h1 : 1 < xs.length) (h2 : 2 < xs.length)
    (h3 : 3 ≤ xs.length) :
    let x1 := xs[1]'h1
    let x2 := xs[2]'h2
    let xs' := (xs.set 1 x2).set 2 x1
    (m7Slice xs' 1 3).Perm (m7Slice xs 1 3) := by
  intro x1 x2 xs'
  exact m7_swap_slice_perm (xs := xs) (lo := 1) (hi := 3) (u := 1) (v := 2)
    (le_refl 1) (by decide) (by decide) h3

theorem m7_ins_exit_lvl {s : FullState} {tmp' : List (BitVec 32)}
    (hsorted : ∀ i j, 1 ≤ i → i ≤ j → j < s.core.tmp_len →
      Full.fullTmpLe s.core.lvl s.core.trail_pos (tmp'[i]?.getD 0#32) (tmp'[j]?.getD 0#32)) :
    ∀ i j, 1 ≤ i → i ≤ j → j < s.core.tmp_len →
      (s.core.lvl[(tmp'[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
      (s.core.lvl[(tmp'[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat := fun i j hi hij hj =>
  fullTmpLe_lvl_le (hsorted i j hi hij hj)

/-! ## 3. Pure Copy, Histogram, Prefix-Sum & Scatter Helpers -/

theorem m7_copy_init_inv {c : FullCfg} {s : FullState} {ws0 : List (BitVec 32)}
    (htmp_len : s.core.tmp.length = c.max_vars) (hlvl_len : s.core.lvl.length = c.max_vars)
    (hws_len : ws0.length = 2 * c.max_vars) (htl : 2 ≤ s.core.tmp_len)
    (hle_mv : s.core.tmp_len ≤ c.max_vars)
    (hbd1 : (s.core.tmp[1]?.getD 0#32).toNat < 2 * c.max_vars) :
    let x1 := s.core.tmp[1]'(by rw [htmp_len]; omega)
    let l1 := s.core.lvl[(s.core.tmp[1]'(by rw [htmp_len]; omega)).toNat / 2]'(by
      have hbd1' := hbd1
      rw [List.getElem?_eq_getElem (l := s.core.tmp) (i := 1) (by rw [htmp_len]; omega),
        Option.getD_some] at hbd1'
      rw [hlvl_len]; omega)
    let ws1 := ws0.set 1 x1
    ws1.length = 2 * c.max_vars ∧
    m7Slice ws1 1 2 = m7Slice s.core.tmp 1 2 ∧
    (∀ p, 1 ≤ p → p < 2 →
      l1.toNat ≤ (s.core.lvl[(ws1[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ∧
      (s.core.lvl[(ws1[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ l1.toNat) := by
  intro x1 l1 ws1
  have hi1_t : 1 < s.core.tmp.length := by rw [htmp_len]; omega
  have hi1_w : 1 < ws0.length := by rw [hws_len]; omega
  have hx1_bd : x1.toNat < 2 * c.max_vars := by
    have := hbd1
    rwa [List.getElem?_eq_getElem (l := s.core.tmp) (i := 1) hi1_t, Option.getD_some] at this
  have h1 := m7Slice_set_end ws0 (lo := 1) (dst := 1) x1 (le_refl 1) hi1_w
  have h2 := m7Slice_append_succ s.core.tmp (lo := 1) (hi := 1) (le_refl 1) hi1_t
  have h1' : m7Slice ws1 1 2 = [x1] := by simpa [ws1, m7Slice_nil _ (le_refl 1)] using h1
  have h2' : m7Slice s.core.tmp 1 2 = [x1] := by
    simpa [m7Slice_nil _ (le_refl 1), x1] using h2
  refine ⟨by simp [ws1, hws_len], h1'.trans h2'.symm, fun p hp1 hp2 => ?_⟩
  have hp : p = 1 := by omega
  subst hp
  have hws_1 : ws1[1]? = some x1 := by simp [ws1, hi1_w]
  have hl1_eq : (s.core.lvl[x1.toNat / 2]?.getD 0#32).toNat = l1.toNat := by
    rw [List.getElem?_eq_getElem (l := s.core.lvl) (i := x1.toNat / 2)
      (by rw [hlvl_len]; omega), Option.getD_some]
  rw [hws_1, Option.getD_some, hl1_eq]; exact ⟨le_refl _, le_refl _⟩

theorem m7_copy_step_inv {c : FullCfg} {s : FullState} {ws_k : List (BitVec 32)}
    {k : Nat} {min_l' max_l' lx : BitVec 32}
    (htmp_len : s.core.tmp.length = c.max_vars) (hlvl_len : s.core.lvl.length = c.max_vars)
    (hlen_wk : ws_k.length = 2 * c.max_vars) (hk2 : 2 ≤ k) (hk_lt : k < s.core.tmp_len)
    (hle_mv : s.core.tmp_len ≤ c.max_vars) (hsl_wk : m7Slice ws_k 1 k = m7Slice s.core.tmp 1 k)
    (hbd_k : (s.core.tmp[k]?.getD 0#32).toNat < 2 * c.max_vars)
    (hlx_def : lx = s.core.lvl[(s.core.tmp[k]'(by rw [htmp_len]; omega)).toNat / 2]'(by
      have hbd_k' := hbd_k
      rw [List.getElem?_eq_getElem (l := s.core.tmp) (i := k) (by rw [htmp_len]; omega),
        Option.getD_some] at hbd_k'
      rw [hlvl_len]; omega))
    (hmn_le_lx : min_l'.toNat ≤ lx.toNat) (hlx_le_mx : lx.toNat ≤ max_l'.toNat)
    (hmn_pre : ∀ p, 1 ≤ p → p < k →
      min_l'.toNat ≤ (s.core.lvl[(ws_k[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)
    (hmx_pre : ∀ p, 1 ≤ p → p < k →
      (s.core.lvl[(ws_k[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ max_l'.toNat) :
    let x := s.core.tmp[k]'(by rw [htmp_len]; omega)
    let ws_k1 := ws_k.set k x
    ws_k1.length = 2 * c.max_vars ∧
    m7Slice ws_k1 1 (k + 1) = m7Slice s.core.tmp 1 (k + 1) ∧
    (∀ p, 1 ≤ p → p < k + 1 →
      min_l'.toNat ≤ (s.core.lvl[(ws_k1[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ∧
      (s.core.lvl[(ws_k1[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ max_l'.toNat) := by
  intro x ws_k1
  have hk_tmp : k < s.core.tmp.length := by rw [htmp_len]; omega
  have hk_ws : k < ws_k.length := by rw [hlen_wk]; omega
  have hx_bd : x.toNat < 2 * c.max_vars := by
    have := hbd_k
    rwa [List.getElem?_eq_getElem (l := s.core.tmp) (i := k) hk_tmp, Option.getD_some] at this
  have h1 := m7Slice_set_end ws_k (lo := 1) (dst := k) x (by omega) hk_ws
  have h2 := m7Slice_append_succ s.core.tmp (lo := 1) (hi := k) (by omega) hk_tmp
  refine ⟨by simp [ws_k1, hlen_wk], by rw [h1, hsl_wk, h2], fun p hp1 hp2 => ?_⟩
  by_cases hpk : p = k
  · subst hpk
    have hpk_get : ws_k1[p]? = some x := by
      dsimp only [ws_k1]
      rw [List.getElem?_eq_getElem (by simpa using hk_ws), List.getElem_set_self]
    have hlx_eq : (s.core.lvl[x.toNat / 2]?.getD 0#32).toNat = lx.toNat := by
      rw [List.getElem?_eq_getElem (l := s.core.lvl) (i := x.toNat / 2)
        (by rw [hlvl_len]; omega), Option.getD_some, hlx_def]
    rw [hpk_get, Option.getD_some, hlx_eq]; exact ⟨hmn_le_lx, hlx_le_mx⟩
  · have hpe : ws_k1[p]? = ws_k[p]? := by
      dsimp only [ws_k1]; rw [List.getElem?_set_ne (Ne.symm hpk)]
    rw [hpe]; exact ⟨hmn_pre p hp1 (by omega), hmx_pre p hp1 (by omega)⟩

private theorem m7BktCnt_le (lvl : List (BitVec 32)) (minL : Nat) (xs : List (BitVec 32))
    (b : Nat) : m7BktCnt lvl minL xs b ≤ xs.length := by
  induction xs with
  | nil => rw [m7BktCnt_nil]; simp
  | cons y ys ih =>
    rw [List.length_cons, ← List.singleton_append, m7BktCnt_append_list]
    have h1 : m7BktCnt lvl minL [y] b ≤ 1 := by
      rw [← List.nil_append [y], m7BktCnt_append, m7BktCnt_nil]
      split <;> omega
    omega

theorem m7_hist_step_cnt {c : FullCfg} {s : FullState}
    {ws_k wst_h : List (BitVec 32)} {k minL span : Nat}
    (_hlvl_len : s.core.lvl.length = c.max_vars)
    (hlen_wk : ws_k.length = 2 * c.max_vars) (hlen_wh : wst_h.length = c.max_vars)
    (hk1 : 1 ≤ k) (hk_lt : k < s.core.tmp_len) (hle_mv : s.core.tmp_len ≤ c.max_vars)
    (hminmax : ∀ p, 1 ≤ p → p < s.core.tmp_len →
      minL ≤ (s.core.lvl[(ws_k[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ∧
      (s.core.lvl[(ws_k[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat < minL + span)
    (hcnt_h : ∀ b < span, (wst_h[b]?.getD 0#32).toNat =
      m7BktCnt s.core.lvl minL (m7Slice ws_k 1 k) b)
    (hspan_le : span ≤ c.max_vars) :
    let x := ws_k[k]'(by rw [hlen_wk]; omega)
    let bi := m7Bkt s.core.lvl minL x
    let old := wst_h[bi]'(by
      have hx1 := (hminmax k hk1 hk_lt).1
      have hx2 := (hminmax k hk1 hk_lt).2
      rw [List.getElem?_eq_getElem (l := ws_k) (i := k) (by rw [hlen_wk]; omega),
        Option.getD_some] at hx1 hx2
      have hbi : bi < span := by dsimp only [bi, x]; rw [m7Bkt_eq]; omega
      omega)
    let wst_h1 := wst_h.set bi (BitVec.ofNat 32 (old.toNat + 1))
    bi < span ∧
    old.toNat + 1 ≤ k ∧
    wst_h1.length = c.max_vars ∧
    (∀ b < span, (wst_h1[b]?.getD 0#32).toNat =
      m7BktCnt s.core.lvl minL (m7Slice ws_k 1 (k + 1)) b) := by
  intro x bi old wst_h1
  have hks_ws : k < ws_k.length := by rw [hlen_wk]; omega
  have hmin_x := (hminmax k hk1 hk_lt).1
  have hmax_x := (hminmax k hk1 hk_lt).2
  rw [List.getElem?_eq_getElem (l := ws_k) (i := k) hks_ws, Option.getD_some] at hmin_x hmax_x
  have hbi_lt : bi < span := by dsimp only [bi, x]; rw [m7Bkt_eq]; omega
  have hbi_arr : bi < wst_h.length := by omega
  have hcnt_old : old.toNat = m7BktCnt s.core.lvl minL (m7Slice ws_k 1 k) bi := by
    have h1 := hcnt_h bi hbi_lt
    rwa [List.getElem?_eq_getElem (l := wst_h) (i := bi) hbi_arr, Option.getD_some] at h1
  have hcnt_le : old.toNat ≤ k - 1 := by
    rw [hcnt_old]
    have hle := m7BktCnt_le s.core.lvl minL (m7Slice ws_k 1 k) bi
    rw [m7Slice_length] at hle; omega
  have hold1_32 : old.toNat + 1 < 2 ^ 32 := by have := c.hmaxv; unfold dimacsBound at this; omega
  refine ⟨hbi_lt, by omega, by simp [wst_h1, hlen_wh], fun b hb => ?_⟩
  rw [m7Slice_append_succ ws_k hk1 hks_ws, m7BktCnt_append]
  by_cases hbb : b = bi
  · subst hbb
    have hb1 : bi < wst_h1.length := by simp [wst_h1]; omega
    rw [List.getElem?_eq_getElem (l := wst_h1) (i := bi) hb1, Option.getD_some]
    dsimp only [wst_h1]; rw [List.getElem_set_self, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hold1_32, hcnt_old]
    simp only [bi, x, ↓reduceIte]
  · dsimp only [bi, x] at hbb
    simp only [hbb, ↓reduceIte, Nat.add_zero]
    have hne : wst_h1[b]? = wst_h[b]? := by
      dsimp only [wst_h1]; rw [List.getElem?_set_ne (Ne.symm hbb)]
    rw [hne]; exact hcnt_h b hb

theorem m7_pref_step_inv {tot : Nat → Nat} {wst_p : List (BitVec 32)}
    {j span span_cap : Nat} {run_sum : BitVec 64}
    (hlen_wp : wst_p.length = span_cap) (hj_lt : j < span)
    (hspan_le : span ≤ span_cap)
    (hsum : run_sum.toNat = m7PrefixStart tot j)
    (hsuf : ∀ b, j ≤ b → b < span → (wst_p[b]?.getD 0#32).toNat = tot b)
    (hpre : ∀ b < j, (wst_p[b]?.getD 0#32).toNat = m7PrefixStart tot b)
    (hs_bound : m7PrefixStart tot (j + 1) < 2 ^ 32) :
    let wj := wst_p[j]'(by omega)
    let wst_p1 := wst_p.set j (BitVec.ofNat 32 run_sum.toNat)
    let run_sum1 := run_sum + wj.setWidth 64
    run_sum1.toNat = m7PrefixStart tot (j + 1) ∧
    (∀ b, j + 1 ≤ b → b < span → (wst_p1[b]?.getD 0#32).toNat = tot b) ∧
    (∀ b < j + 1, (wst_p1[b]?.getD 0#32).toNat = m7PrefixStart tot b) := by
  intro wj wst_p1 run_sum1
  have hwj_tot : wj.toNat = tot j := by
    have h := hsuf j (le_refl _) hj_lt
    rwa [List.getElem?_eq_getElem (l := wst_p) (i := j) (by omega), Option.getD_some] at h
  have hsum_step : m7PrefixStart tot (j + 1) = run_sum.toNat + wj.toNat := by
    rw [m7PrefixStart_succ, hsum, hwj_tot]
  have hr_32 : run_sum.toNat < 2 ^ 32 := by
    have : m7PrefixStart tot j ≤ m7PrefixStart tot (j + 1) := by
      rw [m7PrefixStart_succ]; exact Nat.le_add_right _ _
    omega
  have hr1_eq : run_sum1.toNat = m7PrefixStart tot (j + 1) := by
    have hr64 : run_sum.toNat < 2 ^ 64 := Nat.lt_trans hr_32 (by decide)
    have hw64 : (wj.setWidth 64).toNat = wj.toNat := by
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans wj.isLt (by decide))]
    have hadd_lt : run_sum.toNat + wj.toNat < 2 ^ 64 :=
      Nat.lt_trans (hsum_step ▸ hs_bound) (by decide)
    dsimp only [run_sum1]
    rw [BitVec.toNat_add, hw64, Nat.mod_eq_of_lt hadd_lt, ← hsum_step]
  refine ⟨hr1_eq, fun b hb1 hb2 => ?_, fun b hb => ?_⟩
  · have hne : wst_p1[b]? = wst_p[b]? := by
      dsimp only [wst_p1]; rw [List.getElem?_set_ne (by omega)]
    rw [hne]; exact hsuf b (by omega) hb2
  · by_cases hbj : b = j
    · subst hbj
      have hb1 : b < wst_p1.length := by simp [wst_p1]; omega
      rw [List.getElem?_eq_getElem (l := wst_p1) (i := b) hb1, Option.getD_some]
      dsimp only [wst_p1]; rw [List.getElem_set_self, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hr_32, hsum]
    · have hne : wst_p1[b]? = wst_p[b]? := by
        dsimp only [wst_p1]; rw [List.getElem?_set_ne (Ne.symm hbj)]
      rw [hne]; exact hpre b (by omega)

theorem m7_scat_step_inv {c : FullCfg} {s : FullState}
    {ws_k tmp_s wst_s : List (BitVec 32)} {minL span N k_s : Nat}
    (hlen_wk : ws_k.length = 2 * c.max_vars) (hlen_ts : tmp_s.length = c.max_vars)
    (hlen_ws : wst_s.length = c.max_vars) (htl : N ≤ c.max_vars)
    (hk1 : 1 ≤ k_s) (hk_lt : k_s < N) (hspan_le : span ≤ c.max_vars)
    (hminmax : ∀ p, 1 ≤ p → p < N →
      minL ≤ (s.core.lvl[(ws_k[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ∧
      (s.core.lvl[(ws_k[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat < minL + span)
    (hspos_N : m7PrefixStart (m7BktCnt s.core.lvl minL (m7Slice ws_k 1 N)) span = N)
    (hspos_le : ∀ b ≤ span, m7PrefixStart (m7BktCnt s.core.lvl minL (m7Slice ws_k 1 N)) b ≤ N)
    (h0_s : tmp_s[0]? = s.core.tmp[0]?)
    (hout_s : ∀ q, N ≤ q → tmp_s[q]? = s.core.tmp[q]?)
    (hepos_s : ∀ b < span, (wst_s[b]?.getD 0#32).toNat =
      m7PrefixStart (m7BktCnt s.core.lvl minL (m7Slice ws_k 1 N)) b +
      m7BktCnt s.core.lvl minL (m7Slice ws_k 1 k_s) b)
    (hbkt_s : ∀ b < span, ∀ p,
      m7PrefixStart (m7BktCnt s.core.lvl minL (m7Slice ws_k 1 N)) b ≤ p →
      p < (wst_s[b]?.getD 0#32).toNat →
      m7Bkt s.core.lvl minL (tmp_s[p]?.getD 0#32) = b ∧
      minL ≤ (s.core.lvl[(tmp_s[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)
    (hperm_s : (m7FlatBkts tmp_s
      (m7PrefixStart (m7BktCnt s.core.lvl minL (m7Slice ws_k 1 N)))
      (fun b => (wst_s[b]?.getD 0#32).toNat) span).Perm (m7Slice ws_k 1 k_s)) :
    let x := ws_k[k_s]'(by rw [hlen_wk]; omega)
    let bi := m7Bkt s.core.lvl minL x
    let tot := m7BktCnt s.core.lvl minL (m7Slice ws_k 1 N)
    let spos := m7PrefixStart tot
    let dst := (wst_s[bi]'(by
      have h1 := (hminmax k_s hk1 hk_lt).1
      have h2 := (hminmax k_s hk1 hk_lt).2
      rw [List.getElem?_eq_getElem (l := ws_k) (i := k_s) (by rw [hlen_wk]; omega),
        Option.getD_some] at h1 h2
      have hbi : bi < span := by dsimp only [bi, x]; rw [m7Bkt_eq]; omega
      omega)).toNat
    let wst_s1 := wst_s.set bi (BitVec.ofNat 32 (dst + 1))
    let tmp_s1 := tmp_s.set dst x
    bi < span ∧ 1 ≤ dst ∧ dst < N ∧ dst + 1 < 2 ^ 32 ∧
    tmp_s1.length = c.max_vars ∧ wst_s1.length = c.max_vars ∧
    tmp_s1[0]? = s.core.tmp[0]? ∧
    (∀ q, N ≤ q → tmp_s1[q]? = s.core.tmp[q]?) ∧
    (∀ b < span, (wst_s1[b]?.getD 0#32).toNat =
      spos b + m7BktCnt s.core.lvl minL (m7Slice ws_k 1 (k_s + 1)) b) ∧
    (∀ b < span, ∀ p, spos b ≤ p → p < (wst_s1[b]?.getD 0#32).toNat →
      m7Bkt s.core.lvl minL (tmp_s1[p]?.getD 0#32) = b ∧
      minL ≤ (s.core.lvl[(tmp_s1[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) ∧
    (m7FlatBkts tmp_s1 spos (fun b => (wst_s1[b]?.getD 0#32).toNat) span).Perm
      (m7Slice ws_k 1 (k_s + 1)) := by
  intro x bi tot spos dst wst_s1 tmp_s1
  have hks_ws : k_s < ws_k.length := by rw [hlen_wk]; omega
  have hlx_min : minL ≤ (s.core.lvl[x.toNat / 2]?.getD 0#32).toNat := by
    have h := (hminmax k_s hk1 hk_lt).1
    rwa [List.getElem?_eq_getElem (l := ws_k) (i := k_s) hks_ws, Option.getD_some] at h
  have hlx_max : (s.core.lvl[x.toNat / 2]?.getD 0#32).toNat < minL + span := by
    have h := (hminmax k_s hk1 hk_lt).2
    rwa [List.getElem?_eq_getElem (l := ws_k) (i := k_s) hks_ws, Option.getD_some] at h
  have hbi_lt : bi < span := by dsimp only [bi]; rw [m7Bkt_eq]; omega
  have hbi_arr : bi < wst_s.length := by omega
  have hpref_de : m7Slice ws_k 1 N =
      m7Slice ws_k 1 (k_s + 1) ++ m7Slice ws_k (k_s + 1) N :=
    (m7Slice_append_slice ws_k (by omega) (by omega) (by rw [hlen_wk]; omega)).symm
  have htot_split : tot bi =
      m7BktCnt s.core.lvl minL (m7Slice ws_k 1 k_s) bi +
      1 + m7BktCnt s.core.lvl minL (m7Slice ws_k (k_s + 1) N) bi := by
    dsimp only [tot]
    rw [hpref_de, m7Slice_append_succ ws_k hk1 hks_ws, m7BktCnt_append_list, m7BktCnt_append]
    simp only [bi, x, ↓reduceIte]
  have hdst_nat : dst = spos bi + m7BktCnt s.core.lvl minL (m7Slice ws_k 1 k_s) bi := by
    have he1 := hepos_s bi hbi_lt
    dsimp only [dst]
    rwa [List.getElem?_eq_getElem (l := wst_s) (i := bi) hbi_arr, Option.getD_some] at he1
  have hdst_hi : dst < spos (bi + 1) := by
    have hs_r : spos (bi + 1) = spos bi + tot bi := m7PrefixStart_succ _ _
    omega
  have hdst_ge1 : 1 ≤ dst := by
    have h1 : 1 ≤ spos bi := m7PrefixStart_ge1 tot bi
    omega
  have hdst_N : dst < N := Nat.lt_of_lt_of_le hdst_hi (hspos_le (bi + 1) hbi_lt)
  have hdst_tmp : dst < tmp_s.length := by rw [hlen_ts]; omega
  have hdst1_32 : dst + 1 < 2 ^ 32 := by have := c.hmaxv; unfold dimacsBound at this; omega
  have hepos_eq : ∀ b < span, (wst_s1[b]?.getD 0#32).toNat =
      if b = bi then (wst_s[bi]?.getD 0#32).toNat + 1
      else (wst_s[b]?.getD 0#32).toNat := fun b hb => by
    by_cases hbb : b = bi
    · subst hbb
      have hb1 : bi < wst_s1.length := by simp [wst_s1, hbi_arr]
      rw [List.getElem?_eq_getElem (l := wst_s1) (i := bi) hb1,
        List.getElem?_eq_getElem (l := wst_s) (i := bi) hbi_arr, Option.getD_some,
        Option.getD_some]
      simp only [wst_s1, List.getElem_set_self, ↓reduceIte, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hdst1_32]
      rfl
    · simp only [wst_s1, hbb, ↓reduceIte]; rw [List.getElem?_set_ne (Ne.symm hbb)]
  have hflat_perm := m7FlatBkts_scatter tmp_s spos (fun b => (wst_s[b]?.getD 0#32).toNat)
    span bi x hbi_lt (m7PrefixStart_zero _)
    (fun b _ => by dsimp only [spos, tot]; rw [m7PrefixStart_succ]; omega)
    (fun b hb => by dsimp only [spos, tot]; rw [hepos_s b hb]; omega)
    (fun b hb => by
      have h1 := hepos_s b hb
      have h2 : m7BktCnt s.core.lvl minL (m7Slice ws_k 1 k_s) b ≤ tot b := by
        have hd := m7Slice_append_slice ws_k hk1 (le_of_lt hk_lt) (by rw [hlen_wk]; omega)
        dsimp only [tot]; rw [← hd, m7BktCnt_append_list]; omega
      have hsr : spos (b + 1) = spos b + tot b := m7PrefixStart_succ _ _
      dsimp only [spos, tot] at h1 h2 hsr ⊢; omega)
    (by have h1 := hepos_s bi hbi_lt
        dsimp only [spos, tot] at h1 hdst_nat hdst_hi ⊢; omega)
    (by dsimp only [spos, tot]; rw [hspos_N, hlen_ts]; exact htl)
  have hflat_congr :
      m7FlatBkts tmp_s1 spos (fun b => (wst_s1[b]?.getD 0#32).toNat) span =
      m7FlatBkts (tmp_s.set dst x) spos
        (fun b => if b = bi then (wst_s[bi]?.getD 0#32).toNat + 1
          else (wst_s[b]?.getD 0#32).toNat) span := by
    have hcon : ∀ m ≤ span,
        m7FlatBkts tmp_s1 spos (fun b => (wst_s1[b]?.getD 0#32).toNat) m =
        m7FlatBkts (tmp_s.set dst x) spos
          (fun b => if b = bi then (wst_s[bi]?.getD 0#32).toNat + 1
            else (wst_s[b]?.getD 0#32).toNat) m := by
      intro m hm
      induction m with
      | zero => rw [m7FlatBkts_zero, m7FlatBkts_zero]
      | succ j ihj => rw [m7FlatBkts_succ, m7FlatBkts_succ, ihj (by omega), hepos_eq j (by omega)]
    exact hcon span (le_refl _)
  refine ⟨hbi_lt, hdst_ge1, hdst_N, hdst1_32, by simp [tmp_s1, hlen_ts], by simp [wst_s1, hlen_ws],
    by rw [← h0_s]; dsimp [tmp_s1]; rw [List.getElem?_set_ne (by omega)],
    fun q hq => by rw [← hout_s q hq]; dsimp [tmp_s1]; rw [List.getElem?_set_ne (by omega)],
    fun b hb => by
      rw [hepos_eq b hb, m7Slice_append_succ ws_k hk1 hks_ws, m7BktCnt_append]
      by_cases hbb : b = bi
      · subst hbb; simp only [↓reduceIte]
        rw [hepos_s bi hb]; dsimp only [spos, tot]; simp only [bi, x, ↓reduceIte]; omega
      · have hbb' : b ≠ m7Bkt s.core.lvl minL ws_k[k_s] := by dsimp [bi, x] at hbb; exact hbb
        simp only [hbb, hbb', ↓reduceIte, Nat.add_zero]
        rw [hepos_s b hb],
    fun b hb p hp1 hp2 => by
      rw [hepos_eq b hb] at hp2
      by_cases hp_d : p = dst
      · subst hp_d
        have hbb : b = bi := by
          by_cases hne : b = bi
          · exact hne
          exfalso; simp only [hne, ↓reduceIte] at hp2
          have h1 := hepos_s b hb
          have htot_b : m7BktCnt s.core.lvl minL (m7Slice ws_k 1 k_s) b ≤ tot b := by
            have hd := m7Slice_append_slice ws_k hk1 (le_of_lt hk_lt) (by rw [hlen_wk]; omega)
            dsimp only [tot]; rw [← hd, m7BktCnt_append_list]; omega
          have hb_not : b < bi ∨ bi < b := by omega
          rcases hb_not with hlt | hgt
          · have : spos (b + 1) ≤ spos bi := m7PrefixStart_mono (by omega)
            have : spos b + tot b = spos (b + 1) := (m7PrefixStart_succ _ _).symm
            dsimp only [spos, tot] at *; omega
          · have : spos (bi + 1) ≤ spos b := m7PrefixStart_mono (by omega)
            dsimp only [spos, tot] at *; omega
        subst hbb
        have hpt : dst < tmp_s1.length := by simp [tmp_s1, hdst_tmp]
        rw [List.getElem?_eq_getElem (l := tmp_s1) (i := dst) hpt, Option.getD_some]
        simp only [tmp_s1, List.getElem_set_self]
        exact ⟨rfl, hlx_min⟩
      · have hps : tmp_s1[p]? = tmp_s[p]? := by
          dsimp [tmp_s1]; rw [List.getElem?_set_ne (Ne.symm hp_d)]
        rw [hps]
        have hp2' : p < (wst_s[b]?.getD 0#32).toNat := by
          by_cases hbb : b = bi
          · subst hbb; simp only [↓reduceIte] at hp2
            have hd_e : (wst_s[bi]?.getD 0#32).toNat = dst := by
              simp [dst, List.getElem?_eq_getElem (l := wst_s) (i := bi) hbi_arr,
                Option.getD_some]
            omega
          · simp only [hbb, ↓reduceIte] at hp2; exact hp2
        exact hbkt_s b hb p hp1 hp2',
    by rw [m7Slice_append_succ ws_k hk1 hks_ws, hflat_congr]
       have hdp : dst = (wst_s[bi]?.getD 0#32).toNat := by
         simp [dst, List.getElem?_eq_getElem (l := wst_s) (i := bi) hbi_arr, Option.getD_some]
       have hfl' := hflat_perm
       dsimp only [spos, tot] at hfl' ⊢
       rw [hdp]
       exact hfl'.trans (by simpa [x] using hperm_s.append_right [x])⟩

theorem m7_scat_finish_inv {c : FullCfg} {s : FullState}
    {ws_k tmp_s wst_s : List (BitVec 32)} {minL span N : Nat}
    (hlen_ts : tmp_s.length = c.max_vars) (htl : N ≤ c.max_vars)
    (hsl_wk : m7Slice ws_k 1 N = m7Slice s.core.tmp 1 N)
    (hspos_N : m7PrefixStart (m7BktCnt s.core.lvl minL (m7Slice ws_k 1 N)) span = N)
    (hepos_s : ∀ b < span, (wst_s[b]?.getD 0#32).toNat =
      m7PrefixStart (m7BktCnt s.core.lvl minL (m7Slice ws_k 1 N)) b +
      m7BktCnt s.core.lvl minL (m7Slice ws_k 1 N) b)
    (hbkt_s : ∀ b < span, ∀ p,
      m7PrefixStart (m7BktCnt s.core.lvl minL (m7Slice ws_k 1 N)) b ≤ p →
      p < (wst_s[b]?.getD 0#32).toNat →
      m7Bkt s.core.lvl minL (tmp_s[p]?.getD 0#32) = b ∧
      minL ≤ (s.core.lvl[(tmp_s[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)
    (hperm_s : (m7FlatBkts tmp_s
      (m7PrefixStart (m7BktCnt s.core.lvl minL (m7Slice ws_k 1 N)))
      (fun b => (wst_s[b]?.getD 0#32).toNat) span).Perm (m7Slice ws_k 1 N)) :
    (m7Slice tmp_s 1 N).Perm (m7Slice s.core.tmp 1 N) ∧
    (∀ i j, 1 ≤ i → i ≤ j → j < N →
      (s.core.lvl[(tmp_s[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
      (s.core.lvl[(tmp_s[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) := by
  let tot := m7BktCnt s.core.lvl minL (m7Slice ws_k 1 N)
  let spos := m7PrefixStart tot
  have he_eq_s : ∀ b < span, (wst_s[b]?.getD 0#32).toNat = spos (b + 1) := fun b hb => by
    rw [hepos_s b hb]; exact (m7PrefixStart_succ _ _).symm
  have hm_flat_eq : m7FlatBkts tmp_s spos (fun b => (wst_s[b]?.getD 0#32).toNat) span =
      m7Slice tmp_s 1 N := by
    have h1 : m7FlatBkts tmp_s spos (fun b => (wst_s[b]?.getD 0#32).toNat) span =
        m7FlatBkts tmp_s spos (fun b => spos (b + 1)) span := by
      have hcon : ∀ m ≤ span,
          m7FlatBkts tmp_s spos (fun b => (wst_s[b]?.getD 0#32).toNat) m =
          m7FlatBkts tmp_s spos (fun b => spos (b + 1)) m := by
        intro m hm
        induction m with
        | zero => rw [m7FlatBkts_zero, m7FlatBkts_zero]
        | succ j ihj => rw [m7FlatBkts_succ, m7FlatBkts_succ, ihj (by omega), he_eq_s j (by omega)]
      exact hcon span (le_refl _)
    rw [h1, m7FlatBkts_eq_slice tmp_s spos span (m7PrefixStart_zero _)
      (fun b _ => by dsimp only [spos]; rw [m7PrefixStart_succ]; omega)
      (by dsimp only [spos, tot]; rw [hspos_N, hlen_ts]; exact htl)]
    dsimp only [spos, tot]; rw [hspos_N]
  refine ⟨by rw [← hm_flat_eq, ← hsl_wk]; exact hperm_s, ?_⟩
  apply m7_bucket_lvl_le hspos_N
  · intro p hp1 hp2
    obtain ⟨b, hb, hp_lo, hp_hi⟩ := m7_find_bkt (tot := tot) (span := span) hp1 (hspos_N ▸ hp2)
    have hp_hi' : p < (wst_s[b]?.getD 0#32).toNat := by
      rw [he_eq_s b hb]; exact hp_hi
    exact (hbkt_s b hb p hp_lo hp_hi').2
  · intro b hb p hp1 hp2
    have hp2' : p < (wst_s[b]?.getD 0#32).toNat := by
      rw [he_eq_s b hb]; exact hp2
    exact (hbkt_s b hb p hp1 hp2').1

/-! ## 4. Pure Run-Sorting Helpers (`rlen = 2`, `RIns`, `Heap` Fallback, `RunNext`) -/

theorem m7_run_swap2_inv {c : FullCfg} {s : FullState} {tmp_r : List (BitVec 32)}
    {N rb rl : Nat}
    (htmp_len : s.core.tmp.length = c.max_vars)
    (hlen_r : tmp_r.length = c.max_vars) (hlvl_len : s.core.lvl.length = c.max_vars)
    (htpos_len : s.core.trail_pos.length = c.max_vars) (htl : N ≤ c.max_vars)
    (hrb1 : 1 ≤ rb) (hrb_2N : rb + 2 ≤ N)
    (hperm_r : (m7Slice tmp_r 1 N).Perm (m7Slice s.core.tmp 1 N))
    (hbd0 : ∀ p, 1 ≤ p → p < N → (s.core.tmp[p]?.getD 0#32).toNat < 2 * c.max_vars)
    (hre_eq : ∀ p, rb ≤ p → p < rb + 2 →
      (s.core.lvl[(tmp_r[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = rl)
    (hlt_tp :
      (s.core.trail_pos[(tmp_r[rb + 1]'(by rw [hlen_r]; omega)).toNat / 2]'(by
        have hbd := m7Slice_perm_bd hperm_r (by rw [hlen_r]; exact htl)
          (by rw [htmp_len]; exact htl) hbd0 (rb + 1) (by omega) (by omega)
        rw [List.getElem?_eq_getElem (l := tmp_r) (i := rb + 1) (by rw [hlen_r]; omega),
          Option.getD_some] at hbd
        rw [htpos_len]; omega)).toNat <
      (s.core.trail_pos[(tmp_r[rb]'(by rw [hlen_r]; omega)).toNat / 2]'(by
        have hbd := m7Slice_perm_bd hperm_r (by rw [hlen_r]; exact htl)
          (by rw [htmp_len]; exact htl) hbd0 rb (by omega) (by omega)
        rw [List.getElem?_eq_getElem (l := tmp_r) (i := rb) (by rw [hlen_r]; omega),
          Option.getD_some] at hbd
        rw [htpos_len]; omega)).toNat) :
    let a := tmp_r[rb]'(by rw [hlen_r]; omega)
    let c_lit := tmp_r[rb + 1]'(by rw [hlen_r]; omega)
    let tr2 := (tmp_r.set rb c_lit).set (rb + 1) a
    tr2.length = c.max_vars ∧
    (m7Slice tr2 rb (rb + 2)).Perm (m7Slice tmp_r rb (rb + 2)) ∧
    tr2[0]? = tmp_r[0]? ∧
    (∀ q, (q < rb ∨ rb + 2 ≤ q) → tr2[q]? = tmp_r[q]?) ∧
    (∀ i j, rb ≤ i → i ≤ j → j < rb + 2 →
      Full.fullTmpLe s.core.lvl s.core.trail_pos (tr2[i]?.getD 0#32) (tr2[j]?.getD 0#32)) := by
  intro a c_lit tr2
  have hr0_lt : rb < tmp_r.length := by rw [hlen_r]; omega
  have hr1_lt : rb + 1 < tmp_r.length := by rw [hlen_r]; omega
  have ha_bd := m7Slice_perm_bd hperm_r (by rw [hlen_r]; exact htl)
    (by rw [htmp_len]; exact htl) hbd0 rb hrb1 (by omega)
  have hc_bd := m7Slice_perm_bd hperm_r (by rw [hlen_r]; exact htl)
    (by rw [htmp_len]; exact htl) hbd0 (rb + 1) (by omega) (by omega)
  rw [List.getElem?_eq_getElem (l := tmp_r) (i := rb) hr0_lt, Option.getD_some] at ha_bd
  rw [List.getElem?_eq_getElem (l := tmp_r) (i := rb + 1) hr1_lt, Option.getD_some] at hc_bd
  have hperm2 := m7_subslice_set_swap_perm (zs := tmp_r) (lo := rb) (hi := rb + 2)
    (a := rb) (b := rb + 1) (le_refl rb) (by omega) (by omega) (by rw [hlen_r]; omega)
  have h1 := hre_eq rb (le_refl _) (by omega)
  have h2 := hre_eq (rb + 1) (by omega) (by omega)
  have hl_eq_ac : (s.core.lvl[c_lit.toNat / 2]'(by rw [hlvl_len]; dsimp [c_lit]; omega)).toNat =
      (s.core.lvl[a.toNat / 2]'(by rw [hlvl_len]; dsimp [a]; omega)).toNat := by
    rw [List.getElem?_eq_getElem (l := tmp_r) (i := rb) hr0_lt, Option.getD_some,
      List.getElem?_eq_getElem (l := s.core.lvl) (i := (tmp_r[rb]'hr0_lt).toNat / 2)
        (by rw [hlvl_len]; omega), Option.getD_some] at h1
    rw [List.getElem?_eq_getElem (l := tmp_r) (i := rb + 1) hr1_lt, Option.getD_some,
      List.getElem?_eq_getElem (l := s.core.lvl) (i := (tmp_r[rb + 1]'hr1_lt).toNat / 2)
        (by rw [hlvl_len]; omega), Option.getD_some] at h2
    dsimp only [a, c_lit]; exact h2.trans h1.symm
  have hca : Full.fullTmpLe s.core.lvl s.core.trail_pos c_lit a :=
    m7_fullTmpLe_of_eq_lvl_tpos (by rw [hlvl_len]; dsimp [c_lit]; omega)
      (by rw [hlvl_len]; dsimp [a]; omega) (by rw [htpos_len]; dsimp [c_lit]; omega)
      (by rw [htpos_len]; dsimp [a]; omega) hl_eq_ac (le_of_lt hlt_tp)
  have hc_get : tr2[rb]? = some c_lit := by simp [tr2, hr0_lt]
  have ha_get : tr2[rb + 1]? = some a := by simp [tr2, hr1_lt]
  refine ⟨by simp [tr2, hlen_r], by simpa [tr2, a, c_lit] using hperm2,
    by simp [tr2, Nat.ne_of_gt hrb1], fun q hq => by
      dsimp [tr2]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)],
    fun i j hi hij hj => ?_⟩
  have hcs : (i = rb ∧ j = rb) ∨ (i = rb ∧ j = rb + 1) ∨ (i = rb + 1 ∧ j = rb + 1) := by omega
  rcases hcs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact m7_fullTmpLe_refl _ _ _
  · rw [hc_get, ha_get, Option.getD_some, Option.getD_some]; exact hca
  · exact m7_fullTmpLe_refl _ _ _

theorem m7_run_noswap2_inv {c : FullCfg} {s : FullState} {tmp_r : List (BitVec 32)}
    {N rb rl : Nat}
    (htmp_len : s.core.tmp.length = c.max_vars)
    (hlen_r : tmp_r.length = c.max_vars) (hlvl_len : s.core.lvl.length = c.max_vars)
    (htpos_len : s.core.trail_pos.length = c.max_vars) (htl : N ≤ c.max_vars)
    (hrb1 : 1 ≤ rb) (hrb_2N : rb + 2 ≤ N)
    (hperm_r : (m7Slice tmp_r 1 N).Perm (m7Slice s.core.tmp 1 N))
    (hbd0 : ∀ p, 1 ≤ p → p < N → (s.core.tmp[p]?.getD 0#32).toNat < 2 * c.max_vars)
    (hre_eq : ∀ p, rb ≤ p → p < rb + 2 →
      (s.core.lvl[(tmp_r[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = rl)
    (hle_tp :
      (s.core.trail_pos[(tmp_r[rb]'(by rw [hlen_r]; omega)).toNat / 2]'(by
        have hbd := m7Slice_perm_bd hperm_r (by rw [hlen_r]; exact htl)
          (by rw [htmp_len]; exact htl) hbd0 rb (by omega) (by omega)
        rw [List.getElem?_eq_getElem (l := tmp_r) (i := rb) (by rw [hlen_r]; omega),
          Option.getD_some] at hbd
        rw [htpos_len]; omega)).toNat ≤
      (s.core.trail_pos[(tmp_r[rb + 1]'(by rw [hlen_r]; omega)).toNat / 2]'(by
        have hbd := m7Slice_perm_bd hperm_r (by rw [hlen_r]; exact htl)
          (by rw [htmp_len]; exact htl) hbd0 (rb + 1) (by omega) (by omega)
        rw [List.getElem?_eq_getElem (l := tmp_r) (i := rb + 1) (by rw [hlen_r]; omega),
          Option.getD_some] at hbd
        rw [htpos_len]; omega)).toNat) :
    ∀ i j, rb ≤ i → i ≤ j → j < rb + 2 →
      Full.fullTmpLe s.core.lvl s.core.trail_pos (tmp_r[i]?.getD 0#32) (tmp_r[j]?.getD 0#32) := by
  intro i j hi hij hj
  have hr0_lt : rb < tmp_r.length := by rw [hlen_r]; omega
  have hr1_lt : rb + 1 < tmp_r.length := by rw [hlen_r]; omega
  have ha_bd := m7Slice_perm_bd hperm_r (by rw [hlen_r]; exact htl)
    (by rw [htmp_len]; exact htl) hbd0 rb hrb1 (by omega)
  have hc_bd := m7Slice_perm_bd hperm_r (by rw [hlen_r]; exact htl)
    (by rw [htmp_len]; exact htl) hbd0 (rb + 1) (by omega) (by omega)
  rw [List.getElem?_eq_getElem (l := tmp_r) (i := rb) hr0_lt, Option.getD_some] at ha_bd
  rw [List.getElem?_eq_getElem (l := tmp_r) (i := rb + 1) hr1_lt, Option.getD_some] at hc_bd
  have h1 := hre_eq rb (le_refl _) (by omega)
  have h2 := hre_eq (rb + 1) (by omega) (by omega)
  have hl_eq_ac : (s.core.lvl[(tmp_r[rb]'hr0_lt).toNat / 2]'(by rw [hlvl_len]; omega)).toNat =
      (s.core.lvl[(tmp_r[rb + 1]'hr1_lt).toNat / 2]'(by rw [hlvl_len]; omega)).toNat := by
    rw [List.getElem?_eq_getElem (l := tmp_r) (i := rb) hr0_lt, Option.getD_some,
      List.getElem?_eq_getElem (l := s.core.lvl) (i := (tmp_r[rb]'hr0_lt).toNat / 2)
        (by rw [hlvl_len]; omega), Option.getD_some] at h1
    rw [List.getElem?_eq_getElem (l := tmp_r) (i := rb + 1) hr1_lt, Option.getD_some,
      List.getElem?_eq_getElem (l := s.core.lvl) (i := (tmp_r[rb + 1]'hr1_lt).toNat / 2)
        (by rw [hlvl_len]; omega), Option.getD_some] at h2
    exact h1.trans h2.symm
  have hac := m7_fullTmpLe_of_eq_lvl_tpos (by rw [hlvl_len]; omega) (by rw [hlvl_len]; omega)
    (by rw [htpos_len]; omega) (by rw [htpos_len]; omega) hl_eq_ac hle_tp
  have hr0_get : tmp_r[rb]? = some (tmp_r[rb]'hr0_lt) :=
    List.getElem?_eq_getElem (l := tmp_r) (i := rb) hr0_lt
  have hr1_get : tmp_r[rb + 1]? = some (tmp_r[rb + 1]'hr1_lt) :=
    List.getElem?_eq_getElem (l := tmp_r) (i := rb + 1) hr1_lt
  have hcs : (i = rb ∧ j = rb) ∨ (i = rb ∧ j = rb + 1) ∨ (i = rb + 1 ∧ j = rb + 1) := by omega
  rcases hcs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact m7_fullTmpLe_refl _ _ _
  · rw [hr0_get, hr1_get, Option.getD_some, Option.getD_some]; exact hac
  · exact m7_fullTmpLe_refl _ _ _

theorem m7_rins_finish_fullTmpLe {c : FullCfg} {s : FullState}
    {tmp_r tmp_ri : List (BitVec 32)} {N rb re rl : Nat}
    (htmp_len : s.core.tmp.length = c.max_vars)
    (hlen_r : tmp_r.length = c.max_vars) (hlen_ri : tmp_ri.length = c.max_vars)
    (hlvl_len : s.core.lvl.length = c.max_vars) (htpos_len : s.core.trail_pos.length = c.max_vars)
    (htl : N ≤ c.max_vars) (hrb1 : 1 ≤ rb) (hre_hi : re ≤ N) (hr_lt : rb ≤ re)
    (hperm_r : (m7Slice tmp_r 1 N).Perm (m7Slice s.core.tmp 1 N))
    (hperm_ri : (m7Slice tmp_ri rb re).Perm (m7Slice tmp_r rb re))
    (hout_ri : ∀ q, (q < rb ∨ re ≤ q) → tmp_ri[q]? = tmp_r[q]?)
    (hbd0 : ∀ p, 1 ≤ p → p < N → (s.core.tmp[p]?.getD 0#32).toNat < 2 * c.max_vars)
    (hre_eq : ∀ p, rb ≤ p → p < re →
      (s.core.lvl[(tmp_r[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = rl)
    (hsort_ri : ∀ i j, rb ≤ i → i ≤ j → j < re →
      (s.core.trail_pos[(tmp_ri[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
      (s.core.trail_pos[(tmp_ri[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) :
    ∀ i j, rb ≤ i → i ≤ j → j < re →
      Full.fullTmpLe s.core.lvl s.core.trail_pos (tmp_ri[i]?.getD 0#32) (tmp_ri[j]?.getD 0#32) := by
  intro i j hi hij hj
  have hperm_ri_N : (m7Slice tmp_ri 1 N).Perm (m7Slice s.core.tmp 1 N) :=
    (m7_slice_perm_sub (xs := tmp_ri) (ys := tmp_r) hrb1 hr_lt hre_hi
      (by rw [hlen_ri]; exact htl) (by rw [hlen_r]; exact htl) hperm_ri hout_ri).trans hperm_r
  have hibd := m7Slice_perm_bd hperm_ri_N (by rw [hlen_ri]; exact htl)
    (by rw [htmp_len]; exact htl) hbd0 i (by omega) (by omega)
  have hjbd := m7Slice_perm_bd hperm_ri_N (by rw [hlen_ri]; exact htl)
    (by rw [htmp_len]; exact htl) hbd0 j (by omega) (by omega)
  have get_l (p : Nat) (hp1 : rb ≤ p) (hp2 : p < re) :
      (s.core.lvl[(tmp_ri[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = rl := by
    have hpri : p < tmp_ri.length := by rw [hlen_ri]; omega
    have hmem : tmp_ri[p]'hpri ∈ m7Slice tmp_ri rb re := by
      rw [List.mem_iff_getElem]
      exact ⟨p - rb, by rw [m7Slice_length, hlen_ri]; omega,
        by rw [m7Slice_getElem]; congr 1; omega⟩
    rw [hperm_ri.mem_iff, List.mem_iff_getElem] at hmem
    obtain ⟨km, hkm, hkeq⟩ := hmem
    rw [m7Slice_getElem] at hkeq
    rw [m7Slice_length, hlen_r] at hkm
    rw [List.getElem?_eq_getElem (l := tmp_ri) (i := p) hpri, Option.getD_some, ← hkeq]
    simpa [List.getElem?_eq_getElem (l := tmp_r) (i := rb + km) (by rw [hlen_r]; omega)] using
      hre_eq (rb + km) (by omega) (by omega)
  have hil : (tmp_ri[i]?.getD 0#32).toNat / 2 < s.core.lvl.length := by rw [hlvl_len]; omega
  have hjl : (tmp_ri[j]?.getD 0#32).toNat / 2 < s.core.lvl.length := by rw [hlvl_len]; omega
  have hl_eq :
      (s.core.lvl[(tmp_ri[i]?.getD 0#32).toNat / 2]'hil).toNat =
      (s.core.lvl[(tmp_ri[j]?.getD 0#32).toNat / 2]'hjl).toNat := by
    have hi1 := get_l i hi (by omega)
    have hj1 := get_l j (by omega) hj
    rw [List.getElem?_eq_getElem (l := s.core.lvl) (i := (tmp_ri[i]?.getD 0#32).toNat / 2) hil,
      Option.getD_some] at hi1
    rw [List.getElem?_eq_getElem (l := s.core.lvl) (i := (tmp_ri[j]?.getD 0#32).toNat / 2) hjl,
      Option.getD_some] at hj1
    exact hi1.trans hj1.symm
  have ht_le := hsort_ri i j hi hij hj
  rw [List.getElem?_eq_getElem (l := s.core.trail_pos)
      (i := (tmp_ri[i]?.getD 0#32).toNat / 2) (by rw [htpos_len]; omega),
    List.getElem?_eq_getElem (l := s.core.trail_pos)
      (i := (tmp_ri[j]?.getD 0#32).toNat / 2) (by rw [htpos_len]; omega),
    Option.getD_some, Option.getD_some] at ht_le
  exact m7_fullTmpLe_of_eq_lvl_tpos (by rw [hlvl_len]; omega) (by rw [hlvl_len]; omega)
    (by rw [htpos_len]; omega) (by rw [htpos_len]; omega) hl_eq ht_le

theorem m7_run_heap_finish {c : FullCfg} {s : FullState}
    {tmp_r sub' : List (BitVec 32)} {N rb re : Nat}
    (hlen_r : tmp_r.length = c.max_vars) (htl : N ≤ c.max_vars)
    (hrb1 : 1 ≤ rb) (hr_lt : rb ≤ re) (hre_hi : re ≤ N)
    (htl_s : sub'.length = (tmp_r.drop (rb - 1)).length)
    (hperm_s : (sub'.take (re - rb + 1)).Perm ((tmp_r.drop (rb - 1)).take (re - rb + 1)))
    (h0_s : 0 < re - rb + 1 → sub'[0]? = (tmp_r.drop (rb - 1))[0]?)
    (hout_s : ∀ q, re - rb + 1 ≤ q → sub'[q]? = (tmp_r.drop (rb - 1))[q]?)
    (hsort_s : ∀ i j, 1 ≤ i → i ≤ j → j < re - rb + 1 →
      Full.fullTmpLe s.core.lvl s.core.trail_pos (sub'[i]?.getD 0#32) (sub'[j]?.getD 0#32)) :
    let off := rb - 1
    let tmp_n := tmp_r.take off ++ sub'
    tmp_n.length = c.max_vars ∧
    (m7Slice tmp_n rb re).Perm (m7Slice tmp_r rb re) ∧
    tmp_n[0]? = tmp_r[0]? ∧
    (∀ q, (q < rb ∨ re ≤ q) → tmp_n[q]? = tmp_r[q]?) ∧
    (∀ i j, rb ≤ i → i ≤ j → j < re →
      Full.fullTmpLe s.core.lvl s.core.trail_pos (tmp_n[i]?.getD 0#32) (tmp_n[j]?.getD 0#32)) := by
  intro off tmp_n
  have hoff_le : off ≤ tmp_r.length := by rw [hlen_r]; omega
  have hlen_n : tmp_n.length = c.max_vars := by
    simp [tmp_n, htl_s, List.length_take, List.length_drop, hlen_r]; omega
  have hlen_take : (tmp_r.take off).length = off := List.length_take_of_le hoff_le
  have hout_n : ∀ q, (q < rb ∨ re ≤ q) → tmp_n[q]? = tmp_r[q]? := fun q hq => by
    dsimp [tmp_n]
    rcases hq with hq_lo | hq_hi
    · by_cases hq_off : q < off
      · rw [List.getElem?_append_left (by omega), List.getElem?_take_of_lt hq_off]
      · have hqe : q = off := by omega
        subst hqe
        rw [List.getElem?_append_right (by omega), hlen_take, Nat.sub_self]
        have := h0_s (by omega)
        rwa [List.getElem?_drop, Nat.add_zero] at this
    · rw [List.getElem?_append_right (by omega), hlen_take]
      have := hout_s (q - off) (by omega)
      rwa [List.getElem?_drop, show off + (q - off) = q by omega] at this
  have hperm_sub : (m7Slice tmp_n rb re).Perm (m7Slice tmp_r rb re) := by
    have hs1 : m7Slice tmp_n rb re = m7Slice sub' 1 (re - rb + 1) := by
      apply List.ext_getElem
      · simp only [m7Slice_length, hlen_n, htl_s, List.length_drop, hlen_r]; omega
      · intro p hp1 hp2
        rw [m7Slice_getElem, m7Slice_getElem]
        exact Option.some.inj ((List.getElem?_eq_getElem (l := tmp_n) (i := rb + p)
          (by rw [hlen_n]; rw [m7Slice_length, hlen_n] at hp1; omega)).symm.trans (by
            dsimp [tmp_n]; rw [List.getElem?_append_right (by omega), hlen_take]
            have hpl : 1 + p < sub'.length := by rw [m7Slice_length] at hp2; omega
            rw [show rb + p - off = 1 + p by omega]
            exact List.getElem?_eq_getElem (l := sub') (i := 1 + p) hpl))
    have hs2 : m7Slice tmp_r rb re = m7Slice (tmp_r.drop off) 1 (re - rb + 1) := by
      apply List.ext_getElem
      · simp only [m7Slice_length, List.length_drop, hlen_r]; omega
      · intro p hp1 hp2
        rw [m7Slice_getElem, m7Slice_getElem, List.getElem_drop]; congr 1; omega
    rw [hs1, hs2]
    exact m7Slice_perm_of_take (h0_s (by omega)) hperm_s (by omega)
      (by rw [htl_s, List.length_drop, hlen_r]; omega)
      (by rw [List.length_drop, hlen_r]; omega)
  refine ⟨hlen_n, hperm_sub, hout_n 0 (Or.inl (by omega)), hout_n, fun i j hi hij hj => ?_⟩
  have get_sub (p : Nat) (hp1 : rb ≤ p) (hp2 : p < re) :
      tmp_n[p]?.getD 0#32 = sub'[p - off]?.getD 0#32 := by
    dsimp [tmp_n]; rw [List.getElem?_append_right (by omega), hlen_take]
  rw [get_sub i hi (by omega), get_sub j (by omega) hj]
  exact hsort_s (i - off) (j - off) (by omega) (by omega) (by omega)

theorem m7_run_next_inv {c : FullCfg} {s : FullState}
    {tmp_r tmp_n : List (BitVec 32)} {N rb re rl : Nat}
    (htmp_len : s.core.tmp.length = c.max_vars)
    (hlen_r : tmp_r.length = c.max_vars) (hlen_n : tmp_n.length = c.max_vars)
    (hlvl_len : s.core.lvl.length = c.max_vars) (htl : N ≤ c.max_vars)
    (hrb1 : 1 ≤ rb) (hrb_lt : rb < N) (hre_lo : rb + 1 ≤ re) (hre_hi : re ≤ N)
    (hperm_r : (m7Slice tmp_r 1 N).Perm (m7Slice s.core.tmp 1 N))
    (hlvl_r : ∀ i j, 1 ≤ i → i ≤ j → j < N →
      (s.core.lvl[(tmp_r[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
      (s.core.lvl[(tmp_r[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)
    (hbdry_r : 1 < rb → rb < N →
      (s.core.lvl[(tmp_r[rb - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat <
      (s.core.lvl[(tmp_r[rb]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)
    (hsort_r : ∀ i j, 1 ≤ i → i ≤ j → j < rb →
      Full.fullTmpLe s.core.lvl s.core.trail_pos (tmp_r[i]?.getD 0#32) (tmp_r[j]?.getD 0#32))
    (hre_eq : ∀ p, rb ≤ p → p < re →
      (s.core.lvl[(tmp_r[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = rl)
    (hre_exit : re = N ∨ rl < (s.core.lvl[(tmp_r[re]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)
    (hperm_sub : (m7Slice tmp_n rb re).Perm (m7Slice tmp_r rb re))
    (hout_n : ∀ q, (q < rb ∨ re ≤ q) → tmp_n[q]? = tmp_r[q]?)
    (hsort_sub : ∀ i j, rb ≤ i → i ≤ j → j < re →
      Full.fullTmpLe s.core.lvl s.core.trail_pos (tmp_n[i]?.getD 0#32) (tmp_n[j]?.getD 0#32))
    (hbd0 : ∀ p, 1 ≤ p → p < N → (s.core.tmp[p]?.getD 0#32).toNat < 2 * c.max_vars) :
    (m7Slice tmp_n 1 N).Perm (m7Slice s.core.tmp 1 N) ∧
    (∀ i j, 1 ≤ i → i ≤ j → j < N →
      (s.core.lvl[(tmp_n[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
      (s.core.lvl[(tmp_n[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) ∧
    (1 < re → re < N →
      (s.core.lvl[(tmp_n[re - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat <
      (s.core.lvl[(tmp_n[re]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) ∧
    (∀ i j, 1 ≤ i → i ≤ j → j < re →
      Full.fullTmpLe s.core.lvl s.core.trail_pos (tmp_n[i]?.getD 0#32) (tmp_n[j]?.getD 0#32)) := by
  have hperm_n : (m7Slice tmp_n 1 N).Perm (m7Slice s.core.tmp 1 N) :=
    (m7_slice_perm_sub (xs := tmp_n) (ys := tmp_r) hrb1 (by omega) hre_hi
      (by rw [hlen_n]; exact htl) (by rw [hlen_r]; exact htl) hperm_sub hout_n).trans hperm_r
  have heq_sub_lvl : ∀ p, rb ≤ p → p < re →
      (s.core.lvl[(tmp_n[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = rl := by
    intro p hp1 hp2
    have hpn : p < tmp_n.length := by rw [hlen_n]; omega
    have hmem : tmp_n[p]'hpn ∈ m7Slice tmp_n rb re := by
      rw [List.mem_iff_getElem]
      exact ⟨p - rb, by rw [m7Slice_length, hlen_n]; omega,
        by rw [m7Slice_getElem]; congr 1; omega⟩
    rw [hperm_sub.mem_iff, List.mem_iff_getElem] at hmem
    obtain ⟨k_m, hk_m, hk_eq⟩ := hmem
    rw [m7Slice_getElem] at hk_eq
    rw [m7Slice_length, hlen_r] at hk_m
    rw [List.getElem?_eq_getElem (l := tmp_n) (i := p) hpn, Option.getD_some, ← hk_eq]
    simpa [List.getElem?_eq_getElem (l := tmp_r) (i := rb + k_m) (by rw [hlen_r]; omega)] using
      hre_eq (rb + k_m) (by omega) (by omega)
  have hlvl_n : ∀ i j, 1 ≤ i → i ≤ j → j < N →
      (s.core.lvl[(tmp_n[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
      (s.core.lvl[(tmp_n[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat := by
    intro i j hi hij hj
    have get_lvl (q : Nat) (hq : q < N) :
        ((q < rb ∨ re ≤ q) ∧ tmp_n[q]? = tmp_r[q]?) ∨
        (rb ≤ q ∧ q < re ∧
          (s.core.lvl[(tmp_n[q]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
          (s.core.lvl[(tmp_r[q]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) := by
      by_cases hq_in : rb ≤ q ∧ q < re
      · exact Or.inr ⟨hq_in.1, hq_in.2, (heq_sub_lvl q hq_in.1 hq_in.2).trans
          (hre_eq q hq_in.1 hq_in.2).symm⟩
      · have ho : q < rb ∨ re ≤ q := by omega
        exact Or.inl ⟨ho, hout_n q ho⟩
    rcases get_lvl i (by omega) with ⟨_, hiq⟩ | ⟨_, _, hil⟩ <;>
    rcases get_lvl j hj with ⟨_, hjq⟩ | ⟨_, _, hjl⟩
    · rw [hiq, hjq]; exact hlvl_r i j hi hij hj
    · rw [hiq, hjl]; exact hlvl_r i j hi hij hj
    · rw [hil, hjq]; exact hlvl_r i j hi hij hj
    · rw [hil, hjl]; exact hlvl_r i j hi hij hj
  have hbdry_n : 1 < re → re < N →
      (s.core.lvl[(tmp_n[re - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat <
      (s.core.lvl[(tmp_n[re]?.getD 0#32).toNat / 2]?.getD 0#32).toNat := by
    intro _ hlt_N
    rw [heq_sub_lvl (re - 1) (by omega) (by omega), hout_n re (Or.inr (le_refl _))]
    rcases hre_exit with hbad | hlt
    · omega
    · exact hlt
  have hsort_n : ∀ i j, 1 ≤ i → i ≤ j → j < re →
      Full.fullTmpLe s.core.lvl s.core.trail_pos (tmp_n[i]?.getD 0#32) (tmp_n[j]?.getD 0#32) := by
    intro i j hi hij hj
    by_cases hj_lo : j < rb
    · rw [hout_n i (Or.inl (by omega)), hout_n j (Or.inl hj_lo)]
      exact hsort_r i j hi hij hj_lo
    · by_cases hi_lo : i < rb
      · have hb1 : 1 < rb := by omega
        have hl_i : (s.core.lvl[(tmp_n[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
            (s.core.lvl[(tmp_n[rb - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat := by
          rw [hout_n i (Or.inl hi_lo), hout_n (rb - 1) (Or.inl (by omega))]
          exact hlvl_r i (rb - 1) hi (by omega) (by omega)
        have hb_lt_rb :
            (s.core.lvl[(tmp_n[rb - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat < rl := by
          rw [hout_n (rb - 1) (Or.inl (by omega))]
          have := hbdry_r hb1 hrb_lt
          rwa [hre_eq rb (le_refl _) (by omega)] at this
        have hrl_j := heq_sub_lvl j (by omega) hj
        have hi_bd := m7Slice_perm_bd hperm_n (by rw [hlen_n]; exact htl)
          (by rw [htmp_len]; exact htl) hbd0 i hi (by omega)
        have hj_bd := m7Slice_perm_bd hperm_n (by rw [hlen_n]; exact htl)
          (by rw [htmp_len]; exact htl) hbd0 j (by omega) (by omega)
        have hil' : (tmp_n[i]?.getD 0#32).toNat / 2 < s.core.lvl.length := by rw [hlvl_len]; omega
        have hjl' : (tmp_n[j]?.getD 0#32).toNat / 2 < s.core.lvl.length := by rw [hlvl_len]; omega
        rw [List.getElem?_eq_getElem (l := s.core.lvl) (i := (tmp_n[i]?.getD 0#32).toNat / 2)
          hil', Option.getD_some] at hl_i
        rw [List.getElem?_eq_getElem (l := s.core.lvl) (i := (tmp_n[j]?.getD 0#32).toNat / 2)
          hjl', Option.getD_some] at hrl_j
        exact m7_fullTmpLe_of_lt hil' hjl' (by omega)
      · exact hsort_sub i j (by omega) hij hj
  exact ⟨hperm_n, hlvl_n, hbdry_n, hsort_n⟩

end LeanQbe.T.Examples.Kissat.FullM7AnalyzeSort
