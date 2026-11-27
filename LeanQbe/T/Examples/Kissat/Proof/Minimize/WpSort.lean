/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Minimize.WpSortMerge
import LeanQbe.T.Examples.Kissat.Proof.Minimize.MinTactics
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.Logic.Rules

/-!
# Canonical WP Soundness Proof for `full_sort_tmp`

Proves `full_sort_tmp_wp` for `Src.Minimize.full_sort_tmp_body` against `Spec.fullSortTmpSpec`:
- early return for `tlen ≤ 2` / `tlen > max_vars`;
- `tlen ≤ 32`: in-place level-only insertion sort (`wsort` untouched);
- `tlen > 32`: copy to `wsort` + `[min_l, max_l]` scan; `span == 1` return; `lvl`-only counting
  sort in `wsort[max_vars + b]` buckets; bottom-up merge-sort fallback (`s7_sort_merge_wp`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Minimize

open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Minimize.FullMinTactics
open Kraken.Bedrock2.Test
open LeanQbe.T.Examples.Kissat.Src.Minimize

local syntax "m7_lets_core" : tactic
local macro_rules
  | `(tactic| m7_lets_core) => `(tactic| repeat (first
      | rw [FullMinTactics.ml_copy_bool] | rw [FullMinTactics.ml_copy8]
      | rw [FullMinTactics.ml_copy32] | rw [FullMinTactics.ml_copy64]
      | rw [FullMinTactics.ml_add32] | rw [FullMinTactics.ml_add64]
      | rw [FullMinTactics.ml_sub64] | rw [FullMinTactics.ml_mul64]
      | rw [FullMinTactics.ml_shl64] | rw [FullMinTactics.ml_lshr64]
      | rw [FullMinTactics.ml_zext32_64] | rw [FullMinTactics.ml_sext32_64]
      | rw [FullMinTactics.ml_trunc64_32]
      | rw [FullMinTactics.ml_ult32] | rw [FullMinTactics.ml_ule32]
      | rw [FullMinTactics.ml_ugt32] | rw [FullMinTactics.ml_eq32]
      | rw [FullMinTactics.ml_ne32]
      | rw [FullMinTactics.ml_ult64] | rw [FullMinTactics.ml_ule64]
      | rw [FullMinTactics.ml_ugt64] | rw [FullMinTactics.ml_uge64]
      | rw [FullMinTactics.ml_eq64] | rw [FullMinTactics.ml_ne64]
      | rw [Arg.val_var] | rw [Arg.val_imm]))

local macro "m7_dsimp" : tactic =>
  `(tactic| dsimp (zeta := false) only [LeanQbe.T.vals, Arg.val, Prod.fst, Prod.snd])

local macro "m7_lets" : tactic =>
  `(tactic| (m7_lets_core; (try rw [LeanQbe.T.wp_jump]); try m7_dsimp))

local syntax "m7_jnz" : tactic
local macro_rules
  | `(tactic| m7_jnz) => `(tactic| (m7_lets; rw [LeanQbe.T.wp_jnz]; dsimp only [Arg.val]))

local syntax "m7_ld " term : tactic
local macro_rules
  | `(tactic| m7_ld $lem:term) => `(tactic| (m7_lets; rw [LeanQbe.T.wp]; refine ⟨_, $lem, ?_⟩))

local macro "m7_st " m:ident ", " h:ident " := " lem:term : tactic =>
  `(tactic| (m7_lets; refine LeanQbe.T.wp_store_sep $lem fun $m:ident $h:ident => ?_))

/-! ## 1. Finishing Helper -/

/-- Finishing lemma deriving every `Spec.fullSortTmpSpec` postcondition from a slice
permutation, `tmp[0]` preservation and level-sortedness. -/
private theorem s7_finish_spec {c : FullCfg} {s st' : FullState}
    {tmp' ws' : List (BitVec 32)} {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post []}
    (hlenOk : FullState.LengthsOk c s) (htl : s.core.tmp_len ≤ c.max_vars)
    (hc' : st'.core = { s.core with tmp := tmp' })
    (hs' : st'.scratch = { s.scratch with wsort := ws' })
    (hlen_t : tmp'.length = c.max_vars)
    (hlen_w : ws'.length = 2 * c.max_vars)
    (hle32_w : s.core.tmp_len ≤ 32 → ws' = s.scratch.wsort)
    (hperm : (m7Slice tmp' 1 s.core.tmp_len).Perm (m7Slice s.core.tmp 1 s.core.tmp_len))
    (h0 : 0 < s.core.tmp_len → tmp'[0]? = s.core.tmp[0]?)
    (hsort : ∀ i j, 1 ≤ i → i ≤ j → j < s.core.tmp_len →
      (s.core.lvl[(tmp'[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
      (s.core.lvl[(tmp'[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)
    (hm' : (FullMem c st' ⋆ R) m')
    (hQ : ∀ tmp' wsort' m',
      let s' : FullState := FullState.mk { s.core with tmp := tmp' }
        { s.scratch with wsort := wsort' };
      FullState.LengthsOk c s' → tmp'.length = c.max_vars →
      (s.core.tmp_len ≤ 32 → wsort' = s.scratch.wsort) →
      (tmp'.take s.core.tmp_len).Perm (s.core.tmp.take s.core.tmp_len) →
      (0 < s.core.tmp_len → tmp'[0]? = s.core.tmp[0]?) →
      (∀ j, 1 ≤ j → j < s.core.tmp_len →
        ∃ i, 1 ≤ i ∧ i < s.core.tmp_len ∧ tmp'[j]? = s.core.tmp[i]?) →
      (∀ i, 1 ≤ i → i < s.core.tmp_len →
        ∃ j, 1 ≤ j ∧ j < s.core.tmp_len ∧ s.core.tmp[i]? = tmp'[j]?) →
      (∀ i j, 1 ≤ i → i ≤ j → j < s.core.tmp_len →
        (s.core.lvl[(tmp'[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
        (s.core.lvl[(tmp'[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
      FullExtScratchPres s s' → (FullMem c s' ⋆ R) m' → Q () m') :
    Q () m' := by
  have hst_ok := m7SortTmp_stateOk c s tmp' ws' hlenOk hlen_t hlen_w
  have htake : (tmp'.take s.core.tmp_len).Perm (s.core.tmp.take s.core.tmp_len) := by
    by_cases hn0 : 0 < s.core.tmp_len
    · exact m7Slice_perm_to_take (h0 hn0) hperm hn0 (by rw [hlen_t]; exact htl)
        (by rw [hlenOk.core_ok.tmp_len_arr]; exact htl)
    · have : s.core.tmp_len = 0 := by omega
      simp [this]
  have hbij := m7Slice_perm_bij hperm (by rw [hlen_t]; exact htl)
    (by rw [hlenOk.core_ok.tmp_len_arr]; exact htl)
  have hst_eq : st' = FullState.mk { s.core with tmp := tmp' }
      { s.scratch with wsort := ws' } :=
    s7_state_eq hc' hs'
  exact hQ tmp' ws' m' hst_ok.1 hlen_t hle32_w htake h0 hbij.1 hbij.2 hsort
    hst_ok.2 (hst_eq ▸ hm')

/-! ## 2. `tlen ≤ 32` Level-Only Insertion Sort -/

private theorem s7_sort_ins_wp {Γ : Env} {c : FullCfg} {s st0 : FullState}
    {sc0 : FullScratch} {R : Mem 64 → Prop} {m0 : Mem 64} {Q : Post []} {X : XPost}
    (htmp_len : s.core.tmp.length = c.max_vars)
    (hlvl_len : s.core.lvl.length = c.max_vars)
    (htl : s.core.tmp_len ≤ c.max_vars)
    (h2lt : 2 ≤ s.core.tmp_len)
    (hbd0 : ∀ p, 1 ≤ p → p < s.core.tmp_len →
      (s.core.tmp[p]?.getD 0#32).toNat < 2 * c.max_vars)
    (hc0 : st0.core = { s.core with tmp := s.core.tmp })
    (hs0 : st0.scratch = sc0)
    (hm0 : (FullMem c st0 ⋆ R) m0)
    (hPost : ∀ st' tmp' m',
      st'.core = { s.core with tmp := tmp' } → st'.scratch = sc0 →
      tmp'.length = c.max_vars →
      (m7Slice tmp' 1 s.core.tmp_len).Perm (m7Slice s.core.tmp 1 s.core.tmp_len) →
      tmp'[0]? = s.core.tmp[0]? →
      (∀ i j, 1 ≤ i → i ≤ j → j < s.core.tmp_len →
        (s.core.lvl[(tmp'[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
        (s.core.lvl[(tmp'[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
      (FullMem c st' ⋆ R) m' → Q () m') :
    wp Γ Q X (s7SortInsExpr (BitVec.ofNat 64 s.core.tmp_len) c.pTmp c.pLevel) m0 := by
  let N := s.core.tmp_len
  let K : BitVec 32 → Nat := fun a => (s.core.lvl[a.toNat / 2]?.getD 0#32).toNat
  have hN64 : N < 2 ^ 64 := by have := c.hmaxv; unfold Ref.dimacsBound at this; omega
  let InvOut : Nat → Tup Val [i64] → Mem 64 → Prop := fun meas xs m =>
    ∃ i st tmp_i, xs.1 = BitVec.ofNat 64 i ∧ 2 ≤ i ∧ i ≤ N ∧ meas = N - i ∧
      st.core = { s.core with tmp := tmp_i } ∧ st.scratch = sc0 ∧
      tmp_i.length = c.max_vars ∧ (m7Slice tmp_i 1 N).Perm (m7Slice s.core.tmp 1 N) ∧
      tmp_i[0]? = s.core.tmp[0]? ∧
      (∀ a b, 1 ≤ a → a ≤ b → b < i → K (tmp_i[a]?.getD 0#32) ≤ K (tmp_i[b]?.getD 0#32)) ∧
      (FullMem c st ⋆ R) m
  refine wp_loop_group InvOut ?_ ?_
  · intro J1 meas xs m hm_ex ⟨i, st, tmp_i, hxs, hi2, hiN, hmeas, hst_c, hst_s, hlen_i,
      hperm_i, h0_i, hsort_i, hm⟩
    rw [Blocks.get_here]
    m7_lets
    m7_jnz
    refine ⟨fun hlt_b => ?_, fun hge_b => ?_⟩
    · have hi_lt : i < N := by
        have h := s7_ult64_true hlt_b
        rw [hxs, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h
        rwa [Nat.mod_eq_of_lt hN64, Nat.mod_eq_of_lt (by omega)] at h
      have hi_tmp : i < tmp_i.length := by rw [hlen_i]; omega
      have hbd_i := m7Slice_perm_bd hperm_i (by rw [hlen_i]; exact htl)
        (by rw [htmp_len]; exact htl) hbd0 i (by omega) hi_lt
      rw [List.getElem?_eq_getElem (l := tmp_i) (i := i) hi_tmp, Option.getD_some] at hbd_i
      m7_lets
      rw [hxs]
      have hld_v7 := s7_load_tmp_nat hst_c hi_tmp (by omega) hm
      m7_ld hld_v7
      m7_lets
      let v7 := tmp_i[i]'hi_tmp
      have hv7_bd : v7.toNat < 2 * c.max_vars := hbd_i
      rw [s7_var_idx64 v7]
      have hv7_lvl : v7.toNat / 2 < s.core.lvl.length := by rw [hlvl_len]; omega
      have hld_lvl := s7_load_lvl_nat hst_c hv7_lvl (by omega) hm
      m7_ld hld_lvl
      let v13 := s.core.lvl[v7.toNat / 2]'hv7_lvl
      have hK7 : K v7 = v13.toNat := by
        show (s.core.lvl[v7.toNat / 2]?.getD 0#32).toNat = v13.toNat
        rw [List.getElem?_eq_getElem hv7_lvl, Option.getD_some]
      let InvIn : Nat → Tup Val [i64] → Mem 64 → Prop := fun m_in ys m_cur =>
        ∃ j st_j tmp_j,
          ys.1 = BitVec.ofNat 64 j ∧ 1 ≤ j ∧ j ≤ i ∧ m_in = j ∧
          st_j.core = { s.core with tmp := tmp_j } ∧ st_j.scratch = sc0 ∧
          tmp_j.length = c.max_vars ∧
          (m7Slice (tmp_j.set j v7) 1 N).Perm (m7Slice s.core.tmp 1 N) ∧
          tmp_j[0]? = s.core.tmp[0]? ∧
          (∀ a b, 1 ≤ a → a ≤ b → b ≤ i → a ≠ j → b ≠ j →
            K (tmp_j[a]?.getD 0#32) ≤ K (tmp_j[b]?.getD 0#32)) ∧
          (∀ k, j < k → k ≤ i → K v7 ≤ K (tmp_j[k]?.getD 0#32)) ∧
          (FullMem c st_j ⋆ R) m_cur
      refine wp_loop_group InvIn ?_ ?_
      · intro J2 m_in ys m_cur hIH_in ⟨j, st_j, tmp_j, hys1, hj1, hji, hmin,
          hstj_c, hstj_s, hlen_j, hperm_j, h0_j, hinv_j, hgt_j, hm_j⟩
        rw [Blocks.get_here]
        let Pex : Tup Val [] → Mem 64 → Prop := fun _ m' =>
          m' = m_cur ∧ (1 < j → K (tmp_j[j - 1]?.getD 0#32) ≤ K v7)
        refine wp_join_group Pex ?_ ?_
        · intro J3 _ m' ⟨hm_eq, hstop⟩
          subst hm_eq
          rw [Blocks.get_here]
          m7_lets
          have hj_lt : j < tmp_j.length := by rw [hlen_j]; omega
          rw [hys1]
          obtain ⟨st_e, hst_ec, hst_es, hok_e, hm_e0⟩ := s7_store_tmp_nat (i := j) v7 hstj_c
            hstj_s hj_lt (by omega) hm_j
          m7_st m_e, hm_e := And.intro hok_e hm_e0
          m7_lets
          let tmp_e := tmp_j.set j v7
          have hi_j : i < tmp_j.length := by rw [hlen_j]; omega
          have hsort_e := m7_ins_place_sorted
            (ltp := fun a b => K a ≤ K b)
            (fun a => Nat.le_refl _)
            (fun a b c h1 h2 => Nat.le_trans h1 h2)
            (xs := tmp_j) (lo := 1) (i := i) (j := j) (x := v7)
            hj1 hji hi_j hinv_j hstop hgt_j
          have hi1_bv : BitVec.ofNat 64 i + (1 : BitVec 64) = BitVec.ofNat 64 (i + 1) :=
            s7_add1_bv64 (by omega)
          rw [hi1_bv]
          exact hm_ex (N - (i + 1)) (BitVec.ofNat 64 (i + 1), ()) _ (by omega)
            ⟨i + 1, st_e, tmp_e, rfl, by omega, by omega, rfl, hst_ec, hst_es,
              by simp [tmp_e, hlen_j], hperm_j,
              by dsimp [tmp_e]; rw [← h0_j]; exact List.getElem?_set_ne (by omega),
              fun a b ha hab hb => hsort_e a b ha hab (by omega), hm_e⟩
        · intro J3 hExit3
          m7_lets
          m7_jnz
          refine ⟨fun hgt1_b => ?_, fun hle1_b => ?_⟩
          · have hj_gt1 : 1 < j := by
              have h := s7_ult64_true hgt1_b
              rw [hys1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
                show (1 : BitVec 64).toNat = 1 from rfl] at h
              exact h
            have hj_sub_eq : ys.1 - (1 : BitVec 64) = BitVec.ofNat 64 (j - 1) := by
              rw [hys1]; exact s7_sub1_bv64 (by omega) (by omega)
            m7_lets
            rw [hj_sub_eq]
            have hj1_lt : j - 1 < tmp_j.length := by rw [hlen_j]; omega
            have hld_v26 := s7_load_tmp_nat hstj_c hj1_lt (by omega) hm_j
            m7_ld hld_v26
            m7_lets
            let v26 := tmp_j[j - 1]'hj1_lt
            have hv26_bd : v26.toNat < 2 * c.max_vars := by
              have hslice_bd := m7Slice_perm_bd hperm_j
                (by simp [hlen_j]; exact htl) (by rw [htmp_len]; exact htl)
                hbd0 (j - 1) (by omega) (by omega)
              rw [List.getElem?_set_ne (by omega),
                List.getElem?_eq_getElem (l := tmp_j) (i := j - 1) hj1_lt,
                Option.getD_some] at hslice_bd
              exact hslice_bd
            rw [s7_var_idx64 v26]
            have hv26_lvl : v26.toNat / 2 < s.core.lvl.length := by rw [hlvl_len]; omega
            have hld_v32 := s7_load_lvl_nat hstj_c hv26_lvl (by omega) hm_j
            m7_ld hld_v32
            let v32 := s.core.lvl[v26.toNat / 2]'hv26_lvl
            have hv26_get : tmp_j[j - 1]?.getD 0#32 = v26 := by
              rw [List.getElem?_eq_getElem (l := tmp_j) (i := j - 1) hj1_lt, Option.getD_some]
            have hK26 : K (tmp_j[j - 1]?.getD 0#32) = v32.toNat := by
              rw [hv26_get]
              show (s.core.lvl[v26.toNat / 2]?.getD 0#32).toNat = v32.toNat
              rw [List.getElem?_eq_getElem hv26_lvl, Option.getD_some]
            m7_lets
            m7_jnz
            refine ⟨fun hgtl_b => ?_, fun hlel_b => ?_⟩
            · have hlt_lv : v13.toNat < v32.toNat := s7_ult32_true hgtl_b
              m7_lets
              have hj_lt : j < tmp_j.length := by rw [hlen_j]; omega
              have hj1_bv : BitVec.ofNat 64 j - (1 : BitVec 64) = BitVec.ofNat 64 (j - 1) :=
                s7_sub1_bv64 (by omega) (by omega)
              rw [hys1, hj1_bv]
              m7_ld hld_v26
              obtain ⟨st_s, hst_sc, hst_ss, hok_s, hm_s0⟩ :=
                s7_store_tmp_nat (i := j) v26 hstj_c hstj_s hj_lt (by omega) hm_j
              m7_st m_s, hm_s := And.intro hok_s hm_s0
              m7_lets
              let tmp_j' := tmp_j.set j v26
              rw [hj1_bv]
              have htmpj'_set : tmp_j' = tmp_j.set j (tmp_j[j - 1]?.getD 0#32) := by
                simp [tmp_j', hv26_get]
              have hi_j : i < tmp_j.length := by rw [hlen_j]; omega
              have hshift := m7_ins_shift_inv
                (ltp := fun a b => K a ≤ K b)
                (xs := tmp_j) (lo := 1) (i := i) (j := j) (x := v7)
                hj_gt1 hji hi_j hinv_j hgt_j (by rw [hK7, hK26]; omega)
              have hperm_j' :
                  (m7Slice (tmp_j'.set (j - 1) v7) 1 N).Perm (m7Slice s.core.tmp 1 N) :=
                (m7_shift_slice_perm (xs := tmp_j) (lo := 1) (hi := N)
                  (j := j) (j' := j - 1) v7 (by omega) (by omega) (by omega)
                  (by rw [hlen_j]; exact htl)).trans hperm_j
              exact hIH_in (j - 1) (BitVec.ofNat 64 (j - 1), ()) _ (by omega)
                ⟨j - 1, st_s, tmp_j', rfl, by omega, by omega, rfl, hst_sc, hst_ss,
                  by simp [tmp_j', hlen_j], hperm_j',
                  by dsimp [tmp_j']; rw [← h0_j]; exact List.getElem?_set_ne (by omega),
                  by simpa [htmpj'_set] using hshift.1,
                  by simpa [htmpj'_set] using hshift.2, hm_s⟩
            · have hge_lv : v32.toNat ≤ v13.toNat := s7_ult32_false hlel_b
              exact hExit3 () m_cur ⟨rfl, fun _ => by rw [hK26, hK7]; exact hge_lv⟩
          · have hj_le1 : j ≤ 1 := by
              have h := s7_ult64_false hle1_b
              rw [hys1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
                show (1 : BitVec 64).toNat = 1 from rfl] at h
              exact h
            exact hExit3 () m_cur ⟨rfl, fun h => absurd h (by omega)⟩
      · intro J4 hExit4
        apply hExit4 i (BitVec.ofNat 64 i, ()) m
        refine ⟨i, st, tmp_i, rfl, by omega, Nat.le_refl i, rfl, hst_c, hst_s,
          hlen_i, ?_, h0_i, ?_, fun k hk1 hk2 => by omega, hm⟩
        · have hset : tmp_i.set i v7 = tmp_i := by
            apply List.ext_getElem
            · simp
            · intro p hp1 hp2
              by_cases hpi : p = i
              · subst hpi; simp [v7]
              · simp [List.getElem_set_ne (Ne.symm hpi)]
          simpa [hset] using hperm_i
        · intro a b ha hab hbi _ _
          exact hsort_i a b ha hab (by omega)
    · have hi_ge : N ≤ i := by
        have h := s7_ult64_false hge_b
        rw [hxs, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h
        rwa [Nat.mod_eq_of_lt hN64, Nat.mod_eq_of_lt (by omega)] at h
      have hi_eq : i = N := by omega
      subst hi_eq
      exact hPost st tmp_i m hst_c hst_s hlen_i hperm_i h0_i hsort_i hm
  · intro J5 hExit5
    apply hExit5 (N - 2) (BitVec.ofNat 64 2, ()) m0
    refine ⟨2, st0, s.core.tmp, rfl, Nat.le_refl 2, h2lt, rfl, hc0, hs0, htmp_len, List.Perm.refl _,
      rfl, ?_, hm0⟩
    intro a b ha hab hb
    have ha1 : a = 1 := by omega
    have hb1 : b = 1 := by omega
    subst ha1; subst hb1
    exact Nat.le_refl _

/-! ## 3. Counting-Sort Phase WP Proofs -/

private theorem s7_sort_zero_wp {Γ : Env} {c : FullCfg} {s st0 : FullState}
    {tmp0 ws0 : List (BitVec 32)} {R : Mem 64 → Prop} {m0 : Mem 64} {Q : Post []}
    {X : XPost} {span : Nat} {kNext : Expr Val Cont []}
    (hspan_le : span ≤ c.max_vars)
    (hc0 : st0.core = { s.core with tmp := tmp0 })
    (hs0 : st0.scratch = { s.scratch with wsort := ws0 })
    (hws_len : ws0.length = 2 * c.max_vars)
    (hm0 : (FullMem c st0 ⋆ R) m0)
    (hNext : ∀ st' ws' m',
      st'.core = { s.core with tmp := tmp0 } →
      st'.scratch = { s.scratch with wsort := ws' } →
      ws'.length = 2 * c.max_vars →
      (∀ q < c.max_vars, ws'[q]? = ws0[q]?) →
      (∀ b < span, (ws'[c.max_vars + b]?.getD 0#32).toNat = 0) →
      (FullMem c st' ⋆ R) m' → wp Γ Q X kNext m') :
    wp Γ Q X (s7SortZeroExpr (BitVec.ofNat 64 c.max_vars) (BitVec.ofNat 64 span) c.pWsort kNext)
      m0 := by
  have hmv60 : c.max_vars < 2 ^ 60 := by have := c.hmaxv; unfold Ref.dimacsBound at this; omega
  have hsp64 : span < 2 ^ 64 := by omega
  let Inv : Nat → Tup Val [i64] → Mem 64 → Prop := fun meas xs m =>
    ∃ k st ws_k, xs.1 = BitVec.ofNat 64 k ∧ k ≤ span ∧ meas = span - k ∧
      st.core = { s.core with tmp := tmp0 } ∧
      st.scratch = { s.scratch with wsort := ws_k } ∧
      ws_k.length = 2 * c.max_vars ∧
      (∀ q < c.max_vars, ws_k[q]? = ws0[q]?) ∧
      (∀ b < k, (ws_k[c.max_vars + b]?.getD 0#32).toNat = 0) ∧
      (FullMem c st ⋆ R) m
  refine wp_loop_group Inv ?_ ?_
  · intro J48 meas xs m hIH ⟨k, st, ws_k, hxs, hk_le, hmeas, hst_c, hst_s, hlen_ws, hpre, hz, hm⟩
    rw [Blocks.get_here]
    m7_lets
    m7_jnz
    refine ⟨fun hlt_b => ?_, fun hge_b => ?_⟩
    · have hk_lt : k < span := by
        have h := s7_ult64_true hlt_b
        rw [hxs, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h
        rwa [Nat.mod_eq_of_lt hsp64, Nat.mod_eq_of_lt (by omega)] at h
      m7_lets
      rw [hxs, s7_add_bv64_ofNat (by omega)]
      obtain ⟨st', hst_c', hst_s', hok, hm_raw⟩ := s7_store_wsort_nat (i := c.max_vars + k)
        0#32 hst_c hst_s (by rw [hlen_ws]; omega) (by omega) hm
      m7_st m_n, hm' := And.intro hok hm_raw
      m7_lets
      let ws' := ws_k.set (c.max_vars + k) 0#32
      have hk1_bv : BitVec.ofNat 64 k + (1 : BitVec 64) = BitVec.ofNat 64 (k + 1) :=
        s7_add1_bv64 (by omega)
      rw [hk1_bv]
      refine hIH (span - (k + 1)) (BitVec.ofNat 64 (k + 1), ()) _ (by omega)
        ⟨k + 1, st', ws', rfl, by omega, rfl, hst_c', hst_s',
          by simp [ws', hlen_ws], fun q hq => by
            dsimp [ws']; rw [List.getElem?_set_ne (by omega)]; exact hpre q hq,
          fun b hb => ?_, hm'⟩
      by_cases hbk : b = k
      · subst hbk; dsimp [ws']
        rw [List.getElem?_eq_getElem (by simp [hlen_ws]; omega),
          List.getElem_set_self, Option.getD_some]; rfl
      · dsimp [ws']; rw [List.getElem?_set_ne (by omega)]; exact hz b (by omega)
    · have hk_ge : span ≤ k := by
        have h := s7_ult64_false hge_b
        rw [hxs, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h
        rwa [Nat.mod_eq_of_lt hsp64, Nat.mod_eq_of_lt (by omega)] at h
      have hk_eq : k = span := by omega
      subst hk_eq
      exact hNext st ws_k m hst_c hst_s hlen_ws hpre hz hm
  · intro J49 hExit49
    exact hExit49 span (BitVec.ofNat 64 0, ()) m0
      ⟨0, st0, ws0, rfl, Nat.zero_le span, rfl, hc0, hs0, hws_len,
        fun _ _ => rfl, fun _ hb => by omega, hm0⟩

private theorem s7_sort_hist_wp {Γ : Env} {c : FullCfg} {s st0 : FullState}
    {ws0 : List (BitVec 32)} {R : Mem 64 → Prop} {m0 : Mem 64} {Q : Post []} {X : XPost}
    {minL_bv : BitVec 32} {span : Nat} {kNext : Expr Val Cont []}
    (hlvl_len : s.core.lvl.length = c.max_vars)
    (hle_mv : s.core.tmp_len ≤ c.max_vars) (h1N : 1 ≤ s.core.tmp_len)
    (hlen_ws0 : ws0.length = 2 * c.max_vars)
    (hspan_le : span ≤ c.max_vars)
    (hminmax : ∀ p, 1 ≤ p → p < s.core.tmp_len →
      minL_bv.toNat ≤ (s.core.lvl[(ws0[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ∧
      (s.core.lvl[(ws0[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat < minL_bv.toNat + span)
    (hbd_ws : ∀ p, 1 ≤ p → p < s.core.tmp_len → (ws0[p]?.getD 0#32).toNat < 2 * c.max_vars)
    (hzero : ∀ b < span, (ws0[c.max_vars + b]?.getD 0#32).toNat = 0)
    (hc0 : st0.core = { s.core with tmp := s.core.tmp })
    (hs0 : st0.scratch = { s.scratch with wsort := ws0 })
    (hm0 : (FullMem c st0 ⋆ R) m0)
    (hNext : ∀ st' ws' m',
      st'.core = { s.core with tmp := s.core.tmp } →
      st'.scratch = { s.scratch with wsort := ws' } →
      ws'.length = 2 * c.max_vars →
      (∀ q < c.max_vars, ws'[q]? = ws0[q]?) →
      (∀ b < span, (ws'[c.max_vars + b]?.getD 0#32).toNat =
        m7BktCnt s.core.lvl minL_bv.toNat (m7Slice ws0 1 s.core.tmp_len) b) →
      (FullMem c st' ⋆ R) m' → wp Γ Q X kNext m') :
    wp Γ Q X (s7SortHistExpr (BitVec.ofNat 64 c.max_vars) (BitVec.ofNat 64 s.core.tmp_len)
      c.pLevel c.pWsort minL_bv kNext) m0 := by
  let N := s.core.tmp_len
  let minL := minL_bv.toNat
  have hmv60 : c.max_vars < 2 ^ 60 := by have := c.hmaxv; unfold Ref.dimacsBound at this; omega
  have hN64 : N < 2 ^ 64 := by omega
  let Inv : Nat → Tup Val [i64] → Mem 64 → Prop := fun meas xs m =>
    ∃ k st ws_k, xs.1 = BitVec.ofNat 64 k ∧ 1 ≤ k ∧ k ≤ N ∧ meas = N - k ∧
      st.core = { s.core with tmp := s.core.tmp } ∧
      st.scratch = { s.scratch with wsort := ws_k } ∧
      ws_k.length = 2 * c.max_vars ∧
      (∀ q < c.max_vars, ws_k[q]? = ws0[q]?) ∧
      (∀ b < span, (ws_k[c.max_vars + b]?.getD 0#32).toNat =
        m7BktCnt s.core.lvl minL (m7Slice ws0 1 k) b) ∧
      (FullMem c st ⋆ R) m
  refine wp_loop_group Inv ?_ ?_
  · intro J55 meas xs m hIH ⟨k, st, ws_k, hxs, hk1, hk_le, hmeas, hst_c, hst_s,
      hlen_wk, hpre, hcnt, hm⟩
    rw [Blocks.get_here]
    m7_lets
    m7_jnz
    refine ⟨fun hlt_b => ?_, fun hge_b => ?_⟩
    · have hk_lt : k < N := by
        have h := s7_ult64_true hlt_b
        rw [hxs, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h
        rwa [Nat.mod_eq_of_lt hN64, Nat.mod_eq_of_lt (by omega)] at h
      have hk_ws : k < ws_k.length := by rw [hlen_wk]; omega
      have hk_ws0 : k < ws0.length := by rw [hlen_ws0]; omega
      have hpre_k : ws_k[k] = ws0[k] := by
        have hq := hpre k (by omega)
        rw [List.getElem?_eq_getElem hk_ws, List.getElem?_eq_getElem hk_ws0] at hq
        exact Option.some.inj hq
      have hbd_k := hbd_ws k hk1 hk_lt
      rw [List.getElem?_eq_getElem (l := ws0) (i := k) hk_ws0, Option.getD_some,
        ← hpre_k] at hbd_k
      m7_lets
      rw [hxs]
      have hld_v61 := s7_load_wsort_nat hst_s hk_ws (by omega) hm
      m7_ld hld_v61
      m7_lets
      let v61 := ws_k[k]'hk_ws
      have hv61_bd : v61.toNat < 2 * c.max_vars := hbd_k
      rw [s7_var_idx64 v61]
      have hv61_lvl : v61.toNat / 2 < s.core.lvl.length := by rw [hlvl_len]; omega
      have hld_v67 := s7_load_lvl_nat hst_c hv61_lvl (by omega) hm
      m7_ld hld_v67
      m7_lets
      let v67 := s.core.lvl[v61.toNat / 2]'hv61_lvl
      let wst_k := ws_k.drop c.max_vars
      have hwst_len : wst_k.length = c.max_vars := by simp [wst_k, hlen_wk]; omega
      have hsl_eq : m7Slice ws_k 1 N = m7Slice ws0 1 N :=
        s7Slice_congr_lt (by omega) (by rw [hlen_wk]; omega) (by rw [hlen_ws0]; omega)
          (fun q hq => hpre q (by omega))
      have hsl_k : m7Slice ws_k 1 k = m7Slice ws0 1 k :=
        s7Slice_congr_lt hk1 (by rw [hlen_wk]; omega) (by rw [hlen_ws0]; omega)
          (fun q hq => hpre q (by omega))
      have hminmax_k : ∀ p, 1 ≤ p → p < s.core.tmp_len →
          minL ≤ (s.core.lvl[(ws_k[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ∧
          (s.core.lvl[(ws_k[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat < minL + span := by
        intro p hp1 hp2
        rw [show ws_k[p]? = ws0[p]? from hpre p (by omega)]
        exact hminmax p hp1 hp2
      have hcnt_wst : ∀ b < span, (wst_k[b]?.getD 0#32).toNat =
          m7BktCnt s.core.lvl minL (m7Slice ws_k 1 k) b := by
        intro b hb; dsimp [wst_k]; rw [List.getElem?_drop, hsl_k]; exact hcnt b hb
      have hstep := m7_hist_step_cnt hlvl_len hlen_wk hwst_len hk1 hk_lt hle_mv
        hminmax_k hcnt_wst hspan_le
      have hx_min : minL ≤ v67.toNat := by
        have h := (hminmax_k k hk1 hk_lt).1
        rw [List.getElem?_eq_getElem (l := ws_k) (i := k) hk_ws, Option.getD_some,
          List.getElem?_eq_getElem (l := s.core.lvl) (i := v61.toNat / 2) hv61_lvl,
          Option.getD_some] at h
        exact h
      have hbi_eq : v67.toNat - minL = m7Bkt s.core.lvl minL v61 := by
        rw [m7Bkt_eq, List.getElem?_eq_getElem (l := s.core.lvl) (i := v61.toNat / 2) hv61_lvl,
          Option.getD_some]
      have hx70_eq : BitVec.setWidth 64 v67 - BitVec.setWidth 64 minL_bv =
          BitVec.ofNat 64 (m7Bkt s.core.lvl minL v61) := by
        rw [s7_sub_zext64_of_le hx_min, hbi_eq]
      rw [hx70_eq]
      let bi := m7Bkt s.core.lvl minL v61
      have hbi_lt : bi < span := hstep.1
      have hidx64 : BitVec.ofNat 64 c.max_vars + BitVec.ofNat 64 bi =
          BitVec.ofNat 64 (c.max_vars + bi) :=
        s7_add_bv64_ofNat (by omega)
      rw [hidx64]
      have hbi_w : c.max_vars + bi < ws_k.length := by rw [hlen_wk]; omega
      have hld_v75 := s7_load_wsort_nat hst_s hbi_w (by omega) hm
      m7_ld hld_v75
      m7_lets
      let old := ws_k[c.max_vars + bi]'hbi_w
      have hold_eq : old = wst_k[bi]'(by rw [hwst_len]; omega) := by
        dsimp [old, wst_k]; simp [List.getElem_drop]
      have hold_le : old.toNat + 1 ≤ k := hold_eq ▸ hstep.2.1
      have hold32 : old.toNat + 1 < 2 ^ 32 := by
        have := c.hmaxv; unfold Ref.dimacsBound at this; omega
      rw [s7_add_bv32_ofNat hold32]
      obtain ⟨st', hst_c', hst_s', hok, hm_raw⟩ := s7_store_wsort_nat (i := c.max_vars + bi)
        (BitVec.ofNat 32 (old.toNat + 1)) hst_c hst_s hbi_w (by omega) hm
      m7_st m_n, hm' := And.intro hok hm_raw
      m7_lets
      have hk1_bv : BitVec.ofNat 64 k + (1 : BitVec 64) = BitVec.ofNat 64 (k + 1) :=
        s7_add1_bv64 (by omega)
      rw [hk1_bv]
      let ws_k1 := ws_k.set (c.max_vars + bi) (BitVec.ofNat 32 (old.toNat + 1))
      have hpre1 : ∀ q < c.max_vars, ws_k1[q]? = ws0[q]? := fun q hq => by
        dsimp [ws_k1]; rw [List.getElem?_set_ne (by omega)]; exact hpre q hq
      have hsl_k1 : m7Slice ws_k 1 (k + 1) = m7Slice ws0 1 (k + 1) :=
        s7Slice_congr_lt (by omega) (by rw [hlen_wk]; omega) (by rw [hlen_ws0]; omega)
          (fun q hq => hpre q (by omega))
      refine hIH (N - (k + 1)) (BitVec.ofNat 64 (k + 1), ()) _ (by omega)
        ⟨k + 1, st', ws_k1, rfl, by omega, by omega, rfl, hst_c', hst_s',
          by simp [ws_k1, hlen_wk], hpre1, fun b hb => ?_, hm'⟩
      have hd_drop : ws_k1.drop c.max_vars = wst_k.set bi (BitVec.ofNat 32 (old.toNat + 1)) :=
        s7_drop_set_offset ws_k _ hlen_wk (by omega)
      have hst_b := hstep.2.2.2 b hb
      rw [← hold_eq, ← hd_drop, List.getElem?_drop] at hst_b
      rwa [← hsl_k1]
    · have hk_ge : N ≤ k := by
        have h := s7_ult64_false hge_b
        rw [hxs, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h
        rwa [Nat.mod_eq_of_lt hN64, Nat.mod_eq_of_lt (by omega)] at h
      have hk_eq : k = N := by omega
      subst hk_eq
      exact hNext st ws_k m hst_c hst_s hlen_wk hpre hcnt hm
  · intro J56 hExit56
    apply hExit56 (N - 1) (BitVec.ofNat 64 1, ()) m0
    refine ⟨1, st0, ws0, rfl, Nat.le_refl 1, h1N, rfl, hc0, hs0, hlen_ws0,
      fun _ _ => rfl, fun b hb => ?_, hm0⟩
    rw [m7Slice_nil _ (Nat.le_refl 1), m7BktCnt_nil]
    exact hzero b hb

private theorem s7_sort_pref_wp {Γ : Env} {c : FullCfg} {s st0 : FullState}
    {ws0 : List (BitVec 32)} {R : Mem 64 → Prop} {m0 : Mem 64} {Q : Post []} {X : XPost}
    {tot : Nat → Nat} {span : Nat} {kNext : Expr Val Cont []}
    (hlen_ws0 : ws0.length = 2 * c.max_vars)
    (hspan_le : span ≤ c.max_vars)
    (hspos_N : m7PrefixStart tot span ≤ c.max_vars)
    (hsuf0 : ∀ b < span, (ws0[c.max_vars + b]?.getD 0#32).toNat = tot b)
    (hc0 : st0.core = { s.core with tmp := s.core.tmp })
    (hs0 : st0.scratch = { s.scratch with wsort := ws0 })
    (hm0 : (FullMem c st0 ⋆ R) m0)
    (hNext : ∀ st' ws' m',
      st'.core = { s.core with tmp := s.core.tmp } →
      st'.scratch = { s.scratch with wsort := ws' } →
      ws'.length = 2 * c.max_vars →
      (∀ q < c.max_vars, ws'[q]? = ws0[q]?) →
      (∀ b < span, (ws'[c.max_vars + b]?.getD 0#32).toNat = m7PrefixStart tot b) →
      (FullMem c st' ⋆ R) m' → wp Γ Q X kNext m') :
    wp Γ Q X (s7SortPrefExpr (BitVec.ofNat 64 c.max_vars) (BitVec.ofNat 64 span) c.pWsort kNext)
      m0 := by
  have hmv60 : c.max_vars < 2 ^ 60 := by have := c.hmaxv; unfold Ref.dimacsBound at this; omega
  have hsp64 : span < 2 ^ 64 := by omega
  have hmv32 : c.max_vars < 2 ^ 32 := by have := c.hmaxv; unfold Ref.dimacsBound at this; omega
  let Inv : Nat → Tup Val [i64, i64] → Mem 64 → Prop := fun meas xs m =>
    ∃ j st ws_j, xs.1 = BitVec.ofNat 64 j ∧ j ≤ span ∧ meas = span - j ∧
      xs.2.1.toNat = m7PrefixStart tot j ∧
      st.core = { s.core with tmp := s.core.tmp } ∧
      st.scratch = { s.scratch with wsort := ws_j } ∧
      ws_j.length = 2 * c.max_vars ∧
      (∀ q < c.max_vars, ws_j[q]? = ws0[q]?) ∧
      (∀ b, j ≤ b → b < span → (ws_j[c.max_vars + b]?.getD 0#32).toNat = tot b) ∧
      (∀ b < j, (ws_j[c.max_vars + b]?.getD 0#32).toNat = m7PrefixStart tot b) ∧
      (FullMem c st ⋆ R) m
  refine wp_loop_group Inv ?_ ?_
  · intro J78 meas xs m hIH ⟨j, st, ws_j, hxs1, hj_le, hmeas, hsum, hst_c, hst_s,
      hlen_ws, hpre_arr, hsuf, hpre, hm⟩
    rw [Blocks.get_here]
    m7_lets
    m7_jnz
    refine ⟨fun hlt_b => ?_, fun hge_b => ?_⟩
    · have hj_lt : j < span := by
        have h := s7_ult64_true hlt_b
        rw [hxs1, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h
        rwa [Nat.mod_eq_of_lt hsp64, Nat.mod_eq_of_lt (by omega)] at h
      have hs_bd : m7PrefixStart tot (j + 1) < 2 ^ 32 := by
        have hmono : m7PrefixStart tot (j + 1) ≤ m7PrefixStart tot span :=
          m7PrefixStart_mono (by omega)
        omega
      let wst_j := ws_j.drop c.max_vars
      have hwst_len : wst_j.length = c.max_vars := by simp [wst_j, hlen_ws]; omega
      have hj_ws : c.max_vars + j < ws_j.length := by rw [hlen_ws]; omega
      m7_lets
      have hj_off64 : BitVec.ofNat 64 c.max_vars + BitVec.ofNat 64 j =
          BitVec.ofNat 64 (c.max_vars + j) :=
        s7_add_bv64_ofNat (by omega)
      rw [hxs1, hj_off64]
      have hld_v84 := s7_load_wsort_nat hst_s hj_ws (by omega) hm
      m7_ld hld_v84
      m7_lets
      rw [hj_off64]
      let wj := ws_j[c.max_vars + j]'hj_ws
      have hwj_drop : wj = wst_j[j]'(by rw [hwst_len]; omega) := by
        dsimp [wj, wst_j]; simp [List.getElem_drop]
      have hrs32 : xs.2.1.toNat < 2 ^ 32 := by
        have hmono : m7PrefixStart tot j ≤ m7PrefixStart tot (j + 1) := by
          rw [m7PrefixStart_succ]; exact Nat.le_add_right _ _
        omega
      rw [s7_trunc_zext64 hrs32]
      obtain ⟨st', hst_c', hst_s', hok, hm_raw⟩ := s7_store_wsort_nat (i := c.max_vars + j)
        (BitVec.ofNat 32 xs.2.1.toNat) hst_c hst_s hj_ws (by omega) hm
      m7_st m_n, hm' := And.intro hok hm_raw
      m7_lets
      have hsuf_w : ∀ b, j ≤ b → b < span → (wst_j[b]?.getD 0#32).toNat = tot b := by
        intro b hb1 hb2; dsimp [wst_j]; rw [List.getElem?_drop]; exact hsuf b hb1 hb2
      have hpre_w : ∀ b < j, (wst_j[b]?.getD 0#32).toNat = m7PrefixStart tot b := by
        intro b hb; dsimp [wst_j]; rw [List.getElem?_drop]; exact hpre b hb
      have hstep := m7_pref_step_inv hwst_len hj_lt hspan_le hsum hsuf_w hpre_w hs_bd
      have hj1_bv : BitVec.ofNat 64 j + (1 : BitVec 64) = BitVec.ofNat 64 (j + 1) :=
        s7_add1_bv64 (by omega)
      rw [hj1_bv]
      let ws_j1 := ws_j.set (c.max_vars + j) (BitVec.ofNat 32 xs.2.1.toNat)
      have hd_drop : ws_j1.drop c.max_vars = wst_j.set j (BitVec.ofNat 32 xs.2.1.toNat) :=
        s7_drop_set_offset ws_j _ hlen_ws (by omega)
      refine hIH (span - (j + 1)) (BitVec.ofNat 64 (j + 1), xs.2.1 + wj.setWidth 64, ()) _
        (by omega) ⟨j + 1, st', ws_j1, rfl, by omega, rfl, hwj_drop ▸ hstep.1, hst_c', hst_s',
          by simp [ws_j1, hlen_ws],
          fun q hq => by dsimp [ws_j1]; rw [List.getElem?_set_ne (by omega)]; exact hpre_arr q hq,
          fun b hb1 hb2 => by
            have h := hstep.2.1 b hb1 hb2
            rwa [← hd_drop, List.getElem?_drop] at h,
          fun b hb => by
            have h := hstep.2.2 b hb
            rwa [← hd_drop, List.getElem?_drop] at h,
          hm'⟩
    · have hj_ge : span ≤ j := by
        have h := s7_ult64_false hge_b
        rw [hxs1, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h
        rwa [Nat.mod_eq_of_lt hsp64, Nat.mod_eq_of_lt (by omega)] at h
      have hj_eq : j = span := by omega
      subst hj_eq
      exact hNext st ws_j m hst_c hst_s hlen_ws hpre_arr hpre hm
  · intro J79 hExit79
    apply hExit79 span (BitVec.ofNat 64 0, BitVec.ofNat 64 1, ()) m0
    refine ⟨0, st0, ws0, rfl, Nat.zero_le span, rfl, ?_, hc0, hs0, hlen_ws0,
      fun _ _ => rfl, fun b _ hb => hsuf0 b hb, fun _ hb => by omega, hm0⟩
    rw [m7PrefixStart_zero]; rfl

private theorem s7_sort_scat_wp {Γ : Env} {c : FullCfg} {s st0 : FullState}
    {ws0 : List (BitVec 32)} {R : Mem 64 → Prop} {m0 : Mem 64} {Q : Post []} {X : XPost}
    {minL_bv : BitVec 32} {span : Nat} {kNext : Expr Val Cont []}
    (htmp_len : s.core.tmp.length = c.max_vars)
    (hlvl_len : s.core.lvl.length = c.max_vars)
    (htl : s.core.tmp_len ≤ c.max_vars) (h1N : 1 ≤ s.core.tmp_len)
    (hlen_ws0 : ws0.length = 2 * c.max_vars)
    (hspan_le : span ≤ c.max_vars)
    (hsl_ws : m7Slice ws0 1 s.core.tmp_len = m7Slice s.core.tmp 1 s.core.tmp_len)
    (hminmax : ∀ p, 1 ≤ p → p < s.core.tmp_len →
      minL_bv.toNat ≤ (s.core.lvl[(ws0[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ∧
      (s.core.lvl[(ws0[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat < minL_bv.toNat + span)
    (hbd_ws : ∀ p, 1 ≤ p → p < s.core.tmp_len → (ws0[p]?.getD 0#32).toNat < 2 * c.max_vars)
    (hspos_N : m7PrefixStart (m7BktCnt s.core.lvl minL_bv.toNat (m7Slice ws0 1 s.core.tmp_len))
      span = s.core.tmp_len)
    (hspos_le : ∀ b ≤ span, m7PrefixStart
      (m7BktCnt s.core.lvl minL_bv.toNat (m7Slice ws0 1 s.core.tmp_len)) b ≤ s.core.tmp_len)
    (hspos0 : ∀ b < span, (ws0[c.max_vars + b]?.getD 0#32).toNat = m7PrefixStart
      (m7BktCnt s.core.lvl minL_bv.toNat (m7Slice ws0 1 s.core.tmp_len)) b)
    (hc0 : st0.core = { s.core with tmp := s.core.tmp })
    (hs0 : st0.scratch = { s.scratch with wsort := ws0 })
    (hm0 : (FullMem c st0 ⋆ R) m0)
    (hNext : ∀ st' tmp' ws' m',
      st'.core = { s.core with tmp := tmp' } →
      st'.scratch = { s.scratch with wsort := ws' } →
      tmp'.length = c.max_vars → ws'.length = 2 * c.max_vars →
      (m7Slice tmp' 1 s.core.tmp_len).Perm (m7Slice s.core.tmp 1 s.core.tmp_len) →
      tmp'[0]? = s.core.tmp[0]? →
      (∀ q, s.core.tmp_len ≤ q → tmp'[q]? = s.core.tmp[q]?) →
      (∀ i j, 1 ≤ i → i ≤ j → j < s.core.tmp_len →
        (s.core.lvl[(tmp'[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
        (s.core.lvl[(tmp'[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
      (FullMem c st' ⋆ R) m' → wp Γ Q X kNext m') :
    wp Γ Q X (s7SortScatExpr (BitVec.ofNat 64 c.max_vars) (BitVec.ofNat 64 s.core.tmp_len)
      c.pTmp c.pLevel c.pWsort minL_bv kNext) m0 := by
  let N := s.core.tmp_len
  let minL := minL_bv.toNat
  let tot := m7BktCnt s.core.lvl minL (m7Slice ws0 1 N)
  let spos := m7PrefixStart tot
  have hmv60 : c.max_vars < 2 ^ 60 := by have := c.hmaxv; unfold Ref.dimacsBound at this; omega
  have hN64 : N < 2 ^ 64 := by omega
  let Inv : Nat → Tup Val [i64] → Mem 64 → Prop := fun meas xs m =>
    ∃ k_s st tmp_s ws_s, xs.1 = BitVec.ofNat 64 k_s ∧ 1 ≤ k_s ∧ k_s ≤ N ∧ meas = N - k_s ∧
      st.core = { s.core with tmp := tmp_s } ∧
      st.scratch = { s.scratch with wsort := ws_s } ∧
      tmp_s.length = c.max_vars ∧ ws_s.length = 2 * c.max_vars ∧
      (∀ q < c.max_vars, ws_s[q]? = ws0[q]?) ∧
      tmp_s[0]? = s.core.tmp[0]? ∧ (∀ q, N ≤ q → tmp_s[q]? = s.core.tmp[q]?) ∧
      (∀ b < span, (ws_s[c.max_vars + b]?.getD 0#32).toNat =
        spos b + m7BktCnt s.core.lvl minL (m7Slice ws0 1 k_s) b) ∧
      (∀ b < span, ∀ p, spos b ≤ p → p < (ws_s[c.max_vars + b]?.getD 0#32).toNat →
        m7Bkt s.core.lvl minL (tmp_s[p]?.getD 0#32) = b ∧
        minL ≤ (s.core.lvl[(tmp_s[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) ∧
      (m7FlatBkts tmp_s spos (fun b => (ws_s[c.max_vars + b]?.getD 0#32).toNat) span).Perm
        (m7Slice ws0 1 k_s) ∧
      (FullMem c st ⋆ R) m
  refine wp_loop_group Inv ?_ ?_
  · intro J91 meas xs m hIH ⟨k_s, st, tmp_s, ws_s, hxs, hk1, hk_le, hmeas, hst_c, hst_s,
      hlen_ts, hlen_ws, hpre, h0_s, hout_s, hepos_s, hbkt_s, hperm_s, hm⟩
    rw [Blocks.get_here]
    m7_lets
    m7_jnz
    refine ⟨fun hlt_b => ?_, fun hge_b => ?_⟩
    · have hk_lt : k_s < N := by
        have h := s7_ult64_true hlt_b
        rw [hxs, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h
        rwa [Nat.mod_eq_of_lt hN64, Nat.mod_eq_of_lt (by omega)] at h
      have hks_ws : k_s < ws_s.length := by rw [hlen_ws]; omega
      have hks_ws0 : k_s < ws0.length := by rw [hlen_ws0]; omega
      have hpre_k : ws_s[k_s] = ws0[k_s] := by
        have hq := hpre k_s (by omega)
        rw [List.getElem?_eq_getElem hks_ws, List.getElem?_eq_getElem hks_ws0] at hq
        exact Option.some.inj hq
      have hbd_k := hbd_ws k_s hk1 hk_lt
      rw [List.getElem?_eq_getElem (l := ws0) (i := k_s) hks_ws0, Option.getD_some,
        ← hpre_k] at hbd_k
      m7_lets
      rw [hxs]
      have hld_v97 := s7_load_wsort_nat hst_s hks_ws (by omega) hm
      m7_ld hld_v97
      m7_lets
      let v97 := ws_s[k_s]'hks_ws
      have hv97_bd : v97.toNat < 2 * c.max_vars := hbd_k
      rw [s7_var_idx64 v97]
      have hv97_lvl : v97.toNat / 2 < s.core.lvl.length := by rw [hlvl_len]; omega
      have hld_v103 := s7_load_lvl_nat hst_c hv97_lvl (by omega) hm
      m7_ld hld_v103
      m7_lets
      let v103 := s.core.lvl[v97.toNat / 2]'hv97_lvl
      let wst_s := ws_s.drop c.max_vars
      have hwst_len : wst_s.length = c.max_vars := by simp [wst_s, hlen_ws]; omega
      have hsl_eq : m7Slice ws_s 1 N = m7Slice ws0 1 N :=
        s7Slice_congr_lt (by omega) (by rw [hlen_ws]; omega) (by rw [hlen_ws0]; omega)
          (fun q hq => hpre q (by omega))
      have hsl_ks : m7Slice ws_s 1 k_s = m7Slice ws0 1 k_s :=
        s7Slice_congr_lt hk1 (by rw [hlen_ws]; omega) (by rw [hlen_ws0]; omega)
          (fun q hq => hpre q (by omega))
      have hminmax_s : ∀ p, 1 ≤ p → p < N →
          minL ≤ (s.core.lvl[(ws_s[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ∧
          (s.core.lvl[(ws_s[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat < minL + span := by
        intro p hp1 hp2
        rw [show ws_s[p]? = ws0[p]? from hpre p (by omega)]
        exact hminmax p hp1 hp2
      have hstep := m7_scat_step_inv hlen_ws hlen_ts hwst_len htl hk1 hk_lt hspan_le
        hminmax_s (by rw [hsl_eq]; exact hspos_N) (by intro b hb; rw [hsl_eq]; exact hspos_le b hb)
        h0_s hout_s
        (fun b hb => by dsimp [wst_s]; rw [List.getElem?_drop, hsl_eq, hsl_ks]; exact hepos_s b hb)
        (fun b hb p hp1 hp2 => by
          dsimp [wst_s] at hp2; rw [List.getElem?_drop] at hp2
          rw [hsl_eq] at hp1; exact hbkt_s b hb p hp1 hp2)
        (by
          have hcon : m7FlatBkts tmp_s
              (m7PrefixStart (m7BktCnt s.core.lvl minL (m7Slice ws_s 1 N)))
              (fun b => (wst_s[b]?.getD 0#32).toNat) span =
              m7FlatBkts tmp_s spos (fun b => (ws_s[c.max_vars + b]?.getD 0#32).toNat) span := by
            have h1 : m7PrefixStart (m7BktCnt s.core.lvl minL (m7Slice ws_s 1 N)) = spos := by
              rw [hsl_eq]
            rw [h1]
            simp only [wst_s, List.getElem?_drop]
          rw [hcon, hsl_ks]; exact hperm_s)
      have hx_min : minL ≤ v103.toNat := by
        have h := (hminmax_s k_s hk1 hk_lt).1
        rw [List.getElem?_eq_getElem (l := ws_s) (i := k_s) hks_ws, Option.getD_some,
          List.getElem?_eq_getElem (l := s.core.lvl) (i := v97.toNat / 2) hv97_lvl,
          Option.getD_some] at h
        exact h
      have hbi_eq : v103.toNat - minL = m7Bkt s.core.lvl minL v97 := by
        rw [m7Bkt_eq, List.getElem?_eq_getElem (l := s.core.lvl) (i := v97.toNat / 2) hv97_lvl,
          Option.getD_some]
      have hx106_eq : BitVec.setWidth 64 v103 - BitVec.setWidth 64 minL_bv =
          BitVec.ofNat 64 (m7Bkt s.core.lvl minL v97) := by
        rw [s7_sub_zext64_of_le hx_min, hbi_eq]
      rw [hx106_eq]
      let bi := m7Bkt s.core.lvl minL v97
      have hbi_lt : bi < span := hstep.1
      have hidx64 : BitVec.ofNat 64 c.max_vars + BitVec.ofNat 64 bi =
          BitVec.ofNat 64 (c.max_vars + bi) :=
        s7_add_bv64_ofNat (by omega)
      rw [hidx64]
      have hbi_w : c.max_vars + bi < ws_s.length := by rw [hlen_ws]; omega
      have hld_v109 := s7_load_wsort_nat hst_s hbi_w (by omega) hm
      m7_ld hld_v109
      m7_lets
      let dst_bv := ws_s[c.max_vars + bi]'hbi_w
      let dst := dst_bv.toNat
      have hdst_eq : dst_bv = wst_s[bi]'(by rw [hwst_len]; omega) := by
        dsimp [dst_bv, wst_s]; simp [List.getElem_drop]
      have hdst_ge1 : 1 ≤ dst := by dsimp [dst]; rw [hdst_eq]; exact hstep.2.1
      have hdst1_32 : dst + 1 < 2 ^ 32 := by dsimp [dst]; rw [hdst_eq]; exact hstep.2.2.2.1
      rw [hidx64, s7_trunc_add1_32 hdst1_32]
      obtain ⟨st1, hst1_c, hst1_s, hok1, hm1_raw⟩ := s7_store_wsort_nat (i := c.max_vars + bi)
        (BitVec.ofNat 32 (dst + 1)) hst_c hst_s hbi_w (by omega) hm
      m7_st m1, hm1 := And.intro hok1 hm1_raw
      m7_lets
      have hv109_eq : BitVec.setWidth 64 dst_bv = BitVec.ofNat 64 dst := by
        apply BitVec.eq_of_toNat_eq
        have hdst64 : dst < 2 ^ 64 := Nat.lt_trans dst_bv.isLt (by decide : 2 ^ 32 < 2 ^ 64)
        rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdst64]
      rw [hv109_eq]
      have hdst_lt : dst < N := by dsimp [dst]; rw [hdst_eq]; exact hstep.2.2.1
      have hdst_ts : dst < tmp_s.length := by rw [hlen_ts]; omega
      obtain ⟨st2, hst2_c, hst2_s, hok2, hm2_raw⟩ := s7_store_tmp_nat (i := dst) v97 hst1_c
        hst1_s hdst_ts (by omega) hm1
      m7_st m2, hm2 := And.intro hok2 hm2_raw
      m7_lets
      have hk1_bv : BitVec.ofNat 64 k_s + (1 : BitVec 64) = BitVec.ofNat 64 (k_s + 1) :=
        s7_add1_bv64 (by omega)
      rw [hk1_bv]
      let ws_s1 := ws_s.set (c.max_vars + bi) (BitVec.ofNat 32 (dst + 1))
      have hpre1 : ∀ q < c.max_vars, ws_s1[q]? = ws0[q]? := fun q hq => by
        dsimp [ws_s1]; rw [List.getElem?_set_ne (by omega)]; exact hpre q hq
      have hd_drop : ws_s1.drop c.max_vars = wst_s.set bi (BitVec.ofNat 32 (dst + 1)) :=
        s7_drop_set_offset ws_s _ hlen_ws (by omega)
      have hdst_raw : dst_bv =
          wst_s[m7Bkt s.core.lvl minL ws_s[k_s]]'(by rw [hwst_len]; have := hstep.1; omega) := by
        simpa only [bi, v97] using hdst_eq
      have hd_drop_raw : ws_s1.drop c.max_vars =
          wst_s.set (m7Bkt s.core.lvl minL ws_s[k_s])
            (BitVec.ofNat 32 (wst_s[m7Bkt s.core.lvl minL ws_s[k_s]].toNat + 1)) := by
        simpa only [bi, v97, dst, hdst_raw] using hd_drop
      have hsl_k1 : m7Slice ws_s 1 (k_s + 1) = m7Slice ws0 1 (k_s + 1) :=
        s7Slice_congr_lt (by omega) (by rw [hlen_ws]; omega) (by rw [hlen_ws0]; omega)
          (fun q hq => hpre q (by omega))
      refine hIH (N - (k_s + 1)) (BitVec.ofNat 64 (k_s + 1), ()) _ (by omega)
        ⟨k_s + 1, st2, tmp_s.set dst v97, ws_s1,
          rfl, by omega, by omega, rfl, hst2_c, hst2_s,
          by simp [hlen_ts],
          by simp [ws_s1, hlen_ws], hpre1,
          by rw [List.getElem?_set_ne (by omega)]; exact h0_s,
          fun q hq => by rw [List.getElem?_set_ne (by omega)]; exact hout_s q hq,
          fun b hb => by
            have h := hstep.2.2.2.2.2.2.2.2.1 b hb
            simpa only [spos, minL, N, ← hd_drop_raw, List.getElem?_drop, hsl_eq, hsl_k1] using h,
          fun b hb p hp1 hp2 => by
            have h := hstep.2.2.2.2.2.2.2.2.2.1 b hb p
              (by simpa only [spos, tot, minL, N, hsl_eq] using hp1)
              (by simpa only [← hd_drop_raw, List.getElem?_drop] using hp2)
            simpa only [dst, v97, ← hdst_raw] using h,
          by
            have h := hstep.2.2.2.2.2.2.2.2.2.2
            rw [← hd_drop_raw, ← hdst_raw] at h
            have hcon : m7FlatBkts (tmp_s.set dst v97) spos
                (fun b => (ws_s1[c.max_vars + b]?.getD 0#32).toNat) span =
                m7FlatBkts (tmp_s.set dst v97)
                  (m7PrefixStart (m7BktCnt s.core.lvl minL (m7Slice ws_s 1 N)))
                  (fun b => ((ws_s1.drop c.max_vars)[b]?.getD 0#32).toNat) span := by
              have h1 : m7PrefixStart (m7BktCnt s.core.lvl minL (m7Slice ws_s 1 N)) = spos := by
                rw [hsl_eq]
              rw [h1]; simp [List.getElem?_drop]
            rw [hcon]
            simpa only [dst, v97, N, hsl_k1] using h,
          hm2⟩
    · have hk_ge : N ≤ k_s := by
        have h := s7_ult64_false hge_b
        rw [hxs, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h
        rwa [Nat.mod_eq_of_lt hN64, Nat.mod_eq_of_lt (by omega)] at h
      have hk_eq : k_s = N := by omega
      subst hk_eq
      have hsl_eq : m7Slice ws_s 1 N = m7Slice ws0 1 N :=
        s7Slice_congr_lt (by omega) (by rw [hlen_ws]; omega) (by rw [hlen_ws0]; omega)
          (fun q hq => hpre q (by omega))
      have hfin := m7_scat_finish_inv hlen_ts htl (hsl_eq.trans hsl_ws)
        (by rw [hsl_eq]; exact hspos_N)
        (fun b hb => by
          rw [List.getElem?_drop, hsl_eq]; exact hepos_s b hb)
        (fun b hb p hp1 hp2 => by
          rw [List.getElem?_drop] at hp2
          rw [hsl_eq] at hp1; exact hbkt_s b hb p hp1 hp2)
        (by
          have hcon : m7FlatBkts tmp_s
              (m7PrefixStart (m7BktCnt s.core.lvl minL (m7Slice ws_s 1 N)))
              (fun b => ((ws_s.drop c.max_vars)[b]?.getD 0#32).toNat) span =
              m7FlatBkts tmp_s spos (fun b => (ws_s[c.max_vars + b]?.getD 0#32).toNat) span := by
            have h1 : m7PrefixStart (m7BktCnt s.core.lvl minL (m7Slice ws_s 1 N)) = spos := by
              rw [hsl_eq]
            rw [h1]; simp [List.getElem?_drop]
          rw [hcon, hsl_eq]; exact hperm_s)
      exact hNext st tmp_s ws_s m hst_c hst_s hlen_ts hlen_ws hfin.1 h0_s hout_s hfin.2 hm
  · intro J92 hExit92
    apply hExit92 (N - 1) (BitVec.ofNat 64 1, ()) m0
    refine ⟨1, st0, s.core.tmp, ws0, rfl, Nat.le_refl 1, h1N, rfl, hc0, hs0, htmp_len, hlen_ws0,
      fun _ _ => rfl, rfl, fun _ _ => rfl, ?_, ?_, ?_, hm0⟩
    · intro b hb; rw [m7Slice_nil _ (Nat.le_refl 1), m7BktCnt_nil, Nat.add_zero]; exact hspos0 b hb
    · intro b hb p hp1 hp2
      change spos b ≤ p at hp1; rw [hspos0 b hb] at hp2
      dsimp only [spos, tot, minL, N] at hp1; omega
    · rw [m7FlatBkts_nil _ _ _ _ (fun b hb => by
          rw [hspos0 b hb]; dsimp only [spos, tot, minL]; exact Nat.le_refl _),
        m7Slice_nil _ (Nat.le_refl 1)]


/-! ## 4. Post-Copy Tail & Main `full_sort_tmp_wp` -/

private abbrev s7SortTailExpr {Val : Ty → Type} {Cont : List Ty → Type}
    (n64 mv64 pTmp pLvl pWsort : Val i64) (minL maxL : Val i32) : Expr Val Cont [] :=
  .let_ (Op.mk (.zext 32 64) (Arg.var maxL, ())) fun t1 =>
  .let_ (Op.mk (.zext 32 64) (Arg.var minL, ())) fun t2 =>
  .let_ (Op.mk (.sub i64) (Arg.var t1.1, Arg.var t2.1, ())) fun t3 =>
  .let_ (Op.mk (.add i64) (Arg.var t3.1, Arg.imm 1, ())) fun sp =>
  .let_ (Op.mk (.sub i64) (Arg.var n64, Arg.imm 1, ())) fun nn =>
  .let_ (Op.mk (.cmp .eq i64 .bool rfl) (Arg.var sp.1, Arg.imm 1, ())) fun c1 =>
  .jnz (Arg.var c1.1) (.ret ())
    (.group (sig := [[]]) (fun _ =>
      .cons (fun _ => s7SortMergeExpr n64 nn.1 pTmp pLvl pWsort) .nil)
      (fun J =>
        .let_ (Op.mk (.cmp .ule i64 .bool rfl) (Arg.var sp.1, Arg.var mv64, ())) fun c2 =>
        .jnz (Arg.var c2.1)
          (.let_ (Op.mk (.sext 32 64) (Arg.imm 2, ())) fun t4 =>
          .let_ (Op.mk (.shl i64) (Arg.var nn.1, Arg.var t4.1, ())) fun t5 =>
          .let_ (Op.mk (.cmp .ule i64 .bool rfl) (Arg.var sp.1, Arg.var t5.1, ())) fun c3 =>
          .jnz (Arg.var c3.1)
            (s7SortZeroExpr mv64 sp.1 pWsort
              (s7SortHistExpr mv64 n64 pLvl pWsort minL
                (s7SortPrefExpr mv64 sp.1 pWsort
                  (s7SortScatExpr mv64 n64 pTmp pLvl pWsort minL (.ret ())))))
            (.jump J.1 ()))
          (.jump J.1 ())))

private theorem s7_ws_eq_tmp {s : FullState} {ws_k : List (BitVec 32)} {mv : Nat}
    (htmp_len : s.core.tmp.length = mv) (hlen_wk : ws_k.length = 2 * mv)
    (htl : s.core.tmp_len ≤ mv)
    (hsl_wk : m7Slice ws_k 1 s.core.tmp_len = m7Slice s.core.tmp 1 s.core.tmp_len)
    {p : Nat} (hp1 : 1 ≤ p) (hp2 : p < s.core.tmp_len) : ws_k[p]? = s.core.tmp[p]? := by
  have hw : p < ws_k.length := by rw [hlen_wk]; omega
  have ht : p < s.core.tmp.length := by rw [htmp_len]; omega
  rw [List.getElem?_eq_getElem (l := ws_k) (i := p) hw,
    List.getElem?_eq_getElem (l := s.core.tmp) (i := p) ht]
  congr 1
  have hs := congrArg (fun l => l[p - 1]?) hsl_wk
  rw [List.getElem?_eq_getElem (by rw [m7Slice_length, hlen_wk]; omega),
    List.getElem?_eq_getElem (by rw [m7Slice_length, htmp_len]; omega),
    m7Slice_getElem, m7Slice_getElem] at hs
  simp only [Option.some.injEq] at hs
  simpa [show 1 + (p - 1) = p by omega] using hs

private theorem s7_sort_tail_wp {Γ : Env} {c : FullCfg} {s st_c : FullState}
    {ws_k : List (BitVec 32)} {R : Mem 64 → Prop} {m_c : Mem 64} {Q : Post []} {X : XPost}
    {minL maxL : BitVec 32}
    (hlenOk : FullState.LengthsOk c s) (htl : s.core.tmp_len ≤ c.max_vars)
    (hbd : ∀ k, 1 ≤ k → k < s.core.tmp_len →
      (s.core.tmp[k]?.getD 0#32).toNat < 2 * c.max_vars)
    (hQ : ∀ tmp' wsort' m',
      let s' : FullState := FullState.mk { s.core with tmp := tmp' }
        { s.scratch with wsort := wsort' };
      FullState.LengthsOk c s' → tmp'.length = c.max_vars →
      (s.core.tmp_len ≤ 32 → wsort' = s.scratch.wsort) →
      (tmp'.take s.core.tmp_len).Perm (s.core.tmp.take s.core.tmp_len) →
      (0 < s.core.tmp_len → tmp'[0]? = s.core.tmp[0]?) →
      (∀ j, 1 ≤ j → j < s.core.tmp_len →
        ∃ i, 1 ≤ i ∧ i < s.core.tmp_len ∧ tmp'[j]? = s.core.tmp[i]?) →
      (∀ i, 1 ≤ i → i < s.core.tmp_len →
        ∃ j, 1 ≤ j ∧ j < s.core.tmp_len ∧ s.core.tmp[i]? = tmp'[j]?) →
      (∀ i j, 1 ≤ i → i ≤ j → j < s.core.tmp_len →
        (s.core.lvl[(tmp'[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
        (s.core.lvl[(tmp'[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
      FullExtScratchPres s s' → (FullMem c s' ⋆ R) m' → Q () m')
    (hNgt32 : 32 < s.core.tmp_len) (hmn_mx : minL.toNat ≤ maxL.toNat)
    (hst_c : st_c.core = { s.core with tmp := s.core.tmp })
    (hst_s : st_c.scratch = { s.scratch with wsort := ws_k })
    (hlen_wk : ws_k.length = 2 * c.max_vars)
    (hsl_wk : m7Slice ws_k 1 s.core.tmp_len = m7Slice s.core.tmp 1 s.core.tmp_len)
    (hminmax_k : ∀ p, 1 ≤ p → p < s.core.tmp_len →
      minL.toNat ≤ (s.core.lvl[(ws_k[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ∧
      (s.core.lvl[(ws_k[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ maxL.toNat)
    (hm_c : (FullMem c st_c ⋆ R) m_c) :
    wp Γ Q X (s7SortTailExpr (BitVec.ofNat 64 s.core.tmp_len) (BitVec.ofNat 64 c.max_vars)
      c.pTmp c.pLevel c.pWsort minL maxL) m_c := by
  have htmp_len : s.core.tmp.length = c.max_vars := hlenOk.core_ok.tmp_len_arr
  have hlvl_len : s.core.lvl.length = c.max_vars := hlenOk.core_ok.lvl_len
  have hmv64 : c.max_vars < 2 ^ 64 := by have := c.hmaxv; unfold Ref.dimacsBound at this; omega
  have hmv60 : c.max_vars < 2 ^ 60 := by have := c.hmaxv; unfold Ref.dimacsBound at this; omega
  have hN64 : s.core.tmp_len < 2 ^ 64 := by omega
  dsimp only [s7SortTailExpr]
  m7_lets
  have hspan_bv :
      (BitVec.setWidth 64 maxL - BitVec.setWidth 64 minL) + (1 : BitVec 64) =
      BitVec.ofNat 64 (maxL.toNat - minL.toNat + 1) := by
    rw [s7_sub_zext64_of_le hmn_mx]
    exact s7_add1_bv64 (by
      have h32 := maxL.isLt
      change maxL.toNat - minL.toNat + 1 < 2 ^ 64; omega)
  rw [hspan_bv]
  let span := maxL.toNat - minL.toNat + 1
  have hsp64 : span < 2 ^ 64 := by have h32 := maxL.isLt; dsimp [span]; omega
  have hN1_bv : BitVec.ofNat 64 s.core.tmp_len - (1 : BitVec 64) =
      BitVec.ofNat 64 (s.core.tmp_len - 1) :=
    s7_sub1_bv64 (by omega) hN64
  rw [hN1_bv]
  have hws_tmp : ∀ p, 1 ≤ p → p < s.core.tmp_len → ws_k[p]? = s.core.tmp[p]? :=
    fun p hp1 hp2 => s7_ws_eq_tmp htmp_len hlen_wk htl hsl_wk hp1 hp2
  m7_jnz
  refine ⟨fun heq1_b => ?_, fun hne1_b => ?_⟩
  · have hsp1 : span = 1 := by
      have hn := congrArg BitVec.toNat (beq_iff_eq.mp heq1_b)
      simp at hn
      show maxL.toNat - minL.toNat + 1 = 1
      omega
    refine s7_finish_spec hlenOk htl hst_c hst_s htmp_len hlen_wk (fun h => by omega)
      (List.Perm.refl _) (fun _ => rfl) (fun i j hi hij hj => ?_) hm_c hQ
    have hmi := hminmax_k i hi (by omega)
    have hmj := hminmax_k j (by omega) hj
    rw [hws_tmp i hi (by omega)] at hmi
    rw [hws_tmp j (by omega) hj] at hmj
    dsimp [span] at hsp1
    omega
  · refine wp_join_group (fun _ m' => m' = m_c) ?_ ?_
    · intro J _ m' hm'
      rw [hm', Blocks.get_here]
      m7_lets
      exact s7_sort_merge_wp htmp_len hlvl_len htl (by omega) hbd hlen_wk hst_c hst_s hm_c
        fun st' tmp' ws' m' hc' hs' hlen_t' hlen_w' hperm' h0' hsort' hm' =>
          s7_finish_spec hlenOk htl hc' hs' hlen_t' hlen_w' (fun h => by omega) hperm'
            (fun _ => h0') hsort' hm' hQ
    · intro J hExit
      m7_lets
      m7_jnz
      refine ⟨fun hle_mv_b => ?_, fun _ => hExit () m_c rfl⟩
      have hspan_le_mv : span ≤ c.max_vars := by
        have h := s7_ule64_true hle_mv_b
        rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsp64,
          Nat.mod_eq_of_lt hmv64] at h
        exact h
      m7_lets
      m7_jnz
      refine ⟨fun _ => ?_, fun _ => hExit () m_c rfl⟩
      change wp Γ Q X (s7SortZeroExpr (BitVec.ofNat 64 c.max_vars)
        (BitVec.ofNat 64 span) c.pWsort
        (s7SortHistExpr (BitVec.ofNat 64 c.max_vars)
          (BitVec.ofNat 64 s.core.tmp_len) c.pLevel c.pWsort minL
          (s7SortPrefExpr (BitVec.ofNat 64 c.max_vars) (BitVec.ofNat 64 span)
            c.pWsort
            (s7SortScatExpr (BitVec.ofNat 64 c.max_vars)
              (BitVec.ofNat 64 s.core.tmp_len) c.pTmp c.pLevel c.pWsort minL
              (.ret ()))))) m_c
      have hminmax_ws : ∀ p, 1 ≤ p → p < s.core.tmp_len →
          minL.toNat ≤
            (s.core.lvl[(ws_k[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ∧
          (s.core.lvl[(ws_k[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat <
            minL.toNat + span := by
        intro p hp1 hp2
        have h := hminmax_k p hp1 hp2
        exact ⟨h.1, by dsimp [span]; omega⟩
      have hbd_ws : ∀ p, 1 ≤ p → p < s.core.tmp_len →
          (ws_k[p]?.getD 0#32).toNat < 2 * c.max_vars := by
        intro p hp1 hp2
        have h1 : ws_k[p]? = s.core.tmp[p]? := by
          have hw : p < ws_k.length := by rw [hlen_wk]; omega
          have ht : p < s.core.tmp.length := by rw [htmp_len]; omega
          rw [List.getElem?_eq_getElem (l := ws_k) (i := p) hw,
            List.getElem?_eq_getElem (l := s.core.tmp) (i := p) ht]
          congr 1
          have hs := congrArg (fun l => l[p - 1]?) hsl_wk
          rw [List.getElem?_eq_getElem (by rw [m7Slice_length, hlen_wk]; omega),
            List.getElem?_eq_getElem (by rw [m7Slice_length, htmp_len]; omega),
            m7Slice_getElem, m7Slice_getElem] at hs
          simp only [Option.some.injEq] at hs
          simpa [show 1 + (p - 1) = p by omega] using hs
        rw [h1]; exact hbd p hp1 hp2
      let tot := m7BktCnt s.core.lvl minL.toNat (m7Slice ws_k 1 s.core.tmp_len)
      have hspos_N : m7PrefixStart tot span = s.core.tmp_len := by
        rw [m7PrefixStart_eq_sum]
        have hsum := m7BktCnt_sum_range s.core.lvl minL.toNat
          (m7Slice ws_k 1 s.core.tmp_len) span (fun y hy => by
            rw [List.mem_iff_getElem] at hy
            obtain ⟨idx, hidx, rfl⟩ := hy
            rw [m7Slice_length, hlen_wk] at hidx
            rw [m7Slice_getElem, m7Bkt_eq]
            have hmm := hminmax_ws (1 + idx) (by omega) (by omega)
            rw [List.getElem?_eq_getElem (l := ws_k) (i := 1 + idx)
              (by rw [hlen_wk]; omega), Option.getD_some] at hmm
            omega)
        rw [m7Slice_length, hlen_wk] at hsum
        dsimp only [tot]; rw [hsum]; omega
      have hspos_le : ∀ b ≤ span, m7PrefixStart tot b ≤ s.core.tmp_len :=
        fun b hb => hspos_N ▸ m7PrefixStart_mono hb
      refine s7_sort_zero_wp hspan_le_mv hst_c hst_s hlen_wk hm_c ?_
      intro st1 ws1 m1 hst1_c hst1_s hlen_ws1 hpre1 hz1 hm1
      have hsl1 :
          m7Slice ws1 1 s.core.tmp_len = m7Slice s.core.tmp 1 s.core.tmp_len :=
        (s7Slice_congr_lt (by omega) (by rw [hlen_ws1]; omega)
          (by rw [hlen_wk]; omega) (fun q hq => hpre1 q (by omega))).trans hsl_wk
      have hminmax1 : ∀ p, 1 ≤ p → p < s.core.tmp_len →
          minL.toNat ≤
            (s.core.lvl[(ws1[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ∧
          (s.core.lvl[(ws1[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat <
            minL.toNat + span := fun p hp1 hp2 => by
        rw [show ws1[p]? = ws_k[p]? from hpre1 p (by omega)]
        exact hminmax_ws p hp1 hp2
      have hbd1' : ∀ p, 1 ≤ p → p < s.core.tmp_len →
          (ws1[p]?.getD 0#32).toNat < 2 * c.max_vars := fun p hp1 hp2 => by
        rw [show ws1[p]? = ws_k[p]? from hpre1 p (by omega)]
        exact hbd_ws p hp1 hp2
      refine s7_sort_hist_wp hlvl_len htl (by omega) hlen_ws1 hspan_le_mv
        hminmax1 hbd1' hz1 hst1_c hst1_s hm1 ?_
      intro st2 ws2 m2 hst2_c hst2_s hlen_ws2 hpre2 hcnt2 hm2
      have hpre20 : ∀ q < c.max_vars, ws2[q]? = ws_k[q]? :=
        fun q hq => (hpre2 q hq).trans (hpre1 q hq)
      have hsl1_k : m7Slice ws1 1 s.core.tmp_len = m7Slice ws_k 1 s.core.tmp_len :=
        s7Slice_congr_lt (by omega) (by rw [hlen_ws1]; omega)
          (by rw [hlen_wk]; omega) (fun q hq => hpre1 q (by omega))
      refine s7_sort_pref_wp hlen_ws2 hspan_le_mv (by rw [hspos_N]; exact htl)
        (fun b hb => by rw [hcnt2 b hb, hsl1_k])
        hst2_c hst2_s hm2 ?_
      intro st3 ws3 m3 hst3_c hst3_s hlen_ws3 hpre3 hpref3 hm3
      have hpre3k : ∀ q < c.max_vars, ws3[q]? = ws_k[q]? :=
        fun q hq => (hpre3 q hq).trans (hpre20 q hq)
      have hsl3 : m7Slice ws3 1 s.core.tmp_len = m7Slice ws_k 1 s.core.tmp_len :=
        s7Slice_congr_lt (by omega) (by rw [hlen_ws3]; omega)
          (by rw [hlen_wk]; omega) (fun q hq => hpre3k q (by omega))
      have hminmax3 : ∀ p, 1 ≤ p → p < s.core.tmp_len →
          minL.toNat ≤
            (s.core.lvl[(ws3[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ∧
          (s.core.lvl[(ws3[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat <
            minL.toNat + span := fun p hp1 hp2 => by
        rw [show ws3[p]? = ws_k[p]? from hpre3k p (by omega)]
        exact hminmax_ws p hp1 hp2
      have hbd3 : ∀ p, 1 ≤ p → p < s.core.tmp_len →
          (ws3[p]?.getD 0#32).toNat < 2 * c.max_vars := fun p hp1 hp2 => by
        rw [show ws3[p]? = ws_k[p]? from hpre3k p (by omega)]
        exact hbd_ws p hp1 hp2
      refine s7_sort_scat_wp htmp_len hlvl_len htl (by omega) hlen_ws3 hspan_le_mv
        (hsl3.trans hsl_wk) hminmax3 hbd3 (by rw [hsl3]; exact hspos_N)
        (fun b hb => by rw [hsl3]; exact hspos_le b hb)
        (fun b hb => by rw [hsl3]; exact hpref3 b hb) hst3_c hst3_s hm3 ?_
      intro st4 tmp4 ws4 m4 hst4_c hst4_s hlen_t4 hlen_ws4 hperm4 h0_4 hout_4
        hlvl4 hm4
      exact s7_finish_spec hlenOk htl hst4_c hst4_s hlen_t4 hlen_ws4
        (fun h => by omega) hperm4 (fun _ => h0_4) hlvl4 hm4 hQ

/-- `Func.wp` soundness of `full_sort_tmp` (`≤ 32` insertion sort, `> 32` counting sort in
`wsort`, bottom-up merge-sort fallback) against `Spec.fullSortTmpSpec`. -/
theorem full_sort_tmp_wp (Γ : Env) :
    ∀ (args : Tup Val [i64]) (m : Mem 64) (Q : Post []) (X : XPost),
      Spec.fullSortTmpSpec args m Q X →
      Func.wp Γ full_sort_tmp_body args m Q X := by
  intro args m Q X hspec
  rcases args with ⟨p_hd, ⟨⟩⟩
  obtain ⟨c, s, R, heq, hlenOk, htl, hbd, hm, hQ⟩ := hspec
  subst heq
  dsimp only [Func.wp, full_sort_tmp_body]
  have htmp_len : s.core.tmp.length = c.max_vars := hlenOk.core_ok.tmp_len_arr
  have hlvl_len : s.core.lvl.length = c.max_vars := hlenOk.core_ok.lvl_len
  have hws_len : s.scratch.wsort.length = 2 * c.max_vars := hlenOk.scratch_ok.wsort_len
  have hmv64 : c.max_vars < 2 ^ 64 := by have := c.hmaxv; unfold Ref.dimacsBound at this; omega
  have hN64 : s.core.tmp_len < 2 ^ 64 := by omega
  m7_lets
  m7_ld (load_full_tmp_len hm)
  m7_lets
  m7_ld (load_full_max_vars hm)
  m7_lets
  m7_jnz
  refine ⟨fun hule2 => ?_, fun hgt2 => ?_⟩
  · have hNle2 : s.core.tmp_len ≤ 2 := by
      have h := s7_ule64_true hule2
      simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hN64] using h
    obtain ⟨st0, hc0, hs0, hm0⟩ := m7_wrap_state hm
    exact s7_finish_spec hlenOk htl hc0 hs0 htmp_len hws_len (fun _ => rfl) (List.Perm.refl _)
      (fun _ => rfl) (fun i j hi hij hj => by
        have : i = 1 := by omega
        have : j = 1 := by omega
        subst_vars; exact Nat.le_refl _) hm0 hQ
  · have hNgt2 : 2 < s.core.tmp_len := by
      have h := s7_ule64_false hgt2
      simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hN64] using h
    m7_lets
    m7_jnz
    refine ⟨fun hbad_gt => ?_, fun _ => ?_⟩
    · have h := s7_ult64_true hbad_gt
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hmv64, Nat.mod_eq_of_lt hN64] at h
      omega
    · m7_lets
      m7_ld (load_full_tmp_lits_ptr hm)
      m7_lets
      m7_ld (load_full_level_ptr hm)
      m7_lets
      m7_jnz
      refine ⟨fun _ => ?_, fun hgt32_b => ?_⟩
      · obtain ⟨st0, hc0, hs0, hm0⟩ := m7_wrap_state hm
        change wp Γ Q X (s7SortInsExpr (BitVec.ofNat 64 s.core.tmp_len) c.pTmp c.pLevel) m
        exact s7_sort_ins_wp htmp_len hlvl_len htl (by omega) hbd hc0 hs0 hm0
          fun st' tmp' m' hc' hs' hlen' hperm' h0' hsort' hm' =>
            s7_finish_spec hlenOk htl hc' hs' hlen' hws_len (fun _ => rfl) hperm'
              (fun _ => h0') hsort' hm' hQ
      · have hNgt32 : 32 < s.core.tmp_len := by
          have h := s7_ule64_false hgt32_b
          simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hN64] using h
        m7_lets
        m7_ld (load_full_wsort_ptr hm)
        m7_lets
        have hs1 : BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 1 := by decide
        rw [hs1]
        have h1t : 1 < s.core.tmp.length := by rw [htmp_len]; omega
        have h1w : 1 < s.scratch.wsort.length := by rw [hws_len]; omega
        have hbd1 := hbd 1 (Nat.le_refl 1) (by omega)
        rw [List.getElem?_eq_getElem (l := s.core.tmp) (i := 1) h1t, Option.getD_some] at hbd1
        obtain ⟨st0, hc0, hs0, hm0⟩ := m7_wrap_state hm
        have hld_v284 := s7_load_tmp_nat hc0 h1t (by decide) hm0
        m7_ld hld_v284
        m7_lets
        obtain ⟨st1, hc1, hs1', hok1, hm1_raw⟩ := s7_store_wsort_nat (i := 1)
          (s.core.tmp[1]'h1t) hc0 hs0 h1w (by decide) hm0
        m7_st m1, hm1 := And.intro hok1 hm1_raw
        m7_lets
        let v284 := s.core.tmp[1]'h1t
        have hv284_bd : v284.toNat < 2 * c.max_vars := hbd1
        rw [s7_var_idx64 v284]
        have hv284_lvl : v284.toNat / 2 < s.core.lvl.length := by rw [hlvl_len]; omega
        have hld_v293 := s7_load_lvl_nat hc1 hv284_lvl (by omega) hm1
        m7_ld hld_v293
        let v293 := s.core.lvl[v284.toNat / 2]'hv284_lvl
        let InvCopy : Nat → Tup Val [i32, i32, i64] → Mem 64 → Prop := fun meas xs m_c =>
          ∃ k st ws_k, xs.1.toNat ≤ xs.2.1.toNat ∧
            xs.2.2.1 = BitVec.ofNat 64 k ∧ 2 ≤ k ∧ k ≤ s.core.tmp_len ∧
            meas = s.core.tmp_len - k ∧
            st.core = { s.core with tmp := s.core.tmp } ∧
            st.scratch = { s.scratch with wsort := ws_k } ∧
            ws_k.length = 2 * c.max_vars ∧
            m7Slice ws_k 1 k = m7Slice s.core.tmp 1 k ∧
            (∀ p, 1 ≤ p → p < k →
              xs.1.toNat ≤ (s.core.lvl[(ws_k[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ∧
              (s.core.lvl[(ws_k[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ xs.2.1.toNat) ∧
            (FullMem c st ⋆ R) m_c
        refine wp_loop_group InvCopy ?_ ?_
        · intro J294 meas xs m_c hIH ⟨k, st_c, ws_k, hmn_mx, hxs3, hk2, hkN, hmeas, hst_c,
            hst_s, hlen_wk, hsl_wk, hminmax_k, hm_c⟩
          rw [Blocks.get_here]
          m7_lets
          m7_jnz
          refine ⟨fun hlt_b => ?_, fun hge_b => ?_⟩
          · have hk_lt : k < s.core.tmp_len := by
              have h := s7_ult64_true hlt_b
              rw [hxs3, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h
              rwa [Nat.mod_eq_of_lt hN64, Nat.mod_eq_of_lt (by omega)] at h
            have hkt : k < s.core.tmp.length := by rw [htmp_len]; omega
            have hbdk := hbd k (by omega) hk_lt
            rw [List.getElem?_eq_getElem (l := s.core.tmp) (i := k) hkt, Option.getD_some]
              at hbdk
            m7_lets
            rw [hxs3]
            have hld_v300 := s7_load_tmp_nat hst_c hkt (by omega) hm_c
            m7_ld hld_v300
            m7_lets
            have hkw : k < ws_k.length := by rw [hlen_wk]; omega
            obtain ⟨st_c', hst_c', hst_s', hok_c, hm_c0⟩ := s7_store_wsort_nat (i := k)
              (s.core.tmp[k]'hkt) hst_c hst_s hkw (by omega) hm_c
            m7_st m_c1, hm_c' := And.intro hok_c hm_c0
            m7_lets
            let v300 := s.core.tmp[k]'hkt
            have hv300_bd : v300.toNat < 2 * c.max_vars := hbdk
            rw [s7_var_idx64 v300]
            have hv300_lvl : v300.toNat / 2 < s.core.lvl.length := by rw [hlvl_len]; omega
            have hld_v308 := s7_load_lvl_nat hst_c' hv300_lvl (by omega) hm_c'
            m7_ld hld_v308
            let v308 := s.core.lvl[v300.toNat / 2]'hv300_lvl
            let Pj309 : Tup Val [i32] → Mem 64 → Prop := fun mn m309 =>
              m309 = m_c1 ∧
              mn.1.toNat ≤ v308.toNat ∧
              (∀ p, 1 ≤ p → p < k →
                mn.1.toNat ≤ (s.core.lvl[(ws_k[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) ∧
              mn.1.toNat ≤ xs.2.1.toNat
            refine wp_join_group Pj309 ?_ ?_
            · intro J309 mn m309 ⟨hm_eq, hmn_lx, hmn_pre, hmn_mx'⟩
              subst hm_eq
              rw [Blocks.get_here]
              let Pj311 : Tup Val [i32] → Mem 64 → Prop := fun mx m311 =>
                m311 = m309 ∧
                v308.toNat ≤ mx.1.toNat ∧
                (∀ p, 1 ≤ p → p < k →
                  (s.core.lvl[(ws_k[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ mx.1.toNat) ∧
                mn.1.toNat ≤ mx.1.toNat
              refine wp_join_group Pj311 ?_ ?_
              · intro J311 mx m311 ⟨hm_eq2, hlx_mx, hmx_pre, hmn_mx''⟩
                subst hm_eq2
                rw [Blocks.get_here]
                m7_lets
                have hstep := m7_copy_step_inv htmp_len hlvl_len hlen_wk hk2 hk_lt htl
                  hsl_wk (by rw [List.getElem?_eq_getElem (l := s.core.tmp) (i := k) hkt,
                    Option.getD_some]; exact hbdk) rfl hmn_lx hlx_mx hmn_pre hmx_pre
                have hk1_bv : BitVec.ofNat 64 k + (1 : BitVec 64) = BitVec.ofNat 64 (k + 1) :=
                  s7_add1_bv64 (by omega)
                rw [hk1_bv]
                refine hIH (s.core.tmp_len - (k + 1)) (mn.1, mx.1, BitVec.ofNat 64 (k + 1), ())
                  _ (by omega) ⟨k + 1, st_c', ws_k.set k v300, hmn_mx'', rfl, by omega,
                    by omega, rfl, hst_c', hst_s', hstep.1, hstep.2.1, hstep.2.2, hm_c'⟩
              · intro J311 hExit311
                m7_lets
                m7_jnz
                refine ⟨fun hgt_mx => ?_, fun hle_mx => ?_⟩
                · have hlt_mx : xs.2.1.toNat < v308.toNat := s7_ult32_true hgt_mx
                  exact hExit311 (v308, ()) _ ⟨rfl, Nat.le_refl _, fun p hp1 hp2 =>
                    Nat.le_trans (hminmax_k p hp1 hp2).2 (Nat.le_of_lt hlt_mx),
                    Nat.le_trans hmn_mx' (Nat.le_of_lt hlt_mx)⟩
                · have hle_mx' : v308.toNat ≤ xs.2.1.toNat := s7_ult32_false hle_mx
                  exact hExit311 (xs.2.1, ()) _ ⟨rfl, hle_mx', fun p hp1 hp2 =>
                    (hminmax_k p hp1 hp2).2, hmn_mx'⟩
            · intro J309 hExit309
              m7_lets
              m7_jnz
              refine ⟨fun hlt_mn => ?_, fun hge_mn => ?_⟩
              · have hlt_mn' : v308.toNat < xs.1.toNat := s7_ult32_true hlt_mn
                exact hExit309 (v308, ()) _ ⟨rfl, Nat.le_refl _, fun p hp1 hp2 =>
                  Nat.le_trans (Nat.le_of_lt hlt_mn') (hminmax_k p hp1 hp2).1,
                  Nat.le_trans (Nat.le_of_lt hlt_mn') hmn_mx⟩
              · have hge_mn' : xs.1.toNat ≤ v308.toNat := s7_ult32_false hge_mn
                exact hExit309 (xs.1, ()) _ ⟨rfl, hge_mn', fun p hp1 hp2 =>
                  (hminmax_k p hp1 hp2).1, hmn_mx⟩
          · have hk_ge : s.core.tmp_len ≤ k := by
              have h := s7_ult64_false hge_b
              rw [hxs3, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h
              rwa [Nat.mod_eq_of_lt hN64, Nat.mod_eq_of_lt (by omega)] at h
            have hk_eq : k = s.core.tmp_len := by omega
            subst hk_eq
            exact s7_sort_tail_wp hlenOk htl hbd hQ hNgt32 hmn_mx hst_c hst_s hlen_wk hsl_wk
              hminmax_k hm_c
        · intro J295 hExit295
          have hinv0 := m7_copy_init_inv htmp_len hlvl_len hws_len (by omega) htl
            (hbd 1 (Nat.le_refl 1) (by omega))
          apply hExit295 (s.core.tmp_len - 2) (v293, v293, BitVec.ofNat 64 2, ()) m1
          refine ⟨2, st1, s.scratch.wsort.set 1 v284, Nat.le_refl _, rfl, Nat.le_refl 2,
            by omega, rfl, hc1, hs1', hinv0.1, hinv0.2.1, hinv0.2.2, hm1⟩

end LeanQbe.T.Examples.Kissat.Proof.Minimize
