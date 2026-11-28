/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Compact.Spec
public import LeanQbe.T.Examples.Kissat.Src.Compact
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Compact.Inv
import LeanQbe.T.Examples.Kissat.Proof.Lib.ContractLemmas
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Canonical WP Proofs for Heuristic Compaction (`Proof.Compact.WpHeur`)

Proves `Func.wp` against `Proof.Compact.Spec` for:
9. `full_compact_sift_q` (`fullCompactSiftQSpec`)
10. `full_compact_vmtf` (`fullCompactVmtfSpec`)
11. `full_compact_sift_h` (`fullCompactSiftHSpec`)
12. `full_compact_heap` (`fullCompactHeapSpec`)
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Compact

open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Compact
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Compact.Spec
open Kraken.Bedrock2.Test
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics

local macro "cmp_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

private theorem addr64_bv_eq (base idx : BitVec 64) :
    base + idx * 8#64 = base + BitVec.ofNat 64 (8 * idx.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

private theorem addr32_bv_eq (base idx : BitVec 64) :
    base + idx * 4#64 = base + BitVec.ofNat 64 (4 * idx.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

@[local c0_load] private theorem c0_load_arr64_bv
    (base idx : BitVec 64) (arr : List (BitVec 64)) (m : Mem 64) (P : Mem 64 → Prop)
    (hlt : idx.toNat < arr.length) (hm : (array64 base arr ⋆ P) m) :
    loadVal m i64 (base + idx * 8#64) = some (arr[idx.toNat]'hlt) := by
  rw [addr64_bv_eq]
  exact loadVal_array64 hlt hm

@[local c0_load] private theorem c0_load_arr32_bv
    (base idx : BitVec 64) (arr : List (BitVec 32)) (m : Mem 64) (P : Mem 64 → Prop)
    (hlt : idx.toNat < arr.length) (hm : (array (t := i32) base arr ⋆ P) m) :
    loadVal m i32 (base + idx * 4#64) = some (arr[idx.toNat]'hlt) := by
  rw [addr32_bv_eq]
  exact loadVal_array (by decide) hlt hm

@[local c0_store] private theorem c0_store_arr32_bv
    (base idx : BitVec 64) (v : BitVec 32) (arr : List (BitVec 32))
    (m : Mem 64) (P : Mem 64 → Prop)
    (hlt : idx.toNat < arr.length) (hm : (array (t := i32) base arr ⋆ P) m) :
    storeOk m i32 (base + idx * 4#64) ∧
      (array (t := i32) base (arr.set idx.toNat v) ⋆ P)
        (storeMem m i32 (base + idx * 4#64) v) := by
  rw [addr32_bv_eq]
  exact store_array (t := i32) v (by decide) hlt hm

private theorem bv32_swap_perm {α : Type} {ws ws0 : List α} {n root ch : Nat}
    (hr : root < n) (hc : ch < n) (hlen : ws.length = ws0.length)
    (hws_len : n ≤ ws0.length)
    (hhi : ∀ k, n ≤ k → ws[k]? = ws0[k]?)
    (hlo : ∀ k, k < n → ∃ j, j < n ∧ ws[k]? = ws0[j]?) :
    let vr := ws[root]'(by omega)
    let vc := ws[ch]'(by omega)
    let ws' := (ws.set root vc).set ch vr
    ws'.length = ws0.length ∧
    (∀ k, n ≤ k → ws'[k]? = ws0[k]?) ∧
    (∀ k, k < n → ∃ j, j < n ∧ ws'[k]? = ws0[j]?) := by
  intro vr vc ws'
  refine ⟨by simp [ws', hlen], fun k hk => ?_, fun k hk => ?_⟩
  · dsimp only [ws']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    exact hhi k hk
  · dsimp only [ws']
    by_cases hkc : k = ch
    · subst hkc
      rw [List.getElem?_set_self (by simp [hlen]; omega)]
      obtain ⟨j, hj, hj_eq⟩ := hlo root hr
      refine ⟨j, hj, ?_⟩
      rw [← hj_eq, List.getElem?_eq_getElem (by omega)]
    · rw [List.getElem?_set_ne (Ne.symm hkc)]
      by_cases hkr : k = root
      · subst hkr
        rw [List.getElem?_set_self (by omega)]
        obtain ⟨j, hj, hj_eq⟩ := hlo ch hc
        refine ⟨j, hj, ?_⟩
        rw [← hj_eq, List.getElem?_eq_getElem (by omega)]
      · rw [List.getElem?_set_ne (Ne.symm hkr)]
        exact hlo k hk

private theorem bv32_set_lo_pres {α : Type} {ws ws0 : List α} {n dst : Nat} {v : α}
    (hd : dst < n) (hn : n ≤ ws.length) (hv : ∃ j, j < n ∧ some v = ws0[j]?)
    (hlen : ws.length = ws0.length)
    (hhi : ∀ k, n ≤ k → ws[k]? = ws0[k]?)
    (hlo : ∀ k, k < n → ∃ j, j < n ∧ ws[k]? = ws0[j]?) :
    (ws.set dst v).length = ws0.length ∧
    (∀ k, n ≤ k → (ws.set dst v)[k]? = ws0[k]?) ∧
    (∀ k, k < n → ∃ j, j < n ∧ (ws.set dst v)[k]? = ws0[j]?) := by
  refine ⟨by simp [hlen], fun k hk => ?_, fun k hk => ?_⟩
  · rw [List.getElem?_set_ne (by omega)]; exact hhi k hk
  · by_cases hkd : k = dst
    · subst hkd
      rw [List.getElem?_set_self (by omega)]; exact hv
    · rw [List.getElem?_set_ne (Ne.symm hkd)]; exact hlo k hk

public section

/-! ## 1. `full_compact_sift_q` -/

/-- Canonical WP proof for `full_compact_sift_q`. -/
theorem full_compact_sift_q_wp (Γ : Env) :
    ∀ a m Q X, compactSiftQSpec a m Q X →
      Func.wp Γ full_compact_sift_q_body a m Q X := by
  rintro ⟨qs_ptr, ws_ptr, start, n, ⟨⟩⟩ m Q X hs
  obtain ⟨⟨qs, ws⟩, R, ⟨hst_lt, hn_le, hn_bd, hq_lt⟩, hm, hQ⟩ := FnContract.elim hs
  have hst_ws : start.toNat < ws.length := by omega
  unfold Func.wp full_compact_sift_q_body
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64])
    (fun (root_end, ()) m_end =>
      root_end.toNat < n.toNat ∧
      ∃ ws_e : List (BitVec 32), ws_e.length = ws.length ∧
        (∀ k, n.toNat ≤ k → ws_e[k]? = ws[k]?) ∧
        (∀ k, k < n.toNat → ∃ j, j < n.toNat ∧ ws_e[k]? = ws[j]?) ∧
        (array (t := i32) qs_ptr qs ⋆ array (t := i32) ws_ptr ws_e ⋆ R) m_end)
    (fun _ ⟨_root_end, ⟨⟩⟩ m_end ⟨_hr_lt_e, ws_e, hlen_e, hhi_e, hlo_e, hm_e⟩ => by
      c0_hsteps
      exact hQ () ws_e m_end ⟨hlen_e, hhi_e, hlo_e⟩ hm_e)
    (fun Jbrk hJbrk => by
      refine wp_loop_inv
        (fun (root, ()) mL =>
          root.toNat < n.toNat ∧
          ∃ wsL : List (BitVec 32), wsL.length = ws.length ∧
            (∀ k, n.toNat ≤ k → wsL[k]? = ws[k]?) ∧
            (∀ k, k < n.toNat → ∃ j, j < n.toNat ∧ wsL[k]? = ws[j]?) ∧
            (array (t := i32) qs_ptr qs ⋆ array (t := i32) ws_ptr wsL ⋆ R) mL)
        (fun (root, ()) _ => n.toNat - root.toNat)
        (fun J hLoop => ?_) ?_
      · c0_hsteps; exact hLoop (start, ()) m ⟨hst_lt, ws, rfl, fun _ _ => rfl,
          fun k hk => ⟨k, hk, rfl⟩, hm⟩
      · rintro J ⟨root, ⟨⟩⟩ mL ⟨hr_lt, wsL, hlenL, hhiL, hloL, hmL⟩ hLoop
        have hch_eq : ((root <<< (1 : Nat)) + (1 : BitVec 64)).toNat = 2 * root.toNat + 1 := by
          bv_omega
        c0_hsteps_nogrp <;> try exact absurd (by assumption : true = false) (by decide)
        c0_hsplit
        · have hch_ge : n.toNat ≤ ((root <<< (1 : Nat)) + (1 : BitVec 64)).toNat := by c0_bound
          c0_hsteps; exact hJbrk (root, ()) mL ⟨hr_lt, wsL, hlenL, hhiL, hloL, hmL⟩
        · have hch_lt : 2 * root.toNat + 1 < n.toNat := by
            have h1 : ((root <<< (1 : Nat)) + (1 : BitVec 64)).toNat < n.toNat := by c0_bound
            omega
          have hch_ws : 2 * root.toNat + 1 < wsL.length := by omega
          have hch_ws1 : (root <<< (1 : Nat) + (1 : BitVec 64)).toNat < wsL.length := by
            rw [hch_eq]; exact hch_ws
          have hcv_qs : (wsL[2 * root.toNat + 1]'hch_ws).toNat < qs.length := by
            obtain ⟨j, hj, hj_eq⟩ := hloL (2 * root.toNat + 1) hch_lt
            have hget := hq_lt j hj
            rw [List.getElem?_eq_getElem hch_ws] at hj_eq
            rw [← hj_eq, Option.getD_some] at hget; exact hget
          have hcv_qs_z :
              ((wsL[(root <<< (1 : Nat) + (1 : BitVec 64)).toNat]'hch_ws1).setWidth 64).toNat <
                qs.length := by
            rw [zext_toNat _ (by decide)]; simp only [hch_eq]; exact hcv_qs
          c0_hsteps_nogrp
          refine wp_join_group (ts := [i64, i32, i32])
            (fun (ch', cv', _, ()) m1 =>
              ch'.toNat < n.toNat ∧ root.toNat < ch'.toNat ∧ wsL[ch'.toNat]? = some cv' ∧
              m1 = mL)
            (fun _ ⟨ch', cv', cs', ⟨⟩⟩ m1 ⟨hch'_lt, hch'_gt, hcv'_eq, hm1_eq⟩ => by
              subst m1
              have hch'_ws : ch'.toNat < wsL.length := by omega
              have hcv'_val : cv' = wsL[ch'.toNat]'hch'_ws :=
                (Option.some.inj ((List.getElem?_eq_getElem hch'_ws).symm.trans hcv'_eq)).symm
              have hr_ws : root.toNat < wsL.length := by omega
              have hrv_qs_z : ((wsL[root.toNat]'hr_ws).setWidth 64).toNat < qs.length := by
                obtain ⟨j, hj, hj_eq⟩ := hloL root.toNat hr_lt
                have hget := hq_lt j hj
                rw [List.getElem?_eq_getElem hr_ws] at hj_eq
                rw [← hj_eq, Option.getD_some] at hget
                rw [zext_toNat _ (by decide)]; exact hget
              c0_hsplit
              · c0_hsteps; exact hJbrk (root, ()) mL ⟨hr_lt, wsL, hlenL, hhiL, hloL, hmL⟩
              · c0_hsteps
                obtain ⟨hlen', hhi', hlo'⟩ :=
                  bv32_swap_perm hr_lt hch'_lt hlenL hn_le hhiL hloL
                let ws_nxt := (wsL.set root.toNat cv').set ch'.toNat (wsL[root.toNat]'hr_ws)
                have hws'_eq : ws_nxt =
                    (wsL.set root.toNat (wsL[ch'.toNat]'hch'_ws)).set ch'.toNat
                      (wsL[root.toNat]'hr_ws) := by
                  simp only [ws_nxt, hcv'_val]
                refine hLoop (ch', ()) _ (by dsimp only; omega)
                  ⟨hch'_lt, ws_nxt, hws'_eq ▸ hlen', hws'_eq ▸ hhi', hws'_eq ▸ hlo', ?_⟩
                · try rw [Std.ExtHashMap.sep_emp] at *
                  exact sep_ac ‹(array (t := i32) ws_ptr ws_nxt ⋆ _) _›)
            (fun Jc hJc => by
              c0_hsplit
              · have hch2_lt : 2 * root.toNat + 2 < n.toNat := by
                  have h1 : (((root <<< (1 : Nat)) + (1 : BitVec 64)) +
                      (1 : BitVec 64)).toNat < n.toNat := by c0_bound
                  have h2 : (((root <<< (1 : Nat)) + (1 : BitVec 64)) +
                      (1 : BitVec 64)).toNat = 2 * root.toNat + 2 := by bv_omega
                  omega
                have hch2_ws : 2 * root.toNat + 2 < wsL.length := by omega
                have hch2_eq : (((root <<< (1 : Nat)) + (1 : BitVec 64)) +
                    (1 : BitVec 64)).toNat = 2 * root.toNat + 2 := by bv_omega
                have hch2_ws1 : (((root <<< (1 : Nat)) + (1 : BitVec 64)) +
                    (1 : BitVec 64)).toNat < wsL.length := by
                  rw [hch2_eq]; exact hch2_ws
                have hsv_qs : (wsL[2 * root.toNat + 2]'hch2_ws).toNat < qs.length := by
                  obtain ⟨j, hj, hj_eq⟩ := hloL (2 * root.toNat + 2) hch2_lt
                  have hget := hq_lt j hj
                  rw [List.getElem?_eq_getElem hch2_ws] at hj_eq
                  rw [← hj_eq, Option.getD_some] at hget; exact hget
                have hsv_qs_z :
                    ((wsL[(((root <<< (1 : Nat)) + (1 : BitVec 64)) +
                      (1 : BitVec 64)).toNat]'hch2_ws1).setWidth 64).toNat < qs.length := by
                  rw [zext_toNat _ (by decide)]; simp only [hch2_eq]; exact hsv_qs
                c0_hsteps <;> first
                  | exact hJc _ mL ⟨by rw [hch2_eq]; exact hch2_lt,
                      by rw [hch2_eq]; omega,
                      by simp only [hch2_eq, List.getElem?_eq_getElem hch2_ws], rfl⟩
                  | exact hJc _ mL ⟨by rw [hch_eq]; exact hch_lt,
                      by rw [hch_eq]; omega,
                      by simp only [hch_eq, List.getElem?_eq_getElem hch_ws], rfl⟩
              · c0_hsteps; exact hJc _ mL ⟨by rw [hch_eq]; exact hch_lt,
                  by rw [hch_eq]; omega,
                  by simp only [hch_eq, List.getElem?_eq_getElem hch_ws], rfl⟩))

/-! ## 2. `full_compact_vmtf` -/

/-- Canonical WP proof for `full_compact_vmtf`. -/
theorem full_compact_vmtf_wp (Γ : Env)
    (hsift : Γ.Has "full_compact_sift_q" compactSiftQSpec) :
    ∀ a m Q X, compactHeurSpec a m Q X →
      Func.wp Γ full_compact_vmtf_body a m Q X := by
  rintro ⟨h, ncv, ⟨⟩⟩ m Q X hs
  obtain ⟨c, s, ⟨⟩, R, rfl, hlen, hncv_le, hm, hQ0⟩ := FullContract.elim hs
  let hQ : ∀ sc' m',
      let s' : FullState := { s with scratch := sc' }
      s'.LengthsOk c → FullExtScratchPres s s' → sc'.work_stk1 = s.scratch.work_stk1 →
      sc'.work_stk2 = s.scratch.work_stk2 → (FullMem c s' ⋆ R) m' → Q () m' :=
    fun sc' m' hlen' hpres' hws1' hws2' hm' =>
      hQ0 () { s with scratch := sc' } m' hlen' ⟨rfl, hpres', hws1', hws2'⟩ hm'
  have hcv_le := hlen.core_ok.cur_vars_le
  have hmax_lt : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  have hncv_lt64 : ncv.toNat < 2 ^ 64 := by omega
  have hncv_lt62 : ncv.toNat < 2 ^ 62 := by omega
  have hncv_le_2m : ncv.toNat ≤ 2 * c.max_vars := by omega
  have hqs_len := hlen.scratch_ok.q_stamp_len
  have hqp_len := hlen.scratch_ok.q_prev_len
  have hqn_len := hlen.scratch_ok.q_next_len
  have hws_len := hlen.scratch_ok.wsort_len
  have hws1_len := hlen.scratch_ok.work_stk1_len
  have hws2_len := hlen.scratch_ok.work_stk2_len
  unfold Func.wp full_compact_vmtf_body
  c0_hsplit
  · c0_hsteps
    let sc' : FullScratch :=
      { s.scratch with
        q_first := 0xFFFFFFFF#64, q_last := 0xFFFFFFFF#64,
        q_search_idx := 0xFFFFFFFF#64, q_search_stamp := 0#64, q_cur_stamp := 0#64 }
    exact hQ sc' _ ⟨hlen.core_ok, { hlen.scratch_ok with }⟩
      ⟨rfl, rfl⟩ rfl rfl (by assumption)
  · have hncv_pos : 0 < ncv.toNat := by
      have hne : ncv ≠ 0#64 := by c0_bound
      exact Nat.pos_of_ne_zero (fun h0 => hne (BitVec.eq_of_toNat_eq (by simpa using h0)))
    c0_hsteps_nogrp
    refine wp_loop_inv
      (fun (i, ()) m1 =>
        i.toNat ≤ ncv.toNat ∧
        ∃ ws1 : List (BitVec 32), ws1.length = 2 * c.max_vars ∧
          (∀ k, k < i.toNat → ws1[k]? = some (BitVec.ofNat 32 k)) ∧
          (FullMem c { s with scratch := { s.scratch with wsort := ws1 } } ⋆ R) m1)
      (fun (i, ()) _ => ncv.toNat - i.toNat)
      (fun J1 hLoop1 => ?_) ?_
    · c0_hsteps; exact hLoop1 (0#64, ()) m ⟨Nat.zero_le _, s.scratch.wsort, hws_len,
        fun _ hk => by simp at hk, hm⟩
    · rintro J1 ⟨i, ⟨⟩⟩ m1 ⟨hi_le, ws1, hlen1, hi_eq1, hm1⟩ hLoop1
      c0_hsplit
      · have hi_lt : i.toNat < ncv.toNat := by c0_bound
        have hi_cm : i.toNat < 2 * c.max_vars := by omega
        have hi1_eq : (i + (1 : BitVec 64)).toNat = i.toNat + 1 := cmp_bv64_add1 (by omega)
        have hi32 : i.setWidth 32 = BitVec.ofNat 32 i.toNat := BitVec.eq_of_toNat_eq (by
          rw [BitVec.toNat_setWidth, bv32_ofNat_toNat (by omega), Nat.mod_eq_of_lt (by omega)])
        c0_hsteps
        refine hLoop1 (i + (1 : BitVec 64), ()) _ (by dsimp only; rw [hi1_eq]; omega) ?_
        refine ⟨by rw [hi1_eq]; omega, ws1.set i.toNat (i.setWidth 32),
          by rw [List.length_set, hlen1], fun k hk => ?_, by assumption⟩
        rw [hi1_eq] at hk
        by_cases hki : k = i.toNat
        · subst hki; rw [List.getElem?_set_self (by omega), hi32]
        · rw [List.getElem?_set_ne (Ne.symm hki)]; exact hi_eq1 k (by omega)
      · have hi_eq : i.toNat = ncv.toNat := by c0_bound
        rw [hi_eq] at hi_eq1
        clear hLoop1 J1
        let s1 : FullState := { s with scratch := { s.scratch with wsort := ws1 } }
        have hws1_perm : ∀ k, k < ncv.toNat → ∃ j, j < ncv.toNat ∧ ws1[k]? =
            some (BitVec.ofNat 32 j) := fun k hk => ⟨k, hk, hi_eq1 k hk⟩
        refine wp_join_group (ts := [])
          (fun () m2 =>
            ∃ ws2 : List (BitVec 32), ws2.length = 2 * c.max_vars ∧
              (∀ k, k < ncv.toNat → ∃ j, j < ncv.toNat ∧ ws2[k]? =
                some (BitVec.ofNat 32 j)) ∧
              (FullMem c { s with scratch := { s.scratch with wsort := ws2 } } ⋆ R) m2)
          (fun _ ⟨⟩ m2 ⟨ws2, hlen2, hperm2, hm2⟩ => by
            have hws2_bd : ∀ k, k < ncv.toNat → (ws2[k]?.getD 0#32).toNat < ncv.toNat := by
              intro k hk
              obtain ⟨j, hj, hj_eq⟩ := hperm2 k hk
              rw [hj_eq, Option.getD_some, bv32_ofNat_toNat (by omega)]
              exact hj
            refine wp_loop_inv
              (fun (idx, ()) m3 =>
                idx.toNat ≤ ncv.toNat ∧
                ∃ qp3 qn3 qs3 : List (BitVec 32),
                  qp3.length = c.max_vars ∧ qn3.length = c.max_vars ∧ qs3.length = c.max_vars ∧
                  (FullMem c { s with scratch := { s.scratch with
                    wsort := ws2, q_prev := qp3, q_next := qn3, q_stamp := qs3 } } ⋆ R) m3)
              (fun (idx, ()) _ => ncv.toNat - idx.toNat)
              (fun J3 hLoop3 => ?_) ?_
            · c0_hsteps; exact hLoop3 (0#64, ()) m2
                ⟨Nat.zero_le _, s.scratch.q_prev, s.scratch.q_next, s.scratch.q_stamp,
                 hqp_len, hqn_len, hqs_len, hm2⟩
            · rintro J3 ⟨idx, ⟨⟩⟩ m3 ⟨hi3_le, qp3, qn3, qs3, hqp3, hqn3, hqs3, hm3⟩ hLoop3
              c0_hsplit
              · have hi3_lt : idx.toNat < ncv.toNat := by c0_bound
                have hi3_ws : idx.toNat < ws2.length := by omega
                have hv_lt : (ws2[idx.toNat]'hi3_ws).toNat < ncv.toNat := by
                  simpa [List.getElem?_eq_getElem hi3_ws] using hws2_bd idx.toNat hi3_lt
                have hv_cm : (ws2[idx.toNat]'hi3_ws).toNat < c.max_vars := by omega
                have hidx1_eq : (idx + (1 : BitVec 64)).toNat = idx.toNat + 1 :=
                  cmp_bv64_add1 (by omega)
                have hidx_pos : idx = 0#64 ∨ idx ≠ 0#64 := Decidable.em _
                c0_hsteps_nogrp
                refine wp_join_group (ts := [i32])
                  (fun (_qp_v, ()) mP => mP = m3 ∧
                    (FullMem c { s with scratch := { s.scratch with
                      wsort := ws2, q_prev := qp3, q_next := qn3, q_stamp := qs3 } } ⋆ R) mP)
                  (fun _ ⟨qp_v, ⟨⟩⟩ mP ⟨hmP_eq, hmP⟩ => by
                    subst mP
                    have hzext : ∀ x : BitVec 32, (x.setWidth 64).toNat = x.toNat :=
                      fun x => zext_toNat x (by decide)
                    c0_hsteps_nogrp
                    simp only [hzext] at *
                    refine wp_join_group (ts := [i32])
                      (fun (_qn_v, ()) mN =>
                        (FullMem c { s with scratch := { s.scratch with
                          wsort := ws2, q_prev := qp3.set (ws2[idx.toNat]'hi3_ws).toNat qp_v,
                          q_next := qn3, q_stamp := qs3 } } ⋆ R) mN)
                      (fun _ ⟨qn_v, ⟨⟩⟩ mN hmN => by
                        c0_hsteps
                        refine hLoop3 (idx + (1 : BitVec 64), ()) _
                          (by
                            dsimp only; rw [hidx1_eq]
                            exact Nat.sub_lt_sub_left hi3_lt (Nat.le_refl _))
                          ⟨by rw [hidx1_eq]; exact hi3_lt,
                           qp3.set (ws2[idx.toNat]'hi3_ws).toNat qp_v,
                           qn3.set (ws2[idx.toNat]'hi3_ws).toNat qn_v,
                           qs3.set (ws2[idx.toNat]'hi3_ws).toNat
                             ((idx + (1 : BitVec 64)).setWidth 32),
                           by rw [List.length_set]; exact hqp3,
                           by rw [List.length_set]; exact hqn3,
                           by rw [List.length_set]; exact hqs3,
                           ?_⟩
                        try rw [Std.ExtHashMap.sep_emp] at *
                        exact sep_ac ‹(FullMem c _ ⋆ _) _›)
                      (fun Jqn hJqn => by
                        c0_hsplit
                        · c0_hsteps
                          exact hJqn (0xFFFFFFFF#32, ()) _ (by assumption)
                        · have hidx_add_lt : (idx + 1#64).toNat < ws2.length := by
                            have h1 : (idx + 1#64).toNat < ncv.toNat := by c0_bound
                            exact Nat.lt_of_lt_of_le h1 (by rw [hlen2]; exact hncv_le_2m)
                          c0_hsteps
                          exact hJqn (_, ()) _ (by assumption)))
                  (fun Jqp hJqp => by
                    c0_hsplit
                    · c0_hsteps; exact hJqp (0xFFFFFFFF#32, ()) m3 ⟨rfl, hm3⟩
                    · have hidx_sub_lt : (idx - 1#64).toNat < ws2.length := by
                        have hne : idx ≠ 0#64 := by c0_bound
                        have hpos : 0 < idx.toNat :=
                          Nat.pos_of_ne_zero
                            (fun h0 => hne (BitVec.eq_of_toNat_eq (by simpa using h0)))
                        have hsub1 : (idx - 1#64).toNat = idx.toNat - 1 := by bv_omega
                        rw [hsub1, hlen2]
                        exact Nat.lt_of_lt_of_le (Nat.sub_lt hpos Nat.zero_lt_one)
                          (Nat.le_trans (Nat.le_of_lt hi3_lt)
                            (Nat.le_trans hncv_le (Nat.le_trans hcv_le
                              (Nat.le_mul_of_pos_left _ Nat.zero_lt_two))))
                      c0_hsteps; exact hJqp (_, ()) m3 ⟨rfl, hm3⟩)
              · have h0_lt : 0 < ws2.length := by omega
                have hlast_lt : (ncv - (1 : BitVec 64)).toNat < ws2.length := by bv_omega
                c0_hsteps
                let sc_end : FullScratch :=
                  { s.scratch with
                    wsort := ws2, q_prev := qp3, q_next := qn3, q_stamp := qs3,
                    q_first := (ws2[0]'h0_lt).setWidth 64,
                    q_last := (ws2[(ncv - (1 : BitVec 64)).toNat]'hlast_lt).setWidth 64,
                    q_search_idx := (ws2[(ncv - (1 : BitVec 64)).toNat]'hlast_lt).setWidth 64,
                    q_search_stamp := ncv, q_cur_stamp := ncv }
                exact hQ sc_end _
                  ⟨hlen.core_ok, { hlen.scratch_ok with
                    wsort_len := hlen2, q_prev_len := hqp3,
                    q_next_len := hqn3, q_stamp_len := hqs3 }⟩
                  ⟨rfl, rfl⟩ rfl rfl (by assumption))
          (fun Jsft hJsft => by
            c0_hsplit
            · have hncv_gt1 : 1 < ncv.toNat := by c0_bound
              have hst_bd : (ncv >>> (1 : Nat)).toNat ≤ ncv.toNat := by bv_omega
              c0_hsteps_nogrp
              refine wp_loop_inv
                (fun (st, ()) mA =>
                  st.toNat ≤ ncv.toNat ∧
                  ∃ wsA : List (BitVec 32), wsA.length = 2 * c.max_vars ∧
                    (∀ k, k < ncv.toNat → ∃ j, j < ncv.toNat ∧ wsA[k]? =
                      some (BitVec.ofNat 32 j)) ∧
                    (FullMem c { s with scratch := { s.scratch with wsort := wsA } } ⋆ R) mA)
                (fun (st, ()) _ => st.toNat)
                (fun JA hLoopA => ?_) ?_
              · c0_hsteps
                exact hLoopA (ncv >>> (1 : Nat), ()) m1 ⟨hst_bd, ws1, hlen1, hws1_perm, hm1⟩
              · rintro JA ⟨st, ⟨⟩⟩ mA ⟨hst_le, wsA, hlenA, hpermA, hmA⟩ hLoopA
                c0_hsplit
                · have hst_pos : 0 < st.toNat := by c0_bound
                  have hst1_lt : (st - (1 : BitVec 64)).toNat < ncv.toNat := by bv_omega
                  have hst1_dec : (st - (1 : BitVec 64)).toNat < st.toNat := by bv_omega
                  c0_hsteps_nogrp; cmp_call hsift
                  have hncv_le_wsA : ncv.toNat ≤ wsA.length := hlenA.symm ▸ hncv_le_2m
                  refine FnContract.intro (s.scratch.q_stamp, wsA) (CompactVmtfRest c s ⋆ R)
                    ⟨hst1_lt, hncv_le_wsA, hncv_lt62, ?_⟩
                    (focus_vmtf_arrays
                      (s := { s with scratch := { s.scratch with wsort := wsA } }) hmA)
                    (fun _ wsA' mA' ⟨hlenA', hhiA', hloA'⟩ hmA' => ?_)
                  · intro k hk
                    obtain ⟨j, hj, hj_eq⟩ := hpermA k hk
                    rw [hj_eq, Option.getD_some, bv32_ofNat_toNat (by omega)]
                    omega
                  · c0_hsteps
                    refine hLoopA (st - (1 : BitVec 64), ()) mA' hst1_dec
                      ⟨by omega, wsA', hlenA'.trans hlenA, fun k hk => ?_,
                       unfocus_vmtf_arrays hmA'⟩
                    obtain ⟨q, hq, hq_eq⟩ := hloA' k hk
                    obtain ⟨j, hj, hj_eq⟩ := hpermA q hq
                    exact ⟨j, hj, hq_eq.trans hj_eq⟩
                · refine wp_loop_inv
                    (fun (ed, ()) mB =>
                      ed.toNat < ncv.toNat ∧
                      ∃ wsB : List (BitVec 32), wsB.length = 2 * c.max_vars ∧
                        (∀ k, k < ncv.toNat → ∃ j, j < ncv.toNat ∧ wsB[k]? =
                          some (BitVec.ofNat 32 j)) ∧
                        (FullMem c { s with scratch := { s.scratch with wsort := wsB } } ⋆ R) mB)
                    (fun (ed, ()) _ => ed.toNat)
                    (fun JB hLoopB => ?_) ?_
                  · have hed_lt : (ncv - (1 : BitVec 64)).toNat < ncv.toNat := by bv_omega
                    c0_hsteps; exact hLoopB (ncv - (1 : BitVec 64), ()) mA
                      ⟨hed_lt, wsA, hlenA, hpermA, hmA⟩
                  · rintro JB ⟨ed, ⟨⟩⟩ mB ⟨hed_lt, wsB, hlenB, hpermB, hmB⟩ hLoopB
                    c0_hsplit
                    · have hed_pos : 0 < ed.toNat := by c0_bound
                      have hed_ws : ed.toNat < wsB.length := by omega
                      have h0_ws : 0 < wsB.length := by omega
                      have hed1_dec : (ed - (1 : BitVec 64)).toNat < ed.toNat := by bv_omega
                      c0_hsteps
                      let v0 := wsB[0]'h0_ws
                      let ved := wsB[ed.toNat]'hed_ws
                      let wsB1 := (wsB.set 0 ved).set ed.toNat v0
                      have hwsB1_len : wsB1.length = 2 * c.max_vars := by simp [wsB1, hlenB]
                      have hwsB1_perm : ∀ k, k < ncv.toNat → ∃ j, j < ncv.toNat ∧ wsB1[k]? =
                          some (BitVec.ofNat 32 j) := by
                        intro k hk
                        dsimp only [wsB1]
                        by_cases hke : k = ed.toNat
                        · subst hke
                          rw [List.getElem?_set_self (by simp [hlenB]; omega)]
                          obtain ⟨j, hj, hj_eq⟩ := hpermB 0 hncv_pos
                          refine ⟨j, hj, ?_⟩
                          rw [← hj_eq, List.getElem?_eq_getElem h0_ws]
                        · rw [List.getElem?_set_ne (Ne.symm hke)]
                          by_cases hk0 : k = 0
                          · subst hk0
                            rw [List.getElem?_set_self h0_ws]
                            obtain ⟨j, hj, hj_eq⟩ := hpermB ed.toNat hed_lt
                            refine ⟨j, hj, ?_⟩
                            rw [← hj_eq, List.getElem?_eq_getElem hed_ws]
                          · rw [List.getElem?_set_ne (Ne.symm hk0)]
                            exact hpermB k hk
                      c0_hsteps_nogrp; cmp_call hsift
                      have hed_le_wsB1 : ed.toNat ≤ wsB1.length :=
                        Nat.le_of_lt (hwsB1_len.symm ▸ Nat.lt_of_lt_of_le hed_lt hncv_le_2m)
                      have hed_lt62 : ed.toNat < 2 ^ 62 := Nat.lt_trans hed_lt hncv_lt62
                      refine FnContract.intro (s.scratch.q_stamp, wsB1) (CompactVmtfRest c s ⋆ R)
                        ⟨hed_pos, hed_le_wsB1, hed_lt62, ?_⟩
                        (focus_vmtf_arrays
                          (s := { s with scratch := { s.scratch with wsort := wsB1 } })
                          (by assumption))
                        (fun _ wsB' mB' ⟨hlenB', hhiB', hloB'⟩ hmB' => ?_)
                      · intro k hk
                        obtain ⟨j, hj, hj_eq⟩ := hwsB1_perm k (Nat.lt_trans hk hed_lt)
                        rw [hj_eq, Option.getD_some, bv32_ofNat_toNat (by omega)]
                        exact Nat.lt_of_lt_of_le hj (Nat.le_trans hncv_le (hqs_len ▸ hcv_le))
                      · c0_hsteps
                        refine hLoopB (ed - (1 : BitVec 64), ()) mB' hed1_dec
                          ⟨Nat.lt_trans hed1_dec hed_lt, wsB',
                           hlenB'.trans hwsB1_len, fun k hk => ?_,
                           unfocus_vmtf_arrays
                             (s := { s with scratch := { s.scratch with wsort := wsB1 } })
                             hmB'⟩
                        by_cases hkl : k < ed.toNat
                        · obtain ⟨q, hq, hq_eq⟩ := hloB' k hkl
                          obtain ⟨j, hj, hj_eq⟩ := hwsB1_perm q (Nat.lt_trans hq hed_lt)
                          exact ⟨j, hj, hq_eq.trans hj_eq⟩
                        · rw [hhiB' k (Nat.not_lt.mp hkl)]
                          exact hwsB1_perm k hk
                    · c0_hsteps; exact hJsft () mB ⟨wsB, hlenB, hpermB, hmB⟩
            · c0_hsteps; exact hJsft () m1 ⟨ws1, hlen1, hws1_perm, hm1⟩)

/-! ## 3. `full_compact_sift_h` & `full_compact_heap` -/

/-- Canonical WP proof for `full_compact_sift_h`. -/
theorem full_compact_sift_h_wp (Γ : Env) :
    ∀ a m Q X, compactSiftHSpec a m Q X →
      Func.wp Γ full_compact_sift_h_body a m Q X := by
  rintro ⟨sc_ptr, hp_ptr, ps_ptr, start, n, ⟨⟩⟩ m Q X hs
  obtain ⟨⟨sc, hp, ps⟩, R, ⟨hst_lt, hn_hp, hn_ps, hn_bd, hsc_lt⟩, hm, hQ⟩ := FnContract.elim hs
  dsimp only at hst_lt hn_hp hn_ps hn_bd hsc_lt hm
  have hst_hp : start.toNat < hp.length := by omega
  have hrvs_sc : (hp[start.toNat]'hst_hp).toNat < sc.length := by
    simpa [List.getElem?_eq_getElem hst_hp] using (hsc_lt start.toNat hst_lt).1
  have hrvs_ps : (hp[start.toNat]'hst_hp).toNat < ps.length := by
    simpa [List.getElem?_eq_getElem hst_hp] using (hsc_lt start.toNat hst_lt).2
  unfold Func.wp full_compact_sift_h_body
  dsimp only
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64])
    (fun (root_end, ()) m_end =>
      root_end.toNat < n.toNat ∧
      ∃ hp_e ps_e : List (BitVec 32), hp_e.length = hp.length ∧ ps_e.length = ps.length ∧
        (∀ k, n.toNat ≤ k → hp_e[k]? = hp[k]?) ∧
        (∀ k, k < n.toNat → ∃ j, j < n.toNat ∧ hp_e[k]? = hp[j]?) ∧
        (array64 sc_ptr sc ⋆ array (t := i32) hp_ptr hp_e ⋆ array (t := i32) ps_ptr ps_e ⋆ R) m_end)
    ?_ ?_
  · rintro _ ⟨root_end, ⟨⟩⟩ m_end
        ⟨hr_lt_e, hp_e, ps_e, hlen_hp_e, hlen_ps_e, hhi_e, hlo_e, hm_e⟩
    have hr_hp : root_end.toNat < hp_e.length := by omega
    have hrv_ps_e : (hp[start.toNat]'hst_hp).toNat < ps_e.length := by
      rw [hlen_ps_e]; exact hrvs_ps
    c0_hsteps
    try clear hm_e
    have hrv_mem : ∃ j, j < n.toNat ∧ some (hp[start.toNat]'hst_hp) = hp[j]? :=
      ⟨start.toNat, hst_lt, (List.getElem?_eq_getElem hst_hp).symm⟩
    obtain ⟨hlen', hhi', hlo'⟩ :=
      bv32_set_lo_pres hr_lt_e (by omega) hrv_mem hlen_hp_e hhi_e hlo_e
    refine hQ () (hp_e.set root_end.toNat (hp[start.toNat]'hst_hp),
      ps_e.set (hp[start.toNat]'hst_hp).toNat (root_end.setWidth 32)) _
      ⟨hlen', by rw [List.length_set, hlen_ps_e], hhi', hlo'⟩ ?_
    dsimp only [compactSiftHSpec]
    have hsw (x : BitVec 32) : (BitVec.setWidth 64 x).toNat = x.toNat := by
      simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans x.isLt
        (by decide : 2 ^ 32 < 2 ^ 64))]
    try simp only [hsw] at *
    exact sep_ac (by assumption)
  · intro Jbrk hJbrk
    refine wp_loop_inv (ts := [i64])
        (fun (root, ()) mL =>
          root.toNat < n.toNat ∧
          ∃ hpL psL : List (BitVec 32), hpL.length = hp.length ∧ psL.length = ps.length ∧
            (∀ k, n.toNat ≤ k → hpL[k]? = hp[k]?) ∧
            (∀ k, k < n.toNat → ∃ j, j < n.toNat ∧ hpL[k]? = hp[j]?) ∧
            (array64 sc_ptr sc ⋆ array (t := i32) hp_ptr hpL ⋆ array (t := i32) ps_ptr psL ⋆ R) mL)
        (fun (root, ()) _ => n.toNat - root.toNat)
        (fun J hLoop => ?_) ?_
    · c0_hsteps; exact hLoop (start, ()) m ⟨hst_lt, hp, ps, rfl, rfl,
        fun _ _ => rfl, fun k hk => ⟨k, hk, rfl⟩, hm⟩
    ·
        rintro J ⟨root, ⟨⟩⟩ mL ⟨hr_lt, hpL, psL, hlen_hpL, hlen_psL, hhiL, hloL, hmL⟩ hLoop
        have hch_eq : ((root <<< (1 : Nat)) + (1 : BitVec 64)).toNat = 2 * root.toNat + 1 := by
          bv_omega
        c0_hsteps_nogrp <;> try exact absurd (by assumption : true = false) (by decide)
        c0_hsplit
        · have hch_ge : n.toNat ≤ ((root <<< (1 : Nat)) + (1 : BitVec 64)).toNat := by c0_bound
          c0_hsteps; exact hJbrk (root, ()) mL
            ⟨hr_lt, hpL, psL, hlen_hpL, hlen_psL, hhiL, hloL, hmL⟩
        · have hch_lt : 2 * root.toNat + 1 < n.toNat := by
            have h1 : ((root <<< (1 : Nat)) + (1 : BitVec 64)).toNat < n.toNat := by c0_bound
            omega
          have hch_ws : 2 * root.toNat + 1 < hpL.length := by omega
          have hch_ws1 : (root <<< (1 : Nat) + (1 : BitVec 64)).toNat < hpL.length := by
            rw [hch_eq]; exact hch_ws
          have hcv_bd : (hpL[2 * root.toNat + 1]'hch_ws).toNat < sc.length ∧
              (hpL[2 * root.toNat + 1]'hch_ws).toNat < psL.length := by
            obtain ⟨j, hj, hj_eq⟩ := hloL (2 * root.toNat + 1) hch_lt
            have hb := hsc_lt j hj
            rw [List.getElem?_eq_getElem hch_ws] at hj_eq
            rw [← hj_eq, Option.getD_some] at hb
            exact ⟨hb.1, by omega⟩
          have hcv_bd_z :
              ((hpL[(root <<< (1 : Nat) + (1 : BitVec 64)).toNat]'hch_ws1).setWidth 64).toNat <
                sc.length := by
            rw [zext_toNat _ (by decide)]; simp only [hch_eq]; exact hcv_bd.1
          c0_hsteps_nogrp
          refine wp_join_group (ts := [i64, i32, i64])
            (fun (ch', cv', _, ()) m1 =>
              ch'.toNat < n.toNat ∧ root.toNat < ch'.toNat ∧ hpL[ch'.toNat]? = some cv' ∧
              (cv'.toNat < psL.length) ∧ m1 = mL)
            (fun _ ⟨ch', cv', cs', ⟨⟩⟩ m1 ⟨hch'_lt, hch'_gt, hcv'_eq, hcv'_ps, hm1_eq⟩ => by
              subst m1
              have hch'_hp : ch'.toNat < hpL.length := by omega
              have hcv'_val : cv' = hpL[ch'.toNat]'hch'_hp :=
                (Option.some.inj ((List.getElem?_eq_getElem hch'_hp).symm.trans hcv'_eq)).symm
              have hrv_hp : root.toNat < hpL.length := by omega
              c0_hsplit
              · c0_hsteps; exact hJbrk (root, ()) mL
                  ⟨hr_lt, hpL, psL, hlen_hpL, hlen_psL, hhiL, hloL, hmL⟩
              · c0_hsteps
                have hcv_mem : ∃ j, j < n.toNat ∧ some cv' = hp[j]? := by
                  obtain ⟨j, hj, hj_eq⟩ := hloL ch'.toNat hch'_lt
                  refine ⟨j, hj, ?_⟩
                  rw [hcv'_val, ← hj_eq, List.getElem?_eq_getElem hch'_hp]
                obtain ⟨hlen', hhi', hlo'⟩ :=
                  bv32_set_lo_pres hr_lt (by omega) hcv_mem hlen_hpL hhiL hloL
                refine hLoop (ch', ()) _ (by dsimp only; omega)
                  ⟨hch'_lt, hpL.set root.toNat cv', psL.set cv'.toNat (root.setWidth 32),
                   hlen', by rw [List.length_set, hlen_psL], hhi', hlo', ?_⟩
                · try rw [Std.ExtHashMap.sep_emp] at *
                  exact sep_ac ‹(array (t := i32) ps_ptr
                    (psL.set cv'.toNat (root.setWidth 32)) ⋆ _) _›)
            (fun Jc hJc => by
              c0_hsplit
              · have hch2_lt : 2 * root.toNat + 2 < n.toNat := by
                  have h1 : (((root <<< (1 : Nat)) + (1 : BitVec 64)) +
                      (1 : BitVec 64)).toNat < n.toNat := by c0_bound
                  have h2 : (((root <<< (1 : Nat)) + (1 : BitVec 64)) +
                      (1 : BitVec 64)).toNat = 2 * root.toNat + 2 := by bv_omega
                  omega
                have hch2_hp : 2 * root.toNat + 2 < hpL.length := by omega
                have hch2_eq : (((root <<< (1 : Nat)) + (1 : BitVec 64)) +
                    (1 : BitVec 64)).toNat = 2 * root.toNat + 2 := by bv_omega
                have hch2_hp1 : (((root <<< (1 : Nat)) + (1 : BitVec 64)) +
                    (1 : BitVec 64)).toNat < hpL.length := by
                  rw [hch2_eq]; exact hch2_hp
                have hsv_bd : (hpL[2 * root.toNat + 2]'hch2_hp).toNat < sc.length ∧
                    (hpL[2 * root.toNat + 2]'hch2_hp).toNat < psL.length := by
                  obtain ⟨j, hj, hj_eq⟩ := hloL (2 * root.toNat + 2) hch2_lt
                  have hb := hsc_lt j hj
                  rw [List.getElem?_eq_getElem hch2_hp] at hj_eq
                  rw [← hj_eq, Option.getD_some] at hb
                  exact ⟨hb.1, by omega⟩
                have hsv_bd_z :
                    ((hpL[(((root <<< (1 : Nat)) + (1 : BitVec 64)) +
                      (1 : BitVec 64)).toNat]'hch2_hp1).setWidth 64).toNat < sc.length := by
                  rw [zext_toNat _ (by decide)]; simp only [hch2_eq]; exact hsv_bd.1
                c0_hsteps <;> first
                  | exact hJc _ mL ⟨by rw [hch2_eq]; exact hch2_lt,
                      by rw [hch2_eq]; omega,
                      by simp only [hch2_eq, List.getElem?_eq_getElem hch2_hp],
                      by simpa only [hch2_eq] using hsv_bd.2, rfl⟩
                  | exact hJc _ mL ⟨by rw [hch_eq]; exact hch_lt,
                      by rw [hch_eq]; omega,
                      by simp only [hch_eq, List.getElem?_eq_getElem hch_ws],
                      by simpa only [hch_eq] using hcv_bd.2, rfl⟩
              · c0_hsteps; exact hJc _ mL ⟨by rw [hch_eq]; exact hch_lt,
                  by rw [hch_eq]; omega,
                  by simp only [hch_eq, List.getElem?_eq_getElem hch_ws],
                  by simpa only [hch_eq] using hcv_bd.2, rfl⟩)

/-- Canonical WP proof for `full_compact_heap`. -/
theorem full_compact_heap_wp (Γ : Env)
    (hsift : Γ.Has "full_compact_sift_h" compactSiftHSpec) :
    ∀ a m Q X, compactHeurSpec a m Q X →
      Func.wp Γ full_compact_heap_body a m Q X := by
  rintro ⟨h, ncv, ⟨⟩⟩ m Q X hs
  obtain ⟨c, s, ⟨⟩, R, rfl, hlen, hncv_le, hm, hQ0⟩ := FullContract.elim hs
  let hQ : ∀ sc' m',
      let s' : FullState := { s with scratch := sc' }
      s'.LengthsOk c → FullExtScratchPres s s' → sc'.work_stk1 = s.scratch.work_stk1 →
      sc'.work_stk2 = s.scratch.work_stk2 → (FullMem c s' ⋆ R) m' → Q () m' :=
    fun sc' m' hlen' hpres' hws1' hws2' hm' =>
      hQ0 () { s with scratch := sc' } m' hlen' ⟨rfl, hpres', hws1', hws2'⟩ hm'
  have hcv_le := hlen.core_ok.cur_vars_le
  have hmax_lt : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  have hncv_lt64 : ncv.toNat < 2 ^ 64 := by omega
  have hncv_lt62 : ncv.toNat < 2 ^ 62 := by omega
  have hncv_le_2m : ncv.toNat ≤ 2 * c.max_vars := by omega
  have hsc_len := hlen.scratch_ok.score_len
  have hhp_len := hlen.scratch_ok.heap_len_arr
  have hps_len := hlen.scratch_ok.pos_len
  unfold Func.wp full_compact_heap_body
  c0_hsteps_nogrp
  refine wp_loop_inv
    (fun (v, ()) m1 =>
      v.toNat ≤ ncv.toNat ∧
      ∃ hp1 ps1 : List (BitVec 32), hp1.length = c.max_vars ∧ ps1.length = c.max_vars ∧
        (∀ k, k < v.toNat → hp1[k]? = some (BitVec.ofNat 32 k)) ∧
        (FullMem c { s with scratch := { s.scratch with heap := hp1, pos := ps1 } } ⋆ R) m1)
    (fun (v, ()) _ => ncv.toNat - v.toNat)
    (fun J1 hLoop1 => ?_) ?_
  · c0_hsteps; exact hLoop1 (0#64, ()) m ⟨Nat.zero_le _, s.scratch.heap, s.scratch.pos,
      hhp_len, hps_len, fun _ hk => by simp at hk, hm⟩
  · rintro J1 ⟨v, ⟨⟩⟩ m1 ⟨hv_le, hp1, ps1, hhp1, hps1, hinv1, hm1⟩ hLoop1
    c0_hsplit
    · have hv_lt : v.toNat < ncv.toNat := by c0_bound
      have hv_cm : v.toNat < c.max_vars := by omega
      have hv1_eq : (v + (1 : BitVec 64)).toNat = v.toNat + 1 := cmp_bv64_add1 (by omega)
      have hv32 : v.setWidth 32 = BitVec.ofNat 32 v.toNat := BitVec.eq_of_toNat_eq (by
        rw [BitVec.toNat_setWidth, bv32_ofNat_toNat (by omega), Nat.mod_eq_of_lt (by omega)])
      c0_hsteps
      refine hLoop1 (v + (1 : BitVec 64), ()) _ (by dsimp only; rw [hv1_eq]; omega) ?_
      refine ⟨by rw [hv1_eq]; omega, hp1.set v.toNat (v.setWidth 32),
        ps1.set v.toNat (v.setWidth 32), by rw [List.length_set, hhp1],
        by rw [List.length_set, hps1], fun k hk => ?_, by assumption⟩
      rw [hv1_eq] at hk
      by_cases hkv : k = v.toNat
      · subst hkv; rw [List.getElem?_set_self (by omega), hv32]
      · rw [List.getElem?_set_ne (Ne.symm hkv)]; exact hinv1 k (by omega)
    · have hv_eq : v.toNat = ncv.toNat := by c0_bound
      rw [hv_eq] at hinv1
      clear hLoop1 J1
      let s1 : FullState :=
        { s with scratch := { s.scratch with heap_len := ncv.toNat, heap := hp1, pos := ps1 } }
      have hperm1 : ∀ k, k < ncv.toNat → ∃ j, j < ncv.toNat ∧ hp1[k]? =
          some (BitVec.ofNat 32 j) := fun k hk => ⟨k, hk, hinv1 k hk⟩
      have hcv_max2 : ncv.toNat ≤ c.max_vars := Nat.le_trans hncv_le hcv_le
      have hncv_64 : BitVec.ofNat 64 ncv.toNat = ncv := bv_ofNat_toNat_eq ncv
      have hncv_lt62 : ncv.toNat < 2 ^ 62 := by omega
      c0_hsteps_nogrp
      refine wp_join_group (ts := [])
        (fun () m_end =>
          ∃ hp2 ps2 : List (BitVec 32), hp2.length = c.max_vars ∧ ps2.length = c.max_vars ∧
            (FullMem c { s with scratch := { s.scratch with
              heap_len := ncv.toNat, heap := hp2, pos := ps2 } } ⋆ R) m_end)
        (fun _ ⟨⟩ m_end ⟨hp2, ps2, hhp2, hps2, hm_end⟩ => by
          c0_hsteps
          exact hQ { s.scratch with heap_len := ncv.toNat, heap := hp2, pos := ps2 } m_end
            ⟨hlen.core_ok, { hlen.scratch_ok with heap_len_arr := hhp2, pos_len := hps2 }⟩
            ⟨rfl, rfl⟩ rfl rfl hm_end)
        (fun Jend hJend => by
          c0_hsplit
          · have hncv_gt1 : 1 < ncv.toNat := by c0_bound
            have hst_bd : (ncv >>> (1 : Nat)).toNat ≤ ncv.toNat := by bv_omega
            c0_hsteps_nogrp
            refine wp_loop_inv
              (fun (st, ()) m2 =>
                st.toNat ≤ ncv.toNat ∧
                ∃ hp2 ps2 : List (BitVec 32), hp2.length = c.max_vars ∧ ps2.length = c.max_vars ∧
                  (∀ k, k < ncv.toNat → ∃ j, j < ncv.toNat ∧ hp2[k]? =
                    some (BitVec.ofNat 32 j)) ∧
                  (FullMem c { s with scratch := { s.scratch with
                    heap_len := ncv.toNat, heap := hp2, pos := ps2 } } ⋆ R) m2)
              (fun (st, ()) _ => st.toNat)
              (fun J2 hLoop2 => ?_) ?_
            · c0_hsteps; exact hLoop2 (ncv >>> (1 : Nat), ()) _
                ⟨hst_bd, hp1, ps1, hhp1, hps1, hperm1, by assumption⟩
            · rintro J2 ⟨st, ⟨⟩⟩ m2 ⟨hst_le, hp2, ps2, hhp2, hps2, hperm2, hm2⟩ hLoop2
              c0_hsplit
              · have hst_pos : 0 < st.toNat := by c0_bound
                have hst1_lt : (st - (1 : BitVec 64)).toNat < ncv.toNat := by bv_omega
                have hst1_dec : (st - (1 : BitVec 64)).toNat < st.toNat := by bv_omega
                have hncv_hp2 : ncv.toNat ≤ hp2.length := hhp2.symm ▸ hcv_max2
                have hncv_ps2 : ncv.toNat ≤ ps2.length := hps2.symm ▸ hcv_max2
                let s2 : FullState :=
                  { s with scratch := { s.scratch with
                      heap_len := ncv.toNat, heap := hp2, pos := ps2 } }
                c0_hsteps_nogrp; cmp_call hsift
                refine FnContract.intro (s.scratch.score, hp2, ps2) (CompactHeapRest c s2 ⋆ R)
                  ⟨hst1_lt, hncv_hp2, hncv_ps2, hncv_lt62, ?_⟩
                  (focus_heap_arrays (s := s2) hm2)
                  (fun _ (hp2', ps2') m2' ⟨hhp2', hps2', hhi2', hlo2'⟩ hm2' => ?_)
                · intro k hk
                  obtain ⟨j, hj, hj_eq⟩ := hperm2 k hk
                  have hj_lt_max : j < c.max_vars := Nat.lt_of_lt_of_le hj hcv_max2
                  have hj_lt32 : j < 2 ^ 32 :=
                    Nat.lt_trans hj_lt_max (Nat.lt_trans hmax_lt (by decide))
                  rw [hj_eq, Option.getD_some, bv32_ofNat_toNat hj_lt32]
                  exact ⟨hsc_len.symm ▸ hj_lt_max, hps2.symm ▸ hj_lt_max⟩
                · c0_hsteps
                  refine hLoop2 (st - (1 : BitVec 64), ()) m2' hst1_dec
                    ⟨Nat.le_of_lt hst1_lt, hp2', ps2', hhp2'.trans hhp2, hps2'.trans hps2,
                     fun k hk => ?_, unfocus_heap_arrays (s := s2) hm2'⟩
                  obtain ⟨q, hq, hq_eq⟩ := hlo2' k hk
                  obtain ⟨j, hj, hj_eq⟩ := hperm2 q hq
                  exact ⟨j, hj, hq_eq.trans hj_eq⟩
              · c0_hsteps; exact hJend () m2 ⟨hp2, ps2, hhp2, hps2, hm2⟩
          · c0_hsteps
            exact hJend () _ ⟨hp1, ps1, hhp1, hps1, by assumption⟩)

end

end LeanQbe.T.Examples.Kissat.Proof.Compact
