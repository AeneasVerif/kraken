/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Transitive.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Transitive.UnrollInv
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1

/-!
# Soundness Proof for `full_trans_sort_m6` (`Proof.Transitive.WpSort`)

Proves `full_trans_sort_m6_wp` (`Src.Transitive.full_trans_sort_m6_body`) against
canonical `Spec.fullTransSortM6Spec` (Knuth-gap Shell sort over `work_stk1[0..<n)`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Transitive

open Std.Sat
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Transitive.Spec
open LeanQbe.T.Examples.Kissat.Src.Transitive
open Kraken.Bedrock2.Test
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics

private theorem knuth_gap_step_lt {g n : Nat} (hg : 0 < g) (hlt : g < n / 3) :
    3 * g + 1 ≤ n ∧ n / 3 - (3 * g + 1) < n / 3 - g := by
  omega

/-- `full_trans_sort_m6` satisfies canonical `Spec.fullTransSortM6Spec`. -/
theorem full_trans_sort_m6_wp (Γ : Env) :
    ∀ a m Q X, fullTransSortM6Spec a m Q X →
      Func.wp Γ full_trans_sort_m6_body a m Q X := by
  rintro ⟨h, n, ⟨⟩⟩ m0 Q X ⟨c, F0, s, R, rfl, hsp, hn_le, hok0, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcl0 := hsp.1.lengths.core_ok; have hscl0 := hsp.1.lengths.scratch_ok
  have hcv_le : s.core.cur_vars ≤ c.max_vars := hcl0.cur_vars_le
  have hsc_len : s.scratch.score.length = c.max_vars := hscl0.score_len
  have hqs_len : s.scratch.q_stamp.length = c.max_vars := hscl0.q_stamp_len
  unfold Func.wp full_trans_sort_m6_body
  c0_hsteps_nogrp
  · exact hQ s.scratch.work_stk1 m0 hscl0.work_stk1_len hsp hok0 hm0
  have hn_gt1 : 1 < n.toNat := by bv_omega
  have hn3_eq : (n / 3#64).toNat = n.toNat / 3 := by
    rw [BitVec.toNat_udiv]; rfl
  refine wp_loop_inv (ts := [i64])
    (fun (gap, ()) mk => 0 < gap.toNat ∧ gap.toNat ≤ n.toNat ∧ mk = m0)
    (fun (gap, ()) _ => n.toNat / 3 - gap.toNat)
    (fun Jk hJk => by
      c0_hsteps
      exact hJk (1#64, ()) m0 ⟨by decide, by bv_omega, rfl⟩)
    (fun Jk ⟨gap0, ⟨⟩⟩ mk ⟨hg0_pos, hg0_le, hmk_eq⟩ ihk => ?_)
  subst hmk_eq
  c0_hsplit
  · have hlt_n3 : gap0.toNat < n.toNat / 3 := by
      have h1 : gap0.toNat < (n / 3#64).toNat := by c0_bound
      omega
    have hstep := knuth_gap_step_lt hg0_pos hlt_n3
    have h3g1_eq : (3#64 * gap0 + 1#64).toNat = 3 * gap0.toNat + 1 := by bv_omega
    c0_hsteps
    exact ihk (3#64 * gap0 + 1#64, ()) mk (by dsimp only; omega)
      ⟨by rw [h3g1_eq]; omega, by rw [h3g1_eq]; exact hstep.1, rfl⟩
  · refine wp_loop_inv (ts := [i64])
      (fun (gap, ()) mg => ∃ ws1 : List (BitVec 32),
        gap.toNat ≤ n.toNat ∧ ws1.length = 2 * c.max_vars ∧
        (∀ i < n.toNat, (ws1[i]?.getD 0#32).toNat < s.core.cur_vars) ∧
        (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1 } } ⋆ R) mg)
      (fun (gap, ()) _ => gap.toNat)
      (fun Jg hJg => by
        c0_hsteps
        exact hJg (gap0, ()) mk ⟨s.scratch.work_stk1, hg0_le, hscl0.work_stk1_len, hok0, hm0⟩)
      (fun Jg ⟨gap, ⟨⟩⟩ mg ⟨wsg, hgap_le, hwsg_len, hokg, hmg⟩ ihg => ?_)
    c0_hsplit
    · have hgap_pos : 0 < gap.toNat := by c0_bound
      c0_hsteps_nogrp
      refine wp_loop_inv (ts := [i64])
        (fun (si, ()) msi => ∃ wss : List (BitVec 32),
          gap.toNat ≤ si.toNat ∧ si.toNat ≤ n.toNat ∧ wss.length = 2 * c.max_vars ∧
          (∀ i < n.toNat, (wss[i]?.getD 0#32).toNat < s.core.cur_vars) ∧
          (FullMem c { s with scratch := { s.scratch with work_stk1 := wss } } ⋆ R) msi)
        (fun (si, ()) _ => n.toNat - si.toNat)
        (fun Ji hJi => by
          c0_hsteps
          exact hJi (gap, ()) mg ⟨wsg, Nat.le_refl _, hgap_le, hwsg_len, hokg, hmg⟩)
        (fun Ji ⟨si, ⟨⟩⟩ msi ⟨wss, hgsi, hsi_le, hwss_len, hoks, hmsi⟩ ihi => ?_)
      c0_hsplit
      · have hsi_lt : si.toNat < n.toNat := by c0_bound
        have hsi_len : si.toNat < wss.length := by omega
        let v := wss[si.toNat]'hsi_len
        have hv_lt : v.toNat < s.core.cur_vars := by
          have h := hoks si.toNat hsi_lt
          rwa [List.getElem?_eq_getElem hsi_len, Option.getD_some] at h
        have hv64 : (v.setWidth 64).toNat = v.toNat := tr_bv32_setWidth64 v
        have hv_sc : (v.setWidth 64).toNat <
            ({ s with scratch := { s.scratch with work_stk1 := wss } } :
              FullState).scratch.score.length := by
          dsimp only; rw [hv64, hsc_len]; omega
        have hv_qs : (v.setWidth 64).toNat <
            ({ s with scratch := { s.scratch with work_stk1 := wss } } :
              FullState).scratch.q_stamp.length := by
          dsimp only; rw [hv64, hqs_len]; omega
        c0_hsteps_nogrp
        refine wp_join_group (ts := [i64]) (fun _ mk => mk = msi) ?_
          (fun Jk hJk => by
            c0_hsplit
            · c0_hsteps; exact hJk _ msi rfl
            · c0_hsteps; exact hJk _ msi rfl)
        rintro _ ⟨kv, ⟨⟩⟩ mk rfl
        c0_hsteps_nogrp
        refine wp_loop_break_group (brkTs := [i64]) (lpTs := [i64])
          (BrkPost := fun (sj_b, ()) mb => ∃ wsb : List (BitVec 32),
            sj_b.toNat < n.toNat ∧ wsb.length = 2 * c.max_vars ∧
            (∀ i < n.toNat, (wsb[i]?.getD 0#32).toNat < s.core.cur_vars) ∧
            (FullMem c { s with scratch := { s.scratch with work_stk1 := wsb } } ⋆ R) mb)
          (Inv := fun rem (sj, ()) mj => ∃ wsj : List (BitVec 32),
            sj.toNat < n.toNat ∧ rem = sj.toNat ∧ wsj.length = 2 * c.max_vars ∧
            (∀ i < n.toNat, (wsj[i]?.getD 0#32).toNat < s.core.cur_vars) ∧
            (FullMem c { s with scratch := { s.scratch with work_stk1 := wsj } } ⋆ R) mj)
          ?_ ?_ ?_
        · rintro _ ⟨sj_b, ⟨⟩⟩ mb ⟨wsb, hsjb_lt, hwsb_len, hokb, hmb⟩
          have hsjb_len : sj_b.toNat < wsb.length := by omega
          have hsi1 : (si + 1#64).toNat = si.toNat + 1 := tr_bv64_add1 (by omega)
          c0_hsteps
          exact ihi (si + 1#64, ()) _ (by dsimp only; omega)
            ⟨wsb.set sj_b.toNat v, by rw [hsi1]; omega, by rw [hsi1]; omega,
             by simp [hwsb_len], tr_ws1_set_lt_bound hsjb_len hv_lt hokb, (by assumption)⟩
        · rintro B L rem ⟨sj, ⟨⟩⟩ mj hB hL ⟨wsj, hsj_lt, hrem, hwsj_len, hokj, hmj⟩
          c0_hsplit
          · have hsj_ge : gap.toNat ≤ sj.toNat := by c0_bound
            have hpj_eq : (sj - gap).toNat = sj.toNat - gap.toNat := by bv_omega
            have hpj_len : (sj - gap).toNat < wsj.length := by omega
            let pv := wsj[(sj - gap).toNat]'hpj_len
            have hpv_lt : pv.toNat < s.core.cur_vars := by
              have h := hokj (sj - gap).toNat (by omega)
              rwa [List.getElem?_eq_getElem hpj_len, Option.getD_some] at h
            have hpv64 : (pv.setWidth 64).toNat = pv.toNat := tr_bv32_setWidth64 pv
            have hpv_sc : (pv.setWidth 64).toNat <
                ({ s with scratch := { s.scratch with work_stk1 := wsj } } :
                  FullState).scratch.score.length := by
              dsimp only; rw [hpv64, hsc_len]; omega
            have hpv_qs : (pv.setWidth 64).toNat <
                ({ s with scratch := { s.scratch with work_stk1 := wsj } } :
                  FullState).scratch.q_stamp.length := by
              dsimp only; rw [hpv64, hqs_len]; omega
            c0_hsteps_nogrp
            refine wp_join_group (ts := [i64]) (fun _ mp => mp = mj) ?_
              (fun Jp hJp => by
                c0_hsplit
                · c0_hsteps; exact hJp _ mj rfl
                · c0_hsteps; exact hJp _ mj rfl)
            rintro _ ⟨kpv, ⟨⟩⟩ mp rfl
            c0_hsplit
            · c0_hsteps; exact hB (sj, ()) mp ⟨wsj, hsj_lt, hwsj_len, hokj, hmj⟩
            · refine wp_join_group (ts := []) (fun _ m_c => m_c = mp)
                (fun _ _ m_c heq => by
                  subst heq
                  have hsj_len : sj.toNat < wsj.length := by omega
                  c0_hsteps
                  exact hL (sj.toNat - gap.toNat) (sj - gap, ()) _ (by omega)
                    ⟨wsj.set sj.toNat pv, by rw [hpj_eq]; omega, by rw [hpj_eq],
                     by simp [hwsj_len], tr_ws1_set_lt_bound hsj_len hpv_lt hokj,
                     (by assumption)⟩)
                (fun Jc hJc => by
                  c0_hsplit
                  · c0_hsplit
                    · c0_hsteps; exact hB (sj, ()) mp ⟨wsj, hsj_lt, hwsj_len, hokj, hmj⟩
                    · c0_hsteps; exact hJc () mp rfl
                  · c0_hsteps; exact hJc () mp rfl)
          · c0_hsteps; exact hB (sj, ()) mj ⟨wsj, hsj_lt, hwsj_len, hokj, hmj⟩
        · intro B L hB hL; c0_hsteps
          exact hL si.toNat (si, ()) mk ⟨wss, hsi_lt, rfl, hwss_len, hoks, hmsi⟩
      · c0_hsteps
        have hdiv : (gap / 3#64).toNat = gap.toNat / 3 := by rw [BitVec.toNat_udiv]; rfl
        exact ihg (gap / 3#64, ()) msi (by dsimp only; rw [hdiv]; omega)
          ⟨wss, by rw [hdiv]; omega, hwss_len, hoks, hmsi⟩
    · c0_hsteps
      exact hQ wsg mg hwsg_len (tr_sparse_with_ws1 hsp hwsg_len) hokg hmg

end LeanQbe.T.Examples.Kissat.Proof.Transitive
