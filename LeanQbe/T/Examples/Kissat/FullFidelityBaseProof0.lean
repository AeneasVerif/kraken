/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityBase
public import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofBve0
public import LeanQbe.T.Examples.Kissat.FullM6SweepProofSpec
public import LeanQbe.T.Examples.Kissat.FullM6OrchAdaptersProof0
import all LeanQbe.T.Examples.Kissat.FullM8CoreParityProofBveK6c
import all LeanQbe.T.Examples.Kissat.FullM8CoreParityProofBveK6c0
import all LeanQbe.T.Examples.Kissat.FullM8WaveACoreProof0
import all LeanQbe.T.Examples.Kissat.FullM8SweepV2VarProof
import LeanQbe.T.Examples.Kissat.FullM6BcpS15Proof
import LeanQbe.T.Examples.Kissat.FullVivTopLemmas1
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.MemLemmas
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Purified `FullFidelityBase` Leaf `Func.wp` Proofs (`FullFidelityBaseProof0`)

Certifies `3` of the `5` newly authored purified C0 bodies exported by
`LeanQbe.T.Examples.Kissat.FullFidelityBase` (`XPost := False`, `std3`):
1. `full_bve_gates_fid_wp`: omits `D-11` syntactic XOR gate matcher (`gates.c:44-55`).
2. `full_vivify_tier_m6_hdr_fid_wp`: exact `vivify.c:1269` candidate-sort guard over `FullMem`.
3. `fid_sweep_vars_wp`: exact upstream `1x` Kitten ticks `(u64)k[K6H_TICKS]` (`sweep.c:1673`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityBase

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullDenseWatchHelpers
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullM6BveFwd
open LeanQbe.T.Examples.Kissat.FullM7BveGates
open LeanQbe.T.Examples.Kissat.FullM6BcpS15
open LeanQbe.T.Examples.Kissat.FullM6Sweep
open LeanQbe.T.Examples.Kissat.FullM6VivBackbone
open LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
open LeanQbe.T.Examples.Kissat.FullM8CoreParity
open LeanQbe.T.Examples.Kissat.FullM8SweepV2
open LeanQbe.T.Examples.Kissat.FullM8WaveACore
open Kraken.Bedrock2.Test

open scoped FullArenaTactics M8K6cTactics M6SweepTactics K6MemATactics K6PtrTactics

local macro "fid_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

/-! ## 1. `full_bve_gates_fid_wp` (Equivalence -> AND -> ITE -> K6, No `D-11` XOR) -/

/-- Parametric `Func.wp` proof for `full_bve_gates_fid`, certifying `m8BveGatesSpec`. -/
theorem full_bve_gates_fid_wp (Γ : Env)
    (hEquiv : ∀ a m Q X, m8BveFindEquivSpec a m Q X →
      Γ "full_bve_find_equiv_m8" [i64, i32, i32] [.bool] a m Q X)
    (hAnd : ∀ a m Q X, m8BveFindAndSpec a m Q X →
      Γ "full_bve_find_and_m8" [i64, i32, i32, i32] [.bool] a m Q X)
    (hIte : ∀ a m Q X, m8BveFindIteSpec a m Q X →
      Γ "full_bve_find_ite_m8" [i64, i32, i32, i32] [.bool] a m Q X)
    (hDefK6 : ∀ a m Q X, m8BveGatesSpec a m Q X →
      Γ "full_bve_def_k6_m8" [i64, i32, i32, i32] [] a m Q X) :
    ∀ a m Q X, m8BveGatesSpec a m Q X →
      Func.wp Γ full_bve_gates_fid_body a m Q X := by
  rintro ⟨h, v, np, nn, ⟨⟩⟩ m0 Q X hSpec
  obtain ⟨c, F0, F_cur, s0, R, rfl, hdw0, htmk0, hsc16384, hv_lt, hnp2001, hnn2001,
    hp_ok, hn_ok, hm0, hQ⟩ := m8BveGatesSpec_elim hSpec
  have hmx := c.hmaxv; have hsc := c.hscr; unfold dimacsBound at hmx hsc
  have hcv_le := hdw0.1.core_ok.cur_vars_le
  have hplnl := m8_pl_nl_eq v (by omega)
  unfold Func.wp full_bve_gates_fid_body
  c0_hsteps_nogrp
  refine wp_loop_group (ts := [i32])
    (fun rem0 (k, ()) mk => ∃ scr0 : List (BitVec 32),
      let s0k : FullState := { s0 with scratch := { s0.scratch with scratch_buf := scr0 } }
      scr0.length = c.scratch_cap ∧ k.toNat ≤ 130 ∧ rem0 = 130 - k.toNat ∧
      (∀ i < 4002, scr0[i]? = s0.scratch.scratch_buf[i]?) ∧ (FullMem c s0k ⋆ R) mk)
    ?_ ?_
  · rintro L0 rem0 ⟨k, ⟨⟩⟩ mk hL0 ⟨scr0, hsc0, hk_le, rfl, hkeep0, hmk⟩
    c0_hsplit
    · have hk_lt : k.toNat < 130 := hc
      have hidx : ((4002#32 + k).setWidth 64).toNat < scr0.length := by
        rw [hsc0, m6_zext32_toNat]; c0_bound
      have hk1 : (k + 1#32).toNat = k.toNat + 1 := by c0_bound
      c0_hsteps!
      exact hL0 (130 - (k + 1#32).toNat) (k + 1#32, ()) _ (by omega)
        ⟨scr0.set ((4002#32 + k).setWidth 64).toNat 0#32, by simp [hsc0], by omega, rfl,
         fun i hi => by
           rw [List.getElem?_set_ne (by rw [m6_zext32_toNat]; c0_bound)]; exact hkeep0 i hi, hm⟩
    · have hdw1 := m8_fullDenseInvW_scr hdw0 hsc0
      have htmk1 : TmkZero { s0 with scratch := { s0.scratch with scratch_buf := scr0 } } := htmk0
      have hp1 : ∀ i < np.toNat, FullBveEntryOkW F_cur
          { s0 with scratch := { s0.scratch with scratch_buf := scr0 } } (2 * v.toNat)
          (scr0[i]?.getD 0#32) := fun i hi => by
        rw [hkeep0 i (by omega)]; exact hp_ok i hi
      have hn1 : ∀ j < nn.toNat, FullBveEntryOkW F_cur
          { s0 with scratch := { s0.scratch with scratch_buf := scr0 } } (2 * v.toNat + 1)
          (scr0[2001 + j]?.getD 0#32) := fun j hj => by
        rw [hkeep0 (2001 + j) (by omega)]; exact hn_ok j hj
      c0_hsplit
      · c0_hsteps!
        exact hQ _ mk hdw1 htmk1 rfl rfl rfl (Nat.le_refl _)
          (fun i hi => hkeep0 i (by omega))
          (fun j hj => hkeep0 (2001 + j) (by omega)) hmk
      · clear hc
        c0_hsplit
        · c0_hsteps!
          exact hQ _ mk hdw1 htmk1 rfl rfl rfl (Nat.le_refl _)
            (fun i hi => hkeep0 i (by omega))
            (fun j hj => hkeep0 (2001 + j) (by omega)) hmk
        · clear hc
          fid_call hEquiv
          refine m8BveFindEquivSpec_intro rfl hdw1 hsc16384 hnp2001 hnn2001
            (fun i hi hbin => m8_k6c_entry_bin_bounds (hp1 i hi) hbin)
            (fun j hj hbin => m8_k6c_entry_bin_bounds (hn1 j hj) hbin)
            hmk ?_
          intro ok_e lm_e scr_e m_e _ hdw_e hsce_l hkeep_e hm_e
          have hk_e : ∀ i < 4002, scr_e[i]? = s0.scratch.scratch_buf[i]? := fun i hi =>
            (hkeep_e i (by omega) (Or.inl hi)).trans (hkeep0 i hi)
          have htmk_e : TmkZero
              { s0 with
                core := { s0.core with lit_mark := lm_e }
                scratch := { s0.scratch with scratch_buf := scr_e } } := htmk0
          c0_hsplit
          · c0_hsteps!
            exact hQ _ m_e hdw_e htmk_e rfl rfl rfl (Nat.le_refl _)
              (fun i hi => hk_e i (by omega))
              (fun j hj => hk_e (2001 + j) (by omega)) hm_e
          · clear hc
            c0_hsteps_nogrp
            have hpl_and1 : ((v <<< (1 : Nat)) &&& 1#32) = 0#32 :=
              BitVec.eq_of_toNat_eq (by
                rw [BitVec.toNat_and, hplnl.1, show (1#32 : BitVec 32).toNat = 1 from rfl,
                  Nat.and_one_is_mod, Nat.mul_mod_right]; rfl)
            have hnl_and1 : (((v <<< (1 : Nat)) ||| 1#32) &&& 1#32) ≠ 0#32 := fun h0 => by
              have h1 := congrArg BitVec.toNat h0
              rw [BitVec.toNat_and, hplnl.2, show (1#32 : BitVec 32).toNat = 1 from rfl,
                Nat.and_one_is_mod, show (0#32 : BitVec 32).toNat = 0 from rfl] at h1
              omega
            fid_call hAnd
            dsimp only [vals, Arg.val]
            refine m8BveFindAndSpec_intro rfl hdw_e hsc16384 hnp2001 hnn2001
              (fun i hi => by
                rw [show (v <<< OfNat.ofNat 1 : BitVec 32) = (v <<< (1 : Nat)) from rfl,
                  hpl_and1, ite_eq_right (by intro h; exact h rfl), Nat.zero_add, hplnl.1,
                  hk_e i (by omega)]
                exact hp_ok i hi)
              (fun j hj => by
                rw [show (v <<< OfNat.ofNat 1 : BitVec 32) = (v <<< (1 : Nat)) from rfl,
                  hpl_and1, ite_eq_right (by intro h; exact h rfl), BitVec.toNat_xor, hplnl.1,
                  show (1#32 : BitVec 32).toNat = 1 from rfl, m8_k6c_xor_two_mul,
                  hk_e (2001 + j) (by omega)]
                exact hn_ok j hj)
              hm_e ?_
            intro ok_ap lm_ap scr_ap m_ap _ hdw_ap hscap_l hkeep_ap hm_ap
            have hk_ap : ∀ i < 4002, scr_ap[i]? = s0.scratch.scratch_buf[i]? := fun i hi =>
              (hkeep_ap i (by omega) (Or.inl hi)).trans (hk_e i hi)
            have htmk_ap : TmkZero
                { s0 with
                  core := { s0.core with lit_mark := lm_ap }
                  scratch := { s0.scratch with scratch_buf := scr_ap } } := htmk0
            c0_hsplit
            · c0_hsteps!
              exact hQ _ m_ap hdw_ap htmk_ap rfl rfl rfl (Nat.le_refl _)
                (fun i hi => hk_ap i (by omega))
                (fun j hj => hk_ap (2001 + j) (by omega)) hm_ap
            · clear hc
              fid_call hAnd
              dsimp only [vals, Arg.val]
              refine m8BveFindAndSpec_intro rfl hdw_ap hsc16384 hnn2001 hnp2001
                (fun i hi => by
                  rw [show (v <<< OfNat.ofNat 1 ||| 1 : BitVec 32) =
                      ((v <<< (1 : Nat)) ||| 1#32) from rfl,
                    ite_eq_left hnl_and1, hplnl.2, hk_ap (2001 + i) (by omega)]
                  exact hn_ok i hi)
                (fun j hj => by
                  rw [show (v <<< OfNat.ofNat 1 ||| 1 : BitVec 32) =
                      ((v <<< (1 : Nat)) ||| 1#32) from rfl,
                    ite_eq_left hnl_and1, Nat.zero_add, BitVec.toNat_xor, hplnl.2,
                    show (1#32 : BitVec 32).toNat = 1 from rfl, m8_k6c_xor_two_mul_add1,
                    hk_ap j (by omega)]
                  exact hp_ok j hj)
                hm_ap ?_
              intro ok_an lm_an scr_an m_an _ hdw_an hscan_l hkeep_an hm_an
              have hk_an : ∀ i < 4002, scr_an[i]? = s0.scratch.scratch_buf[i]? := fun i hi =>
                (hkeep_an i (by omega) (Or.inl hi)).trans (hk_ap i hi)
              have htmk_an : TmkZero
                  { s0 with
                    core := { s0.core with lit_mark := lm_an }
                    scratch := { s0.scratch with scratch_buf := scr_an } } := htmk0
              c0_hsplit
              · c0_hsteps!
                exact hQ _ m_an hdw_an htmk_an rfl rfl rfl (Nat.le_refl _)
                  (fun i hi => hk_an i (by omega))
                  (fun j hj => hk_an (2001 + j) (by omega)) hm_an
              · clear hc
                fid_call hIte
                dsimp only [vals, Arg.val]
                refine m8BveFindIteSpec_intro rfl hdw_an hsc16384 hv_lt hnp2001 hnn2001
                  (fun i hi => by rw [hk_an i (by omega)]; exact hp_ok i hi)
                  (fun j hj => by rw [hk_an (2001 + j) (by omega)]; exact hn_ok j hj)
                  hm_an ?_
                intro ok_i scr_i m_i _ hsci_l hkeep_i hm_i
                have hdw_i := m8_fullDenseInvW_scr hdw_an hsci_l
                have hk_i : ∀ k < 4002, scr_i[k]? = s0.scratch.scratch_buf[k]? := fun k hk =>
                  (hkeep_i k (by omega) (Or.inl hk)).trans (hk_an k hk)
                have htmk_i : TmkZero
                    { s0 with
                      core := { s0.core with lit_mark := lm_an }
                      scratch := { s0.scratch with scratch_buf := scr_i } } := htmk0
                c0_hsplit
                · c0_hsteps!
                  exact hQ _ m_i hdw_i htmk_i rfl rfl rfl (Nat.le_refl _)
                    (fun k hk => hk_i k (by omega))
                    (fun j hj => hk_i (2001 + j) (by omega)) hm_i
                · clear hc
                  c0_hsteps_nogrp
                  fid_call hDefK6
                  dsimp only [vals, Arg.val]
                  refine m8BveGatesSpec_intro rfl hdw_i htmk_i hsc16384 hv_lt hnp2001 hnn2001
                    (fun i hi => by rw [hk_i i (by omega)]; exact hp_ok i hi)
                    (fun j hj => by rw [hk_i (2001 + j) (by omega)]; exact hn_ok j hj)
                    hm_i ?_
                  intro s_f m_f hdw_f htmk_f hcv_f har_f hal_f hfl_f hp_f hn_f hm_f
                  c0_hsteps!
                  exact hQ s_f m_f hdw_f htmk_f hcv_f har_f hal_f hfl_f
                    (fun i hi => (hp_f i hi).trans (hk_i i (by omega)))
                    (fun j hj => (hn_f j hj).trans (hk_i (2001 + j) (by omega)))
                    hm_f
  · intro L0 hL0; c0_hsteps!
    exact hL0 130 (0#32, ()) m0 ⟨s0.scratch.scratch_buf, hdw0.1.scratch_ok.scratch_buf_len,
      Nat.zero_le _, rfl, fun _ _ => rfl, hm0⟩

/-! ## 2. `full_vivify_tier_m6_hdr_fid_wp` (Exact `vivify.c:1269` Sort Guard) -/

/-- Parametric `Func.wp` proof for `full_vivify_tier_m6_hdr_fid_body` against canonical
`m6aVivifyTierSpec` over `FullMem` (no Wave-A extension writes). -/
theorem full_vivify_tier_m6_hdr_fid_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hCollect : ∀ a m Q X, fullVivCollectM6Spec a m Q X →
      Γ "full_viv_collect_m6" [i64, i64] [i64] a m Q X)
    (hCount : ∀ a m Q X, fullVivCountM6Spec a m Q X →
      Γ "full_viv_count_m6" [i64, i64] [] a m Q X)
    (hKeys : ∀ a m Q X, fullVivKeysM6Spec a m Q X →
      Γ "full_viv_keys_m6" [i64, i64] [] a m Q X)
    (hSortSched : ∀ a m Q X, fullVivSortSchedM6Spec a m Q X →
      Γ "full_viv_sort_sched_m6" [i64, i64] [] a m Q X)
    (hVivClause : ∀ a m Q X, fullVivClauseM6Spec a m Q X →
      Γ "full_viv_clause_m6" [i64, i32] [i64] a m Q X)
    (hProp : ∀ a m Q X, fullBcpS15Spec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hClearTier : ∀ a m Q X, fullVivClearTierM6Spec a m Q X →
      Γ "full_viv_clear_tier_m6" [i64, i64] [] a m Q X) :
    ∀ a m Q X, m6aVivifyTierSpec a m Q X →
      Func.wp Γ full_vivify_tier_m6_hdr_fid_body a m Q X := by
  rintro ⟨h, tier_mode, budget0, tick_lim, ⟨⟩⟩ m0 Q X hs
  obtain ⟨c, F0, s, R, rfl, hsp0, hm0, hQ⟩ := m6aVivifyTierSpec_elim hs
  have har_cap := c.harena; have hmx := c.hmaxv; have hrc := c.hred
  unfold LratBytes.dimacsBound at har_cap hmx hrc
  have hmaxv : c.max_vars < 2 * 2 ^ 28 := hmx
  have h3 : (3#64 : BitVec 64) ≠ 0#64 := by decide
  have h10 : (10#64 : BitVec 64) ≠ 0#64 := by decide
  unfold Func.wp full_vivify_tier_m6_hdr_fid_body; c0_hsteps_nogrp
  · exact hQ 1#64 s m0 hsp0 (fun h => h) (fun h => h) (fun hb => absurd (by c0_bound) hb)
      (Nat.le_refl _) (Or.inl rfl) (fun h => by cases h) hm0
  refine wp_join_group (ts := [])
    (fun () m1 => ∃ s1 : FullState, FullSparseInv c F0 s1 ∧ s1.core.cur_level = 0 ∧
      s1.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s1 ⋆ R) m1) ?_ ?_
  · rintro _ ⟨⟩ m ⟨s1, hsp1, hcl1, hfl1, hm⟩
    c0_hsteps_nogrp
    let s2 : FullState := { s1 with core := { s1.core with probing := 1#64 } }
    have hsp2 : FullSparseInv c F0 s2 := FullVivTop.FullSparseInv.with_probing hsp1 1#64
    have hm2 : (FullMem c s2 ⋆ R) m := hm
    have hfl2 : s2.core.fuel.toNat ≤ s.core.fuel.toNat := hfl1
    clear_value s2; clear hsp1 hcl1 hfl1
    fid_call hCollect
    refine ⟨c, F0, s2, R, rfl, hsp2, hm2, fun bn rr3 m3 h3bn hrr3 hok3 hm3 => ?_⟩
    let s3 : FullState := { s2 with scratch := { s2.scratch with red_refs := rr3 } }
    have hsp3 : FullSparseInv c F0 s3 := sparse_with_rr_wac hsp2 hrr3
    c0_hsteps_nogrp
    refine wp_join_group (ts := [])
      (fun () m5 => ∃ s5 : FullState, FullSparseInv c F0 s5 ∧
        s5.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        fullArenaClauseRefs s5 = fullArenaClauseRefs s2 ∧
        s5.scratch.red_refs.length = c.red_cap ∧
        (∀ k < bn.toNat, (s5.scratch.red_refs[3 * k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s2) ∧
        (FullMem c s5 ⋆ R) m5) ?_ ?_
    · rintro _ ⟨⟩ m5 ⟨s5, hsp5, hfl5, hrefs5, hrr5_len, hok5', hm5'⟩
      let rr5 := s5.scratch.red_refs
      have hrr5 : s5.scratch.red_refs = rr5 := rfl
      clear hrr3 hok3 hm3 s3 hsp3 hsp2 hm2 hfl2 hCollect hCount hKeys hSortSched
      c0_hsteps_nogrp
      refine wp_loop_break_group (brkTs := [i64, i64, i64]) (lpTs := [i64, i64])
        (fun (_budget_b, res_b, bi_b, ()) mb => ∃ sb : FullState,
          FullSparseInv c F0 sb ∧ sb.core.fuel.toNat ≤ s.core.fuel.toNat ∧
          (res_b = 1#64 ∨ res_b = 20#64) ∧ (res_b = 20#64 → F0.Unsat) ∧
          (FullMem c sb ⋆ R) mb)
        (fun rem (budget, bi, ()) mvi => ∃ svi : FullState,
          bi.toNat ≤ bn.toNat ∧ rem = bn.toNat - bi.toNat ∧
          FullSparseInv c F0 svi ∧ svi.core.fuel.toNat ≤ s.core.fuel.toNat ∧
          fullArenaClauseRefs svi = fullArenaClauseRefs s2 ∧
          svi.scratch.red_refs = rr5 ∧ (FullMem c svi ⋆ R) mvi)
        ?_ ?_ ?_
      · rintro _ ⟨_, res_b, bi_b, ⟨⟩⟩ mb ⟨sb, hspb, hflb, hresb, h20b, hmb⟩
        refine wp_join_group (ts := [])
          (fun () m_bt => ∃ sbt : FullState, FullSparseInv c F0 sbt ∧ sbt.core.cur_level = 0 ∧
            sbt.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c sbt ⋆ R) m_bt) ?_ ?_
        · rintro _ ⟨⟩ m_bt ⟨sbt, hspbt, hclbt, hflbt, hm_bt⟩
          refine wp_join_group (ts := [])
            (fun () m_w => ∃ sw : FullState, FullSparseInv c F0 sw ∧ sw.core.cur_level = 0 ∧
              sw.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c sw ⋆ R) m_w) ?_ ?_
          · rintro _ ⟨⟩ m_w ⟨sw, hspw, hclw, hflw, hm_w⟩
            c0_hsteps
            let sf : FullState := { sw with core := { sw.core with probing := 0#64 } }
            have hspf : FullSparseInv c F0 sf := FullVivTop.FullSparseInv.with_probing hspw 0#64
            exact hQ res_b sf _ hspf (fun _ => hclw) (fun _ => rfl)
              (fun _ => ⟨hclw, rfl⟩) hflw hresb h20b hm
          · intro Jw hJw; c0_hsteps
            · fid_call hClearTier
              refine ⟨c, F0, sbt, R, rfl, hspbt, hclbt, hm_bt,
                fun sw m_w hspw hclw hflw hm_w =>
                  hJw () m_w ⟨sw, hspw, hclw, by rw [hflw]; exact hflbt, hm_w⟩⟩
            · exact hJw () m_bt ⟨sbt, hspbt, hclbt, hflbt, hm_bt⟩
            · exact hJw () m_bt ⟨sbt, hspbt, hclbt, hflbt, hm_bt⟩
            · exact hJw () m_bt ⟨sbt, hspbt, hclbt, hflbt, hm_bt⟩
        · intro Jbt hJbt
          obtain ⟨F_curb, hswb⟩ := hspb.exists_witness
          have hclb_lt : sb.core.cur_level < 2 ^ 64 := by
            have := hswb.2.1.cur_level_le; have := hspb.1.lengths.core_ok.trail_end_le
            have := hspb.1.lengths.core_ok.cur_vars_le; omega
          c0_hsteps
          · fid_call hBacktrack
            refine ⟨c, sb, R, rfl, hspb.1.lengths, hclb_lt,
              (by intro _; have := hswb.2.1.cur_level_le
                  have := hspb.1.lengths.core_ok.trail_end_le
                  have := hspb.1.lengths.core_ok.cur_vars_le; omega),
              hswb.2.1.trail_lits_lt, hmb,
              fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m_bt
                hlen_bt _ _ hcl_bt hpres_bt _ _ _ hw_bt _ hm_bt => ?_⟩
            have hsp_bt : FullSparseInv c F0 _ :=
              FullVivTop.FullSparseInv.of_backtrack hspb (Nat.zero_le _) hlen_bt hpres_bt
                (by simpa using hw_bt F0)
            exact hJbt () m_bt ⟨_, hsp_bt, by rw [hcl_bt]; simp, hflb, hm_bt⟩
          · have hclb0 : sb.core.cur_level = 0 := by
              have h0 : (BitVec.ofNat 64 sb.core.cur_level).toNat = 0 := by rw [hc]; rfl
              rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hclb_lt] at h0
            exact hJbt () mb ⟨sb, hspb, hclb0, hflb, hmb⟩
      · intro B L rem ⟨budget, bi, ⟨⟩⟩ mvi hB hL
          ⟨svi, hbi_le, hrem, hspv, hflv, hrefsv, hrrv, hmvi⟩
        subst hrem
        c0_hsteps
        · have hbi_lt : bi.toNat < bn.toNat := by c0_bound
          have hbi3_nat : (bi * 3).toNat = 3 * bi.toNat := by
            rw [BitVec.toNat_mul, show (3 : BitVec 64).toNat = 3 from rfl,
              Nat.mod_eq_of_lt (by omega), Nat.mul_comm]
          have hrr5_len' : rr5.length = c.red_cap := hrr5_len
          have hbi3_lt : (bi * 3).toNat < svi.scratch.red_refs.length := by
            rw [hrrv, hrr5_len', hbi3_nat]; omega
          let cr := svi.scratch.red_refs[(bi * 3).toNat]'hbi3_lt
          have hcr_ref : cr.toNat ∈ fullArenaClauseRefs svi := by
            rw [hrefsv]
            have h := hok5' bi.toNat hbi_lt
            dsimp only [rr5] at hrr5_len' h ⊢
            rw [List.getElem?_eq_getElem (by rw [hrr5_len']; omega), Option.getD_some] at h
            have heq : cr = s5.scratch.red_refs[3 * bi.toNat]'(by rw [hrr5_len']; omega) :=
              Option.some.inj (by
                rw [← List.getElem?_eq_getElem hbi3_lt, hrrv, hbi3_nat,
                  List.getElem?_eq_getElem (by rw [hrr5_len']; omega)])
            rwa [heq]
          obtain ⟨F_curv, hswv⟩ := hspv.exists_witness
          have hbi1 : (bi + 1#64).toNat = bi.toNat + 1 := by bv_omega
          c0_hsteps
          fid_call hVivClause
          refine ⟨c, F0, F_curv, svi, R, rfl, hswv, hcr_ref, hmvi,
            fun vc s_vc m_vc hsw_vc hfl_vc _ hrefs_vc hrr_vc hvc h20_vc hm_vc => ?_⟩
          have hrefs_vc2 : fullArenaClauseRefs s_vc = fullArenaClauseRefs s2 :=
            hrefs_vc.trans hrefsv
          have hrr_vc5 : s_vc.scratch.red_refs = rr5 := hrr_vc.trans hrrv
          have hfl_vc' : s_vc.core.fuel.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfl_vc hflv
          c0_hsteps
          · exact hB (budget - 1#64, 20#64, bi, ()) m_vc
              ⟨s_vc, hsw_vc.toSparse, hfl_vc', Or.inr rfl, fun _ => h20_vc (by c0_bound), hm_vc⟩
          · exact hB (budget - 1#64, 1#64, bi, ()) m_vc
              ⟨s_vc, hsw_vc.toSparse, hfl_vc', Or.inl rfl, (fun h => by cases h), hm_vc⟩
          · have hcl_vc_lt : s_vc.core.cur_level < 2 ^ 64 := by
              have := hsw_vc.2.1.cur_level_le; have := hsw_vc.1.core_ok.trail_end_le
              have := hsw_vc.1.core_ok.cur_vars_le; omega
            have hcl_vc0 : s_vc.core.cur_level = 0 := by
              have h0 : (BitVec.ofNat 64 s_vc.core.cur_level).toNat = 0 := by
                have hc0 : BitVec.ofNat 64 s_vc.core.cur_level = 0#64 := by c0_bound
                rw [hc0]; rfl
              rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcl_vc_lt] at h0
            fid_call hProp
            refine ⟨c, F0, F_curv, s_vc, R, rfl, hsw_vc.1, hsw_vc.2.1, hsw_vc.2.2.2.2.2, hm_vc,
              fun pr vals_p flags_p lvl_p rsns_p trl_p tp_p te_p prop_p unass_p unfl_p
                wvec_p arena_p wstk_p wlen_p wu_p fuel_p ctype_p cref_p c0_p c1_p oom_p
                ticks_p wsort_p phases_p delayed_p m_p hlen_p hw_p _ hperm_p _ hfl_p _ _ hpr1 _ _
                hm_p => ?_⟩
            let s_p : FullState :=
              { s_vc with
                core := { s_vc.core with
                  vals := vals_p, flags := flags_p, lvl := lvl_p, rsns := rsns_p,
                  trl := trl_p, trail_pos := tp_p, trail_end := te_p, propagated := prop_p,
                  unassigned := unass_p, unflushed := unfl_p, wvec := wvec_p,
                  arena := arena_p, wstk := wstk_p, wlen := wlen_p, wusable := wu_p,
                  fuel := fuel_p, confl_type := ctype_p, confl_ref := cref_p,
                  confl_lit0 := c0_p, confl_lit1 := c1_p, oom := oom_p }
                scratch := { s_vc.scratch with
                  search_ticks := ticks_p, wsort := wsort_p, phases := phases_p,
                  delayed := delayed_p } }
            have hsw_p : FullSparseInvW c F0 F_curv s_p :=
              sparseInvW_of_prop_wac hsw_vc hlen_p hw_p hperm_p
            have hrefs_p : fullArenaClauseRefs s_p = fullArenaClauseRefs s_vc := hperm_p.2.1
            have hfl_p' : s_p.core.fuel.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfl_p hfl_vc'
            c0_hsteps
            · have hpr_eq1 : pr = 1#64 := by c0_bound
              have hunsat : F0.Unsat :=
                FullVivTopSpecs.level0_unsat_of_conflict_okW hw_p hcl_vc0 (hpr1 hpr_eq1).2.2
              exact hB (budget - 1#64, 20#64, bi, ()) m_p
                ⟨s_p, hsw_p.toSparse, hfl_p', Or.inr rfl, fun _ => hunsat, hm_p⟩
            · exact hL (bn.toNat - (bi + 1#64).toNat) (budget - 1#64, bi + 1#64, ()) m_p
                (by rw [hbi1]; omega)
                ⟨s_p, by rw [hbi1]; omega, rfl, hsw_p.toSparse, hfl_p',
                  hrefs_p.trans hrefs_vc2, hrr_vc5, hm_p⟩
          · exact hL (bn.toNat - (bi + 1#64).toNat) (budget - 1#64, bi + 1#64, ()) m_vc
              (by rw [hbi1]; omega)
              ⟨s_vc, by rw [hbi1]; omega, rfl, hsw_vc.toSparse, hfl_vc', hrefs_vc2, hrr_vc5, hm_vc⟩
        · exact hB (budget, 1#64, bi, ()) mvi
            ⟨svi, hspv, hflv, Or.inl rfl, (fun h => by cases h), hmvi⟩
        · exact hB (budget, 1#64, bi, ()) mvi
            ⟨svi, hspv, hflv, Or.inl rfl, (fun h => by cases h), hmvi⟩
        · exact hB (budget, 1#64, bi, ()) mvi
            ⟨svi, hspv, hflv, Or.inl rfl, (fun h => by cases h), hmvi⟩
        · exact hB (budget, 1#64, bi, ()) mvi
            ⟨svi, hspv, hflv, Or.inl rfl, (fun h => by cases h), hmvi⟩
        · exact hB (budget, 1#64, bi, ()) mvi
            ⟨svi, hspv, hflv, Or.inl rfl, (fun h => by cases h), hmvi⟩
      · intro B L _ hL; c0_hsteps
        exact hL bn.toNat (budget0, 0#64, ()) m5
          ⟨s5, Nat.zero_le _, by simp, hsp5, hfl5, hrefs5, hrr5, hm5'⟩
    · intro J5 hJ5; c0_hsteps
      rotate_right 1
      · exact hJ5 () m3 ⟨s3, hsp3, hfl2, rfl, hrr3, hok3, hm3⟩
      all_goals
        fid_call hCount
        refine ⟨c, F0, s3, R, rfl, hsp3, h3bn, hok3, hm3, fun tr3 m3c htr3 hm3c => ?_⟩
        let s3c : FullState := { s3 with scratch := { s3.scratch with tarjan_reach := tr3 } }
        have hsp3c : FullSparseInv c F0 s3c := sparse_with_tr_wac hsp3 htr3
        fid_call hKeys
        refine ⟨c, F0, s3c, R, rfl, hsp3c, h3bn, hok3, hm3c, fun rr4 m4 hrr4 hok4 hm4 => ?_⟩
        let s4 : FullState := { s3c with scratch := { s3c.scratch with red_refs := rr4 } }
        have hsp4 : FullSparseInv c F0 s4 := sparse_with_rr_wac hsp3c hrr4
        fid_call hSortSched
        refine ⟨c, F0, s4, R, rfl, hsp4, h3bn, hok4, hm4, fun rr5 m5 hrr5_len hok5 hm5 => ?_⟩
        let s5 : FullState := { s4 with scratch := { s4.scratch with red_refs := rr5 } }
        exact hJ5 () m5 ⟨s5, sparse_with_rr_wac hsp4 hrr5_len, hfl2, rfl, hrr5_len, hok5, hm5⟩
  · intro Jc hJc
    obtain ⟨F_cur0, hsw0⟩ := hsp0.exists_witness
    have hcl0_lt : s.core.cur_level < 2 ^ 64 := by
      have := hsw0.2.1.cur_level_le; have := hsp0.1.lengths.core_ok.trail_end_le
      have := hsp0.1.lengths.core_ok.cur_vars_le; omega
    c0_hsteps
    · fid_call hBacktrack
      refine ⟨c, s, R, rfl, hsp0.1.lengths, hcl0_lt,
        (by intro _; have := hsw0.2.1.cur_level_le
            have := hsp0.1.lengths.core_ok.trail_end_le
            have := hsp0.1.lengths.core_ok.cur_vars_le; omega),
        hsw0.2.1.trail_lits_lt, hm0,
        fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m1
          hlen1 _ _ hcl1 hpres1 _ _ _ hw_bt _ hm1 => ?_⟩
      have hsp1 : FullSparseInv c F0 _ :=
        FullVivTop.FullSparseInv.of_backtrack hsp0 (Nat.zero_le _) hlen1 hpres1
          (by simpa using hw_bt F0)
      exact hJc () m1 ⟨_, hsp1, by rw [hcl1]; simp, Nat.le_refl _, hm1⟩
    · have hcl0 : s.core.cur_level = 0 := by
        have h0 : (BitVec.ofNat 64 s.core.cur_level).toNat = 0 := by rw [hc]; rfl
        rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcl0_lt] at h0
      exact hJc () m0 ⟨s, hsp0, hcl0, Nat.le_refl _, hm0⟩

/-! ## 3. `fid_sweep_vars_wp` (Exact `sweep.c:1673` `1x` Ticks & `per_v = 16384`) -/

/-- Parametric `Func.wp` proof for `full_m6_sweep_vars_fid_body` (`1x` Kitten ticks,
`per_v = 16384`), certifying canonical `m6SweepVarsSpec`. -/
theorem fid_sweep_vars_wp (Γ : Env)
    (hMaxV : M6EnvSpec Γ "full_m6_max_v" m6MaxVSpec)
    (hDP : M6EnvSpec Γ "full_m6_dense_prop" m6DensePropSpec)
    (hCol : M6EnvSpec Γ "full_m6_collect_cands" m6CollectCandsSpec)
    (hSV : M6EnvSpec Γ "full_m6_sweep_var" m6SweepVarSpec) :
    ∀ args m Q X, m6SweepVarsSpec args m Q X →
      Func.wp Γ full_m6_sweep_vars_fid_body args m Q X := by
  rintro ⟨h, budget, tlim, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, htmk, hm, hQ⟩
  unfold Func.wp full_m6_sweep_vars_fid_body
  have hlen := hinv.lengths
  have hcap_lt : c.scratch_cap < 2 ^ 64 := Nat.lt_trans c.hscr (by unfold dimacsBound; decide)
  c0_hsteps_nogrp
  refine m8_call_max_v_cap hMaxV (cap := BitVec.ofNat 64 c.scratch_cap) ?_
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcap_lt]
  c0_hsplit
  · c0_hsteps!
    exact hQ 1#64 s m hinv rfl (Nat.le_refl _) htmk (Or.inl rfl) (fun h => by simp at h) hm
  have hcap_ge : k6MinScr ≤ c.scratch_cap := by
    rcases Nat.lt_or_ge c.scratch_cap k6MinScr with hlt | hle
    · have hmv0 : k6MaxV c.scratch_cap = 0 := k6MaxV_eq_zero hlt
      have hmv0_32 : (BitVec.ofNat 64 (k6MaxV c.scratch_cap)).setWidth 32 = 0#32 := by
        rw [hmv0]; rfl
      have hnot : ¬ (BitVec.ofNat 64 (k6MaxV c.scratch_cap)).setWidth 32 = 0#32 := hc
      exact absurd hmv0_32 hnot
    · exact hle
  c0_hsplit
  · c0_hsteps!
    exact hQ 1#64 s m hinv rfl (Nat.le_refl _) htmk (Or.inl rfl) (fun h => by simp at h) hm
  c0_hsplit
  · c0_hsteps!
    exact hQ 1#64 s m hinv rfl (Nat.le_refl _) htmk (Or.inl rfl) (fun h => by simp at h) hm
  obtain ⟨F_cur, hwW⟩ := hinv.exists_witness
  have hdw : FullDenseInvW c F0 F_cur s := hwW
  refine m8_call_dense_prop hDP hdw hm
    (fun ok s1 m1 hdw1 hcv1 hfuel1 htmk1 htrc1 hok1 hno1 hm1 => ?_)
  c0_hsplit; rotate_left
  · have hokf : ok = false := by cases ok <;> simp_all
    c0_hsteps!
    exact hQ 20#64 s1 m1 (m8_denseInv_of_W hdw1) hcv1 (by rw [hfuel1]; exact Nat.le_refl _)
      (m8_tmkZero_congr htmk hcv1 htmk1) (Or.inr rfl) (fun _ => (hno1 hokf).1) hm1
  have hlen1 := hdw1.1
  have htmk1_z : M6TmkZero s1 := m8_tmkZero_congr htmk hcv1 htmk1
  refine m8_call_collect_cands hCol hlen1 hm1 (fun nc trc2 ws2_2 m2 hlen2 hnc2 hbd2 hm2 => ?_)
  let s2 : FullState :=
    { s1 with scratch := { s1.scratch with tarjan_reach := trc2, work_stk2 := ws2_2 } }
  have hdw2 : FullDenseInvW c F0 F_cur s2 :=
    m8_denseInvW_set_trc_ws2 hdw1 hlen2.scratch_ok.tarjan_reach_len hlen2.scratch_ok.work_stk2_len
  have htmk2 : M6TmkZero s2 := m8_tmkZero_congr htmk1_z rfl rfl
  c0_hsteps_nogrp
  c0_hsplit
  · c0_hsteps!
    exact hQ 1#64 s2 m2 (m8_denseInv_of_W hdw2) hcv1
      (by dsimp only [s2]; rw [hfuel1]; exact Nat.le_refl _)
      htmk2 (Or.inl rfl) (fun h => by simp at h) hm2
  obtain ⟨L, hL⟩ : ∃ L : K6Layout, L = k6LayoutOfCap c.scratch_cap hcap_ge c.hscr := ⟨_, rfl⟩
  have hL_len : L.scrLen = c.scratch_cap := hL ▸ k6LayoutOfCap_scrLen hcap_ge c.hscr
  have hL_mv : L.maxV = k6MaxV c.scratch_cap := by rw [hL]; rfl
  have hkptr_c0 : c.pScratchBuf + BitVec.setWidth 64
      ((1280 : BitVec 32) + (BitVec.setWidth 32 (BitVec.ofNat 64 (k6MaxV c.scratch_cap)) <<<
        (1 : Nat))) * 4 = L.kPtr c.pScratchBuf := by
    rw [← hL_mv, k6_mv32_zext]
    simpa only [show (1280 : BitVec 32) = 1280#32 from rfl] using
      k6_ptr_base_k6Base L c.pScratchBuf
  have hscr2 : s2.scratch.scratch_buf.length = c.scratch_cap := hlen2.scratch_ok.scratch_buf_len
  c0_hsteps_nogrp
  try rw [hkptr_c0]
  have hk11_ptr := m8_k11_ptr (c := c) (L := L) hL_len
  have hk11_idx := m8_k11_idx (c := c) (L := L) hL_len
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64]) (fun (tl_c, ()) mt => tl_c.toNat ≤ 0xFFFFFFFF ∧ mt = m2)
    (fun _ (tl_c, ()) mt ⟨htl_le, hmt⟩ => by
      subst mt
      c0_hsteps_nogrp
      refine wp_loop_inv (ts := [i64, i32, i64])
        (fun (tl_l, ci_l, rem_l, ()) ml =>
          ci_l.toNat ≤ nc.toNat ∧
          ∃ s_l : FullState, FullDenseInvW c F0 F_cur s_l ∧
            s_l.core.cur_vars = s2.core.cur_vars ∧
            s_l.core.fuel.toNat ≤ s2.core.fuel.toNat ∧
            M6TmkZero s_l ∧ s_l.scratch.tarjan_reach = trc2 ∧ (FullMem c s_l ⋆ R) ml)
        (fun (_, ci_l, _, ()) _ => nc.toNat - ci_l.toNat)
        (fun _ hJ_in => by
          c0_hsteps!
          exact hJ_in (tl_c, 0#32, budget, ()) m2
            ⟨Nat.zero_le _, s2, hdw2, rfl, Nat.le_refl _, htmk2, rfl, hm2⟩)
        (fun _ (tl_l, ci_l, rem_l, ()) ml ⟨hci_le, s_l, hdw_l, hcv_l, hfl_l, htmk_l,
            htrc_l, hm_l⟩ hJ_in => by
          have hlen_l := hdw_l.1
          have hfuel_all : s_l.core.fuel.toNat ≤ s.core.fuel.toNat := by
            dsimp only [s2] at hfl_l; rw [hfuel1] at hfl_l; exact hfl_l
          have hcv_all : s_l.core.cur_vars = s.core.cur_vars := hcv_l.trans hcv1
          c0_hsteps_nogrp
          refine wp_join_group (ts := []) (fun _ me => me = ml)
            (fun _ _ me hme => by
              subst me
              c0_hsteps_nogrp
              refine wp_unroll_group fun J hJ => ?_
              c0_hsplit
              · c0_hsteps_nogrp
                exact hQ 20#64 s_l ml (m8_denseInv_of_W hdw_l) hcv_all hfuel_all htmk_l
                  (Or.inr rfl) (fun _ => (m8_denseInv_of_W hdw_l).inconsistent_unsat hc) hm_l
              · c0_hsteps_nogrp
                exact hQ 1#64 s_l ml (m8_denseInv_of_W hdw_l) hcv_all hfuel_all htmk_l
                  (Or.inl rfl) (fun h => by simp at h) hm_l)
            (fun _ hJ_ex => by
              c0_hsplit
              · have hci_lt : ci_l.toNat < nc.toNat := hc
                have hmx := maxVars_lt_2p31 c
                have hci_trc : (ci_l.setWidth 64).toNat < s_l.scratch.tarjan_reach.length := by
                  rw [htrc_l, hlen2.scratch_ok.tarjan_reach_len, BitVec.toNat_setWidth,
                    Nat.mod_eq_of_lt (by omega)]
                  have := hnc2; have := hlen.core_ok.cur_vars_le; omega
                c0_hsplit
                · have hrem_pos : 0 < rem_l.toNat := hc
                  c0_hsplit
                  · have htl_pos : 0 < tl_l.toNat := hc
                    c0_hsteps_nogrp <;> try exact hJ_ex () ml rfl
                    have hci1 : (ci_l + 1#32).toNat = ci_l.toNat + 1 :=
                      bv32_add1_toNat (by have := hnc2; have := hlen.core_ok.cur_vars_le; omega)
                    refine wp_join_group (ts := [i64, i64])
                      (fun (tl_n, rem_n, ()) mj =>
                        ∃ s_n : FullState, FullDenseInvW c F0 F_cur s_n ∧
                          s_n.core.cur_vars = s2.core.cur_vars ∧
                          s_n.core.fuel.toNat ≤ s2.core.fuel.toNat ∧
                          M6TmkZero s_n ∧ s_n.scratch.tarjan_reach = trc2 ∧
                          (FullMem c s_n ⋆ R) mj)
                      (fun _ (tl_n, rem_n, ()) mj ⟨s_n, hdw_n, hcv_n, hfl_n, htmk_n,
                          htrc_n, hm_n⟩ => by
                        c0_hsteps_nogrp
                        exact hJ_in (tl_n, ci_l + 1#32, rem_n, ()) mj
                          (by dsimp only; rw [hci1]; omega)
                          ⟨by rw [hci1]; omega, s_n, hdw_n, hcv_n, hfl_n, htmk_n, htrc_n, hm_n⟩)
                      (fun _ hJ_step => by
                        let rv := s_l.scratch.tarjan_reach[(ci_l.setWidth 64).toNat]'hci_trc
                        have hrv_lt : rv.toNat < s_l.core.cur_vars := by
                          have hci_m : (ci_l.setWidth 64).toNat = ci_l.toNat := by
                            rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                          have hbd := hbd2 ci_l.toNat hci_lt
                          rw [← hci_m, List.getElem?_eq_getElem (by rw [← htrc_l]; exact hci_trc),
                            Option.getD_some] at hbd
                          rw [hcv_l]; dsimp only [s2]
                          have hrv_eq : rv = trc2[(ci_l.setWidth 64).toNat]'(htrc_l ▸ hci_trc) := by
                            dsimp only [rv]; simp only [htrc_l]
                          rwa [hrv_eq]
                        have hrv_fl : (BitVec.setWidth 64 rv).toNat < s_l.core.flags.length := by
                          rw [hdw_l.1.core_ok.flags_len, BitVec.toNat_setWidth,
                            Nat.mod_eq_of_lt (by omega)]
                          exact Nat.lt_of_lt_of_le hrv_lt hdw_l.1.core_ok.cur_vars_le
                        have hrv_vals : (BitVec.setWidth 64 (rv <<< (1 : Nat))).toNat <
                            s_l.core.vals.length := by
                          rw [hdw_l.1.core_ok.vals_len]
                          have := hdw_l.1.core_ok.cur_vars_le
                          bv_omega
                        have h_skip_step : ∃ s_n : FullState, FullDenseInvW c F0 F_cur s_n ∧
                            s_n.core.cur_vars = s2.core.cur_vars ∧
                            s_n.core.fuel.toNat ≤ s2.core.fuel.toNat ∧ M6TmkZero s_n ∧
                            s_n.scratch.tarjan_reach = trc2 ∧ (FullMem c s_n ⋆ R) ml :=
                          ⟨s_l, hdw_l, hcv_l, hfl_l, htmk_l, htrc_l, hm_l⟩
                        c0_hsteps_nogrp <;> (try exact hJ_step (tl_l, rem_l, ()) ml h_skip_step)
                        refine wp_join_group (ts := [i64])
                          (fun (_pv, ()) mp =>
                            ∃ fl_l : List (BitVec 32), fl_l.length = c.max_vars ∧
                              (FullMem c { s_l with core := { s_l.core with flags := fl_l } } ⋆
                                R) mp)
                          (fun _ (pv, ()) mp ⟨fl_l, hfl_l_len, hmp⟩ => by
                            refine m8_call_sweep_var_fl hSV hmp hdw_l
                              hfl_l_len hcap_ge hrv_lt htmk_l
                              (fun r3 s3 m3 hdw3 hcv3 hfl3 htmk3 htrc3 hr3 hunsat3 hm3 => ?_)
                            c0_hsteps_nogrp
                            c0_hsplit
                            · c0_hsteps!
                              exact hQ 20#64 s3 m3 (m8_denseInv_of_W hdw3) (hcv3.trans hcv_all)
                                (Nat.le_trans hfl3 hfuel_all) htmk3 (Or.inr rfl)
                                (fun _ => hunsat3 hc) hm3
                            · refine wp_join_group (ts := [])
                                (fun () md => ∃ s_d : FullState, FullDenseInvW c F0 F_cur s_d ∧
                                  s_d.core.cur_vars = s2.core.cur_vars ∧
                                  s_d.core.fuel.toNat ≤ s2.core.fuel.toNat ∧
                                  M6TmkZero s_d ∧ s_d.scratch.tarjan_reach = trc2 ∧
                                  (FullMem c s_d ⋆ R) md)
                                (fun _ () md ⟨s_d, hdw_d, hcv_d, hfl_d, htmk_d, htrc_d, hm_d⟩ => by
                                  have hscr_d : s_d.scratch.scratch_buf.length = c.scratch_cap :=
                                    hdw_d.1.scratch_ok.scratch_buf_len
                                  have hk11_sd : (BitVec.setWidth 64
                                      (BitVec.ofNat 32 (L.k6Base + 11))).toNat <
                                      s_d.scratch.scratch_buf.length := hscr_d ▸ hk11_idx
                                  c0_hsteps_nogrp
                                  try rw [hk11_ptr]
                                  c0_hsteps_nogrp
                                  refine wp_join_group (ts := [i64])
                                    (fun (_tl_n, ()) mj' => mj' = md)
                                    (fun _ (tl_n, ()) mj' hmj' => by
                                      subst mj'
                                      c0_hsteps!
                                      have hstep_d : ∃ s_n : FullState,
                                          FullDenseInvW c F0 F_cur s_n ∧
                                          s_n.core.cur_vars = s2.core.cur_vars ∧
                                          s_n.core.fuel.toNat ≤ s2.core.fuel.toNat ∧
                                          M6TmkZero s_n ∧ s_n.scratch.tarjan_reach = trc2 ∧
                                          (FullMem c s_n ⋆ R) md :=
                                        ⟨s_d, hdw_d, hcv_d, hfl_d, htmk_d, htrc_d, hm_d⟩
                                      exact hJ_step (tl_n, rem_l - 1#64, ()) md hstep_d)
                                    (fun _ hJ87 => by
                                      c0_hsteps! <;> exact hJ87 (_, ()) md rfl))
                                (fun _ hJ_dp => by
                                  c0_hsteps_nogrp
                                  c0_hsplit
                                  · refine m8_call_dense_prop hDP hdw3 hm3
                                      (fun ok4 s4 m4 hdw4 hcv4 hfl4 htmk4 htrc4 hok4 hno4 hm4 => ?_)
                                    c0_hsteps_nogrp
                                    c0_hsplit
                                    · c0_hsteps_nogrp
                                      exact hJ_dp () m4 ⟨s4, hdw4, hcv4.trans (hcv3.trans hcv_l),
                                        by rw [hfl4]; exact Nat.le_trans hfl3 hfl_l,
                                        m8_tmkZero_congr htmk3 hcv4 htmk4,
                                        htrc4.trans (htrc3.trans htrc_l), hm4⟩
                                    · have hokf : ok4 = false := by cases ok4 <;> simp_all
                                      c0_hsteps!
                                      exact hQ 20#64 s4 m4 (m8_denseInv_of_W hdw4)
                                        (hcv4.trans (hcv3.trans hcv_all))
                                        (by rw [hfl4]; exact Nat.le_trans hfl3 hfuel_all)
                                        (m8_tmkZero_congr htmk3 hcv4 htmk4) (Or.inr rfl)
                                        (fun _ => (hno4 hokf).1) hm4
                                  · c0_hsteps_nogrp
                                    exact hJ_dp () m3 ⟨s3, hdw3, hcv3.trans hcv_l,
                                      Nat.le_trans hfl3 hfl_l, htmk3, htrc3.trans htrc_l, hm3⟩))
                          (fun _ hJ_pv => by
                            c0_hsteps_nogrp <;>
                              (refine hJ_pv (_, ()) _ ⟨_, ?_, by assumption⟩
                               rw [List.length_set, hdw_l.1.core_ok.flags_len])))
                  · c0_hsteps_nogrp; exact hJ_ex () ml rfl
                · c0_hsteps_nogrp; exact hJ_ex () ml rfl
              · c0_hsteps_nogrp; exact hJ_ex () ml rfl)))
    (fun _ hJt => by
      c0_hsplit
      · c0_hsteps!; exact hJt (0xFFFFFFFF#64, ()) m2 ⟨by decide, rfl⟩
      · have hle : tlim.toNat ≤ 0xFFFFFFFF := by
          have hnot : ¬ (4294967295 : Nat) < tlim.toNat := hc
          omega
        c0_hsteps!; exact hJt (tlim, ()) m2 ⟨hle, rfl⟩)

end LeanQbe.T.Examples.Kissat.FullFidelityBase
