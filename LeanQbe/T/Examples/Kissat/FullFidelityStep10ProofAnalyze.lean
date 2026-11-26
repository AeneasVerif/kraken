/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep10
public import LeanQbe.T.Examples.Kissat.FullFidelityStep10ProofLearn
public import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofAnalyze0
public import LeanQbe.T.Examples.Kissat.FullM7AnalyzeHdrProof
import LeanQbe.T.Examples.Kissat.FullAnalyzeLemmas1
import LeanQbe.T.Examples.Kissat.FullAnalyzeLemmas2
import LeanQbe.T.Examples.Kissat.FullDeduce1UipLemmas1
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1
import LeanQbe.T.Examples.Kissat.FullLearnAnaLemmas
import LeanQbe.T.Examples.Kissat.FullPropDecLemmas
import LeanQbe.T.Examples.Kissat.FullM6MinShrinkProof3a
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullSpec
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.OpsLemmas
import LeanQbe.T.Logic.Rules
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 10: `full_analyze_core_m6` `Func.wp` Proof (`FullFidelityStep10ProofAnalyze`)

Proves `full_analyze_core_m6_step10_wp`: Step-10 `full_analyze_core_m6` (calling
`full_learn_clause_m6` instead of legacy `full_learn_clause`) satisfies canonical
`FullM6Hdr.m6HdrAnalyzeSpec` (`public section`, `0` `@[expose]` on theorems/lemmas, `0`
`import all`, `std3`, `XPost`-polymorphic).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep10

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open scoped LeanQbe.T.ProofUtil
open Kraken.Bedrock2.Test
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open LeanQbe.T.Examples.Kissat.FullM5HeurCore
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open scoped LeanQbe.T.Examples.Kissat.FullM6ProofUtil.M6ProofUtilTactics
open LeanQbe.T.Examples.Kissat.FullM7Proof
open LeanQbe.T.Examples.Kissat.FullM8CoreParity

section AnalyzeStep10Helpers

private def S10AnaCoreLoopInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s : FullState) (R : Mem 64 → Prop) (iter_lim : BitVec 64)
    (st : BitVec 64 × FullState × List (BitVec 64)) (m' : Mem 64) : Prop :=
  ∃ cut', cut' ≤ st.2.1.core.trail_end ∧ FullCutInvW c F0 F_cur cut' st.2.1 ∧
    FullConflictOkCut F_cur cut' st.2.1 ∧ M6HdrExtOk st.2.2 ∧
    st.2.1.core.cur_vars = s.core.cur_vars ∧ st.2.1.core.fuel = s.core.fuel ∧
    st.2.1.core.cur_level ≤ s.core.cur_level ∧ st.2.1.scratch.work_stk2 = s.scratch.work_stk2 ∧
    st.1.toNat ≤ iter_lim.toNat ∧
    (FullMem c st.2.1 ⋆ (m6ExtMem (m6ExtAddr c.hdr) st.2.2 ⋆ R)) m'

private def S10AnaCoreShrinkPost (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s : FullState) (s' : FullState) : Prop :=
  FullOtfsInvW c F0 F_cur s' ∧ 0 < s'.core.cur_level ∧
  1 ≤ s'.core.tmp_len ∧ s'.core.tmp_len ≤ s'.core.cur_vars ∧
  (List.map (fun x => x.toNat / 2) (List.take s'.core.tmp_len s'.core.tmp)).Nodup ∧
  (∀ k < s'.core.tmp_len, let l := (s'.core.tmp[k]?.getD 0#32).toNat
    l < 2 * s'.core.cur_vars ∧ s'.core.vals[l]?.getD 0#8 = 255#8) ∧
  (∀ k, 1 ≤ k → k < s'.core.tmp_len →
    let lv := (s'.core.lvl[(s'.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
    0 < lv ∧ lv < s'.core.cur_level ∧
    lv ≤ (s'.core.lvl[(s'.core.tmp[s'.core.tmp_len - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) ∧
  (cnfOfClauses F_cur).EntailsClause
    (cnfClause (List.map BitVec.toNat (List.take s'.core.tmp_len s'.core.tmp))) ∧
  s'.core.cur_vars = s.core.cur_vars ∧ s'.core.fuel = s.core.fuel ∧
  s'.core.cur_level ≤ s.core.cur_level ∧ s'.scratch.work_stk2 = s.scratch.work_stk2

private def S10AnaCoreCutJoin (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (cut3 : Nat) (s : FullState) (s' : FullState) : Prop :=
  cut3 ≤ s'.core.trail_end ∧ FullCutInvW c F0 F_cur cut3 s' ∧
  FullConflictOkCut F_cur cut3 s' ∧
  s'.core.cur_vars = s.core.cur_vars ∧ s'.core.fuel = s.core.fuel ∧
  s'.core.cur_level ≤ s.core.cur_level ∧ s'.scratch.work_stk2 = s.scratch.work_stk2

end AnalyzeStep10Helpers

/-- Parametric `Func.wp` proof for `fidStep10AnalyzeCoreM6Fn` (`full_analyze_core_m6`, calling
`full_learn_clause_m6` to thread `M6HdrExt` across emergency reduction) against
`FullM6Hdr.m6HdrAnalyzeSpec`. -/
theorem full_analyze_core_m6_step10_wp (Γ : Env)
    (hOneLit : ∀ a m Q X, Full.fullOneLitConflSpec a m Q X →
      Γ "full_one_lit_confl" [i64] [i64] a m Q X)
    (hFailed : ∀ a m Q X, FullM6OrchAdapters.m6aAnaFailedLitSpecP M6ExtW2bPres a m Q X →
      Γ "full_ana_failed_lit_m6_hdr" [i64] [i64] a m Q X)
    (hDeduce : ∀ a m Q X, m7Deduce1uipHdrSpec a m Q X →
      Γ "full_deduce_1uip_m6_hdr" [i64] [i64] a m Q X)
    (hRestore : ∀ a m Q X, FullM6OrchAdapters.m6aRestoreBumpAnaSpecP M6ExtW2bPres a m Q X →
      Γ "full_restore_bump_ana_m6_hdr" [i64] [] a m Q X)
    (hMinShrink : ∀ a m Q X, m8MinShrinkSpec a m Q X →
      Γ "full_min_shrink_m6" [i64] [] a m Q X)
    (hTick : ∀ a m Q X, Full.fullTickRelSpec a m Q X → Γ "full_tick_rel" [i64] [] a m Q X)
    (hEma : ∀ a m Q X, Full.fullEmaUpdateSpec a m Q X →
      Γ "full_ema_update" [i64, i64] [] a m Q X)
    (hLearnM6 : ∀ a m Q X, step10LearnClauseM6Spec a m Q X →
      Γ "full_learn_clause_m6" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, FullM6Hdr.m6HdrAnalyzeSpec a m Q X →
      Func.wp Γ fidStep10AnalyzeCoreM6Fn.body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  rcases m6HdrAnalyzeSpec_elim hs with ⟨c, F0, F_cur, ext, s, R, rfl, hinv, hcf, hm, hQ⟩
  have hmaxv := c.hmaxv; have har_cap := c.harena; unfold dimacsBound at hmaxv har_cap
  have hcv_le := hinv.sparseW.1.core_ok.cur_vars_le
  let iter_lim : BitVec 64 := BitVec.ofNat 64 s.core.cur_vars + 64#64
  have hil_val : iter_lim.toNat = s.core.cur_vars + 64 := by
    change (BitVec.ofNat 64 s.core.cur_vars + 64#64).toNat = _
    rw [bv64_add_small_eq] <;> simp [BitVec.toNat_ofNat] <;> omega
  unfold Func.wp fidStep10AnalyzeCoreM6Fn full_analyze_core_m6_body; dsimp only
  refine wp_m6Hdr_focus_frame hm fun hm' => ?_; c0_hsteps_nogrp
  refine wp_while_state1 (α := BitVec 64 × FullState × List (BitVec 64)) (fun st => st.1)
    (fun st => iter_lim.toNat - st.1.toNat) (S10AnaCoreLoopInv c F0 F_cur s R iter_lim) ?_ ?_
  · intro J hJ; refine hJ (0#64, s, ext) m ⟨s.core.trail_end, Nat.le_refl _, hinv.sparseW.toCut,
      hcf.toCut hinv.sparseW.2.1, hinv.extOk, rfl, rfl, Nat.le_refl _, rfl, by simp, hm'⟩
  · intro J ⟨iter, s1, ext1⟩ m1
      ⟨cut1, hcut1_le, hcut1, hcf1, hext1, hcv1, hfu1, hcl1, hws1, hil1, hm1⟩ ih
    dsimp only at hcut1_le hcut1 hcf1 hext1 hcv1 hfu1 hcl1 hws1 hil1 hm1 ⊢
    c0_hsteps_nogrp
    · have hlt : iter.toNat < iter_lim.toNat := by
        simpa [iter_lim, BitVec.toNat_add, BitVec.toNat_ofNat] using hc
      have hcv_fit : (BitVec.ofNat 64 s1.core.cur_vars + 64#64).toNat = s1.core.cur_vars + 64 := by
        rw [hcv1]; exact hil_val
      c0_hsteps_nogrp; c0_call hOneLit
      refine ⟨c, F0, F_cur, cut1, s1, m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R,
        rfl, hcut1, hcf1, hm1, ?_⟩
      intro ol s2 m2 hlen2 hol hcv2 hfu2 hws2 h20 h1 h2 h0 hm2
      have hm2' := fullM6HdrMem_unfocus hm2
      rcases hol with rfl | rfl | rfl | rfl
      · rcases h0 rfl with ⟨cut2, hcut2_le, hcut2, hlvl2, hlle2, hcf2⟩
        c0_hsteps_nogrp
        · c0_call hFailed
          refine FullM6OrchAdapters.m6aAnaFailedLitSpecP_ofP hinv.cfgOk hext1 hcut2 hlvl2 hcf2 hm2'
            ?_
          intro r ext3 s3 m3 hext3 _ hlen3 hr hcv3 hfu3 hws3 hr20 hr0 hr1 hm3
          exact hQ r ext3 s3 m3 hext3 hlen3 hr (hcv3.trans (hcv2.trans hcv1))
            (by rw [hfu3, hfu2, hfu1]; exact Nat.le_refl _) ⟨hws3.trans (hws2.trans hws1),
              fun heq => by
                have ⟨_, ho, hcl, _hdm⟩ := hr20 heq
                exact ⟨ho, Nat.le_trans hcl (Nat.le_trans hlle2 hcl1),
                  ho.2.2.2.2.2.trans hinv.sparseW.2.2.2.2.2.symm⟩⟩
            (fun heq => (hr20 heq).1) hr0
            (fun heq => ⟨FullM6HdrInvW.mk_inv hinv.cfgOk hext3 (hr1 heq).1,
              Nat.lt_of_lt_of_le (hr1 heq).2 (Nat.le_trans hlle2 hcl1)⟩) hm3
        · c0_call hDeduce
          refine m7Deduce1uipHdrSpec_of hinv.cfgOk hext1 hcut2 hlvl2 hcf2 hm2' ?_
          intro dst ext3 s3 m3 hext3 hlen3 hdst hcv3 hfu3 hws3 hr20 hr0 hr1 hr2 hm3
          rcases hdst with rfl | rfl | rfl | rfl
          · c0_hsteps_nogrp
            exact hQ 0#64 ext3 s3 m3 hext3 hlen3 (Or.inl rfl) (hcv3.trans (hcv2.trans hcv1))
              (by rw [hfu3, hfu2, hfu1]; exact Nat.le_refl _) ⟨hws3.trans (hws2.trans hws1),
                fun h => by cases h⟩
              (fun h => by cases h) hr0 (fun h => by cases h) hm3
          · rcases hr1 rfl with ⟨ho3, hcl3, htl_ge, htl_le, hnd3, hvals3, hlvl3, _hlvl0, hent3⟩
            refine wp_m6Hdr_focus_frame hm3 fun hm3f => ?_; c0_hsteps_nogrp; c0_call hMinShrink
            refine m8MinShrinkSpec_of hlen3 ho3.2.1 ho3.2.2.1 htl_ge htl_le hnd3
              hent3 hvals3 hlvl3 _hlvl0 hm3f
              (fun tmp4 tl4 mrk4 mclr4 sstk4 wsort4 mcl4 mcf4 conf4 llits4 mrem4 ticks4 m4
                hlen4 ho4 hmc4 htl4_ge htl4_le htmp04 hnd4 h4lits hent4 hm4 => ?_)
            let s4 := m8MinShrinkState s3 tmp4 tl4 mrk4 mclr4 sstk4 wsort4
              mcl4 mcf4 conf4 llits4 mrem4 ticks4
            have hotfs4 : FullOtfsInvW c F0 F_cur s4 :=
              ⟨hlen4, ho4, hmc4, ho3.2.2.2.1,
                FullExtScratchOk.of_pres ho3.2.2.2.2.1 ⟨rfl, rfl⟩ (fun _ hr => hr),
                ho3.2.2.2.2.2⟩
            have h4v : ∀ k < tl4, let l := (tmp4[k]?.getD 0#32).toNat
                l < 2 * s4.core.cur_vars ∧ s4.core.vals[l]?.getD 0#8 = 255#8 := fun k hk => by
              by_cases hk0 : k = 0
              · subst hk0
                simpa [s4, htmp04] using hvals3 0 (Nat.lt_of_lt_of_le Nat.zero_lt_one htl_ge)
              · exact ⟨(h4lits k (Nat.pos_of_ne_zero hk0) hk).1,
                  (h4lits k (Nat.pos_of_ne_zero hk0) hk).2.1⟩
            have hm4' := fullM6HdrMem_unfocus hm4
            c0_hsteps_nogrp
            refine wp_join_state0 (α := FullState × List (BitVec 64))
              (fun st m' => S10AnaCoreShrinkPost c F0 F_cur s st.1 ∧ M6HdrExtOk st.2 ∧
                (FullM6HdrMem c st.2 st.1 ⋆ R) m') ?_ ?_
            · rintro J4 ⟨s5, ext5⟩ m5 ⟨⟨ho5, hpos5, htl5_ge, htl5_le, hnd5, hvals5, hlvl5,
                hent5, hcv5, hfu5, hcl5, hws5⟩, hext5, hm5⟩
              dsimp only at ho5 hpos5 htl5_ge htl5_le hnd5 hvals5 hlvl5
              dsimp only at hent5 hcv5 hfu5 hcl5 hws5 hext5 hm5 ⊢
              refine wp_m6Hdr_focus_frame hm5 fun hm5f => ?_
              have htl5_arr := ho5.1.core_ok.tmp_len_arr; have hcv5_le := ho5.1.core_ok.cur_vars_le
              have hcv5_b : s5.core.cur_vars < 2 * 2 ^ 28 := Nat.lt_of_le_of_lt hcv5_le hmaxv
              have htl5_max : s5.core.tmp_len < 2 * 2 ^ 28 := Nat.lt_of_le_of_lt htl5_le hcv5_b
              have htl5_fit : s5.core.tmp_len < 2 ^ 64 := by omega
              c0_hsteps_nogrp
              refine wp_while_state_pure (α := BitVec 64 × BitVec 64 × BitVec 32)
                (fun st => (st.2.1, st.2.2, st.1, ())) (fun st => s5.core.tmp_len - st.1.toNat)
                (fun st => 1 ≤ st.1.toNat ∧ st.1.toNat ≤ s5.core.tmp_len) ?_ ?_
              · intro J5 hJ5; exact hJ5 (1#64, 0#64, 0#32) ⟨by decide, htl5_ge⟩
              · intro J5 ⟨gi, glue, llvl⟩ ⟨hgi_lo, hgi_hi⟩ ih5
                dsimp only at hgi_lo hgi_hi ⊢; c0_hsteps_nogrp
                · have hgi_lt : gi.toNat < s5.core.tmp_len := by
                    simpa [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt htl5_fit] using hc
                  have hlt_arr : gi.toNat < s5.core.tmp.length := by rw [htl5_arr]; omega
                  have hl_lt : (s5.core.tmp[gi.toNat]'hlt_arr).toNat < 2 * s5.core.cur_vars := by
                    simpa [List.getElem?_eq_getElem hlt_arr] using (hvals5 gi.toNat hgi_lt).1
                  have hv_lt : (BitVec.setWidth 64
                      ((s5.core.tmp[gi.toNat]'hlt_arr) >>> 1#32)).toNat < s5.core.lvl.length := by
                    have hb : ((s5.core.tmp[gi.toNat]'hlt_arr) >>> 1#32).toNat =
                        (s5.core.tmp[gi.toNat]'hlt_arr).toNat / 2 := by
                      simpa using bv32_lshr_1 (s5.core.tmp[gi.toNat]'hlt_arr)
                    rw [ho5.1.core_ok.lvl_len, BitVec.toNat_setWidth, hb]
                    have hdiv : (s5.core.tmp[gi.toNat]'hlt_arr).toNat / 2 < s5.core.cur_vars := by
                      omega
                    rw [Nat.mod_eq_of_lt (by omega : (s5.core.tmp[gi.toNat]'hlt_arr).toNat / 2 <
                      2 ^ 64)]
                    exact Nat.lt_of_lt_of_le hdiv hcv5_le
                  have hgi_add1 : (gi + 1#64).toNat = gi.toNat + 1 :=
                    bv64_add_small_eq (by rw [show (1#64 : BitVec 64).toNat = 1 from rfl]; omega)
                  c0_hsteps
                  · exact ih5 (gi + 1#64, glue + 1#64, s5.core.lvl[(BitVec.setWidth 64
                        ((s5.core.tmp[gi.toNat]'hlt_arr) >>> 1#32)).toNat]'hv_lt)
                      (by dsimp only; rw [hgi_add1]; omega)
                      ⟨by dsimp only; rw [hgi_add1]; omega, by dsimp only; rw [hgi_add1]; omega⟩
                  · exact ih5 (gi + 1#64, glue, llvl) (by dsimp only; rw [hgi_add1]; omega)
                      ⟨by dsimp only; rw [hgi_add1]; omega, by dsimp only; rw [hgi_add1]; omega⟩
                · refine wp_join_state0 (α := FullState)
                    (fun s6 m' => S10AnaCoreShrinkPost c F0 F_cur s s6 ∧
                      (FullMem c s6 ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext5 ⋆ R)) m') ?_ ?_
                  · rintro J6 s6 m6 ⟨⟨ho6, hpos6, htl6_ge, htl6_le, hnd6, hvals6, hlvl6,
                      hent6, hcv6, hfu6, hcl6, hws6⟩, hm6⟩
                    c0_hsteps_nogrp; c0_call hLearnM6
                    refine step10LearnClauseM6Spec_of hinv.cfgOk hext5 ho6 hpos6 htl6_ge htl6_le
                      hnd6 hvals6 hlvl6 hent6 (fullM6HdrMem_unfocus hm6) ?_
                    intro r ext7 s7 m7 hext7 hlen7 hr hcv7 hfu7 hws7 h20_7 h0_7 h1_7 hm7
                    exact hQ r ext7 s7 m7 hext7 hlen7 hr (hcv7.trans hcv6)
                      (Nat.le_trans hfu7 (by rw [hfu6]; exact Nat.le_refl _))
                      ⟨hws7.trans hws6, fun h => let ⟨_, hsp, hcl⟩ := h20_7 h
                        ⟨hsp.toOtfs, Nat.le_trans (Nat.le_of_lt hcl) hcl6,
                          hsp.2.2.2.2.2.trans hinv.sparseW.2.2.2.2.2.symm⟩⟩
                      (fun h => (h20_7 h).1) (fun h => (h0_7 h).toOtfs)
                      (fun h => ⟨FullM6HdrInvW.mk_inv hinv.cfgOk hext7 (h1_7 h).1,
                        Nat.lt_of_lt_of_le (h1_7 h).2 hcl6⟩) hm7
                  · intro J6 hJ6; c0_hsteps_nogrp
                    · c0_call hEma
                      refine ⟨c, s5, m6ExtMem (m6ExtAddr c.hdr) ext5 ⋆ R, rfl, ho5.1, hm5f, ?_⟩
                      rintro ⟨⟩ s6 m6 hcore6 hlen6 hpres6 hm6
                      have heq6 := fullCoreState_agrees_with_scratch hcore6
                      exact hJ6 s6 m6 ⟨⟨m8Ana_fullOtfsInvW_of_safetySlice ho5 hlen6 hcore6
                          hpres6.1,
                        by change 0 < s6.core.cur_level; rw [heq6]; exact hpos5,
                        by rw [heq6]; exact htl5_ge, by rw [heq6]; exact htl5_le,
                        by rw [heq6]; exact hnd5, by rw [heq6]; exact hvals5,
                        by rw [heq6]; exact hlvl5, by rw [heq6]; exact hent5,
                        by rw [heq6]; exact hcv5, by rw [heq6]; exact hfu5,
                        by change s6.core.cur_level ≤ _; rw [heq6]; exact hcl5,
                        hpres6.2.2.1.trans hws5⟩, hm6⟩
                    · exact hJ6 s5 m5 ⟨⟨ho5, hpos5, htl5_ge, htl5_le, hnd5, hvals5, hlvl5,
                        hent5, hcv5, hfu5, hcl5, hws5⟩, hm5f⟩
            · intro J4 hJ4
              let mkShk : ∀ {s' : FullState}, FullOtfsInvW c F0 F_cur s' → 0 < s'.core.cur_level →
                  1 ≤ s'.core.tmp_len → s'.core.tmp_len ≤ s'.core.cur_vars →
                  (List.map (fun x => x.toNat / 2)
                    (List.take s'.core.tmp_len s'.core.tmp)).Nodup →
                  (∀ k < s'.core.tmp_len, let l := (s'.core.tmp[k]?.getD 0#32).toNat
                    l < 2 * s'.core.cur_vars ∧ s'.core.vals[l]?.getD 0#8 = 255#8) →
                  (∀ k, 1 ≤ k → k < s'.core.tmp_len →
                    let lv := (s'.core.lvl[(s'.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
                    0 < lv ∧ lv < s'.core.cur_level ∧
                    lv ≤ (s'.core.lvl[(s'.core.tmp[s'.core.tmp_len - 1]?.getD 0#32).toNat / 2]?.getD
                      0#32).toNat) →
                  (cnfOfClauses F_cur).EntailsClause
                    (cnfClause (List.map BitVec.toNat (List.take s'.core.tmp_len s'.core.tmp))) →
                  s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
                  s'.core.cur_level ≤ s.core.cur_level →
                  s'.scratch.work_stk2 = s.scratch.work_stk2 →
                  S10AnaCoreShrinkPost c F0 F_cur s s' :=
                fun ho hp h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
                  ⟨ho, hp, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
              c0_hsteps_nogrp
              · c0_call hRestore
                refine FullM6OrchAdapters.m6aRestoreBumpAnaSpecP_ofP hinv.cfgOk hext3 hlen4 hmc4.1
                  hm4' ?_
                intro mrk5 mcl5 sc5 ext5 m5 _s5 hlen5 hmz5 _ _ hpres5 hws5 hext5 _ hm5
                let s5 : FullState :=
                  { core := { s4.core with mrk := mrk5, min_clr_len := mcl5 }, scratch := sc5 }
                have ho5 := m8Ana_fullOtfsInvW_of_restoreBump hotfs4 hlen5 hmz5 hpres5
                refine wp_m6Hdr_focus_frame hm5 fun hm5f => ?_; c0_hsteps_nogrp; c0_call hTick
                refine ⟨c, s5, m6ExtMem (m6ExtAddr c.hdr) ext5 ⋆ R, rfl, hlen5, hm5f, ?_⟩
                rintro ⟨⟩ s6 m6 hcore6 hlen6 hpres6 hm6
                have heq6 := fullCoreState_agrees_with_scratch hcore6
                exact hJ4 (s6, ext5) m6 ⟨mkShk (m8Ana_fullOtfsInvW_of_safetySlice ho5 hlen6 hcore6
                    hpres6.1)
                  (by change 0 < s6.core.cur_level; rw [heq6]; change 0 < s3.core.cur_level; omega)
                  (by rw [heq6]; exact htl4_ge) (by rw [heq6]; exact Nat.le_trans htl4_le htl_le)
                  (by rw [heq6]; exact hnd4) (by rw [heq6]; exact h4v)
                  (fun k hk1 hk2 => by rw [heq6] at hk2 ⊢; exact (h4lits k hk1 hk2).2.2)
                  (by rw [heq6]; exact hent4)
                  (by change s6.core.cur_vars = _; rw [heq6]; exact hcv3.trans (hcv2.trans hcv1))
                  (by change s6.core.fuel = _; rw [heq6]; rw [hfu3, hfu2, hfu1])
                  (by change s6.core.cur_level ≤ _; rw [heq6, hcl3]; exact Nat.le_trans hlle2 hcl1)
                  (hpres6.2.2.1.trans (hws5.trans (hws3.trans (hws2.trans hws1)))),
                  hext5, fullM6HdrMem_unfocus hm6⟩
              · exact hJ4 (s4, ext3) m4 ⟨mkShk hotfs4 (by change 0 < s3.core.cur_level; omega)
                  htl4_ge (Nat.le_trans htl4_le htl_le) hnd4 h4v
                    (fun k hk1 hk2 => (h4lits k hk1 hk2).2.2)
                  hent4 (hcv3.trans (hcv2.trans hcv1)) (by rw [hfu3, hfu2, hfu1])
                  (by rw [hcl3]; exact Nat.le_trans hlle2 hcl1)
                  (hws3.trans (hws2.trans hws1)), hext3, hm4'⟩
          · rcases hr2 rfl with ⟨cut3, hcut3_le, hcut3, hcl3, hcf3⟩
            refine wp_m6Hdr_focus_frame hm3 fun hm3f => ?_; c0_hsteps_nogrp
            have hcut3k := m8Ana_fullCutInvW_with_conflicts hcut3 (s3.scratch.conflicts + 1#64)
            have hcf3k := hcf3
            let s3k : FullState :=
              { s3 with scratch := { s3.scratch with conflicts := s3.scratch.conflicts + 1#64 } }
            refine wp_join_state0 (α := FullState × List (BitVec 64))
              (fun st m' => S10AnaCoreCutJoin c F0 F_cur cut3 s st.1 ∧ M6HdrExtOk st.2 ∧
                (FullM6HdrMem c st.2 st.1 ⋆ R) m') ?_ ?_
            · rintro J4 ⟨s5, ext5⟩ m5 ⟨⟨hcut5_le, hcut5, hcf5, hcv5, hfu5, hcl5, hws5⟩, hext5, hm5⟩
              dsimp only at hcut5_le hcut5 hcf5 hcv5 hfu5 hcl5 hws5 hext5 hm5 ⊢
              refine wp_m6Hdr_focus_frame hm5 fun hm5f => ?_
              c0_hsteps_nogrp
              exact ih (iter + 1#64, s5, ext5) m5 (bv64_measure_sub_lt hlt)
                ⟨cut3, hcut5_le, hcut5, hcf5, hext5, hcv5, hfu5, hcl5, hws5,
                 by rw [bv64_add1_toNat hlt]; exact hlt, hm5f⟩
            · intro J4 hJ4; c0_hsteps_nogrp
              · refine wp_join_state0 (α := FullState)
                  (fun st m' => S10AnaCoreCutJoin c F0 F_cur cut3 s st ∧
                    (FullMem c st ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext3 ⋆ R)) m') ?_ ?_
                · rintro J5 s4 m4 ⟨⟨hcut4_le, hcut4, hcf4, hcv4, hfu4, hcl4, hws4⟩, hm4⟩
                  c0_hsteps_nogrp; c0_call hRestore
                  refine FullM6OrchAdapters.m6aRestoreBumpAnaSpecP_ofP hinv.cfgOk hext3 hcut4.1
                    hcut4.2.2.1.1 (fullM6HdrMem_unfocus hm4) ?_
                  intro mrk5 mcl5 sc5 ext5 m5 _s5 hlen5 hmz5 _ _ hpres5 hws5 hext5 _ hm5
                  let s5 : FullState :=
                    { core := { s4.core with mrk := mrk5, min_clr_len := mcl5 }, scratch := sc5 }
                  have hcut5 := m8Ana_fullCutInvW_of_restoreBump hcut4 hlen5 hmz5 hpres5
                  have hcf5 := hcf4
                  exact hJ4 (s5, ext5) m5
                    ⟨⟨hcut4_le, hcut5, hcf5, hcv4, hfu4, hcl4, hws5.trans hws4⟩, hext5, hm5⟩
                · intro J5 hJ5
                  have hJ_s3k : ∀ m',
                      (FullMem c s3k ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext3 ⋆ R)) m' →
                      J5 () m' := fun m' hm' =>
                    hJ5 s3k m' ⟨⟨hcut3_le, hcut3k, hcf3k, hcv3.trans (hcv2.trans hcv1),
                      by rw [hfu3, hfu2, hfu1], by rw [hcl3]; exact Nat.le_trans hlle2 hcl1,
                      hws3.trans (hws2.trans hws1)⟩, hm'⟩
                  c0_hsteps_nogrp
                  · have hpos3 : 0 < s3k.core.cur_vars := by
                      change 0 < s3.core.cur_vars
                      have : s3.core.cur_vars < 2 ^ 64 := by omega
                      simpa [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt this] using hc
                    have htl0 : (0#64 : BitVec 64).toNat < s3k.core.tmp.length := by
                      rw [hcut3k.1.core_ok.tmp_len_arr]
                      exact Nat.lt_of_lt_of_le hpos3 (by
                        change s3.core.cur_vars ≤ c.max_vars; rw [hcv3, hcv2, hcv1]; exact hcv_le)
                    have hJ_tmp : ∀ {tp' : List (BitVec 32)} {m'} (htp' : tp'.length = c.max_vars),
                        (FullMem c { s3k with core := { s3k.core with
                          tmp := tp', tmp_len := (1#64 : BitVec 64).toNat } } ⋆
                          (m6ExtMem (m6ExtAddr c.hdr) ext3 ⋆ R)) m' → J5 () m' := by
                      intro tp' m' htp' hm'
                      have htw :=
                        (⟨m8Ana_fullCutInvW_with_tmp_tl hcut3k tp' (1#64 : BitVec 64).toNat
                            htp' (by rw [show (1#64 : BitVec 64).toNat = 1 from rfl]; omega),
                          hcf3k⟩ :
                          FullCutInvW c F0 F_cur cut3
                            { s3k with core :=
                              { s3k.core with tmp := tp', tmp_len := (1#64 : BitVec 64).toNat } } ∧
                          FullConflictOkCut F_cur cut3
                            { s3k with core :=
                              { s3k.core with tmp := tp', tmp_len := (1#64 : BitVec 64).toNat } })
                      refine hJ5 _ m' ⟨?_, hm'⟩
                      exact ⟨hcut3_le, htw.1, htw.2, hcv3.trans (hcv2.trans hcv1),
                        by rw [hfu3, hfu2, hfu1], by rw [hcl3]; exact Nat.le_trans hlle2 hcl1,
                        hws3.trans (hws2.trans hws1)⟩
                    refine wp_unroll_group fun Jlit hJlit => ?_; c0_hsteps_nogrp
                    · exact hJ_tmp
                        (by simpa [List.length_set] using hcut3k.1.core_ok.tmp_len_arr) hm
                    · refine wp_unroll_group fun Js hJs => ?_
                      have har_len := hcut3k.1.core_ok.arena_len_arr
                      have har_le := hcut3k.1.core_ok.arena_len_le
                      c0_hsteps_nogrp
                      · rename_i hlt_ar; dsimp only [s3k] at har_len har_le
                        have href_lt : s3.core.confl_ref.toNat < s3.core.arena_len := by
                          simpa [BitVec.lt_def, BitVec.toNat_ofNat,
                            Nat.mod_eq_of_lt (by omega : s3.core.arena_len < 2 ^ 64)] using hlt_ar
                        have hsub_lt : 3 < s3.core.arena_len - s3.core.confl_ref.toNat := by
                          have hc' : 3 < (2 ^ 64 - s3.core.confl_ref.toNat +
                              s3.core.arena_len) % 2 ^ 64 := hc
                          omega
                        have har_lt : (s3k.core.confl_ref + 3#64).toNat <
                            s3k.core.arena.length := by
                          dsimp only [s3k]; rw [bv64_add_small_eq (by simp; omega)]; simp; omega
                        c0_hsteps_nogrp
                        exact hJ_tmp
                            (by simpa [List.length_set] using hcut3k.1.core_ok.tmp_len_arr) hm
                      · exact hJ_s3k _ (by assumption)
                      · exact hJ_s3k _ (by assumption)
                      · exact hJ_s3k _ (by assumption)
                  · exact hJ_s3k _ (by assumption)
              · exact hJ4 (s3k, ext3) _ ⟨⟨hcut3_le, hcut3k, hcf3k,
                  hcv3.trans (hcv2.trans hcv1), by rw [hfu3, hfu2, hfu1],
                  by rw [hcl3]; exact Nat.le_trans hlle2 hcl1,
                  hws3.trans (hws2.trans hws1)⟩, hext3, fullM6HdrMem_unfocus (by assumption)⟩
          · rcases hr20 rfl with ⟨hu3, ho3, hcl3, _hdm3⟩
            c0_hsteps_nogrp
            exact hQ 20#64 ext3 s3 m3 hext3 hlen3 (Or.inr (Or.inr rfl))
              (hcv3.trans (hcv2.trans hcv1)) (by rw [hfu3, hfu2, hfu1]; exact Nat.le_refl _)
              ⟨hws3.trans (hws2.trans hws1),
                fun _ => ⟨ho3, Nat.le_trans hcl3 (Nat.le_trans hlle2 hcl1),
                  ho3.2.2.2.2.2.trans hinv.sparseW.2.2.2.2.2.symm⟩⟩
              (fun _ => hu3) (fun h => by cases h) (fun h => by cases h) hm3
      · c0_hsteps
        c0_hsplit
        · c0_hsteps
          let s2k : FullState :=
            { s2 with scratch := { s2.scratch with conflicts := s2.scratch.conflicts + 1#64 } }
          have h1s := h1 rfl
          have hlen2k : s2k.LengthsOk c :=
            ⟨hlen2.core_ok, fullScratch_lengthsOk_of_arr_len hlen2.scratch_ok
              rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
              rfl rfl rfl rfl⟩
          have hsp2k : FullSparseInvW c F0 F_cur s2k :=
            ⟨hlen2k, h1s.1.2.1, h1s.1.2.2.1, h1s.1.2.2.2.1,
              FullExtScratchOk.of_pres h1s.1.2.2.2.2.1 ⟨rfl, rfl⟩ (fun _ r => r),
              h1s.1.2.2.2.2.2⟩
          exact hQ 1#64 ext1 s2k _ hext1 hlen2k (Or.inr (Or.inl rfl)) (hcv2.trans hcv1)
            (by rw [hfu2, hfu1]; exact Nat.le_refl _) ⟨hws2.trans hws1, fun h => by cases h⟩
            (fun h => by cases h) (fun h => by cases h)
            (fun _ => ⟨FullM6HdrInvW.mk_inv hinv.cfgOk hext1 hsp2k,
              Nat.lt_of_lt_of_le h1s.2 hcl1⟩) (fullM6HdrMem_unfocus (by assumption))
        · c0_hsteps
          exact hQ 1#64 ext1 s2 m2 hext1 hlen2 (Or.inr (Or.inl rfl)) (hcv2.trans hcv1)
            (by rw [hfu2, hfu1]; exact Nat.le_refl _) ⟨hws2.trans hws1, fun h => by cases h⟩
            (fun h => by cases h) (fun h => by cases h)
            (fun _ => ⟨FullM6HdrInvW.mk_inv hinv.cfgOk hext1 (h1 rfl).1,
              Nat.lt_of_lt_of_le (h1 rfl).2 hcl1⟩) hm2'
      · c0_hsteps_nogrp
        exact hQ 0#64 ext1 s2 m2 hext1 hlen2 (Or.inl rfl) (hcv2.trans hcv1)
          (by rw [hfu2, hfu1]; exact Nat.le_refl _) ⟨hws2.trans hws1, fun h => by cases h⟩
          (fun h => by cases h) (fun _ => h2 rfl) (fun h => by cases h) hm2'
      · c0_hsteps_nogrp
        have ⟨hu2, ho2, hcl2, _hdm2⟩ := h20 rfl
        exact hQ 20#64 ext1 s2 m2 hext1 hlen2 (Or.inr (Or.inr rfl)) (hcv2.trans hcv1)
          (by rw [hfu2, hfu1]; exact Nat.le_refl _) ⟨hws2.trans hws1,
            fun _ => ⟨ho2, Nat.le_trans hcl2 hcl1,
              ho2.2.2.2.2.2.trans hinv.sparseW.2.2.2.2.2.symm⟩⟩
          (fun _ => hu2) (fun h => by cases h) (fun h => by cases h) hm2'
    · c0_hsteps_nogrp
      exact hQ 0#64 ext1 s1 m1 hext1 hcut1.1 (Or.inl rfl) hcv1
        (by rw [hfu1]; exact Nat.le_refl _)
        ⟨hws1, fun h => by cases h⟩ (fun h => by cases h)
        (fun _ => hcut1.toOtfs) (fun h => by cases h) (fullM6HdrMem_unfocus hm1)

end LeanQbe.T.Examples.Kissat.FullFidelityStep10

end
