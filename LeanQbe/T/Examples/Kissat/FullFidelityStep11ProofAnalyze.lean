/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep11
public import LeanQbe.T.Examples.Kissat.FullFidelityStep10ProofLearn
public import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofAnalyze0
public import LeanQbe.T.Examples.Kissat.FullM7AnalyzeHdrProof
public import LeanQbe.T.Examples.Kissat.FullM7FidelitySchedFixProof
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
# Kissat Fidelity Step 11 PR 1: Analyze & Preprocess Proofs (`FullFidelityStep11ProofAnalyze`)

UNSAT-only `Func.wp` proofs (`public section`, `0` `@[expose]` on theorems/lemmas, `0` `import all`,
`std3`, `XPost`-polymorphic) for three Step-11 PR 1 `S11-2` probing-counter-guarded functions:
1. `full_analyze_core_m6_step11_wp` (`FullM6Hdr.m6HdrAnalyzeSpec`): guards OTFS `h->conflicts++`
   with `h->probing == 0ULL` while preserving Step 10's `full_learn_clause_m6` call.
2. `full_analyze_step11_wp` (`Full.fullAnalyzeSpec`): guards OTFS `h->conflicts++` with
   `h->probing == 0ULL` against `m8MinShrinkSpec`.
3. `full_preprocess_m6_step11_wp` (`FullM6.fullM6PreprocessSpec`): saves and restores
   `h->search_ticks` across `full_lucky(h)`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep11

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open scoped LeanQbe.T.ProofUtil
open Kraken.Bedrock2.Test
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open LeanQbe.T.Examples.Kissat.FullM5HeurCore
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open scoped LeanQbe.T.Examples.Kissat.FullM6ProofUtil.M6ProofUtilTactics
open LeanQbe.T.Examples.Kissat.FullM7Proof
open LeanQbe.T.Examples.Kissat.FullM8CoreParity
open LeanQbe.T.Examples.Kissat.FullFidelityStep10

/-! ## 1. `full_analyze_core_m6_step11_wp` (`FullM6Hdr.m6HdrAnalyzeSpec`) -/

section AnalyzeCoreStep11

private def S11AnaCoreLoopInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s : FullState) (R : Mem 64 → Prop) (iter_lim : BitVec 64)
    (st : BitVec 64 × FullState × List (BitVec 64)) (m' : Mem 64) : Prop :=
  ∃ cut', cut' ≤ st.2.1.core.trail_end ∧ FullCutInvW c F0 F_cur cut' st.2.1 ∧
    FullConflictOkCut F_cur cut' st.2.1 ∧ M6HdrExtOk st.2.2 ∧
    st.2.1.core.cur_vars = s.core.cur_vars ∧ st.2.1.core.fuel = s.core.fuel ∧
    st.2.1.core.cur_level ≤ s.core.cur_level ∧ st.2.1.scratch.work_stk2 = s.scratch.work_stk2 ∧
    st.1.toNat ≤ iter_lim.toNat ∧
    (FullMem c st.2.1 ⋆ (m6ExtMem (m6ExtAddr c.hdr) st.2.2 ⋆ R)) m'

private def S11AnaCoreShrinkPost (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
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

private def S11AnaCoreCutJoin (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (cut3 : Nat) (s : FullState) (s' : FullState) : Prop :=
  cut3 ≤ s'.core.trail_end ∧ FullCutInvW c F0 F_cur cut3 s' ∧
  FullConflictOkCut F_cur cut3 s' ∧
  s'.core.cur_vars = s.core.cur_vars ∧ s'.core.fuel = s.core.fuel ∧
  s'.core.cur_level ≤ s.core.cur_level ∧ s'.scratch.work_stk2 = s.scratch.work_stk2

end AnalyzeCoreStep11

/-- Step-11 transparent-bridge specification for `full_deduce_1uip_m6_hdr` matching canonical
`m7Deduce1uipHdrSpec` / `m6Deduce1uipHdrSpec` (`0` `@[expose]`, paired `_of`/`_elim`). -/
def s11Deduce1uipHdrSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ c F0 F_cur cut ext s R, h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧
    FullCutInvW c F0 F_cur cut s ∧ 0 < s.core.cur_level ∧ FullConflictOkCut F_cur cut s ∧
    (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ (r : BitVec 64) (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
      M6HdrExtOk ext' → s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (r = 20#64 → F0.Unsat ∧ FullOtfsInvW c F0 F_cur s' ∧
        s'.core.cur_level ≤ s.core.cur_level ∧ s'.core.dense_mode = s.core.dense_mode) →
      (r = 0#64 → FullOtfsInvW c F0 F_cur s') →
      (r = 1#64 → FullOtfsInvW c F0 F_cur s' ∧ s'.core.cur_level = s.core.cur_level ∧
        1 ≤ s'.core.tmp_len ∧ s'.core.tmp_len ≤ s'.core.cur_vars ∧
        (List.map (fun x => x.toNat / 2) (List.take s'.core.tmp_len s'.core.tmp)).Nodup ∧
        (∀ k, k < s'.core.tmp_len → let l := (s'.core.tmp[k]?.getD 0#32).toNat
          l < 2 * s'.core.cur_vars ∧ s'.core.vals[l]?.getD 0#8 = 255#8) ∧
        (∀ k, 1 ≤ k → k < s'.core.tmp_len →
          let lv := (s'.core.lvl[(s'.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
          0 < lv ∧ lv < s'.core.cur_level) ∧
        (s'.core.lvl[(s'.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = s'.core.cur_level ∧
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause (List.map BitVec.toNat (List.take s'.core.tmp_len s'.core.tmp)))) →
      (r = 2#64 → ∃ cut', cut' ≤ s'.core.trail_end ∧ FullCutInvW c F0 F_cur cut' s' ∧
        s'.core.cur_level = s.core.cur_level ∧ FullConflictOkCut F_cur cut' s') →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

theorem s11Deduce1uipHdrSpec_monoX {xs : Tup Val [i64]} {m : Mem 64}
    {Q : Post [i64]} {X X' : XPost} (h : s11Deduce1uipHdrSpec xs m Q X) :
    s11Deduce1uipHdrSpec xs m Q X' := by
  rcases xs with ⟨_, ⟨⟩⟩; exact h

theorem s11Deduce1uipHdrSpec_of {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {ext : List (BitVec 64)} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext) (hcut : FullCutInvW c F0 F_cur cut s)
    (hlvl : 0 < s.core.cur_level) (hcf : FullConflictOkCut F_cur cut s)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ (r : BitVec 64) (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
      M6HdrExtOk ext' → s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (r = 20#64 → F0.Unsat ∧ FullOtfsInvW c F0 F_cur s' ∧
        s'.core.cur_level ≤ s.core.cur_level ∧ s'.core.dense_mode = s.core.dense_mode) →
      (r = 0#64 → FullOtfsInvW c F0 F_cur s') →
      (r = 1#64 → FullOtfsInvW c F0 F_cur s' ∧ s'.core.cur_level = s.core.cur_level ∧
        1 ≤ s'.core.tmp_len ∧ s'.core.tmp_len ≤ s'.core.cur_vars ∧
        (List.map (fun x => x.toNat / 2) (List.take s'.core.tmp_len s'.core.tmp)).Nodup ∧
        (∀ k, k < s'.core.tmp_len → let l := (s'.core.tmp[k]?.getD 0#32).toNat
          l < 2 * s'.core.cur_vars ∧ s'.core.vals[l]?.getD 0#8 = 255#8) ∧
        (∀ k, 1 ≤ k → k < s'.core.tmp_len →
          let lv := (s'.core.lvl[(s'.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
          0 < lv ∧ lv < s'.core.cur_level) ∧
        (s'.core.lvl[(s'.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
          s'.core.cur_level ∧
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause (List.map BitVec.toNat (List.take s'.core.tmp_len s'.core.tmp)))) →
      (r = 2#64 → ∃ cut', cut' ≤ s'.core.trail_end ∧ FullCutInvW c F0 F_cur cut' s' ∧
        s'.core.cur_level = s.core.cur_level ∧ FullConflictOkCut F_cur cut' s') →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m') :
    s11Deduce1uipHdrSpec (c.hdr, ()) m Q X :=
  ⟨c, F0, F_cur, cut, ext, s, R, rfl, hcfg, hext, hcut, hlvl, hcf, hm, hQ⟩

theorem s11Deduce1uipHdrSpec_elim {h : BitVec 64} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (hs : s11Deduce1uipHdrSpec (h, ()) m Q X) :
    ∃ c F0 F_cur cut ext s R, h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧
      FullCutInvW c F0 F_cur cut s ∧ 0 < s.core.cur_level ∧ FullConflictOkCut F_cur cut s ∧
      (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ (r : BitVec 64) (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
        M6HdrExtOk ext' → s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) →
        s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
        s'.scratch.work_stk2 = s.scratch.work_stk2 →
        (r = 20#64 → F0.Unsat ∧ FullOtfsInvW c F0 F_cur s' ∧
          s'.core.cur_level ≤ s.core.cur_level ∧ s'.core.dense_mode = s.core.dense_mode) →
        (r = 0#64 → FullOtfsInvW c F0 F_cur s') →
        (r = 1#64 → FullOtfsInvW c F0 F_cur s' ∧ s'.core.cur_level = s.core.cur_level ∧
          1 ≤ s'.core.tmp_len ∧ s'.core.tmp_len ≤ s'.core.cur_vars ∧
          (List.map (fun x => x.toNat / 2) (List.take s'.core.tmp_len s'.core.tmp)).Nodup ∧
          (∀ k, k < s'.core.tmp_len → let l := (s'.core.tmp[k]?.getD 0#32).toNat
            l < 2 * s'.core.cur_vars ∧ s'.core.vals[l]?.getD 0#8 = 255#8) ∧
          (∀ k, 1 ≤ k → k < s'.core.tmp_len →
            let lv := (s'.core.lvl[(s'.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
            0 < lv ∧ lv < s'.core.cur_level) ∧
          (s'.core.lvl[(s'.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
            s'.core.cur_level ∧
          (cnfOfClauses F_cur).EntailsClause
            (cnfClause (List.map BitVec.toNat (List.take s'.core.tmp_len s'.core.tmp)))) →
        (r = 2#64 → ∃ cut', cut' ≤ s'.core.trail_end ∧ FullCutInvW c F0 F_cur cut' s' ∧
          s'.core.cur_level = s.core.cur_level ∧ FullConflictOkCut F_cur cut' s') →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m' :=
  hs

private theorem full_analyze_core_m6_step11_aux (Γ : Env)
    (hOneLit : ∀ a m Q X, Full.fullOneLitConflSpec a m Q X →
      Γ "full_one_lit_confl" [i64] [i64] a m Q X)
    (hFailed : ∀ a m Q X, FullM6OrchAdapters.m6aAnaFailedLitSpecP M6ExtW2bPres a m Q X →
      Γ "full_ana_failed_lit_m6_hdr" [i64] [i64] a m Q X)
    (hDeduce : ∀ a m Q X, s11Deduce1uipHdrSpec a m Q X →
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
      Func.wp Γ fidStep11AnalyzeCoreM6Fn.body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  rcases m6HdrAnalyzeSpec_elim hs with ⟨c, F0, F_cur, ext, s, R, rfl, hinv, hcf, hm, hQ⟩
  have hmaxv := c.hmaxv; have har_cap := c.harena; unfold dimacsBound at hmaxv har_cap
  have hcv_le := hinv.sparseW.1.core_ok.cur_vars_le
  let iter_lim : BitVec 64 := BitVec.ofNat 64 s.core.cur_vars + 64#64
  have hil_val : iter_lim.toNat = s.core.cur_vars + 64 := by
    change (BitVec.ofNat 64 s.core.cur_vars + 64#64).toNat = _
    rw [bv64_add_small_eq] <;> simp [BitVec.toNat_ofNat] <;> omega
  unfold Func.wp fidStep11AnalyzeCoreM6Fn full_analyze_core_m6_body; dsimp only
  refine wp_m6Hdr_focus_frame hm fun hm' => ?_; c0_hsteps_nogrp
  refine wp_while_state1 (α := BitVec 64 × FullState × List (BitVec 64)) (fun st => st.1)
    (fun st => iter_lim.toNat - st.1.toNat) (S11AnaCoreLoopInv c F0 F_cur s R iter_lim) ?_ ?_
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
          refine s11Deduce1uipHdrSpec_of hinv.cfgOk hext1 hcut2 hlvl2 hcf2 hm2' ?_
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
              (fun st m' => S11AnaCoreShrinkPost c F0 F_cur s st.1 ∧ M6HdrExtOk st.2 ∧
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
                    (fun s6 m' => S11AnaCoreShrinkPost c F0 F_cur s s6 ∧
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
                  S11AnaCoreShrinkPost c F0 F_cur s s' :=
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
            refine wp_join_state0 (α := FullState × List (BitVec 64))
              (fun st m' => S11AnaCoreCutJoin c F0 F_cur cut3 s st.1 ∧ M6HdrExtOk st.2 ∧
                (FullM6HdrMem c st.2 st.1 ⋆ R) m') ?_ ?_
            · rintro J4 ⟨s5, ext5⟩ m5 ⟨⟨hcut5_le, hcut5, hcf5, hcv5, hfu5, hcl5, hws5⟩, hext5, hm5⟩
              dsimp only at hcut5_le hcut5 hcf5 hcv5 hfu5 hcl5 hws5 hext5 hm5 ⊢
              refine wp_m6Hdr_focus_frame hm5 fun hm5f => ?_
              c0_hsteps_nogrp
              exact ih (iter + 1#64, s5, ext5) m5 (bv64_measure_sub_lt hlt)
                ⟨cut3, hcut5_le, hcut5, hcf5, hext5, hcv5, hfu5, hcl5, hws5,
                 by rw [bv64_add1_toNat hlt]; exact hlt, hm5f⟩
            · intro J4 hJ4; c0_hsteps_nogrp
              · c0_hsteps_nogrp
                have hcut3k := m8Ana_fullCutInvW_with_conflicts hcut3 (s3.scratch.conflicts + 1#64)
                have hcf3k := hcf3
                let s3k : FullState :=
                  { s3 with
                    scratch := { s3.scratch with conflicts := s3.scratch.conflicts + 1#64 } }
                refine wp_join_state0 (α := FullState)
                  (fun st m' => S11AnaCoreCutJoin c F0 F_cur cut3 s st ∧
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
              · exact hJ4 (s3, ext3) _ ⟨⟨hcut3_le, hcut3, hcf3,
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

/-- Parametric `Func.wp` proof for `fidStep11AnalyzeCoreM6Fn` against `s11Deduce1uipHdrSpec`. -/
theorem full_analyze_core_m6_step11_s11_wp (Γ : Env)
    (hOneLit : ∀ a m Q X, Full.fullOneLitConflSpec a m Q X →
      Γ "full_one_lit_confl" [i64] [i64] a m Q X)
    (hFailed : ∀ a m Q X, FullM6OrchAdapters.m6aAnaFailedLitSpecP M6ExtW2bPres a m Q X →
      Γ "full_ana_failed_lit_m6_hdr" [i64] [i64] a m Q X)
    (hDeduce : ∀ a m Q X, s11Deduce1uipHdrSpec a m Q X →
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
      Func.wp Γ fidStep11AnalyzeCoreM6Fn.body a m Q X :=
  full_analyze_core_m6_step11_aux Γ hOneLit hFailed hDeduce hRestore hMinShrink hTick hEma hLearnM6

/-- Parametric `Func.wp` proof for `fidStep11AnalyzeCoreM6Fn` (`full_analyze_core_m6` with
probing-guarded OTFS `conflicts++`) against `FullM6Hdr.m6HdrAnalyzeSpec`. -/
theorem full_analyze_core_m6_step11_wp (Γ : Env)
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
      Func.wp Γ fidStep11AnalyzeCoreM6Fn.body a m Q X :=
  full_analyze_core_m6_step11_aux Γ hOneLit hFailed (fun ⟨h, ⟨⟩⟩ m Q X hs => by
    rcases s11Deduce1uipHdrSpec_elim hs with
      ⟨c, F0, F_cur, cut, ext, s, R, rfl, hcfg, hext, hcut, hlvl, hcf, hm, hQ⟩
    exact hDeduce _ m Q X (m7Deduce1uipHdrSpec_of hcfg hext hcut hlvl hcf hm hQ))
    hRestore hMinShrink hTick hEma hLearnM6

/-! ## 2. `full_analyze_step11_wp` (`Full.fullAnalyzeSpec`) -/

/-- Canonical `Full.fullAnalyzeSpec` theorem for Step-11 `fidStep11AnalyzeFn` (`full_analyze` with
probing-guarded `conflicts++` in `ol == 1ULL` and `dst == 2ULL`, against `m8MinShrinkSpec`). -/
theorem full_analyze_step11_wp (Γ : Env)
    (hOneLit : ∀ a m Q X, Full.fullOneLitConflSpec a m Q X →
      Γ "full_one_lit_confl" [i64] [i64] a m Q X)
    (hDeduce : ∀ a m Q X, Full.fullDeduce1uipSpec a m Q X →
      Γ "full_deduce_1uip" [i64] [i64] a m Q X)
    (hRestoreBump : ∀ a m Q X, fullRestoreBumpAnaSpec a m Q X →
      Γ "full_restore_bump_ana_m5" [i64] [] a m Q X)
    (hMinShrink : ∀ a m Q X, m8MinShrinkSpec a m Q X →
      Γ "full_min_shrink" [i64] [] a m Q X)
    (hTickRel : ∀ a m Q X, Full.fullTickRelSpec a m Q X →
      Γ "full_tick_rel" [i64] [] a m Q X)
    (hEma : ∀ a m Q X, Full.fullEmaUpdateSpec a m Q X →
      Γ "full_ema_update" [i64, i64] [] a m Q X)
    (hLearnCl : ∀ a m Q X, Full.fullLearnClauseSpec a m Q X →
      Γ "full_learn_clause" [i64, i64] [i64] a m Q X) :
    ∀ args m Q X, Full.fullAnalyzeSpec args m Q X →
      Func.wp Γ fidStep11AnalyzeFn.body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hs, hconfl, hm, hQ⟩
  have hmv := c.hmaxv; unfold dimacsBound at hmv
  have hcl := hs.1.core_ok
  have hcv_le := hcl.cur_vars_le
  have hcur_le := hs.2.1.cur_level_le
  have hte_le := hcl.trail_end_le
  unfold Func.wp fidStep11AnalyzeFn full_analyze_body; dsimp only
  c0_hsplit
  · have hcl0 : s.core.cur_level = 0 := by bv_omega
    c0_hsteps
    exact hQ 20#64 s m hs.1 (Or.inr (Or.inr rfl)) rfl (Nat.le_refl _)
      ⟨rfl, fun _ => ⟨hs.toOtfs, Nat.le_refl _, rfl⟩⟩
      (fun _ => Full.level0_unsat_of_conflict_okW hs.2.1 hcl0 hconfl)
      (fun h => by cases h) (fun h => by cases h) hm
  · have hcur_pos : 0 < s.core.cur_level := by bv_omega
    have hlim_nat : (BitVec.ofNat 64 s.core.cur_vars + 64#64).toNat = s.core.cur_vars + 64 := by
      bv_omega
    c0_hsteps_nogrp
    refine wp_loop_group (ts := [i64])
      (fun rem (iter_v, ()) m_i =>
        ∃ iter cut s_i,
          iter ≤ s.core.cur_vars + 64 ∧ rem = s.core.cur_vars + 64 - iter ∧
          iter_v = BitVec.ofNat 64 iter ∧ cut ≤ s_i.core.trail_end ∧
          FullCutInvW c F0 F_cur cut s_i ∧ 0 < s_i.core.cur_level ∧
          s_i.core.cur_level ≤ s.core.cur_level ∧ FullConflictOkCut F_cur cut s_i ∧
          s_i.core.cur_vars = s.core.cur_vars ∧ s_i.core.fuel.toNat ≤ s.core.fuel.toNat ∧
          s_i.scratch.work_stk2 = s.scratch.work_stk2 ∧ (FullMem c s_i ⋆ R) m_i) ?_ ?_
    · rintro L rem ⟨iter_v, ⟨⟩⟩ m_i ih
        ⟨iter, cut, s_i, hiter_le, rfl, rfl, hcut_le, hcut_inv, hcl_pos_i, hcl_le_i,
          hconfl_i, hcv_i, hfu_i, hws2_i, hm_i⟩
      c0_hsplit
      · have hiter_lt : iter < s.core.cur_vars + 64 := by
          have hlt : iter % 2 ^ 64 < (s.core.cur_vars + (64#64 : BitVec 64).toNat) % 2 ^ 64 := by
            assumption
          rw [Nat.mod_eq_of_lt (by omega : iter < 2 ^ 64),
            show (64#64 : BitVec 64).toNat = 64 from rfl,
            Nat.mod_eq_of_lt (by omega : s.core.cur_vars + 64 < 2 ^ 64)] at hlt
          exact hlt
        have hiter1_eq : (BitVec.ofNat 64 iter + 1#64).toNat = iter + 1 := by
          rw [m8Ana_bv64_add1_toNat (by rw [bv64_ofNat_toNat (by omega)]; omega),
            bv64_ofNat_toNat (by omega)]
        have hiter1_bv : BitVec.ofNat 64 iter + 1#64 = BitVec.ofNat 64 (iter + 1) :=
          BitVec.eq_of_toNat_eq (by rw [hiter1_eq, bv64_ofNat_toNat (by omega)])
        c0_hsteps_nogrp; c0_call hOneLit
        refine ⟨c, F0, F_cur, cut, s_i, R, rfl, hcut_inv, hconfl_i, hm_i, ?_⟩
        intro ol s1 m1 h1_len hol_dom h1_cv h1_fu h1_ws2 h1_20 h1_1 h1_2 h1_0 hm1
        have h1_cv' : s1.core.cur_vars = s.core.cur_vars := h1_cv.trans hcv_i
        have h1_fu' : s1.core.fuel.toNat ≤ s.core.fuel.toNat := by rw [h1_fu]; exact hfu_i
        have h1_ws2' : s1.scratch.work_stk2 = s.scratch.work_stk2 := h1_ws2.trans hws2_i
        c0_hsplit
        · c0_hsteps
          obtain ⟨hu1, ho1, hcl1, hdm1⟩ := h1_20 (by assumption)
          exact hQ 20#64 s1 m1 h1_len (Or.inr (Or.inr rfl)) h1_cv' h1_fu'
            ⟨h1_ws2', fun _ => ⟨ho1, Nat.le_trans hcl1 hcl_le_i,
              hdm1.trans (hcut_inv.2.2.2.2.2.trans hs.2.2.2.2.2.symm)⟩⟩
            (fun _ => hu1) (fun h => by cases h) (fun h => by cases h) hm1
        · c0_hsplit
          · obtain ⟨h1_sp, h1_cl_lt⟩ := h1_1 (by assumption)
            c0_hsteps
            c0_hsplit
            · c0_hsteps
              let s1' : FullState :=
                { s1 with scratch := { s1.scratch with conflicts := s1.scratch.conflicts + 1#64 } }
              have h1_len' : s1'.LengthsOk c :=
                ⟨h1_len.core_ok, fullScratch_lengthsOk_of_arr_len h1_len.scratch_ok
                  rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
                  rfl rfl rfl rfl⟩
              have h1_sp' : FullSparseInvW c F0 F_cur s1' :=
                ⟨h1_len', h1_sp.2.1, h1_sp.2.2.1, h1_sp.2.2.2.1,
                  FullExtScratchOk.of_pres h1_sp.2.2.2.2.1 ⟨rfl, rfl⟩ (fun _ r => r),
                  h1_sp.2.2.2.2.2⟩
              exact hQ 1#64 s1' _ h1_len' (Or.inr (Or.inl rfl)) h1_cv' h1_fu'
                ⟨h1_ws2', fun h => by cases h⟩
                (fun h => by cases h) (fun h => by cases h)
                (fun _ => ⟨h1_sp', by dsimp only [s1']; omega⟩) (by assumption)
            · c0_hsteps
              exact hQ 1#64 s1 m1 h1_len (Or.inr (Or.inl rfl)) h1_cv' h1_fu'
                ⟨h1_ws2', fun h => by cases h⟩
                (fun h => by cases h) (fun h => by cases h)
                (fun _ => ⟨h1_sp, by omega⟩) hm1
          · c0_hsplit
            · c0_hsteps
              exact hQ 0#64 s1 m1 h1_len (Or.inl rfl) h1_cv' h1_fu'
                ⟨h1_ws2', fun h => by cases h⟩
                (fun h => by cases h) (fun _ => h1_2 (by assumption))
                (fun h => by cases h) hm1
            · have hol_0 : ol = 0#64 := by
                rcases hol_dom with rfl | rfl | rfl | rfl <;> first | rfl | contradiction
              obtain ⟨cut1, hcut1_le, hcut1_inv, hcl1_pos, hcl1_le, hconfl1⟩ := h1_0 hol_0
              have hcl1_le' : s1.core.cur_level ≤ s.core.cur_level := Nat.le_trans hcl1_le hcl_le_i
              c0_hsteps_nogrp; c0_call hDeduce
              refine ⟨c, F0, F_cur, cut1, s1, R, rfl, hcut1_inv, hcl1_pos, hconfl1, hm1, ?_⟩
              intro dst s2 m2 h2_len hdst_dom h2_cv h2_fu h2_ws2 h2_20 h2_0 h2_1 h2_2 hm2
              have h2_cv' : s2.core.cur_vars = s.core.cur_vars := h2_cv.trans h1_cv'
              have h2_fu' : s2.core.fuel.toNat ≤ s.core.fuel.toNat := by rw [h2_fu]; exact h1_fu'
              have h2_ws2' : s2.scratch.work_stk2 = s.scratch.work_stk2 := h2_ws2.trans h1_ws2'
              c0_hsplit
              · c0_hsteps
                obtain ⟨hu2, ho2, hcl2, hdm2⟩ := h2_20 (by assumption)
                exact hQ 20#64 s2 m2 h2_len (Or.inr (Or.inr rfl)) h2_cv' h2_fu'
                  ⟨h2_ws2', fun _ => ⟨ho2, Nat.le_trans hcl2 hcl1_le',
                    hdm2.trans (hcut1_inv.2.2.2.2.2.trans hs.2.2.2.2.2.symm)⟩⟩
                  (fun _ => hu2) (fun h => by cases h) (fun h => by cases h) hm2
              · c0_hsplit
                · c0_hsteps
                  exact hQ 0#64 s2 m2 h2_len (Or.inl rfl) h2_cv' h2_fu'
                    ⟨h2_ws2', fun h => by cases h⟩
                    (fun h => by cases h) (fun _ => h2_0 (by assumption))
                    (fun h => by cases h) hm2
                · c0_hsplit
                  · have hdst_2 : dst = 2#64 := by
                      rcases hdst_dom with rfl | rfl | rfl | rfl <;> first | rfl | contradiction
                    obtain ⟨cut2, hcut2_le, hcut2_inv, hcl2_eq, hconfl2⟩ := h2_2 hdst_2
                    c0_hsteps_nogrp
                    refine wp_join_group (ts := []) (fun _ m_rb =>
                      ∃ s_rb : FullState,
                        s_rb.core.trail_end ≥ cut2 ∧ FullCutInvW c F0 F_cur cut2 s_rb ∧
                        s_rb.core.cur_level = s2.core.cur_level ∧
                        FullConflictOkCut F_cur cut2 s_rb ∧
                        s_rb.core.cur_vars = s2.core.cur_vars ∧
                        s_rb.core.fuel = s2.core.fuel ∧
                        s_rb.scratch.work_stk2 = s2.scratch.work_stk2 ∧
                        (FullMem c s_rb ⋆ R) m_rb) ?_ ?_
                    · rintro _ ⟨⟩ m_rb
                        ⟨s_rb, hrb_cut, hrb_inv, hrb_cl, hrb_cf, hrb_cv, hrb_fu, hrb_ws2, hm_rb⟩
                      rw [Blocks.get_here]; try dsimp only
                      c0_hsteps
                      rw [show (1 : BitVec 64) = 1#64 from rfl, hiter1_bv]
                      exact ih (s.core.cur_vars + 64 - (iter + 1)) (BitVec.ofNat 64 (iter + 1), ())
                        m_rb (by omega)
                        ⟨iter + 1, cut2, s_rb, by omega, rfl, rfl, hrb_cut, hrb_inv,
                          by rw [hrb_cl, hcl2_eq]; exact hcl1_pos,
                          by rw [hrb_cl, hcl2_eq]; exact hcl1_le',
                          hrb_cf, hrb_cv.trans h2_cv', by rw [hrb_fu]; exact h2_fu',
                          hrb_ws2.trans h2_ws2', hm_rb⟩
                    · intro Jrb hJrb
                      c0_hsplit
                      · c0_hsteps_nogrp
                        let s2c : FullState :=
                          { s2 with
                            scratch :=
                              { s2.scratch with conflicts := s2.scratch.conflicts + 1#64 } }
                        have h2c_inv :=
                          m8Ana_fullCutInvW_with_conflicts hcut2_inv (s2.scratch.conflicts + 1#64)
                        refine wp_join_group (ts := []) (fun _ m_t =>
                          ∃ s_t : FullState,
                            cut2 ≤ s_t.core.trail_end ∧
                            FullCutInvW c F0 F_cur cut2 s_t ∧
                            s_t.core.cur_level = s2.core.cur_level ∧
                            FullConflictOkCut F_cur cut2 s_t ∧
                            s_t.core.cur_vars = s2.core.cur_vars ∧
                            s_t.core.fuel = s2.core.fuel ∧
                            s_t.scratch.work_stk2 = s2.scratch.work_stk2 ∧
                            (FullMem c s_t ⋆ R) m_t) ?_ ?_
                        · rintro _ ⟨⟩ m_t
                            ⟨s_t, ht_cut, ht_inv, ht_cl, ht_cf, ht_cv, ht_fu, ht_ws2, hm_t⟩
                          rw [Blocks.get_here]; try dsimp only
                          c0_hsteps_nogrp; c0_call hRestoreBump
                          refine ⟨c, s_t, R, rfl, ht_inv.1, ht_inv.2.2.1.1, hm_t, ?_⟩
                          intro mrk_r mcl_r sc_r m_r _ hlen_r hmrk_r hpres_r hws2_r hm_r
                          let s_rb : FullState :=
                            { core := { s_t.core with mrk := mrk_r, min_clr_len := mcl_r }
                              scratch := sc_r }
                          c0_hsteps
                          exact hJrb () m_r
                            ⟨s_rb, ht_cut,
                              m8Ana_fullCutInvW_of_restoreBump ht_inv hlen_r hmrk_r hpres_r,
                              ht_cl, ht_cf, ht_cv, ht_fu, hws2_r.trans ht_ws2, hm_r⟩
                        · intro Jt hJt
                          c0_hsplit
                          · have hcv_pos2 : 0 < s2.core.cur_vars := by bv_omega
                            have htmp_pos : 0 < s2c.core.tmp.length := by
                              rw [h2_len.core_ok.tmp_len_arr]
                              have := h2_len.core_ok.cur_vars_le; omega
                            have htl1_le : 1 ≤ c.max_vars := by
                              have := h2_len.core_ok.cur_vars_le; omega
                            c0_hsteps_nogrp
                            refine wp_unroll_group fun _ _ => ?_
                            c0_hsplit
                            · let lit0_32 := s2c.core.confl_lit0.setWidth 32
                              let s_t : FullState :=
                                { s2c with core :=
                                  { s2c.core with
                                    tmp := s2c.core.tmp.set 0 lit0_32, tmp_len := 1 } }
                              c0_hsteps
                              exact hJt () m
                                ⟨s_t, hcut2_le, m8Ana_fullCutInvW_with_tmp_tl h2c_inv _ 1
                                  (by simp [s2c, h2_len.core_ok.tmp_len_arr]) htl1_le,
                                  rfl, hconfl2, rfl, rfl, rfl,
                                  by simpa only [s_t, s2c, lit0_32,
                                    show (BitVec.ofNat 64 0).toNat = 0 from rfl,
                                    show (1#64 : BitVec 64) = 1 from rfl,
                                    show (1 : BitVec 64).toNat = 1 from rfl] using hm⟩
                            · c0_hsteps
                              all_goals first
                              | exact hJt () m ⟨s2c, hcut2_le, h2c_inv, rfl, hconfl2,
                                  rfl, rfl, rfl, hm⟩
                              | (have haca := c.harena; unfold dimacsBound at haca
                                 have hal_le := h2_len.core_ok.arena_len_le
                                 have hc3_lt : (s2c.core.confl_ref + 3#64).toNat <
                                     s2c.core.arena.length := by
                                   dsimp only [s2c]
                                   rw [h2_len.core_ok.arena_len_arr]; bv_omega
                                 let l_ar :=
                                   s2c.core.arena[(s2c.core.confl_ref + 3#64).toNat]'hc3_lt
                                 let s_t : FullState :=
                                   { s2c with core :=
                                     { s2c.core with
                                       tmp := s2c.core.tmp.set 0 l_ar, tmp_len := 1 } }
                                 c0_hsteps
                                 exact hJt () m
                                   ⟨s_t, hcut2_le, m8Ana_fullCutInvW_with_tmp_tl h2c_inv _ 1
                                     (by simp [s2c, h2_len.core_ok.tmp_len_arr]) htl1_le,
                                     rfl, hconfl2, rfl, rfl, rfl,
                                     by simpa only [s_t, s2c, l_ar,
                                       show (BitVec.ofNat 64 0).toNat = 0 from rfl,
                                       show (1#64 : BitVec 64) = 1 from rfl,
                                       show (3#64 : BitVec 64) = 3 from rfl,
                                       show (1 : BitVec 64).toNat = 1 from rfl] using hm⟩)
                          · c0_hsteps
                            exact hJt () m ⟨s2c, hcut2_le, h2c_inv, rfl, hconfl2,
                              rfl, rfl, rfl, hm⟩
                      · c0_hsteps
                        exact hJrb () m2 ⟨s2, hcut2_le, hcut2_inv, rfl, hconfl2,
                          rfl, rfl, rfl, hm2⟩
                  · have hdst_1 : dst = 1#64 := by
                      rcases hdst_dom with rfl | rfl | rfl | rfl <;> first | rfl | contradiction
                    obtain ⟨h2_otfs, h2_cl, h2_tl1, h2_tl_cv, h2_nd, h2_vals, h2_lvls, h2_lvl0,
                      h2_ent⟩ := h2_1 hdst_1
                    clear ih L
                    c0_hsteps_nogrp; c0_call hMinShrink
                    refine m8MinShrinkSpec_of h2_len h2_otfs.2.1 h2_otfs.2.2.1 h2_tl1 h2_tl_cv
                      h2_nd h2_ent h2_vals h2_lvls h2_lvl0 hm2
                      (fun tmp_ms tl_ms mrk_ms mclr_ms sstk_ms wsort_ms mcl_ms mcf_ms
                          conf_ms llits_ms mrem_ms ticks_ms m_ms hms_len hms_w hms_clr hms_tl1
                          hms_tl_le hms_0 hms_nd hms_post hms_ent hm_ms => ?_)
                    let s_ms := m8MinShrinkState s2 tmp_ms tl_ms mrk_ms mclr_ms sstk_ms wsort_ms
                      mcl_ms mcf_ms conf_ms llits_ms mrem_ms ticks_ms
                    have hms_otfs : FullOtfsInvW c F0 F_cur s_ms :=
                      ⟨hms_len, hms_w, hms_clr,
                        m8Ana_fullArenaVarsNodup_congr_core h2_otfs.2.2.2.1 rfl rfl,
                        FullExtScratchOk.of_pres h2_otfs.2.2.2.2.1 ⟨rfl, rfl⟩ (fun _ r => r),
                        h2_otfs.2.2.2.2.2⟩
                    c0_hsteps_nogrp
                    refine wp_join_group (ts := []) (fun _ m_r1 =>
                      ∃ s_r1 : FullState,
                        FullOtfsInvW c F0 F_cur s_r1 ∧
                        s_r1.core.tmp = tmp_ms ∧ s_r1.core.tmp_len = tl_ms ∧
                        s_r1.core.lvl = s2.core.lvl ∧ s_r1.core.vals = s2.core.vals ∧
                        s_r1.core.cur_level = s2.core.cur_level ∧
                        s_r1.core.cur_vars = s2.core.cur_vars ∧
                        s_r1.core.fuel = s2.core.fuel ∧
                        s_r1.core.dense_mode = s2.core.dense_mode ∧
                        s_r1.core.probing = s2.core.probing ∧
                        s_r1.scratch.work_stk2 = s.scratch.work_stk2 ∧
                        (FullMem c s_r1 ⋆ R) m_r1) ?_ ?_
                    · rintro _ ⟨⟩ m_tr
                        ⟨s_tr, htr_otfs, hr1_tmp, hr1_tl, hr1_lvl, hr1_vals, hr1_cl, hr1_cv,
                          hr1_fu, hr1_dm, hr1_pr, htr_ws2, hm_tr⟩
                      have htr_len := htr_otfs.1
                      have htr_core_eq : s_tr.core = s_tr.core := rfl
                      have hm_gi : (FullMem c s_tr ⋆ R) m_tr := hm_tr
                      c0_hsteps_nogrp
                      refine wp_loop_group (ts := [i64, i32, i64])
                        (fun r_gi (glue_v, last_v, gi_v, ()) m_gi =>
                          ∃ gi, 1 ≤ gi ∧ gi ≤ tl_ms ∧ r_gi = tl_ms - gi ∧
                            gi_v = BitVec.ofNat 64 gi ∧ (FullMem c s_tr ⋆ R) m_gi) ?_ ?_
                      · rintro Lgi _ ⟨glue_v, last_v, gi_v, ⟨⟩⟩ m_gi ih_gi
                          ⟨gi, hgi1, hgile, rfl, rfl, hm_gi⟩
                        have htr_tl_bd : tl_ms < 2 ^ 64 := by
                          have := h2_len.core_ok.cur_vars_le; omega
                        c0_hsplit
                        · have hgi_bv : (BitVec.ofNat 64 gi).toNat = gi :=
                            bv64_ofNat_toNat (by omega)
                          have hgilt : gi < tl_ms := by
                            have hlt : (BitVec.ofNat 64 gi).toNat <
                                (BitVec.ofNat 64 s_tr.core.tmp_len).toNat := by assumption
                            rw [htr_core_eq, hr1_tl, hgi_bv, bv64_ofNat_toNat htr_tl_bd] at hlt
                            exact hlt
                          have htr_tmp_len : s_tr.core.tmp.length = c.max_vars :=
                            htr_len.core_ok.tmp_len_arr
                          have hgi_idx : (BitVec.ofNat 64 gi).toNat < s_tr.core.tmp.length := by
                            rw [hgi_bv, htr_tmp_len]
                            have := h2_len.core_ok.cur_vars_le; omega
                          have hgi_post := hms_post gi hgi1 hgilt
                          have htr_tmp_gi_lt : gi < tmp_ms.length := by
                            rw [← hr1_tmp, ← htr_core_eq, htr_tmp_len]
                            have := h2_len.core_ok.cur_vars_le; omega
                          have hgi_t_eq : s_tr.core.tmp[(BitVec.ofNat 64 gi).toNat]'hgi_idx =
                              tmp_ms[gi]'htr_tmp_gi_lt :=
                            m8Ana_getElem_congr_list (by rw [htr_core_eq, hr1_tmp]) hgi_bv
                          have hgi_l_eq : (tmp_ms[gi]'htr_tmp_gi_lt).toNat / 2 =
                              ((tmp_ms[gi]?.getD 0#32).toNat / 2) := by
                            rw [List.getElem?_eq_getElem htr_tmp_gi_lt, Option.getD_some]
                          have hgi_lvl_lt : ((s_tr.core.tmp[(BitVec.ofNat 64 gi).toNat]'hgi_idx
                              >>> 1#32).setWidth 64).toNat < s_tr.core.lvl.length := by
                            rw [m8Ana_bv32_setWidth64_toNat, m8Ana_bv32_lshr_1, hgi_t_eq, hgi_l_eq,
                              htr_core_eq, hr1_lvl, h2_len.core_ok.lvl_len]
                            have := h2_len.core_ok.cur_vars_le; have := hgi_post.1; omega
                          have hgi1_nat : (BitVec.ofNat 64 gi + 1#64).toNat = gi + 1 := by
                            rw [m8Ana_bv64_add1_toNat (by rw [hgi_bv]; omega), hgi_bv]
                          c0_hsteps
                          all_goals exact (ih_gi (tl_ms - (gi + 1)) _ m_gi (by omega)
                            ⟨gi + 1, by omega, by omega, rfl,
                              BitVec.eq_of_toNat_eq (by
                                rw [show (1 : BitVec 64) = 1#64 from rfl, hgi1_nat,
                                  bv64_ofNat_toNat (by omega)]),
                              hm_gi⟩)
                        · c0_hsteps_nogrp
                          refine wp_join_group (ts := []) (fun _ m_em =>
                            ∃ s_em : FullState,
                              FullOtfsInvW c F0 F_cur s_em ∧ s_em.core = s_tr.core ∧
                              s_em.scratch.work_stk2 = s.scratch.work_stk2 ∧
                              (FullMem c s_em ⋆ R) m_em) ?_ ?_
                          · rintro _ ⟨⟩ m_em ⟨s_em, hem_otfs, hem_core, hem_ws2, hm_em⟩
                            rw [Blocks.get_here]; try dsimp only
                            c0_hsteps_nogrp; c0_call hLearnCl
                            refine ⟨c, F0, F_cur, s_em, R, rfl, hem_otfs,
                              ?_, ?_, ?_, ?_, ?_, ?_, ?_, hm_em, ?_⟩
                            · rw [hem_core, htr_core_eq, hr1_cl, h2_cl]; exact hcl1_pos
                            · rw [hem_core, htr_core_eq, hr1_tl]; exact hms_tl1
                            · rw [hem_core, htr_core_eq, hr1_tl, hr1_cv]; omega
                            · rw [hem_core, htr_core_eq, hr1_tmp, hr1_tl]; exact hms_nd
                            · intro k hk
                              rw [hem_core, htr_core_eq, hr1_tl] at hk
                              rw [hem_core, htr_core_eq, hr1_tmp, hr1_vals, hr1_cv]
                              cases k with
                              | zero =>
                                have h0_s2 := h2_vals 0 h2_tl1
                                have h0_eq : tmp_ms[0]? = s2.core.tmp[0]? := hms_0
                                rw [h0_eq]; exact h0_s2
                              | succ k' =>
                                have hk_p := hms_post (k' + 1) (by omega) hk
                                exact ⟨hk_p.1, hk_p.2.1⟩
                            · intro k hk1 hk2
                              rw [hem_core, htr_core_eq, hr1_tl] at hk2
                              rw [hem_core, htr_core_eq, hr1_lvl, hr1_tmp, hr1_tl, hr1_cl]
                              have hk_p := hms_post k hk1 hk2
                              exact ⟨hk_p.2.2.1, hk_p.2.2.2.1, hk_p.2.2.2.2⟩
                            · rw [hem_core, htr_core_eq, hr1_tmp, hr1_tl]; exact hms_ent
                            · intro rl s_lc m_lc hlc_len hlc_dom hlc_cv hlc_fu hlc_ws2
                                hlc_20 hlc_0 hlc_1 hm_lc
                              have hlc_cv' : s_lc.core.cur_vars = s.core.cur_vars := by
                                rw [hlc_cv, hem_core, htr_core_eq, hr1_cv]; exact h2_cv'
                              have hlc_fu' : s_lc.core.fuel.toNat ≤ s.core.fuel.toNat := by
                                rw [hem_core, htr_core_eq, hr1_fu] at hlc_fu
                                exact Nat.le_trans hlc_fu h2_fu'
                              have hlc_ws2' : s_lc.scratch.work_stk2 = s.scratch.work_stk2 :=
                                hlc_ws2.trans hem_ws2
                              have hcl_tr : s_em.core.cur_level = s2.core.cur_level := by
                                rw [hem_core, htr_core_eq, hr1_cl]
                              c0_hsteps
                              exact hQ rl s_lc m_lc hlc_len hlc_dom hlc_cv' hlc_fu'
                                ⟨hlc_ws2', fun h20 => let ⟨_, hsp, hcl⟩ := hlc_20 h20
                                  ⟨hsp.toOtfs, by rw [hcl_tr] at hcl; omega,
                                    hsp.2.2.2.2.2.trans hs.2.2.2.2.2.symm⟩⟩
                                (fun h20 => (hlc_20 h20).1)
                                (fun h0 => (hlc_0 h0).toOtfs)
                                (fun h1 => let ⟨hs1, hcl1⟩ := hlc_1 h1
                                  ⟨hs1, by rw [hcl_tr] at hcl1; omega⟩)
                                hm_lc
                          · intro Jem hJem
                            c0_hsplit
                            · c0_hsteps_nogrp; c0_call hEma
                              refine ⟨c, s_tr, R, rfl, htr_len, hm_gi,
                                fun _ s_em m_em hem_core hem_len hem_pres hm_em => ?_⟩
                              have hem_otfs :=
                                m8Ana_fullOtfsInvW_of_safetySlice htr_otfs hem_len hem_core
                                  hem_pres.1
                              have hem_core_eq : s_em.core = s_tr.core :=
                                fullCoreState_agrees_with_scratch hem_core
                              have hem_ws2 : s_em.scratch.work_stk2 = s.scratch.work_stk2 :=
                                hem_pres.2.2.1.trans htr_ws2
                              c0_hsteps
                              exact hJem () m_em ⟨s_em, hem_otfs, hem_core_eq, hem_ws2, hm_em⟩
                            · c0_hsteps
                              exact hJem () m_gi ⟨s_tr, htr_otfs, rfl, htr_ws2, hm_gi⟩
                      · intro Jgl hJgl
                        c0_hsteps
                        exact hJgl (tl_ms - 1) (0#64, 0#32, 1#64, ()) m_tr
                          ⟨1, Nat.le_refl _, hms_tl1, rfl, rfl, hm_tr⟩
                    · intro Jr1 hJr1
                      c0_hsplit
                      · c0_hsteps_nogrp; c0_call hRestoreBump
                        refine ⟨c, s_ms, R, rfl, hms_len, hms_clr.1, hm_ms, ?_⟩
                        intro mrk_r mcl_r sc_r m_r _ hlen_r hmrk_r hpres_r hws2_r hm_r
                        let s_r1 : FullState :=
                          { core := { s_ms.core with mrk := mrk_r, min_clr_len := mcl_r }
                            scratch := sc_r }
                        have hr1_otfs :=
                          m8Ana_fullOtfsInvW_of_restoreBump hms_otfs hlen_r hmrk_r hpres_r
                        have hr1_ws2 : s_r1.scratch.work_stk2 = s.scratch.work_stk2 :=
                          hws2_r.trans h2_ws2'
                        c0_hsteps_nogrp; c0_call hTickRel
                        refine ⟨c, s_r1, R, rfl, hlen_r, hm_r,
                          fun _ s_tr m_tr htr_core htr_len htr_pres hm_tr => ?_⟩
                        have htr_otfs :=
                          m8Ana_fullOtfsInvW_of_safetySlice hr1_otfs htr_len htr_core htr_pres.1
                        have htr_core_eq : s_tr.core = s_r1.core :=
                          fullCoreState_agrees_with_scratch htr_core
                        have htr_ws2 : s_tr.scratch.work_stk2 = s.scratch.work_stk2 :=
                          htr_pres.2.2.1.trans hr1_ws2
                        c0_hsteps
                        exact hJr1 () m_tr
                          ⟨s_tr, htr_otfs, by rw [htr_core_eq], by rw [htr_core_eq],
                            by rw [htr_core_eq], by rw [htr_core_eq], by rw [htr_core_eq],
                            by rw [htr_core_eq], by rw [htr_core_eq], by rw [htr_core_eq],
                            by rw [htr_core_eq], htr_ws2, hm_tr⟩
                      · c0_hsteps
                        exact hJr1 () m_ms
                          ⟨s_ms, hms_otfs, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                            h2_ws2', hm_ms⟩
      · c0_hsteps
        exact hQ 0#64 s_i m_i hcut_inv.1 (Or.inl rfl) hcv_i hfu_i
          ⟨hws2_i, fun h => by cases h⟩
          (fun h => by cases h) (fun _ => hcut_inv.toOtfs) (fun h => by cases h) hm_i
    · intro L hL; c0_hsteps
      exact hL (s.core.cur_vars + 64) (0#64, ()) m
        ⟨0, s.core.trail_end, s, Nat.zero_le _, rfl, rfl, Nat.le_refl _,
          hs.toCut, hcur_pos, Nat.le_refl _, hconfl.toCut hs.2.1, rfl, Nat.le_refl _, rfl, hm⟩

/-! ## 3. `full_preprocess_m6_step11_wp` (`FullM6.fullM6PreprocessSpec`) -/

section PreprocessStep11

private theorem s11_fullWitnessInv_with_unflushed {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) :
    FullWitnessInv c F0 F_cur { k with unflushed := 0#64 } :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }

private theorem s11_call_bcp {Γ : Env} {ret : List Ty}
    {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont ret}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {ext : List (BitVec 64)}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, ()))
    (hΓ : ∀ a m' Q' X', FullM6BcpS15.fullBcpS15Spec a m' Q' X' →
      Γ "full_propagate" [i64] [i64] a m' Q' X')
    (hinv : FullM6HdrInvW c F0 F_cur ext s)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      FullM6HdrInvW c F0 F_cur ext s' → s'.core.cur_level = s.core.cur_level →
      FullTrailExt s.core s'.core → FullArenaPermEq s.core s'.core →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 0#64 → s'.core.propagated = s'.core.trail_end ∧
        (s.core.oom = 0#64 → s'.core.oom = 0#64) ∧
        (s.core.propagated < s.core.trail_end → s'.core.fuel.toNat < s.core.fuel.toNat)) →
      (r = 1#64 → s'.core.fuel.toNat < s.core.fuel.toNat ∧ s'.core.oom = 0#64 ∧
        FullConflictOkW F_cur s') →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call "full_propagate" args k) m := by
  refine wp_call_of_spec args k ?_
  rw [hargs]
  have hsp := hinv.sparseW
  refine hΓ _ _ _ X ⟨c, F0, F_cur, s, array64 (c.hdr - 2304) ext ⋆ R, rfl, hsp.1, hsp.2.1,
    hsp.2.2.2.2.2, (fullM6HdrMem_iff c ext s R m).mp hm, ?_⟩
  intro r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
    fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' delayed' m' s'
    hlen' hw' htr' hperm' _ hfu' hdom hr0 hr1 _ _ hm'
  have hnd' : FullArenaVarsNodup s' := by
    intro r' hr' hgb'
    have hr0' : r' ∈ fullArenaClauseRefs s := by
      change r' ∈ fullArenaClauseRefsCore s'.core at hr'
      change r' ∈ fullArenaClauseRefsCore s.core
      rwa [← hperm'.2.1]
    have hp := hperm'.2.2 r' hr0'
    have hgb0 : fullArenaClauseGarb s r' = false := by
      change fullArenaClauseGarbCore s.core r' = false
      change fullArenaClauseGarbCore s'.core r' = false at hgb'
      rwa [← hp.2.1]
    exact (hp.2.2.map (· / 2)).nodup_iff.mpr (hsp.2.2.2.1 r' hr0' hgb0)
  have hll' : FullLastLearnedWf s' :=
    hsp.2.2.2.2.1.1.of_refs_subset rfl fun r' hr' => by
      change r' ∈ fullArenaClauseRefsCore s.core at hr'
      change r' ∈ fullArenaClauseRefsCore s'.core
      rwa [hperm'.2.1]
  have hinv' : FullM6HdrInvW c F0 F_cur ext s' :=
    FullM6HdrInvW.mk_inv hinv.cfgOk hinv.extOk
      ⟨hlen', hw', hsp.2.2.1, hnd', ⟨hll', hsp.2.2.2.2.1.2⟩, hsp.2.2.2.2.2⟩
  exact hk r s' m' hinv' rfl htr' hperm' hfu' hdom hr0 hr1
    ((fullM6HdrMem_iff c ext s' R m').mpr hm')

private theorem s11_conflict_level0_unsat {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core)
    (hl0 : s.core.cur_level = 0) (hc : FullConflictOkW F_cur s) : F0.Unsat := by
  rcases hc with ⟨_, h0lt, h1lt, hf0, hf1, hent⟩ | ⟨_, href, hng, hfals⟩
  · refine hw.ext_sound.2
      (unsat_of_entails_nil (entails_of_mem_or_false hent fun l hl => Or.inr ?_))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · obtain ⟨i, hi, hieq⟩ := (hw.vals_false_iff _ h0lt).mp hf0
      have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega); rwa [hieq] at hs
    · obtain ⟨i, hi, hieq⟩ := (hw.vals_false_iff _ h1lt).mp hf1
      have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega); rwa [hieq] at hs
  · refine hw.ext_sound.2 (unsat_of_entails_nil
      (entails_of_mem_or_false (hw.arena.entails _ href hng) fun l hl => Or.inr ?_))
    obtain ⟨i, hi, hieq⟩ :=
      (hw.vals_false_iff l (hw.arena.lits_lt _ href hng l hl)).mp (hfals l hl)
    have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega); rwa [hieq] at hs

private abbrev S11PrePost (c : FullCfg) (F0 : CNF Nat) (s : FullState)
    (R : Mem 64 → Prop) (Q : Post [i64]) : Prop :=
  ∀ (r : BitVec 64) c' ext' s' m',
    FullM4Compact.FullCfgCompat c c' → s'.LengthsOk c' → FullM6HdrCfgOk c' →
    M6HdrExtOk ext' → (r = 0#64 ∨ r = 1#64 ∨ r = 10#64 ∨ r = 20#64) →
    s'.core.fuel.toNat ≤ s.core.fuel.toNat → (r = 20#64 → F0.Unsat) →
    (r = 1#64 → FullM6HdrInv c' F0 ext' s' ∧ s'.core.cur_level = 0) →
    (r = 10#64 → s'.scratch.extend_len ≤ c'.extend_cap) →
    (FullM6HdrMem c' ext' s' ⋆ R) m' → Q (r, ()) m'

private theorem s11Pre_ret10 {c c' : FullCfg} {F0 : CNF Nat} {ext' : List (BitVec 64)}
    {s s' : FullState} {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post [i64]}
    (hQ : S11PrePost c F0 s R Q) (hcmp : FullM4Compact.FullCfgCompat c c')
    (hinv : FullM6HdrInv c' F0 ext' s')
    (hfu : s'.core.fuel.toNat ≤ s.core.fuel.toNat) (hm : (FullM6HdrMem c' ext' s' ⋆ R) m') :
    Q (10#64, ()) m' :=
  hQ 10#64 c' ext' s' m' hcmp hinv.sparse.lengths hinv.cfgOk hinv.extOk
    (Or.inr (Or.inr (Or.inl rfl))) hfu (fun h => by cases h) (fun h => by cases h)
    (fun _ => hinv.sparse.2.2.2.1.2) hm

private theorem s11Pre_ret20 {c c' : FullCfg} {F0 : CNF Nat} {ext' : List (BitVec 64)}
    {s s' : FullState} {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post [i64]}
    (hQ : S11PrePost c F0 s R Q) (hcmp : FullM4Compact.FullCfgCompat c c')
    (hlen : s'.LengthsOk c') (hcfg : FullM6HdrCfgOk c') (hext : M6HdrExtOk ext')
    (hfu : s'.core.fuel.toNat ≤ s.core.fuel.toNat) (hu : F0.Unsat)
    (hm : (FullM6HdrMem c' ext' s' ⋆ R) m') : Q (20#64, ()) m' :=
  hQ 20#64 c' ext' s' m' hcmp hlen hcfg hext (Or.inr (Or.inr (Or.inr rfl))) hfu
    (fun _ => hu) (fun h => by cases h) (fun h => by cases h) hm

private theorem s11Pre_ret20_inc {c c' : FullCfg} {F0 : CNF Nat} {ext' : List (BitVec 64)}
    {s s' : FullState} {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post [i64]}
    (hQ : S11PrePost c F0 s R Q) (hcmp : FullM4Compact.FullCfgCompat c c')
    (hinv : FullM6HdrInv c' F0 ext' s') (hfu : s'.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hinc : s'.core.inconsistent ≠ 0#64) (hm : (FullM6HdrMem c' ext' s' ⋆ R) m') :
    Q (20#64, ()) m' :=
  s11Pre_ret20 hQ hcmp hinv.sparse.lengths hinv.cfgOk hinv.extOk hfu
    (fullM6HdrInv_inconsistent_unsat hinv hinc) hm

private theorem s11Pre_ret0_inv {c c' : FullCfg} {F0 : CNF Nat} {ext' : List (BitVec 64)}
    {s s' : FullState} {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post [i64]}
    (hQ : S11PrePost c F0 s R Q) (hcmp : FullM4Compact.FullCfgCompat c c')
    (hinv : FullM6HdrInv c' F0 ext' s') (hfu : s'.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hm : (FullM6HdrMem c' ext' s' ⋆ R) m') : Q (0#64, ()) m' :=
  hQ 0#64 c' ext' s' m' hcmp hinv.sparse.lengths hinv.cfgOk hinv.extOk (Or.inl rfl) hfu
    (fun h => by cases h) (fun h => by cases h) (fun h => by cases h) hm

private theorem s11_pre_unflushed {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {ext : List (BitVec 64)} {s s1 : FullState} {R : Mem 64 → Prop} {m1 : Mem 64}
    {Q : Post [i64]} {X : XPost} {J2 : Cont []}
    (hProp : ∀ a m Q X, FullM6BcpS15.fullBcpS15Spec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hinv1 : FullM6HdrInv c F0 ext s1) (hcl1' : s1.core.cur_level = 0)
    (hfu1 : s1.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hm1 : (FullM6HdrMem c ext s1 ⋆ R) m1)
    (hJ2 : ∀ xs m2, (∃ s2, FullM6HdrInv c F0 ext s2 ∧ s2.core.cur_level = 0 ∧
      s2.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c ext s2 ⋆ R) m2) → J2 xs m2)
    (hQ : S11PrePost c F0 s R Q) :
    wp Γ Q X (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 512, ())) fun p_7 =>
      Expr.load i64 (Arg.var p_7.fst) fun ld =>
        Expr.let_ (Op.mk (.cmp .ugt i64 Ty.bool rfl) (Arg.var ld, Arg.imm 0, ())) fun p_8 =>
          Expr.jnz (Arg.var p_8.fst)
            (Expr.call (as := [i64]) (bs := [i64]) "full_arena_sweep" (Arg.var c.hdr, ())
                fun p_9 =>
              Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var p_9.fst, Arg.imm 2, ()))
                  fun p_10 =>
                Expr.jnz (Arg.var p_10.fst) (Expr.ret (Arg.imm 20, ()))
                  (Expr.call (as := [i64]) (bs := [i64]) "full_propagate" (Arg.var c.hdr, ())
                      fun p_11 =>
                    Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl)
                        (Arg.var p_11.fst, Arg.imm 1, ())) fun p_12 =>
                      Expr.jnz (Arg.var p_12.fst) (Expr.ret (Arg.imm 20, ()))
                        (Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 512, ())) fun p =>
                          Expr.store (t := i64) (Arg.imm 0) (Arg.var p.fst) (Expr.jump J2 ()))))
            (Expr.jump J2 ())) m1 := by
  refine wp_m6Hdr_focus_frame hm1 fun hm1f => ?_
  c0_hsteps_nogrp
  · obtain ⟨F_cur1, hw1⟩ := hinv1.sparse.1.witness
    c0_call hSweep
    refine ⟨c, F0, F_cur1, s1, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl,
      hinv1.sparse.lengths, hw1, hinv1.sparse.2.2.1, hinv1.sparse.2.2.2.2,
      fun hpos => by omega, hm1f,
      fun sr vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' arena' alen' wlen'
        wu' fred' ni' nr' nb' oom' sc' mS hlenS hsr hexlenS hws2S hllS hwS hndS
        _ _ _ h20S _ hmS => ?_⟩
    have hmS' := fullM6HdrMem_unfocus hmS
    let sSc : FullCoreState := { s1.core with
      vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
      trail_end := te', unassigned := unass', unflushed := unfl', wvec := wvec', wstk := wstk',
      arena := arena', arena_len := alen', wlen := wlen', wusable := wu', arena_garbage := 0#64,
      first_reducible := fred', num_irred := ni', num_redundant := nr', num_binary := nb',
      oom := oom' }
    let sS : FullState := { core := sSc, scratch := sc' }
    have hinvWS : FullM6HdrInvW c F0 F_cur1 ext sS :=
      FullM6HdrInvW.mk_inv hinv1.cfgOk hinv1.extOk
        ⟨hlenS, hwS, hinv1.sparse.2.1, hndS,
          ⟨hllS, (by change sc'.extend_len ≤ c.extend_cap; rw [hexlenS]
                     exact hinv1.sparse.2.2.2.1.2)⟩,
          hinv1.sparse.2.2.2.2⟩
    c0_hsteps_nogrp
    · exact s11Pre_ret20 hQ (.refl c) hlenS hinvWS.cfgOk hinvWS.extOk hfu1 (h20S ‹_›).2 hmS'
    · refine s11_call_bcp rfl hProp hinvWS hmS'
        fun pr sP mP hinvWP hclP _ _ hfuP _ _ hrP1 hmP => ?_
      have hinvP := hinvWP.toInv; have hfuP' := Nat.le_trans hfuP hfu1
      c0_hsteps_nogrp
      · exact s11Pre_ret20 hQ (.refl c) hinvP.sparse.lengths hinvP.cfgOk hinvP.extOk hfuP'
          (s11_conflict_level0_unsat hinvWP.sparseW.2.1 (hclP ▸ hcl1') (hrP1 ‹_›).2.2) hmP
      · refine wp_m6Hdr_focus_frame hmP fun hmPf => ?_
        c0_hsteps_nogrp
        have hinvP' : FullM6HdrInv c F0 ext
            { sP with core := { sP.core with unflushed := 0#64 } } :=
          FullM6HdrInv.mk_inv hinvP.cfgOk hinvP.extOk ⟨⟨⟨{ hinvP.sparse.lengths.core_ok with
              vals_len := hinvP.sparse.lengths.core_ok.vals_len }, hinvP.sparse.lengths.scratch_ok⟩,
            ⟨F_cur1, s11_fullWitnessInv_with_unflushed hinvWP.sparseW.2.1⟩⟩,
            hinvP.sparse.2.1, hinvP.sparse.2.2.1, hinvP.sparse.2.2.2.1, hinvP.sparse.2.2.2.2⟩
        exact hJ2 () _ ⟨_, hinvP', hclP ▸ hcl1', hfuP', fullM6HdrMem_unfocus (by assumption)⟩
  · exact hJ2 () m1 ⟨s1, hinv1, hcl1', hfu1, fullM6HdrMem_unfocus hm1f⟩

private theorem s11_pre_compact_step {Γ : Env} {c c0 : FullCfg} {hdr : BitVec 64}
    {F0 : CNF Nat} {ext : List (BitVec 64)} {s s0 : FullState} {R : Mem 64 → Prop} {m0 : Mem 64}
    {Q : Post [i64]} {X : XPost} {JC : Cont []}
    (hCompNeed : ∀ a m Q X, FullM4Compact.fullCompactNeededSpec a m Q X →
      Γ "full_compact_needed" [i64] [.bool] a m Q X)
    (hCompact : ∀ a m Q X, FullM4Compact.fullCompactSpec a m Q X →
      Γ "full_compact" [i64] [i64] a m Q X)
    (hhdr : c0.hdr = hdr)
    (hcmp0 : FullM4Compact.FullCfgCompat c c0) (hinv0 : FullM6HdrInv c0 F0 ext s0)
    (hcl0 : s0.core.cur_level = 0) (hfu0 : s0.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hm0f : (FullMem c0 s0 ⋆ (m6ExtMem (m6ExtAddr c0.hdr) ext ⋆ R)) m0)
    (hJC : ∀ xs mC, (∃ cC sC, FullM4Compact.FullCfgCompat c cC ∧
      FullM6HdrInv cC F0 ext sC ∧ sC.core.cur_level = 0 ∧
      sC.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem cC ext sC ⋆ R) mC) → JC xs mC)
    (hQ : S11PrePost c F0 s R Q) :
    wp Γ Q X (Expr.call (as := [i64]) (bs := [.bool]) "full_compact_needed" (Arg.var hdr, ())
        fun p =>
      Expr.jnz (Arg.var p.fst)
        (Expr.call (as := [i64]) (bs := [i64]) "full_compact" (Arg.var hdr, ()) fun p_13 =>
          Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var p_13.fst, Arg.imm 20, ()))
              fun p_14 =>
            Expr.jnz (Arg.var p_14.fst) (Expr.ret (Arg.imm 20, ()))
              (Expr.let_ (Op.mk (.cmp .ne i64 Ty.bool rfl) (Arg.var p_13.fst, Arg.imm 1, ()))
                  fun p_15 =>
                Expr.jnz (Arg.var p_15.fst) (Expr.ret (Arg.imm 0, ())) (Expr.jump JC ())))
        (Expr.jump JC ())) m0 := by
  subst hhdr
  have hlen0 := hinv0.sparse.lengths
  c0_hsteps_nogrp; c0_call hCompNeed
  refine ⟨c0, s0, m6ExtMem (m6ExtAddr c0.hdr) ext ⋆ R, rfl, hlen0,
    by have := hlen0.core_ok.trail_end_le; have := hlen0.core_ok.cur_vars_le
       have := c0.hmaxv; unfold dimacsBound at *; omega,
    hm0f, fun need _ => ?_⟩
  c0_hsteps_nogrp
  · c0_call hCompact
    refine ⟨c0, F0, s0, m6ExtMem (m6ExtAddr c0.hdr) ext ⋆ R, rfl, hinv0.sparse, hm0f,
      fun rC cC sC mC hcmpC hspC hrC _ hfuC huC h1C hmC => ?_⟩
    have hcfgC := M6HdrCfgOk_of_le (by rw [hcmpC.hdr]; exact M6HdrCfgOk_le hinv0.cfgOk)
    have hinvC := FullM6HdrInv.mk_inv hcfgC hinv0.extOk hspC; have hfuC' := Nat.le_trans hfuC hfu0
    have hmC' := fullM6HdrMem_unfocus (hcmpC.hdr ▸ hmC); have hcmpC' := hcmp0.trans hcmpC
    c0_hsteps_nogrp
    · exact s11Pre_ret20 hQ hcmpC' hspC.lengths hcfgC hinvC.extOk hfuC' (huC ‹_›) hmC'
    · exact s11Pre_ret0_inv hQ hcmpC' hinvC hfuC' hmC'
    · exact hJC () mC ⟨cC, sC, hcmpC', hinvC, h1C ‹_›, hfuC', hmC'⟩
  · exact hJC () m0 ⟨c0, s0, hcmp0, hinv0, hcl0, hfu0, fullM6HdrMem_unfocus hm0f⟩

private theorem s11_sparseInv_with_search_ticks {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hs : FullSparseInv c F0 s) (tk : BitVec 64) :
    FullSparseInv c F0 { s with scratch := { s.scratch with search_ticks := tk } } := by
  obtain ⟨⟨hlen, F_cur, hw⟩, hlm, hnd, hext, hdm⟩ := hs
  exact ⟨⟨⟨hlen.core_ok, { hlen.scratch_ok with }⟩, F_cur, hw⟩, hlm, hnd,
    FullExtScratchOk.of_pres hext ⟨rfl, rfl⟩ (fun _ r => r), hdm⟩

end PreprocessStep11

/-- Parametric `Func.wp` proof for `fidStep11PreprocessM6Fn` (`full_preprocess_m6`, saving and
restoring `h->search_ticks` across `full_lucky`) against `FullM6.fullM6PreprocessSpec`. -/
theorem full_preprocess_m6_step11_wp (Γ : Env)
    (hProp : ∀ a m Q X, FullM6BcpS15.fullBcpS15Spec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hLucky : ∀ a m Q X, fullLuckySpec a m Q X →
      Γ "full_lucky" [i64] [i64] a m Q X)
    (hCompNeed : ∀ a m Q X, FullM4Compact.fullCompactNeededSpec a m Q X →
      Γ "full_compact_needed" [i64] [.bool] a m Q X)
    (hCompact : ∀ a m Q X, FullM4Compact.fullCompactSpec a m Q X →
      Γ "full_compact" [i64] [i64] a m Q X)
    (hScale : ∀ a m Q X, FullFastSched.schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta_m5" [i64, i64] [i64] a m Q X)
    (hProbe : ∀ a m Q X, FullM6Orch.m6ProbeSpec a m Q X →
      Γ "full_probe_m6" [i64, .bool] [i64] a m Q X) :
    ∀ a m Q X, fullM6PreprocessSpec a m Q X →
      Func.wp Γ fidStep11PreprocessM6Fn.body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  rcases fullM6PreprocessSpec_elim hs with ⟨c, F0, ext, s, R, rfl, hinv, hcl0, hm, hQ⟩
  unfold Func.wp fidStep11PreprocessM6Fn full_preprocess_m6_body; dsimp only
  obtain ⟨F_cur, hw0⟩ := hinv.sparse.1.witness
  have hinvW0 : FullM6HdrInvW c F0 F_cur ext s := FullM6HdrInvW.mk_inv hinv.cfgOk hinv.extOk
    ⟨hinv.sparse.lengths, hw0, hinv.sparse.2.1, hinv.sparse.2.2.1, hinv.sparse.2.2.2.1,
      hinv.sparse.2.2.2.2⟩
  c0_hsteps_nogrp
  refine s11_call_bcp rfl hProp hinvW0 hm
    fun r1 s1 m1 hinvW1 hcl1 _ _ hfu1 _ _ hr1_1 hm1 => ?_
  have hinv1 := hinvW1.toInv; have hcl1' : s1.core.cur_level = 0 := hcl1 ▸ hcl0
  refine wp_m6Hdr_focus_frame hm1 fun hm1f => ?_
  c0_hsteps_nogrp
  · exact s11Pre_ret20 hQ (.refl c) hinv1.sparse.lengths hinv1.cfgOk hinv1.extOk hfu1
      (s11_conflict_level0_unsat hinvW1.sparseW.2.1 hcl1' (hr1_1 ‹_›).2.2)
      (fullM6HdrMem_unfocus hm1f)
  · exact s11Pre_ret0_inv hQ (.refl c) hinv1 hfu1 (fullM6HdrMem_unfocus hm1f)
  · exact s11Pre_ret0_inv hQ (.refl c) hinv1 hfu1 (fullM6HdrMem_unfocus hm1f)
  · refine wp_join_group (ts := []) (fun _ m2 => ∃ s2, FullM6HdrInv c F0 ext s2 ∧
        s2.core.cur_level = 0 ∧ s2.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        (FullM6HdrMem c ext s2 ⋆ R) m2) ?_ ?_
    · rintro _ _ m2 ⟨s2, hinv2, hcl2, hfu2, hm2⟩
      refine wp_m6Hdr_focus_frame hm2 fun hm2f => ?_
      c0_hsteps_nogrp
      · exact s11Pre_ret10 hQ (.refl c) hinv2 hfu2 (fullM6HdrMem_unfocus hm2f)
      · c0_call hLucky
        refine ⟨c, F0, s2, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hinv2.sparse, hcl2, hm2f,
          fun lk s3 m3 hlen3 hlk hfu3 _ hu3 hsp3 h10_3 hm3 => ?_⟩
        let s3t : FullState :=
          { s3 with scratch := { s3.scratch with search_ticks := s2.scratch.search_ticks } }
        have hlen3t : s3t.LengthsOk c := ⟨hlen3.core_ok, { hlen3.scratch_ok with }⟩
        have hfu3' : s3t.core.fuel.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfu3 hfu2
        let mkInv3 : lk ≠ 20#64 → lk ≠ 10#64 →
            FullM6HdrInv c F0 ext s3t ∧ s3t.core.cur_level = 0 := fun h20 h10 =>
          let h02 : lk = 0#64 ∨ lk = 2#64 := by
            rcases hlk with rfl | rfl | rfl | rfl <;>
              (first | exact Or.inl rfl | exact Or.inr rfl | contradiction)
          let ⟨hs3, hc3⟩ := hsp3 h02
          ⟨FullM6HdrInv.mk_inv hinv2.cfgOk hinv2.extOk
            (s11_sparseInv_with_search_ticks hs3 s2.scratch.search_ticks), hc3⟩
        c0_hsteps_nogrp
        · rw [‹lk = 20#64›]
          exact s11Pre_ret20 hQ (.refl c) hlen3t hinv2.cfgOk hinv2.extOk hfu3' (hu3 ‹_›)
            (fullM6HdrMem_unfocus (by assumption))
        · rw [‹lk = 10#64›]
          exact hQ 10#64 c ext s3t _ (.refl c) hlen3t hinv2.cfgOk hinv2.extOk
            (Or.inr (Or.inr (Or.inl rfl))) hfu3' (fun _ => by cases ‹_›)
            (fun h => by cases h) (fun _ => h10_3 ‹_›) (fullM6HdrMem_unfocus (by assumption))
        · exact s11Pre_ret20_inc hQ (.refl c) (mkInv3 ‹_› ‹_›).1 hfu3' ‹_›
            (fullM6HdrMem_unfocus (by assumption))
        · exact s11Pre_ret0_inv hQ (.refl c) (mkInv3 ‹_› ‹_›).1 hfu3'
            (fullM6HdrMem_unfocus (by assumption))
        · exact s11Pre_ret0_inv hQ (.refl c) (mkInv3 ‹_› ‹_›).1 hfu3'
            (fullM6HdrMem_unfocus (by assumption))
        · obtain ⟨hinv3, hcl3⟩ := mkInv3 ‹_› ‹_›
          refine wp_join_group (ts := []) (fun (_ : Tup Val []) m3u => ∃ s3u,
              FullM6HdrInv c F0 ext s3u ∧ s3u.core.cur_level = 0 ∧
              s3u.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c ext s3u ⋆ R) m3u) ?_ ?_
          · rintro _ _ m3u ⟨s3u, hinv3u, hcl3u, hfu3u, hm3u⟩
            refine wp_join_group (fun (_ : Tup Val []) m4 => ∃ c4 s4,
                FullM4Compact.FullCfgCompat c c4 ∧ FullM6HdrInv c4 F0 ext s4 ∧
                s4.core.cur_level = 0 ∧ s4.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                (FullM6HdrMem c4 ext s4 ⋆ R) m4) ?_ ?_
            · rintro _ _ m4 ⟨c4, s4, hcmp4, hinv4, hcl4, hfu4, hm4⟩; rw [← hcmp4.hdr]
              refine wp_m6Hdr_focus_frame hm4 fun hm4f => ?_
              c0_hsteps_nogrp
              · exact s11Pre_ret20_inc hQ hcmp4 hinv4 hfu4 ‹_› (fullM6HdrMem_unfocus hm4f)
              · exact s11Pre_ret0_inv hQ hcmp4 hinv4 hfu4 (fullM6HdrMem_unfocus hm4f)
              · exact s11Pre_ret10 hQ hcmp4 hinv4 hfu4 (fullM6HdrMem_unfocus hm4f)
              · c0_call hScale
                refine ⟨c4, s4, m6ExtMem (m6ExtAddr c4.hdr) ext ⋆ R, rfl, hinv4.sparse.lengths,
                  hm4f, fun sd1 => ?_⟩
                c0_hsteps_nogrp; c0_call hScale
                refine ⟨c4, _, m6ExtMem (m6ExtAddr c4.hdr) ext ⋆ R, rfl,
                  (fullState_upd_probe_step hinv4.sparse.lengths sd1 s4.scratch.probings).1,
                  by assumption, fun sd2 => ?_⟩
                c0_hsteps_nogrp
                have hst4 := fullState_upd_probe_step hinv4.sparse.lengths sd1 s4.scratch.probings
                have hst4' := fullState_upd_elim_step hst4.1 sd2 s4.scratch.eliminations
                  s4.scratch.elim_bound
                have hinv4' := fullM6HdrInv_of_probeStep hinv4 (probeStep_trans hst4 hst4')
                have hm4' := fullM6HdrMem_unfocus (by assumption)
                c0_call hProbe
                refine FullM6Orch.m6ProbeSpec_of hinv4'
                  (by rw [hst4'.2.1, hst4.2.1]; exact hcl4) hm4'
                  fun r5 ext5 s5 m5 hlen5 hext5 hfu5 hr5 hu5 h15 hm5 => ?_
                have hfu5' : s5.core.fuel.toNat ≤ s.core.fuel.toNat := by
                  rw [hst4'.2.1, hst4.2.1] at hfu5; exact Nat.le_trans hfu5 hfu4
                c0_hsteps_nogrp
                · exact s11Pre_ret20 hQ hcmp4 hlen5 hinv4'.cfgOk hext5 hfu5' (hu5 ‹_›) hm5
                · obtain ⟨hinv5, hcl5⟩ := h15 (hr5.resolve_right ‹_›)
                  refine wp_m6Hdr_focus_frame hm5 fun hm5f => ?_
                  c0_hsteps_nogrp
                  · exact s11Pre_ret20_inc hQ hcmp4 hinv5 hfu5' ‹_› (fullM6HdrMem_unfocus hm5f)
                  · exact s11Pre_ret0_inv hQ hcmp4 hinv5 hfu5' (fullM6HdrMem_unfocus hm5f)
                  · exact s11Pre_ret0_inv hQ hcmp4 hinv5 hfu5' (fullM6HdrMem_unfocus hm5f)
                  · refine wp_join_group (fun (_ : Tup Val []) m6 => ∃ c6 s6,
                          FullM4Compact.FullCfgCompat c c6 ∧ FullM6HdrInv c6 F0 ext5 s6 ∧
                          s6.core.cur_level = 0 ∧ s6.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                          (FullM6HdrMem c6 ext5 s6 ⋆ R) m6) ?_ ?_
                    · rintro _ _ m6 ⟨c6, s6, hcmp6, hinv6, hcl6, hfu6, hm6⟩
                      rw [hcmp4.hdr, ← hcmp6.hdr]
                      refine wp_m6Hdr_focus_frame hm6 fun hm6f => ?_
                      c0_hsteps_nogrp
                      · exact s11Pre_ret20_inc hQ hcmp6 hinv6 hfu6 ‹_› (fullM6HdrMem_unfocus hm6f)
                      · exact s11Pre_ret0_inv hQ hcmp6 hinv6 hfu6 (fullM6HdrMem_unfocus hm6f)
                      · exact s11Pre_ret10 hQ hcmp6 hinv6 hfu6 (fullM6HdrMem_unfocus hm6f)
                      · c0_call hScale
                        refine ⟨c6, s6, m6ExtMem (m6ExtAddr c6.hdr) ext5 ⋆ R, rfl,
                          hinv6.sparse.lengths, hm6f, fun sd3 => ?_⟩
                        c0_hsteps_nogrp; c0_call hScale
                        refine ⟨c6, _, m6ExtMem (m6ExtAddr c6.hdr) ext5 ⋆ R, rfl,
                          (fullState_upd_probe_step hinv6.sparse.lengths sd3
                            s6.scratch.probings).1,
                          by assumption, fun sd4 => ?_⟩
                        c0_hsteps_nogrp
                        have hst6 := fullState_upd_probe_step hinv6.sparse.lengths sd3
                          s6.scratch.probings
                        have hst6' := fullState_upd_elim_step hst6.1 sd4 s6.scratch.eliminations
                          s6.scratch.elim_bound
                        have hinv6' := fullM6HdrInv_of_probeStep hinv6
                          (probeStep_trans hst6 hst6')
                        exact hQ 1#64 c6 ext5 _ _ hcmp6 hinv6'.sparse.lengths hinv6'.cfgOk
                          hinv6'.extOk (Or.inr (Or.inl rfl))
                          (by rw [hst6'.2.1, hst6.2.1]; exact hfu6) (fun h => by cases h)
                          (fun _ => ⟨hinv6', by rw [hst6'.2.1, hst6.2.1]; exact hcl6⟩)
                          (fun h => by cases h) (fullM6HdrMem_unfocus (by assumption))
                    · exact fun _ hJC2 => wp_m6Hdr_focus_frame hm5 fun hm5f =>
                        s11_pre_compact_step hCompNeed hCompact rfl hcmp4 hinv5 hcl5 hfu5' hm5f
                          hJC2 hQ
            · exact fun _ hJC1 => wp_m6Hdr_focus_frame hm3u fun hm3uf =>
                s11_pre_compact_step hCompNeed hCompact rfl (.refl c) hinv3u hcl3u hfu3u hm3uf hJC1
                  hQ
          · intro _ hJ3u
            c0_hsteps_nogrp
            refine wp_join_group (ts := []) (fun _ m_b => m = m_b) ?_ ?_
            · rintro _ ⟨⟩ mb hmb; subst mb
              c0_hsteps_nogrp
              refine wp_join_group (ts := []) (fun _ m_w => ∃ sW,
                  FullM6HdrInv c F0 ext sW ∧ sW.core.cur_level = 0 ∧
                  sW.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                  (FullMem c sW ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R)) m_w) ?_ ?_
              · rintro _ _ m_w ⟨sW, hinvW, hclW, hfuW, hmW⟩
                c0_hsteps
                have hinvW' :
                    FullM6HdrInv c F0 ext
                      { sW with core := { sW.core with unflushed := 0#64 } } := by
                  obtain ⟨F_curW, hwW⟩ := hinvW.sparse.1.witness
                  exact FullM6HdrInv.mk_inv hinvW.cfgOk hinvW.extOk
                    ⟨⟨⟨{ hinvW.sparse.lengths.core_ok with
                          vals_len := hinvW.sparse.lengths.core_ok.vals_len },
                       hinvW.sparse.lengths.scratch_ok⟩,
                      ⟨F_curW, s11_fullWitnessInv_with_unflushed hwW⟩⟩,
                     hinvW.sparse.2.1, hinvW.sparse.2.2.1, hinvW.sparse.2.2.2.1,
                     hinvW.sparse.2.2.2.2⟩
                exact hJ3u () _ ⟨_, hinvW', hclW, hfuW, fullM6HdrMem_unfocus (by assumption)⟩
              · intro J_brk hJ_brk
                have hJ_brkF : ∀ (sW : FullState) m_w,
                    FullM6HdrInv c F0 ext sW → sW.core.cur_level = 0 →
                    sW.core.fuel.toNat ≤ s.core.fuel.toNat →
                    (FullMem c sW ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R)) m_w →
                    J_brk () m_w := fun sW m_w h1 h2 h3 hmW => hJ_brk () m_w ⟨sW, h1, h2, h3, hmW⟩
                c0_hsteps_nogrp
                refine wp_while_state0 (α := FullState)
                  (μ := fun st => st.core.fuel.toNat)
                  (Inv := fun sL mL => FullM6HdrInv c F0 ext sL ∧ sL.core.cur_level = 0 ∧
                    sL.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                    (FullMem c sL ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R)) mL) ?_ ?_
                · intro JL hJL; c0_hsteps; exact hJL s3t _ ⟨hinv3, hcl3, hfu3', by assumption⟩
                · intro JL sL mL ⟨hinvL, hclL, hfuL, hmL⟩ ihL
                  rw [Blocks.get_here]; dsimp only
                  obtain ⟨F_curL, hwL⟩ := hinvL.sparse.1.witness
                  have hpr_le : sL.core.propagated ≤ sL.core.trail_end :=
                    hinvL.sparse.lengths.core_ok.propagated_le
                  c0_hsteps_nogrp
                  · c0_call hSweep
                    refine ⟨c, F0, F_curL, sL, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl,
                      hinvL.sparse.lengths, hwL, hinvL.sparse.2.2.1, hinvL.sparse.2.2.2.2,
                      fun hpos => by omega, hmL,
                      fun sr2 valsS flagsS lvlS rsnsS trlS tpS teS unassS unflS wvecS wstkS
                        arenaS alenS wlenS wuS fredS niS nrS nbS oomS scS mS
                        hlenS hsr2 hexlenS _ hllS hwS hndS _ _ hsr1 h20S _ hmS => ?_⟩
                    let sS : FullState :=
                      { sL with
                        core := { sL.core with
                          vals := valsS, flags := flagsS, lvl := lvlS, rsns := rsnsS, trl := trlS,
                          trail_pos := tpS, trail_end := teS, unassigned := unassS,
                          unflushed := unflS, wvec := wvecS, wstk := wstkS, arena := arenaS,
                          arena_len := alenS, wlen := wlenS, wusable := wuS, arena_garbage := 0#64,
                          first_reducible := fredS, num_irred := niS, num_redundant := nrS,
                          num_binary := nbS, oom := oomS }
                        scratch := scS }
                    have hinvWS : FullM6HdrInvW c F0 F_curL ext sS :=
                      FullM6HdrInvW.mk_inv hinvL.cfgOk hinvL.extOk
                        ⟨hlenS, hwS, hinvL.sparse.2.1, hndS,
                          ⟨hllS, by
                            change scS.extend_len ≤ c.extend_cap
                            rw [hexlenS]; exact hinvL.sparse.2.2.2.1.2⟩,
                          hinvL.sparse.2.2.2.2⟩
                    have hinvS := hinvWS.toInv
                    c0_hsteps_nogrp
                    · exact s11Pre_ret20 hQ (.refl c) hlenS hinvWS.cfgOk hinvWS.extOk hfuL
                        (h20S ‹_›).2 (fullM6HdrMem_unfocus hmS)
                    · exact hJ_brkF sS mS hinvS hclL hfuL hmS
                    · refine s11_call_bcp rfl hProp hinvWS (fullM6HdrMem_unfocus hmS)
                        fun pr2 sP mP hinvWP hclP _ _ hfuP hdomP hrP0 hrP1 hmP => ?_
                      have hinvP := hinvWP.toInv
                      have hfuP' : sP.core.fuel.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfuP hfuL
                      c0_hsplit
                      · c0_hsteps
                        exact s11Pre_ret20 hQ (.refl c) hinvP.sparse.lengths hinvP.cfgOk
                          hinvP.extOk hfuP'
                          (s11_conflict_level0_unsat hinvWP.sparseW.2.1 (hclP ▸ hclL)
                            (hrP1 ‹_›).2.2) hmP
                      · c0_hsplit
                        · refine wp_m6Hdr_focus_frame hmP fun hmPf => ?_
                          c0_hsteps
                          exact hJ_brkF sP _ hinvP (hclP ▸ hclL) hfuP' hmPf
                        · refine wp_m6Hdr_focus_frame hmP fun hmPf => ?_
                          have hpr2_0 : pr2 = 0#64 := by
                            rcases hdomP with rfl | rfl | rfl <;> first | rfl | contradiction
                          have hpeq := (hrP0 hpr2_0).1
                          c0_hsplit
                          · c0_hsplit
                            · c0_hsteps
                              exact hJ_brkF sP _ hinvP (hclP ▸ hclL) hfuP' hmPf
                            · exfalso
                              have hbv_eq : BitVec.ofNat 64 sP.core.propagated =
                                  BitVec.ofNat 64 sP.core.trail_end :=
                                congrArg (BitVec.ofNat 64) hpeq
                              rw [hbv_eq] at *
                              bv_omega
                          · have hsr1_ne : sr2 ≠ 0#64 := by assumption
                            have hsr1_eq : sr2 = 1#64 := by
                              rcases hsr2 with rfl | rfl | rfl | rfl <;>
                                first | rfl | contradiction
                            have hte_lt := (hrP0 hpr2_0).2.2 (by
                              change sL.core.propagated < teS
                              have := (hsr1 hsr1_eq).2; omega)
                            have hfu_lt : sP.core.fuel.toNat < sL.core.fuel.toNat := hte_lt
                            c0_hsteps
                            exact ihL sP _ hfu_lt ⟨hinvP, hclP ▸ hclL, hfuP', hmPf⟩
                  · cases hc
            · intro Jb hJb; c0_hsplit
              · exact hJb () _ rfl
              · c0_hsplit
                · exact hJb () _ rfl
                · exact hJ3u () _ ⟨s3t, hinv3, hcl3, hfu3', fullM6HdrMem_unfocus (by assumption)⟩
    · exact fun _ hJ2 =>
        s11_pre_unflushed hProp hSweep hinv1 hcl1' hfu1 (fullM6HdrMem_unfocus hm1f) hJ2 hQ

end LeanQbe.T.Examples.Kissat.FullFidelityStep11

end
