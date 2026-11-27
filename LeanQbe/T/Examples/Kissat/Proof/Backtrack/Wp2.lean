/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Wp1
import LeanQbe.T.Examples.Kissat.Proof.Backtrack.WitnessLemmas
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv1
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Backtrack WP Proofs — Part 2 (`Proof.Backtrack.Wp2`)

Parametric `(Γ : Env)` `Func.wp` proofs (`public section`, `0` `@[expose]` on theorems/lemmas,
`0` `import all`, `std3`) for:
1. `full_backtrack` (`fullBacktrackSpec`)
2. `full_backtrack_ac_fid` (`fullBacktrackSpec`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Backtrack

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
open LeanQbe.T.Examples.Kissat.Src.Backtrack
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics

local elab "bt2_steps_nogrp" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, splitJnz := false } 10000

local macro "bt2_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

private theorem bv64_sub1_toNat' {n : Nat} (hn0 : 0 < n) (hn64 : n < 2 ^ 64) :
    (BitVec.ofNat 64 n - 1#64).toNat = n - 1 := by
  rw [BitVec.toNat_sub, bv64_ofNat_toNat' hn64, show (1#64 : BitVec 64).toNat = 1 from rfl]
  omega

private abbrev btSaveScratchUpd (sc : FullScratch) (ta ba : BitVec 64)
    (pt pb : List (BitVec 8)) : FullScratch :=
  { sc with
    target_assigned := ta, best_assigned := ba,
    phases_target := pt, phases_best := pb }

private abbrev btRawScratchUpd (sc : FullScratch) (ta ba : BitVec 64) (pt pb : List (BitVec 8))
    (hp ps : List (BitVec 32)) (hl : Nat) (qsi qss : BitVec 64) : FullScratch :=
  { sc with
    target_assigned := ta, best_assigned := ba,
    phases_target := pt, phases_best := pb,
    heap := hp, pos := ps, heap_len := hl,
    q_search_idx := qsi, q_search_stamp := qss }

private theorem bt_probing_raw_tail_wp {Γ : Env}
    (hRaw : ∀ a m Q X, fullBacktrackRawSpec a m Q X →
      Γ "full_backtrack_raw_m5" [i64, i64] [] a m Q X)
    {c : FullCfg} {s s1 : FullState} {R : Mem 64 → Prop} {Q : Post []} {X : XPost}
    {target_lvl : Val i64} {m1 : Mem 64}
    (hcore1 : s1.core = s.core) (hlen1 : FullState.LengthsOk c s1)
    (hpres1 : FullProbeScratchPres s s1)
    (hsc1 : ∃ ta1 ba1 pt1 pb1, s1.scratch = btSaveScratchUpd s.scratch ta1 ba1 pt1 pb1)
    (hcl64 : s.core.cur_level < 2 ^ 64)
    (htv_max : target_lvl.toNat < s.core.cur_level → target_lvl.toNat < c.max_vars)
    (htrl_bd : ∀ i < s.core.trail_end, (s.core.trl[i]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hm1 : (FullMem c s1 ⋆ R) m1)
    (hPost : ∀ vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m',
      let s' : FullState :=
        { core := { s.core with
            unassigned := unass', vals := vals', lvl := lvl', rsns := rsns',
            trl := trl', trail_pos := tp', trail_end := te', propagated := prop',
            cur_level := cl' },
          scratch := sc' }
      FullState.LengthsOk c s' → te' ≤ s.core.trail_end → prop' ≤ te' →
      cl' = min s.core.cur_level target_lvl.toNat →
      FullProbeScratchPres s s' →
      (∃ ta' ba' pt' pb' hp' ps' hl' qsi' qss',
        sc' = btRawScratchUpd s.scratch ta' ba' pt' pb' hp' ps' hl' qsi' qss') →
      (∀ i < te', (trl'[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) →
      ((∃ F0 F_cur, FullWitnessInv c F0 F_cur s.core ∨ FullOtfsWitnessInv c F0 F_cur s.core) →
        (∀ l < 2 * s.core.cur_vars,
          vals'[l]?.getD 0#8 =
            if (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ target_lvl.toNat
            then s.core.vals[l]?.getD 0#8 else 0#8) ∧
        (∀ i < s.core.trail_end,
          let v := (s.core.trl[i]?.getD 0#32).toNat / 2
          lvl'[v]?.getD 0#32 =
            if (s.core.lvl[v]?.getD 0#32).toNat ≤ target_lvl.toNat
            then s.core.lvl[v]?.getD 0#32 else 0#32)) →
      (∀ F0 F_cur, FullWitnessInv c F0 F_cur s.core → target_lvl.toNat ≤ s.core.cur_level →
        FullWitnessInv c F0 F_cur s'.core) →
      (∀ F0 F_cur, FullOtfsWitnessInv c F0 F_cur s.core → target_lvl.toNat < s.core.cur_level →
        FullWitnessInv c F0 F_cur s'.core) →
      (FullMem c s' ⋆ R) m' → Q () m') :
    wp Γ Q X
      (Expr.let_
        { sig := [i64, i64], code := OpCode.add i64,
          args := (Arg.var (V := Val) (t := i64) c.hdr, Arg.imm (V := Val) (t := i64) 520, ()) }
        fun p => Expr.load i64 (Arg.var p.fst) fun ld =>
          Expr.let_
            { sig := [i64, i64], code := OpCode.add i64,
              args := (Arg.var (V := Val) (t := i64) c.hdr, Arg.imm (V := Val) (t := i64) 520, ()) }
            fun p => Expr.store (Arg.imm (V := Val) (t := i64) 1) (Arg.var p.fst)
              (Expr.call (V := Val) (L := Cont) (rs := []) (as := [i64, i64]) (bs := [])
                "full_backtrack_raw_m5"
                (Arg.var (V := Val) (t := i64) c.hdr, Arg.var (V := Val) (t := i64) target_lvl, ())
                fun _ =>
                Expr.let_
                  { sig := [i64, i64], code := OpCode.add i64,
                    args := (Arg.var (V := Val) (t := i64) c.hdr,
                      Arg.imm (V := Val) (t := i64) 520, ()) }
                  fun p => Expr.store (Arg.var ld) (Arg.var p.fst) (Expr.ret ()))) m1 := by
  bt2_steps_nogrp
  let s1p : FullState := ⟨{ s1.core with probing := 1#64 }, s1.scratch⟩
  bt2_call hRaw
  refine ⟨c, s1p, R, rfl, bt_lengthsOk_with_probing 1#64 hlen1, ?_, ?_, ?_, (by assumption), ?_⟩
  · simpa only [s1p, hcore1] using hcl64
  · change BitVec.toNat target_lvl < s1p.core.cur_level → BitVec.toNat target_lvl < c.max_vars
    simpa only [s1p, hcore1] using htv_max
  · simpa only [s1p, hcore1] using htrl_bd
  · intro vals2 lvl2 rsns2 trl2 tp2 te2 prop2 cl2 unass2 sc2 m2 s2_st
      hlen2 hte2 hprop2 hcl2 hpres2 hsc2 htrl2 _hlvl_k hinv_eq2 hw2 hotfs2 _hm2
    bt2_steps_nogrp
    dsimp only [s2_st] at *
    have harg : (Arg.var (V := Val) (t := i64) target_lvl).val = target_lvl := rfl
    have hcore_restore :
        (let k2 := s1p.core
         let k3 : FullCoreState := { k2 with
           unassigned := unass2, vals := vals2, lvl := lvl2, rsns := rsns2,
           trl := trl2, trail_pos := tp2, trail_end := te2, propagated := prop2,
           cur_level := cl2 }
         { k3 with probing := s1.core.probing }) =
        (let k0 := s.core
         { k0 with
           unassigned := unass2, vals := vals2, lvl := lvl2, rsns := rsns2,
           trl := trl2, trail_pos := tp2, trail_end := te2, propagated := prop2,
           cur_level := cl2 }) := by
      simp only [s1p, hcore1]
    obtain ⟨ta1, ba1, pt1, pb1, hsc1_eq⟩ := hsc1
    obtain ⟨ta2, ba2, pt2, pb2, hp2, ps2, hl2, qsi2, qss2, hsc2_eq⟩ := hsc2
    have hsc_eq : sc2 = btRawScratchUpd s.scratch ta2 ba2 pt2 pb2 hp2 ps2 hl2 qsi2 qss2 := by
      rw [hsc2_eq, hsc1_eq]
    refine hPost vals2 lvl2 rsns2 trl2 tp2 te2 prop2 cl2 unass2 sc2 _
      ⟨by simpa only [hcore_restore] using
            (bt_lengthsOk_with_probing s1.core.probing hlen2).core_ok,
       hlen2.scratch_ok⟩
      (by simpa only [s1p, hcore1] using hte2) hprop2
      (by simpa only [s1p, hcore1, harg] using hcl2)
      (bt_fullProbeScratchPres_trans hpres1 hpres2)
      ⟨ta2, ba2, pt2, pb2, hp2, ps2, hl2, qsi2, qss2, hsc_eq⟩
      (by simpa only [s1p, hcore1] using htrl2)
      (fun ⟨F0, F_cur, hw⟩ => by
        rcases hw with hw | hw
        · simpa only [s1p, hcore1, harg] using
            hinv_eq2 ⟨F0, F_cur, Or.inl (bt_witness_with_probing 1#64 (by rwa [← hcore1] at hw))⟩
        · simpa only [s1p, hcore1, harg] using
            hinv_eq2
              ⟨F0, F_cur, Or.inr (bt_otfsWitness_with_probing 1#64 (by rwa [← hcore1] at hw))⟩)
      (fun F0 F_cur hw hle_c => by
        have hw1 := bt_witness_with_probing 1#64
          (by simpa only [hcore1] using hw : FullWitnessInv c F0 F_cur s1.core)
        have hw2 := hw2 F0 F_cur hw1 (by simpa only [s1p, hcore1, harg] using hle_c)
        simpa only [hcore_restore] using bt_witness_with_probing s1.core.probing hw2)
      (fun F0 F_cur hw hlt_c => by
        have hw1 := bt_otfsWitness_with_probing 1#64
          (by simpa only [hcore1] using hw : FullOtfsWitnessInv c F0 F_cur s1.core)
        have hw2 := hotfs2 F0 F_cur hw1 (by simpa only [s1p, hcore1, harg] using hlt_c)
        simpa only [hcore_restore] using bt_witness_with_probing s1.core.probing hw2)
      (by dsimp only [s1p] at hm; rw [hcore1] at hm; exact hm)

theorem full_backtrack_wp (Γ : Env)
    (hSave : ∀ a m Q X, fullSaveTargetBestSpec a m Q X →
      Γ "full_save_target_best" [i64] [] a m Q X)
    (hRaw : ∀ a m Q X, fullBacktrackRawSpec a m Q X →
      Γ "full_backtrack_raw_m5" [i64, i64] [] a m Q X) :
    ∀ a m Q X, fullBacktrackSpec a m Q X →
      Func.wp Γ full_backtrack_body a m Q X := by
  rintro ⟨h, target_lvl, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hcl64, htv_max, htrl_bd, hm, hPost⟩
  unfold Func.wp full_backtrack_body
  bt2_steps_nogrp
  refine wp_jnz_of (fun hc => ?_) (fun hnc => ?_)
  · bt2_steps_nogrp
    have hle : s.core.cur_level ≤ target_lvl.toNat := by
      have h1 := bv64_ule_true_le' hc
      rwa [bv64_ofNat_toNat' hcl64] at h1
    exact bt_post_noop_raw hlen hle htrl_bd hm (fun vals' lvl' rsns' trl' tp' te' prop' cl'
      unass' sc' m' h1 h2 h3 h4 h5 h6 h7 _ h9 h10 h11 h12 =>
      hPost vals' lvl' rsns' trl' tp' te' prop' cl'
        unass' sc' m' h1 h2 h3 h4 h5 h6 h7 h9 h10 h11 h12)
  · bt2_steps_nogrp
    bt2_call hSave
    refine ⟨c, s, R, rfl, hlen, hm, ?_⟩
    intro _ s1 m1 hcore1 hlen1 ⟨hpres1, ta1, ba1, pt1, pb1, hsc1⟩ hm1
    dsimp only [fullSafetySlice] at hlen1 hm1
    have hcore1_eq : s1.core = s.core := fullCoreState_agrees_with_scratch hcore1
    exact bt_probing_raw_tail_wp hRaw hcore1_eq hlen1 hpres1 ⟨ta1, ba1, pt1, pb1, hsc1⟩
      hcl64 htv_max htrl_bd hm1 hPost

theorem full_backtrack_ac_fid_wp (Γ : Env)
    (hSave : ∀ a m Q X, fullSaveTargetBestSpec a m Q X →
      Γ "full_save_target_best" [i64] [] a m Q X)
    (hRaw : ∀ a m Q X, fullBacktrackRawSpec a m Q X →
      Γ "full_backtrack_raw_m5" [i64, i64] [] a m Q X) :
    ∀ a m Q X, fullBacktrackSpec a m Q X →
      Func.wp Γ full_backtrack_ac_fid_body a m Q X := by
  rintro ⟨h, target_lvl, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hcl64, htv_max, htrl_bd, hm, hPost⟩
  unfold Func.wp full_backtrack_ac_fid_body
  bt2_steps_nogrp
  refine wp_jnz_of (fun hc => ?_) (fun hnc => ?_)
  · bt2_steps_nogrp
    have hle : s.core.cur_level ≤ target_lvl.toNat := by
      have h1 := bv64_ule_true_le' hc
      rwa [bv64_ofNat_toNat' hcl64] at h1
    exact bt_post_noop_raw hlen hle htrl_bd hm (fun vals' lvl' rsns' trl' tp' te' prop' cl'
      unass' sc' m' h1 h2 h3 h4 h5 h6 h7 _ h9 h10 h11 h12 =>
      hPost vals' lvl' rsns' trl' tp' te' prop' cl'
        unass' sc' m' h1 h2 h3 h4 h5 h6 h7 h9 h10 h11 h12)
  · bt2_steps_nogrp
    refine wp_unroll_group (fun Jtail hJtail => ?_)
    have hJ_of : ∀ (s1 : FullState) (m1 : Mem 64),
        s1.core = s.core → FullState.LengthsOk c s1 → FullProbeScratchPres s s1 →
        (∃ ta1 ba1 pt1 pb1, s1.scratch = btSaveScratchUpd s.scratch ta1 ba1 pt1 pb1) →
        (FullMem c s1 ⋆ R) m1 → Jtail () m1 :=
      fun s1 m1 hcore1 hlen1 hpres1 hsc1 hm1 =>
        hJtail () m1
          (bt_probing_raw_tail_wp hRaw hcore1 hlen1 hpres1 hsc1 hcl64 htv_max htrl_bd hm1 hPost)
    clear hJtail
    bt2_steps_nogrp
    refine wp_jnz_of (fun hprob => ?_) (fun hnprob => ?_)
    · bt2_steps_nogrp
      refine wp_jnz_of (fun hstab => ?_) (fun hnstab => ?_)
      · bt2_steps_nogrp
        refine wp_jnz_of (fun hmv => ?_) (fun hnmv => ?_)
        · bt2_steps_nogrp
          have hprob0 : s.core.probing = 0#64 :=
            beq_iff_eq.mp (by change (s.core.probing == 0#64) = true; exact hprob)
          have hcl_lt : target_lvl.toNat < s.core.cur_level := by
            have h1 := bv64_ule_false_lt' hnc
            rwa [bv64_ofNat_toNat' hcl64] at h1
          have hm1_bv_nat : (BitVec.ofNat 64 s.core.cur_level - 1).toNat = s.core.cur_level - 1 :=
            bv64_sub1_toNat' (by omega) hcl64
          have hm1_nat :
              (Arg.var (V := Val) (t := i64)
                  (BitVec.ofNat 64 s.core.cur_level - 1, ()).fst).val.toNat =
                s.core.cur_level - 1 := hm1_bv_nat
          have hmv_lt : s.core.cur_level - 1 < c.max_vars := by
            have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
            have h1 := bv64_ult_true_lt' hmv
            rwa [hm1_bv_nat, bv64_ofNat_toNat' (by omega)] at h1
          let s0p : FullState := ⟨{ (s.core) with probing := 1#64 }, s.scratch⟩
          bt2_call hRaw
          refine ⟨c, s0p, R, rfl, bt_lengthsOk_with_probing 1#64 hlen,
            (by simpa only [s0p] using hcl64),
            (fun _ => by rwa [hm1_nat]),
            (by simpa only [s0p] using htrl_bd), (by assumption), ?_⟩
          intro vals1 lvl1 rsns1 trl1 tp1 te1 prop1 cl1 unass1 sc1 m1 s1_st
            hlen1 hte1 hprop1 hcl1 hpres1 hsc1 htrl1 hlvl1_k hinv_eq1 hw1 hotfs1 _hm1
          bt2_steps_nogrp
          dsimp only [s1_st] at hlen1 hinv_eq1 hw1 hotfs1
          let s1z : FullState :=
            ⟨{ (s.core) with
                unassigned := unass1, vals := vals1, lvl := lvl1, rsns := rsns1,
                trl := trl1, trail_pos := tp1, trail_end := te1, propagated := prop1,
                cur_level := cl1, probing := 0#64 },
              sc1⟩
          have hs1_eq_core : { (s0p.core) with
              unassigned := unass1, vals := vals1, lvl := lvl1, rsns := rsns1,
              trl := trl1, trail_pos := tp1, trail_end := te1, propagated := prop1,
              cur_level := cl1 } = { s1z.core with probing := 1#64 } := rfl
          have hlen1z : FullState.LengthsOk c s1z := by
            simpa only [s1z] using (bt_lengthsOk_with_probing 0#64 hlen1)
          have hcl1_eq : cl1 = s.core.cur_level - 1 := by
            simpa only [s0p, hm1_nat, Nat.min_eq_right (Nat.sub_le _ _)] using hcl1
          have hinv_s1z : ∀ F0 F_cur,
              (FullWitnessInv c F0 F_cur s.core ∨ FullOtfsWitnessInv c F0 F_cur s.core) →
              FullWitnessInv c F0 F_cur s1z.core := by
            intro F0 F_cur h
            have hw' : FullWitnessInv c F0 F_cur
                { (s0p.core) with
                  unassigned := unass1, vals := vals1, lvl := lvl1, rsns := rsns1,
                  trl := trl1, trail_pos := tp1, trail_end := te1, propagated := prop1,
                  cur_level := cl1 } := by
              rcases h with h | h
              · exact hw1 F0 F_cur (bt_witness_with_probing 1#64 h)
                  (by simpa only [s0p, hm1_nat] using Nat.sub_le _ _)
              · exact hotfs1 F0 F_cur (bt_otfsWitness_with_probing 1#64 h)
                  (by simpa only [s0p, hm1_nat] using Nat.sub_lt (by omega) Nat.zero_lt_one)
            simpa only [hs1_eq_core] using bt_witness_with_probing 0#64 hw'
          bt2_call hSave
          refine ⟨c, s1z, R, rfl, hlen1z, (by assumption), ?_⟩
          intro _ s2 m2 hcore2 hlen2 ⟨hpres2, ta2, ba2, pt2, pb2, hsc2⟩ hm2
          dsimp only [fullSafetySlice] at hlen2 hm2
          have hcore2_eq : s2.core = s1z.core := fullCoreState_agrees_with_scratch hcore2
          bt2_steps_nogrp
          refine wp_unroll_group (fun Jret hJret => ?_)
          bt2_steps_nogrp
          refine wp_jnz_of (fun hlt2 => ?_) (fun hnlt2 => ?_)
          · bt2_steps_nogrp
            have hlt2_nat : target_lvl.toNat < s.core.cur_level - 1 := by
              have h1 := bv64_ult_true_lt' hlt2
              rwa [hm1_bv_nat] at h1
            let s2p : FullState := ⟨{ (s2.core) with probing := 1#64 }, s2.scratch⟩
            bt2_call hRaw
            refine ⟨c, s2p, R, rfl, bt_lengthsOk_with_probing 1#64 hlen2,
              (by simpa only [s2p, hcore2_eq, s1z, hcl1_eq] using
                Nat.lt_trans (Nat.sub_lt (by omega) Nat.zero_lt_one) hcl64),
              (fun _ => htv_max hcl_lt),
              (by simpa only [s2p, hcore2_eq, s1z] using htrl1), (by assumption), ?_⟩
            intro vals3 lvl3 rsns3 trl3 tp3 te3 prop3 cl3 unass3 sc3 m3 s3_st
              hlen3 hte3 hprop3 hcl3 hpres3 hsc3 htrl3 hlvl3_k hinv_eq3 hw3 _hotfs3 hm3
            have harg : (Arg.var (V := Val) (t := i64) target_lvl).val = target_lvl := rfl
            dsimp only [s3_st] at hlen3 hinv_eq3 hw3 hm3
            have hDone : ∀ m_fin
                (hm_fin : (FullMem c ⟨{ (s.core) with
                    unassigned := unass3, vals := vals3, lvl := lvl3, rsns := rsns3,
                    trl := trl3, trail_pos := tp3, trail_end := te3, propagated := prop3,
                    cur_level := cl3 }, sc3⟩ ⋆ R) m_fin), Q () m_fin := by
              intro m_fin hm_fin
              have hcore3_eq : { (s.core) with
                  unassigned := unass3, vals := vals3, lvl := lvl3, rsns := rsns3,
                  trl := trl3, trail_pos := tp3, trail_end := te3, propagated := prop3,
                  cur_level := cl3 } =
                { ({ (s2p.core) with
                    unassigned := unass3, vals := vals3, lvl := lvl3, rsns := rsns3,
                    trl := trl3, trail_pos := tp3, trail_end := te3, propagated := prop3,
                    cur_level := cl3 } : FullCoreState) with probing := s.core.probing } := by
                simp only [s2p, hcore2_eq, s1z, hprob0]
              obtain ⟨ta1, ba1, pt1, pb1, hp1, ps1, hl1, qsi1, qss1, hsc1_eq⟩ := hsc1
              obtain ⟨ta3, ba3, pt3, pb3, hp3, ps3, hl3, qsi3, qss3, hsc3_eq⟩ := hsc3
              have hsc_fin :
                  sc3 = btRawScratchUpd s.scratch ta3 ba3 pt3 pb3 hp3 ps3 hl3 qsi3 qss3 := by
                rw [hsc3_eq, hsc2]; dsimp only [s1z, s0p]; rw [hsc1_eq]
              refine hPost vals3 lvl3 rsns3 trl3 tp3 te3 prop3 cl3 unass3 sc3 m_fin
                ⟨by simpa only [← hcore3_eq] using
                      (bt_lengthsOk_with_probing s.core.probing hlen3).core_ok,
                 hlen3.scratch_ok⟩
                (Nat.le_trans hte3 (by simpa only [s2p, hcore2_eq, s1z] using hte1))
                hprop3
                (by rw [hcl3]; simp only [s2p, hcore2_eq, s1z, hcl1_eq, harg]; omega)
                (bt_fullProbeScratchPres_trans hpres1 (bt_fullProbeScratchPres_trans hpres2 hpres3))
                ⟨ta3, ba3, pt3, pb3, hp3, ps3, hl3, qsi3, qss3, hsc_fin⟩
                (by simpa only [s2p, hcore2_eq, s1z] using htrl3)
                ?_ ?_ ?_ hm_fin
              · rintro ⟨F0, F_cur, hw⟩
                have hw1_full : FullWitnessInv c F0 F_cur s1z.core := hinv_s1z F0 F_cur hw
                have hw2_full : FullWitnessInv c F0 F_cur s2p.core := by
                  simpa only [s2p, hcore2_eq] using bt_witness_with_probing 1#64 hw1_full
                obtain ⟨hvals3, hlvl3⟩ := hinv_eq3 ⟨F0, F_cur, Or.inl hw2_full⟩
                have hinv1 := hinv_eq1 (by
                  rcases hw with hw | hw
                  · exact ⟨F0, F_cur, Or.inl (bt_witness_with_probing 1#64 hw)⟩
                  · exact ⟨F0, F_cur, Or.inr (bt_otfsWitness_with_probing 1#64 hw)⟩)
                refine ⟨fun l hl => ?_, fun i hi => ?_⟩
                · rw [hvals3 l (by simpa only [s2p, hcore2_eq, s1z] using hl)]
                  have hv1 := hinv1.1 l (by simpa only [s0p] using hl)
                  have hl1_eq : (s2p.core.lvl[l / 2]?.getD 0#32).toNat =
                      (lvl1[l / 2]?.getD 0#32).toNat := by simp only [s2p, hcore2_eq, s1z]
                  have hv2_eq : s2p.core.vals[l]?.getD 0#8 = vals1[l]?.getD 0#8 := by
                    simp only [s2p, hcore2_eq, s1z]
                  rw [hl1_eq, hv2_eq, hv1]
                  have htgt_val : (Arg.var target_lvl).val = target_lvl := rfl
                  by_cases hle_tgt : (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ target_lvl.toNat
                  · have hle_m1 :
                        (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level - 1 := by omega
                    have hvl1 := hlvl1_k (l / 2) (by dsimp only [s0p]; omega)
                      (by simpa only [hm1_nat] using hle_m1)
                    have hlv1_le : (lvl1[l / 2]?.getD 0#32).toNat ≤ target_lvl.toNat := by
                      simpa only [s0p, hvl1] using hle_tgt
                    simp only [s0p, hm1_nat, hle_m1, hle_tgt, hlv1_le, htgt_val, ite_true]
                  · simp only [hle_tgt, ite_false]
                    by_cases hle_m1 : (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level - 1
                    · have hvl1 := hlvl1_k (l / 2) (by dsimp only [s0p]; omega)
                        (by simpa only [hm1_nat] using hle_m1)
                      have hlv1_gt : ¬ (lvl1[l / 2]?.getD 0#32).toNat ≤ target_lvl.toNat := by
                        simpa only [s0p, hvl1] using hle_tgt
                      simp only [htgt_val, hlv1_gt, ite_false]
                    · simp only [hm1_nat, hle_m1, ite_false, s0p, ite_self]
                · let lit := (s.core.trl[i]?.getD 0#32).toNat
                  let v := lit / 2
                  have hlit_lt : lit < 2 * s.core.cur_vars := htrl_bd i hi
                  have hv_lt : v < s.core.cur_vars := by omega
                  dsimp only
                  by_cases hle_tgt : (s.core.lvl[v]?.getD 0#32).toNat ≤ target_lvl.toNat
                  · have hle_tgt' :
                        (s.core.lvl[(s.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
                          target_lvl.toNat := hle_tgt
                    simp only [hle_tgt', ite_true]
                    have hle_m1 :
                        (s.core.lvl[v]?.getD 0#32).toNat ≤ s.core.cur_level - 1 := by omega
                    have hvl1 := hlvl1_k v hv_lt (by simpa only [hm1_nat] using hle_m1)
                    have hvl2_le : (s2p.core.lvl[v]?.getD 0#32).toNat ≤ target_lvl.toNat := by
                      simpa only [s2p, hcore2_eq, s1z, s0p, hvl1] using hle_tgt
                    have hvl3 :=
                      hlvl3_k v (by simpa only [s2p, hcore2_eq, s1z] using hv_lt) hvl2_le
                    simpa only [s2p, hcore2_eq, s1z, s0p, hvl1] using hvl3
                  · have hle_tgt' :
                        ¬ (s.core.lvl[(s.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
                            target_lvl.toNat := hle_tgt
                    simp only [hle_tgt', ite_false]
                    by_cases hle_m1 : (s.core.lvl[v]?.getD 0#32).toNat ≤ s.core.cur_level - 1
                    · have hvl1 := hlvl1_k v hv_lt (by simpa only [hm1_nat] using hle_m1)
                      have hs_v1 : s.core.vals[lit]?.getD 0#8 = 1#8 := by
                        rcases hw with hw | hw
                        · exact (hw.vals_true_iff lit hlit_lt).mpr ⟨i, hi, rfl⟩
                        · exact (hw.vals_true_iff lit hlit_lt).mpr ⟨i, hi, rfl⟩
                      have hv1_1 : vals1[lit]?.getD 0#8 = 1#8 := by
                        have h_eq := hinv1.1 lit (by simpa only [s0p] using hlit_lt)
                        have hle_m1_d :
                            (s.core.lvl[lit / 2]?.getD 0#32).toNat ≤ s.core.cur_level - 1 := hle_m1
                        simpa only [s0p, hm1_nat, hle_m1_d, ite_true, hs_v1] using h_eq
                      obtain ⟨j, hj, hj_eq⟩ := (hw1_full.vals_true_iff lit
                        (by simpa only [s1z] using hlit_lt)).mp (by simpa only [s1z] using hv1_1)
                      have hvl3 := hlvl3 j (by simpa only [s2p, hcore2_eq] using hj)
                      have hj_v : (s2p.core.trl[j]?.getD 0#32).toNat / 2 = v := by
                        simp only [s2p, hcore2_eq]; rw [hj_eq]
                      have hvl2_gt : ¬ (s2p.core.lvl[v]?.getD 0#32).toNat ≤ target_lvl.toNat := by
                        simpa only [s2p, hcore2_eq, s1z, s0p, hvl1] using hle_tgt
                      have hvl3' : lvl3[v]?.getD 0#32 = 0#32 := by
                        simpa only [harg, hj_v, hvl2_gt, ite_false] using hvl3
                      exact hvl3'
                    · have hlvl1_0 : lvl1[v]?.getD 0#32 = 0#32 := by
                        have h0 := hinv1.2 i (by simpa only [s0p] using hi)
                        have hle_m1_i :
                            ¬ (s.core.lvl[(s.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
                              s.core.cur_level - 1 := hle_m1
                        simp only [s0p, hm1_nat, hle_m1_i, ite_false] at h0
                        exact h0
                      have h2lvl : s2p.core.lvl = lvl1 := by simp only [s2p, hcore2_eq, s1z]
                      have hvl2_le : (s2p.core.lvl[v]?.getD 0#32).toNat ≤ target_lvl.toNat := by
                        rw [h2lvl, hlvl1_0]; exact Nat.zero_le _
                      have hvl3 :=
                        hlvl3_k v (by simpa only [s2p, hcore2_eq, s1z] using hv_lt) hvl2_le
                      exact hvl3.trans (by rw [h2lvl]; exact hlvl1_0)
              · intro F0 F_cur hw _
                have hw2' : FullWitnessInv c F0 F_cur s2p.core := by
                  simpa only [s2p, hcore2_eq] using
                    bt_witness_with_probing 1#64 (hinv_s1z F0 F_cur (Or.inl hw))
                have hw3' := hw3 F0 F_cur hw2' (by
                  simpa only [s2p, hcore2_eq, s1z, hcl1_eq, harg] using Nat.le_of_lt hlt2_nat)
                simpa only [← hcore3_eq] using bt_witness_with_probing s.core.probing hw3'
              · intro F0 F_cur hw _
                have hw2' : FullWitnessInv c F0 F_cur s2p.core := by
                  simpa only [s2p, hcore2_eq] using
                    bt_witness_with_probing 1#64 (hinv_s1z F0 F_cur (Or.inr hw))
                have hw3' := hw3 F0 F_cur hw2' (by
                  simpa only [s2p, hcore2_eq, s1z, hcl1_eq, harg] using Nat.le_of_lt hlt2_nat)
                simpa only [← hcore3_eq] using bt_witness_with_probing s.core.probing hw3'
            bt2_steps_nogrp
            exact hDone _ (by
              dsimp only at *
              have h0_bv : (0 : BitVec 64) = 0#64 := by decide
              rw [h0_bv] at hm
              simpa only [s2p, hcore2_eq, s1z, hprob0] using hm)
          · bt2_steps_nogrp
            have hle2_nat : s.core.cur_level - 1 ≤ target_lvl.toNat := by
              have h1 := bv64_ult_false_le' hnlt2
              rwa [hm1_bv_nat] at h1
            have htgt_eq : target_lvl.toNat = s.core.cur_level - 1 := by omega
            have hcore2_final : s2.core =
                { (s.core) with
                  unassigned := unass1, vals := vals1, lvl := lvl1, rsns := rsns1,
                  trl := trl1, trail_pos := tp1, trail_end := te1, propagated := prop1,
                  cur_level := cl1 } := by
              rw [hcore2_eq]; simp only [s1z, hprob0]
            obtain ⟨ta1, ba1, pt1, pb1, hp1, ps1, hl1, qsi1, qss1, hsc1_eq⟩ := hsc1
            have hsc_fin : s2.scratch =
                btRawScratchUpd s.scratch ta2 ba2 pt2 pb2 hp1 ps1 hl1 qsi1 qss1 := by
              rw [hsc2]; dsimp only [s1z, s0p]; rw [hsc1_eq]
            have hm2' : (FullMem c ⟨{ (s.core) with
                unassigned := unass1, vals := vals1, lvl := lvl1, rsns := rsns1,
                trl := trl1, trail_pos := tp1, trail_end := te1, propagated := prop1,
                cur_level := cl1 }, s2.scratch⟩ ⋆ R) m2 := by
              simpa only [← hcore2_final] using hm2
            refine hPost vals1 lvl1 rsns1 trl1 tp1 te1 prop1 cl1 unass1 s2.scratch m2
              ⟨by simpa only [← hcore2_final] using hlen2.core_ok, hlen2.scratch_ok⟩
              (by simpa only [s0p] using hte1) hprop1
              (by rw [hcl1_eq, htgt_eq]; omega)
              (bt_fullProbeScratchPres_trans hpres1 hpres2)
              ⟨ta2, ba2, pt2, pb2, hp1, ps1, hl1, qsi1, qss1, hsc_fin⟩
              (by simpa only [s0p] using htrl1)
              ?_ ?_ ?_ hm2'
            · rintro ⟨F0, F_cur, hw⟩
              have hinv1 := hinv_eq1 (by
                rcases hw with hw | hw
                · exact ⟨F0, F_cur, Or.inl (bt_witness_with_probing 1#64 hw)⟩
                · exact ⟨F0, F_cur, Or.inr (bt_otfsWitness_with_probing 1#64 hw)⟩)
              simpa only [s0p, hm1_nat, htgt_eq] using hinv1
            · intro F0 F_cur hw _
              simpa only [← hcore2_final, hcore2_eq] using hinv_s1z F0 F_cur (Or.inl hw)
            · intro F0 F_cur hw _
              simpa only [← hcore2_final, hcore2_eq] using hinv_s1z F0 F_cur (Or.inr hw)
        · bt2_steps_nogrp
          bt2_call hSave
          refine ⟨c, s, R, rfl, hlen, hm, ?_⟩
          intro _ s1 m1 hcore1 hlen1 ⟨hpres1, ta1, ba1, pt1, pb1, hsc1⟩ hm1
          dsimp only [fullSafetySlice] at hlen1 hm1
          bt2_steps_nogrp
          exact hJ_of s1 m1 (fullCoreState_agrees_with_scratch hcore1) hlen1 hpres1
            ⟨ta1, ba1, pt1, pb1, hsc1⟩ hm1
      · bt2_steps_nogrp
        exact hJ_of s m rfl hlen (bt_fullProbeScratchPres_refl s)
          ⟨s.scratch.target_assigned, s.scratch.best_assigned, s.scratch.phases_target,
            s.scratch.phases_best, rfl⟩ hm
    · bt2_steps_nogrp
      exact hJ_of s m rfl hlen (bt_fullProbeScratchPres_refl s)
        ⟨s.scratch.target_assigned, s.scratch.best_assigned, s.scratch.phases_target,
          s.scratch.phases_best, rfl⟩ hm

end LeanQbe.T.Examples.Kissat.Proof.Backtrack
