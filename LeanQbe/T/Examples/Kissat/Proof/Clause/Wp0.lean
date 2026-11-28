/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Clause
public import LeanQbe.T.Examples.Kissat.Proof.Clause.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Clause.Helpers
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts4
import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation
meta import LeanQbe.T.Logic.C0Step
meta import LeanQbe.T.Logic.C0HeadStep

/-!
# WP Proofs for `Src.Clause` Part 0 (`Proof.Clause.Wp0`)

Canonical parametric `(Γ : Env)` `Func.wp` proofs for binary and unit clause insertion:
1. `full_add_bin_m6_wp` (`Proof.Spec.fullAddBinSpec`)
2. `full_add_bin_wp` (`Proof.Spec.fullAddBinSpec`)
3. `full_add_unit_wp` (`Proof.Spec.fullAddUnitSpec`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Clause

open Std.Sat
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Clause
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullBvaFwdTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open Kraken.Bedrock2.Test

/-! ## 1. Pure Post-Condition & Entailment Helpers -/

private theorem add_bin_entails_unit_of_fals {F_cur : List (List Nat)} {a b : Nat}
    (h1 : (cnfOfClauses F_cur).EntailsClause (cnfClause [a, b]))
    (h2 : (cnfOfClauses F_cur).EntailsClause (cnfClause [a ^^^ 1])) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [b]) :=
  entails_of_mem_or_false h1 fun l hl => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · exact .inr h2
    · exact .inl List.mem_cons_self

private theorem add_bin_entails_unit_self {F_cur : List (List Nat)} {a : Nat}
    (h1 : (cnfOfClauses F_cur).EntailsClause (cnfClause [a, a])) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [a]) :=
  entails_of_mem_or_false h1 fun l hl => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;> exact .inl List.mem_cons_self

private theorem add_bin_false_lit_entailed {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k)
    (hcl0 : k.cur_level = 0) {l : Nat} (hlt : l < 2 * k.cur_vars)
    (hfals : k.vals[l]?.getD 0#8 = 0xFF#8) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [l ^^^ 1]) := by
  obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff l hlt).mp hfals
  have h0 := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega)
  rwa [heq] at h0

private theorem add_bin_conflict_unsat {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k)
    (hcl0 : k.cur_level = 0) {a b : Nat} (ha : a < 2 * k.cur_vars) (hb : b < 2 * k.cur_vars)
    (hfa : k.vals[a]?.getD 0#8 = 0xFF#8) (hfb : k.vals[b]?.getD 0#8 = 0xFF#8)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [a, b])) :
    (cnfOfClauses F_cur).Unsat := by
  refine unsat_of_entails_nil (entails_of_mem_or_false hent fun l hl => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl <;> right
  · exact add_bin_false_lit_entailed hw hcl0 ha hfa
  · exact add_bin_false_lit_entailed hw hcl0 hb hfb

private theorem i8_vals_eq0_of_not_pos_neg {b : BitVec 8}
    (hd : b = 0#8 ∨ b = 1#8 ∨ b = 0xFF#8)
    (hnpos : (0#32 : BitVec 32).slt (b.signExtend 32) = false)
    (hnneg : (b.signExtend 32).slt 0#32 = false) : b = 0#8 := by
  rcases hd with rfl | rfl | rfl
  · rfl
  · simp at hnpos
  · simp at hnneg

private theorem add_bin_assign_post {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {Q : Post [i64]} {m' : Mem 64}
    (hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core) (hcl0 : s.core.cur_level = 0)
    {lit : BitVec 32} (hlt : lit.toNat < 2 * s.core.cur_vars)
    (hun : s.core.vals[lit.toNat]?.getD 0#8 = 0#8)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat]))
    {flags' : List (BitVec 32)} {unass' : BitVec 64} {phases' : List (BitVec 8)}
    (hf_len : flags'.length = c.max_vars) (hp_len : phases'.length = c.max_vars)
    (hm' : (FullMem c { s with
      core := { s.core with
        vals := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
        flags := flags'
        lvl := s.core.lvl.set (lit.toNat / 2) 0#32
        rsns := s.core.rsns.set (lit.toNat / 2) 0xFFFFFFFF#32
        trl := s.core.trl.set s.core.trail_end lit
        trail_pos := s.core.trail_pos.set (lit.toNat / 2) (BitVec.ofNat 32 s.core.trail_end)
        trail_end := s.core.trail_end + 1
        unassigned := unass'
        unflushed := s.core.unflushed + 1#64 }
      scratch := { s.scratch with phases := phases' } } ⋆ R) m')
    (hQ : ∀ r vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' wlen' wu'
      nb' oom' inc' phases' wsort' m',
      let s' : FullState :=
        { s with
          core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                trl := trl', trail_pos := tp', trail_end := te',
                                unassigned := unass', unflushed := unfl', wvec := wvec',
                                wstk := wstk', wlen := wlen', wusable := wu', num_binary := nb',
                                oom := oom', inconsistent := inc' }
          scratch := { s.scratch with phases := phases', wsort := wsort' } }
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat ∧ inc' ≠ 0#64) →
      (r = 2#64 → oom' ≠ 0#64) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    Q (1#64, ()) m' := by
  have hcl := hlen.core_ok
  have hte_lt := hw.trail_end_lt_of_unassigned hlt hun
  have hte_mv : s.core.trail_end < c.max_vars := Nat.lt_of_lt_of_le hte_lt hcl.cur_vars_le
  have hlen' : FullState.LengthsOk c { s with
      core := { s.core with
        vals := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
        flags := flags'
        lvl := s.core.lvl.set (lit.toNat / 2) 0#32
        rsns := s.core.rsns.set (lit.toNat / 2) 0xFFFFFFFF#32
        trl := s.core.trl.set s.core.trail_end lit
        trail_pos := s.core.trail_pos.set (lit.toNat / 2) (BitVec.ofNat 32 s.core.trail_end)
        trail_end := s.core.trail_end + 1
        unassigned := unass'
        unflushed := s.core.unflushed + 1#64 }
      scratch := { s.scratch with phases := phases' } } :=
    ⟨{ hcl with
       vals_len := by simp [hcl.vals_len]
       flags_len := hf_len
       lvl_len := by simp [hcl.lvl_len]
       rsns_len := by simp [hcl.rsns_len]
       trl_len := by simp [hcl.trl_len]
       trail_pos_len := by simp [hcl.trail_pos_len]
       trail_end_le := hte_lt
       propagated_le := Nat.le_trans hcl.propagated_le (Nat.le_succ _) },
     { hlen.scratch_ok with phases_len := hp_len }⟩
  have hw' := assignLevel0_preserves_fullWitness hlen hw hcl0 hlt hun hent flags' unass'
    (s.core.unflushed + 1#64)
  exact hQ 1#64 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' hlen' hw'
    (.inr (.inl rfl)) (fun h => by cases h) (fun h => by cases h) hm'

/-! ## 2. `full_add_bin_m6_wp` & `full_add_bin_wp` -/

/-- Canonical `Func.wp` proof for `full_add_bin_m6` against `Proof.Spec.fullAddBinSpec`. -/
theorem full_add_bin_m6_wp (Γ : Env)
    (hHasBin : Γ.Has "full_has_bin" Proof.Spec.fullHasBinSpec)
    (hWatchPush : Γ.Has "full_watch_push" Proof.Spec.fullWatchPushSpec)
    (hAssignLvl : Γ.Has "full_assign_lvl" Proof.Spec.fullAssignLvlSpec) :
    ∀ a m Q X, Proof.Spec.fullAddBinSpec a m Q X → Func.wp Γ full_add_bin_m6_body a m Q X := by
  rintro ⟨h, a, b, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hcl0, hent, hm, hQ⟩
  unfold Func.wp full_add_bin_m6_body
  have hcl := hlen.core_ok
  have hcv_le : s.core.cur_vars ≤ c.max_vars := hcl.cur_vars_le
  have hmax_lt : 2 * c.max_vars < 0x7FFFFFFF := by
    have hmx := c.hmaxv; unfold dimacsBound at hmx; omega
  have hnlits : (BitVec.ofNat 64 s.core.cur_vars <<< 1).toNat = 2 * s.core.cur_vars := by
    rw [BitVec.toNat_shiftLeft, bv64_ofNat_toNat (by omega), Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (by omega)]; omega
  have hvals_len : s.core.vals.length = 2 * c.max_vars := hcl.vals_len
  have hfl_len : s.core.flags.length = c.max_vars := hcl.flags_len
  c0_hsteps_nogrp
  · exact hQ 0#64 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m hlen hw (.inl rfl)
      (fun h => by cases h) (fun h => by cases h) hm
  · exact hQ 0#64 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m hlen hw (.inl rfl)
      (fun h => by cases h) (fun h => by cases h) hm
  · exact hQ 0#64 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m hlen hw (.inl rfl)
      (fun h => by cases h) (fun h => by cases h) hm
  · exact hQ 0#64 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m hlen hw (.inl rfl)
      (fun h => by cases h) (fun h => by cases h) hm
  · exact hQ 0#64 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m hlen hw (.inl rfl)
      (fun h => by cases h) (fun h => by cases h) hm
  · have ha_lt : a.toNat < 2 * s.core.cur_vars := by c0_bound
    have hb_lt : b.toNat < 2 * s.core.cur_vars := by c0_bound
    have ha_vl : a.toNat < s.core.vals.length := by omega
    have hb_vl : b.toNat < s.core.vals.length := by omega
    have ha_fl : (a >>> 1#32).toNat < c.max_vars :=
      Nat.lt_of_lt_of_le (bv32_shr1_lt_vars ha_lt) hcv_le
    have hb_fl : (b >>> 1#32).toNat < c.max_vars :=
      Nat.lt_of_lt_of_le (bv32_shr1_lt_vars hb_lt) hcv_le
    have hdom_a := hw.vals_domain a.toNat ha_lt
    have hdom_b := hw.vals_domain b.toNat hb_lt
    have hent_ab := hent ha_lt hb_lt
    refine wp_join_group (ts := [])
      (fun _ m1 => m1 = m ∧
        (s.core.vals[a.toNat]?.getD 0#8 = 0#8 ∨ s.core.vals[b.toNat]?.getD 0#8 = 0#8))
      ?_ ?_
    · rintro _ ⟨⟩ m1 ⟨rfl, hnot_both_fals⟩
      dsimp only [Blocks.get]
      c0_hsteps_nogrp
      refine wp_join_group (ts := [])
        (fun _ m2 => m2 = m1 ∧
          ((s.core.vals[a.toNat]?.getD 0#8 = 0xFF#8 ∧
            s.core.vals[b.toNat]?.getD 0#8 = 0#8) ∨
           (a = b ∧ s.core.vals[a.toNat]?.getD 0#8 = 0#8)))
        ?_ ?_
      · rintro _ ⟨⟩ m2 ⟨rfl, hor⟩
        have hzb : s.core.vals[b.toNat]?.getD 0#8 = 0#8 := by
          rcases hor with ⟨_, hzb⟩ | ⟨rfl, hza⟩ <;> assumption
        have hent_b : (cnfOfClauses F_cur).EntailsClause (cnfClause [b.toNat]) := by
          rcases hor with ⟨hfa, _⟩ | ⟨rfl, _⟩
          · exact add_bin_entails_unit_of_fals hent_ab
              (add_bin_false_lit_entailed hw hcl0 ha_lt hfa)
          · exact add_bin_entails_unit_self hent_ab
        have hte_mv : s.core.trail_end < c.max_vars :=
          Nat.lt_of_lt_of_le (hw.trail_end_lt_of_unassigned hb_lt hzb) hcv_le
        c0_call hAssignLvl
        refine ⟨c, s, R, rfl, hlen, hm, ?_⟩
        rw [ite_eq_right (by have := hb_lt; simp [hte_mv, hzb]; omega)]
        dsimp only
        rintro flags' unass' phases' m' hf_len hp_len hm'
        c0_hsteps
        exact add_bin_assign_post hlen hw hcl0 hb_lt hzb hent_b hf_len hp_len hm' hQ
      · intro J hJ
        c0_hsteps
        · have hfa : s.core.vals[a.toNat]?.getD 0#8 = 0xFF#8 := by
            rw [List.getElem?_eq_getElem ha_vl, Option.getD_some]
            exact (i8_vals_slt0
              (by rw [List.getElem?_eq_getElem ha_vl, Option.getD_some] at hdom_a
                  exact hdom_a)).mp (by c0_bound)
          have hzb : s.core.vals[b.toNat]?.getD 0#8 = 0#8 := by
            rcases hnot_both_fals with hza | hzb
            · rw [hza] at hfa; cases hfa
            · exact hzb
          exact hJ _ m1 ⟨rfl, .inl ⟨hfa, hzb⟩⟩
        · have hab : a = b := by c0_bound
          have hza : s.core.vals[a.toNat]?.getD 0#8 = 0#8 := by
            rw [List.getElem?_eq_getElem ha_vl, Option.getD_some]
            exact i8_vals_eq0_of_not_pos_neg
              (by rw [List.getElem?_eq_getElem ha_vl, Option.getD_some] at hdom_a
                  exact hdom_a)
              (by c0_bound) (by c0_bound)
          exact hJ _ m1 ⟨rfl, .inr ⟨hab, hza⟩⟩
        · have hfb : s.core.vals[b.toNat]?.getD 0#8 = 0xFF#8 := by
            rw [List.getElem?_eq_getElem hb_vl, Option.getD_some]
            exact (i8_vals_slt0
              (by rw [List.getElem?_eq_getElem hb_vl, Option.getD_some] at hdom_b
                  exact hdom_b)).mp (by c0_bound)
          have hza : s.core.vals[a.toNat]?.getD 0#8 = 0#8 := by
            rw [List.getElem?_eq_getElem ha_vl, Option.getD_some]
            exact i8_vals_eq0_of_not_pos_neg
              (by rw [List.getElem?_eq_getElem ha_vl, Option.getD_some] at hdom_a
                  exact hdom_a)
              (by c0_bound) (by c0_bound)
          have hent_a := add_bin_entails_unit_of_fals (entails_swap2 hent_ab)
            (add_bin_false_lit_entailed hw hcl0 hb_lt hfb)
          have hte_mv : s.core.trail_end < c.max_vars :=
            Nat.lt_of_lt_of_le (hw.trail_end_lt_of_unassigned ha_lt hza) hcv_le
          c0_call hAssignLvl
          refine ⟨c, s, R, rfl, hlen, hm, ?_⟩
          rw [ite_eq_right (by have := ha_lt; simp [hte_mv, hza]; omega)]
          dsimp only
          rintro flags' unass' phases' m' hf_len hp_len hm'
          c0_hsteps
          exact add_bin_assign_post hlen hw hcl0 ha_lt hza hent_a hf_len hp_len hm' hQ
        · c0_call hHasBin
          refine ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hm, ?_⟩
          intro ok _
          c0_hsteps
          · exact hQ 0#64 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 hlen hw (.inl rfl)
              (fun h => by cases h) (fun h => by cases h) hm
          · have hw0a : ((b &&& 0x7FFFFFFF#32) ||| 0x80000000#32) ≠ 0xFFFFFFFF#32 :=
              bv32_tag_bin_ne_sent (lit_lt_0x7FFFFFFF hcv_le hb_lt)
            have hw0b : ((a &&& 0x7FFFFFFF#32) ||| 0x80000000#32) ≠ 0xFFFFFFFF#32 :=
              bv32_tag_bin_ne_sent (lit_lt_0x7FFFFFFF hcv_le ha_lt)
            c0_call hWatchPush
            refine ⟨c, s, R, rfl, hlen, hw.watches.layout, (fun _ => hw0a),
              (fun h => by cases h), hm, ?_⟩
            intro ok1 wvec1 wstk1 wlen1 wu1 wsort1 m1
            dsimp only
            rintro hlen1 hlay1 hoth1 hok1t hok1f hm1
            let s1 : FullState :=
              { s with
                core := { s.core with wvec := wvec1, wstk := wstk1, wlen := wlen1,
                                      wusable := wu1 }
                scratch := { s.scratch with wsort := wsort1 } }
            have hwat1 : ModeWatchesInv F_cur s1.core := by
              refine fullWatchPush_preserves_modeWatchesInv hw.watches hlay1 rfl rfl
                (fun _ h => h) (fun _ => ?_) (fun h => by cases h) hoth1 hok1t
                (fun h hlt => (hok1f h).1 hlt)
              refine ⟨bv32_tag_bin_msb_ne b, hw0a, ?_, ?_⟩
              · change (((b &&& 0x7FFFFFFF#32) ||| 0x80000000#32) &&& 0x7FFFFFFF#32).toNat < _
                rw [bv32_tag_bin_unmask, bv32_and_mask_eq
                  (by have := lit_lt_0x7FFFFFFF hcv_le hb_lt; omega)]
                exact hb_lt
              · change (cnfOfClauses F_cur).EntailsClause
                  (cnfClause [a.toNat, (((b &&& 0x7FFFFFFF#32) ||| 0x80000000#32) &&&
                    0x7FFFFFFF#32).toNat])
                rw [bv32_tag_bin_unmask, bv32_and_mask_eq
                  (by have := lit_lt_0x7FFFFFFF hcv_le hb_lt; omega)]
                exact hent_ab
            have hw1 := fullWitnessInv_with_watches_meta hw hwat1
            c0_hsteps
            · c0_call hWatchPush
              refine ⟨c, s1, R, rfl, hlen1, hlay1, (fun _ => hw0b),
                (fun h => by cases h), hm1, ?_⟩
              intro ok2 wvec2 wstk2 wlen2 wu2 wsort2 m2
              dsimp only
              rintro hlen2 hlay2 hoth2 hok2t hok2f hm2
              let s2 : FullState :=
                { s1 with
                  core := { s1.core with wvec := wvec2, wstk := wstk2,
                                         wlen := wlen2, wusable := wu2 }
                  scratch := { s1.scratch with wsort := wsort2 } }
              have hwat2 : ModeWatchesInv F_cur s2.core := by
                refine fullWatchPush_preserves_modeWatchesInv hwat1 hlay2 rfl rfl
                  (fun _ h => h) (fun _ => ?_) (fun h => by cases h) hoth2 hok2t
                  (fun h hlt => (hok2f h).1 hlt)
                refine ⟨bv32_tag_bin_msb_ne a, hw0b, ?_, ?_⟩
                · change (((a &&& 0x7FFFFFFF#32) ||| 0x80000000#32) &&&
                    0x7FFFFFFF#32).toNat < _
                  rw [bv32_tag_bin_unmask, bv32_and_mask_eq
                    (by have := lit_lt_0x7FFFFFFF hcv_le ha_lt; omega)]
                  exact ha_lt
                · change (cnfOfClauses F_cur).EntailsClause
                    (cnfClause [b.toNat, (((a &&& 0x7FFFFFFF#32) ||| 0x80000000#32) &&&
                      0x7FFFFFFF#32).toNat])
                  rw [bv32_tag_bin_unmask, bv32_and_mask_eq
                    (by have := lit_lt_0x7FFFFFFF hcv_le ha_lt; omega)]
                  exact entails_swap2 hent_ab
              c0_hsteps_nogrp
              · have hfl2_len : s2.core.flags.length = c.max_vars := hlen2.core_ok.flags_len
                have ha_fl1 : (BitVec.setWidth 64 (a >>> OfNat.ofNat 1)).toNat <
                    s2.core.flags.length := by
                  change (BitVec.setWidth 64 (a >>> 1#32)).toNat < s2.core.flags.length
                  rw [hfl2_len, BitVec.toNat_setWidth,
                    Nat.mod_eq_of_lt (Nat.lt_trans (BitVec.isLt _) (by decide))]
                  exact ha_fl
                have hb_fl1 : (BitVec.setWidth 64 (b >>> OfNat.ofNat 1)).toNat <
                    s2.core.flags.length := by
                  change (BitVec.setWidth 64 (b >>> 1#32)).toNat < s2.core.flags.length
                  rw [hfl2_len, BitVec.toNat_setWidth,
                    Nat.mod_eq_of_lt (Nat.lt_trans (BitVec.isLt _) (by decide))]
                  exact hb_fl
                c0_hsteps_nogrp_nobound
                refine LeanQbe.T.wp_join_group (fun (_ : Tup Val [i32]) m' => m' = m2) ?_ ?_
                · rintro J ⟨bit_a, ⟨⟩⟩ m' rfl
                  rw [Blocks.get_here]
                  c0_hsteps_nogrp_nobound
                  obtain ⟨v_b, hv_b⟩ : ∃ v_b : BitVec 32,
                      loadVal m i32
                        (c.pFlags + BitVec.setWidth 64 (b >>> OfNat.ofNat 1) * 4) =
                        some v_b := by
                    refine ⟨_, FullArenaTactics.c0_load_full_flags ?_ hm⟩
                    rw [List.length_set]; exact hb_fl1
                  apply LeanQbe.T.wp_load_of hv_b
                  c0_hsteps_nogrp_nobound
                  refine LeanQbe.T.wp_join_group (fun (_ : Tup Val [i32]) m'' => m'' = m) ?_ ?_
                  · rintro Js ⟨bit_b, ⟨⟩⟩ m'' rfl
                    rw [Blocks.get_here]
                    c0_hsteps_nogrp_nobound
                    apply LeanQbe.T.wp_store_sep
                    · refine FullArenaTactics.c0_store_full_flags _ ?_ hm
                      rw [List.length_set]; exact hb_fl1
                    · intro m_f hm_f
                      clear hv_b hm
                      c0_hsteps_nobound
                      refine hQ 1#64 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?_ ?_
                        (.inr (.inl rfl)) (fun h => by cases h) (fun h => by cases h)
                        (by assumption)
                      · exact ⟨{ hlen2.core_ok with
                            flags_len := by
                              try simp only [List.length_set]
                              exact hlen2.core_ok.flags_len },
                          hlen2.scratch_ok⟩
                      · have hwat2' := modeWatchesInv_of_slice_relocate hwat2
                          (hlay2.with_wstk rfl rfl rfl rfl) rfl rfl
                          (fun _ h => h) (fun _ _ => ⟨rfl, fun _ _ => rfl⟩)
                        exact { hw with
                          arena := ⟨hw.arena.len_ok, hw.arena.refs_wf, hw.arena.shrk_term,
                            hw.arena.lits_lt, hw.arena.entails⟩
                          watches := hwat2'.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }
                  · intro Js hJs
                    c0_hfast_nogrp_nobound
                    all_goals exact hJs _ _ rfl
                · intro J hJ
                  c0_hfast_nogrp_nobound
                  all_goals exact hJ _ _ rfl
              · c0_hsteps
                have hwat2' : ModeWatchesInv F_cur
                    { s.core with wvec := wvec2, wstk := wstk2, wlen := wlen2, wusable := wu2,
                                  oom := 1#64 } :=
                  modeWatchesInv_of_slice_relocate hwat2 (hlay2.with_wstk rfl rfl rfl rfl)
                    rfl rfl (fun _ h => h) (fun _ _ => ⟨rfl, fun _ _ => rfl⟩)
                have hw2' := fullWitnessInv_with_watches_meta hw hwat2'
                have hlen2' : FullState.LengthsOk c
                    { s2 with core := { s2.core with oom := 1#64 } } :=
                  ⟨{ hlen2.core_ok with vals_len := hlen2.core_ok.vals_len }, hlen2.scratch_ok⟩
                exact hQ 2#64 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hlen2' hw2'
                  (.inr (.inr (.inl rfl))) (fun h => by cases h) (fun _ => by decide)
                  (by assumption)
            · have hwat1' : ModeWatchesInv F_cur
                  { s.core with wvec := wvec1, wstk := wstk1, wlen := wlen1, wusable := wu1,
                                oom := 1#64 } :=
                modeWatchesInv_of_slice_relocate hwat1 (hlay1.with_wstk rfl rfl rfl rfl)
                  rfl rfl (fun _ h => h) (fun _ _ => ⟨rfl, fun _ _ => rfl⟩)
              have hw1' := fullWitnessInv_with_watches_meta hw hwat1'
              have hlen1' : FullState.LengthsOk c
                  { s1 with core := { s1.core with oom := 1#64 } } :=
                ⟨{ hlen1.core_ok with vals_len := hlen1.core_ok.vals_len }, hlen1.scratch_ok⟩
              exact hQ 2#64 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hlen1' hw1'
                (.inr (.inr (.inl rfl))) (fun h => by cases h) (fun _ => by decide)
                (by assumption)
    · intro J hJ
      have ha_vl64 : (a.setWidth 64).toNat < s.core.vals.length := by
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans a.isLt (by decide))]
        exact ha_vl
      have hb_vl64 : (b.setWidth 64).toNat < s.core.vals.length := by
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans b.isLt (by decide))]
        exact hb_vl
      c0_hsteps_nobound
      · have hfa : s.core.vals[a.toNat]?.getD 0#8 = 0xFF#8 := by
          rw [List.getElem?_eq_getElem ha_vl, Option.getD_some]
          exact (i8_vals_slt0
            (by rw [List.getElem?_eq_getElem ha_vl, Option.getD_some] at hdom_a
                exact hdom_a)).mp (by c0_bound)
        have hfb : s.core.vals[b.toNat]?.getD 0#8 = 0xFF#8 := by
          rw [List.getElem?_eq_getElem hb_vl, Option.getD_some]
          exact (i8_vals_slt0
            (by rw [List.getElem?_eq_getElem hb_vl, Option.getD_some] at hdom_b
                exact hdom_b)).mp (by c0_bound)
        have hu := add_bin_conflict_unsat hw hcl0 ha_lt hb_lt hfa hfb hent_ab
        have hw' := FullBvaFwdHelpers.fullWitnessInv_set_inconsistent hw hu
        have hlen' : FullState.LengthsOk c
            { s with core := { s.core with inconsistent := 1#64 } } :=
          ⟨{ hcl with vals_len := hcl.vals_len }, hlen.scratch_ok⟩
        exact hQ 20#64 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hlen' hw'
          (.inr (.inr (.inr rfl))) (fun _ => ⟨hw.ext_sound.2 hu, by decide⟩)
          (fun h => by cases h) (by assumption)
      · have hzb : s.core.vals[b.toNat]?.getD 0#8 = 0#8 := by
          rw [List.getElem?_eq_getElem hb_vl, Option.getD_some]
          exact i8_vals_eq0_of_not_pos_neg
            (by rw [List.getElem?_eq_getElem hb_vl, Option.getD_some] at hdom_b
                exact hdom_b)
            (by c0_bound) (by c0_bound)
        exact hJ _ m ⟨rfl, .inr hzb⟩
      · have hza : s.core.vals[a.toNat]?.getD 0#8 = 0#8 := by
          rw [List.getElem?_eq_getElem ha_vl, Option.getD_some]
          exact i8_vals_eq0_of_not_pos_neg
            (by rw [List.getElem?_eq_getElem ha_vl, Option.getD_some] at hdom_a
                exact hdom_a)
            (by c0_bound) (by c0_bound)
        exact hJ _ m ⟨rfl, .inl hza⟩

/-- Canonical `Func.wp` proof for `full_add_bin` against `Proof.Spec.fullAddBinSpec`. -/
theorem full_add_bin_wp (Γ : Env)
    (hAddBinM6 : Γ.Has "full_add_bin_m6" Proof.Spec.fullAddBinSpec) :
    ∀ a m Q X, Proof.Spec.fullAddBinSpec a m Q X → Func.wp Γ full_add_bin_body a m Q X := by
  rintro ⟨h, a, b, ⟨⟩⟩ m Q X hPre
  unfold Func.wp full_add_bin_body
  c0_hsteps
  c0_call hAddBinM6
  exact hPre

/-! ## 3. `full_add_unit_wp` -/

/-- Canonical `Func.wp` proof for `full_add_unit` against `Proof.Spec.fullAddUnitSpec`. -/
theorem full_add_unit_wp (Γ : Env)
    (hBacktrack : Γ.Has "full_backtrack" Proof.Spec.fullBacktrackSpec)
    (hAssignLvl : Γ.Has "full_assign_lvl" Proof.Spec.fullAssignLvlSpec) :
    ∀ a m Q X, Proof.Spec.fullAddUnitSpec a m Q X → Func.wp Γ full_add_unit_body a m Q X := by
  rintro ⟨h, lit, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hent, hm, hQ⟩
  unfold Func.wp full_add_unit_body
  have hcl_64 : s.core.cur_level < 2 ^ 64 := by
    have := hw.cur_level_le; have := hlen.core_ok.trail_end_le
    have := hlen.core_ok.cur_vars_le; have := fullInv_max_vars_lt32 c; omega
  c0_hsteps_nogrp
  refine wp_join_group (ts := [])
    (fun _ m1 => ∃ s1 : FullState,
      s1.LengthsOk c ∧ FullWitnessInv c F0 F_cur s1.core ∧ s1.core.cur_level = 0 ∧
      s1.core = { s.core with
        vals := s1.core.vals, lvl := s1.core.lvl, rsns := s1.core.rsns,
        trl := s1.core.trl, trail_pos := s1.core.trail_pos, trail_end := s1.core.trail_end,
        propagated := s1.core.propagated, cur_level := s1.core.cur_level,
        unassigned := s1.core.unassigned } ∧
      (∃ ta1 ba1 pt1 pb1 hp1 ps1 hl1 qsi1 qss1, s1.scratch = { s.scratch with
        target_assigned := ta1, best_assigned := ba1, phases_target := pt1, phases_best := pb1,
        heap := hp1, pos := ps1, heap_len := hl1, q_search_idx := qsi1, q_search_stamp := qss1 }) ∧
      (FullMem c s1 ⋆ R) m1) ?_ ?_
  · rintro _ ⟨⟩ m1 ⟨s1, hlen1, hw1, hcl1, hs1_core,
      ⟨ta1, ba1, pt1, pb1, hp1, ps1, hl1, qsi1, qss1, hsc1⟩, hm1⟩
    dsimp only [Blocks.get]
    have hcl := hlen1.core_ok
    have hcv1 : s1.core.cur_vars = s.core.cur_vars := by rw [hs1_core]
    have hcv_lt32 : s1.core.cur_vars < 2 ^ 32 :=
      Nat.lt_of_le_of_lt hcl.cur_vars_le (fullInv_max_vars_lt32 c)
    have hcv64_toNat : (BitVec.ofNat 64 s1.core.cur_vars).toNat = s1.core.cur_vars :=
      bv64_ofNat_toNat (Nat.lt_trans hcv_lt32 (by decide))
    have hvals_len : s1.core.vals.length = 2 * c.max_vars := hcl.vals_len
    have hcv_le : s1.core.cur_vars ≤ c.max_vars := hcl.cur_vars_le
    c0_hsteps
    · -- `(lit >> 1) >= cur_vars` -> `return false`
      have hge : 2 * s.core.cur_vars ≤ lit.toNat := by
        have hb : s1.core.cur_vars % 2 ^ 64 ≤ lit.toNat / 2 := by c0_bound
        rw [Nat.mod_eq_of_lt (Nat.lt_trans hcv_lt32 (by decide))] at hb; omega
      have hfin : s1 =
          { s with
            core := { s.core with vals := s1.core.vals, flags := s1.core.flags, lvl := s1.core.lvl,
                                  rsns := s1.core.rsns, trl := s1.core.trl,
                                  trail_pos := s1.core.trail_pos, trail_end := s1.core.trail_end,
                                  propagated := s1.core.propagated, cur_level := s1.core.cur_level,
                                  unassigned := s1.core.unassigned, unflushed := s1.core.unflushed,
                                  inconsistent := s1.core.inconsistent }
            scratch := { s.scratch with phases := s1.scratch.phases, target_assigned := ta1,
                                        best_assigned := ba1, phases_target := pt1,
                                        phases_best := pb1, heap := hp1, pos := ps1,
                                        heap_len := hl1, q_search_idx := qsi1,
                                        q_search_stamp := qss1 } } := by
        rcases s1 with ⟨c1, sc1⟩; dsimp only at hs1_core hsc1; rw [hs1_core, hsc1]
      rw [hfin] at hlen1 hw1 hm1
      exact hQ false _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 hlen1 hw1 hcl1
        (fun hlt => absurd hlt (by omega)) (fun _ => .inl hge) hm1
    · -- `vals[lit] > 0` -> `return true`
      have hfin : s1 =
          { s with
            core := { s.core with
              vals := s1.core.vals, flags := s1.core.flags, lvl := s1.core.lvl,
              rsns := s1.core.rsns, trl := s1.core.trl, trail_pos := s1.core.trail_pos,
              trail_end := s1.core.trail_end, propagated := s1.core.propagated,
              cur_level := s1.core.cur_level, unassigned := s1.core.unassigned,
              unflushed := s1.core.unflushed, inconsistent := s1.core.inconsistent }
            scratch := { s.scratch with
              phases := s1.scratch.phases, target_assigned := ta1, best_assigned := ba1,
              phases_target := pt1, phases_best := pb1, heap := hp1, pos := ps1,
              heap_len := hl1, q_search_idx := qsi1, q_search_stamp := qss1 } } := by
        rcases s1 with ⟨c1, sc1⟩; dsimp only at hs1_core hsc1; rw [hs1_core, hsc1]
      rw [hfin] at hlen1 hw1 hm1
      exact hQ true _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 hlen1 hw1 hcl1
        (fun _ h => by cases h) (fun h => by cases h) hm1
    · -- `vals[lit] < 0` -> `inconsistent = 1; return false`
      have hlt1 : lit.toNat < 2 * s1.core.cur_vars := by
        have hb : lit.toNat / 2 < s1.core.cur_vars % 2 ^ 64 := by c0_bound
        rw [Nat.mod_eq_of_lt (Nat.lt_trans hcv_lt32 (by decide))] at hb; omega
      have hlt : lit.toNat < 2 * s.core.cur_vars := Nat.lt_of_lt_of_eq hlt1 (congrArg (2 * ·) hcv1)
      have hvl : lit.toNat < s1.core.vals.length := by omega
      have hdom := hw1.vals_domain lit.toNat hlt1
      have hfl : s1.core.vals[lit.toNat]?.getD 0#8 = 0xFF#8 := by
        rw [List.getElem?_eq_getElem hvl, Option.getD_some]
        exact (i8_vals_slt0
          (by rw [List.getElem?_eq_getElem hvl, Option.getD_some] at hdom
              exact hdom)).mp (by c0_bound)
      have hneg_ent := add_bin_false_lit_entailed hw1 hcl1 hlt1 hfl
      have hu : (cnfOfClauses F_cur).Unsat :=
        unsat_of_entails_nil (entails_of_mem_or_false (hent hlt) fun l hl => by
          simp only [List.mem_singleton] at hl; subst hl; exact .inr hneg_ent)
      have hw2 := FullBvaFwdHelpers.fullWitnessInv_set_inconsistent hw1 hu
      have hlen2 : FullState.LengthsOk c
          { s1 with core := { s1.core with inconsistent := 1#64 } } :=
        ⟨{ hcl with vals_len := hcl.vals_len }, hlen1.scratch_ok⟩
      have hfin_core : ({ s1.core with inconsistent := 1#64 } : FullCoreState) =
          { s.core with
            vals := s1.core.vals, flags := s1.core.flags, lvl := s1.core.lvl,
            rsns := s1.core.rsns, trl := s1.core.trl, trail_pos := s1.core.trail_pos,
            trail_end := s1.core.trail_end, propagated := s1.core.propagated,
            cur_level := s1.core.cur_level, unassigned := s1.core.unassigned,
            unflushed := s1.core.unflushed, inconsistent := 1#64 } := by
        rw [hs1_core]
      have hfin : ({ s1 with core := { s1.core with inconsistent := 1#64 } } : FullState) =
          { s with
            core := { s.core with
              vals := s1.core.vals, flags := s1.core.flags, lvl := s1.core.lvl,
              rsns := s1.core.rsns, trl := s1.core.trl, trail_pos := s1.core.trail_pos,
              trail_end := s1.core.trail_end, propagated := s1.core.propagated,
              cur_level := s1.core.cur_level, unassigned := s1.core.unassigned,
              unflushed := s1.core.unflushed, inconsistent := 1#64 }
            scratch := { s.scratch with
              phases := s1.scratch.phases, target_assigned := ta1, best_assigned := ba1,
              phases_target := pt1, phases_best := pb1, heap := hp1, pos := ps1,
              heap_len := hl1, q_search_idx := qsi1, q_search_stamp := qss1 } } := by
        rcases s1 with ⟨c1, sc1⟩; dsimp only at hs1_core hsc1; rw [hs1_core, hsc1]
      change (FullMem c { s1 with core := { s1.core with inconsistent := 1#64 } } ⋆ R) m at hm
      rw [hfin] at hlen2 hm
      rw [hfin_core] at hw2
      exact hQ false _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m hlen2 hw2 hcl1
        (fun _ _ => ⟨hw1.ext_sound.2 hu, by decide⟩)
        (fun _ => .inr ⟨hw1.ext_sound.2 hu, by decide⟩) hm
    · -- `vals[lit] == 0` -> `full_assign_lvl(h, lit, 0xFFFFFFFFu, 0u); return true`
      have hlt1 : lit.toNat < 2 * s1.core.cur_vars := by
        have hb : lit.toNat / 2 < s1.core.cur_vars % 2 ^ 64 := by c0_bound
        rw [Nat.mod_eq_of_lt (Nat.lt_trans hcv_lt32 (by decide))] at hb; omega
      have hlt : lit.toNat < 2 * s.core.cur_vars :=
        Nat.lt_of_lt_of_eq hlt1 (congrArg (2 * ·) hcv1)
      have hvl : lit.toNat < s1.core.vals.length := by omega
      have hdom := hw1.vals_domain lit.toNat hlt1
      have hz : s1.core.vals[lit.toNat]?.getD 0#8 = 0#8 := by
        rw [List.getElem?_eq_getElem hvl, Option.getD_some]
        exact i8_vals_eq0_of_not_pos_neg
          (by rw [List.getElem?_eq_getElem hvl, Option.getD_some] at hdom
              exact hdom)
          (by c0_bound) (by c0_bound)
      have hte_cv : s1.core.trail_end < s1.core.cur_vars :=
        hw1.trail_end_lt_of_unassigned hlt1 hz
      have hte_mv : s1.core.trail_end < c.max_vars := Nat.lt_of_lt_of_le hte_cv hcv_le
      c0_call hAssignLvl
      refine ⟨c, s1, R, rfl, hlen1, hm1, ?_⟩
      rw [ite_eq_right (by have := hlt1; simp [hte_mv, hz]; omega)]
      dsimp only
      rintro flags2 unass2 phases2 m2 hf_len hp_len hm2
      c0_hsteps
      let s2 : FullState :=
        { s1 with
          core := { s1.core with
            vals := (s1.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
            flags := flags2
            lvl := s1.core.lvl.set (lit.toNat / 2) 0#32
            rsns := s1.core.rsns.set (lit.toNat / 2) 0xFFFFFFFF#32
            trl := s1.core.trl.set s1.core.trail_end lit
            trail_pos := s1.core.trail_pos.set (lit.toNat / 2)
              (BitVec.ofNat 32 s1.core.trail_end)
            trail_end := s1.core.trail_end + 1
            unassigned := unass2
            unflushed := s1.core.unflushed + 1#64 }
          scratch := { s1.scratch with phases := phases2 } }
      have hlen2 : s2.LengthsOk c :=
        ⟨{ hcl with
           vals_len := by simp [s2, hcl.vals_len]
           flags_len := hf_len
           lvl_len := by simp [s2, hcl.lvl_len]
           rsns_len := by simp [s2, hcl.rsns_len]
           trl_len := by simp [s2, hcl.trl_len]
           trail_pos_len := by simp [s2, hcl.trail_pos_len]
           trail_end_le := by dsimp [s2]; omega
           propagated_le := by dsimp [s2]; exact Nat.le_trans hcl.propagated_le (Nat.le_succ _) },
         { hlen1.scratch_ok with phases_len := hp_len }⟩
      have hw2 := assignLevel0_preserves_fullWitness hlen1 hw1 hcl1 hlt1 hz (hent hlt)
        flags2 unass2 (s1.core.unflushed + 1#64)
      have hfin_core : s2.core =
          { s.core with
            vals := s2.core.vals, flags := flags2, lvl := s2.core.lvl, rsns := s2.core.rsns,
            trl := s2.core.trl, trail_pos := s2.core.trail_pos, trail_end := s2.core.trail_end,
            propagated := s1.core.propagated, cur_level := s1.core.cur_level,
            unassigned := unass2, unflushed := s1.core.unflushed + 1#64,
            inconsistent := s1.core.inconsistent } := by
        dsimp only [s2]; rw [hs1_core]
      have hfin : s2 =
          { s with
            core := { s.core with
              vals := s2.core.vals, flags := flags2, lvl := s2.core.lvl, rsns := s2.core.rsns,
              trl := s2.core.trl, trail_pos := s2.core.trail_pos, trail_end := s2.core.trail_end,
              propagated := s1.core.propagated, cur_level := s1.core.cur_level,
              unassigned := unass2, unflushed := s1.core.unflushed + 1#64,
              inconsistent := s1.core.inconsistent }
            scratch := { s.scratch with phases := phases2, target_assigned := ta1,
                                        best_assigned := ba1, phases_target := pt1,
                                        phases_best := pb1, heap := hp1, pos := ps1,
                                        heap_len := hl1, q_search_idx := qsi1,
                                        q_search_stamp := qss1 } } := by
        dsimp only [s2] at *; rcases s1 with ⟨c1, sc1⟩; dsimp only at hs1_core hsc1
        rw [hs1_core, hsc1]
      change FullWitnessInv c F0 F_cur s2.core at hw2
      change (FullMem c s2 ⋆ R) m2 at hm2
      rw [hfin] at hlen2 hm2
      rw [hfin_core] at hw2
      exact hQ true _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 hlen2 hw2 hcl1
        (fun _ h => by cases h) (fun h => by cases h) hm2
  · intro J hJ
    c0_hsteps
    · have hcl := hlen.core_ok
      have hmv_pos : 0 < s.core.cur_level → 0 < c.max_vars := by
        have := hw.cur_level_le; have := hcl.trail_end_le; have := hcl.cur_vars_le; omega
      c0_call hBacktrack
      refine ⟨c, s, R, rfl, hlen, hcl_64, hmv_pos, hw.trail_lits_lt, hm, ?_⟩
      intro vals1 lvl1 rsns1 trl1 tp1 te1 prop1 cl1 unass1 sc1 m1
      dsimp only
      rintro hlen1 hte1 hprop1 hcl1 hpres1 hsc1 htrl1 _ hinvW1 _ hm1
      c0_hsteps
      let s1 : FullState :=
        { s with
          core := { s.core with vals := vals1, lvl := lvl1, rsns := rsns1, trl := trl1,
                                trail_pos := tp1, trail_end := te1, propagated := prop1,
                                cur_level := cl1, unassigned := unass1 }
          scratch := sc1 }
      exact hJ _ m1 ⟨s1, hlen1, hinvW1 F0 F_cur hw (Nat.zero_le _), by simp only [s1, hcl1]; simp,
        rfl, hsc1, hm1⟩
    · have hc0 : ¬ 0 < s.core.cur_level % 2 ^ 64 := by c0_bound
      have hcl0 : s.core.cur_level = 0 := by rw [Nat.mod_eq_of_lt hcl_64] at hc0; omega
      exact hJ _ m ⟨s, hlen, hw, hcl0, rfl,
        ⟨s.scratch.target_assigned, s.scratch.best_assigned, s.scratch.phases_target,
         s.scratch.phases_best, s.scratch.heap, s.scratch.pos, s.scratch.heap_len,
         s.scratch.q_search_idx, s.scratch.q_search_stamp, rfl⟩, hm⟩

end LeanQbe.T.Examples.Kissat.Proof.Clause
