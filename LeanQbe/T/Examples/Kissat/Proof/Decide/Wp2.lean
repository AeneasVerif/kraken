/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Decide.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Tiers.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
public import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv1
public import LeanQbe.T.Examples.Kissat.Src.Decide
public import LeanQbe.T.Logic.C0Step
public import LeanQbe.T.Logic.C0HeadStep
public import LeanQbe.T.Logic.ControlComb

/-!
# Soundness Proofs for `Kissat.Src.Decide` — Part 2 (`Proof.Decide.Wp2`)

Proves `full_decide_m7_wp` (`fullDecideSpec`) and `m6_hdr_decide_fid_wp` (`m6HdrDecideSpec`)
(`0` legacy imports, `0` `@[expose]` on theorems/lemmas/sections).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Decide

open Std.Sat
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Decide.Spec
open LeanQbe.T.Examples.Kissat.Src.Decide
open Kraken.Bedrock2.Test

open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.M6HdrTactics

private theorem bv32_ofNat_lt32 {n : Nat} (hn : n < 2 ^ 32) :
    (BitVec.ofNat 32 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

private theorem bv64_ofNat_lt64 {n : Nat} (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

private theorem decide_preserves_fullCore {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hinv : FullCoreInv c F0 s) {v : Nat} {lit : BitVec 32}
    {flags' : List (BitVec 32)} {unas' unfl' : BitVec 64} {scratch' : FullScratch}
    (hsok' : scratch'.LengthsOk c) (hfll : flags'.length = c.max_vars)
    (hv_lt : v < s.core.cur_vars) (hval0 : s.core.vals[2 * v]?.getD 0#8 = 0#8)
    (hlit_eq : lit.toNat = 2 * v ∨ lit.toNat = 2 * v + 1) :
    let nlvl := s.core.cur_level + 1
    let ftrl' := s.core.frame_trail.set nlvl (BitVec.ofNat 32 s.core.trail_end)
    let fdec' := s.core.frame_dec.set nlvl lit
    let s' : FullState :=
      { core :=
          { s.core with
            vals := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
            flags := flags', lvl := s.core.lvl.set (lit.toNat / 2) (BitVec.ofNat 32 nlvl)
            rsns := s.core.rsns.set (lit.toNat / 2) 0xFFFFFFFF#32
            trl := s.core.trl.set s.core.trail_end lit
            trail_pos := s.core.trail_pos.set (lit.toNat / 2) (BitVec.ofNat 32 s.core.trail_end)
            frame_trail := ftrl', frame_dec := fdec', trail_end := s.core.trail_end + 1
            cur_level := nlvl, unassigned := unas', unflushed := unfl' }
        scratch := scratch' }
    FullCoreInv c F0 s' ∧ s.core.vals[lit.toNat]?.getD 0#8 = 0#8 ∧
    s.core.trail_end < s.core.cur_vars ∧ nlvl ≤ c.max_vars := by
  intro nlvl ftrl' fdec' s'
  obtain ⟨F_cur, hw⟩ := hinv.witness; have hcl := hinv.lengths.core_ok
  have hcv := hcl.cur_vars_le; have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hlit_lt : lit.toNat < 2 * s.core.cur_vars := by omega
  have hlit_v : lit.toNat / 2 = v := by omega
  have hun : s.core.vals[lit.toNat]?.getD 0#8 = 0#8 := by
    rcases hlit_eq with he | ho
    · rw [he]; exact hval0
    · have hnot0 := (hw.vals_zero_iff (by omega : 2 * v < 2 * s.core.cur_vars)).mp hval0
      rw [ho]
      exact (hw.vals_zero_iff (by omega : 2 * v + 1 < 2 * s.core.cur_vars)).mpr fun i hi => by
        have := hnot0 i hi; omega
  have hte_lt : s.core.trail_end < s.core.cur_vars := hw.trail_end_lt_of_unassigned hlit_lt hun
  have hcl_le : s.core.cur_level ≤ s.core.trail_end := hw.cur_level_le
  have hnlvl_le : nlvl ≤ c.max_vars := by dsimp [nlvl]; omega
  have hte_lt32 : s.core.trail_end < 2 ^ 32 := by omega
  have hnot_var : ∀ i < s.core.trail_end, (s.core.trl[i]?.getD 0#32).toNat / 2 ≠ lit.toNat / 2 :=
    (hw.vals_zero_iff hlit_lt).mp hun
  have hft_get : ∀ L ≤ nlvl, (ftrl'[L]?.getD 0#32).toNat =
      if L = nlvl then s.core.trail_end
      else (s.core.frame_trail[L]?.getD 0#32).toNat := fun L _ => by
    by_cases hL : L = nlvl
    · subst hL; dsimp only [ftrl']
      rw [List.getElem?_set_self (by rw [hcl.frame_trail_len]; omega), Option.getD_some,
        bv32_ofNat_lt32 hte_lt32]; simp
    · dsimp only [ftrl']; rw [List.getElem?_set_ne (Ne.symm hL)]; simp [hL]
  have hfd_get : ∀ L ≤ nlvl, (fdec'[L]?.getD 0#32).toNat =
      if L = nlvl then lit.toNat else (s.core.frame_dec[L]?.getD 0#32).toNat := fun L _ => by
    by_cases hL : L = nlvl
    · subst hL; dsimp only [fdec']
      rw [List.getElem?_set_self (by rw [hcl.frame_dec_len]; omega), Option.getD_some]; simp
    · dsimp only [fdec']; rw [List.getElem?_set_ne (Ne.symm hL)]; simp [hL]
  have hcore' := chronoAssign_preserves_fullCore hinv (lit := lit) (rsn := 0xFFFFFFFF#32)
    (alvl := nlvl) (cur_level' := nlvl) (propagated' := s.core.propagated)
    (flags' := flags') (frame_trail' := ftrl') (frame_dec' := fdec')
    (unassigned' := unas') (unflushed' := unfl') (scratch' := scratch')
    hsok' hfll (by simp [ftrl', hcl.frame_trail_len]) (by simp [fdec', hcl.frame_dec_len])
    hlit_lt hun (Nat.le_refl _) (by have := hcl.propagated_le; omega) (by dsimp [nlvl]; omega)
    (fun L hL => by
      rw [hft_get L hL]; split
      · omega
      · have := hw.frame_trail_lt L (by dsimp [nlvl] at *; omega); omega)
    (fun L1 L2 h12 h2 => by
      rw [hft_get L1 (by omega), hft_get L2 h2]
      by_cases h2e : L2 = nlvl
      · by_cases h1e : L1 = nlvl
        · simp [h1e, h2e]
        · simp only [h1e, h2e, ↓reduceIte]; exact hw.frame_trail_lt L1 (by dsimp [nlvl] at *; omega)
      · have h1n : L1 ≠ nlvl := by omega
        simp only [h1n, h2e, ↓reduceIte]
        exact hw.frame_trail_mono L1 L2 h12 (by dsimp [nlvl] at *; omega))
    (fun L hL1 hLle i hi => by
      rw [hft_get L hLle] at hi
      by_cases hLe : L = nlvl
      · subst hLe; simp only [↓reduceIte] at hi
        have hne_i : i ≠ s.core.trail_end := by omega
        have hnv : (s.core.trl[i]?.getD 0#32).toNat / 2 ≠ lit.toNat / 2 := hnot_var i hi
        simp only [hne_i, hnv, ↓reduceIte]
        have := hw.lvl_le i hi; dsimp [nlvl]; omega
      · simp only [hLe, ↓reduceIte] at hi
        have hLle' : L ≤ s.core.cur_level := by dsimp [nlvl] at *; omega
        have hi_lt : i < s.core.trail_end := Nat.lt_of_lt_of_le hi (hw.frame_trail_lt L hLle')
        have hne_i : i ≠ s.core.trail_end := by omega
        have hnv : (s.core.trl[i]?.getD 0#32).toNat / 2 ≠ lit.toNat / 2 := hnot_var i hi_lt
        simp only [hne_i, hnv, ↓reduceIte]
        exact hw.frame_trail_before_lt L hL1 hLle' i hi)
    (fun L hL1 hLle => by
      rw [hfd_get L hLle]; split
      · exact hlit_lt
      · exact hw.frame_dec_lt L hL1 (by dsimp [nlvl] at *; omega))
    (fun i hi => by have := hw.lvl_le i hi; dsimp [nlvl]; omega)
    (fun L hL1 hLle => by
      by_cases hLe : L = nlvl
      · exact Or.inl hLe
      · exact Or.inr (hw.levels_inhabited L hL1 (by dsimp [nlvl] at *; omega)))
    (fun _ _ i hi => by have := hw.lvl_le i hi; dsimp [nlvl]; omega)
    (fun hz => by dsimp [nlvl] at hz; omega)
    (fun _ hne => absurd rfl hne)
    (fun _ hne _ => absurd rfl hne)
  have hnlvl_ne0 : nlvl ≠ 0 := by dsimp [nlvl]; omega
  simpa only [s', hnlvl_ne0, ↓reduceIte] using ⟨hcore', hun, hte_lt, hnlvl_le⟩

/-- Soundness proof for `full_decide_m7` against canonical `Proof.Spec.fullDecideSpec`. -/
theorem full_decide_m7_wp (Γ : Env)
    (hRandec : ∀ a m Q X, fullRandecVarSpec a m Q X →
      Γ "full_randec_var_m7" [i64] [i64] a m Q X)
    (hNextDec : ∀ a m Q X, fullNextDecVarSpec a m Q X →
      Γ "full_next_dec_var" [i64] [i64] a m Q X)
    (hAssign : ∀ a m Q X, fullAssignSpec a m Q X →
      Γ "full_assign" [i64, i32, i32] [] a m Q X) :
    ∀ a m Q X, fullDecideSpec a m Q X → Func.wp Γ full_decide_m7_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hm, hQ⟩
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  unfold Func.wp full_decide_m7_body
  c0_hsteps_nogrp
  c0_call hRandec
  refine ⟨c, s, R, rfl, hinv.lengths, hm, fun ⟨chosen, ⟨⟩⟩ s1 m1 hc1 hlen1 ⟨hp1, _, hch1⟩ hm1 => ?_⟩
  dsimp only [fullSafetySlice] at hc1 hlen1 hm1
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64])
    (fun (ch, ()) m2 => ∃ s2 : FullState,
      s2.core = s.core ∧ s2.LengthsOk c ∧ FullExtScratchPres s s2 ∧
      (ch = 0xFFFFFFFFFFFFFFFF#64 ∨
        ch.toNat < s.core.cur_vars ∧ s.core.vals[2 * ch.toNat]?.getD 0#8 = 0#8) ∧
      (FullMem c s2 ⋆ R) m2) ?_ ?_
  · rintro Jc ⟨ch, ⟨⟩⟩ m2 ⟨s2, hc2, hlen2, hext2, hch2, hm2⟩
    rw [Blocks.get_here]
    have hinv2 : FullCoreInv c F0 s2 := hinv.with_fuel_scratch_spec hlen2 (by rw [hc2])
    have hcl2 := hinv2.lengths.core_ok
    have hsok2 := hinv2.lengths.scratch_ok
    c0_hsteps_nogrp
    · cases s2; dsimp only at hc2; subst hc2
      exact hQ 0#64 s.core.vals s.core.flags s.core.lvl s.core.rsns s.core.trl s.core.trail_pos
        s.core.frame_trail s.core.frame_dec s.core.trail_end s.core.cur_level s.core.unassigned
        s.core.unflushed _ m2 hinv2 hext2 (Or.inl rfl) (fun _ => ⟨rfl, rfl⟩)
        (fun h01 => by cases h01) hm2
    · obtain ⟨hv_lt, hval0⟩ := hch2.resolve_left (by assumption)
      have hcv2 : s.core.cur_vars ≤ c.max_vars := hc2 ▸ hcl2.cur_vars_le
      have hch_lt_max : ch.toNat < c.max_vars := by omega
      have hch_lt30 : ch.toNat < 2 ^ 30 := by omega
      have hv_tgt : ch.toNat < s2.scratch.phases_target.length := by
        rw [hsok2.phases_target_len]; omega
      have hv_ph : ch.toNat < s2.scratch.phases.length := by
        rw [hsok2.phases_len]; omega
      c0_hsteps_nogrp
      refine wp_join_group (fun _ md1 => m2 = md1) ?_ ?_
      · rintro Jd1 ⟨dph1, ⟨⟩⟩ _ rfl
        rw [Blocks.get_here]; c0_hsteps_nogrp
        refine wp_join_group (fun _ md2 => m2 = md2) ?_ ?_
        · rintro Jd2 ⟨dph2, ⟨⟩⟩ _ rfl
          rw [Blocks.get_here]; c0_hsteps_nogrp
          refine wp_join_group (fun _ md3 => m2 = md3) ?_ ?_
          · rintro Jd3 ⟨dph3, ⟨⟩⟩ _ rfl
            rw [Blocks.get_here]; c0_hsteps_nogrp
            refine wp_join_group (ts := [i32])
              (fun (lit, ()) ml => m2 = ml ∧
                (lit.toNat = 2 * ch.toNat ∨ lit.toNat = 2 * ch.toNat + 1)) ?_ ?_
            · rintro Jl ⟨lit, ⟨⟩⟩ _ ⟨rfl, hlit_eq⟩
              rw [Blocks.get_here]
              cases s2 with | mk sc_c sc_sc =>
              dsimp only at hc2; subst hc2
              have hinv2' : FullCoreInv c F0 { core := s.core, scratch := sc_sc } := hinv2
              have hcl2' := hinv2'.lengths.core_ok
              have hsok2' := hinv2'.lengths.scratch_ok
              have hte2 : s.core.trail_end ≤ s.core.cur_vars := hcl2'.trail_end_le
              have hcv2' : s.core.cur_vars ≤ c.max_vars := hcl2'.cur_vars_le
              obtain ⟨_, hw2⟩ := hinv2'.witness
              have hcl2_le : s.core.cur_level ≤ s.core.trail_end := hw2.cur_level_le
              have hnlvl_bv : (BitVec.ofNat 64 s.core.cur_level + 1#64).toNat =
                  s.core.cur_level + 1 := by
                have := bv64_ofNat_lt64 (n := s.core.cur_level) (by omega)
                bv_omega
              have hftrl1 : s.core.frame_trail.length = c.max_vars + 1 := hcl2'.frame_trail_len
              have hfdec1 : s.core.frame_dec.length = c.max_vars + 1 := hcl2'.frame_dec_len
              c0_hsteps_nogrp
              · exact hQ 0#64 s.core.vals s.core.flags s.core.lvl s.core.rsns s.core.trl
                  s.core.trail_pos s.core.frame_trail s.core.frame_dec s.core.trail_end
                  s.core.cur_level s.core.unassigned s.core.unflushed _ m2 hinv2' hext2
                  (Or.inl rfl) (fun _ => ⟨rfl, rfl⟩) (fun h01 => by cases h01) hm2
              · have hnlvl_le : s.core.cur_level + 1 ≤ c.max_vars := by
                  have h1 := hc
                  rw [show (1 : BitVec 64).toNat = 1 from rfl,
                    Nat.mod_eq_of_lt (by omega : c.max_vars < 2 ^ 64),
                    Nat.mod_eq_of_lt (by omega : s.core.cur_level + 1 < 2 ^ 64)] at h1
                  omega
                have hft_lt : (BitVec.ofNat 64 s.core.cur_level + 1#64).toNat <
                    s.core.frame_trail.length := by
                  rw [hnlvl_bv, hftrl1]; omega
                have hfd_lt : (BitVec.ofNat 64 s.core.cur_level + 1#64).toNat <
                    s.core.frame_dec.length := by
                  rw [hnlvl_bv, hfdec1]; omega
                have ⟨_, hun, hte_lt, _⟩ := decide_preserves_fullCore hinv2' hsok2'
                  hcl2'.flags_len hv_lt hval0 hlit_eq (flags' := s.core.flags)
                  (unas' := s.core.unassigned) (unfl' := s.core.unflushed)
                let nlvl := s.core.cur_level + 1
                let ftrl' := s.core.frame_trail.set nlvl (BitVec.ofNat 32 s.core.trail_end)
                let fdec' := s.core.frame_dec.set nlvl lit
                let s_pre : FullState :=
                  { core := { s.core with frame_trail := ftrl', frame_dec := fdec',
                                          cur_level := nlvl }
                    scratch := sc_sc }
                have hlen_pre : s_pre.LengthsOk c :=
                  ⟨{ hcl2' with
                      frame_trail_len := by
                        dsimp only [s_pre, ftrl']; rw [List.length_set]; exact hftrl1
                      frame_dec_len := by
                        dsimp only [s_pre, fdec']; rw [List.length_set]; exact hfdec1 },
                    hsok2'⟩
                have hte_bv : (BitVec.ofNat 64 s.core.trail_end).setWidth 32 =
                    BitVec.ofNat 32 s.core.trail_end := by
                  apply BitVec.eq_of_toNat_eq
                  rw [BitVec.toNat_setWidth, bv64_ofNat_lt64 (by omega),
                    bv32_ofNat_lt32 (by omega), Nat.mod_eq_of_lt (by omega)]
                c0_hsteps_nogrp
                have hte_max : s.core.trail_end < c.max_vars := Nat.lt_of_lt_of_le hte_lt hcv2'
                have hlit_v : lit.toNat / 2 = ch.toNat := by omega
                have hng : ¬ (s_pre.core.cur_vars ≤ lit.toNat / 2 ∨
                    c.max_vars ≤ s_pre.core.trail_end ∨
                    s_pre.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8) := by
                  change ¬ (s.core.cur_vars ≤ lit.toNat / 2 ∨
                    c.max_vars ≤ s.core.trail_end ∨
                    s.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8)
                  simp only [hun, ne_eq, not_true_eq_false, or_false]; rw [hlit_v]; omega
                c0_call hAssign
                refine ⟨c, s_pre, R, rfl, hlen_pre, by dsimp [s_pre, nlvl]; omega, ?_, ?_⟩
                · dsimp only [s_pre, ftrl', fdec', nlvl]
                  rw [← hnlvl_bv, ← hte_bv]
                  assumption
                · simp only [hng, ↓reduceIte]
                  intro flags' unas' phases' m3 hfl_l hph_l hm3
                  have hsok3 : ({ sc_sc with phases := phases' } : FullScratch).LengthsOk c :=
                    { hsok2' with phases_len := hph_l }
                  have ⟨hinv3, _, _, _⟩ := decide_preserves_fullCore hinv2' hsok3 hfl_l
                    hv_lt hval0 hlit_eq (flags' := flags')
                    (unas' := unas') (unfl' := s.core.unflushed)
                  have hnl_ne0 : nlvl ≠ 0 := by dsimp [nlvl]; omega
                  have hff : (4294967295 : BitVec 32) = 0xFFFFFFFF#32 := rfl
                  have hm3' : (FullMem c
                      { core := { s.core with
                          vals := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
                          flags := flags'
                          lvl := s.core.lvl.set (lit.toNat / 2) (BitVec.ofNat 32 nlvl)
                          rsns := s.core.rsns.set (lit.toNat / 2) 0xFFFFFFFF#32
                          trl := s.core.trl.set s.core.trail_end lit
                          trail_pos := s.core.trail_pos.set (lit.toNat / 2)
                            (BitVec.ofNat 32 s.core.trail_end)
                          frame_trail := ftrl', frame_dec := fdec'
                          trail_end := s.core.trail_end + 1, cur_level := nlvl
                          unassigned := unas', unflushed := s.core.unflushed }
                        scratch := { sc_sc with phases := phases' } } ⋆ R) m3 := by
                    simpa only [s_pre, hnl_ne0, ↓reduceIte, hff] using hm3
                  c0_hsteps
                  exact hQ 1#64 _ flags' _ _ _ _ ftrl' fdec' (s.core.trail_end + 1) nlvl unas'
                    s.core.unflushed { sc_sc with phases := phases' } m3 hinv3 hext2 (Or.inr rfl)
                    (fun h10 => by cases h10) (fun _ => ⟨rfl, rfl⟩) hm3'
            · intro Jl hJl; c0_hsteps
              · exact hJl _ m2 ⟨rfl, Or.inr (FullKissatMath.bv32_lit_odd hch_lt30)⟩
              · exact hJl _ m2 ⟨rfl, Or.inl (FullKissatMath.bv32_lit_even hch_lt30)⟩
          · intro Jd3 hJd3; c0_hsteps <;> exact hJd3 _ m2 rfl
        · intro Jd2 hJd2; c0_hsteps <;> exact hJd2 _ m2 rfl
      · intro Jd1 hJd1; c0_hsteps <;> exact hJd1 _ m2 rfl
  · intro Jc hJc
    c0_hsteps_nogrp
    · c0_call hNextDec
      refine ⟨c, s1, R, rfl, hlen1, hm1, fun ⟨chosen', ⟨⟩⟩ s2 m2 hc2 hlen2 ⟨hext2, hch2⟩ hm2 => ?_⟩
      dsimp only [fullSafetySlice] at hc2 hlen2 hm2
      have hc2' : s2.core = s.core := Eq.trans hc2 hc1
      have hext2' : FullExtScratchPres s s2 := fullExtScratchPres_trans hp1 hext2
      have hch2' : chosen' = 0xFFFFFFFFFFFFFFFF#64 ∨
          chosen'.toNat < s.core.cur_vars ∧ s.core.vals[2 * chosen'.toNat]?.getD 0#8 = 0#8 := by
        have hc1' : s1.core = s.core := hc1
        simpa [hc1'] using hch2
      c0_hsteps; exact hJc (chosen', ()) m2 ⟨s2, hc2', hlen2, hext2', hch2', hm2⟩
    · obtain ⟨hv_lt, _, hv0⟩ := hch1.resolve_left (by assumption)
      exact hJc (chosen, ()) m1 ⟨s1, hc1, hlen1, hp1, Or.inr ⟨hv_lt, hv0⟩, hm1⟩

/-- Soundness proof for `m6_hdr_decide_fid` against canonical `Proof.Spec.m6HdrDecideSpec`. -/
theorem m6_hdr_decide_fid_wp (Γ : Env)
    (hDecide : ∀ a m Q X, fullDecideSpec a m Q X →
      Γ "full_decide_m7" [i64] [i64] a m Q X)
    (hDrInit : ∀ a m Q X, m6HdrDrMutSpec a m Q X →
      Γ "m6_hdr_dr_init" [i64] [] a m Q X) :
    ∀ a m Q X, m6HdrDecideSpec a m Q X → Func.wp Γ m6_hdr_decide_fid_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  obtain ⟨c, F0, ext, s, R, rfl, hinv, hm, hQ⟩ := m6HdrDecideSpec_elim hs
  have hcfg := hinv.cfgOk
  have hext := hinv.extOk
  have hcore0 := hinv.coreInv
  unfold Func.wp m6_hdr_decide_fid_body
  c0_hsteps_nogrp
  c0_call hDecide
  refine ⟨c, F0, s, (array64 (c.hdr - 2304) ext ⋆ R), rfl, hcore0, (fullM6HdrMem_iff ..).mp hm,
    fun r vals' flags' lvl' rsns' trl' tp' ftrl' fdec' te' cl' unass' unfl' sc' m1
      hinv1 hpres1 hdom h0 h1 hm1 => ?_⟩
  let s1 : FullState :=
    { core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                            trl := trl', trail_pos := tp', frame_trail := ftrl',
                            frame_dec := fdec', trail_end := te', cur_level := cl',
                            unassigned := unass', unflushed := unfl' }
      scratch := sc' }
  c0_hsteps_nogrp
  · exact hQ 0#64 vals' flags' lvl' rsns' trl' tp' ftrl' fdec' te' cl' unass' unfl' sc' ext m1
      (FullM6HdrCoreInv.mk_inv hcfg hext hinv1) hpres1 (Or.inl rfl)
      (fun _ => h0 hc) (fun h => by cases h) ((fullM6HdrMem_iff ..).mpr hm1)
  · have hr1 : r = 1#64 := hdom.resolve_left hc
    have hl1 : ext.length = 288 := hext.len
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64])
      (fun (st4, ()) m4 => ∃ ext4 : List (BitVec 64),
        M6HdrExtInitOk ext4 ∧ (M6HdrExtInitOk ext → M6ExtW2aPres ext ext4) ∧
        ext4[1]? = some st4 ∧ (FullMem c s1 ⋆ (array64 (c.hdr - 2304) ext4 ⋆ R)) m4)
      (fun _ ⟨st4, ⟨⟩⟩ m4 ⟨ext4, hinit4, hw4, hst4_eq, hm4⟩ => by
        have hl4 : ext4.length = 288 := hinit4.toOk.len
        let mask56 : BitVec 64 := (1#64 <<< 56) - 1#64
        let hi4 := st4 &&& ~~~mask56
        let decs4 := st4 &&& mask56
        let ext4' := ext4.set 1 (hi4 ||| (decs4 + 1#64))
        c0_hsteps
        · refine hQ 1#64 vals' flags' lvl' rsns' trl' tp' ftrl' fdec' te' cl' unass' unfl' sc'
            ext4' _ (FullM6HdrCoreInv.mk_inv hcfg (hinit4.set_pos _ (by decide)).toOk hinv1)
            hpres1 (Or.inr rfl) (fun h => by cases h)
            (fun _ => ⟨(h1 hr1).1, (h1 hr1).2, hinit4.set_pos _ (by decide),
              fun hi => (hw4 hi).trans (M6ExtW2aPres.set_w2b _ (by decide) (by decide))⟩)
            ((fullM6HdrMem_iff ..).mpr ?_)
          simpa [ext4', hi4, decs4, mask56] using (by assumption : _)
        · exact hQ 1#64 vals' flags' lvl' rsns' trl' tp' ftrl' fdec' te' cl' unass' unfl' sc'
            ext4 m4 (FullM6HdrCoreInv.mk_inv hcfg hinit4.toOk hinv1) hpres1 (Or.inr rfl)
            (fun h => by cases h) (fun _ => ⟨(h1 hr1).1, (h1 hr1).2, hinit4, hw4⟩)
            ((fullM6HdrMem_iff ..).mpr hm4)) ?_
    intro Jst hJst
    refine wp_join_group (ts := [])
      (fun _ m_in => (FullMem c s1 ⋆ (array64 (c.hdr - 2304) ext ⋆ R)) m_in)
      (fun _ ⟨⟩ m_in hm_in => by
        c0_hsteps_nogrp
        c0_call hDrInit
        refine m6HdrDrMutSpec_of hcfg hext hinv1.lengths ((fullM6HdrMem_iff ..).mpr hm_in)
          fun ext4 m4 hinit4 hw4 hm4 => ?_
        have hl4 : ext4.length = 288 := hinit4.toOk.len
        rw [fullM6HdrMem_iff] at hm4
        c0_hsteps
        exact hJst (ext4[1]'(by omega), ()) m4
          ⟨ext4, hinit4, hw4, List.getElem?_eq_getElem (by omega), hm4⟩) ?_
    intro Jinit hJinit
    c0_hsteps_nogrp
    · exact hJinit () m1 hm1
    · exact hJinit () m1 hm1
    · have hmag_eq : ext[0]'(by omega) = Src.fullM6HdrMagic := by
        simpa [Src.fullM6HdrMagic] using
          (by assumption : ext[(0 : BitVec 64).toNat]'(by simp; omega) = 0x4D36484452455831#64)
      have hinit1 : M6HdrExtInitOk ext :=
        ⟨hext, by rw [List.getElem?_eq_getElem (by omega), hmag_eq]⟩
      exact hJst (ext[1]'(by omega), ()) m1
        ⟨ext, hinit1, fun _ => M6ExtW2aPres.refl ext, List.getElem?_eq_getElem (by omega), hm1⟩

end LeanQbe.T.Examples.Kissat.Proof.Decide
