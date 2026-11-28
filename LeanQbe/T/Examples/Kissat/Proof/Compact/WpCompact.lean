/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Compact.Spec
public import LeanQbe.T.Examples.Kissat.Src.Compact
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Compact.Inv
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Canonical WP Proof for Top-Level `full_compact` (`Proof.Compact.WpCompact`)

Proves `full_compact_wp` against the `FullM6HdrMem`-threaded `fullCompactSpec` (Step-13 Option-A),
focusing `FullM6HdrMem` onto `FullMem` across all `10` internal compaction helpers plus
`full_wstack_defrag` and `full_rewatch_arena`, then unfocusing back onto `FullM6HdrMem`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Compact

open Std Std.Sat
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

public section

/-- Canonical WP proof for `full_compact` against `fullCompactSpec` (`FullM6HdrMem`-threaded). -/
theorem full_compact_wp (Γ : Env)
    (hfl : Γ.Has "full_compact_flush" fullCompactFlushSpec)
    (hmk : Γ.Has "full_compact_mark_live" fullCompactMarkLiveSpec)
    (hmp : Γ.Has "full_compact_assign_map" fullCompactAssignMapSpec)
    (hre : Γ.Has "full_compact_record_ext" fullCompactRecordExtSpec)
    (hbn : Γ.Has "full_compact_bins" fullCompactBinsSpec)
    (hdf : Γ.Has "full_wstack_defrag" fullWstackDefragSpec)
    (har : Γ.Has "full_compact_arena" fullCompactArenaSpec)
    (hvr : Γ.Has "full_compact_vars" fullCompactVarsSpec)
    (hvm : Γ.Has "full_compact_vmtf" fullCompactVmtfSpec)
    (hhp : Γ.Has "full_compact_heap" fullCompactHeapSpec)
    (hrw : Γ.Has "full_rewatch_arena" fullRewatchArenaSpec) :
    ∀ a m Q X, fullCompactSpec a m Q X → Func.wp Γ full_compact_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, ext, s, R, rfl, hinv, hm, hQ⟩
  have hdm0 : s.core.dense_mode = 0#64 := hinv.sparse.2.2.2.2
  unfold Func.wp full_compact_body
  refine wp_m6Hdr_focus_frame hm fun hmf => ?_
  c0_hsteps_nogrp; cmp_call hfl
  refine ⟨c, F0, ext, s, R, rfl, hinv, fullM6HdrMem_unfocus_full hmf, ?_⟩
  intro fst ext1 s1 m1 hext1 _ hinv1 _ _ _ _ _ hfst hcv1 _ hfuel1 _ h20 h1 _ hm1
  c0_hsplit
  · have hfst_ne1 : fst ≠ 1#64 := by c0_bound
    c0_hsteps
    rcases hfst with rfl | rfl | rfl
    · exact hQ 0#64 c ext1 s1 m1 (FullCfgCompat.refl c) hinv1 (Or.inl rfl) (by omega) hfuel1
        (fun h => by cases h) (fun h => by cases h) hm1
    · exact absurd rfl hfst_ne1
    · exact hQ 20#64 c ext1 s1 m1 (FullCfgCompat.refl c) hinv1 (Or.inr (Or.inr rfl)) (by omega)
        hfuel1 h20 (fun h => by cases h) hm1
  · have hfst1 : fst = 1#64 := by c0_bound
    obtain ⟨hcl1, _, _, _, hinc1, _⟩ := h1 hfst1
    have hsp1 := hinv1.sparse
    obtain ⟨F_cur, hspW1⟩ := hsp1.exists_witness
    have hcv1_le := hspW1.1.core_ok.cur_vars_le
    have hmax_lt := c.hmaxv
    have hcv1_lt64 : s1.core.cur_vars < 2 ^ 64 := by unfold dimacsBound at hmax_lt; omega
    refine wp_m6Hdr_focus_frame hm1 fun hm1f => ?_
    c0_hsplit
    · c0_hsteps
      exact hQ 1#64 c ext1 s1 m1 (FullCfgCompat.refl c) hinv1 (Or.inr (Or.inl rfl)) (by omega)
        hfuel1 (fun h => by cases h) (fun _ => hcl1) hm1
    · c0_hsteps_nogrp; cmp_call hmk
      refine ⟨c, F0, F_cur, s1, m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R, rfl, hspW1, hm1f,
        fun ws1_mk m2 hspW2 hm2 => ?_⟩
      let s2 : FullState := { s1 with scratch := { s1.scratch with work_stk1 := ws1_mk } }
      c0_hsteps_nogrp; cmp_call hmp
      refine ⟨c, s2, m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R, rfl, hspW2.1, hm2,
        fun ncv ws1_3 ws2_3 m3 hlen3 hbij3 hm3 => ?_⟩
      let s3 : FullState :=
        { s2 with scratch := { s2.scratch with work_stk1 := ws1_3, work_stk2 := ws2_3 } }
      have hspW3 : FullSparseInvW c F0 F_cur s3 :=
        ⟨hlen3, hspW2.2.1, hspW2.2.2.1, hspW2.2.2.2.1, hspW2.2.2.2.2.1, hspW2.2.2.2.2.2⟩
      c0_hsplit
      · c0_hsteps
        exact hQ 1#64 c ext1 s3 _ (FullCfgCompat.refl c)
          ⟨hinv1.cfgOk, hext1, hspW3.toSparse⟩ (Or.inr (Or.inl rfl))
          (by change s1.core.cur_vars ≤ _; omega) hfuel1 (fun h => by cases h) (fun _ => hcl1)
          (fullM6HdrMem_unfocus_full hm3)
      · have hold_cv : (BitVec.ofNat 64 s1.core.cur_vars).toNat = s3.core.cur_vars :=
          bv64_ofNat_toNat hcv1_lt64
        have hncv_le : ncv.toNat ≤ (BitVec.ofNat 64 s1.core.cur_vars).toNat := by
          rw [hold_cv]; exact hbij3.ncv_le
        have hncv_le_s : ncv.toNat ≤ s.core.cur_vars := by
          rw [hold_cv, show s3.core.cur_vars = s1.core.cur_vars from rfl, hcv1] at hncv_le
          exact hncv_le
        c0_hsteps_nogrp; cmp_call hre
        refine ⟨c, s3, m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R, rfl, hlen3, hold_cv.symm, hncv_le,
          hspW3.2.2.2.2.1.2, hm3, fun ok ext4 elen4 m4 hlen4 helen4 _ hm4 => ?_⟩
        let s4 : FullState :=
          { s3 with scratch := { s3.scratch with extend_stk := ext4, extend_len := elen4 } }
        have hspW4 : FullSparseInvW c F0 F_cur s4 :=
          ⟨hlen4, hspW3.2.1, hspW3.2.2.1, hspW3.2.2.2.1,
           ⟨hspW3.2.2.2.2.1.1, helen4⟩, hspW3.2.2.2.2.2⟩
        c0_hsplit
        rotate_left
        · c0_hsteps
          exact hQ 1#64 c ext1 s4 _ (FullCfgCompat.refl c)
            ⟨hinv1.cfgOk, hext1, hspW4.toSparse⟩ (Or.inr (Or.inl rfl))
            (by change s1.core.cur_vars ≤ _; omega) hfuel1 (fun h => by cases h) (fun _ => hcl1)
            (fullM6HdrMem_unfocus_full hm4)
        c0_hsteps_nogrp; cmp_call hbn
        refine ⟨c, F0, F_cur, s4, m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R, rfl, hspW4, hold_cv.symm,
          hncv_le, (by
            change CompactBijOk (BitVec.ofNat 64 s1.core.cur_vars).toNat _ _ _ _
            rw [hold_cv]; exact hbij3),
          hm4, fun wvec5 wstk5 wu5 nb5 m5 hlen5 hbin5 hm5 => ?_⟩
        let s5 : FullState :=
          { s4 with core := { s4.core with wvec := wvec5, wstk := wstk5, wusable := wu5,
                                           num_binary := nb5 } }
        c0_hsteps_nogrp; cmp_call hdf
        refine ⟨c, s5, m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R, rfl, hlen5, hbin5.layout, hm5,
          fun wvec6 wstk6 wlen6 wsort6 m6 hlen6 hlay6 _ hpres6 hm6 => ?_⟩
        let s6 : FullState :=
          { s5 with
            core := { s5.core with wvec := wvec6, wstk := wstk6, wlen := wlen6, wusable := 0#64 }
            scratch := { s5.scratch with wsort := wsort6 } }
        have hbin6 : CompactUnmapBinsOk ncv.toNat s6.scratch.work_stk2 F_cur s6.core := by
          refine ⟨hlay6, fun l hl1 hl2 => ?_, fun l hl => ?_⟩
          · exact (hpres6 l hl2).1.trans (hbin5.empty_hi l hl1 hl2)
          · have hncv_s5 : ncv.toNat ≤ s5.core.cur_vars := by
              change ncv.toNat ≤ s3.core.cur_vars; exact hbij3.ncv_le
            obtain ⟨hsz, hsl⟩ := hpres6 l (by omega)
            have hsz' : fullWatchSizeCore s6.core l = fullWatchSizeCore s5.core l := hsz
            rw [hsz']
            exact (hbin5.slices l hl).relocate hsl
        have hw3 := hspW3.2.1
        c0_hsteps_nogrp; cmp_call har
        refine ⟨c, F0, F_cur, ncv.toNat, s6, m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R, rfl, hlen6,
          (by change ExtUnsatSound F0 (BitVec.ofNat 64 s1.core.cur_vars).toNat F_cur
              rw [hold_cv]; exact hw3.ext_sound),
          ⟨hw3.arena.len_ok, hw3.arena.refs_wf, hw3.arena.shrk_term, hw3.arena.lits_lt,
           hw3.arena.entails⟩,
          hspW3.2.2.2.1, hspW3.2.2.2.2.2, hcl1, hold_cv.symm, hncv_le,
          (by change CompactBijOk (BitVec.ofNat 64 s1.core.cur_vars).toNat _ _ _ _
              rw [hold_cv]; exact hbij3),
          (by change ∀ l < 2 * (BitVec.ofNat 64 s1.core.cur_vars).toNat, _
              rw [hold_cv]; exact hw3.vals_domain),
          fun l hl hf => level0_vals_false_entails hw3 hcl1
            (by change l < 2 * s3.core.cur_vars; rw [← hold_cv]; exact hl) hf,
          hbin6, hm6,
          fun ast ar7 al7 fred7 ni7 nr7 wvec7 wstk7 wlen7 wu7 nb7 oom7 ll7 ws7 m7
            hlen7 hast hast2 hast3 hbin7 har7 hll7 hm7 => ?_⟩
        let s7 : FullState :=
          { core := { s6.core with arena := ar7, arena_len := al7, arena_garbage := 0#64,
                                   first_reducible := fred7, num_irred := ni7,
                                   num_redundant := nr7, wvec := wvec7, wstk := wstk7,
                                   wlen := wlen7, wusable := wu7, num_binary := nb7, oom := oom7 }
            scratch := { s6.scratch with last_learned := ll7, wsort := ws7 } }
        c0_hsteps_nogrp; cmp_call hvr
        refine ⟨c, s7, m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R, rfl, hlen7, hold_cv.symm, hncv_le,
          fun nv hnv => ?_, hm7,
          fun c' vals8 fl8 lvl8 rsns8 ft0 fd0 sc8 m8 hcompat8 hlen8 hft0 hvals8 hpres8
            hws1_8 hws2_8 hm8 => ?_⟩
        · obtain ⟨ov, hov, _, _, hinv_ov, _⟩ := hbij3.inv_ok nv hnv
          rw [hinv_ov, Option.getD_some, bv32_ofNat_toNat (by have := hbij3.old_cv_lt; omega)]
          dsimp [Arg.val]; rw [hold_cv]; exact hov
        · let s8 : FullState :=
            { core := { s7.core with vals := vals8, flags := fl8, lvl := lvl8, rsns := rsns8,
                                     frame_trail := s7.core.frame_trail.set 0 ft0,
                                     frame_dec := s7.core.frame_dec.set 0 fd0,
                                     trail_end := 0, propagated := 0, cur_level := 0,
                                     unflushed := 0#64, confl_ref := 0xFFFFFFFF#64,
                                     confl_type := 0#64, cur_vars := ncv.toNat,
                                     unassigned := ncv }
              scratch := sc8 }
          c0_hsteps_nogrp; cmp_call hvm
          refine ⟨c', s8, m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R, hcompat8.hdr.symm, hlen8,
            Nat.le_refl _, hm8,
            fun sc9 m9 hlen9 hpres9 hws1_9 hws2_9 hm9 => ?_⟩
          let s9 : FullState := { s8 with scratch := sc9 }
          c0_hsteps_nogrp; cmp_call hhp
          refine ⟨c', s9, m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R, hcompat8.hdr.symm, hlen9,
            Nat.le_refl _, hm9,
            fun sc10 m10 hlen10 hpres10 hws1_10 hws2_10 hm10 => ?_⟩
          let s10 : FullState := { s9 with scratch := sc10 }
          have har10 : CompactArenaOk c' ncv.toNat ws2_3 F_cur s10.core :=
            har7.with_core (c' := c') rfl rfl
          have hbin10 : CompactUnmapBinsOk ncv.toNat ws2_3 F_cur s10.core :=
            hbin7.with_vars (Nat.le_refl _) (by change ncv.toNat ≤ s1.core.cur_vars; omega)
              rfl rfl rfl
          have hnd10 : FullArenaVarsNodup s10 := fun r hr _ => har10.nodup r hr
          have hmarks10 : FullLitMarksClear c' s10 :=
            FullLitMarksClear.of_compat hcompat8 hspW3.2.2.1
          have hext10 : FullExtScratchOk c' s10 :=
            FullExtScratchOk.of_compat hcompat8 ⟨hll7, helen4⟩
              ⟨hpres10.1.trans (hpres9.1.trans hpres8.1),
               hpres10.2.trans (hpres9.2.trans hpres8.2)⟩
              fun _ h => h
          have hvals10 : ∀ l < 2 * s10.core.cur_vars, s10.core.vals[l]?.getD 0#8 = 0#8 := by
            intro l hl
            have hl1 : l < 2 * c'.max_vars := by
              have := hlen10.core_ok.cur_vars_le
              change l < 2 * s10.core.cur_vars at hl
              change s10.core.cur_vars ≤ c'.max_vars at this; omega
            have hl2 : l < 2 * (BitVec.ofNat 64 s1.core.cur_vars).toNat := by
              rw [hold_cv]; have := hbij3.ncv_le
              change l < 2 * ncv.toNat at hl
              change ncv.toNat ≤ s3.core.cur_vars at this; omega
            rw [hvals8 l hl1 hl2]
          have hft10 : (s10.core.frame_trail[0]?.getD 0#32).toNat = 0 := by
            have hft_len : 0 < s7.core.frame_trail.length := by
              have := hlen7.core_ok.frame_trail_len
              dsimp only [s7] at this ⊢; omega
            change ((s7.core.frame_trail.set 0 ft0)[0]?.getD 0#32).toNat = 0
            rw [List.getElem?_set_self hft_len, Option.getD_some, hft0]
          have hcfg' : FullM6HdrCfgOk c' := FullM6HdrCfgOk_of_compat hcompat8 hinv1.cfgOk
          have hext_m6 : m6ExtAddr c.hdr = m6ExtAddr c'.hdr := by rw [hcompat8.hdr]
          c0_hsplit
          · have hast_2 : ast = 2#64 := by c0_bound
            rw [← hcompat8.hdr]; c0_hsteps
            let s11 : FullState := { s10 with core := { s10.core with inconsistent := 1#64 } }
            have har11 : CompactArenaOk c' ncv.toNat ws2_3 F_cur s11.core :=
              har10.with_core rfl rfl
            have hbin11 : CompactUnmapBinsOk ncv.toNat ws2_3 F_cur s11.core :=
              hbin10.with_vars (Nat.le_refl _) (Nat.le_refl _) rfl rfl rfl
            have hw11 := fullWitnessInv_compact_unsat (hast2 hast_2) hbin11 har11 rfl
              hspW3.2.2.2.2.2 rfl rfl hft10 hvals10
            have hsp11 : FullSparseInv c' F0 s11 :=
              ⟨⟨{ hlen10 with core_ok := { hlen10.core_ok with
                  vals_len := hlen10.core_ok.vals_len } },
                [[]], hw11⟩, hmarks10, hnd10, hext10, hspW3.2.2.2.2.2⟩
            exact hQ 20#64 c' ext1 s11 _ hcompat8 ⟨hcfg', hext1, hsp11⟩
              (Or.inr (Or.inr rfl)) hncv_le_s hfuel1 (fun _ => hast2 hast_2) (fun h => by cases h)
              (fullM6HdrMem_unfocus_full (by rw [← hext_m6]; assumption))
          · c0_hsplit
            · rw [← hcompat8.hdr]; c0_hsteps
              let s11 : FullState := { s10 with core := { s10.core with oom := 1#64 } }
              have har11 : CompactArenaOk c' ncv.toNat ws2_3 F_cur s11.core :=
                har10.with_core rfl rfl
              have hbin11 : CompactUnmapBinsOk ncv.toNat ws2_3 F_cur s11.core :=
                hbin10.with_vars (Nat.le_refl _) (Nat.le_refl _) rfl rfl rfl
              have hw11 := fullWitnessInv_compact_build hw3.ext_sound
                hbin11 har11 rfl hinc1 hspW3.2.2.2.2.2 rfl rfl hft10 hvals10
              have hsp11 : FullSparseInv c' F0 s11 :=
                ⟨⟨{ hlen10 with core_ok := { hlen10.core_ok with
                    vals_len := hlen10.core_ok.vals_len } },
                  stateClausesCore s11.core, hw11⟩, hmarks10, hnd10, hext10, hspW3.2.2.2.2.2⟩
              exact hQ 0#64 c' ext1 s11 _ hcompat8 ⟨hcfg', hext1, hsp11⟩ (Or.inl rfl)
                hncv_le_s hfuel1 (fun h => by cases h) (fun h => by cases h)
                (fullM6HdrMem_unfocus_full (by rw [← hext_m6]; assumption))
            · have hw10 := fullWitnessInv_compact_build hw3.ext_sound
                hbin10 har10 rfl hinc1 hspW3.2.2.2.2.2 rfl rfl hft10 hvals10
              have hal10_lt : s10.core.arena_len < 2 ^ 64 := by
                have hle : s10.core.arena_len ≤ c'.arena_cap := hlen10.core_ok.arena_len_le
                have := c'.harena; unfold dimacsBound at *; omega
              rw [← hcompat8.hdr]; c0_hsteps_nogrp; cmp_call hrw
              refine ⟨c', F0, stateClausesCore s10.core, s10, m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R,
                rfl, hlen10, hw10, hspW3.2.2.2.2.2, bv64_ofNat_toNat hal10_lt, ?_, hm10,
                fun ok arena11 wvec11 wstk11 wlen11 wu11 oom11 ws11 m11
                  hlen11 hw11 hnd11 href11 _ _ hm11 => ?_⟩
              · intro r hr
                refine ⟨?_, har10.no_shrk r hr⟩
                have := har10.no_garb r hr
                unfold fullArenaClauseGarb fullArenaClauseGarbCore; simp [this]
              · let s11 : FullState :=
                  { s10 with
                    core := { s10.core with arena := arena11, wvec := wvec11, wstk := wstk11,
                                            wlen := wlen11, wusable := wu11, oom := oom11 }
                    scratch := { s10.scratch with wsort := ws11 } }
                have hext11 : FullExtScratchOk c' s11 :=
                  FullExtScratchOk.of_pres hext10 ⟨rfl, rfl⟩ fun r hr => by
                    change r ∈ fullArenaClauseRefs s11
                    rw [href11]; exact hr
                have hsp11 : FullSparseInv c' F0 s11 :=
                  ⟨⟨hlen11, stateClausesCore s10.core, hw11⟩, hmarks10, hnd11 hnd10, hext11,
                   hspW3.2.2.2.2.2⟩
                c0_hsplit
                · c0_hsteps
                  exact hQ 1#64 c' ext1 s11 _ hcompat8 ⟨hcfg', hext1, hsp11⟩
                    (Or.inr (Or.inl rfl)) hncv_le_s hfuel1 (fun h => by cases h) (fun _ => rfl)
                    (fullM6HdrMem_unfocus_full (hext_m6 ▸ hm11))
                · c0_hsteps
                  let s12 : FullState := { s11 with core := { s11.core with oom := 1#64 } }
                  have hw12 : FullWitnessInv c' F0 (stateClausesCore s10.core) s12.core :=
                    { hw11 with
                      arena := { hw11.arena with len_ok := hw11.arena.len_ok }
                      watches := hw11.watches.with_wstk rfl rfl rfl rfl rfl fun _ h => h }
                  have hlen12 : s12.LengthsOk c' :=
                    { hlen11 with core_ok := { hlen11.core_ok with
                        vals_len := hlen11.core_ok.vals_len } }
                  have hext12 : FullExtScratchOk c' s12 :=
                    FullExtScratchOk.of_pres hext11 ⟨rfl, rfl⟩ fun _ h => h
                  have hsp12 : FullSparseInv c' F0 s12 :=
                    ⟨⟨hlen12, stateClausesCore s10.core, hw12⟩, hmarks10, hnd11 hnd10,
                     hext12, hspW3.2.2.2.2.2⟩
                  exact hQ 0#64 c' ext1 s12 _ hcompat8 ⟨hcfg', hext1, hsp12⟩ (Or.inl rfl)
                    hncv_le_s hfuel1 (fun h => by cases h) (fun h => by cases h)
                    (fullM6HdrMem_unfocus_full (by rw [← hext_m6]; assumption))

end

end LeanQbe.T.Examples.Kissat.Proof.Compact
