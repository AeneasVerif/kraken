/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Compact.Spec
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.Spec
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
# Canonical WP Proofs for `Kissat.Src.Compact` — Part 0

Proves `Func.wp` against `Proof.Compact.Spec` for:
1. `full_compact_needed` (`fullCompactNeededSpec`)
2. `full_compact_flush` (`fullCompactFlushSpec`)
3. `full_compact_mark_live` (`fullCompactMarkLiveSpec`)
4. `full_compact_assign_map` (`fullCompactAssignMapSpec`)
5. `full_compact_record_ext` (`fullCompactRecordExtSpec`)
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Compact

open Std Std.Sat
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Compact
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.PropSearch.Spec
open LeanQbe.T.Examples.Kissat.Proof.Compact.Spec
open Kraken.Bedrock2.Test
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics

local macro "cmp_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

private theorem bv64_shl1_toNat {v : BitVec 64} (h : 2 * v.toNat < 2 ^ 64) :
    (v <<< (1 : Nat)).toNat = 2 * v.toNat := by
  bv_omega

private theorem bv64_shl1_add1_toNat {v : BitVec 64} (h : 2 * v.toNat + 1 < 2 ^ 64) :
    ((v <<< (1 : Nat)) + 1#64).toNat = 2 * v.toNat + 1 := by
  bv_omega

private theorem bv64_shr1_toNat (v : BitVec 64) :
    (v >>> (1 : Nat)).toNat = v.toNat / 2 := by
  bv_omega

private theorem bv32_shr1_nat_toNat (v : BitVec 32) :
    (v >>> (1 : Nat)).toNat = v.toNat / 2 := by
  bv_omega

private theorem bv32_shr1_zext_lt {lit : BitVec 32} {n m : Nat}
    (hl : lit.toNat < 2 * n) (hnm : n ≤ m) :
    ((lit >>> (1 : BitVec 32)).setWidth 64).toNat < m := by
  rw [zext_toNat _ (by decide), show (1 : BitVec 32) = 1#32 from rfl, bv32_shr1_toNat]
  omega

public section

/-! ## 1. `full_compact_needed` & `full_compact_flush` -/

/-- Canonical WP proof for `full_compact_needed` (`10%` dead-variable compaction trigger). -/
theorem full_compact_needed_wp (Γ : Env) :
    ∀ a m Q X, compactNeededSpec a m Q X →
      Func.wp Γ full_compact_needed_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  obtain ⟨c, s, ⟨⟩, R, rfl, hlen, hcl_lt, hm, hQ⟩ := FullContract.elim hs
  have hcv := hlen.core_ok.cur_vars_le
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  unfold Func.wp full_compact_needed_body
  c0_hsteps <;>
    first
    | exact hQ (false, ()) s m hlen ⟨rfl, fun hf => Bool.noConfusion hf⟩ hm
    | (refine hQ (_, ()) s m hlen ⟨rfl, fun hres => ?_⟩ hm
       have hcl0 : s.core.cur_level = 0 := by c0_bound
       have hdm0 : s.core.dense_mode = 0#64 := by c0_bound
       have hcv_pos : 0 < s.core.cur_vars := by c0_bound
       have hun_lt : s.core.unassigned.toNat < s.core.cur_vars := by c0_bound
       have h10 : s.core.cur_vars < 10 * (s.core.cur_vars - s.core.unassigned.toNat) := by
         have hsub : (BitVec.ofNat 64 s.core.cur_vars - s.core.unassigned).toNat =
             s.core.cur_vars - s.core.unassigned.toNat := by bv_omega
         have hmul : ((BitVec.ofNat 64 s.core.cur_vars - s.core.unassigned) * 10#64).toNat =
             (s.core.cur_vars - s.core.unassigned.toNat) * 10 := by
           rw [BitVec.toNat_mul, hsub, show (10#64 : BitVec 64).toNat = 10 from rfl,
             Nat.mod_eq_of_lt (by omega)]
         have hgt : BitVec.ult (BitVec.ofNat 64 s.core.cur_vars)
             ((BitVec.ofNat 64 s.core.cur_vars - s.core.unassigned) * 10#64) = true := hres
         rw [BitVec.ult_iff_toNat_lt, hmul, BitVec.toNat_ofNat,
           Nat.mod_eq_of_lt (by omega)] at hgt
         omega
       exact ⟨hcl0, hdm0, hcv_pos, hun_lt, h10⟩)

/-- Canonical WP proof for `full_compact_flush` (`full_flush_trail` delegate). -/
theorem full_compact_flush_wp (Γ : Env)
    (hFlush : Γ.Has "full_flush_trail" PropSearch.Spec.flushTrailM6Spec) :
    ∀ a m Q X, compactFlushSpec a m Q X →
      Func.wp Γ full_compact_flush_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  obtain ⟨c, ext, s, F0, R, rfl, _, _, _, hinv, hm, hQ⟩ := M6HdrContract.elim hs
  unfold Func.wp full_compact_flush_body
  c0_hsteps; cmp_call hFlush
  refine ⟨c, F0, ext, s, R, rfl, hinv, hm,
    fun r ext' s' m' hext' hrel' hinv' _ _ _ _ _ hr hcv' _ hfu' _ h20 h1 _ hm' => ?_⟩
  exact hQ (r, ()) ext' s' m' hext' hrel' hinv'.sparse.lengths
    ⟨hinv', hr, hcv', hfu', h20, fun eq1 =>
      let ⟨hcl, _, _, _, hinc, _⟩ := h1 eq1; ⟨hcl, hinc⟩⟩ hm'

/-! ## 2. `full_compact_mark_live` -/

private theorem fullSparseInvW_with_ws1 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} {ws1' : List (BitVec 32)}
    (hsp : FullSparseInvW c F0 F_cur s) (hws1 : ws1'.length = 2 * c.max_vars) :
    FullSparseInvW c F0 F_cur { s with scratch := { s.scratch with work_stk1 := ws1' } } :=
  ⟨⟨hsp.1.core_ok, { hsp.1.scratch_ok with work_stk1_len := hws1 }⟩,
   hsp.2.1, hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩

/-- Canonical WP proof for `full_compact_mark_live`. -/
theorem full_compact_mark_live_wp (Γ : Env)
    (hnext : Γ.Has "full_arena_next" fullArenaNextSpec) :
    ∀ a m Q X, compactMarkLiveSpec a m Q X →
      Func.wp Γ full_compact_mark_live_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  obtain ⟨c, s, ⟨F0, F_cur⟩, R, rfl, _, hsp, hm, hQ⟩ := FullContract.elim hs
  have hlen := hsp.1
  have hw := hsp.2.1
  have hdm := hsp.2.2.2.2.2
  have hwat : WatchesInv F_cur s.core := by
    have hm' := hw.watches; unfold ModeWatchesInv at hm'; rwa [ite_eq_left hdm] at hm'
  have hcv_le := hlen.core_ok.cur_vars_le; have hal_le := hlen.core_ok.arena_len_le
  have har_len := hlen.core_ok.arena_len_arr; have hv_len := hlen.core_ok.vals_len
  have hfl_len := hlen.core_ok.flags_len; have hwv_len := hlen.core_ok.wvec_len
  have hws_len := hlen.core_ok.wstk_len_arr; have hws1_len := hlen.scratch_ok.work_stk1_len
  have hmx := c.hmaxv; have hac := c.harena; have hwc := c.hwcap; unfold dimacsBound at hmx hac hwc
  unfold Func.wp full_compact_mark_live_body
  c0_hsteps_nogrp
  refine wp_loop_inv
    (fun (v, ()) m1 =>
      v.toNat ≤ s.core.cur_vars ∧
      ∃ ws1 : List (BitVec 32), ws1.length = 2 * c.max_vars ∧
        (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1 } } ⋆ R) m1)
    (fun (v, ()) _ => s.core.cur_vars - v.toNat)
    (fun J1 hLoop1 => ?_) ?_
  · c0_hsteps; exact hLoop1 (0#64, ()) m ⟨Nat.zero_le _, s.scratch.work_stk1, hws1_len, hm⟩
  · rintro J1 ⟨v, ⟨⟩⟩ m1 ⟨hv_le, ws1, hlen1, hm1⟩ hLoop1
    c0_hsplit
    · have hv_lt : v.toNat < s.core.cur_vars := by c0_bound
      have hv1_eq : (v + 1#64).toNat = v.toNat + 1 := cmp_bv64_add1 (by omega)
      have h2v_eq : (v <<< (1 : Nat)).toNat = 2 * v.toNat := bv64_shl1_toNat (by omega)
      c0_hsteps
      · refine hLoop1 (v + 1#64, ()) _ (by dsimp only; rw [hv1_eq]; omega)
          ⟨by rw [hv1_eq]; omega, ws1.set v.toNat 1#32, by simp [hlen1], by assumption⟩
      · refine hLoop1 (v + 1#64, ()) _ (by dsimp only; rw [hv1_eq]; omega)
          ⟨by rw [hv1_eq]; omega, ws1.set v.toNat 0#32, by simp [hlen1], by assumption⟩
      · refine hLoop1 (v + 1#64, ()) _ (by dsimp only; rw [hv1_eq]; omega)
          ⟨by rw [hv1_eq]; omega, ws1.set v.toNat 0#32, by simp [hlen1], by assumption⟩
    · clear hLoop1 J1 hc hv_le v hm hs m
      c0_hsteps_nogrp
      refine wp_loop_inv
        (fun (l, ()) m2 =>
          l.toNat ≤ 2 * s.core.cur_vars ∧
          ∃ ws2 : List (BitVec 32), ws2.length = 2 * c.max_vars ∧
            (FullMem c { s with scratch := { s.scratch with work_stk1 := ws2 } } ⋆ R) m2)
        (fun (l, ()) _ => 2 * s.core.cur_vars - l.toNat)
        (fun J2 hLoop2 => ?_) ?_
      · c0_hsteps; exact hLoop2 (0#64, ()) m1 ⟨Nat.zero_le _, ws1, hlen1, hm1⟩
      · rintro J2 ⟨l, ⟨⟩⟩ m2 ⟨hl_le, ws2, hlen2, hm2⟩ hLoop2
        c0_hsplit
        · have hl_lt : l.toNat < 2 * s.core.cur_vars := by c0_bound
          have hl1_eq : (l + 1#64).toNat = l.toNat + 1 := cmp_bv64_add1 (by omega)
          have h2l_eq : (l <<< (1 : Nat)).toNat = 2 * l.toNat := bv64_shl1_toNat (by omega)
          have h2l1_eq : ((l <<< (1 : Nat)) + 1#64).toNat = 2 * l.toNat + 1 :=
            bv64_shl1_add1_toNat (by omega)
          have h2l_lt : 2 * l.toNat < s.core.wvec.length := by omega
          have h2l1_lt : 2 * l.toNat + 1 < s.core.wvec.length := by omega
          let off0 := fullWatchOffCore s.core l.toNat
          let sz0 := fullWatchSizeCore s.core l.toNat
          have hoff_eq : (s.core.wvec[2 * l.toNat]'h2l_lt).toNat = off0 := by
            unfold off0 fullWatchOffCore
            rw [List.getElem?_eq_getElem h2l_lt, Option.getD_some]
          have hsz_eq : (s.core.wvec[2 * l.toNat + 1]'h2l1_lt).toNat = sz0 := by
            unfold sz0 fullWatchSizeCore
            rw [List.getElem?_eq_getElem h2l1_lt, Option.getD_some]
          have hbd_l : off0 + sz0 ≤ s.core.wlen := hwat.layout.bounds l.toNat hl_lt
          have hslice0 : WatchSliceOk F_cur s.core l.toNat off0 sz0 := hwat.slices l.toNat hl_lt
          let end0 := off0 + sz0
          have hwl_le := hlen.core_ok.wlen_le
          have h_z1 :
              ((s.core.wvec[(l <<< (1 : Nat)).toNat]'(by rw [h2l_eq]; omega)).setWidth 64).toNat =
              off0 := by
            rw [BitVec.toNat_setWidth,
              Nat.mod_eq_of_lt (Nat.lt_trans (BitVec.isLt _) (by decide))]
            simpa [h2l_eq] using hoff_eq
          have h_z2 : ((s.core.wvec[((l <<< (1 : Nat)) + 1#64).toNat]'(by
                rw [h2l1_eq]; omega)).setWidth 64).toNat = sz0 := by
            rw [BitVec.toNat_setWidth,
              Nat.mod_eq_of_lt (Nat.lt_trans (BitVec.isLt _) (by decide))]
            simpa [h2l1_eq] using hsz_eq
          have hend_nat :
              ((s.core.wvec[(l <<< (1 : Nat)).toNat]'(by rw [h2l_eq]; omega)).setWidth 64 +
                (s.core.wvec[((l <<< (1 : Nat)) + 1#64).toNat]'(by
                  rw [h2l1_eq]; omega)).setWidth 64).toNat = end0 := by
            rw [BitVec.toNat_add, h_z1, h_z2, Nat.mod_eq_of_lt (by omega)]
          have hoff64 :
              ((s.core.wvec[2 * l.toNat]'h2l_lt).setWidth 64).toNat = off0 := by
            rw [BitVec.toNat_setWidth,
              Nat.mod_eq_of_lt (Nat.lt_trans (BitVec.isLt _) (by decide))]; exact hoff_eq
          c0_hsteps
          refine wp_loop_inv
            (fun (p, ()) mJ =>
              off0 ≤ p.toNat ∧ p.toNat ≤ end0 ∧
              WatchSliceOk F_cur s.core l.toNat p.toNat (end0 - p.toNat) ∧
              ∃ wsJ : List (BitVec 32), wsJ.length = 2 * c.max_vars ∧
                (FullMem c { s with scratch := { s.scratch with work_stk1 := wsJ } } ⋆ R) mJ)
            (fun (p, ()) _ => end0 - p.toNat)
            (fun Jj hLoopJ => ?_) ?_
          · c0_hsteps
            refine hLoopJ _ m2 ⟨by simp only [h2l_eq, hoff64]; exact Nat.le_refl _,
              by simp only [h2l_eq, hoff64]; omega, ?_, ws2, hlen2, hm2⟩
            simpa only [h2l_eq, hoff64, show end0 - off0 = sz0 by omega] using hslice0
          · rintro Jj ⟨p, ⟨⟩⟩ mJ ⟨hop, hpe, hrem, wsJ, hlenJ, hmJ⟩ hLoopJ
            c0_hsplit
            · have hp_lt : p.toNat < end0 := by
                have h1 : p.toNat <
                    ((s.core.wvec[(l <<< (1 : Nat)).toNat]'(by rw [h2l_eq]; omega)).setWidth 64 +
                      (s.core.wvec[((l <<< (1 : Nat)) + 1#64).toNat]'(by
                        rw [h2l1_eq]; omega)).setWidth 64).toNat := by c0_bound
                omega
              have hp_wstk : p.toNat < s.core.wstk.length := by omega
              let w0 := s.core.wstk[p.toNat]'hp_wstk
              have hw0_some : s.core.wstk[p.toNat]? = some w0 :=
                List.getElem?_eq_getElem hp_wstk
              have hstep := watchSliceOk_step hrem (by omega) hw0_some
              have hp1_eq : (p + 1#64).toNat = p.toNat + 1 := cmp_bv64_add1 (by omega)
              have hp2_eq : (p + 2#64).toNat = p.toNat + 2 := cmp_bv64_add2 (by omega)
              have hlv_eq : (l >>> (1 : Nat)).toNat = l.toNat / 2 := bv64_shr1_toNat l
              have hlv_fl : (l >>> (1 : Nat)).toNat < s.core.flags.length := by rw [hlv_eq]; omega
              have hlv_ws : (l >>> (1 : Nat)).toNat < wsJ.length := by rw [hlv_eq]; omega
              c0_hsteps_nogrp
              refine wp_join_group (ts := [i64])
                (fun (p', ()) m' =>
                  off0 ≤ p'.toNat ∧ p'.toNat ≤ end0 ∧ p.toNat < p'.toNat ∧
                  WatchSliceOk F_cur s.core l.toNat p'.toNat (end0 - p'.toNat) ∧
                  ∃ ws' : List (BitVec 32), ws'.length = 2 * c.max_vars ∧
                    (FullMem c { s with scratch := { s.scratch with work_stk1 := ws' } } ⋆ R) m')
                (fun _ ⟨p', ⟨⟩⟩ m' ⟨hop', hpe', hp_inc, hrem', ws', hlen', hm'⟩ => by
                  c0_hsteps
                  exact hLoopJ (p', ()) m' (by dsimp only; omega)
                    ⟨hop', hpe', hrem', ws', hlen', hm'⟩)
                (fun Jstep hJstep => by
                  clear hLoop2 J2 hLoopJ Jj hQ hnext hsp
                  c0_hsplit
                  · have hbin1 : (w0 &&& 0x80000000#32) ≠ 0#32 := by c0_bound
                    have hrem_p1 : WatchSliceOk F_cur s.core l.toNat (p.toNat + 1)
                        (end0 - (p.toNat + 1)) := by
                      simpa [Nat.sub_sub] using (hstep.1 hbin1).2.2.2
                    have hot_lt : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars :=
                      (hstep.1 hbin1).2.1
                    have hot_v_eq : ((w0 &&& 0x7FFFFFFF#32) >>> (1 : Nat)).toNat =
                        (w0 &&& 0x7FFFFFFF#32).toNat / 2 := bv32_shr1_nat_toNat _
                    have hot_fl : ((w0 &&& 0x7FFFFFFF#32) >>> (1 : Nat)).toNat <
                        s.core.flags.length := by rw [hot_v_eq]; omega
                    have hot_ws : ((w0 &&& 0x7FFFFFFF#32) >>> (1 : Nat)).toNat < wsJ.length := by
                      rw [hot_v_eq]; omega
                    c0_hsteps <;> first
                      | exact hJstep (p + 1#64, ()) mJ
                          ⟨by rw [hp1_eq]; omega, by rw [hp1_eq]; omega,
                           by rw [hp1_eq]; omega, by rw [hp1_eq]; exact hrem_p1,
                           wsJ, hlenJ, hmJ⟩
                      | (refine hJstep (p + 1#64, ()) _
                           ⟨by rw [hp1_eq]; omega, by rw [hp1_eq]; omega,
                            by rw [hp1_eq]; omega, by rw [hp1_eq]; exact hrem_p1,
                            ((wsJ.set (l >>> (1 : Nat)).toNat 1#32).set
                              ((w0 &&& 0x7FFFFFFF#32) >>> (1 : Nat)).toNat 1#32),
                            by simp [hlenJ], by assumption⟩)
                  · have hlg0 : (w0 &&& 0x80000000#32) = 0#32 := by c0_bound
                    have ⟨hrem2, hrem'⟩ := hstep.2 hlg0
                    have hrem_p2 : WatchSliceOk F_cur s.core l.toNat (p.toNat + 2)
                        (end0 - (p.toNat + 2)) := by simpa [Nat.sub_sub] using hrem'
                    c0_hsteps
                    exact hJstep (p + 2#64, ()) mJ
                      ⟨by rw [hp2_eq]; omega, by rw [hp2_eq]; omega,
                       by rw [hp2_eq]; omega, by rw [hp2_eq]; exact hrem_p2,
                       wsJ, hlenJ, hmJ⟩)
            · c0_hsteps
              exact hLoop2 (l + 1#64, ()) mJ (by dsimp only; rw [hl1_eq]; omega)
                ⟨by rw [hl1_eq]; omega, wsJ, hlenJ, hmJ⟩
        · clear hLoop2 J2 hc hl_le l hm1 hlen1 ws1 m1 hwat hw hdm hwv_len hws_len hwc hws1_len
          have hcv_64 : (BitVec.ofNat 64 s.core.cur_vars).toNat = s.core.cur_vars := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          have hcur_64 : s.core.cur_vars < 2 ^ 64 := by omega
          have hcur2_64 : 2 * s.core.cur_vars < 2 ^ 64 := by omega
          have hal_lt : s.core.arena_len < 2 ^ 31 := by omega
          c0_hsteps_nogrp
          refine wp_join_group (ts := [i64])
            (fun (_, ()) m_end =>
              ∃ ws_end : List (BitVec 32), ws_end.length = 2 * c.max_vars ∧
                (FullMem c { s with scratch := { s.scratch with work_stk1 := ws_end } } ⋆ R) m_end)
            (fun _ ⟨_, ⟨⟩⟩ m_end ⟨ws_end, hlen_end, hm_end⟩ => by
              c0_hsteps
              have hsp_end := fullSparseInvW_with_ws1 hsp hlen_end
              have hmod_end : ScratchModifies [.work_stk1] s
                  { s with scratch := { s.scratch with work_stk1 := ws_end } } := by
                intro f hf; cases f <;> first | exact rfl | (exfalso; exact hf (by simp))
              exact hQ () _ m_end hsp_end.1 ⟨rfl, hmod_end, hsp_end⟩ hm_end)
            (fun Jbrk hJbrk => by
              refine wp_loop_inv
                (fun (p, ()) m3 =>
                  p.toNat ≤ s.core.arena_len ∧
                  ∃ ws3 : List (BitVec 32), ws3.length = 2 * c.max_vars ∧
                    (FullMem c { s with scratch := { s.scratch with work_stk1 := ws3 } } ⋆ R) m3)
                (fun (p, ()) _ => s.core.arena_len - p.toNat)
                (fun J3 hLoop3 => ?_) ?_
              · c0_hsteps
                exact hLoop3 (0#64, ()) m2 ⟨Nat.zero_le _, ws2, hlen2, hm2⟩
              · rintro J3 ⟨p, ⟨⟩⟩ m3 ⟨hp_le, ws3, hlen3, hm3⟩ hLoop3
                c0_hsplit
                · have hp_lt : p.toNat < s.core.arena_len := by c0_bound
                  c0_hsplit
                  · c0_hsteps; exact hJbrk (p, ()) m3 ⟨ws3, hlen3, hm3⟩
                  · have hp3_le : p.toNat + 3 ≤ s.core.arena_len := by c0_bound
                    have hp2_eq : (p + 2#64).toNat = p.toNat + 2 := cmp_bv64_add2 (by omega)
                    let csz := s.core.arena[(p + 2#64).toNat]'(by rw [hp2_eq]; omega)
                    have hcsz_eq : s.core.arena[p.toNat + 2]'(by omega) = csz := by
                      dsimp only [csz]; simp only [hp2_eq]
                    have hn_bd := fullArenaNextOff_bounds (ar := s.core.arena)
                      (alen := s.core.arena_len) (cref := p.toNat) hp3_le
                    let s3 : FullState := { s with scratch := { s.scratch with work_stk1 := ws3 } }
                    have hsp3 := fullSparseInvW_with_ws1 hsp hlen3
                    c0_hsteps_nogrp; cmp_call hnext
                    refine ⟨c, s3, R, rfl, hsp3.1, hm3, ?_⟩
                    let np := fullArenaNextOff s.core.arena s.core.arena_len p.toNat
                    have hnp_le : np ≤ s.core.arena_len := hn_bd.2
                    have hnp_lt : np < 2 ^ 32 := Nat.lt_of_le_of_lt hnp_le (by omega)
                    have hnp_eq : (BitVec.ofNat 32 np).setWidth 64 = BitVec.ofNat 64 np := by
                      apply BitVec.eq_of_toNat_eq
                      rw [zext_toNat _ (by decide), bv32_ofNat_toNat hnp_lt,
                        bv64_ofNat_toNat (by omega)]
                    have hnp_to : (BitVec.ofNat 64 np).toNat = np := bv64_ofNat_toNat (by omega)
                    c0_hsteps_nogrp
                    refine wp_join_group (ts := [])
                      (fun () m4 =>
                        ∃ ws4 : List (BitVec 32), ws4.length = 2 * c.max_vars ∧
                          (FullMem c { s with scratch := { s.scratch with work_stk1 := ws4 } } ⋆
                            R) m4)
                      (fun _ ⟨⟩ m4 ⟨ws4, hlen4, hm4⟩ => by
                        c0_hsteps
                        dsimp only [Arg.val]
                        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : p.toNat < 2 ^ 32)]
                        exact hLoop3 ((BitVec.ofNat 32 np).setWidth 64, ()) m4
                          (by
                            dsimp only; rw [hnp_eq, hnp_to]
                            exact Nat.sub_lt_sub_left hp_lt hn_bd.1)
                          ⟨by rw [hnp_eq, hnp_to]; exact hnp_le, ws4, hlen4, hm4⟩)
                      (fun J4 hJ4 => by
                        c0_hsplit
                        · c0_hsplit
                          · have hcsz_ge3 : 3 ≤ csz.toNat := by c0_bound
                            c0_hsplit
                            · have hfit : p.toNat + 3 + csz.toNat ≤ s.core.arena_len := by
                                have h1 := hc
                                simp only [bv_c0, BitVec.reduceToNat] at h1
                                simp only [Nat.mod_eq_of_lt (by omega : p.toNat + 2 < 2 ^ 64)] at h1
                                rw [hcsz_eq] at h1
                                have hcsz_32 := csz.isLt
                                rw [Nat.mod_eq_of_lt (by omega : p.toNat + 3 + csz.toNat < 2 ^ 64),
                                  Nat.mod_eq_of_lt (by omega : s.core.arena_len < 2 ^ 64)] at h1
                                exact h1
                              have hp3csz_64 : p.toNat + 3 + csz.toNat < 2 ^ 64 := by omega
                              c0_hsteps_nogrp
                              refine wp_join_group (ts := [Ty.bool, Ty.bool, i32, i32])
                                (fun _ mI => mI = m3)
                                (fun _ ⟨sat, hd, ucnt, j_out, ⟨⟩⟩ mI hmI => by
                                  rw [hmI] at *
                                  clear hmI mI
                                  c0_hsteps_nogrp
                                  refine wp_join_group (ts := [i32])
                                    (fun _ mA =>
                                      ∃ wsK : List (BitVec 32), wsK.length = 2 * c.max_vars ∧
                                        (FullMem c { s with scratch :=
                                          { s.scratch with work_stk1 := wsK } } ⋆ R) mA)
                                    (fun _ ⟨_, ⟨⟩⟩ mA ⟨wsK, hlenK, hmK⟩ => by
                                      c0_hsteps; exact hJ4 () mA ⟨wsK, hlenK, hmK⟩)
                                    (fun Js hJs => by
                                      clear hLoop3 J3 hJbrk Jbrk hJ4 J4 hQ hnext hsp3 hsp s3
                                        hnp_to hnp_eq hnp_lt hnp_le hn_bd np
                                      c0_hsplit
                                      · c0_hsteps; exact hJs (j_out, ()) m3 ⟨ws3, hlen3, hm3⟩
                                      · c0_hsteps_nogrp
                                        refine wp_join_group (ts := []) (fun () mB => mB = m3)
                                          (fun _ ⟨⟩ mB hmB => by
                                            rw [hmB] at *
                                            clear hmB mB
                                            c0_hsplit
                                            · c0_hsteps_nogrp
                                              refine wp_loop_inv
                                                (fun (j2, ()) mK =>
                                                  j2.toNat ≤ csz.toNat ∧
                                                  ∃ wsK : List (BitVec 32),
                                                    wsK.length = 2 * c.max_vars ∧
                                                    (FullMem c { s with scratch :=
                                                      { s.scratch with work_stk1 := wsK } } ⋆ R) mK)
                                                (fun (j2, ()) _ => csz.toNat - j2.toNat)
                                                (fun JK hLoopK => ?_) ?_
                                              · c0_hsteps
                                                exact hLoopK (0#32, ()) m3
                                                  ⟨Nat.zero_le _, ws3, hlen3, hm3⟩
                                              · rintro JK ⟨j2, ⟨⟩⟩ mK
                                                  ⟨hj2_le, wsK, hlenK, hmK⟩ hLoopK
                                                c0_hsplit
                                                · have hj2_lt : j2.toNat < csz.toNat := by c0_bound
                                                  have hj2_1_eq :
                                                      (j2 + 1#32).toNat = j2.toNat + 1 :=
                                                    cmp_bv32_add1 (by omega)
                                                  have hpj2_eq : (p + 3#64 + j2.setWidth 64).toNat =
                                                      p.toNat + 3 + j2.toNat :=
                                                    cmp_bv64_add3_zext_toNat (by omega)
                                                  have hpj2_lt64 :
                                                      p.toNat + 3 + j2.toNat < 2 ^ 64 := by omega
                                                  have hpj2_ar :
                                                      (p + 3#64 + j2.setWidth 64).toNat <
                                                        s.core.arena.length := by
                                                    rw [hpj2_eq]; omega
                                                  have hpj2_mod_ar :
                                                      (p.toNat + 3 + j2.toNat) % 2 ^ 64 <
                                                        s.core.arena.length := by
                                                    rw [Nat.mod_eq_of_lt hpj2_lt64]
                                                    exact hpj2_eq ▸ hpj2_ar
                                                  c0_hsteps <;> first
                                                    | exact hLoopK (j2 + 1#32, ()) mK
                                                        (by dsimp only; rw [hj2_1_eq]; omega)
                                                        ⟨by rw [hj2_1_eq]; omega, wsK,
                                                         hlenK, hmK⟩
                                                    | (have hlit2_lt :
                                                           (s.core.arena[(p + 3#64 +
                                                             j2.setWidth 64).toNat]'hpj2_ar).toNat <
                                                           2 * s.core.cur_vars := by
                                                         have hraw :
                                                             (s.core.arena[(p.toNat + 3 +
                                                               j2.toNat) % 2 ^ 64]'hpj2_mod_ar
                                                               ).toNat <
                                                             2 * (s.core.cur_vars % 2 ^ 64) %
                                                               2 ^ 64 := by assumption
                                                         simp only [Nat.mod_eq_of_lt hpj2_lt64,
                                                           Nat.mod_eq_of_lt hcur_64,
                                                           Nat.mod_eq_of_lt hcur2_64] at hraw
                                                         simpa only [hpj2_eq] using hraw
                                                       have hfl2_lt :
                                                           ((s.core.arena[(p + 3#64 +
                                                             j2.setWidth 64).toNat]'hpj2_ar >>>
                                                             (1 : BitVec 32)).setWidth 64).toNat <
                                                           s.core.flags.length :=
                                                         bv32_shr1_zext_lt hlit2_lt
                                                           (hfl_len.symm ▸ hcv_le)
                                                       have hmap2_lt :
                                                           ((s.core.arena[(p + 3#64 +
                                                             j2.setWidth 64).toNat]'hpj2_ar >>>
                                                             (1 : BitVec 32)).setWidth 64).toNat <
                                                           wsK.length :=
                                                         bv32_shr1_zext_lt hlit2_lt
                                                           (hlenK.symm ▸ Nat.le_trans hcv_le
                                                             (Nat.le_mul_of_pos_left _
                                                               Nat.zero_lt_two))
                                                       c0_hsteps <;> first
                                                         | exact hLoopK (j2 + 1#32, ()) mK
                                                             (by dsimp only; rw [hj2_1_eq]; omega)
                                                             ⟨by rw [hj2_1_eq]; omega, wsK,
                                                              hlenK, hmK⟩
                                                         | (refine hLoopK (j2 + 1#32, ()) _
                                                              (by dsimp only; rw [hj2_1_eq]; omega)
                                                              ?_
                                                            refine ⟨by rw [hj2_1_eq]; omega,
                                                              wsK.set
                                                                ((s.core.arena[(p + 3#64 +
                                                                  j2.setWidth 64).toNat]'hpj2_ar >>>
                                                                  (1 : BitVec 32)).setWidth 64
                                                                  ).toNat 1#32,
                                                              by rw [List.length_set]; exact hlenK,
                                                              by assumption⟩))
                                                · c0_hsteps
                                                  exact hJs (j2, ()) mK ⟨wsK, hlenK, hmK⟩
                                            · c0_hsteps; exact hJs (j_out, ()) m3 ⟨ws3, hlen3, hm3⟩)
                                          (fun Js1 hJs1 => by
                                            c0_hsplit
                                            · c0_hsplit
                                              · c0_hsteps
                                                exact hJs (j_out, ()) m3 ⟨ws3, hlen3, hm3⟩
                                              · c0_hsteps; exact hJs1 () m3 rfl
                                            · c0_hsteps; exact hJs1 () m3 rfl)))
                                (fun JI hJI => by
                                  clear hLoop3 J3 hJbrk Jbrk hJ4 J4 hQ hnext hsp3 hsp s3
                                    hnp_to hnp_eq hnp_lt hnp_le hn_bd np
                                  refine wp_loop_inv
                                    (fun (_hd, _ucnt, j, ()) mL => j.toNat ≤ csz.toNat ∧ mL = m3)
                                    (fun (_, _, j, ()) _ => csz.toNat - j.toNat)
                                    (fun Js hLoopS => ?_) ?_
                                  · c0_hsteps
                                    exact hLoopS (false, 0#32, 0#32, ()) m3 ⟨Nat.zero_le _, rfl⟩
                                  · rintro Js ⟨_hd, _ucnt, j, ⟨⟩⟩ mL ⟨hj_le, hmL⟩ hLoopS
                                    rw [hmL] at *; clear hmL mL
                                    c0_hsplit
                                    · have hj_lt : j.toNat < csz.toNat := by c0_bound
                                      have hj1_eq : (j + 1#32).toNat = j.toNat + 1 :=
                                        cmp_bv32_add1 (by omega)
                                      have hpj_eq : (p + 3#64 + j.setWidth 64).toNat =
                                          p.toNat + 3 + j.toNat :=
                                        cmp_bv64_add3_zext_toNat (by omega)
                                      have hpj_lt64 : p.toNat + 3 + j.toNat < 2 ^ 64 := by omega
                                      have hpj_ar :
                                          (p + 3#64 + j.setWidth 64).toNat <
                                            s.core.arena.length := by rw [hpj_eq]; omega
                                      have hpj_mod_ar :
                                          (p.toNat + 3 + j.toNat) % 2 ^ 64 <
                                            s.core.arena.length := by
                                        rw [Nat.mod_eq_of_lt hpj_lt64]; exact hpj_eq ▸ hpj_ar
                                      c0_hsteps_nogrp
                                      refine wp_join_group (ts := [Ty.bool, Ty.bool, i32])
                                        (fun _ mO => mO = m3)
                                        (fun _ ⟨_, hd', ucnt', ⟨⟩⟩ mO hmO => by
                                          rw [hmO] at *; clear hmO mO; c0_hsteps
                                          exact hLoopS (hd', ucnt', j + 1#32, ()) m3
                                            (by dsimp only; rw [hj1_eq]; omega)
                                            ⟨by rw [hj1_eq]; omega, rfl⟩)
                                        (fun Jo hJo => by
                                          c0_hsplit
                                          · have hlit_lt :
                                                (s.core.arena[(p + 3#64 +
                                                  j.setWidth 64).toNat]'hpj_ar).toNat <
                                                2 * s.core.cur_vars := by
                                              have hraw :
                                                  (s.core.arena[(p.toNat + 3 +
                                                    j.toNat) % 2 ^ 64]'hpj_mod_ar).toNat <
                                                  2 * (s.core.cur_vars % 2 ^ 64) % 2 ^ 64 := by
                                                assumption
                                              simp only [Nat.mod_eq_of_lt hpj_lt64,
                                                Nat.mod_eq_of_lt hcur_64,
                                                Nat.mod_eq_of_lt hcur2_64] at hraw
                                              simpa only [hpj_eq] using hraw
                                            have hfl_lt :
                                                ((s.core.arena[(p + 3#64 +
                                                  j.setWidth 64).toNat]'hpj_ar >>>
                                                  (1 : BitVec 32)).setWidth 64).toNat <
                                                s.core.flags.length :=
                                              bv32_shr1_zext_lt hlit_lt (hfl_len.symm ▸ hcv_le)
                                            c0_hsplit
                                            · c0_hsteps
                                              exact hJI (true, _hd, _ucnt, j, ()) m3 rfl
                                            · refine wp_join_group (ts := [Ty.bool, i32])
                                                (fun _ mS => mS = m3)
                                                (fun _ ⟨hd', ucnt', ⟨⟩⟩ mS hmS => by
                                                  rw [hmS] at *; clear hmS mS; c0_hsteps
                                                  exact hJo (false, hd', ucnt', ()) m3 rfl)
                                                (fun Js1 hJs1 => by
                                                  c0_hsplit
                                                  · c0_hsteps <;> exact hJs1 (_, _, ()) m3 rfl
                                                  · c0_hsteps; exact hJs1 (_, _, ()) m3 rfl)
                                          · c0_hsteps
                                            exact hJo (false, _hd, _ucnt, ()) m3 rfl)
                                    · c0_hsteps; exact hJI (false, _, _, j, ()) m3 rfl)
                            · c0_hsteps; exact hJ4 () m3 ⟨ws3, hlen3, hm3⟩
                          · c0_hsteps; exact hJ4 () m3 ⟨ws3, hlen3, hm3⟩
                        · c0_hsteps; exact hJ4 () m3 ⟨ws3, hlen3, hm3⟩)
                · c0_hsteps
                  exact hJbrk (p, ()) m3 ⟨ws3, hlen3, hm3⟩)

/-! ## 3. `full_compact_assign_map` & `full_compact_record_ext` -/

/-- Canonical WP proof for `full_compact_assign_map`. -/
theorem full_compact_assign_map_wp (Γ : Env) :
    ∀ a m Q X, compactAssignMapSpec a m Q X →
      Func.wp Γ full_compact_assign_map_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  obtain ⟨c, s, ⟨⟩, R, rfl, hlen, _, hm, hQ⟩ := FullContract.elim hs
  have hcv_le := hlen.core_ok.cur_vars_le
  have hmax_lt : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  have hcv_lt : s.core.cur_vars < 0x7FFFFFFF := by unfold dimacsBound at hmax_lt; omega
  have hv_len := hlen.core_ok.vals_len
  have hws1_len := hlen.scratch_ok.work_stk1_len
  have hws2_len := hlen.scratch_ok.work_stk2_len
  unfold Func.wp full_compact_assign_map_body
  c0_hsteps_nogrp
  refine wp_loop_inv
    (fun (ncv, v, ()) mL =>
      v.toNat ≤ s.core.cur_vars ∧ ncv.toNat ≤ v.toNat ∧
      ∃ ws1 ws2 : List (BitVec 32), ws1.length = 2 * c.max_vars ∧ ws2.length = 2 * c.max_vars ∧
        (∀ u < v.toNat,
          ws1[u]? = some 0xFFFFFFFF#32 ∨
          ∃ nv < ncv.toNat, nv ≤ u ∧ s.core.vals[2 * u]?.getD 0#8 = 0#8 ∧
            ws1[u]? = some (BitVec.ofNat 32 nv) ∧ ws2[nv]? = some (BitVec.ofNat 32 u)) ∧
        (∀ nv < ncv.toNat,
          ∃ ov < v.toNat, nv ≤ ov ∧ s.core.vals[2 * ov]?.getD 0#8 = 0#8 ∧
            ws2[nv]? = some (BitVec.ofNat 32 ov) ∧ ws1[ov]? = some (BitVec.ofNat 32 nv)) ∧
        (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1, work_stk2 := ws2 } } ⋆
          R) mL)
    (fun (_, v, ()) _ => s.core.cur_vars - v.toNat)
    (fun J hLoop => ?_) ?_
  · c0_hsteps
    exact hLoop (0#64, 0#64, ()) m ⟨Nat.zero_le _, Nat.zero_le _, s.scratch.work_stk1,
      s.scratch.work_stk2, hws1_len, hws2_len, fun _ h => by simp at h,
      fun _ h => by simp at h, hm⟩
  · rintro J ⟨ncv, v, ⟨⟩⟩ mL ⟨hv_le, hnv_le, ws1, ws2, hlen1, hlen2, hmapL, hinvL, hmL⟩ hLoop
    c0_hsplit
    · have hv_lt : v.toNat < s.core.cur_vars := by c0_bound
      have hv1_eq : (v + (1 : BitVec 64)).toNat = v.toNat + 1 := cmp_bv64_add1 (by omega)
      have h2v_eq : (v <<< (1 : Nat)).toNat = 2 * v.toNat := bv64_shl1_toNat (by omega)
      have h2v_lt : (v <<< (1 : Nat)).toNat < s.core.vals.length := by rw [h2v_eq]; omega
      have hv_ws1 : v.toNat < ws1.length := by omega
      have hncv_lt : ncv.toNat < ws2.length := by omega
      have hncv1_eq : (ncv + (1 : BitVec 64)).toNat = ncv.toNat + 1 :=
        cmp_bv64_add1 (by omega)
      have hncv32 : ncv.setWidth 32 = BitVec.ofNat 32 ncv.toNat := BitVec.eq_of_toNat_eq (by
        rw [BitVec.toNat_setWidth, bv32_ofNat_toNat (by omega), Nat.mod_eq_of_lt (by omega)])
      have hv32 : v.setWidth 32 = BitVec.ofNat 32 v.toNat := BitVec.eq_of_toNat_eq (by
        rw [BitVec.toNat_setWidth, bv32_ofNat_toNat (by omega), Nat.mod_eq_of_lt (by omega)])
      refine wp_join_group (ts := [i64])
        (fun (ncv', ()) mN =>
          ncv'.toNat ≤ v.toNat + 1 ∧
          ∃ ws1' ws2' : List (BitVec 32),
            ws1'.length = 2 * c.max_vars ∧ ws2'.length = 2 * c.max_vars ∧
            (∀ u < v.toNat + 1,
              ws1'[u]? = some 0xFFFFFFFF#32 ∨
              ∃ nv < ncv'.toNat, nv ≤ u ∧ s.core.vals[2 * u]?.getD 0#8 = 0#8 ∧
                ws1'[u]? = some (BitVec.ofNat 32 nv) ∧ ws2'[nv]? = some (BitVec.ofNat 32 u)) ∧
            (∀ nv < ncv'.toNat,
              ∃ ov < v.toNat + 1, nv ≤ ov ∧ s.core.vals[2 * ov]?.getD 0#8 = 0#8 ∧
                ws2'[nv]? = some (BitVec.ofNat 32 ov) ∧ ws1'[ov]? = some (BitVec.ofNat 32 nv)) ∧
            (FullMem c { s with scratch :=
              { s.scratch with work_stk1 := ws1', work_stk2 := ws2' } } ⋆ R) mN)
        (fun _ ⟨ncv', ⟨⟩⟩ mN ⟨hnv_le', ws1', ws2', hlen1', hlen2', hmap', hinv', hmN⟩ => by
          c0_hsteps
          exact hLoop (ncv', v + (1 : BitVec 64), ()) mN (by dsimp only; rw [hv1_eq]; omega)
            ⟨by rw [hv1_eq]; omega, by rw [hv1_eq]; exact hnv_le', ws1', ws2', hlen1', hlen2',
             by rw [hv1_eq]; exact hmap', by rw [hv1_eq]; exact hinv', hmN⟩)
        (fun Jn hJn => by
          refine wp_join_group (ts := [])
            (fun () mE => mE = mL ∧
              (FullMem c { s with scratch :=
                { s.scratch with work_stk1 := ws1, work_stk2 := ws2 } } ⋆ R) mE)
            (fun _ ⟨⟩ mE ⟨hmE_eq, hmE⟩ => by
              subst mE
              c0_hsteps
              let ws1' := ws1.set v.toNat 0xFFFFFFFF#32
              refine hJn (ncv, ()) _ ⟨by omega, ws1', ws2, by simp [ws1', hlen1], hlen2,
                fun u hu => ?_, fun nv hnv => ?_, by assumption⟩
              · by_cases huv : u = v.toNat
                · subst huv; exact Or.inl (List.getElem?_set_self hv_ws1)
                · rcases hmapL u (by omega) with hff | ⟨nv, h1, h2, h3, h4, h5⟩
                  · exact Or.inl ((List.getElem?_set_ne (Ne.symm huv)).trans hff)
                  · exact Or.inr ⟨nv, h1, h2, h3, (List.getElem?_set_ne (Ne.symm huv)).trans h4, h5⟩
              · obtain ⟨ov, hov_lt, h1, h2, h3, h4⟩ := hinvL nv hnv
                refine ⟨ov, by omega, h1, h2, h3, ?_⟩
                exact (List.getElem?_set_ne (by omega)).trans h4)
            (fun Je hJe => by
              c0_hsplit
              · c0_hsplit
                · have hsext : (s.core.vals[(v <<< (1 : Nat)).toNat]'h2v_lt).signExtend 32 =
                      0#32 := by c0_bound
                  have hv_zero : s.core.vals[2 * v.toNat]?.getD 0#8 = 0#8 := by
                    rw [List.getElem?_eq_getElem (by omega : 2 * v.toNat < s.core.vals.length),
                      Option.getD_some]
                    exact cmp_bv8_sext32_eq0 (by simpa [h2v_eq] using hsext)
                  c0_hsteps
                  let ws1' := ws1.set v.toNat (ncv.setWidth 32)
                  let ws2' := ws2.set ncv.toNat (v.setWidth 32)
                  refine hJn (ncv + (1 : BitVec 64), ()) _ ⟨by rw [hncv1_eq]; omega, ws1', ws2',
                    by simp [ws1', hlen1], by simp [ws2', hlen2], fun u hu => ?_, fun nv hnv => ?_,
                    by assumption⟩
                  · by_cases huv : u = v.toNat
                    · subst huv; right
                      refine ⟨ncv.toNat, by rw [hncv1_eq]; omega, hnv_le, hv_zero, ?_, ?_⟩
                      · dsimp only [ws1']; rw [List.getElem?_set_self hv_ws1, hncv32]
                      · dsimp only [ws2']; rw [List.getElem?_set_self hncv_lt, hv32]
                    · rcases hmapL u (by omega) with hff | ⟨nv, h1, h2, h3, h4, h5⟩
                      · exact Or.inl ((List.getElem?_set_ne (Ne.symm huv)).trans hff)
                      · refine Or.inr ⟨nv, by rw [hncv1_eq]; omega, h2, h3,
                          (List.getElem?_set_ne (Ne.symm huv)).trans h4,
                          (List.getElem?_set_ne (by omega)).trans h5⟩
                  · rw [hncv1_eq] at hnv
                    by_cases hnk : nv = ncv.toNat
                    · subst hnk
                      refine ⟨v.toNat, by omega, hnv_le, hv_zero, ?_, ?_⟩
                      · dsimp only [ws2']; rw [List.getElem?_set_self hncv_lt, hv32]
                      · dsimp only [ws1']; rw [List.getElem?_set_self hv_ws1, hncv32]
                    · obtain ⟨ov, hov_lt, h1, h2, h3, h4⟩ := hinvL nv (by omega)
                      refine ⟨ov, by omega, h1, h2, ?_, ?_⟩
                      · dsimp only [ws2']; exact (List.getElem?_set_ne (Ne.symm hnk)).trans h3
                      · dsimp only [ws1']; exact (List.getElem?_set_ne (by omega)).trans h4
                · c0_hsteps; exact hJe () mL ⟨rfl, hmL⟩
              · c0_hsteps; exact hJe () mL ⟨rfl, hmL⟩))
    · have hv_eq : v.toNat = s.core.cur_vars := by c0_bound
      rw [hv_eq] at hmapL hinvL hnv_le
      c0_hsteps
      let s' : FullState :=
        { s with scratch := { s.scratch with work_stk1 := ws1, work_stk2 := ws2 } }
      have hlen' : s'.LengthsOk c := ⟨hlen.core_ok, { hlen.scratch_ok with
        work_stk1_len := hlen1, work_stk2_len := hlen2 }⟩
      have hmod' : ScratchModifies [.work_stk1, .work_stk2] s s' := by
        intro f hf; cases f <;> first | exact rfl | (exfalso; exact hf (by simp))
      exact hQ (ncv, ()) s' mL hlen' ⟨rfl, hmod', ⟨hnv_le, hcv_lt, hmapL, hinvL⟩⟩ hmL

/-- Canonical WP proof for `full_compact_record_ext`. -/
theorem full_compact_record_ext_wp (Γ : Env) :
    ∀ a m Q X, compactRecordExtSpec a m Q X →
      Func.wp Γ full_compact_record_ext_body a m Q X := by
  rintro ⟨h, old_cv, ncv, ⟨⟩⟩ m Q X hs
  obtain ⟨c, s, ⟨⟩, R, rfl, hlen, ⟨hold, hncv_le, helen⟩, hm, hQ0⟩ := FullContract.elim hs
  let hQ : ∀ (ok : Bool) (ext' : List (BitVec 32)) (elen' : Nat) m',
      let s' : FullState :=
        { s with scratch := { s.scratch with extend_stk := ext', extend_len := elen' } }
      s'.LengthsOk c → elen' ≤ c.extend_cap →
      (ok = false → ext' = s.scratch.extend_stk ∧ elen' = s.scratch.extend_len) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m' :=
    fun ok ext' elen' m' hlen' hel' hfalse hm' => by
      have hmod' : ScratchModifies [.extend_stk, .extend_len] s
          { s with scratch := { s.scratch with extend_stk := ext', extend_len := elen' } } := by
        intro f hf; cases f <;> first | exact rfl | (exfalso; exact hf (by simp))
      exact hQ0 (ok, ()) _ m' hlen' ⟨rfl, hmod', hel', fun hok => by
        obtain ⟨rfl, rfl⟩ := hfalse hok; rfl⟩ hm'
  have hcv_le := hlen.core_ok.cur_vars_le
  have hv_len := hlen.core_ok.vals_len
  have hws2_len := hlen.scratch_ok.work_stk2_len
  have hext_len := hlen.scratch_ok.extend_stk_len
  have hext_lt : c.extend_cap < 2 ^ 28 := c.hext
  have hmax_lt : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  have hsub_eq : (BitVec.ofNat 64 c.extend_cap - BitVec.ofNat 64 s.scratch.extend_len).toNat =
      c.extend_cap - s.scratch.extend_len := by
    rw [cmp_bv_sub_ofNat helen (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  unfold Func.wp full_compact_record_ext_body
  c0_hsplit
  · c0_hsteps
    exact hQ false s.scratch.extend_stk s.scratch.extend_len m hlen helen
      (fun _ => ⟨rfl, rfl⟩) hm
  · let cntFix (hi : Nat) : Nat :=
      (List.range hi).countP (fun u => decide (s.core.vals[2 * u]?.getD 0#8 ≠ 0#8))
    have hcf_step : ∀ u, cntFix (u + 1) =
        cntFix u + (if s.core.vals[2 * u]?.getD 0#8 ≠ 0#8 then 1 else 0) := by
      intro u; dsimp only [cntFix]
      rw [List.range_succ, List.countP_append, List.countP_singleton]
      by_cases hne : s.core.vals[2 * u]?.getD 0#8 ≠ 0#8 <;> simp [hne]
    have hcf_mono : ∀ {a b}, a ≤ b → cntFix a ≤ cntFix b := by
      intro a b hab
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
      induction d with
      | zero => simp
      | succ d ih =>
        rw [← Nat.add_assoc, hcf_step]
        exact Nat.le_trans (ih (Nat.le_add_right _ _)) (Nat.le_add_right _ _)
    c0_hsteps_nogrp
    refine wp_loop_inv
      (fun (nfix, v, ()) m1 =>
        v.toNat ≤ old_cv.toNat ∧ nfix.toNat ≤ v.toNat ∧ nfix.toNat = cntFix v.toNat ∧ m = m1)
      (fun (_, v, ()) _ => old_cv.toNat - v.toNat)
      (fun J1 hLoop1 => ?_) ?_
    · c0_hsteps; exact hLoop1 (0#64, 0#64, ()) m ⟨Nat.zero_le _, Nat.zero_le _, rfl, rfl⟩
    · rintro J1 ⟨nfix, v, ⟨⟩⟩ m1 ⟨hv_le, hnf_le, hnf_eq, rfl⟩ hLoop1
      c0_hsplit
      · have hv_lt : v.toNat < old_cv.toNat := by c0_bound
        have hv1_eq : (v + (1 : BitVec 64)).toNat = v.toNat + 1 := cmp_bv64_add1 (by omega)
        have h2v_eq : (v <<< (1 : Nat)).toNat = 2 * v.toNat := bv64_shl1_toNat (by omega)
        have h2v_lt : (v <<< (1 : Nat)).toNat < s.core.vals.length := by rw [h2v_eq]; omega
        have hnf1_eq : (nfix + (1 : BitVec 64)).toNat = nfix.toNat + 1 :=
          cmp_bv64_add1 (by omega)
        c0_hsteps
        · have hnz : s.core.vals[2 * v.toNat]?.getD 0#8 ≠ 0#8 := by
            have hsext : (s.core.vals[(v <<< (1 : Nat)).toNat]'h2v_lt).signExtend 32 ≠ 0#32 := by
              c0_bound
            rw [List.getElem?_eq_getElem (by omega : 2 * v.toNat < s.core.vals.length),
              Option.getD_some]
            intro hz; apply hsext; simp [h2v_eq, hz]
          exact hLoop1 (nfix + (1 : BitVec 64), v + (1 : BitVec 64), ()) m
            (by dsimp only; rw [hv1_eq]; omega)
            ⟨by rw [hv1_eq]; omega, by rw [hv1_eq, hnf1_eq]; omega,
             by rw [hv1_eq, hnf1_eq, hcf_step, ite_eq_left hnz, hnf_eq], rfl⟩
        · have hze : ¬ s.core.vals[2 * v.toNat]?.getD 0#8 ≠ 0#8 := by
            have hsext : (s.core.vals[(v <<< (1 : Nat)).toNat]'h2v_lt).signExtend 32 = 0#32 := by
              c0_bound
            rw [List.getElem?_eq_getElem (by omega : 2 * v.toNat < s.core.vals.length),
              Option.getD_some]
            intro hne
            exact hne (cmp_bv8_sext32_eq0 (by simpa [h2v_eq] using hsext))
          exact hLoop1 (nfix, v + (1 : BitVec 64), ()) m
            (by dsimp only; rw [hv1_eq]; omega)
            ⟨by rw [hv1_eq]; omega, by rw [hv1_eq]; omega,
             by rw [hv1_eq, hcf_step, ite_eq_right hze, hnf_eq]; omega, rfl⟩
      · have hv_eq : v.toNat = old_cv.toNat := by c0_bound
        have hnf_le_cv : nfix.toNat ≤ old_cv.toNat := hv_eq ▸ hnf_le
        have hnf_tot : nfix.toNat = cntFix old_cv.toNat := hv_eq ▸ hnf_eq
        c0_hsplit
        · c0_hsteps
          exact hQ false s.scratch.extend_stk s.scratch.extend_len m hlen helen
            (fun _ => ⟨rfl, rfl⟩) hm
        · have hneed_le : nfix.toNat + ncv.toNat + 1 ≤ c.extend_cap - s.scratch.extend_len := by
            have hcmp :
                (nfix + ncv + (1 : BitVec 64)).toNat ≤
                  (BitVec.ofNat 64 c.extend_cap - BitVec.ofNat 64 s.scratch.extend_len).toNat := by
              c0_bound
            rw [hsub_eq] at hcmp
            have hsum : (nfix + ncv + (1 : BitVec 64)).toNat = nfix.toNat + ncv.toNat + 1 := by
              rw [BitVec.toNat_add, BitVec.toNat_add, show (1 : BitVec 64).toNat = 1 from rfl,
                Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
            omega
          c0_hsteps_nogrp
          refine wp_loop_inv
            (fun (v2, p, ()) m2 =>
              v2.toNat ≤ old_cv.toNat ∧ p.toNat = s.scratch.extend_len + cntFix v2.toNat ∧
              ∃ ext2 : List (BitVec 32), ext2.length = c.extend_cap ∧
                (FullMem c { s with scratch := { s.scratch with extend_stk := ext2 } } ⋆ R) m2)
            (fun (v2, _, ()) _ => old_cv.toNat - v2.toNat)
            (fun J2 hLoop2 => ?_) ?_
          · have helen_64 : s.scratch.extend_len < 2 ^ 64 := by omega
            c0_hsteps; exact hLoop2 (0#64, BitVec.ofNat 64 s.scratch.extend_len, ()) m
              ⟨Nat.zero_le _, by dsimp only [cntFix]; simp [Nat.mod_eq_of_lt helen_64],
               s.scratch.extend_stk, hext_len, hm⟩
          · rintro J2 ⟨v2, p, ⟨⟩⟩ m2 ⟨hv2_le, hp_eq, ext2, hext2, hm2⟩ hLoop2
            c0_hsplit
            · have hv2_lt : v2.toNat < old_cv.toNat := by c0_bound
              have hv2_1_eq : (v2 + (1 : BitVec 64)).toNat = v2.toNat + 1 :=
                cmp_bv64_add1 (by omega)
              have h2v2_eq : (v2 <<< (1 : Nat)).toNat = 2 * v2.toNat := bv64_shl1_toNat (by omega)
              have h2v2_lt : (v2 <<< (1 : Nat)).toNat < s.core.vals.length := by rw [h2v2_eq]; omega
              have h2v2_mod : 2 * v2.toNat % 2 ^ 64 = 2 * v2.toNat := Nat.mod_eq_of_lt (by omega)
              c0_hsteps_nogrp
              refine wp_join_group (ts := [i64])
                (fun (p', ()) mJ =>
                  p'.toNat = s.scratch.extend_len + cntFix (v2.toNat + 1) ∧
                  ∃ extJ : List (BitVec 32), extJ.length = c.extend_cap ∧
                    (FullMem c { s with scratch := { s.scratch with extend_stk := extJ } } ⋆
                      R) mJ)
                (fun _ ⟨p', ⟨⟩⟩ mJ ⟨hp', extJ, hextJ, hmJ⟩ => by
                  c0_hsteps
                  exact hLoop2 (v2 + (1 : BitVec 64), p', ()) mJ
                    (by dsimp only; rw [hv2_1_eq]; omega)
                    ⟨by rw [hv2_1_eq]; omega, by rw [hv2_1_eq]; exact hp', extJ, hextJ, hmJ⟩)
                (fun Jext hJext => by
                  c0_hsplit
                  · have hnz2 : s.core.vals[2 * v2.toNat]?.getD 0#8 ≠ 0#8 := by
                      have hsext : (s.core.vals[(v2 <<< (1 : Nat)).toNat]'h2v2_lt).signExtend 32 ≠
                          0#32 := by
                        have h1 := hc; simp only [h2v2_mod] at h1; simp only [h2v2_eq]; exact h1
                      rw [List.getElem?_eq_getElem (by omega : 2 * v2.toNat < s.core.vals.length),
                        Option.getD_some]
                      intro hz; apply hsext; simp [h2v2_eq, hz]
                    have hcf_lt : cntFix v2.toNat + 1 ≤ nfix.toNat := by
                      have h1 := hcf_step v2.toNat; rw [ite_eq_left hnz2] at h1
                      have h2 := hcf_mono (show v2.toNat + 1 ≤ old_cv.toNat by omega)
                      omega
                    have hp_lt : p.toNat < ext2.length := by omega
                    have hp1_eq : (p + (1 : BitVec 64)).toNat = p.toNat + 1 :=
                      cmp_bv64_add1 (by omega)
                    c0_hsteps <;>
                    (refine hJext (p + (1 : BitVec 64), ()) _
                      ⟨by rw [hp1_eq, hcf_step, ite_eq_left hnz2, hp_eq]; omega,
                       _, ?_, by assumption⟩
                     rw [List.length_set]; exact hext2)
                  · have hze2 : ¬ s.core.vals[2 * v2.toNat]?.getD 0#8 ≠ 0#8 := by
                      have hsext : (s.core.vals[(v2 <<< (1 : Nat)).toNat]'h2v2_lt).signExtend 32 =
                          0#32 := by
                        have h1 := hc; simp only [h2v2_mod] at h1; simp only [h2v2_eq]; exact h1
                      rw [List.getElem?_eq_getElem (by omega : 2 * v2.toNat < s.core.vals.length),
                        Option.getD_some]
                      intro hne
                      exact hne (cmp_bv8_sext32_eq0 (by simpa [h2v2_eq] using hsext))
                    c0_hsteps
                    exact hJext (p, ()) m2
                      ⟨by rw [hcf_step, ite_eq_right hze2, hp_eq]; omega,
                       ext2, hext2, hm2⟩)
            · have hv2_eq : v2.toNat = old_cv.toNat := by c0_bound
              have hp_eq_tot : p.toNat = s.scratch.extend_len + nfix.toNat := by
                rw [hp_eq, hv2_eq, hnf_tot]
              have hp_lt_tag : p.toNat < ext2.length := by omega
              have hp1_eq : (p + (1 : BitVec 64)).toNat = p.toNat + 1 :=
                cmp_bv64_add1 (by omega)
              c0_hsteps_nogrp
              refine wp_loop_inv
                (fun (p3, nv, ()) m3 =>
                  nv.toNat ≤ ncv.toNat ∧ p3.toNat ≤ p.toNat + 1 + nv.toNat ∧
                  ∃ ext3 : List (BitVec 32), ext3.length = c.extend_cap ∧
                    (FullMem c { s with scratch := { s.scratch with extend_stk := ext3 } } ⋆
                      R) m3)
                (fun (_, nv, ()) _ => ncv.toNat - nv.toNat)
                (fun J3 hLoop3 => ?_) ?_
              · c0_hsteps
                refine hLoop3 (p + (1 : BitVec 64), 0#64, ()) _
                  ⟨Nat.zero_le _, by rw [hp1_eq]; omega,
                   ext2.set p.toNat
                     (2147483648#32 ||| 1073741824#32 |||
                       (BitVec.setWidth 32 ncv &&& 1073741823#32)),
                   by rw [List.length_set]; exact hext2, by assumption⟩
              · rintro J3 ⟨p3, nv, ⟨⟩⟩ m3 ⟨hnv_le3, hp3_le, ext3, hext3, hm3⟩ hLoop3
                c0_hsplit
                · have hnv_lt : nv.toNat < ncv.toNat := by c0_bound
                  have hnv_ws2 : nv.toNat < s.scratch.work_stk2.length := by omega
                  have hp3_lt : p3.toNat < ext3.length := by omega
                  have hnv1_eq : (nv + (1 : BitVec 64)).toNat = nv.toNat + 1 :=
                    cmp_bv64_add1 (by omega)
                  have hp3_1_eq : (p3 + (1 : BitVec 64)).toNat = p3.toNat + 1 :=
                    cmp_bv64_add1 (by omega)
                  c0_hsteps
                  refine hLoop3 (p3 + (1 : BitVec 64), nv + (1 : BitVec 64), ()) _
                    (by dsimp only; rw [hnv1_eq]; omega)
                    ⟨by rw [hnv1_eq]; omega, by rw [hp3_1_eq, hnv1_eq]; omega,
                     ext3.set p3.toNat (s.scratch.work_stk2[nv.toNat]'hnv_ws2),
                     by rw [List.length_set]; exact hext3, by assumption⟩
                · have hnv_eq : nv.toNat = ncv.toNat := by c0_bound
                  have hp3_le_cap : p3.toNat ≤ c.extend_cap := by omega
                  c0_hsteps
                  exact hQ true ext3 p3.toNat _
                    ⟨hlen.core_ok, { hlen.scratch_ok with extend_stk_len := hext3 }⟩
                    hp3_le_cap (fun h => Bool.noConfusion h) (by assumption)

end

end LeanQbe.T.Examples.Kissat.Proof.Compact
