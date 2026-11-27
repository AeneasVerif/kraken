/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S3SearchRestart
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S3Spec
public import LeanQbe.T.Examples.Kissat.FullM4CompactLemmas
public import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Examples.Kissat.FullArena

/-!
# Kissat Fidelity Step 13 Shard S3-B Proofs — Part 1a (`FullFidelityStep13S3SearchRestartProof1a`)

Callee-parametric (`Γ : Env`, `XPost := False`, `0` SAT model proofs) `Func.wp` proofs for the
`2` compaction functions in `FullFidelityStep13S3SearchRestart`:
1. `full_compact_mark_live_step13_wp` (`FullM4Compact.fullCompactMarkLiveSpec`)
2. `full_compact_vars_step13_wp` (`FullM4Compact.fullCompactVarsSpec`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S3

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM4Compact
open Kraken.Bedrock2.Test
open scoped FullArenaTactics

/-! ## 1. Local Arithmetic Helpers -/

section Helpers

private theorem sr1a_add1 {x : BitVec 64} (h : x.toNat + 1 < 2 ^ 64) :
    (x + (1 : BitVec 64)).toNat = x.toNat + 1 := by bv_omega

private theorem sr1a_add2 {x : BitVec 64} (h : x.toNat + 2 < 2 ^ 64) :
    (x + (2 : BitVec 64)).toNat = x.toNat + 2 := by bv_omega

private theorem sr1a_add1_32 {k s : BitVec 32} (h : k.toNat < s.toNat) :
    (k + (1 : BitVec 32)).toNat = k.toNat + 1 := by
  rw [BitVec.toNat_add, show (1 : BitVec 32).toNat = 1 from rfl,
    Nat.mod_eq_of_lt (by have := s.isLt; omega)]

private theorem sr1a_zext32 (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat :=
  zext_toNat x (by decide)

private theorem sr1a_shl1 {x : BitVec 64} (h : 2 * x.toNat < 2 ^ 64) :
    (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, show 2 ^ 1 = 2 from rfl,
    show x.toNat * 2 = 2 * x.toNat by omega, Nat.mod_eq_of_lt h]

private theorem sr1a_shr1_64 (x : BitVec 64) : (x >>> (1 : Nat)).toNat = x.toNat / 2 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]

private theorem sr1a_shr1_32 (x : BitVec 32) : (x >>> 1#32).toNat = x.toNat / 2 := by
  change (x >>> (1 : Nat)).toNat = x.toNat / 2
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]

end Helpers

/-! ## 2. `full_compact_mark_live` (`FullM4Compact.fullCompactMarkLiveSpec`) -/

/-- Step-13 `full_compact_mark_live` satisfies `FullM4Compact.fullCompactMarkLiveSpec`. -/
theorem full_compact_mark_live_step13_wp (Γ : Env)
    (hnext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X) :
    ∀ a m Q X, fullCompactMarkLiveSpec a m Q X →
      Func.wp Γ FullFidelityStep13S3.full_compact_mark_live_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hsp, hm, hQ⟩
  have hlen := hsp.1; have hw := hsp.2.1; have hdm := hsp.2.2.2.2.2
  have hwat : WatchesInv F_cur s.core := by
    have hm' := hw.watches; unfold ModeWatchesInv at hm'; rwa [ite_eq_left hdm] at hm'
  have hcv_le := hlen.core_ok.cur_vars_le; have hal_le := hlen.core_ok.arena_len_le
  have har_len := hlen.core_ok.arena_len_arr; have hwl_le := hlen.core_ok.wlen_le
  have hws_len := hlen.core_ok.wstk_len_arr; have hwv_len := hlen.core_ok.wvec_len
  have hv_len := hlen.core_ok.vals_len; have hfl_len := hlen.core_ok.flags_len
  have hws1_len := hlen.scratch_ok.work_stk1_len
  have hmax_lt : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  have hcv_64 : (BitVec.ofNat 64 s.core.cur_vars).toNat = s.core.cur_vars :=
    bv64_ofNat_toNat (by omega)
  have hnlits_eq : ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat =
      2 * s.core.cur_vars := by rw [sr1a_shl1 (by rw [hcv_64]; omega), hcv_64]
  dsimp only [Func.wp, FullFidelityStep13S3.full_compact_mark_live_body]
  c0_hsteps_nogrp
  -- Loop 1: `v < cv`
  refine wp_loop_group (ts := [i64])
    (fun fn ⟨v, ⟨⟩⟩ m1 => v.toNat ≤ s.core.cur_vars ∧ fn = s.core.cur_vars - v.toNat ∧
      ∃ ws1 : List (BitVec 32), ws1.length = 2 * c.max_vars ∧
        (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1 } } ⋆ R) m1) ?_ ?_
  · intro J1 fn ⟨v, ⟨⟩⟩ m1 hJ1 ⟨hv_le, hfn, ws1, hlen1, hm1⟩
    c0_hsplit
    · have hv_lt : v.toNat < s.core.cur_vars := by
        rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc; exact hc
      have hv1 : (v + 1).toNat = v.toNat + 1 := sr1a_add1 (by omega)
      have hv_fl : v.toNat < s.core.flags.length := by rw [hfl_len]; omega
      have h2v_eq : (v <<< (1 : Nat)).toNat = 2 * v.toNat := sr1a_shl1 (by omega)
      have h2v_v : (v <<< (1 : Nat)).toNat < s.core.vals.length := by
        rw [h2v_eq, hv_len]; omega
      have hv_ws : v.toNat < ws1.length := by rw [hlen1]; omega
      refine wp_join_group (ts := [i32]) (fun _ mN => m1 = mN)
        (fun _ ⟨val, ⟨⟩⟩ mN hmN => by
          rcases hmN with rfl
          c0_let_simp
          refine wp_store_sep (FullArenaTactics.c0_store_full_work_stk1
            (s := { s with scratch := { s.scratch with work_stk1 := ws1 } }) val hv_ws hm1) ?_
          intro m1' hm1'; c0_hsteps
          exact hJ1 (s.core.cur_vars - (v.toNat + 1)) _ m1' (by omega)
            ⟨by rw [hv1]; omega, by rw [hv1], ws1.set v.toNat val, by simp [hlen1], hm1'⟩)
        (fun Jn hJn => by
          c0_hsplit; rotate_left; · c0_hsteps; exact hJn (0#32, ()) m1 rfl
          c0_hsplit; · c0_hsteps; exact hJn (1#32, ()) m1 rfl
          · c0_hsteps; exact hJn (0#32, ()) m1 rfl)
    · -- Loop 2: `l < nlits`
      clear hc; c0_hsteps_nogrp
      refine wp_loop_group (ts := [i64])
        (fun fn ⟨l, ⟨⟩⟩ m2 => l.toNat ≤ 2 * s.core.cur_vars ∧
          fn = 2 * s.core.cur_vars - l.toNat ∧
          ∃ ws2 : List (BitVec 32), ws2.length = 2 * c.max_vars ∧
            (FullMem c { s with scratch := { s.scratch with work_stk1 := ws2 } } ⋆ R) m2) ?_ ?_
      · intro J2 fn ⟨l, ⟨⟩⟩ m2 hJ2 ⟨hl_le, hfn2, ws2, hlen2, hm2⟩
        c0_hsplit
        · have hl_lt : l.toNat < 2 * s.core.cur_vars := by
            rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64),
              Nat.mod_eq_of_lt (by omega : 2 * s.core.cur_vars < 2 ^ 64)] at hc; exact hc
          clear hc
          have hl1 : (l + 1).toNat = l.toNat + 1 := sr1a_add1 (by omega)
          have h2l_eq : (l <<< (1 : Nat)).toNat = 2 * l.toNat := sr1a_shl1 (by omega)
          have h2l1_eq : ((l <<< (1 : Nat)) + 1).toNat = 2 * l.toNat + 1 := by
            rw [sr1a_add1 (by rw [h2l_eq]; omega), h2l_eq]
          have h2l_lt : 2 * l.toNat < s.core.wvec.length := by rw [hwv_len]; omega
          have h2l1_lt : 2 * l.toNat + 1 < s.core.wvec.length := by rw [hwv_len]; omega
          have h2l_wv : (l <<< (1 : Nat)).toNat < s.core.wvec.length := by
            rw [h2l_eq]; exact h2l_lt
          have h2l1_wv : ((l <<< (1 : Nat)) + 1).toNat < s.core.wvec.length := by
            rw [h2l1_eq]; exact h2l1_lt
          let off0 := fullWatchOffCore s.core l.toNat
          let sz0 := fullWatchSizeCore s.core l.toNat
          have hoff_eq : (s.core.wvec[2 * l.toNat]'h2l_lt).toNat = off0 := by
            unfold off0 fullWatchOffCore
            rw [List.getElem?_eq_getElem h2l_lt, Option.getD_some]
          have hsz_eq : (s.core.wvec[2 * l.toNat + 1]'h2l1_lt).toNat = sz0 := by
            unfold sz0 fullWatchSizeCore
            rw [List.getElem?_eq_getElem h2l1_lt, Option.getD_some]
          have hbd : off0 + sz0 ≤ s.core.wlen := hwat.layout.bounds l.toNat hl_lt
          have hslice0 := hwat.slices l.toNat hl_lt
          let end0 := off0 + sz0
          have hend_nat :
              ((s.core.wvec[(l <<< (1 : Nat)).toNat]'h2l_wv).setWidth 64 +
                (s.core.wvec[((l <<< (1 : Nat)) + 1).toNat]'h2l1_wv).setWidth 64).toNat =
              end0 := by
            rw [BitVec.toNat_add, sr1a_zext32, sr1a_zext32]
            simp only [h2l_eq, h2l1_eq, hoff_eq, hsz_eq]; exact Nat.mod_eq_of_lt (by omega)
          c0_hsteps_nogrp
          refine wp_loop_group (ts := [i64])
            (fun fnP ⟨p, ⟨⟩⟩ mP => off0 ≤ p.toNat ∧ p.toNat ≤ end0 ∧ fnP = end0 - p.toNat ∧
              WatchSliceOk F_cur s.core l.toNat p.toNat (end0 - p.toNat) ∧
              ∃ wsP : List (BitVec 32), wsP.length = 2 * c.max_vars ∧
                (FullMem c { s with scratch :=
                  { s.scratch with work_stk1 := wsP } } ⋆ R) mP) ?_ ?_
          · intro JP fnP ⟨p, ⟨⟩⟩ mP hJP ⟨hop, hpe, hfnP, hrem, wsP, hlenP, hmP⟩
            c0_hsplit
            · have hp_lt : p.toNat < end0 := by
                simp only [show (1 : BitVec 64).toNat = 1 from rfl,
                  Nat.mod_eq_of_lt (by omega : 2 * l.toNat < 2 ^ 64),
                  Nat.mod_eq_of_lt (by omega : 2 * l.toNat + 1 < 2 ^ 64),
                  hoff_eq, hsz_eq, Nat.mod_eq_of_lt (by omega : off0 + sz0 < 2 ^ 64)] at hc
                exact hc
              have hp_ws : p.toNat < s.core.wstk.length := by rw [hws_len]; omega
              let w0 := s.core.wstk[p.toNat]'hp_ws
              have hstep := WatchSliceOk_step hrem (by omega) (List.getElem?_eq_getElem hp_ws)
              clear hc; dsimp only
              c0_hsteps_nogrp
              refine wp_join_group (ts := [i64])
                (fun ⟨pN, ⟨⟩⟩ mN => off0 ≤ pN.toNat ∧ pN.toNat ≤ end0 ∧ p.toNat < pN.toNat ∧
                  WatchSliceOk F_cur s.core l.toNat pN.toNat (end0 - pN.toNat) ∧
                  ∃ wsN : List (BitVec 32), wsN.length = 2 * c.max_vars ∧
                    (FullMem c { s with scratch :=
                      { s.scratch with work_stk1 := wsN } } ⋆ R) mN)
                (fun _ ⟨pN, ⟨⟩⟩ mN ⟨hopN, hpeN, hltN, hremN, wsN, hlenN, hmN⟩ => by
                  c0_hsteps; exact hJP (end0 - pN.toNat) (pN, ()) mN (by omega)
                    ⟨hopN, hpeN, rfl, hremN, wsN, hlenN, hmN⟩)
                (fun Jif hJif => by
                  c0_hsplit
                  · have hbin0 : (w0 &&& 0x80000000#32) ≠ 0#32 := hc
                    have hrem' := (hstep.1 hbin0).2.2.2
                    have hp1 : (p + 1).toNat = p.toNat + 1 := sr1a_add1 (by omega)
                    have hrem_p1 : WatchSliceOk F_cur s.core l.toNat (p.toNat + 1)
                        (end0 - (p.toNat + 1)) := by simpa [Nat.sub_sub] using hrem'
                    c0_hsteps_nogrp
                    refine wp_join_group (ts := [])
                      (fun _ mN => ∃ wsN : List (BitVec 32), wsN.length = 2 * c.max_vars ∧
                        (FullMem c { s with scratch :=
                          { s.scratch with work_stk1 := wsN } } ⋆ R) mN)
                      (fun _ ⟨⟩ mN ⟨wsN, hlenN, hmN⟩ => by
                        c0_hsteps; exact hJif (p + 1, ()) mN
                          ⟨by rw [hp1]; omega, by rw [hp1]; omega, by rw [hp1]; omega,
                            by rw [hp1]; exact hrem_p1, wsN, hlenN, hmN⟩)
                      (fun Jb hJb => by
                        c0_hsplit; rotate_left; · c0_hsteps; exact hJb () mP ⟨wsP, hlenP, hmP⟩
                        have hot_lt : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars := by
                          rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64),
                            Nat.mod_eq_of_lt (by omega : 2 * s.core.cur_vars < 2 ^ 64)] at hc
                          exact hc
                        c0_hsplit; rotate_left; · c0_hsteps; exact hJb () mP ⟨wsP, hlenP, hmP⟩
                        have hl_v : l.toNat < s.core.vals.length := by rw [hv_len]; omega
                        c0_hsplit; rotate_left; · c0_hsteps; exact hJb () mP ⟨wsP, hlenP, hmP⟩
                        have hot_v : ((w0 &&& 0x7FFFFFFF#32).setWidth 64).toNat <
                            s.core.vals.length := by rw [sr1a_zext32, hv_len]; omega
                        c0_hsplit; rotate_left; · c0_hsteps; exact hJb () mP ⟨wsP, hlenP, hmP⟩
                        have hlv_fl : (l >>> (1 : Nat)).toNat < s.core.flags.length := by
                          rw [sr1a_shr1_64, hfl_len]; omega
                        c0_hsplit; rotate_left; · c0_hsteps; exact hJb () mP ⟨wsP, hlenP, hmP⟩
                        have hotv_fl : (((w0 &&& 0x7FFFFFFF#32) >>> 1#32).setWidth 64).toNat <
                            s.core.flags.length := by
                          rw [sr1a_zext32, sr1a_shr1_32, hfl_len]; omega
                        c0_hsplit; rotate_left; · c0_hsteps; exact hJb () mP ⟨wsP, hlenP, hmP⟩
                        have hlv_ws : (l >>> (1 : Nat)).toNat < wsP.length := by
                          rw [sr1a_shr1_64, hlenP]; omega
                        have hotv_ws : (((w0 &&& 0x7FFFFFFF#32) >>> 1#32).setWidth 64).toNat <
                            (wsP.set (l >>> (1 : Nat)).toNat 1#32).length := by
                          rw [List.length_set, sr1a_zext32, sr1a_shr1_32, hlenP]; omega
                        c0_hsteps
                        exact hJb () _ ⟨_, by rw [List.length_set, List.length_set, hlenP], hm⟩)
                  · have hlg0 : (w0 &&& 0x80000000#32) = 0#32 := hc
                    have ⟨_, hrem'⟩ := hstep.2 hlg0
                    have hp2 : (p + 2).toNat = p.toNat + 2 := sr1a_add2 (by omega)
                    have hrem_p2 : WatchSliceOk F_cur s.core l.toNat (p.toNat + 2)
                        (end0 - (p.toNat + 2)) := by simpa [Nat.sub_sub] using hrem'
                    c0_hsteps; exact hJif (p + 2, ()) mP
                      ⟨by rw [hp2]; omega, by rw [hp2]; omega, by rw [hp2]; omega,
                        by rw [hp2]; exact hrem_p2, wsP, hlenP, hmP⟩)
            · c0_hsteps; exact hJ2 (2 * s.core.cur_vars - (l.toNat + 1)) _ mP (by omega)
                ⟨by rw [hl1]; omega, by rw [hl1], wsP, hlenP, hmP⟩
          · intro JP hJP; c0_hsteps
            have hoff64 : ((s.core.wvec[2 * l.toNat]'h2l_lt).setWidth 64).toNat = off0 := by
              rw [sr1a_zext32]; exact hoff_eq
            exact hJP sz0 _ m2 ⟨by simp only [h2l_eq, hoff64]; exact Nat.le_refl _,
              by simp only [h2l_eq, hoff64]; omega, by simp only [h2l_eq, hoff64]; omega,
              by simpa only [h2l_eq, hoff64, show end0 - off0 = sz0 by omega] using hslice0,
              ws2, hlen2, hm2⟩
        · -- Loop 3: `pos < alen` (`break` exits via `[i64]` join group)
          clear hc; c0_hsteps_nogrp
          refine wp_join_group (ts := [i64])
            (fun _ mB => ∃ wsB : List (BitVec 32), wsB.length = 2 * c.max_vars ∧
              (FullMem c { s with scratch := { s.scratch with work_stk1 := wsB } } ⋆ R) mB)
            (fun _ ⟨_, ⟨⟩⟩ mB ⟨wsB, hlenB, hmB⟩ => by
              c0_hsteps; exact hQ wsB mB (FullSparseInvW_with_work_stk1 hsp hlenB) hmB)
            (fun Jbrk hJbrk => ?_)
          c0_hsteps_nogrp
          refine wp_loop_group (ts := [i64])
            (fun fn3 ⟨pos, ⟨⟩⟩ m3 => pos.toNat ≤ s.core.arena_len ∧
              fn3 = s.core.arena_len - pos.toNat ∧
              ∃ ws3 : List (BitVec 32), ws3.length = 2 * c.max_vars ∧
                (FullMem c { s with scratch :=
                  { s.scratch with work_stk1 := ws3 } } ⋆ R) m3) ?_ ?_
          · intro J3 fn3 ⟨pos, ⟨⟩⟩ m3 hJ3 ⟨hpos_le, hfn3, ws3, hlen3, hm3⟩
            c0_hsplit
            · have hpos_lt : pos.toNat < s.core.arena_len := by
                have := c.harena; unfold dimacsBound at *
                rw [Nat.mod_eq_of_lt (by omega : s.core.arena_len < 2 ^ 64)] at hc; exact hc
              have hal_lt : s.core.arena_len < 2 ^ 31 := by
                have := c.harena; unfold dimacsBound at *; omega
              clear hc
              c0_hsplit
              · c0_hsteps; exact hJbrk (pos, ()) m3 ⟨ws3, hlen3, hm3⟩
              have hpos3_le : pos.toNat + 3 ≤ s.core.arena_len := by
                rw [show (3 : BitVec 64).toNat = 3 from rfl,
                  Nat.mod_eq_of_lt (by omega : pos.toNat + 3 < 2 ^ 64),
                  Nat.mod_eq_of_lt (by omega : s.core.arena_len < 2 ^ 64)] at hc; omega
              have hpos_ar : pos.toNat < s.core.arena.length := by rw [har_len]; omega
              have hpos2 : (pos + 2).toNat = pos.toNat + 2 := sr1a_add2 (by omega)
              have hpos2_ar : (pos + 2).toNat < s.core.arena.length := by
                rw [hpos2, har_len]; omega
              let csz := s.core.arena[(pos + 2).toNat]'hpos2_ar
              have hn_bounds := fullArenaNextOff_bounds (ar := s.core.arena)
                (alen := s.core.arena_len) (cref := pos.toNat) hpos3_le
              have hpos32 : (pos.setWidth 32).toNat = pos.toNat := by
                rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
              c0_hsteps_nogrp; c0_call hnext
              refine ⟨c, { s with scratch := { s.scratch with work_stk1 := ws3 } }, R, rfl,
                ⟨hlen.core_ok, { hlen.scratch_ok with work_stk1_len := hlen3 }⟩, hm3, ?_⟩
              dsimp only; simp only [hpos32]
              let npos_nat := fullArenaNextOff s.core.arena s.core.arena_len pos.toNat
              have hnpos_to : ((BitVec.ofNat 32 npos_nat).setWidth 64).toNat = npos_nat := by
                rw [sr1a_zext32, bv32_ofNat_toNat (by omega)]
              c0_hsteps_nogrp
              refine wp_join_group (ts := [])
                (fun _ m4 => ∃ ws4 : List (BitVec 32), ws4.length = 2 * c.max_vars ∧
                  (FullMem c { s with scratch := { s.scratch with work_stk1 := ws4 } } ⋆ R) m4)
                (fun _ ⟨⟩ m4 ⟨ws4, hlen4, hm4⟩ => by
                  c0_hsteps; exact hJ3 (s.core.arena_len - npos_nat) _ m4 (by rw [hfn3]; omega)
                    ⟨by rw [hnpos_to]; omega, by rw [hnpos_to], ws4, hlen4, hm4⟩)
                (fun J4 hJ4 => by
                  c0_hsplit; rotate_left; · c0_hsteps; exact hJ4 () m3 ⟨ws3, hlen3, hm3⟩
                  c0_hsplit; rotate_left; · c0_hsteps; exact hJ4 () m3 ⟨ws3, hlen3, hm3⟩
                  c0_hsplit; rotate_left; · c0_hsteps; exact hJ4 () m3 ⟨ws3, hlen3, hm3⟩
                  have hfit : pos.toNat + 3 + csz.toNat ≤ s.core.arena_len := by
                    have hcsz32 := csz.isLt
                    have hcsz_eq : s.core.arena[(pos.toNat + (2 : BitVec 64).toNat) % 2 ^ 64]'(by
                        rw [show (2 : BitVec 64).toNat = 2 from rfl,
                          Nat.mod_eq_of_lt (by omega), har_len]; omega) = csz := by
                      dsimp only [csz]; congr 1
                    rw [hcsz_eq, show (3 : BitVec 64).toNat = 3 from rfl,
                      Nat.mod_eq_of_lt (by omega : pos.toNat + 3 + csz.toNat < 2 ^ 64),
                      Nat.mod_eq_of_lt (by omega : s.core.arena_len < 2 ^ 64)] at hc; omega
                  c0_hsteps_nogrp
                  refine wp_join_group (ts := [Ty.bool, Ty.bool, i32, i32]) (fun _ mA => m3 = mA)
                    (fun _ ⟨sat, hd, ucnt, i0, ⟨⟩⟩ mA hmA => by
                      rcases hmA with rfl; c0_hsteps_nogrp
                      refine wp_join_group (ts := [i32])
                        (fun _ mF => ∃ wsF : List (BitVec 32), wsF.length = 2 * c.max_vars ∧
                          (FullMem c { s with scratch :=
                            { s.scratch with work_stk1 := wsF } } ⋆ R) mF)
                        (fun _ _ mF ⟨wsF, hlenF, hmF⟩ => by
                          c0_hsteps; exact hJ4 () mF ⟨wsF, hlenF, hmF⟩)
                        (fun Jif hJif => ?_)
                      c0_hsplit
                      · c0_hsteps; exact hJif (i0, ()) m3 ⟨ws3, hlen3, hm3⟩
                      · c0_hsteps_nogrp
                        refine wp_join_group (ts := []) (fun _ m' => m' = m3)
                          (fun _ ⟨⟩ m' hm' => by
                            rcases hm'.symm with rfl; c0_hsteps_nogrp; c0_hsplit; rotate_left
                            · c0_hsteps; exact hJif (i0, ()) m3 ⟨ws3, hlen3, hm3⟩
                            c0_hsteps_nogrp
                            refine wp_loop_group (ts := [i32])
                              (fun fnK ⟨i2, ⟨⟩⟩ mK => i2.toNat ≤ csz.toNat ∧
                                fnK = csz.toNat - i2.toNat ∧ ∃ wsK : List (BitVec 32),
                                wsK.length = 2 * c.max_vars ∧
                                (FullMem c { s with scratch :=
                                  { s.scratch with work_stk1 := wsK } } ⋆ R) mK) ?_ ?_
                            · intro JK fnK ⟨i2, ⟨⟩⟩ mK hJK ⟨hi2_le, hfnK, wsK, hlenK, hmK⟩
                              c0_hsplit; rotate_left
                              · c0_hsteps; exact hJif (i2, ()) mK ⟨wsK, hlenK, hmK⟩
                              have hi2_lt : i2.toNat < csz.toNat := hc
                              have hi2_1 : (i2 + 1).toNat = i2.toNat + 1 := sr1a_add1_32 hi2_lt
                              have hpi2 : (pos + 3 + i2.setWidth 64).toNat =
                                  pos.toNat + 3 + i2.toNat := by
                                rw [BitVec.toNat_add, BitVec.toNat_add, sr1a_zext32,
                                  show (3 : BitVec 64).toNat = 3 from rfl,
                                  Nat.mod_eq_of_lt (by omega : pos.toNat + 3 < 2 ^ 64),
                                  Nat.mod_eq_of_lt (by omega : pos.toNat + 3 + i2.toNat < 2 ^ 64)]
                              have hpi2_ar : (pos + 3 + i2.setWidth 64).toNat <
                                  s.core.arena.length := by rw [hpi2, har_len]; omega
                              c0_hsteps_nogrp
                              refine wp_join_group (ts := [])
                                (fun _ mN => ∃ wsN : List (BitVec 32), wsN.length = 2 * c.max_vars ∧
                                  (FullMem c { s with scratch :=
                                    { s.scratch with work_stk1 := wsN } } ⋆ R) mN)
                                (fun _ ⟨⟩ mN ⟨wsN, hlenN, hmN⟩ => by
                                  c0_hsteps; exact hJK (csz.toNat - (i2.toNat + 1)) _ mN (by omega)
                                    ⟨by rw [hi2_1]; omega, by rw [hi2_1], wsN, hlenN, hmN⟩)
                                (fun Jn hJn => ?_)
                              c0_hsplit; rotate_left; · c0_hsteps; exact hJn () mK ⟨wsK, hlenK, hmK⟩
                              let l2 := s.core.arena[(pos + 3 + i2.setWidth 64).toNat]'hpi2_ar
                              have hlit2_lt : l2.toNat < 2 * s.core.cur_vars := by
                                rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64),
                                  Nat.mod_eq_of_lt (by omega : 2 * s.core.cur_vars < 2 ^ 64)] at hc
                                simpa only [l2, hpi2, show (3 : BitVec 64).toNat = 3 from rfl,
                                  Nat.mod_eq_of_lt
                                    (by omega : pos.toNat + 3 + i2.toNat < 2 ^ 64)] using hc
                              have hlit2_v : (l2.setWidth 64).toNat < s.core.vals.length := by
                                rw [sr1a_zext32, hv_len]; omega
                              c0_hsplit; rotate_left; · c0_hsteps; exact hJn () mK ⟨wsK, hlenK, hmK⟩
                              have hlit2_fl : ((l2 >>> 1#32).setWidth 64).toNat <
                                  s.core.flags.length := by
                                rw [sr1a_zext32, sr1a_shr1_32, hfl_len]; omega
                              c0_hsplit; rotate_left; · c0_hsteps; exact hJn () mK ⟨wsK, hlenK, hmK⟩
                              have hlit2_ws : ((l2 >>> 1#32).setWidth 64).toNat < wsK.length := by
                                rw [sr1a_zext32, sr1a_shr1_32, hlenK]; omega
                              c0_hsteps
                              exact hJn () m ⟨wsK.set ((l2 >>> 1#32).setWidth 64).toNat 1#32,
                                by rw [List.length_set, hlenK], hm⟩
                            · intro JK hJK; c0_hsteps
                              exact hJK csz.toNat (0#32, ()) m3
                                ⟨Nat.zero_le _, by simp, ws3, hlen3, hm3⟩)
                          (fun Jred hJred => ?_)
                        c0_hsplit
                        · c0_hsplit
                          · c0_hsteps; exact hJif (i0, ()) m3 ⟨ws3, hlen3, hm3⟩
                          · c0_hsteps; exact hJred () m3 rfl
                        · c0_hsteps; exact hJred () m3 rfl)
                    (fun JA hJA => by
                      refine wp_loop_group (ts := [Ty.bool, i32, i32])
                        (fun fnI ⟨_, _, i, ⟨⟩⟩ mI => i.toNat ≤ csz.toNat ∧
                          fnI = csz.toNat - i.toNat ∧ m3 = mI) ?_ ?_
                      · intro JI fnI ⟨hd, ucnt, i, ⟨⟩⟩ mI hJI ⟨hi_le, hfnI, hmI⟩
                        rcases hmI with rfl
                        c0_hsplit; rotate_left
                        · c0_hsteps; exact hJA (false, hd, ucnt, i, ()) m3 rfl
                        have hi_lt : i.toNat < csz.toNat := hc
                        have hi1 : (i + 1).toNat = i.toNat + 1 := sr1a_add1_32 hi_lt
                        have hpi : (pos + 3 + i.setWidth 64).toNat = pos.toNat + 3 + i.toNat := by
                          rw [BitVec.toNat_add, BitVec.toNat_add, sr1a_zext32,
                            show (3 : BitVec 64).toNat = 3 from rfl,
                            Nat.mod_eq_of_lt (by omega : pos.toNat + 3 < 2 ^ 64),
                            Nat.mod_eq_of_lt (by omega : pos.toNat + 3 + i.toNat < 2 ^ 64)]
                        have hpi_ar : (pos + 3 + i.setWidth 64).toNat < s.core.arena.length := by
                          rw [hpi, har_len]; omega
                        c0_hsteps_nogrp
                        refine wp_join_group (ts := [Ty.bool, Ty.bool, i32]) (fun _ mN => m3 = mN)
                          ?_ ?_
                        · rintro _ ⟨_, hd', uc', ⟨⟩⟩ mN hmN
                          rcases hmN with rfl; c0_hsteps
                          exact hJI (csz.toNat - (i.toNat + 1)) (hd', uc', i + 1, ()) m3
                            (by omega) ⟨by rw [hi1]; omega, by rw [hi1], rfl⟩
                        · intro Jn hJn
                          c0_hsplit; rotate_left
                          · c0_hsteps; exact hJn (false, hd, ucnt, ()) m3 rfl
                          let l0 := s.core.arena[(pos + 3 + i.setWidth 64).toNat]'hpi_ar
                          have hlit_lt : l0.toNat < 2 * s.core.cur_vars := by
                            rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64),
                              Nat.mod_eq_of_lt (by omega : 2 * s.core.cur_vars < 2 ^ 64)] at hc
                            simpa only [l0, hpi, show (3 : BitVec 64).toNat = 3 from rfl,
                              Nat.mod_eq_of_lt
                                (by omega : pos.toNat + 3 + i.toNat < 2 ^ 64)] using hc
                          have hlit_v : (l0.setWidth 64).toNat < s.core.vals.length := by
                            rw [sr1a_zext32, hv_len]; omega
                          have hlit_fl : ((l0 >>> 1#32).setWidth 64).toNat <
                              s.core.flags.length := by
                            rw [sr1a_zext32, sr1a_shr1_32, hfl_len]; omega
                          c0_hsplit; · c0_hsteps; exact hJA (true, hd, ucnt, i, ()) m3 rfl
                          c0_hsteps <;> exact hJn (false, _, _, ()) m3 rfl
                      · intro JI hJI; c0_hsteps
                        exact hJI csz.toNat (false, 0#32, 0#32, ()) m3
                          ⟨Nat.zero_le _, by simp, rfl⟩))
            · c0_hsteps; exact hJbrk (pos, ()) m3 ⟨ws3, hlen3, hm3⟩
          · intro J3 hJ3; c0_hsteps
            exact hJ3 s.core.arena_len (0#64, ()) m2
              ⟨Nat.zero_le _, by simp, ws2, hlen2, hm2⟩
      · intro J2 hJ2; c0_hsteps
        exact hJ2 (2 * s.core.cur_vars) (0#64, ()) m1 ⟨Nat.zero_le _, by simp, ws1, hlen1, hm1⟩
  · intro J1 hJ1; c0_hsteps
    exact hJ1 s.core.cur_vars (0#64, ()) m
      ⟨Nat.zero_le _, by simp, s.scratch.work_stk1, hws1_len, hm⟩

/-! ## 3. `full_compact_vars` (`FullM4Compact.fullCompactVarsSpec`) -/

private theorem sr1a_cv_lengths {c c' : FullCfg} {s : FullState}
    {vals' : List (BitVec 8)} {fl' lvl' rsns' qp' qn' qs' ps' : List (BitVec 32)}
    {ph' pt' pb' wb' : List (BitVec 8)} {sc' : List (BitVec 64)} {ncv tgt bst : BitVec 64}
    (hlen : s.LengthsOk c) (hcompat : FullCfgCompat c c')
    (hcv_ge : c'.mv ≤ ncv.toNat) (hcv_le : ncv.toNat ≤ c.max_vars)
    (hvl : vals'.length = 2 * c.max_vars) (hfl : fl'.length = c.max_vars)
    (hlv : lvl'.length = c.max_vars) (hrs : rsns'.length = c.max_vars)
    (hph : ph'.length = c.max_vars) (hpt : pt'.length = c.max_vars)
    (hpb : pb'.length = c.max_vars) (hwb : wb'.length = c.max_vars)
    (hsc : sc'.length = c.max_vars) (hqs : qs'.length = c.max_vars)
    (hqp : qp'.length = c.max_vars) (hqn : qn'.length = c.max_vars)
    (hps : ps'.length = c.max_vars) :
    FullState.LengthsOk c'
      { core := { s.core with
          vals := vals', flags := fl', lvl := lvl', rsns := rsns',
          frame_trail := s.core.frame_trail.set 0 0#32,
          frame_dec := s.core.frame_dec.set 0 0xFFFFFFFF#32,
          trail_end := 0, propagated := 0, cur_level := 0,
          unflushed := 0#64, confl_ref := 0xFFFFFFFF#64, confl_type := 0#64,
          cur_vars := ncv.toNat, unassigned := ncv }
        scratch := { s.scratch with
          phases := ph', phases_target := pt', phases_best := pb', walk_best := wb',
          score := sc', q_stamp := qs', q_prev := qp', q_next := qn', pos := ps',
          target_assigned := tgt, best_assigned := bst } } := by
  obtain ⟨_, _, _, hmax', _, har, hwc, hdel, hred, hext, hscr⟩ := hcompat
  exact ⟨⟨hmax' ▸ hvl, hmax' ▸ hlen.core_ok.lit_mark_len, hmax' ▸ hlen.core_ok.mrk_len,
    hmax' ▸ hfl, hmax' ▸ hlv, hmax' ▸ hrs, hmax' ▸ hlen.core_ok.trl_len,
    hmax' ▸ hlen.core_ok.trail_pos_len, hmax' ▸ hlen.core_ok.tmp_len_arr,
    hmax' ▸ hlen.core_ok.min_clr_len_arr,
    hmax' ▸ (by rw [List.length_set]; exact hlen.core_ok.frame_trail_len),
    hmax' ▸ (by rw [List.length_set]; exact hlen.core_ok.frame_dec_len),
    hmax' ▸ hlen.core_ok.wvec_len, hmax' ▸ hlen.core_ok.repr_len,
    by simp only [FullCfg.minDepth, hmax']; exact hlen.core_ok.min_stk_len,
    har ▸ hlen.core_ok.arena_len_arr, hwc ▸ hlen.core_ok.wstk_len_arr,
    hcv_ge, hmax' ▸ hcv_le, har ▸ hlen.core_ok.arena_len_le, hwc ▸ hlen.core_ok.wlen_le,
    Nat.zero_le _, Nat.zero_le _, hmax' ▸ hlen.core_ok.tmp_len_le,
    hmax' ▸ hlen.core_ok.min_clr_len_le⟩,
   ⟨hmax' ▸ hlen.scratch_ok.walk_vals_len, hmax' ▸ hph, hmax' ▸ hpt, hmax' ▸ hpb, hmax' ▸ hwb,
    hmax' ▸ hlen.scratch_ok.heap_len_arr, hmax' ▸ hps, hmax' ▸ hlen.scratch_ok.shrink_stk_len,
    hmax' ▸ hqp, hmax' ▸ hqn, hmax' ▸ hqs, hmax' ▸ hlen.scratch_ok.wsort_len,
    hmax' ▸ hlen.scratch_ok.work_stk1_len, hmax' ▸ hlen.scratch_ok.work_stk2_len,
    hmax' ▸ hlen.scratch_ok.tarjan_mark_len, hmax' ▸ hlen.scratch_ok.tarjan_reach_len,
    hmax' ▸ hsc, hmax' ▸ hlen.scratch_ok.sim_sig_len, hlen.scratch_ok.glue_used_len,
    hlen.scratch_ok.last_learned_len, hdel ▸ hlen.scratch_ok.delayed_len_arr,
    hred ▸ hlen.scratch_ok.red_refs_len, hext ▸ hlen.scratch_ok.extend_stk_len,
    hscr ▸ hlen.scratch_ok.scratch_buf_len⟩⟩

private structure Sr1aL3 (c : FullCfg) where
  fl : List (BitVec 32)
  lvl : List (BitVec 32)
  rsns : List (BitVec 32)
  qp : List (BitVec 32)
  qn : List (BitVec 32)
  qs : List (BitVec 32)
  ps : List (BitVec 32)
  ph : List (BitVec 8)
  pt : List (BitVec 8)
  pb : List (BitVec 8)
  wb : List (BitVec 8)
  sc : List (BitVec 64)
  hfl : fl.length = c.max_vars
  hlv : lvl.length = c.max_vars
  hrs : rsns.length = c.max_vars
  hqp : qp.length = c.max_vars
  hqn : qn.length = c.max_vars
  hqs : qs.length = c.max_vars
  hps : ps.length = c.max_vars
  hph : ph.length = c.max_vars
  hpt : pt.length = c.max_vars
  hpb : pb.length = c.max_vars
  hwb : wb.length = c.max_vars
  hsc : sc.length = c.max_vars

private abbrev Sr1aL3.toState {c : FullCfg} (st : Sr1aL3 c) (s : FullState)
    (vals1 : List (BitVec 8)) : FullState :=
  { core := { s.core with vals := vals1, flags := st.fl, lvl := st.lvl, rsns := st.rsns }
    scratch := { s.scratch with
      phases := st.ph, phases_target := st.pt, phases_best := st.pb, walk_best := st.wb,
      score := st.sc, q_stamp := st.qs, q_prev := st.qp, q_next := st.qn, pos := st.ps } }

/-- Step-13 `full_compact_vars` (also zeroing `ph/ptgt/pbst/wbst[ncv..old_cv)`) satisfies
`FullM4Compact.fullCompactVarsSpec`. -/
theorem full_compact_vars_step13_wp (Γ : Env) :
    ∀ a m Q X, fullCompactVarsSpec a m Q X →
      Func.wp Γ FullFidelityStep13S3.full_compact_vars_body a m Q X := by
  rintro ⟨h, old_cv, ncv, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hold, hncv_le, hinv_ok, hm, hQ⟩
  have hmax_lt : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  have hcv_le := hlen.core_ok.cur_vars_le
  have hcv2_lt64 : 2 * old_cv.toNat < 2 ^ 64 := by unfold dimacsBound at hmax_lt; omega
  have hcv_lt64 : old_cv.toNat < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left _ Nat.zero_lt_two) hcv2_lt64
  have hncv_lt64 : ncv.toNat < 2 ^ 64 := Nat.lt_of_le_of_lt hncv_le hcv_lt64
  have hv_len := hlen.core_ok.vals_len; have hfl_len := hlen.core_ok.flags_len
  have hlv_len := hlen.core_ok.lvl_len; have hrs_len := hlen.core_ok.rsns_len
  have hft_len := hlen.core_ok.frame_trail_len; have hfd_len := hlen.core_ok.frame_dec_len
  have hph_len := hlen.scratch_ok.phases_len; have hpt_len := hlen.scratch_ok.phases_target_len
  have hpb_len := hlen.scratch_ok.phases_best_len; have hwb_len := hlen.scratch_ok.walk_best_len
  have hsc_len := hlen.scratch_ok.score_len; have hqs_len := hlen.scratch_ok.q_stamp_len
  have hqp_len := hlen.scratch_ok.q_prev_len; have hqn_len := hlen.scratch_ok.q_next_len
  have hps_len := hlen.scratch_ok.pos_len; have hws2_len := hlen.scratch_ok.work_stk2_len
  have hnlits_eq : (old_cv <<< (1 : Nat)).toNat = 2 * old_cv.toNat := by
    rw [BitVec.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega
  dsimp only [Func.wp, FullFidelityStep13S3.full_compact_vars_body]
  c0_hsteps_nogrp
  -- Loop 1: zero `vals[0..2*old_cv)`
  refine wp_loop_inv
    (fun (l, ()) m1 => l.toNat ≤ 2 * old_cv.toNat ∧
      ∃ vals1 : List (BitVec 8), vals1.length = 2 * c.max_vars ∧
        (∀ i < l.toNat, vals1[i]? = some 0#8) ∧
        (FullMem c { s with core := { s.core with vals := vals1 } } ⋆ R) m1)
    (fun (l, ()) _ => 2 * old_cv.toNat - l.toNat)
    (fun J1 hL1 => by
      c0_hsteps
      exact hL1 (0#64, ()) m ⟨Nat.zero_le _, s.core.vals, hv_len, (fun _ h => by cases h), hm⟩)
    (fun J1 ⟨l, ⟨⟩⟩ m1 ⟨hl_le, vals1, hvl1, hz1, hm1⟩ hL1 => ?_)
  c0_hsplit
  · have hl_lt : l.toNat < 2 * old_cv.toNat := by
      have h1 : l.toNat < (old_cv <<< (1 : Nat)).toNat := hc; rwa [hnlits_eq] at h1
    have hl1 : (l + 1#64).toNat = l.toNat + 1 := sr1a_add1 (by omega)
    have hl_v : l.toNat < vals1.length := by rw [hvl1]; omega
    c0_hsteps_nobound
    refine hL1 (l + 1#64, ()) m (by dsimp only; rw [hl1]; omega)
      ⟨by rw [hl1]; omega, vals1.set l.toNat 0#8, by rw [List.length_set, hvl1], fun i hi => ?_, hm⟩
    rw [hl1] at hi
    by_cases hil : i = l.toNat
    · subst hil; exact List.getElem?_set_self hl_v
    · rw [List.getElem?_set_ne (Ne.symm hil)]; exact hz1 i (by omega)
  · clear hL1 J1
    have hl_eq : l.toNat = 2 * old_cv.toNat := by
      have h1 : ¬ l.toNat < (old_cv <<< (1 : Nat)).toNat := hc; rw [hnlits_eq] at h1; omega
    rw [hl_eq] at hz1
    c0_hsteps_nogrp_nobound
    -- Loop 2: compact `nv < ncv`
    refine wp_loop_inv
      (fun (tgt_asg, bst_asg, nv, ()) m2 => nv.toNat ≤ ncv.toNat ∧
        ∃ st : Sr1aL3 c, (FullMem c (st.toState s vals1) ⋆ R) m2)
      (fun (_, _, nv, ()) _ => ncv.toNat - nv.toNat)
      (fun J2 hL2 => by
        c0_hfast_nobound
        exact hL2 (0#64, 0#64, 0#64, ()) m1 ⟨Nat.zero_le _,
          ⟨s.core.flags, s.core.lvl, s.core.rsns, s.scratch.q_prev, s.scratch.q_next,
            s.scratch.q_stamp, s.scratch.pos, s.scratch.phases, s.scratch.phases_target,
            s.scratch.phases_best, s.scratch.walk_best, s.scratch.score, hfl_len, hlv_len, hrs_len,
            hqp_len, hqn_len, hqs_len, hps_len, hph_len, hpt_len, hpb_len, hwb_len, hsc_len⟩,
          compactMem_cast hm1 rfl⟩)
      (fun J2 ⟨tgt_asg, bst_asg, nv, ⟨⟩⟩ m2 ⟨hnv_le, st2, hm2⟩ hL2 => ?_)
    c0_hsplit
    · clear hm1
      have hnv_lt : nv.toNat < ncv.toNat := hc
      have hnv_cm : nv.toNat < c.max_vars :=
        Nat.lt_of_lt_of_le hnv_lt (Nat.le_trans hncv_le (hold ▸ hcv_le))
      have hnv_ws2 : nv.toNat < s.scratch.work_stk2.length :=
        hws2_len ▸ Nat.lt_of_lt_of_le hnv_cm (Nat.le_mul_of_pos_left _ Nat.zero_lt_two)
      have hov_lt : (s.scratch.work_stk2[nv.toNat]'hnv_ws2).toNat < old_cv.toNat := by
        simpa [List.getElem?_eq_getElem hnv_ws2] using hinv_ok nv.toNat hnv_lt
      have hov_cm : ((s.scratch.work_stk2[nv.toNat]'hnv_ws2).setWidth 64).toNat < c.max_vars := by
        rw [sr1a_zext32]; exact Nat.lt_of_lt_of_le hov_lt (hold ▸ hcv_le)
      have hnv_fl2 : nv.toNat < st2.fl.length := st2.hfl ▸ hnv_cm
      have hov_fl2 : ((s.scratch.work_stk2[nv.toNat]'hnv_ws2).setWidth 64).toNat < st2.fl.length :=
        st2.hfl ▸ hov_cm
      have hnv_ph2 : nv.toNat < st2.ph.length := st2.hph ▸ hnv_cm
      have hov_ph2 : ((s.scratch.work_stk2[nv.toNat]'hnv_ws2).setWidth 64).toNat < st2.ph.length :=
        st2.hph ▸ hov_cm
      have hnv_pt2 : nv.toNat < st2.pt.length := st2.hpt ▸ hnv_cm
      have hov_pt2 : ((s.scratch.work_stk2[nv.toNat]'hnv_ws2).setWidth 64).toNat < st2.pt.length :=
        st2.hpt ▸ hov_cm
      have hnv_pb2 : nv.toNat < st2.pb.length := st2.hpb ▸ hnv_cm
      have hov_pb2 : ((s.scratch.work_stk2[nv.toNat]'hnv_ws2).setWidth 64).toNat < st2.pb.length :=
        st2.hpb ▸ hov_cm
      have hnv_wb2 : nv.toNat < st2.wb.length := st2.hwb ▸ hnv_cm
      have hov_wb2 : ((s.scratch.work_stk2[nv.toNat]'hnv_ws2).setWidth 64).toNat < st2.wb.length :=
        st2.hwb ▸ hov_cm
      have hnv_sc2 : nv.toNat < st2.sc.length := st2.hsc ▸ hnv_cm
      have hov_sc2 : ((s.scratch.work_stk2[nv.toNat]'hnv_ws2).setWidth 64).toNat < st2.sc.length :=
        st2.hsc ▸ hov_cm
      have hnv_qs2 : nv.toNat < st2.qs.length := st2.hqs ▸ hnv_cm
      have hov_qs2 : ((s.scratch.work_stk2[nv.toNat]'hnv_ws2).setWidth 64).toNat < st2.qs.length :=
        st2.hqs ▸ hov_cm
      have hnv_lv2 : nv.toNat < st2.lvl.length := st2.hlv ▸ hnv_cm
      have hnv_rs2 : nv.toNat < st2.rsns.length := st2.hrs ▸ hnv_cm
      have hnv1 : (nv + 1#64).toNat = nv.toNat + 1 :=
        sr1a_add1 (Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hnv_lt) hncv_lt64)
      c0_hfast_nobound <;>
        (refine hL2 (_, _, nv + 1#64, ()) m
          (by dsimp only; rw [hnv1]; exact Nat.sub_lt_sub_left hnv_lt (Nat.lt_succ_self _))
          ⟨by rw [hnv1]; exact Nat.succ_le_of_lt hnv_lt,
            ⟨_, _, _, st2.qp, st2.qn, _, st2.ps, _, _, _, _, _,
              by rw [List.length_set]; exact st2.hfl, by rw [List.length_set]; exact st2.hlv,
              by rw [List.length_set]; exact st2.hrs, st2.hqp, st2.hqn,
              by rw [List.length_set]; exact st2.hqs, st2.hps,
              by rw [List.length_set]; exact st2.hph, by rw [List.length_set]; exact st2.hpt,
              by rw [List.length_set]; exact st2.hpb, by rw [List.length_set]; exact st2.hwb,
              by rw [List.length_set]; exact st2.hsc⟩, hm⟩)
    · clear hL2 J2 hm1
      c0_hsteps_nogrp_nobound
      -- Loop 3: zero `v ∈ [ncv, old_cv)` including `ph/ptgt/pbst/wbst`
      refine wp_loop_inv
        (fun (v, ()) m3 => v.toNat ≤ old_cv.toNat ∧
          ∃ st : Sr1aL3 c, (FullMem c (st.toState s vals1) ⋆ R) m3)
        (fun (v, ()) _ => old_cv.toNat - v.toNat)
        (fun J3 hL3 => by
          c0_hfast_nobound
          exact hL3 (ncv, ()) m2 ⟨hncv_le, st2, hm2⟩)
        (fun J3 ⟨v, ⟨⟩⟩ m3 ⟨hv_le3, st, hm3⟩ hL3 => ?_)
      c0_hsplit
      · clear hm2
        have hv_lt : v.toNat < old_cv.toNat := hc
        have hv_cm : v.toNat < c.max_vars := Nat.lt_of_lt_of_le hv_lt (hold ▸ hcv_le)
        have hv_fl3 : v.toNat < st.fl.length := st.hfl ▸ hv_cm
        have hv_lv3 : v.toNat < st.lvl.length := st.hlv ▸ hv_cm
        have hv_rs3 : v.toNat < st.rsns.length := st.hrs ▸ hv_cm
        have hv_sc3 : v.toNat < st.sc.length := st.hsc ▸ hv_cm
        have hv_ph3 : v.toNat < st.ph.length := st.hph ▸ hv_cm
        have hv_pt3 : v.toNat < st.pt.length := st.hpt ▸ hv_cm
        have hv_pb3 : v.toNat < st.pb.length := st.hpb ▸ hv_cm
        have hv_wb3 : v.toNat < st.wb.length := st.hwb ▸ hv_cm
        have hv_qs3 : v.toNat < st.qs.length := st.hqs ▸ hv_cm
        have hv_qp3 : v.toNat < st.qp.length := st.hqp ▸ hv_cm
        have hv_qn3 : v.toNat < st.qn.length := st.hqn ▸ hv_cm
        have hv_ps3 : v.toNat < st.ps.length := st.hps ▸ hv_cm
        have hv1 : (v + 1#64).toNat = v.toNat + 1 :=
          sr1a_add1 (Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hv_lt) hcv_lt64)
        c0_hfast_nobound
        exact hL3 (v + 1#64, ()) m
          (by dsimp only; rw [hv1]; exact Nat.sub_lt_sub_left hv_lt (Nat.lt_succ_self _))
          ⟨by rw [hv1]; exact Nat.succ_le_of_lt hv_lt,
            ⟨_, _, _, _, _, _, _, _, _, _, _, _,
              by rw [List.length_set]; exact st.hfl, by rw [List.length_set]; exact st.hlv,
              by rw [List.length_set]; exact st.hrs, by rw [List.length_set]; exact st.hqp,
              by rw [List.length_set]; exact st.hqn, by rw [List.length_set]; exact st.hqs,
              by rw [List.length_set]; exact st.hps, by rw [List.length_set]; exact st.hph,
              by rw [List.length_set]; exact st.hpt, by rw [List.length_set]; exact st.hpb,
              by rw [List.length_set]; exact st.hwb, by rw [List.length_set]; exact st.hsc⟩, hm⟩
      · have hft0 : 0 < s.core.frame_trail.length := by rw [hft_len]; exact Nat.zero_lt_succ _
        have hfd0 : 0 < s.core.frame_dec.length := by rw [hfd_len]; exact Nat.zero_lt_succ _
        clear hL3 J3 hm2 hinv_ok hws2_len hncv_lt64 hfl_len hlv_len hrs_len hph_len hpt_len
          hpb_len hwb_len hsc_len hqs_len hqp_len hqn_len hps_len hmax_lt hcv2_lt64 hcv_lt64 hv_len
        have hc_mv_lt : c.mv < 2 ^ 64 := Nat.lt_trans c.hmv (by unfold dimacsBound; decide)
        have hmax_lt64 : c.max_vars < 2 ^ 64 := Nat.lt_trans c.hmaxv (by unfold dimacsBound; decide)
        have hmv_lt_max : ncv.toNat ≤ c.max_vars := Nat.le_trans hncv_le (hold ▸ hcv_le)
        have hncv_bv : ncv = BitVec.ofNat 64 ncv.toNat := (@bv_ofNat_toNat_eq 64 ncv).symm
        have hsub_bv : BitVec.ofNat 64 c.max_vars - ncv =
            BitVec.ofNat 64 (c.max_vars - ncv.toNat) :=
          (congrArg (BitVec.ofNat 64 c.max_vars - ·) hncv_bv).trans
            (bv_sub_ofNat hmv_lt_max hmax_lt64)
        let sc_final : FullScratch :=
          { s.scratch with
            phases := st.ph, phases_target := st.pt, phases_best := st.pb, walk_best := st.wb,
            score := st.sc, q_stamp := st.qs, q_prev := st.qp, q_next := st.qn, pos := st.ps,
            target_assigned := tgt_asg, best_assigned := bst_asg }
        let s_final : FullState :=
          { core := { s.core with
              vals := vals1, flags := st.fl, lvl := st.lvl, rsns := st.rsns,
              frame_trail := s.core.frame_trail.set 0 0#32,
              frame_dec := s.core.frame_dec.set 0 0xFFFFFFFF#32,
              trail_end := 0, propagated := 0, cur_level := 0,
              unflushed := 0#64, confl_ref := 0xFFFFFFFF#64, confl_type := 0#64,
              cur_vars := ncv.toNat, unassigned := ncv }
            scratch := sc_final }
        c0_hsteps_nogrp
        refine wp_join_group
          (fun () mJ => ∃ c' : FullCfg, FullCfgCompat c c' ∧ c'.mv ≤ ncv.toNat ∧
            (FullMem c' s_final ⋆ R) mJ)
          (fun _ ⟨⟩ mJ ⟨c', hcompat', hcv_ge', hmJ⟩ => by
            c0_hsteps
            exact hQ c' vals1 st.fl st.lvl st.rsns 0#32 0xFFFFFFFF#32 sc_final mJ hcompat'
              (sr1a_cv_lengths hlen hcompat' hcv_ge' hmv_lt_max hvl1 st.hfl st.hlv st.hrs
                st.hph st.hpt st.hpb st.hwb st.hsc st.hqs st.hqp st.hqn st.hps)
              rfl (fun l _ hl => hz1 l hl) ⟨rfl, rfl⟩ rfl rfl hmJ)
          (fun Jmv hJmv => ?_)
        c0_hsplit
        · have hlt_mv : ncv.toNat < c.mv := by
            rw [Nat.mod_eq_of_lt hc_mv_lt] at hc; exact hc
          let c' := fullCfgShrinkMv c ncv.toNat (Nat.le_of_lt hlt_mv)
          refine wp_store_sep (full_store_mv_mid ncv hm) ?_
          intro m4 hm4; c0_hsteps_nogrp
          refine wp_load_of (full_load_max_vars_mid hm4) ?_
          have hm4' : (FullMemShrinkMid c (BitVec.ofNat 64 ncv.toNat) _ ⋆ R) m4 :=
            (show ∀ {x : BitVec 64}, ncv = x →
              (FullMemShrinkMid c x _ ⋆ R) m4 from fun h => h ▸ hm4) hncv_bv
          c0_hsteps_nogrp
          refine wp_store_sep (by
            rw [hsub_bv]; exact full_store_bva_mid (Nat.le_of_lt hlt_mv) hm4') ?_
          intro m5 hm5; c0_hsteps
          exact hJmv () m5 ⟨c', FullCfgCompat.shrinkMv c ncv.toNat (Nat.le_of_lt hlt_mv),
            Nat.le_refl _, compactMem_cast hm5 (by
              dsimp only [s_final, sc_final]; simp only [← hncv_bv]; rfl)⟩
        · have hge_mv : c.mv ≤ ncv.toNat := by
            rw [Nat.mod_eq_of_lt hc_mv_lt] at hc; omega
          c0_hsteps
          exact hJmv () m ⟨c, FullCfgCompat.refl c, hge_mv,
            compactMem_cast hm (by dsimp only [s_final, sc_final]; rfl)⟩

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S3
