/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S4EVSIDSReorder
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S4EVSIDSReorderProof0
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S4ReorderProof0
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S4ReorderMemProof
public import LeanQbe.T.Examples.Kissat.FullM4TernaryProof
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 13 S4-A Proofs — `full_reorder_queue_m7` Part 1 (P2–P4 + Main)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S4

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM4Ternary
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.FullFidelityStep13S4.S13ReorderTactics
open Kraken.Bedrock2.Test

private theorem s13_reorder_phase2_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    {c : FullCfg} {s s6 : FullState} {R : Mem 64 → Prop} {wl6 wr6 : S13Arr64 c.max_vars}
    {n : BitVec 64} {m6 : Mem 64}
    (hlen : s.LengthsOk c) (hQ' : ∀ r m', S13RPostOk c s R m' → Q r m')
    (hcv_le : s.core.cur_vars ≤ c.max_vars) (hcv_30 : s.core.cur_vars < 2 ^ 30)
    (hn_cv : n.toNat ≤ s.core.cur_vars) (hn_29 : n.toNat < 2 ^ 30)
    (hs6_eq : S13RWsortEq s s6) (hws6_len : s6.scratch.wsort.length = s.scratch.wsort.length)
    (hwb6 : S13WsortBounded s6.scratch.wsort n.toNat s.core.cur_vars)
    (hm6 : (S13ReorderMem c s6 wl6 wr6 ⋆ R) m6) :
    wp Γ Q X (s13rPhase2Expr c.hdr n (BitVec.ofNat 64 s.core.cur_vars) c.pVals c.pFlags
      c.pWsort c.pQPrev c.pQNext c.pQStamp c.pTarjanMark c.pTarjanReach) m6 := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_ws : s.core.cur_vars ≤ 2 * c.max_vars :=
    Nat.le_trans hcv_le (Nat.le_mul_of_pos_left _ (by decide))
  dsimp only [s13rPhase2Expr]
  obtain ⟨s7, hs7, hmF7⟩ := s13rel_of_reorder hlen hs6_eq hws6_len hwb6 hm6
  c0_hsteps_nogrp
  refine wp_while_state1 (fun i : BitVec 64 => i) (fun i => s.core.cur_vars - i.toNat)
    (fun i m7 => i.toNat ≤ s.core.cur_vars ∧ ∃ s7' : FullState,
      S13RRelinkOk c s s7' n.toNat ∧ (FullMem c s7' ⋆ R) m7)
    (fun J7 hJ7 => by c0_hsteps; exact hJ7 0#64 m6 ⟨Nat.zero_le _, s7, hs7, hmF7⟩)
    (fun J7 i m7 ⟨hi7, s7', hs7', hm7⟩ hJ7 => ?_)
  have h7len := s13rel_lengths hs7'
  c0_hsplit
  · have hi7_lt : i.toNat < s.core.cur_vars := s13r_bv64_lt_mod hcv_30 ‹_›
    have hi7_mv : i.toNat < c.max_vars := Nat.lt_of_lt_of_le hi7_lt hcv_le
    have hi7_qp : i.toNat < s7'.scratch.q_prev.length := h7len.2.2.2.1.symm ▸ hi7_mv
    have hi7_qn : i.toNat < s7'.scratch.q_next.length := h7len.2.2.2.2.1.symm ▸ hi7_mv
    have hi7_qs : i.toNat < s7'.scratch.q_stamp.length := h7len.2.2.2.2.2.symm ▸ hi7_mv
    have hi7p1 := s13r_add1 hcv_30 hi7_lt
    c0_hsteps
    exact hJ7 (i + 1#64) _ hi7p1.2.2
      ⟨hi7p1.2.1, _, s13rel_set_qstamp (s13rel_set_qnext (s13rel_set_qprev hs7' _ _) _ _) _ _,
       by assumption⟩
  · c0_hsplit
    · c0_hsteps
      exact hQ' (0#64, ()) _ (s13rel_to_post (s13rel_hdr5 hs7' _ _ _ _ _) (by assumption))
    · have hn_pos : 0 < n.toNat := s13r_pos_ne0 ‹_›
      have hn1_p := s13r_sub1 hn_29 (le_refl _) hn_pos
      refine wp_while_state (fun p : BitVec 64 × BitVec 64 × BitVec 64 × PUnit => p)
        (fun p => n.toNat - p.2.2.1.toNat)
        (fun p m8 => p.2.2.1.toNat ≤ n.toNat ∧ ∃ s8 : FullState,
          S13RRelinkOk c s s8 n.toNat ∧ (FullMem c s8 ⋆ R) m8)
        (fun J8 hJ8 => by
          c0_hsteps; exact hJ8 (4294967295#64, 0#64, 0#64, ()) m7 ⟨Nat.zero_le _, s7', hs7', hm7⟩)
        (fun J8 ⟨bidx, bstamp, i, ⟨⟩⟩ m8 ⟨hi, s8, hs8, hm8⟩ hJ8 => ?_)
      have h8len := s13rel_lengths hs8
      c0_hsplit
      · have hi_nat : i.toNat < n.toNat := ‹_›
        have hi_ws : i.toNat < s8.scratch.wsort.length :=
          h8len.2.2.1.symm ▸ Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hi_nat hn_cv) hcv_ws
        have hv_lt : (s8.scratch.wsort[i.toNat]'hi_ws).toNat < s.core.cur_vars :=
          s13rel_wsort_get hs8 hi_nat hi_ws
        have hv_mv : (BitVec.setWidth 64 (s8.scratch.wsort[i.toNat]'hi_ws)).toNat < c.max_vars :=
          s13r_zext64_32_lt (Nat.lt_of_lt_of_le hv_lt hcv_le)
        have hip1 := s13r_add1 hn_29 hi_nat
        c0_hsteps_nogrp
        refine wp_join_group (ts := [i32])
          (fun _ m8' => ∃ s8' : FullState, S13RRelinkOk c s s8' n.toNat ∧ (FullMem c s8' ⋆ R) m8')
          (fun _ _ m8' ⟨s8', hs8', hm8'⟩ => ?_)
          (fun Jp hJp => by
            c0_hsplit
            · have hi_pos : 0 < i.toNat := ‹_›
              have hi1_p := s13r_sub1 hn_29 (Nat.le_of_lt hi_nat) hi_pos
              have hi1_ws : (i - 1#64).toNat < s8.scratch.wsort.length :=
                h8len.2.2.1.symm ▸ Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hi1_p.2.2.2 hn_cv) hcv_ws
              c0_hsteps; exact hJp (_, ()) m8 ⟨s8, hs8, hm8⟩
            · c0_hsteps; exact hJp (_, ()) m8 ⟨s8, hs8, hm8⟩)
        have h8' := s13rel_lengths hs8'
        have hv_qp : (BitVec.setWidth 64 (s8.scratch.wsort[i.toNat]'hi_ws)).toNat <
            s8'.scratch.q_prev.length := h8'.2.2.2.1.symm ▸ hv_mv
        c0_hsteps_nogrp
        refine wp_join_group (ts := [i32])
          (fun _ m8'' =>
            ∃ s8'' : FullState, S13RRelinkOk c s s8'' n.toNat ∧ (FullMem c s8'' ⋆ R) m8'')
          (fun _ _ m8'' ⟨s8'', hs8'', hm8''⟩ => ?_)
          (fun Jn hJn => by
            c0_hsplit
            · have hi1_ws : (i + 1#64).toNat < s8'.scratch.wsort.length :=
                h8'.2.2.1.symm ▸ Nat.lt_of_lt_of_le
                  (Nat.lt_of_lt_of_le ‹(i + 1#64).toNat < n.toNat› hn_cv) hcv_ws
              c0_hsteps; exact hJn (_, ()) _ ⟨_, s13rel_set_qprev hs8' _ _, by assumption⟩
            · c0_hsteps; exact hJn (_, ()) _ ⟨_, s13rel_set_qprev hs8' _ _, by assumption⟩)
        have h8'' := s13rel_lengths hs8''
        have hv_qn : (BitVec.setWidth 64 (s8.scratch.wsort[i.toNat]'hi_ws)).toNat <
            s8''.scratch.q_next.length := h8''.2.2.2.2.1.symm ▸ hv_mv
        have hv_qs : (BitVec.setWidth 64 (s8.scratch.wsort[i.toNat]'hi_ws)).toNat <
            s8''.scratch.q_stamp.length := h8''.2.2.2.2.2.symm ▸ hv_mv
        c0_hsteps_nogrp
        refine wp_join_group (ts := [i64, i64])
          (fun _ m9 => ∃ s9 : FullState, S13RRelinkOk c s s9 n.toNat ∧ (FullMem c s9 ⋆ R) m9)
          (fun _ ⟨nbi, nbs, ⟨⟩⟩ m9 ⟨s9, hs9, hm9⟩ => by
            dsimp only [Blocks.get]; c0_hsteps
            exact hJ8 (nbi, nbs, i + 1#64, ()) m9 hip1.2.2 ⟨hip1.2.1, s9, hs9, hm9⟩)
          (fun Jb hJb => ?_)
        have hv_v0 : ((BitVec.setWidth 64 (s8.scratch.wsort[i.toNat]'hi_ws)) <<<
            (1 : BitVec 64)).toNat < s8''.core.vals.length :=
          h8''.2.1.symm ▸ s13r_shl1_mul2_bv_lt hv_mv hmx
        have hv_v0n : ((BitVec.setWidth 64 (s8.scratch.wsort[i.toNat]'hi_ws)) <<<
            (1 : Nat)).toNat < s8''.core.vals.length :=
          h8''.2.1.symm ▸ s13r_shl1_mul2_nat_lt hv_mv hmx
        c0_hsteps_nogrp; c0_hsplit
        · c0_hsteps; exact hJb (_, _, ()) _
            ⟨_, s13rel_set_qstamp (s13rel_set_qnext hs8'' _ _) _ _, by assumption⟩
        · c0_hsteps; exact hJb (_, _, ()) _
            ⟨_, s13rel_set_qstamp (s13rel_set_qnext hs8'' _ _) _ _, by assumption⟩
      · have hn_ws0 : 0 < s8.scratch.wsort.length :=
          h8len.2.2.1.symm ▸ Nat.lt_of_lt_of_le hn_pos (Nat.le_trans hn_cv hcv_ws)
        have hn_wsl : (n - 1#64).toNat < s8.scratch.wsort.length :=
          h8len.2.2.1.symm ▸ Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hn1_p.2.2.2 hn_cv) hcv_ws
        c0_hsteps_nogrp
        refine wp_join_group (ts := [i64, i64])
          (fun _ m9 => ∃ s9 : FullState, S13RRelinkOk c s s9 n.toNat ∧ (FullMem c s9 ⋆ R) m9)
          (fun _ _ m9 ⟨s9, hs9, hm9⟩ => by
            try dsimp only [Blocks.get]
            c0_hsteps
            exact hQ' (n, ()) _ (s13rel_to_post (s13rel_hdr2 hs9 _ _) (by assumption)))
          (fun Jf hJf => ?_)
        c0_hsplit
        · have hv_lt : (s8.scratch.wsort[(n - 1#64).toNat]'hn_wsl).toNat < s.core.cur_vars :=
            s13rel_wsort_get hs8 hn1_p.2.2.2 hn_wsl
          have hqlast_qs : (BitVec.setWidth 64
              (s8.scratch.wsort[(n - 1#64).toNat]'hn_wsl)).toNat <
              s8.scratch.q_stamp.length := h8len.2.2.2.2.2.symm ▸
                s13r_zext64_32_lt (Nat.lt_of_lt_of_le hv_lt hcv_le)
          c0_hsteps; exact hJf (_, _, ()) _ ⟨_, s13rel_hdr3 hs8 _ _ _, by assumption⟩
        · c0_hsteps; exact hJf (_, _, ()) _ ⟨_, s13rel_hdr3 hs8 _ _ _, by assumption⟩

/-! ## 5. P3: Focus-Mode Collect & Heapsort (`s13_reorder_focus_wp`) -/

private theorem s13_reorder_focus_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {wl4 wr4 : S13Arr64 c.max_vars}
    {m4 : Mem 64}
    (hSift : EnvSpec Γ "full_reorder_sift_fid" s13ReorderSiftSpec)
    (hlen : s.LengthsOk c) (hQ' : ∀ r m', S13RPostOk c s R m' → Q r m')
    (hcv_le : s.core.cur_vars ≤ c.max_vars) (hcv_29 : s.core.cur_vars < 2 ^ 29)
    (hcv_30 : s.core.cur_vars < 2 ^ 30) (hflags_len : s.core.flags.length = c.max_vars)
    (hm4 : (S13ReorderMem c s wl4 wr4 ⋆ R) m4) :
    wp Γ Q X (s13rFocusExpr c.hdr (BitVec.ofNat 64 s.core.cur_vars) c.pVals c.pFlags
      c.pWsort c.pQPrev c.pQNext c.pQStamp c.pTarjanMark c.pTarjanReach) m4 := by
  have hws_len := hlen.scratch_ok.wsort_len
  dsimp only [s13rFocusExpr]
  refine wp_while_state (fun p : BitVec 64 × BitVec 64 × PUnit => p)
    (fun p => s.core.cur_vars - p.2.1.toNat)
    (fun p m5 => p.2.1.toNat ≤ s.core.cur_vars ∧ p.1.toNat ≤ p.2.1.toNat ∧
      ∃ (s5 : FullState) (wl5 wr5 : S13Arr64 c.max_vars),
        S13RWsortEq s s5 ∧ s5.scratch.wsort.length = s.scratch.wsort.length ∧
        S13WsortBounded s5.scratch.wsort p.1.toNat s.core.cur_vars ∧
        (S13ReorderMem c s5 wl5 wr5 ⋆ R) m5)
    (fun J5 hJ5 => by
      c0_hsteps; exact hJ5 (0#64, 0#64, ()) m4 ⟨Nat.zero_le _, Nat.zero_le _, s, wl4, wr4,
        s13rw_refl s, rfl, fun _ h => absurd h (Nat.not_lt_zero _), hm4⟩)
    (fun J5 ⟨n, v, ⟨⟩⟩ m5 ⟨hv, hn_le, s5, wl5, wr5, hs5_eq, hws5_len, hwb5, hm5⟩ hJ5 => ?_)
  c0_hsplit
  · have hv_lt : v.toNat < s.core.cur_vars := s13r_bv64_lt_mod hcv_30 ‹_›
    have hv_fl : v.toNat < s5.core.flags.length :=
      (s13rw_flags hs5_eq).symm ▸ hflags_len.symm ▸ Nat.lt_of_lt_of_le hv_lt hcv_le
    have hvp1 := s13r_add1 hcv_30 hv_lt
    have hn_lt : n.toNat < s.core.cur_vars := Nat.lt_of_le_of_lt hn_le hv_lt
    have hnp1 := s13r_add1 hcv_30 hn_lt
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64])
      (fun n' m5' => n'.1.toNat ≤ v.toNat + 1 ∧ ∃ s5' : FullState,
        S13RWsortEq s s5' ∧ s5'.scratch.wsort.length = s.scratch.wsort.length ∧
        S13WsortBounded s5'.scratch.wsort n'.1.toNat s.core.cur_vars ∧
        (S13ReorderMem c s5' wl5 wr5 ⋆ R) m5')
      (fun _ ⟨n', ⟨⟩⟩ m5' ⟨hn', s5', hs5', hlen5', hwb5', hm5'⟩ => by
        dsimp only [Blocks.get]; c0_hsteps
        exact hJ5 (n', v + 1#64, ()) m5' hvp1.2.2
          ⟨hvp1.2.1, hvp1.1 ▸ hn', s5', wl5, wr5, hs5', hlen5', hwb5', hm5'⟩)
      (fun Jc hJc => ?_)
    c0_hsplit
    · have hn_ws : n.toNat < s5.scratch.wsort.length :=
        hws5_len.symm ▸ hws_len.symm ▸ Nat.lt_of_lt_of_le hn_lt
          (Nat.le_trans hcv_le (Nat.le_mul_of_pos_left _ (by decide)))
      have hv_cv : (BitVec.setWidth 32 v).toNat < s.core.cur_vars := by
        have : v.toNat < 2 ^ 32 := lt_trans hv_lt (lt_trans hcv_29 (by decide))
        have hz : (BitVec.setWidth 32 v).toNat = v.toNat := by bv_omega
        omega
      c0_hsteps
      exact hJc (n + 1#64, ()) _
        ⟨Nat.le_trans (Nat.le_of_eq hnp1.1) (Nat.succ_le_succ hn_le),
         { s5 with scratch :=
             { s5.scratch with wsort := s5.scratch.wsort.set n.toNat (BitVec.setWidth 32 v) } },
         s13rw_set hs5_eq _, by simp [hws5_len],
         hnp1.1 ▸ s13wb_push hwb5 hn_ws hv_cv, by assumption⟩
    · c0_hsteps; exact hJc (n, ()) m5
        ⟨Nat.le_trans hn_le (Nat.le_succ _), s5, hs5_eq, hws5_len, hwb5, hm5⟩
  · have hn_cv : n.toNat ≤ s.core.cur_vars := Nat.le_trans hn_le hv
    have hn_29 : n.toNat < 2 ^ 30 := Nat.lt_of_le_of_lt hn_cv (lt_trans hcv_29 (by decide))
    have hcv_ws : s.core.cur_vars ≤ 2 * c.max_vars :=
      Nat.le_trans hcv_le (Nat.le_mul_of_pos_left _ (by decide))
    refine wp_join_group (ts := [])
      (fun _ m6 => ∃ (s6 : FullState) (wl6 wr6 : S13Arr64 c.max_vars),
        S13RWsortEq s s6 ∧ s6.scratch.wsort.length = s.scratch.wsort.length ∧
        S13WsortBounded s6.scratch.wsort n.toNat s.core.cur_vars ∧
        (S13ReorderMem c s6 wl6 wr6 ⋆ R) m6) ?_ ?_
    · rintro _ _ m6 ⟨s6, wl6, wr6, hs6_eq, hws6_len, hwb6, hm6⟩
      dsimp only [Blocks.get]
      exact s13_reorder_phase2_wp hlen hQ' hcv_le hcv_30 hn_cv hn_29 hs6_eq hws6_len hwb6 hm6
    · intro J6 hJ6; c0_hsplit
      · have hn_pos : 0 < n.toNat := Nat.lt_trans Nat.zero_lt_one ‹_›
        c0_hsteps_nogrp
        refine wp_while_state1 (fun i : BitVec 64 => i) (fun i => i.toNat)
          (fun i m6 => i.toNat ≤ n.toNat ∧ ∃ (s6 : FullState) (wl6 wr6 : S13Arr64 c.max_vars),
            S13RWsortEq s s6 ∧ s6.scratch.wsort.length = s.scratch.wsort.length ∧
            S13WsortBounded s6.scratch.wsort n.toNat s.core.cur_vars ∧
            (S13ReorderMem c s6 wl6 wr6 ⋆ R) m6)
          (fun J_bld hJ_bld => by
            c0_hsteps; exact hJ_bld (n >>> 1#64) m5 ⟨s13r_ushr1_le (le_refl _),
              s5, wl5, wr5, hs5_eq, hws5_len, hwb5, hm5⟩)
          (fun J_bld i m6 ⟨hi, s6, wl6, wr6, hs6_eq, hws6_len, hwb6, hm6⟩ hJ_bld => ?_)
        c0_hsplit
        · have hip := s13r_sub1 hn_29 hi ‹_›
          c0_hsteps_nogrp; apply s13r_call_spec hSift
          refine ⟨c, s6, wl6, wr6, R, rfl, s13rw_lengthsOk hlen hs6_eq hws6_len,
            (by change S13WsortBounded s6.scratch.wsort n.toNat s6.core.cur_vars
                rw [s13rw_curVars hs6_eq]; exact hwb6),
            hm6, fun ws' m6' hwl' hwb' _ hm6' => ?_⟩
          c0_hsteps
          exact hJ_bld (i - 1#64) m6' hip.2.1
            ⟨hip.2.2.1, { s6 with scratch := { s6.scratch with wsort := ws' } },
             wl6, wr6, s13rw_set hs6_eq ws', hwl'.trans hws6_len,
             (by change S13WsortBounded ws' n.toNat s.core.cur_vars
                 rw [← s13rw_curVars hs6_eq]; exact hwb'), hm6'⟩
        · refine wp_while_state1 (fun e : BitVec 64 => e) (fun e => e.toNat)
            (fun e m7 => e.toNat ≤ n.toNat ∧ ∃ (s7 : FullState) (wl7 wr7 : S13Arr64 c.max_vars),
              S13RWsortEq s s7 ∧ s7.scratch.wsort.length = s.scratch.wsort.length ∧
              S13WsortBounded s7.scratch.wsort n.toNat s.core.cur_vars ∧
              (S13ReorderMem c s7 wl7 wr7 ⋆ R) m7)
            (fun J_pop hJ_pop => by
              c0_hsteps; exact hJ_pop n m6 ⟨le_refl _, s6, wl6, wr6, hs6_eq, hws6_len, hwb6, hm6⟩)
            (fun J_pop e m7 ⟨he, s7, wl7, wr7, hs7_eq, hws7_len, hwb7, hm7⟩ hJ_pop => ?_)
          c0_hsplit
          · have he_pos : 0 < e.toNat := Nat.lt_trans Nat.zero_lt_one ‹_›
            have hep := s13r_sub1 hn_29 he he_pos
            have he1_n : (e - 1#64).toNat < n.toNat := Nat.lt_of_lt_of_le hep.2.1 he
            have h0_ws : 0 < s7.scratch.wsort.length :=
              hws7_len.symm ▸ hws_len.symm ▸ Nat.lt_of_lt_of_le hn_pos (Nat.le_trans hn_cv hcv_ws)
            have he_ws : (e - 1#64).toNat < s7.scratch.wsort.length :=
              hws7_len.symm ▸ hws_len.symm ▸
                Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le he1_n hn_cv) hcv_ws
            have hv0_lt : (s7.scratch.wsort[0]'h0_ws).toNat < s.core.cur_vars :=
              s13wb_get hwb7 hn_pos h0_ws
            have hve_lt : (s7.scratch.wsort[(e - 1#64).toNat]'he_ws).toNat < s.core.cur_vars :=
              s13wb_get hwb7 he1_n he_ws
            have he_ws' : (e - 1#64).toNat <
                (s7.scratch.wsort.set 0 (s7.scratch.wsort[(e - 1#64).toNat]'he_ws)).length := by
              simpa using he_ws
            c0_hsteps_nogrp
            let ws_sw := (s7.scratch.wsort.set 0 (s7.scratch.wsort[(e - 1#64).toNat]'he_ws)).set
              (e - 1#64).toNat (s7.scratch.wsort[0]'h0_ws)
            have hwb_sw : S13WsortBounded ws_sw n.toNat s.core.cur_vars :=
              s13wb_swap hwb7 hve_lt hv0_lt
            apply s13r_call_spec hSift
            refine ⟨c, { s7 with scratch := { s7.scratch with wsort := ws_sw } },
              wl7, wr7, R, rfl,
              s13rw_lengthsOk hlen (s13rw_set hs7_eq ws_sw) (by simpa [ws_sw] using hws7_len),
              (by change S13WsortBounded ws_sw (e - 1#64).toNat s7.core.cur_vars
                  rw [s13rw_curVars hs7_eq]
                  exact s13wb_shrink hwb_sw (Nat.le_of_lt he1_n)),
              by assumption, fun ws' m7' hwl' hwb' hpres' hm7' => ?_⟩
            c0_hsteps
            exact hJ_pop (e - 1#64) m7' hep.2.1
              ⟨Nat.le_of_lt he1_n, { s7 with scratch := { s7.scratch with wsort := ws' } },
               wl7, wr7, s13rw_set hs7_eq ws',
               (hwl'.trans (by simp only [ws_sw, List.length_set])).trans hws7_len,
               s13wb_lift hwb_sw
                 (by change S13WsortBounded ws' (e - 1#64).toNat s.core.cur_vars
                     rw [← s13rw_curVars hs7_eq]; exact hwb')
                 hpres', hm7'⟩
          · c0_hsteps; exact hJ6 () m7 ⟨s7, wl7, wr7, hs7_eq, hws7_len, hwb7, hm7⟩
      · c0_hsteps; exact hJ6 () m5 ⟨s5, wl5, wr5, hs5_eq, hws5_len, hwb5, hm5⟩

/-! ## 6. P4: Binary Watches, Fold Loop & Mode Dispatch (`s13_reorder_loop34_wp`) -/

private theorem s13_reorder_loop34_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {wl2 wr2 : S13Arr64 c.max_vars}
    {m2 : Mem 64}
    (hFadd : EnvSpec Γ "f64u_add" f64uPure2Spec)
    (hFmul : EnvSpec Γ "f64u_mul" f64uPure2Spec)
    (hRescale : EnvSpec Γ "full_rescale" fullRescaleSpec)
    (hHeapUp : EnvSpec Γ "full_heap_up" fullHeapUpSpec)
    (hSift : EnvSpec Γ "full_reorder_sift_fid" s13ReorderSiftSpec)
    (hlen : s.LengthsOk c) (hQ' : ∀ r m', S13RPostOk c s R m' → Q r m')
    (hcv_le : s.core.cur_vars ≤ c.max_vars) (hcv_29 : s.core.cur_vars < 2 ^ 29)
    (hcv_30 : s.core.cur_vars < 2 ^ 30) (h2cv_le : 2 * s.core.cur_vars ≤ 2 * c.max_vars)
    (h2cv_30 : 2 * s.core.cur_vars < 2 ^ 30) (hvals_2cv : 2 * s.core.cur_vars ≤ s.core.vals.length)
    (hflags_len : s.core.flags.length = c.max_vars) (hwlen_29 : s.core.wlen < 2 ^ 29)
    (hwlen_stk : s.core.wlen ≤ s.core.wstk.length) (hwvec_len : s.core.wvec.length = 4 * c.max_vars)
    (hm2 : (S13ReorderMem c s wl2 wr2 ⋆ R) m2) :
    wp Γ Q X (s13rLoop34Expr c.hdr (BitVec.ofNat 64 s.core.cur_vars)
      (BitVec.ofNat 64 s.core.cur_vars <<< 1#64) (BitVec.ofNat 64 s.core.wlen)
      c.pVals c.pFlags c.pWvec c.pWstk c.pWsort c.pQPrev c.pQNext c.pQStamp
      c.pTarjanMark c.pTarjanReach) m2 := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  conv => arg 4; whnf
  c0_hsteps_nogrp
  -- Loop 3: binary watches scan
  refine wp_while_state1 (fun lit : BitVec 64 => lit)
    (fun lit => 2 * s.core.cur_vars - lit.toNat)
    (fun lit m3 => lit.toNat ≤ 2 * s.core.cur_vars ∧
      ∃ wl3 wr3 : S13Arr64 c.max_vars, (S13ReorderMem c s wl3 wr3 ⋆ R) m3)
    (fun J3 hJ3 => by c0_hsteps; exact hJ3 0#64 m2 ⟨Nat.zero_le _, wl2, wr2, hm2⟩)
    (fun J3 lit m3 ⟨hlit, wl3, wr3, hm3⟩ hJ3 => ?_)
  c0_hsplit
  · have hlit_nat : lit.toNat < 2 * s.core.cur_vars := s13r_bv64_lt_two_mul_mod hcv_29 ‹_›
    have hlit_2mx : lit.toNat < 2 * c.max_vars := Nat.lt_of_lt_of_le hlit_nat h2cv_le
    have hlit_vals : lit.toNat < s.core.vals.length := Nat.lt_of_lt_of_le hlit_nat hvals_2cv
    have hlit_v1 : (lit >>> (1 : BitVec 64)).toNat < s.core.flags.length :=
      hflags_len.symm ▸ Nat.lt_of_lt_of_le (s13r_ushr1_bv_lt hlit_nat) hcv_le
    have hlit_v2 : (lit >>> (1 : Nat)).toNat < s.core.flags.length :=
      hflags_len.symm ▸ Nat.lt_of_lt_of_le (s13r_ushr1_nat_lt hlit_nat) hcv_le
    have hlit_mv1 : (lit >>> (1 : BitVec 64)).toNat < c.max_vars :=
      Nat.lt_of_lt_of_le (s13r_ushr1_bv_lt hlit_nat) hcv_le
    have hlit_mv2 : (lit >>> (1 : Nat)).toNat < c.max_vars :=
      Nat.lt_of_lt_of_le (s13r_ushr1_nat_lt hlit_nat) hcv_le
    have hlit_w0 : (lit <<< (1 : BitVec 64)).toNat < s.core.wvec.length :=
      hwvec_len.symm ▸ s13r_shl1_bv_lt hlit_2mx hmx
    have hlit_w0n : (lit <<< (1 : Nat)).toNat < s.core.wvec.length :=
      hwvec_len.symm ▸ s13r_shl1_nat_lt hlit_2mx hmx
    have hlit_w1 : ((lit <<< (1 : BitVec 64)) + 1#64).toNat < s.core.wvec.length :=
      hwvec_len.symm ▸ s13r_shl1_add1_bv_lt hlit_2mx hmx
    have hlit_w1n : ((lit <<< (1 : Nat)) + 1#64).toNat < s.core.wvec.length :=
      hwvec_len.symm ▸ s13r_shl1_add1_nat_lt hlit_2mx hmx
    have hlitp1 := s13r_add1 h2cv_30 hlit_nat
    c0_hsteps_nogrp
    refine wp_join_group (ts := [])
      (fun _ m3' => ∃ wl3' wr3' : S13Arr64 c.max_vars, (S13ReorderMem c s wl3' wr3' ⋆ R) m3')
      (fun _ _ m3' ⟨wl3', wr3', hm3'⟩ => by
        dsimp only [Blocks.get]; c0_hsteps
        exact hJ3 (lit + 1#64) m3' hlitp1.2.2 ⟨hlitp1.2.1, wl3', wr3', hm3'⟩)
      (fun J_next hJ_next => ?_)
    c0_hsplit
    · c0_hsplit
      · c0_hsteps_nogrp
        refine wp_join_group (ts := [])
          (fun _ m3' => ∃ wl3' wr3' : S13Arr64 c.max_vars, (S13ReorderMem c s wl3' wr3' ⋆ R) m3')
          (fun _ _ m3' hm3' => by dsimp only [Blocks.get]; c0_hsteps; exact hJ_next () m3' hm3')
          (fun J_next2 hJ_next2 => ?_)
        c0_hsplit
        · c0_hsplit
          · c0_hsplit
            · refine wp_join_group (ts := [i64])
                (fun _ m3' => ∃ wl3' wr3' : S13Arr64 c.max_vars,
                  (S13ReorderMem c s wl3' wr3' ⋆ R) m3')
                (fun _ _ m3' hm3' => by
                  dsimp only [Blocks.get]; c0_hsteps; exact hJ_next2 () m3' hm3')
                (fun J_aw hJ_aw => ?_)
              have hwe_le := (s13r_we_le_wlen hwlen_29 ‹_› ‹_›).2
              have hwe_29 : ((BitVec.setWidth 64 s.core.wvec[2 * lit.toNat % 2 ^ 64]) +
                  (BitVec.setWidth 64 s.core.wvec[(2 * lit.toNat + 1) % 2 ^ 64])).toNat <
                  2 ^ 30 := Nat.lt_of_le_of_lt hwe_le (lt_trans hwlen_29 (by decide))
              refine wp_while_state1 (fun wi : BitVec 64 => wi)
                (fun wi => ((BitVec.setWidth 64 s.core.wvec[2 * lit.toNat % 2 ^ 64]) +
                  (BitVec.setWidth 64 s.core.wvec[(2 * lit.toNat + 1) % 2 ^ 64])).toNat - wi.toNat)
                (fun _ m4 => ∃ wl4 wr4 : S13Arr64 c.max_vars, (S13ReorderMem c s wl4 wr4 ⋆ R) m4)
                (fun J_wi hJ_wi => by c0_hsteps; exact hJ_wi _ m3 ⟨wl3, wr3, hm3⟩)
                (fun J_wi wi m4 ⟨wl4, wr4, hm4⟩ hJ_wi => ?_)
              c0_hsplit
              · have hwi_we : wi.toNat < ((BitVec.setWidth 64 s.core.wvec[2 * lit.toNat % 2 ^ 64]) +
                    (BitVec.setWidth 64 s.core.wvec[(2 * lit.toNat + 1) % 2 ^ 64])).toNat := by
                  dsimp only [lift2, Arg.val] at *; exact ‹_›
                have hwi_stk : wi.toNat < s.core.wstk.length :=
                  Nat.lt_of_lt_of_le hwi_we (Nat.le_trans hwe_le hwlen_stk)
                c0_hsteps_nogrp; c0_hsplit
                · c0_hsteps
                  exact hJ_wi (wi + 2#64) m4 (s13r_add2_sub_lt hwe_29 hwi_we) ⟨wl4, wr4, hm4⟩
                · c0_hsteps; exact hJ_aw (wi, ()) m4 ⟨wl4, wr4, hm4⟩
                · refine wp_join_group (ts := [])
                    (fun _ m4' => ∃ wl4' wr4' : S13Arr64 c.max_vars,
                      (S13ReorderMem c s wl4' wr4' ⋆ R) m4')
                    (fun _ _ m4' ⟨wl4', wr4', hm4'⟩ => by
                      dsimp only [Blocks.get]; c0_hsteps
                      exact hJ_wi (wi + 1#64) m4' (s13r_add1 hwe_29 hwi_we).2.2 ⟨wl4', wr4', hm4'⟩)
                    (fun J_cont hJ_cont => ?_)
                  c0_hsplit
                  · c0_hsplit
                    · have hother_lt : (BitVec.setWidth 64
                          (s.core.wstk[wi.toNat]'hwi_stk &&& 2147483647#32)).toNat <
                          2 * s.core.cur_vars := s13r_lt_shl1_ofNat hcv_29 ‹_›
                      have hov_vals : (BitVec.setWidth 64
                          (s.core.wstk[wi.toNat]'hwi_stk &&& 2147483647#32)).toNat <
                          s.core.vals.length := Nat.lt_of_lt_of_le hother_lt hvals_2cv
                      have hov_fl1 : (BitVec.setWidth 64
                          ((s.core.wstk[wi.toNat]'hwi_stk &&& 2147483647#32) >>>
                            (1 : BitVec 32))).toNat < s.core.flags.length :=
                        hflags_len.symm ▸
                          Nat.lt_of_lt_of_le (s13r_zext32_bv32_ushr1_bv_lt hother_lt) hcv_le
                      have hov_fl2 : (BitVec.setWidth 64
                          ((s.core.wstk[wi.toNat]'hwi_stk &&& 2147483647#32) >>>
                            (1 : Nat))).toNat < s.core.flags.length :=
                        hflags_len.symm ▸
                          Nat.lt_of_lt_of_le (s13r_zext32_bv32_ushr1_lt hother_lt) hcv_le
                      have hov_mv1 : ((BitVec.setWidth 64
                          (s.core.wstk[wi.toNat]'hwi_stk &&& 2147483647#32)) >>>
                            (1 : BitVec 64)).toNat < c.max_vars :=
                        Nat.lt_of_lt_of_le (s13r_zext32_ushr1_lt hother_lt) hcv_le
                      have hov_mv2 : ((BitVec.setWidth 64
                          (s.core.wstk[wi.toNat]'hwi_stk &&& 2147483647#32)) >>>
                            (1 : Nat)).toNat < c.max_vars :=
                        Nat.lt_of_lt_of_le (s13r_zext32_ushr1_nat_lt hother_lt) hcv_le
                      c0_hsteps_nogrp
                      refine wp_join_group (ts := [])
                        (fun _ m4' => ∃ wl4' wr4' : S13Arr64 c.max_vars,
                          (S13ReorderMem c s wl4' wr4' ⋆ R) m4')
                        (fun _ _ m4' hm4' => by
                          dsimp only [Blocks.get]; c0_hsteps; exact hJ_cont () m4' hm4')
                        (fun J_nw hJ_nw => ?_)
                      c0_hsteps_nogrp; c0_hsplit
                      · refine wp_join_group (ts := [])
                          (fun _ m4' => ∃ wl4' wr4' : S13Arr64 c.max_vars,
                            (S13ReorderMem c s wl4' wr4' ⋆ R) m4')
                          (fun _ _ m4' ⟨wl4', wr4', hm4'⟩ => by
                            dsimp only [Blocks.get]
                            refine wp_join_group (ts := [])
                              (fun _ m4'' => ∃ wl4'' wr4'' : S13Arr64 c.max_vars,
                                (S13ReorderMem c s wl4'' wr4'' ⋆ R) m4'')
                              (fun _ _ m4'' hm4'' => by c0_hsteps; exact hJ_nw () m4'' hm4'')
                              (fun J_nw' hJ_nw' => by
                                c0_hsplit
                                · c0_hsteps_nogrp; c0_call hFadd
                                  refine f64uPure2Spec_of fun _ => ?_
                                  c0_hsteps; exact hJ_nw' () _ ⟨_, _, by assumption⟩
                                · c0_hsteps_nogrp; c0_call hFadd
                                  refine f64uPure2Spec_of fun _ => ?_
                                  c0_hsteps; exact hJ_nw' () _ ⟨_, _, by assumption⟩))
                          (fun J_lit2 hJ_lit2 => by
                            c0_hsplit
                            · c0_hsteps_nogrp; c0_call hFadd; refine f64uPure2Spec_of fun _ => ?_
                              c0_hsteps; exact hJ_lit2 () _ ⟨_, _, by assumption⟩
                            · c0_hsteps_nogrp; c0_call hFadd; refine f64uPure2Spec_of fun _ => ?_
                              c0_hsteps; exact hJ_lit2 () _ ⟨_, _, by assumption⟩)
                      · c0_hsteps; exact hJ_nw () m4 ⟨wl4, wr4, hm4⟩
                      · c0_hsteps; exact hJ_nw () m4 ⟨wl4, wr4, hm4⟩
                    · c0_hsteps; exact hJ_cont () m4 ⟨wl4, wr4, hm4⟩
                  · c0_hsteps; exact hJ_cont () m4 ⟨wl4, wr4, hm4⟩
              · c0_hsteps; exact hJ_aw (wi, ()) m4 ⟨wl4, wr4, hm4⟩
            · c0_hsteps; exact hJ_next2 () m3 ⟨wl3, wr3, hm3⟩
          · c0_hsteps; exact hJ_next2 () m3 ⟨wl3, wr3, hm3⟩
        · c0_hsteps; exact hJ_next2 () m3 ⟨wl3, wr3, hm3⟩
      · c0_hsteps; exact hJ_next () m3 ⟨wl3, wr3, hm3⟩
    · c0_hsteps; exact hJ_next () m3 ⟨wl3, wr3, hm3⟩
  · -- Loop 4: fold `wl[fv]` with `f64u_mul` + `f64u_add`, then dispatch on `h->stable != 0`
    c0_hsteps_nogrp
    refine wp_while_state1 (fun fv : BitVec 64 => fv) (fun fv => s.core.cur_vars - fv.toNat)
      (fun fv m4 => fv.toNat ≤ s.core.cur_vars ∧
        ∃ wl4 wr4 : S13Arr64 c.max_vars, (S13ReorderMem c s wl4 wr4 ⋆ R) m4)
      (fun J4 hJ4 => by c0_hsteps; exact hJ4 0#64 m3 ⟨Nat.zero_le _, wl3, wr3, hm3⟩)
      (fun J4 fv m4 ⟨hfv, wl4, wr4, hm4⟩ hJ4 => ?_)
    c0_hsplit
    · have hfv_lt : fv.toNat < s.core.cur_vars := s13r_bv64_lt_mod hcv_30 ‹_›
      have hfv_mv : fv.toNat < c.max_vars := Nat.lt_of_lt_of_le hfv_lt hcv_le
      have hfvp1 := s13r_add1 hcv_30 hfv_lt
      c0_hsteps_nogrp
      refine wp_join_group (ts := [i64]) (fun _ m' => m' = m4)
        (fun _ _ m4' hm_eq => by
          subst m4'; dsimp only [Blocks.get]; c0_hsteps
          exact hJ4 (fv + 1#64) _ hfvp1.2.2 ⟨hfvp1.2.1, _, _, by assumption⟩)
        (fun Jf hJf => by
          c0_hsplit
          · c0_hsteps_nogrp; c0_call hFmul; refine f64uPure2Spec_of fun _ => ?_
            c0_hsteps_nogrp; c0_call hFadd; refine f64uPure2Spec_of fun _ => ?_
            c0_hsteps; exact hJf _ m4 rfl
          · c0_hsteps_nogrp; c0_call hFmul; refine f64uPure2Spec_of fun _ => ?_
            c0_hsteps_nogrp; c0_call hFadd; refine f64uPure2Spec_of fun _ => ?_
            c0_hsteps; exact hJf _ m4 rfl)
    · c0_hsteps_nogrp; c0_hsplit
      · exact s13_reorder_stable_wp hFadd hRescale hHeapUp hlen hQ' hcv_le hcv_29 hcv_30 hm4
      · exact s13_reorder_focus_wp hSift hlen hQ' hcv_le hcv_29 hcv_30 hflags_len hm4

/-! ## 7. Main Theorem: `full_reorder_queue_m7_step13_wp` -/

/-- Step-13 `full_reorder_queue_m7` satisfies canonical `FullM4Ternary.fullReorderQueueSpec`. -/
theorem full_reorder_queue_m7_step13_wp (Γ : Env)
    (hFadd : EnvSpec Γ "f64u_add" f64uPure2Spec)
    (hFmul : EnvSpec Γ "f64u_mul" f64uPure2Spec)
    (hArenaNext : EnvSpec Γ "full_arena_next" fullArenaNextSpec)
    (hRescale : EnvSpec Γ "full_rescale" fullRescaleSpec)
    (hHeapUp : EnvSpec Γ "full_heap_up" fullHeapUpSpec)
    (hSift : EnvSpec Γ "full_reorder_sift_fid" s13ReorderSiftSpec) :
    ∀ a m Q X, fullReorderQueueSpec a m Q X →
      Func.wp Γ full_reorder_queue_m7_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hmF, hQ⟩
  have hQ' : ∀ r m', S13RPostOk c s R m' → Q r m' := by
    intro r m' ⟨s', hcore, hlen', hext, hm'⟩; exact hQ r s' m' hcore hlen' hext hm'
  clear hQ
  have hmx := c.hmaxv; have har := c.harena; have hwc := c.hwcap; unfold dimacsBound at hmx har hwc
  have hcv_le := hlen.core_ok.cur_vars_le
  have hcv_29 : s.core.cur_vars < 2 ^ 29 := by omega
  have hcv_30 : s.core.cur_vars < 2 ^ 30 := lt_trans hcv_29 (by decide)
  have h2cv_le : 2 * s.core.cur_vars ≤ 2 * c.max_vars := Nat.mul_le_mul_left 2 hcv_le
  have h2cv_30 : 2 * s.core.cur_vars < 2 ^ 30 := by omega
  have hvals_len := hlen.core_ok.vals_len
  have hvals_2cv : 2 * s.core.cur_vars ≤ s.core.vals.length := hvals_len ▸ h2cv_le
  have hflags_len := hlen.core_ok.flags_len
  have harena_le := hlen.core_ok.arena_len_le; have har_len := hlen.core_ok.arena_len_arr
  have har_29 : s.core.arena_len < 2 ^ 29 := by omega
  have har_le_arr : s.core.arena_len ≤ s.core.arena.length := by omega
  have hwlen_le := hlen.core_ok.wlen_le; have hwlen_29 : s.core.wlen < 2 ^ 29 := by omega
  have hwstk_len := hlen.core_ok.wstk_len_arr
  have hwlen_stk : s.core.wlen ≤ s.core.wstk.length := by omega
  have hwvec_len := hlen.core_ok.wvec_len
  obtain ⟨wl, wr, hmR⟩ := s13r_reorderMem_of_fullMem hlen hmF
  clear hmF
  unfold Func.wp full_reorder_queue_m7_body
  c0_hsteps_nogrp
  -- Loop 1: zero `wl[z]`, `wr[z]`
  refine wp_while_state1 (fun z : BitVec 64 => z) (fun z => s.core.cur_vars - z.toNat)
    (fun z m1 => z.toNat ≤ s.core.cur_vars ∧
      ∃ wl1 wr1 : S13Arr64 c.max_vars, (S13ReorderMem c s wl1 wr1 ⋆ R) m1)
    (fun J1 hJ1 => by c0_hsteps; exact hJ1 0#64 m ⟨Nat.zero_le _, wl, wr, hmR⟩)
    (fun J1 z m1 ⟨hz, wl1, wr1, hm1⟩ hJ1 => ?_)
  c0_hsplit
  · have hz_lt : z.toNat < s.core.cur_vars := s13r_bv64_lt_mod hcv_30 ‹_›
    have hz_mv : z.toNat < c.max_vars := Nat.lt_of_lt_of_le hz_lt hcv_le
    have hzp1 := s13r_add1 hcv_30 hz_lt
    c0_hsteps; exact hJ1 (z + 1#64) _ hzp1.2.2 ⟨hzp1.2.1, _, _, by assumption⟩
  · -- Loop 2: arena clause scan wrapped in `J_after2`
    refine wp_join_group (ts := [i64])
      (fun _ m2 => ∃ wl2 wr2 : S13Arr64 c.max_vars, (S13ReorderMem c s wl2 wr2 ⋆ R) m2) ?_ ?_
    · rintro _ _ m2 ⟨wl2, wr2, hm2⟩
      dsimp only [Blocks.get]
      exact s13_reorder_loop34_wp hFadd hFmul hRescale hHeapUp hSift hlen hQ' hcv_le hcv_29
        hcv_30 h2cv_le h2cv_30 hvals_2cv hflags_len hwlen_29 hwlen_stk hwvec_len hm2
    · intro J_after2 hJ_after2
      refine wp_while_state1 (fun p : BitVec 64 => p) (fun p => s.core.arena_len - p.toNat)
        (fun _ m2 => ∃ wl2 wr2 : S13Arr64 c.max_vars, (S13ReorderMem c s wl2 wr2 ⋆ R) m2)
        (fun J2 hJ2 => by c0_hsteps; exact hJ2 0#64 m1 ⟨wl1, wr1, hm1⟩)
        (fun J2 p m2 ⟨wl2, wr2, hm2⟩ hJ2 => ?_)
      c0_hsplit
      · c0_hsplit
        · c0_hsteps; exact hJ_after2 (p, ()) m2 ⟨wl2, wr2, hm2⟩
        · rcases s13r_off_bounds har_29 har_le_arr (by assumption) (by assumption) rfl with
              ⟨hoff3_le, hoff_29, hoff2_eq, hoff_lt, hoff2_lt⟩
          c0_hsteps_nogrp
          refine wp_join_group (ts := [])
            (fun _ m2' => ∃ wl2' wr2' : S13Arr64 c.max_vars, (S13ReorderMem c s wl2' wr2' ⋆ R) m2')
            (fun _ _ m2' ⟨wl2', wr2', hm2'⟩ => by
              dsimp only [Blocks.get]; c0_hsteps_nogrp
              obtain ⟨tmk, trc, htmk, htrc, hmF'⟩ := s13r_fullMem_of_reorderMem hm2'
              apply s13r_call_spec hArenaNext
              refine ⟨c, _, R, rfl, ?_, hmF', ?_⟩
              · exact ⟨hlen.core_ok, { hlen.scratch_ok with
                  tarjan_mark_len := htmk, tarjan_reach_len := htrc }⟩
              · c0_hsplit
                · c0_hsteps; exact hJ_after2 (p, ()) m2' ⟨wl2', wr2', hm2'⟩
                · c0_hsteps; refine hJ2 _ m2' ?_ ⟨wl2', wr2', hm2'⟩
                  first
                  | exact Nat.sub_lt_sub_left
                      (Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide)) hoff3_le)
                      (Nat.lt_of_not_le (by assumption))
                  | (clear hJ2 hJ_after2 hm2 hm2' hmF' hSift hArenaNext hRescale
                       hHeapUp hFadd hFmul hQ'
                     have hlt : p.toNat < s.core.arena_len :=
                       Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide)) hoff3_le
                     bv_omega))
            (fun J_skip hJ_skip => ?_)
          c0_hsplit
          · c0_hsplit
            · rcases s13r_sz_off3_le hoff3_le har_29 hoff2_lt hoff2_eq (by assumption) rfl rfl with
                ⟨hsz_le, hsz_29⟩
              c0_hsteps_nogrp
              refine wp_join_group (ts := [Ty.bool, i64, i64]) (fun _ m2' => m2' = m2)
                (fun _ ⟨sat, sz, _⟩ m2' hm_eq => by
                  subst m2'; dsimp only [Blocks.get]; c0_hsteps_nogrp
                  refine wp_join_group (ts := [i64, i64])
                    (fun _ m2'' => ∃ wl2'' wr2'' : S13Arr64 c.max_vars,
                      (S13ReorderMem c s wl2'' wr2'' ⋆ R) m2'')
                    (fun _ _ m2'' hm2'' => by c0_hsteps; exact hJ_skip () m2'' hm2'')
                    (fun J_cw hJ_cw => ?_)
                  c0_hsplit
                  · c0_hsteps; exact hJ_cw _ m2 ⟨wl2, wr2, hm2⟩
                  · c0_hsplit
                    · c0_hsteps_nogrp
                      refine wp_join_group (ts := [i64]) (fun _ mw => mw = m2)
                        (fun _ ⟨sz', _⟩ mw hmw => by
                          subst mw; dsimp only [Blocks.get]; c0_hsteps_nogrp
                          refine wp_while_state1 (fun ci : BitVec 64 => ci)
                            (fun ci => (BitVec.setWidth 64
                              (s.core.arena[(p + 2#64).toNat]'hoff2_lt)).toNat - ci.toNat)
                            (fun ci m2k => ci.toNat ≤ (BitVec.setWidth 64
                                (s.core.arena[(p + 2#64).toNat]'hoff2_lt)).toNat ∧
                              ∃ wl2k wr2k : S13Arr64 c.max_vars,
                                (S13ReorderMem c s wl2k wr2k ⋆ R) m2k)
                            (fun J_k hJ_k => by
                              c0_hsteps; exact hJ_k 0#64 m2 ⟨Nat.zero_le _, wl2, wr2, hm2⟩)
                            (fun J_k ci m2k ⟨hk, wl2k, wr2k, hm2k⟩ hJ_k => ?_)
                          c0_hsplit
                          · have hk_lt : ci.toNat < (BitVec.setWidth 64
                                (s.core.arena[(p + 2#64).toNat]'hoff2_lt)).toNat :=
                              s13r_arena_k_lt hoff2_eq hoff_29 hoff2_lt (by assumption) rfl
                            have hk_29 : ci.toNat < 2 ^ 29 := Nat.lt_trans hk_lt hsz_29
                            have hk3 := s13r_off3_add hoff_29 hk_29
                            have hk1 := s13r_add1 (lt_trans hsz_29 (by decide)) hk_lt
                            have hk_ar : ((p + 3#64) + ci).toNat < s.core.arena.length :=
                              hk3.1 ▸ Nat.lt_of_lt_of_le (Nat.add_lt_add_left hk_lt (p.toNat + 3))
                                (Nat.le_trans hsz_le har_le_arr)
                            c0_hsteps_nogrp
                            refine wp_join_group (ts := [])
                              (fun _ m2k' => ∃ wl2k' wr2k' : S13Arr64 c.max_vars,
                                (S13ReorderMem c s wl2k' wr2k' ⋆ R) m2k')
                              (fun _ _ m2k' hm2k' => by
                                dsimp only [Blocks.get]; c0_hsteps
                                exact hJ_k (ci + 1#64) m2k' hk1.2.2 ⟨hk1.2.1, hm2k'⟩)
                              (fun J_kl hJ_kl => ?_)
                            c0_hsplit
                            · have hlit_2cv : (BitVec.setWidth 64
                                  (s.core.arena[((p + 3#64) + ci).toNat]'hk_ar)).toNat <
                                  2 * s.core.cur_vars := by
                                refine s13r_arena_lit_2cv ?_ hcv_29 hk_ar _ (by assumption)
                                have h3b : (3 : BitVec 64).toNat = 3 := rfl
                                have hm3 : (3 : Nat) % 2 ^ 64 = 3 := by decide
                                rw [hk3.1, ← hk3.2.1]; simp only [h3b, hm3]
                              have hlit_2mx := Nat.lt_of_lt_of_le hlit_2cv h2cv_le
                              have hlit_mv3 : (BitVec.setWidth 64
                                  (s.core.arena[((p + 3#64) + ci).toNat]'hk_ar >>>
                                    (1 : Nat))).toNat < c.max_vars :=
                                s13r_zext32_bv32_ushr1_lt hlit_2mx
                              have hlit_mv4 : (BitVec.setWidth 64
                                  (s.core.arena[((p + 3#64) + ci).toNat]'hk_ar >>>
                                    (1 : BitVec 32))).toNat < c.max_vars :=
                                s13r_zext32_bv32_ushr1_bv_lt hlit_2mx
                              clear hJ2 hJ_after2 hJ_skip hJ_cw hJ_k hlit_2cv hlit_2mx hk1 hk3 hk_29
                              clear hk_lt hsz_le hsz_29 hoff3_le hoff_29 hoff2_eq hm2 hm1 hmR
                              c0_hsteps_nogrp
                              refine wp_join_group (ts := [])
                                (fun _ m' => ∃ wl' wr' : S13Arr64 c.max_vars,
                                  (S13ReorderMem c s wl' wr' ⋆ R) m')
                                (fun _ _ m' hm' => by
                                  try dsimp only [Blocks.get]
                                  c0_hsteps; exact hJ_kl () m' hm')
                                (fun Js hJs => by
                                  c0_hsplit
                                  · c0_hsteps_nogrp; c0_call hFadd
                                    refine f64uPure2Spec_of fun _ => ?_
                                    c0_hsteps; exact hJs () _ ⟨_, _, by assumption⟩
                                  · c0_hsteps_nogrp; c0_call hFadd
                                    refine f64uPure2Spec_of fun _ => ?_
                                    c0_hsteps; exact hJs () _ ⟨_, _, by assumption⟩)
                            · c0_hsteps; exact hJ_kl () m2k ⟨wl2k, wr2k, hm2k⟩
                          · c0_hsteps; exact hJ_cw _ m2k ⟨wl2k, wr2k, hm2k⟩)
                        (fun Jw hJw => by
                          c0_hsteps_nogrp; all_goals exact hJw (_, ()) m2 rfl)
                    · c0_hsteps; exact hJ_cw _ m2 ⟨wl2, wr2, hm2⟩)
                (fun J_su hJ_su => ?_)
              refine wp_while_state (fun q : BitVec 64 × BitVec 64 × PUnit => q)
                (fun q => (BitVec.setWidth 64
                  (s.core.arena[(p + 2#64).toNat]'hoff2_lt)).toNat - q.2.1.toNat)
                (fun q m_su => m_su = m2 ∧ q.2.1.toNat ≤ (BitVec.setWidth 64
                    (s.core.arena[(p + 2#64).toNat]'hoff2_lt)).toNat)
                (fun J_j hJ_j => by c0_hsteps; exact hJ_j (0#64, 0#64, ()) m2 ⟨rfl, Nat.zero_le _⟩)
                (fun J_j ⟨sz, ci, ⟨⟩⟩ m_su ⟨hm_eq, hj⟩ hJ_j => ?_)
              subst m_su; c0_hsplit
              · have hj_lt : ci.toNat < (BitVec.setWidth 64
                    (s.core.arena[(p + 2#64).toNat]'hoff2_lt)).toNat :=
                  s13r_arena_k_lt hoff2_eq hoff_29 hoff2_lt (by assumption) rfl
                have hj_29 : ci.toNat < 2 ^ 29 := Nat.lt_trans hj_lt hsz_29
                have hj3 := s13r_off3_add hoff_29 hj_29
                have hj1 := s13r_add1 (lt_trans hsz_29 (by decide)) hj_lt
                have hj_ar : ((p + 3#64) + ci).toNat < s.core.arena.length :=
                  hj3.1 ▸ Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj_lt (p.toNat + 3))
                    (Nat.le_trans hsz_le har_le_arr)
                c0_hsteps_nogrp
                refine wp_join_group (ts := [Ty.bool, i64]) (fun _ m_su' => m_su' = m2)
                  (fun _ ⟨sat, sz', _⟩ m_su' hm_eq' => by
                    subst m_su'; dsimp only [Blocks.get]; c0_hsteps
                    exact hJ_j (sz', ci + 1#64, ()) m2 hj1.2.2 ⟨rfl, hj1.2.1⟩)
                  (fun J_lit hJ_lit => ?_)
                c0_hsplit
                · have hj_2cv : (BitVec.setWidth 64
                      (s.core.arena[((p + 3#64) + ci).toNat]'hj_ar)).toNat <
                      2 * s.core.cur_vars := by
                    refine s13r_arena_lit_2cv ?_ hcv_29 hj_ar _ (by assumption)
                    have h3b : (3 : BitVec 64).toNat = 3 := rfl
                    have hm3 : (3 : Nat) % 2 ^ 64 = 3 := by decide
                    rw [hj3.1, ← hj3.2.1]; simp only [h3b, hm3]
                  have hj_val : (BitVec.setWidth 64
                      (s.core.arena[((p + 3#64) + ci).toNat]'hj_ar)).toNat < s.core.vals.length :=
                    hvals_len ▸ Nat.lt_of_lt_of_le hj_2cv h2cv_le
                  clear hJ2 hJ_after2 hJ_skip hm1 hmR hsz_le hsz_29 hoff3_le hoff_29 hoff2_eq
                  clear hj3 hj1 hj_2cv hj_lt hj_29 hSift hArenaNext hRescale hHeapUp hFadd hFmul hQ'
                  c0_hsteps_nogrp; c0_hsplit
                  · c0_hsteps; exact hJ_su (true, sz, ci, ()) m2 rfl
                  · c0_hsteps; all_goals exact hJ_lit (false, _, ()) m2 rfl
                · c0_hsteps; exact hJ_lit (false, sz, ()) m2 rfl
              · c0_hsteps; exact hJ_su (false, sz, ci, ()) m2 rfl
            · c0_hsteps; exact hJ_skip () m2 ⟨wl2, wr2, hm2⟩
          · c0_hsteps; exact hJ_skip () m2 ⟨wl2, wr2, hm2⟩
      · c0_hsteps; exact hJ_after2 (p, ()) m2 ⟨wl2, wr2, hm2⟩

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S4
