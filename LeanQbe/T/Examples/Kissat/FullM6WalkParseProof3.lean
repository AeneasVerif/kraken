module

public import LeanQbe.T.Examples.Kissat.FullM6WalkParseProof2
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat M6 Wave 2 (`RC-26b` + `RC-27`) `Func.wp` Proofs — Part 3 (`FullM6WalkParseProof3`)

Proves UNSAT-only parametric `Func.wp` contracts (`XPost := False`, `0` SAT proofs) for:
1. `m6WalkPickSpec` and `full_walk_pick_m6_wp`.
2. `m6WalkFlipSpec` and `full_walk_flip_m6_wp`.
3. `full_walk_core_m6_wp` against exact canonical `Full.fullWalkSpec`.
4. `m6WalkSpec` (`fullWarmupSpec`) and `full_walk_m6_wp` (`full_warmup` + `full_walk_core_m6`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM6WalkParse

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

/-! ## 1. Specs & Helpers -/

/-- Contract for `full_walk_pick_m6(h, ci, ncl, max_cl, occ_cap, inv_q16) -> lit`. -/
def m6WalkPickSpec : Spec [i64, i64, i64, i64, i64, i64] [i32] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, ci, ncl, max_cl, occ_cap, _inv, ()) s =>
      h = c.hdr ∧ (∃ F0, FullCoreInv c F0 s) ∧
      ci.toNat < ncl.toNat ∧ ncl.toNat ≤ max_cl.toNat ∧
      5 * max_cl.toNat + occ_cap.toNat ≤ c.scratch_cap ∧
      FullWalkEntriesOk s ncl.toNat)
    (fun _ _ (r, ()) s s' =>
      FullExtScratchPres s s' ∧
      s'.scratch.scratch_buf = s.scratch.scratch_buf ∧
      (r = 0xFFFFFFFF#32 ∨ r.toNat < 2 * s.core.cur_vars))

/-- Contract for `full_walk_flip_m6(h, lit, ncl, max_cl, occ_cap, ulen) -> ulen'`. -/
def m6WalkFlipSpec : Spec [i64, i32, i64, i64, i64, i64] [i64] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _lit, ncl, max_cl, occ_cap, ulen, ()) _ =>
      h = c.hdr ∧ ncl.toNat ≤ max_cl.toNat ∧ ulen.toNat ≤ ncl.toNat ∧
      5 * max_cl.toNat + occ_cap.toNat ≤ c.scratch_cap)
    (fun _ (_, _, ncl, _, _, _, ()) (r, ()) s s' =>
      FullExtScratchPres s s' ∧ r.toNat ≤ ncl.toNat ∧
      (∀ i < 2 * ncl.toNat, s'.scratch.scratch_buf[i]? = s.scratch.scratch_buf[i]?))

/-- Top-level `full_walk_m6` contract (`full_warmup` at level 0 sparse + `full_walk_core_m6`),
matching exact canonical `Full.fullWarmupSpec`. -/
abbrev m6WalkSpec : Spec [i64] [] := fullWarmupSpec

private def M6WsortLitsOk (cv : Nat) (ws : List (BitVec 32)) (m : Nat) : Prop :=
  ∀ idx < m, (ws[2 * idx]?.getD 0#32).toNat < 2 * cv

private theorem m6_wsortLitsOk_push {cv m : Nat} {ws : List (BitVec 32)} {lit sc : BitVec 32}
    (hok : M6WsortLitsOk cv ws m) (hlit : lit.toNat < 2 * cv) (hlen : 2 * m + 1 < ws.length) :
    M6WsortLitsOk cv ((ws.set (2 * m) lit).set (2 * m + 1) sc) (m + 1) := by
  intro idx hidx
  rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hidx) with hlt | rfl
  · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    exact hok idx hlt
  · rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega), Option.getD_some]
    exact hlit

private theorem m6_extPres_trans {s1 s2 s3 : FullState}
    (h12 : FullExtScratchPres s1 s2) (h23 : FullExtScratchPres s2 s3) :
    FullExtScratchPres s1 s3 :=
  ⟨h23.1.trans h12.1, h23.2.trans h12.2⟩

private theorem m6_extPres_of_rng {s1 s2 : FullState}
    (h : s2.scratch = { s1.scratch with rng_state := s2.scratch.rng_state }) :
    FullExtScratchPres s1 s2 := by
  have h1 := congrArg FullScratch.last_learned h
  have h2 := congrArg FullScratch.extend_len h
  exact ⟨h1, h2⟩

private theorem m6_len_set_ws {c : FullCfg} {s : FullState} {i : Nat} {v : BitVec 32}
    (hs : s.LengthsOk c) :
    ({ s with scratch := { s.scratch with wsort := s.scratch.wsort.set i v } }).LengthsOk c :=
  hs.with_scratch { hs.scratch_ok with
    wsort_len := by rw [List.length_set]; exact hs.scratch_ok.wsort_len }

private theorem m6_core_set_ws {s0 s : FullState} {i : Nat} {v : BitVec 32}
    (hc : PreservesCoreSlice FullState.core s0 s) :
    PreservesCoreSlice FullState.core s0
      { s with scratch := { s.scratch with wsort := s.scratch.wsort.set i v } } := hc

private theorem m6_extPres_set_ws {s0 s : FullState} {i : Nat} {v : BitVec 32}
    (hp : FullExtScratchPres s0 s) :
    FullExtScratchPres s0
      { s with scratch := { s.scratch with wsort := s.scratch.wsort.set i v } } := hp

private theorem m6_sb_set_ws {s0 s : FullState} {i : Nat} {v : BitVec 32}
    (hsb : s.scratch.scratch_buf = s0.scratch.scratch_buf) :
    ({ s with scratch := { s.scratch with wsort := s.scratch.wsort.set i v } }).scratch.scratch_buf
      = s0.scratch.scratch_buf := hsb

private theorem m6_wsortLitsOk_push_2 {s : FullState} {cv m i0 i1 : Nat} {lit sc : BitVec 32}
    (hok : M6WsortLitsOk cv s.scratch.wsort m) (hi0 : i0 = 2 * m) (hi1 : i1 = 2 * m + 1)
    (hlit : lit.toNat < 2 * cv) (hlen : 2 * m + 1 < s.scratch.wsort.length) :
    let s1 := { s with scratch := { s.scratch with wsort := s.scratch.wsort.set i0 lit } }
    M6WsortLitsOk cv
      ({ s1 with scratch := { s1.scratch with wsort := s1.scratch.wsort.set i1 sc } }).scratch.wsort
      (m + 1) := by
  intro s1; dsimp only [s1]; rw [hi0, hi1]; exact m6_wsortLitsOk_push hok hlit hlen

private theorem m6_arenaPerm_refl (k : FullCoreState) : FullArenaPermEq k k :=
  ⟨rfl, rfl, fun _ _ => ⟨rfl, rfl, List.Perm.refl _⟩⟩

private theorem m6_mul3_add_64 {max_cl : BitVec 64} {x : BitVec 32}
    (h : 3 * max_cl.toNat + x.toNat < 2 ^ 64) :
    (max_cl * 3 + x.setWidth 64).toNat = 3 * max_cl.toNat + x.toNat := by
  rw [BitVec.toNat_add, BitVec.toNat_mul, show (3 : BitVec 64).toNat = 3 from rfl,
    zext_toNat _ (by decide), Nat.mod_eq_of_lt (by omega : max_cl.toNat * 3 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : max_cl.toNat * 3 + x.toNat < 2 ^ 64)]
  omega

private theorem m6_scr_lo_set_st {s0 s : FullState} {n idx : Nat} {val : BitVec 32}
    (hprev : ∀ i < 2 * n, s.scratch.scratch_buf[i]? = s0.scratch.scratch_buf[i]?)
    (hhi : 2 * n ≤ idx) :
    ∀ i < 2 * n,
      ({ s with scratch := { s.scratch with
        scratch_buf := s.scratch.scratch_buf.set idx val } }).scratch.scratch_buf[i]? =
        s0.scratch.scratch_buf[i]? :=
  fun i hi => by rw [List.getElem?_set_ne (by omega)]; exact hprev i hi

/-! ## 2. `full_walk_pick_m6` (`m6WalkPickSpec`) -/

section WalkPickProof

open scoped FullArenaTactics

/-- `full_walk_pick_m6` satisfies `m6WalkPickSpec`. -/
theorem full_walk_pick_m6_wp (Γ : Env)
    (hBreak : ∀ a m Q X,
      m6WalkBreakSpec a m Q X → Γ "full_walk_break_m6" [i64, i32, i64, i64, i64] [i64] a m Q X)
    (hScore : ∀ a m Q X,
      m6WalkScoreSpec a m Q X → Γ "full_walk_score_m6" [i64, i64] [i32] a m Q X)
    (hRng : ∀ a m Q X,
      fullRngNextSpec a m Q X → Γ "full_rng_next" [i64] [i64] a m Q X) :
    ∀ a m Q X, m6WalkPickSpec a m Q X → Func.wp Γ full_walk_pick_m6_body a m Q X := by
  rintro ⟨h, ci, ncl, max_cl, occ_cap, inv_q16, ⟨⟩⟩ m Q X
    ⟨c, s, R, ⟨rfl, ⟨F0, hinv⟩, hci, hncl, hcap, hok⟩, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hlen hm hQ
  obtain ⟨F_cur, hw_inv⟩ := hinv.witness
  obtain ha := hw_inv.arena
  obtain hmax : c.max_vars < 2 * dimacsBound := c.hmaxv
  obtain haca : c.arena_cap < 2 * dimacsBound := c.harena
  obtain hsca : c.scratch_cap < dimacsBound := c.hscr
  unfold dimacsBound at hmax haca hsca
  obtain hcv_le := hlen.core_ok.cur_vars_le
  obtain harl := hlen.core_ok.arena_len_arr
  obtain hale := hlen.core_ok.arena_len_le
  obtain hvl := hlen.core_ok.vals_len
  obtain hsbl := hlen.scratch_ok.scratch_buf_len
  have h2ci : (ci <<< (1 : Nat)).toNat = 2 * ci.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]; omega
  have h2ci_lt : 2 * ci.toNat < s.scratch.scratch_buf.length := by rw [hsbl]; omega
  have h2ci_lt' : (ci <<< (1 : Nat)).toNat < s.scratch.scratch_buf.length := by
    rw [h2ci]; exact h2ci_lt
  have h2ci1_eq : ((ci <<< (1 : Nat)) + 1#64).toNat = 2 * ci.toNat + 1 := by
    rw [BitVec.toNat_add, h2ci, show (1#64 : BitVec 64).toNat = 1 from rfl,
      Nat.mod_eq_of_lt (by omega)]
  have h2ci1_lt : 2 * ci.toNat + 1 < s.scratch.scratch_buf.length := by rw [hsbl]; omega
  have h2ci1_lt' : ((ci <<< (1 : Nat)) + 1#64).toNat < s.scratch.scratch_buf.length := by
    rw [h2ci1_eq]; exact h2ci1_lt
  let w0 := s.scratch.scratch_buf[(ci <<< (1 : Nat)).toNat]'h2ci_lt'
  have hw0_at : s.scratch.scratch_buf[2 * ci.toNat]?.getD 0#32 = w0 := by
    have heq : s.scratch.scratch_buf[2 * ci.toNat]'h2ci_lt = w0 := by simp only [w0, h2ci]
    rw [List.getElem?_eq_getElem h2ci_lt, Option.getD_some, heq]
  have h2ci_mod : 2 * ci.toNat % 2 ^ 64 = 2 * ci.toNat := Nat.mod_eq_of_lt (by omega)
  have hent := hok ci.toNat hci
  unfold FullWalkEntryOk at hent
  c0_hsteps_nogrp
  -- Join after collecting candidates from binary or large clause -> roulette selection
  refine wp_join_group (ts := [i64, i64, i64, i32])
    (fun (mv, sum_s, zcnt, zlit, ()) mj => ∃ sj : FullState,
      PreservesCoreSlice FullState.core s sj ∧ sj.LengthsOk c ∧
      mv.toNat ≤ s.core.cur_vars ∧ M6WsortLitsOk s.core.cur_vars sj.scratch.wsort mv.toNat ∧
      (0 < zcnt.toNat → zlit.toNat < 2 * s.core.cur_vars) ∧
      sj.scratch.scratch_buf = s.scratch.scratch_buf ∧ FullExtScratchPres s sj ∧
      (FullMem c sj ⋆ R) mj)
    (fun _ ⟨mv, sum_s, zcnt, zlit, ⟨⟩⟩ mj
        ⟨sj, hcorej, hsj, hmv_le, hws_ok, hz_ok, hsbj, hpresj, hmj⟩ => ?_)
    (fun Jc hJc => ?_)
  · -- Post-collection: `m == 0`, `zcnt > 0`, `sum_s == 0`, or roulette loop
    obtain hwslj := hsj.scratch_ok.wsort_len
    c0_hsteps_nogrp
    · exact hQ (0xFFFFFFFF#32, ()) sj mj hcorej hsj ⟨hpresj, hsbj, Or.inl rfl⟩ hmj
    · have hz_pos : 0 < zcnt.toNat := by c0_bound
      exact hQ (zlit, ()) sj mj hcorej hsj ⟨hpresj, hsbj, Or.inr (hz_ok hz_pos)⟩ hmj
    · have hmv_pos : 0 < mv.toNat := by
        have : mv ≠ 0#64 := by assumption
        have : mv.toNat ≠ 0 := fun h0 => this (BitVec.eq_of_toNat_eq h0)
        omega
      have h0_lt : 0 < sj.scratch.wsort.length := by rw [hwslj]; omega
      c0_hsteps
      have hlit0 : (sj.scratch.wsort[0]'h0_lt).toNat < 2 * s.core.cur_vars := by
        have := hws_ok 0 hmv_pos
        rwa [List.getElem?_eq_getElem h0_lt, Option.getD_some] at this
      exact hQ (_, ()) sj mj hcorej hsj ⟨hpresj, hsbj, Or.inr hlit0⟩ hmj
    · have hmv_pos : 0 < mv.toNat := by
        have : mv ≠ 0#64 := by assumption
        have : mv.toNat ≠ 0 := fun h0 => this (BitVec.eq_of_toNat_eq h0)
        omega
      have hsum_nz : sum_s ≠ 0#64 := by assumption
      c0_call hRng
      refine ⟨c, sj, R, rfl, hsj, hmj, ?_⟩
      intro rng sr mr hcorer hsr hrng_eq hmr
      dsimp only [fullSafetySlice] at hsr hmr
      have hceqr : sr.core = s.core := Eq.trans hcorer hcorej
      have hpresr : FullExtScratchPres s sr :=
        m6_extPres_trans hpresj (m6_extPres_of_rng hrng_eq)
      have hsbr : sr.scratch.scratch_buf = s.scratch.scratch_buf := by
        rw [hrng_eq]; exact hsbj
      have hwsr_eq : sr.scratch.wsort = sj.scratch.wsort := by rw [hrng_eq]
      obtain hwslr := hsr.scratch_ok.wsort_len
      c0_hsteps_nogrp
      -- Roulette loop `while (i < m)`
      refine wp_loop_group (ts := [i64, i64])
        (fun rem (_acc, idx, ()) ml => ml = mr ∧ idx.toNat ≤ mv.toNat ∧
          rem = mv.toNat - idx.toNat) ?_ ?_
      · rintro _ rem ⟨acc, idx, ⟨⟩⟩ ml ih ⟨rfl, hile, rfl⟩
        c0_hsteps_nogrp
        · have hilt : idx.toNat < mv.toNat := by assumption
          have h2i : (idx <<< (1 : Nat)).toNat = 2 * idx.toNat := by
            rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]; omega
          have h2i_lt : (idx <<< (1 : Nat)).toNat < sr.scratch.wsort.length := by
            rw [h2i, hwslr]; omega
          c0_hsteps
          have hlit_i : (sr.scratch.wsort[(idx <<< (1 : Nat)).toNat]'h2i_lt).toNat <
              2 * s.core.cur_vars := by
            have h := hws_ok idx.toNat hilt
            rw [← hwsr_eq, List.getElem?_eq_getElem (by rw [hwslr]; omega),
              Option.getD_some] at h
            simpa only [h2i] using h
          exact hQ (_, ()) sr ml hceqr hsr ⟨hpresr, hsbr, Or.inr hlit_i⟩ hmr
        · have hilt : idx.toNat < mv.toNat := by assumption
          have hi1 : (idx + 1#64).toNat = idx.toNat + 1 := by bv_omega
          exact ih (mv.toNat - (idx + 1#64).toNat) (_, idx + 1#64, ()) ml
            (by rw [hi1]; omega) ⟨rfl, by rw [hi1]; omega, rfl⟩
        · have hm1_eq : (mv - 1#64).toNat = mv.toNat - 1 := by bv_omega
          have h2m1 : ((mv - 1#64) <<< (1 : Nat)).toNat = 2 * (mv.toNat - 1) := by
            rw [BitVec.toNat_shiftLeft, hm1_eq, Nat.shiftLeft_eq,
              Nat.mod_eq_of_lt (by omega)]; omega
          have h2m1_lt : ((mv - 1#64) <<< (1 : Nat)).toNat < sr.scratch.wsort.length := by
            rw [h2m1, hwslr]; omega
          c0_hsteps
          have hlit_last : (sr.scratch.wsort[((mv - 1#64) <<< (1 : Nat)).toNat]'h2m1_lt).toNat <
              2 * s.core.cur_vars := by
            have h := hws_ok (mv.toNat - 1) (by omega)
            rw [← hwsr_eq, List.getElem?_eq_getElem (by rw [hwslr]; omega),
              Option.getD_some] at h
            simpa only [h2m1] using h
          exact hQ (_, ()) sr ml hceqr hsr ⟨hpresr, hsbr, Or.inr hlit_last⟩ hmr
      · intro _ hL; c0_hsteps; exact hL mv.toNat (0#64, 0#64, ()) mr ⟨rfl, by simp, by simp⟩
  · -- Collect candidates: binary vs large clause
    c0_hsteps_nogrp
    · -- Binary clause entry
      have hbin : (w0 &&& 0x80000000#32) ≠ 0#32 := by
        have hw_eq : s.scratch.scratch_buf[2 * ci.toNat % 2 ^ 64]'(by
            rw [h2ci_mod]; exact h2ci_lt) = w0 := by simp only [w0, h2ci, h2ci_mod]
        rw [← hw_eq]; exact hc
      rw [hw0_at, ite_eq_left hbin] at hent
      obtain ⟨ha_lt, hb_lt⟩ := hent
      let a_lit := w0 &&& 0x7FFFFFFF#32
      let b_lit := s.scratch.scratch_buf[((ci <<< (1 : Nat)) + 1#64).toNat]'h2ci1_lt'
      have ha_v : (a_lit.setWidth 64).toNat < s.core.vals.length := by
        rw [zext_toNat _ (by decide), hvl]; exact Nat.lt_of_lt_of_le ha_lt (by omega)
      have hb_lt' : b_lit.toNat < 2 * s.core.cur_vars := by
        have h : (s.scratch.scratch_buf[2 * ci.toNat + 1]'h2ci1_lt).toNat <
            2 * s.core.cur_vars := by
          rw [List.getElem?_eq_getElem h2ci1_lt, Option.getD_some] at hb_lt; exact hb_lt
        simpa only [b_lit, h2ci1_eq] using h
      -- Join after literal `a` -> process literal `b`
      refine wp_join_group (ts := [i64, i64, i64, i32])
        (fun (m1, sum1, zc1, zl1, ()) m_a => ∃ s_a : FullState,
          PreservesCoreSlice FullState.core s s_a ∧ s_a.LengthsOk c ∧
          m1.toNat ≤ s.core.cur_vars ∧ zc1.toNat ≤ m1.toNat ∧
          M6WsortLitsOk s.core.cur_vars s_a.scratch.wsort m1.toNat ∧
          (0 < zc1.toNat → zl1.toNat < 2 * s.core.cur_vars) ∧
          s_a.scratch.scratch_buf = s.scratch.scratch_buf ∧ FullExtScratchPres s s_a ∧
          (FullMem c s_a ⋆ R) m_a)
        (fun _ ⟨m1, sum1, zc1, zl1, ⟨⟩⟩ m_a
            ⟨s_a, hcore_a, hs_a, hm1_le, hzc1_le, hws_a, hzl_a, hsb_a, hpres_a, hm_a⟩ => ?_)
        (fun Ja hJa => ?_)
      · -- Process literal `b`
        have hb_v : (b_lit.setWidth 64).toNat < s_a.core.vals.length := by
          rw [zext_toNat _ (by decide), hcore_a, hvl]; omega
        refine wp_join_group (ts := [i64, i64, i64, i32])
          (fun (m2, sum2, zc2, zl2, ()) mb => ∃ sb : FullState,
            PreservesCoreSlice FullState.core s sb ∧ sb.LengthsOk c ∧
            m2.toNat ≤ s.core.cur_vars ∧ M6WsortLitsOk s.core.cur_vars sb.scratch.wsort m2.toNat ∧
            (0 < zc2.toNat → zl2.toNat < 2 * s.core.cur_vars) ∧
            sb.scratch.scratch_buf = s.scratch.scratch_buf ∧ FullExtScratchPres s sb ∧
            (FullMem c sb ⋆ R) mb)
          (fun _ ⟨m2, sum2, zc2, zl2, ⟨⟩⟩ mb
              ⟨sb, hcoreb, hsb, hm2_le, hwsb, hzlb, hsbb, hpresb, hmb⟩ => by
            c0_hsteps
            exact hJc (m2, sum2, zc2, zl2, ()) mb
              ⟨sb, hcoreb, hsb, hm2_le, hwsb, hzlb, hsbb, hpresb, hmb⟩)
          (fun Jb hJb => ?_)
        c0_hsteps_nogrp
        · have hm1_lt : m1.toNat < s.core.cur_vars := by
            have : m1.toNat < s.core.cur_vars % 2 ^ 64 := by assumption
            rwa [Nat.mod_eq_of_lt (by omega)] at this
          c0_call hBreak
          refine ⟨c, s_a, R, ⟨rfl, hncl, hcap⟩, hs_a, hm_a, ?_⟩
          intro brk sb mb _ _ hsb_eq hmb
          subst sb
          dsimp only [fullSafetySlice] at hmb
          c0_hsteps_nogrp
          -- Join after `if (brk == 0)` for literal `b`
          refine wp_join_group (ts := [i64, i32])
            (fun (zc2, zl2, ()) mz => ∃ sz : FullState,
              PreservesCoreSlice FullState.core s sz ∧ sz.LengthsOk c ∧
              M6WsortLitsOk s.core.cur_vars sz.scratch.wsort m1.toNat ∧
              (0 < zc2.toNat → zl2.toNat < 2 * s.core.cur_vars) ∧
              sz.scratch.scratch_buf = s.scratch.scratch_buf ∧ FullExtScratchPres s sz ∧
              (FullMem c sz ⋆ R) mz)
            (fun _ ⟨zc2, zl2, ⟨⟩⟩ mz
                ⟨sz, hcorez, hsz, hwsz, hzlz, hsbz, hpresz, hmz⟩ => ?_)
            (fun Jz hJz => ?_)
          · c0_call hScore
            intro sc _
            obtain hwslz := hsz.scratch_ok.wsort_len
            have h2m1 : (m1 <<< (1 : Nat)).toNat = 2 * m1.toNat := by
              rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]; omega
            have h2m1_lt : (m1 <<< (1 : Nat)).toNat < sz.scratch.wsort.length := by
              rw [h2m1, hwslz]; omega
            have h2m1p_eq : ((m1 <<< (1 : Nat)) + 1#64).toNat = 2 * m1.toNat + 1 := by
              rw [BitVec.toNat_add, h2m1, show (1#64 : BitVec 64).toNat = 1 from rfl,
                Nat.mod_eq_of_lt (by omega)]
            have h2m1p_lt : ((m1 <<< (1 : Nat)) + 1#64).toNat < sz.scratch.wsort.length := by
              rw [h2m1p_eq, hwslz]; omega
            have hm1p1 : (m1 + 1#64).toNat = m1.toNat + 1 := by bv_omega
            c0_hsteps
            refine hJb (m1 + 1#64, sum1 + sc.setWidth 64, zc2, zl2, ()) _
              ⟨_, ?_, ?_, by omega, ?_, hzlz, ?_, ?_, hm⟩
            · exact m6_core_set_ws (m6_core_set_ws hcorez)
            · exact m6_len_set_ws (m6_len_set_ws hsz)
            · rw [hm1p1]
              exact m6_wsortLitsOk_push_2 hwsz h2m1 h2m1p_eq hb_lt' (by rw [hwslz]; omega)
            · exact m6_sb_set_ws (m6_sb_set_ws hsbz)
            · exact m6_extPres_set_ws (m6_extPres_set_ws hpresz)
          · c0_hsteps_nogrp
            · have hzc1p : (zc1 + 1#64).toNat = zc1.toNat + 1 := by bv_omega
              have hzc_nz : zc1 + 1#64 ≠ 0#64 := fun h0 => by
                have := congrArg BitVec.toNat h0; simp [hzc1p] at this
              refine wp_join_group (ts := [i32])
                (fun (zl2, ()) mz => ∃ sz : FullState,
                  PreservesCoreSlice FullState.core s sz ∧ sz.LengthsOk c ∧
                  M6WsortLitsOk s.core.cur_vars sz.scratch.wsort m1.toNat ∧
                  zl2.toNat < 2 * s.core.cur_vars ∧
                  sz.scratch.scratch_buf = s.scratch.scratch_buf ∧ FullExtScratchPres s sz ∧
                  (FullMem c sz ⋆ R) mz)
                (fun _ ⟨zl2, ⟨⟩⟩ mz ⟨sz, hcorez, hsz, hwsz, hzl2, hsbz, hpresz, hmz⟩ => by
                  c0_hsteps
                  exact hJz (zc1 + 1#64, zl2, ()) mz
                    ⟨sz, hcorez, hsz, hwsz, fun _ => hzl2, hsbz, hpresz, hmz⟩)
                (fun Jzl hJzl => ?_)
              c0_hsteps_nogrp
              · exact hJzl (b_lit, ()) mb
                  ⟨s_a, hcore_a, hs_a, hws_a, hb_lt', hsb_a, hpres_a, hmb⟩
              · c0_call hRng
                refine ⟨c, s_a, R, rfl, hs_a, hmb, ?_⟩
                intro rv sr mr hcorer hsr hrng_eq hmr
                dsimp only [fullSafetySlice] at hsr hmr
                have hceqr : sr.core = s.core := Eq.trans hcorer hcore_a
                have hpresr : FullExtScratchPres s sr :=
                  m6_extPres_trans hpres_a (m6_extPres_of_rng hrng_eq)
                have hsbr : sr.scratch.scratch_buf = s.scratch.scratch_buf := by
                  rw [hrng_eq]; exact hsb_a
                have hwsr : M6WsortLitsOk s.core.cur_vars sr.scratch.wsort m1.toNat := by
                  rw [hrng_eq]; exact hws_a
                have hzc1_pos : 0 < zc1.toNat := Nat.pos_of_ne_zero fun h0 => by
                  have hne1 : zc1 + 1#64 ≠ 1#64 := by assumption
                  exact hne1 (BitVec.eq_of_toNat_eq (by rw [hzc1p, h0]; rfl))
                c0_hsteps
                · exact hJzl (b_lit, ()) mr
                    ⟨sr, hceqr, hsr, hwsr, hb_lt', hsbr, hpresr, hmr⟩
                · exact hJzl (zl1, ()) mr
                    ⟨sr, hceqr, hsr, hwsr, hzl_a hzc1_pos, hsbr, hpresr, hmr⟩
            · exact hJz (zc1, zl1, ()) mb
                ⟨s_a, hcore_a, hs_a, hws_a, hzl_a, hsb_a, hpres_a, hmb⟩
        · exact hJb (m1, sum1, zc1, zl1, ()) m_a
            ⟨s_a, hcore_a, hs_a, hm1_le, hws_a, hzl_a, hsb_a, hpres_a, hm_a⟩
        · exact hJb (m1, sum1, zc1, zl1, ()) m_a
            ⟨s_a, hcore_a, hs_a, hm1_le, hws_a, hzl_a, hsb_a, hpres_a, hm_a⟩
      · -- Process literal `a`
        c0_hsteps_nogrp
        · have hcv_pos : 0 < s.core.cur_vars := by
            have : (0#64 : BitVec 64).toNat < s.core.cur_vars % 2 ^ 64 := by assumption
            rw [Nat.mod_eq_of_lt (by omega)] at this; simp at this; exact this
          c0_call hBreak
          refine ⟨c, s, R, ⟨rfl, hncl, hcap⟩, hlen, hm, ?_⟩
          intro brk sb mb _ _ hsb_eq hmb
          subst sb
          dsimp only [fullSafetySlice] at hmb
          c0_hsteps_nogrp
          refine wp_join_group (ts := [i64, i32])
            (fun (zc1, zl1, ()) mz => mz = mb ∧ zc1.toNat ≤ 1 ∧
              (0 < zc1.toNat → zl1.toNat < 2 * s.core.cur_vars))
            (fun _ ⟨zc1, zl1, ⟨⟩⟩ mz ⟨rfl, hzc1, hzl1⟩ => ?_)
            (fun Jz hJz => ?_)
          · c0_call hScore
            intro sc _
            obtain hwsl := hlen.scratch_ok.wsort_len
            have h0_lt : 0 < s.scratch.wsort.length := by rw [hwsl]; omega
            have h1_lt : 1 < s.scratch.wsort.length := by rw [hwsl]; omega
            c0_hsteps
            refine hJa (0#64 + 1#64, 0#64 + sc.setWidth 64, zc1, zl1, ()) _
              ⟨_, ?_, ?_, by simp; omega, by simp; omega, ?_, hzl1, ?_, ?_, hm⟩
            · exact m6_core_set_ws (m6_core_set_ws rfl)
            · exact m6_len_set_ws (m6_len_set_ws hlen)
            · exact m6_wsortLitsOk_push_2 (fun _ h => absurd h (Nat.not_lt_zero _))
                rfl rfl ha_lt h1_lt
            · exact m6_sb_set_ws (m6_sb_set_ws rfl)
            · exact m6_extPres_set_ws (m6_extPres_set_ws ⟨rfl, rfl⟩)
          · c0_hsteps
            · exact hJz (1#64, a_lit, ()) mb ⟨rfl, by simp, fun _ => ha_lt⟩
            · exact hJz (0#64, 0xFFFFFFFF#32, ()) mb ⟨rfl, by simp, fun h => by simp at h⟩
        · exact hJa (0#64, 0#64, 0#64, 0xFFFFFFFF#32, ()) m
            ⟨s, rfl, hlen, by simp, by simp, fun _ h => absurd h (Nat.not_lt_zero _),
              fun h => by simp at h, rfl, ⟨rfl, rfl⟩, hm⟩
    · -- Large clause entry
      have hlg : (w0 &&& 0x80000000#32) = 0#32 := by
        have hw_eq : s.scratch.scratch_buf[2 * ci.toNat % 2 ^ 64]'(by
            rw [h2ci_mod]; exact h2ci_lt) = w0 := by simp only [w0, h2ci, h2ci_mod]
        rw [← hw_eq]; exact hc
      rw [hw0_at, ite_eq_right (by simp [hlg])] at hent
      obtain ⟨hw0_ref, hw0_ng⟩ := hent
      have hwf := ha.refs_wf w0.toNat hw0_ref
      have hwf1 := hwf.1; have hwf3 := hwf.2.2.1; have hwf4 := hwf.2.2.2.1
      have hw02_idx : (w0.setWidth 64 + 2#64).toNat = w0.toNat + 2 := by
        rw [BitVec.toNat_add, zext_toNat _ (by decide),
          show (2#64 : BitVec 64).toNat = 2 from rfl, Nat.mod_eq_of_lt (by omega)]
      have hw02_ar : (w0.setWidth 64 + 2#64).toNat < s.core.arena.length := by
        rw [hw02_idx, harl]; omega
      have hsz_eq : (s.core.arena[(w0.setWidth 64 + 2#64).toNat]'hw02_ar).toNat =
          fullArenaClauseSizeCore s.core w0.toNat := by
        have h1 : s.core.arena[(w0.setWidth 64 + 2#64).toNat]'hw02_ar =
            s.core.arena[w0.toNat + 2]'(by rw [harl]; omega) := by simp only [hw02_idx]
        rw [h1]; unfold fullArenaClauseSizeCore
        rw [List.getElem?_eq_getElem (by rw [harl]; omega), Option.getD_some]
      c0_hsteps_nogrp
      refine wp_loop_safety_slice (fullSafetySlice c) s R (fun _ => True) trivial
        (fun sk (m_k, sumk, zck, zlk, k, ()) =>
          k.toNat ≤ fullArenaClauseSizeCore s.core w0.toNat ∧
          m_k.toNat ≤ s.core.cur_vars ∧ zck.toNat ≤ m_k.toNat ∧
          M6WsortLitsOk s.core.cur_vars sk.scratch.wsort m_k.toNat ∧
          (0 < zck.toNat → zlk.toNat < 2 * s.core.cur_vars) ∧
          sk.scratch.scratch_buf = s.scratch.scratch_buf ∧ FullExtScratchPres s sk)
        (fun (_, _, _, _, k, ()) => fullArenaClauseSizeCore s.core w0.toNat - k.toNat)
        (fun Jk hJk => by
          c0_hsteps
          exact hJk s (0#64, 0#64, 0#64, 0xFFFFFFFF#32, 0#32, ()) m hm rfl hlen
            ⟨by simp, by simp, by simp, fun _ h => absurd h (Nat.not_lt_zero _),
              fun h => by simp at h, rfl, ⟨rfl, rfl⟩⟩)
        (fun Jk sk (m_k, sumk, zck, zlk, k, ()) mem_k hcorek hsk _
            ⟨hkle, hmk_le, hzck_le, hwsk, hzlk, hsbk, hpresk⟩ hmk hJk => ?_)
      dsimp only [fullSafetySlice] at hsk hmk
      have hceqk : sk.core = s.core := hcorek
      have hexit_k : Jc (m_k, sumk, zck, zlk, ()) mem_k :=
        hJc (m_k, sumk, zck, zlk, ()) mem_k ⟨sk, hceqk, hsk, hmk_le, hwsk, hzlk, hsbk, hpresk, hmk⟩
      c0_hsteps_nogrp
      · have hklt : k.toNat < fullArenaClauseSizeCore s.core w0.toNat := by
          have : k.toNat < (s.core.arena[(w0.setWidth 64 + 2#64).toNat]'hw02_ar).toNat := by
            assumption
          omega
        have hmk_lt : m_k.toNat < s.core.cur_vars := by
          have : m_k.toNat < s.core.cur_vars % 2 ^ 64 := by assumption
          rwa [Nat.mod_eq_of_lt (by omega)] at this
        have hk_idx : (w0.setWidth 64 + 3#64 + k.setWidth 64).toNat = w0.toNat + 3 + k.toNat := by
          rw [BitVec.toNat_add, BitVec.toNat_add, zext_toNat _ (by decide),
            zext_toNat _ (by decide), show (3#64 : BitVec 64).toNat = 3 from rfl,
            Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        have hk_ar : (w0.setWidth 64 + 3#64 + k.setWidth 64).toNat < sk.core.arena.length := by
          rw [hk_idx, hceqk, harl]; omega
        let lit := sk.core.arena[(w0.setWidth 64 + 3#64 + k.setWidth 64).toNat]'hk_ar
        have hlit_lt : lit.toNat < 2 * s.core.cur_vars := by
          have hmem : (s.core.arena[w0.toNat + 3 + k.toNat]'(by rw [harl]; omega)).toNat ∈
              fullArenaClauseLitsCore s.core w0.toNat := by
            unfold fullArenaClauseLitsCore
            refine List.mem_map.mpr ⟨_, ?_, rfl⟩
            have hlt : k.toNat < ((s.core.arena.drop (w0.toNat + 3)).take
                (fullArenaClauseSizeCore s.core w0.toNat)).length := by
              rw [List.length_take, List.length_drop, harl]; omega
            simpa [List.getElem_take, List.getElem_drop] using List.getElem_mem hlt
          have := ha.lits_lt w0.toNat hw0_ref hw0_ng _ hmem
          simpa only [lit, hceqk, hk_idx] using this
        have hlit_v : (lit.setWidth 64).toNat < sk.core.vals.length := by
          rw [zext_toNat _ (by decide), hceqk, hvl]; omega
        have hk1 : (k + 1#32).toNat = k.toNat + 1 := by bv_omega
        c0_hsteps_nogrp
        -- Join after `if (vals[lit] == 0)` -> `k = k + 1; jump Jk`
        refine wp_join_group (ts := [i64, i64, i64, i32])
          (fun (mk', sumk', zck', zlk', ()) m' => ∃ sk' : FullState,
            PreservesCoreSlice FullState.core s sk' ∧ sk'.LengthsOk c ∧
            mk'.toNat ≤ s.core.cur_vars ∧ zck'.toNat ≤ mk'.toNat ∧
            M6WsortLitsOk s.core.cur_vars sk'.scratch.wsort mk'.toNat ∧
            (0 < zck'.toNat → zlk'.toNat < 2 * s.core.cur_vars) ∧
            sk'.scratch.scratch_buf = s.scratch.scratch_buf ∧ FullExtScratchPres s sk' ∧
            (FullMem c sk' ⋆ R) m')
          (fun _ ⟨mk', sumk', zck', zlk', ⟨⟩⟩ m'
              ⟨sk', hcore', hs', hmk', hzck', hws', hzl', hsb', hpres', hm'⟩ => by
            c0_hsteps
            exact hJk sk' (mk', sumk', zck', zlk', k + 1#32, ()) m' hm'
              (by dsimp only; omega) (Eq.trans hcore' hceqk.symm) hs'
              ⟨by omega, hmk', hzck', hws', hzl', hsb', hpres'⟩)
          (fun Jlit hJlit => ?_)
        c0_hsteps_nogrp
        · c0_call hBreak
          refine ⟨c, sk, R, ⟨rfl, hncl, hcap⟩, hsk, hmk, ?_⟩
          intro brk sb mb _ _ hsb_eq hmb
          subst sb
          dsimp only [fullSafetySlice] at hmb
          c0_hsteps_nogrp
          refine wp_join_group (ts := [i64, i32])
            (fun (zc2, zl2, ()) mz => ∃ sz : FullState,
              PreservesCoreSlice FullState.core s sz ∧ sz.LengthsOk c ∧
              zc2.toNat ≤ m_k.toNat + 1 ∧
              M6WsortLitsOk s.core.cur_vars sz.scratch.wsort m_k.toNat ∧
              (0 < zc2.toNat → zl2.toNat < 2 * s.core.cur_vars) ∧
              sz.scratch.scratch_buf = s.scratch.scratch_buf ∧ FullExtScratchPres s sz ∧
              (FullMem c sz ⋆ R) mz)
            (fun _ ⟨zc2, zl2, ⟨⟩⟩ mz
                ⟨sz, hcorez, hsz, hzc2_le, hwsz, hzlz, hsbz, hpresz, hmz⟩ => ?_)
            (fun Jz hJz => ?_)
          · c0_call hScore
            intro sc _
            obtain hwslz := hsz.scratch_ok.wsort_len
            have h2m : (m_k <<< (1 : Nat)).toNat = 2 * m_k.toNat := by
              rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]; omega
            have h2m_lt : (m_k <<< (1 : Nat)).toNat < sz.scratch.wsort.length := by
              rw [h2m, hwslz]; omega
            have h2mp_eq : ((m_k <<< (1 : Nat)) + 1#64).toNat = 2 * m_k.toNat + 1 := by
              rw [BitVec.toNat_add, h2m, show (1#64 : BitVec 64).toNat = 1 from rfl,
                Nat.mod_eq_of_lt (by omega)]
            have h2mp_lt : ((m_k <<< (1 : Nat)) + 1#64).toNat < sz.scratch.wsort.length := by
              rw [h2mp_eq, hwslz]; omega
            have hmp1 : (m_k + 1#64).toNat = m_k.toNat + 1 := by bv_omega
            c0_hsteps
            refine hJlit (m_k + 1#64, sumk + sc.setWidth 64, zc2, zl2, ()) _
              ⟨_, ?_, ?_, by omega, by omega, ?_, hzlz, ?_, ?_, hm⟩
            · exact m6_core_set_ws (m6_core_set_ws hcorez)
            · exact m6_len_set_ws (m6_len_set_ws hsz)
            · rw [hmp1]
              exact m6_wsortLitsOk_push_2 hwsz h2m h2mp_eq hlit_lt (by rw [hwslz]; omega)
            · exact m6_sb_set_ws (m6_sb_set_ws hsbz)
            · exact m6_extPres_set_ws (m6_extPres_set_ws hpresz)
          · c0_hsteps_nogrp
            · have hzcp : (zck + 1#64).toNat = zck.toNat + 1 := by bv_omega
              have hzc_nz : zck + 1#64 ≠ 0#64 := fun h0 => by
                have := congrArg BitVec.toNat h0; simp [hzcp] at this
              refine wp_join_group (ts := [i32])
                (fun (zl2, ()) mz => ∃ sz : FullState,
                  PreservesCoreSlice FullState.core s sz ∧ sz.LengthsOk c ∧
                  M6WsortLitsOk s.core.cur_vars sz.scratch.wsort m_k.toNat ∧
                  zl2.toNat < 2 * s.core.cur_vars ∧
                  sz.scratch.scratch_buf = s.scratch.scratch_buf ∧ FullExtScratchPres s sz ∧
                  (FullMem c sz ⋆ R) mz)
                (fun _ ⟨zl2, ⟨⟩⟩ mz ⟨sz, hcorez, hsz, hwsz, hzl2, hsbz, hpresz, hmz⟩ => by
                  c0_hsteps
                  exact hJz (zck + 1#64, zl2, ()) mz
                    ⟨sz, hcorez, hsz, by omega, hwsz, fun _ => hzl2, hsbz, hpresz, hmz⟩)
                (fun Jzl hJzl => ?_)
              c0_hsteps_nogrp
              · exact hJzl (lit, ()) mb
                  ⟨sk, hceqk, hsk, hwsk, hlit_lt, hsbk, hpresk, hmb⟩
              · c0_call hRng
                refine ⟨c, sk, R, rfl, hsk, hmb, ?_⟩
                intro rv sr mr hcorer hsr hrng_eq hmr
                dsimp only [fullSafetySlice] at hsr hmr
                have hceqr : sr.core = s.core := Eq.trans hcorer hceqk
                have hpresr : FullExtScratchPres s sr :=
                  m6_extPres_trans hpresk (m6_extPres_of_rng hrng_eq)
                have hsbr : sr.scratch.scratch_buf = s.scratch.scratch_buf := by
                  rw [hrng_eq]; exact hsbk
                have hwsr : M6WsortLitsOk s.core.cur_vars sr.scratch.wsort m_k.toNat := by
                  rw [hrng_eq]; exact hwsk
                have hzck_pos : 0 < zck.toNat := Nat.pos_of_ne_zero fun h0 => by
                  have hne1 : zck + 1#64 ≠ 1#64 := by assumption
                  exact hne1 (BitVec.eq_of_toNat_eq (by rw [hzcp, h0]; rfl))
                c0_hsteps
                · exact hJzl (lit, ()) mr
                    ⟨sr, hceqr, hsr, hwsr, hlit_lt, hsbr, hpresr, hmr⟩
                · exact hJzl (zlk, ()) mr
                    ⟨sr, hceqr, hsr, hwsr, hzlk hzck_pos, hsbr, hpresr, hmr⟩
            · exact hJz (zck, zlk, ()) mb
                ⟨sk, hceqk, hsk, by omega, hwsk, hzlk, hsbk, hpresk, hmb⟩
        · exact hJlit (m_k, sumk, zck, zlk, ()) mem_k
            ⟨sk, hceqk, hsk, hmk_le, hzck_le, hwsk, hzlk, hsbk, hpresk, hmk⟩
      · exact hexit_k
      · exact hexit_k

end WalkPickProof

/-! ## 3. `full_walk_flip_m6` (`m6WalkFlipSpec`) -/

section WalkFlipProof

open scoped FullArenaTactics

private theorem m6_scr_lo_set {buf : List (BitVec 32)} {n idx : Nat} {val : BitVec 32}
    (hhi : 2 * n ≤ idx) :
    ∀ i < 2 * n, (buf.set idx val)[i]? = buf[i]? :=
  fun _ hi => List.getElem?_set_ne (by omega)

private theorem m6_sat_hi {max_cl ncl : BitVec 64} (hncl : ncl.toNat ≤ max_cl.toNat)
    (hmc : 5 * max_cl.toNat < 2 ^ 28) (x : BitVec 32) :
    2 * ncl.toNat ≤ ((max_cl <<< (1 : Nat)) + x.setWidth 64).toNat := by
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, zext_toNat _ (by decide),
    Nat.mod_eq_of_lt (by omega : max_cl.toNat * 2 ^ 1 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : max_cl.toNat * 2 ^ 1 + x.toNat < 2 ^ 64)]
  omega

private theorem m6_up_hi {max_cl ncl : BitVec 64} (hncl : ncl.toNat ≤ max_cl.toNat)
    (hmc : 5 * max_cl.toNat < 2 ^ 28) (x : BitVec 32) :
    2 * ncl.toNat ≤ (max_cl * 3 + x.setWidth 64).toNat := by
  rw [m6_mul3_add_64 (by omega)]; omega

private theorem m6_add1_64 {x : BitVec 64} (h : x.toNat + 1 < 2 ^ 64) :
    (x + 1#64).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt h]

private theorem m6_occ_idx_64 {max_cl off k : BitVec 64}
    (h : 5 * max_cl.toNat + off.toNat + k.toNat < 2 ^ 64) :
    ((max_cl * 5#64 + off) + k).toNat = 5 * max_cl.toNat + off.toNat + k.toNat := by
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_mul,
    show (5#64 : BitVec 64).toNat = 5 from rfl,
    Nat.mod_eq_of_lt (by omega : max_cl.toNat * 5 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : max_cl.toNat * 5 + off.toNat < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : max_cl.toNat * 5 + off.toNat + k.toNat < 2 ^ 64)]
  omega

private theorem m6_ul_hi32 {max_cl ncl : BitVec 64} (hncl : ncl.toNat ≤ max_cl.toNat)
    (hmc : 5 * max_cl.toNat < 2 ^ 28) (x : BitVec 32) :
    2 * ncl.toNat ≤ ((max_cl <<< (2 : Nat)) + x.setWidth 64).toNat := by
  have hx : x.toNat < 2 ^ 32 := x.isLt
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, zext_toNat _ (by decide),
    Nat.mod_eq_of_lt (by omega : max_cl.toNat * 2 ^ 2 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : max_cl.toNat * 2 ^ 2 + x.toNat < 2 ^ 64)]
  omega

private theorem m6_ul_hi {max_cl ncl : BitVec 64} (hncl : ncl.toNat ≤ max_cl.toNat)
    (hmc : 5 * max_cl.toNat < 2 ^ 28) (x : BitVec 64) (hx : x.toNat ≤ max_cl.toNat) :
    2 * ncl.toNat ≤ ((max_cl <<< (2 : Nat)) + x).toNat := by
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (by omega : max_cl.toNat * 2 ^ 2 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : max_cl.toNat * 2 ^ 2 + x.toNat < 2 ^ 64)]
  omega

/-- `full_walk_flip_m6` satisfies `m6WalkFlipSpec`. -/
theorem full_walk_flip_m6_wp (Γ : Env) :
    ∀ a m Q X, m6WalkFlipSpec a m Q X → Func.wp Γ full_walk_flip_m6_body a m Q X := by
  rintro ⟨h, lit, ncl, max_cl, occ_cap, ulen, ⟨⟩⟩ m Q X
    ⟨c, s, R, ⟨rfl, hncl, hulen, hcap⟩, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hlen hm hQ
  obtain hmax : c.max_vars < 2 * dimacsBound := c.hmaxv
  obtain hsca : c.scratch_cap < dimacsBound := c.hscr
  unfold dimacsBound at hmax hsca
  have h5mc_bd : 5 * max_cl.toNat < 2 ^ 28 := by omega
  obtain hcv_le := hlen.core_ok.cur_vars_le
  obtain hwvl := hlen.scratch_ok.walk_vals_len
  obtain hws1l := hlen.scratch_ok.work_stk1_len
  obtain hws2l := hlen.scratch_ok.work_stk2_len
  have hsh_mc : (max_cl <<< (1 : Nat)).toNat = 2 * max_cl.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]; omega
  have hsh_mc4 : (max_cl <<< (2 : Nat)).toNat = 4 * max_cl.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]; omega
  c0_hsteps_nogrp
  · exact hQ (ulen, ()) s m rfl hlen ⟨⟨rfl, rfl⟩, hulen, fun _ _ => rfl⟩ hm
  · have hv_lt : (lit >>> (1 : Nat)).toNat < s.core.cur_vars := by
      have h1 : ¬s.core.cur_vars % 2 ^ 64 ≤ (lit >>> (1 : Nat)).toNat := by assumption
      rw [Nat.mod_eq_of_lt (by omega)] at h1; omega
    have hpos_eq : (((lit >>> (1 : Nat)).setWidth 64) <<< (1 : Nat)).toNat =
        2 * (lit >>> (1 : Nat)).toNat := by
      rw [BitVec.toNat_shiftLeft, zext_toNat _ (by decide), Nat.shiftLeft_eq,
        Nat.mod_eq_of_lt (by omega)]; omega
    let pos_lit := ((lit >>> (1 : Nat)).setWidth 64) <<< (1 : Nat)
    have hpos_wv : pos_lit.toNat < s.scratch.walk_vals.length := by
      dsimp only [pos_lit]; rw [hpos_eq, hwvl]; omega
    -- Join after ternary `old_t = (wv[pos_lit] > 0) ? pos_lit : (pos_lit ^ 1)`
    refine wp_join_group (ts := [i64])
      (fun (old_t, ()) m0 => m0 = m ∧ old_t.toNat < 2 * s.core.cur_vars)
      (fun _ ⟨old_t, ⟨⟩⟩ m0 ⟨rfl, hold_lt⟩ => ?_)
      (fun Jt hJt => ?_)
    · have hnew_eq : (old_t ^^^ 1#64).toNat = old_t.toNat ^^^ 1 := by
        rw [BitVec.toNat_xor]; rfl
      have hnew_lt : (old_t ^^^ 1#64).toNat < 2 * s.core.cur_vars := by
        rw [hnew_eq]; have := fullInv_var_xor1 old_t.toNat; omega
      have hold_wv : old_t.toNat < s.scratch.walk_vals.length := by rw [hwvl]; omega
      have hnew_wv : (old_t ^^^ 1#64).toNat < s.scratch.walk_vals.length := by rw [hwvl]; omega
      have hold_w1 : old_t.toNat < s.scratch.work_stk1.length := by rw [hws1l]; omega
      have hold_w2 : old_t.toNat < s.scratch.work_stk2.length := by rw [hws2l]; omega
      let s1_0 : FullState := { s with scratch := { s.scratch with
        walk_vals := s.scratch.walk_vals.set old_t.toNat 0xFF#8 } }
      let s1 : FullState := { s1_0 with scratch := { s1_0.scratch with
        walk_vals := s1_0.scratch.walk_vals.set (old_t ^^^ 1#64).toNat 1#8 } }
      have hs1_len : s1.LengthsOk c := m6_len_set_wv (m6_len_set_wv hlen)
      have hs1_core : s1.core = s.core := rfl
      have hs1_pres : FullExtScratchPres s s1 := ⟨rfl, rfl⟩
      have hs1_scr : ∀ i < 2 * ncl.toNat,
          s1.scratch.scratch_buf[i]? = s.scratch.scratch_buf[i]? := fun _ _ => rfl
      c0_hsteps_nogrp
      rw [show s1.scratch.work_stk1[old_t.toNat]'hold_w1 =
          s.scratch.work_stk1[old_t.toNat]'hold_w1 from rfl,
        show s1.scratch.work_stk2[old_t.toNat]'hold_w2 =
          s.scratch.work_stk2[old_t.toNat]'hold_w2 from rfl]
      have hm_s1 : (FullMem c s1 ⋆ R) m := hm
      clear hm
      generalize hs1_eq : s1 = s1v at hs1_len hs1_core hs1_pres hs1_scr hm_s1
      clear hs1_eq s1 s1_0
      -- Join after Loop 1 (`old_t` occurrences) -> Loop 2 (`new_t` occurrences)
      refine wp_join_group (ts := [i64])
        (fun (ul1, ()) m1 => ∃ s_a : FullState,
          PreservesCoreSlice FullState.core s s_a ∧ s_a.LengthsOk c ∧
          ul1.toNat ≤ ncl.toNat ∧ FullExtScratchPres s s_a ∧
          (∀ i < 2 * ncl.toNat, s_a.scratch.scratch_buf[i]? = s.scratch.scratch_buf[i]?) ∧
          (FullMem c s_a ⋆ R) m1)
        (fun _ ⟨ul1, ⟨⟩⟩ m1 ⟨s_a, hcore_a, hs_a, hul1_le, hpres_a, hscr_a, hm_a⟩ => ?_)
        (fun J1 hJ1 => ?_)
      · -- Loop 2 (`new_t` occurrences)
        clear s1v hs1_len hs1_core hs1_pres hs1_scr hm_s1 hold_wv hnew_wv hold_w1 hold_w2
          pos_lit hpos_eq hpos_wv
        obtain hws1a := hs_a.scratch_ok.work_stk1_len
        obtain hws2a := hs_a.scratch_ok.work_stk2_len
        have hnew_w1 : (old_t ^^^ 1#64).toNat < s_a.scratch.work_stk1.length := by
          rw [hws1a]; omega
        have hnew_w2 : (old_t ^^^ 1#64).toNat < s_a.scratch.work_stk2.length := by
          rw [hws2a]; omega
        c0_hsteps_nogrp
        refine wp_join_group (ts := [i64])
          (fun (ul2, ()) m2 => ∃ s_b : FullState,
            PreservesCoreSlice FullState.core s s_b ∧ s_b.LengthsOk c ∧
            ul2.toNat ≤ ncl.toNat ∧ FullExtScratchPres s s_b ∧
            (∀ i < 2 * ncl.toNat, s_b.scratch.scratch_buf[i]? = s.scratch.scratch_buf[i]?) ∧
            (FullMem c s_b ⋆ R) m2)
          (fun _ ⟨ul2, ⟨⟩⟩ m2 ⟨s_b, hcore_b, hs_b, hul2_le, hpres_b, hscr_b, hm_b⟩ => by
            c0_hsteps
            exact hQ (ul2, ()) s_b m2 hcore_b hs_b ⟨hpres_b, hul2_le, hscr_b⟩ hm_b)
          (fun J2 hJ2 => ?_)
        c0_hsteps_nogrp
        · let off2 := (s_a.scratch.work_stk1[(old_t ^^^ 1#64).toNat]'hnew_w1).setWidth 64
          let len2 := (s_a.scratch.work_stk2[(old_t ^^^ 1#64).toNat]'hnew_w2).setWidth 64
          have hoff2_eq : off2.toNat =
              (s_a.scratch.work_stk1[(old_t ^^^ 1#64).toNat]'hnew_w1).toNat :=
            zext_toNat _ (by decide)
          have hlen2_eq : len2.toNat =
              (s_a.scratch.work_stk2[(old_t ^^^ 1#64).toNat]'hnew_w2).toNat :=
            zext_toNat _ (by decide)
          have hoff2_le : off2.toNat ≤ occ_cap.toNat := by
            rw [hoff2_eq]; exact by assumption
          have hlen2_le : len2.toNat ≤ occ_cap.toNat - off2.toNat := by
            have h1 : (s_a.scratch.work_stk2[(old_t ^^^ 1#64).toNat]'hnew_w2).toNat ≤
                (2 ^ 64 - (s_a.scratch.work_stk1[(old_t ^^^ 1#64).toNat]'hnew_w1).toNat +
                  occ_cap.toNat) % 2 ^ 64 := by assumption
            have hsub : (2 ^ 64 - (s_a.scratch.work_stk1[(old_t ^^^ 1#64).toNat]'hnew_w1).toNat +
                occ_cap.toNat) % 2 ^ 64 = occ_cap.toNat - off2.toNat := by
              have : 2 ^ 64 - off2.toNat + occ_cap.toNat =
                  2 ^ 64 + (occ_cap.toNat - off2.toNat) := by omega
              rw [← hoff2_eq, this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
            rw [hsub] at h1; omega
          refine wp_loop_safety_slice_pure (fullSafetySlice c) s_a R
            (fun sb (ulb, k, ()) =>
              k.toNat ≤ len2.toNat ∧ ulb.toNat ≤ ncl.toNat ∧ FullExtScratchPres s sb ∧
              (∀ i < 2 * ncl.toNat, sb.scratch.scratch_buf[i]? = s.scratch.scratch_buf[i]?))
            (fun (_, k, ()) => len2.toNat - k.toNat)
            (fun Jl2 hJl2 => by
              c0_hsteps
              exact hJl2 s_a (ul1, 0#64, ()) m1 hm_a rfl hs_a
                ⟨Nat.zero_le _, hul1_le, hpres_a, hscr_a⟩)
            (fun Jl2 sb (ulb, k, ()) mb hcoreb hsb ⟨hkle, hulb_le, hpresb, hscrb⟩ hmb hJl2 => ?_)
          dsimp only [fullSafetySlice] at hsb hmb
          have hceqb : sb.core = s.core := Eq.trans hcoreb hcore_a
          obtain hsblb := hsb.scratch_ok.scratch_buf_len
          c0_hsteps_nogrp
          · have hklt : k.toNat < len2.toNat := by
              have : k.toNat < (s_a.scratch.work_stk2[(old_t ^^^ 1#64).toNat]'hnew_w2).toNat := by
                assumption
              omega
            have hocc_idx : ((max_cl * 5#64 + off2) + k).toNat =
                5 * max_cl.toNat + off2.toNat + k.toNat := m6_occ_idx_64 (by omega)
            have hocc_lt : ((max_cl * 5#64 + off2) + k).toNat < sb.scratch.scratch_buf.length := by
              rw [hocc_idx, hsblb]; omega
            have hk1 : (k + 1#64).toNat = k.toNat + 1 := m6_add1_64 (by omega)
            let ci32 := sb.scratch.scratch_buf[((max_cl * 5#64 + off2) + k).toNat]'hocc_lt
            c0_hsteps_nogrp
            refine wp_join_group (ts := [i64])
              (fun (ul', ()) mb' => ∃ sb' : FullState,
                PreservesCoreSlice (fullSafetySlice c).coreProj sb sb' ∧ sb'.LengthsOk c ∧
                ul'.toNat ≤ ncl.toNat ∧ FullExtScratchPres s sb' ∧
                (∀ i < 2 * ncl.toNat, sb'.scratch.scratch_buf[i]? = s.scratch.scratch_buf[i]?) ∧
                (FullMem c sb' ⋆ R) mb')
              (fun _ ⟨ul', ⟨⟩⟩ mb' ⟨sb', hcore', hs', hul', hpres', hscr', hm'⟩ => by
                c0_hsteps
                exact hJl2 sb' (ul', k + 1#64, ()) mb' hm' (by dsimp only; omega) hcore' hs'
                  ⟨by omega, hul', hpres', hscr'⟩)
              (fun Jk2 hJk2 => ?_)
            c0_hsteps_nogrp
            · have hci_lt : ci32.toNat < ncl.toNat := by
                have hraw : (sb.scratch.scratch_buf[(max_cl.toNat * (5 : BitVec 64).toNat +
                    (s_a.scratch.work_stk1[(old_t ^^^ 1#64).toNat]'hnew_w1).toNat + k.toNat) %
                    2 ^ 64]'(by
                      rw [show (5 : BitVec 64).toNat = 5 from rfl,
                        Nat.mod_eq_of_lt (by omega), hsblb]; omega)).toNat < ncl.toNat := by
                  assumption
                have hidx_eq : ((max_cl * 5#64 + off2) + k).toNat =
                    (max_cl.toNat * (5 : BitVec 64).toNat +
                      (s_a.scratch.work_stk1[(old_t ^^^ 1#64).toNat]'hnew_w1).toNat + k.toNat) %
                      2 ^ 64 := by
                  rw [hocc_idx, hoff2_eq, show (5 : BitVec 64).toNat = 5 from rfl,
                    Nat.mod_eq_of_lt (by omega)]; omega
                simpa only [ci32, hidx_eq] using hraw
              have hsat_idx : ((max_cl <<< (1 : Nat)) + ci32.setWidth 64).toNat =
                  2 * max_cl.toNat + ci32.toNat := by
                have hz := zext_toNat ci32 (by decide : 32 ≤ 64)
                rw [BitVec.toNat_add, hsh_mc, hz, Nat.mod_eq_of_lt (by omega)]
              have hsat_lt : ((max_cl <<< (1 : Nat)) + ci32.setWidth 64).toNat <
                  sb.scratch.scratch_buf.length := by rw [hsat_idx, hsblb]; omega
              have hup_idx : (max_cl * 3 + ci32.setWidth 64).toNat =
                  3 * max_cl.toNat + ci32.toNat := m6_mul3_add_64 (by omega)
              have hup_lt : (max_cl * 3 + ci32.setWidth 64).toNat <
                  sb.scratch.scratch_buf.length := by rw [hup_idx, hsblb]; omega
              clear hQ hJ2 hJl2 hcore_a hs_a hm_a hws1a hws2a
              let sb_s1 : FullState := { sb with scratch := { sb.scratch with
                scratch_buf := sb.scratch.scratch_buf.set
                  ((max_cl <<< (1 : Nat)) + ci32.setWidth 64).toNat
                  (sb.scratch.scratch_buf[((max_cl <<< (1 : Nat)) +
                    ci32.setWidth 64).toNat]'hsat_lt + 1#32) } }
              have hsb1_core : PreservesCoreSlice (fullSafetySlice c).coreProj sb sb_s1 :=
                m6_core_set_sb rfl
              have hsb1_len : sb_s1.LengthsOk c := m6_len_set_sb hsb
              have hsb1_pres : FullExtScratchPres s sb_s1 := m6_extPres_set_sb hpresb
              have hsb1_scr : ∀ i < 2 * ncl.toNat,
                  sb_s1.scratch.scratch_buf[i]? = s.scratch.scratch_buf[i]? :=
                m6_scr_lo_set_st hscrb (m6_sat_hi hncl h5mc_bd _)
              c0_hsteps_nogrp
              have hm_sb1 : (FullMem c sb_s1 ⋆ R) m := hm
              clear hm
              generalize hsb1_eq : sb_s1 = sb1v at hsb1_core hsb1_len hsb1_pres hsb1_scr hm_sb1
              clear hsb1_eq sb_s1
              have hsbl1 := hsb1_len.scratch_ok.scratch_buf_len
              refine wp_join_group (ts := [i64])
                (fun (ul', ()) mb' => ∃ sb' : FullState,
                  PreservesCoreSlice (fullSafetySlice c).coreProj sb sb' ∧ sb'.LengthsOk c ∧
                  ul'.toNat ≤ ncl.toNat ∧ FullExtScratchPres s sb' ∧
                  (∀ i < 2 * ncl.toNat, sb'.scratch.scratch_buf[i]? = s.scratch.scratch_buf[i]?) ∧
                  (FullMem c sb' ⋆ R) mb')
                (fun _ ⟨ul', ⟨⟩⟩ mb' ⟨sb', hcore', hs', hul', hpres', hscr', hm'⟩ => by
                  c0_hsteps
                  exact hJk2 (ul', ()) mb' ⟨sb', hcore', hs', hul', hpres', hscr', hm'⟩)
                (fun Josc hJosc => ?_)
              c0_hsteps_nogrp
              · -- `osc == 0 && ulen > 0 && ulen <= ncl`
                have hul_pos : 0 < ulb.toNat := by c0_bound
                have hup_lt1 : (max_cl * 3 + ci32.setWidth 64).toNat <
                    sb1v.scratch.scratch_buf.length := by rw [hup_idx, hsbl1]; omega
                c0_hsteps_nogrp
                refine wp_join_group (ts := [i64])
                  (fun (ul', ()) mb' => ∃ sb' : FullState,
                    PreservesCoreSlice (fullSafetySlice c).coreProj sb sb' ∧ sb'.LengthsOk c ∧
                    ul'.toNat ≤ ncl.toNat ∧ FullExtScratchPres s sb' ∧
                    (∀ i < 2 * ncl.toNat, sb'.scratch.scratch_buf[i]? = s.scratch.scratch_buf[i]?) ∧
                    (FullMem c sb' ⋆ R) mb')
                  (fun _ ⟨ul', ⟨⟩⟩ mb' ⟨sb', hcore', hs', hul', hpres', hscr', hm'⟩ => by
                    c0_hsteps
                    exact hJosc (ul', ()) mb' ⟨sb', hcore', hs', hul', hpres', hscr', hm'⟩)
                  (fun Jup hJup => ?_)
                c0_hsteps_nogrp
                · let up32 :=
                      sb1v.scratch.scratch_buf[(max_cl * 3 + ci32.setWidth 64).toNat]'hup_lt1
                  have hup_lt_ul : up32.toNat < ulb.toNat := by
                    have hc' := hc
                    have hidx5 : ∀ hp : (old_t ^^^ (1 : BitVec 64)).toNat <
                        s_a.scratch.work_stk1.length,
                        (max_cl.toNat * (5 : BitVec 64).toNat +
                          (s_a.scratch.work_stk1[(old_t ^^^ (1 : BitVec 64)).toNat]'hp).toNat +
                          k.toNat) % 2 ^ 64 = ((max_cl * 5#64 + off2) + k).toNat := by
                      intro hp
                      have h1 :
                          (s_a.scratch.work_stk1[(old_t ^^^ (1 : BitVec 64)).toNat]'hp).toNat =
                            off2.toNat := hoff2_eq.symm
                      rw [h1, hocc_idx, show (5 : BitVec 64).toNat = 5 from rfl,
                        Nat.mod_eq_of_lt (by omega)]; omega
                    simp only [hidx5] at hc'
                    have hidx3 : (max_cl.toNat * (3 : BitVec 64).toNat + ci32.toNat) % 2 ^ 64 =
                        (max_cl * 3 + ci32.setWidth 64).toNat := by
                      rw [hup_idx, show (3 : BitVec 64).toNat = 3 from rfl,
                        Nat.mod_eq_of_lt (by omega : max_cl.toNat * 3 + ci32.toNat < 2 ^ 64)]
                      omega
                    simpa only [up32, ci32, hidx3] using hc'
                  have hul_sub : (ulb - 1#64).toNat = ulb.toNat - 1 := by
                    rw [BitVec.toNat_sub, show (1#64 : BitVec 64).toNat = 1 from rfl]; omega
                  have hul1_idx : ((max_cl <<< (2 : Nat)) + (ulb - 1#64)).toNat =
                      4 * max_cl.toNat + (ulb.toNat - 1) := by
                    rw [BitVec.toNat_add, hsh_mc4, hul_sub, Nat.mod_eq_of_lt (by omega)]
                  have hul1_lt : ((max_cl <<< (2 : Nat)) + (ulb - 1#64)).toNat <
                      sb1v.scratch.scratch_buf.length := by rw [hul1_idx, hsbl1]; omega
                  have hup_ul_idx : ((max_cl <<< (2 : Nat)) + up32.setWidth 64).toNat =
                      4 * max_cl.toNat + up32.toNat := by
                    have hz := zext_toNat up32 (by decide : 32 ≤ 64)
                    rw [BitVec.toNat_add, hsh_mc4, hz, Nat.mod_eq_of_lt (by omega)]
                  have hup_ul_lt : ((max_cl <<< (2 : Nat)) + up32.setWidth 64).toNat <
                      sb1v.scratch.scratch_buf.length := by rw [hup_ul_idx, hsbl1]; omega
                  c0_hsteps_nogrp
                  refine wp_join_group (ts := [])
                    (fun () m_l => ∃ sl : FullState,
                      PreservesCoreSlice (fullSafetySlice c).coreProj sb sl ∧ sl.LengthsOk c ∧
                      FullExtScratchPres s sl ∧
                      (∀ i < 2 * ncl.toNat, sl.scratch.scratch_buf[i]? =
                        s.scratch.scratch_buf[i]?) ∧
                      (FullMem c sl ⋆ R) m_l)
                    (fun _ () m_l ⟨sl, hcorel, hsl, hpresl, hscrl, hml⟩ => by
                      have hsbl_l := hsl.scratch_ok.scratch_buf_len
                      have hup_lt_l : (max_cl * 3 + ci32.setWidth 64).toNat <
                          sl.scratch.scratch_buf.length := by rw [hup_idx, hsbl_l]; omega
                      c0_hsteps
                      exact hJup (ulb - 1#64, ()) _ ⟨_,
                        m6_core_set_sb hcorel, m6_len_set_sb hsl, by omega,
                        m6_extPres_set_sb hpresl,
                        m6_scr_lo_set_st hscrl (m6_up_hi hncl h5mc_bd _), hm⟩)
                    (fun Jlast hJlast => ?_)
                  c0_hsteps_nogrp
                  · let last32 := sb1v.scratch.scratch_buf[
                        ((max_cl <<< (2 : Nat)) + (ulb - 1#64)).toNat]'hul1_lt
                    have hul1_raw : ((max_cl <<< (2 : Nat)).toNat +
                        (2 ^ 64 - (1 : BitVec 64).toNat + ulb.toNat)) % 2 ^ 64 =
                        ((max_cl <<< (2 : Nat)) + (ulb - 1#64)).toNat := by
                      rw [hul1_idx, hsh_mc4, show (1 : BitVec 64).toNat = 1 from rfl]
                      have : 4 * max_cl.toNat + (2 ^ 64 - 1 + ulb.toNat) =
                          2 ^ 64 + (4 * max_cl.toNat + (ulb.toNat - 1)) := by omega
                      rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
                    have hlast_lt : last32.toNat < ncl.toNat := by
                      simpa only [last32, hul1_raw] using hc
                    have hlast_idx : (max_cl * 3 + last32.setWidth 64).toNat =
                        3 * max_cl.toNat + last32.toNat := m6_mul3_add_64 (by omega)
                    have hlast_up_lt : (max_cl * 3 + last32.setWidth 64).toNat <
                        sb1v.scratch.scratch_buf.length := by rw [hlast_idx, hsbl1]; omega
                    c0_hsteps
                    exact hJlast () _ ⟨_,
                      m6_core_set_sb (m6_core_set_sb hsb1_core),
                      m6_len_set_sb (m6_len_set_sb hsb1_len),
                      m6_extPres_set_sb (m6_extPres_set_sb hsb1_pres),
                      m6_scr_lo_set_st (m6_scr_lo_set_st hsb1_scr
                        (m6_ul_hi32 hncl h5mc_bd _))
                        (m6_up_hi hncl h5mc_bd _), hm⟩
                  · exact hJlast () _ ⟨_,
                      m6_core_set_sb hsb1_core,
                      m6_len_set_sb hsb1_len,
                      m6_extPres_set_sb hsb1_pres,
                      m6_scr_lo_set_st hsb1_scr (m6_ul_hi32 hncl h5mc_bd _), hm⟩
                · exact hJup (ulb, ()) _
                    ⟨sb1v, hsb1_core, hsb1_len, hulb_le, hsb1_pres, hsb1_scr, hm_sb1⟩
              · exact hJosc (ulb, ()) _
                  ⟨sb1v, hsb1_core, hsb1_len, hulb_le, hsb1_pres, hsb1_scr, hm_sb1⟩
              · exact hJosc (ulb, ()) _
                  ⟨sb1v, hsb1_core, hsb1_len, hulb_le, hsb1_pres, hsb1_scr, hm_sb1⟩
            · exact hJk2 (ulb, ()) mb ⟨sb, rfl, hsb, hulb_le, hpresb, hscrb, hmb⟩
          · exact hJ2 (ulb, ()) mb ⟨sb, hceqb, hsb, hulb_le, hpresb, hscrb, hmb⟩
        · exact hJ2 (ul1, ()) m1 ⟨s_a, hcore_a, hs_a, hul1_le, hpres_a, hscr_a, hm_a⟩
        · exact hJ2 (ul1, ()) m1 ⟨s_a, hcore_a, hs_a, hul1_le, hpres_a, hscr_a, hm_a⟩
      · -- Loop 1 (`old_t` occurrences)
        clear hQ pos_lit hpos_eq hpos_wv hold_wv hnew_wv hnew_lt hnew_eq
        let off1 := (s.scratch.work_stk1[old_t.toNat]'hold_w1).setWidth 64
        let len1 := (s.scratch.work_stk2[old_t.toNat]'hold_w2).setWidth 64
        have hoff1_eq : off1.toNat = (s.scratch.work_stk1[old_t.toNat]'hold_w1).toNat :=
          zext_toNat _ (by decide)
        have hlen1_eq : len1.toNat = (s.scratch.work_stk2[old_t.toNat]'hold_w2).toNat :=
          zext_toNat _ (by decide)
        c0_hsteps_nogrp
        · have hoff1_le : off1.toNat ≤ occ_cap.toNat := by
            rw [hoff1_eq]; exact by assumption
          have hlen1_le : len1.toNat ≤ occ_cap.toNat - off1.toNat := by
            have h1 : (s.scratch.work_stk2[old_t.toNat]'hold_w2).toNat ≤
                (2 ^ 64 - (s.scratch.work_stk1[old_t.toNat]'hold_w1).toNat +
                  occ_cap.toNat) % 2 ^ 64 := by assumption
            have hsub : (2 ^ 64 - (s.scratch.work_stk1[old_t.toNat]'hold_w1).toNat +
                occ_cap.toNat) % 2 ^ 64 = occ_cap.toNat - off1.toNat := by
              have : 2 ^ 64 - off1.toNat + occ_cap.toNat =
                  2 ^ 64 + (occ_cap.toNat - off1.toNat) := by omega
              rw [← hoff1_eq, this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
            rw [hsub] at h1; omega
          refine wp_loop_safety_slice_pure (fullSafetySlice c) s1v R
            (fun sa (ula, k, ()) =>
              k.toNat ≤ len1.toNat ∧ ula.toNat ≤ ncl.toNat ∧ FullExtScratchPres s sa ∧
              (∀ i < 2 * ncl.toNat, sa.scratch.scratch_buf[i]? = s.scratch.scratch_buf[i]?))
            (fun (_, k, ()) => len1.toNat - k.toNat)
            (fun Jl1 hJl1 => by
              c0_hsteps
              exact hJl1 s1v (ulen, 0#64, ()) _ hm_s1 rfl hs1_len
                ⟨Nat.zero_le _, hulen, hs1_pres, hs1_scr⟩)
            (fun Jl1 sa (ula, k, ()) ma hcorea hsa ⟨hkle, hula_le, hpresa, hscra⟩ hma hJl1 => ?_)
          dsimp only [fullSafetySlice] at hsa hma
          have hceqa : sa.core = s.core := Eq.trans hcorea hs1_core
          obtain hsbla := hsa.scratch_ok.scratch_buf_len
          c0_hsteps_nogrp
          · have hklt : k.toNat < len1.toNat := by
              have : k.toNat < (s.scratch.work_stk2[old_t.toNat]'hold_w2).toNat := by assumption
              omega
            have hocc_idx : ((max_cl * 5#64 + off1) + k).toNat =
                5 * max_cl.toNat + off1.toNat + k.toNat := m6_occ_idx_64 (by omega)
            have hocc_lt : ((max_cl * 5#64 + off1) + k).toNat < sa.scratch.scratch_buf.length := by
              rw [hocc_idx, hsbla]; omega
            have hk1 : (k + 1#64).toNat = k.toNat + 1 := m6_add1_64 (by omega)
            let ci32 := sa.scratch.scratch_buf[((max_cl * 5#64 + off1) + k).toNat]'hocc_lt
            c0_hsteps_nogrp
            refine wp_join_group (ts := [i64])
              (fun (ul', ()) ma' => ∃ sa' : FullState,
                PreservesCoreSlice (fullSafetySlice c).coreProj sa sa' ∧ sa'.LengthsOk c ∧
                ul'.toNat ≤ ncl.toNat ∧ FullExtScratchPres s sa' ∧
                (∀ i < 2 * ncl.toNat, sa'.scratch.scratch_buf[i]? = s.scratch.scratch_buf[i]?) ∧
                (FullMem c sa' ⋆ R) ma')
              (fun _ ⟨ul', ⟨⟩⟩ ma' ⟨sa', hcore', hs', hul', hpres', hscr', hm'⟩ => by
                c0_hsteps
                exact hJl1 sa' (ul', k + 1#64, ()) ma' hm' (by dsimp only; omega) hcore' hs'
                  ⟨by omega, hul', hpres', hscr'⟩)
              (fun Jk1 hJk1 => ?_)
            c0_hsteps_nogrp
            · have hci_lt : ci32.toNat < ncl.toNat := by
                have hraw : (sa.scratch.scratch_buf[(max_cl.toNat * (5 : BitVec 64).toNat +
                    (s.scratch.work_stk1[old_t.toNat]'hold_w1).toNat + k.toNat) % 2 ^ 64]'(by
                      rw [show (5 : BitVec 64).toNat = 5 from rfl,
                        Nat.mod_eq_of_lt (by omega), hsbla]; omega)).toNat < ncl.toNat := by
                  assumption
                have hidx_eq : ((max_cl * 5#64 + off1) + k).toNat =
                    (max_cl.toNat * (5 : BitVec 64).toNat +
                      (s.scratch.work_stk1[old_t.toNat]'hold_w1).toNat + k.toNat) % 2 ^ 64 := by
                  rw [hocc_idx, hoff1_eq, show (5 : BitVec 64).toNat = 5 from rfl,
                    Nat.mod_eq_of_lt (by omega)]; omega
                simpa only [ci32, hidx_eq] using hraw
              have hsat_idx : ((max_cl <<< (1 : Nat)) + ci32.setWidth 64).toNat =
                  2 * max_cl.toNat + ci32.toNat := by
                have hz := zext_toNat ci32 (by decide : 32 ≤ 64)
                rw [BitVec.toNat_add, hsh_mc, hz, Nat.mod_eq_of_lt (by omega)]
              have hsat_lt : ((max_cl <<< (1 : Nat)) + ci32.setWidth 64).toNat <
                  sa.scratch.scratch_buf.length := by rw [hsat_idx, hsbla]; omega
              have hup_idx : (max_cl * 3 + ci32.setWidth 64).toNat =
                  3 * max_cl.toNat + ci32.toNat := m6_mul3_add_64 (by omega)
              have hup_lt : (max_cl * 3 + ci32.setWidth 64).toNat <
                  sa.scratch.scratch_buf.length := by rw [hup_idx, hsbla]; omega
              clear hJ1 hJl1 hs1_len hs1_core hs1_pres hs1_scr hm_s1
              c0_hsteps_nogrp
              refine wp_join_group (ts := [i64, i32])
                (fun (ul', _sc', ()) ma' => ∃ sa' : FullState,
                  PreservesCoreSlice (fullSafetySlice c).coreProj sa sa' ∧ sa'.LengthsOk c ∧
                  ul'.toNat ≤ ncl.toNat ∧ FullExtScratchPres s sa' ∧
                  (∀ i < 2 * ncl.toNat, sa'.scratch.scratch_buf[i]? = s.scratch.scratch_buf[i]?) ∧
                  (FullMem c sa' ⋆ R) ma')
                (fun _ ⟨ul', _sc', ⟨⟩⟩ ma' ⟨sa', hcore', hs', hul', hpres', hscr', hm'⟩ => by
                  c0_hsteps
                  exact hJk1 (ul', ()) ma' ⟨sa', hcore', hs', hul', hpres', hscr', hm'⟩)
                (fun Jgt0 hJgt0 => ?_)
              c0_hsteps_nogrp
              · let sa1 : FullState := { sa with scratch := { sa.scratch with
                  scratch_buf := sa.scratch.scratch_buf.set
                    ((max_cl <<< (1 : Nat)) + ci32.setWidth 64).toNat
                    (sa.scratch.scratch_buf[((max_cl <<< (1 : Nat)) +
                      ci32.setWidth 64).toNat]'hsat_lt - 1#32) } }
                have hsa1_core : PreservesCoreSlice (fullSafetySlice c).coreProj sa sa1 :=
                  m6_core_set_sb rfl
                have hsa1_len : sa1.LengthsOk c := m6_len_set_sb hsa
                have hsa1_pres : FullExtScratchPres s sa1 := m6_extPres_set_sb hpresa
                have hsa1_scr : ∀ i < 2 * ncl.toNat,
                    sa1.scratch.scratch_buf[i]? = s.scratch.scratch_buf[i]? :=
                  m6_scr_lo_set_st hscra (m6_sat_hi hncl h5mc_bd _)
                c0_hsteps_nogrp
                have hm_sa1 : (FullMem c sa1 ⋆ R) m := hm
                clear hm
                generalize hsa1_eq : sa1 = sa1v at hsa1_core hsa1_len hsa1_pres hsa1_scr hm_sa1
                clear hsa1_eq sa1
                have hsbl1 := hsa1_len.scratch_ok.scratch_buf_len
                have hup_lt1 : (max_cl * 3 + ci32.setWidth 64).toNat <
                    sa1v.scratch.scratch_buf.length := by rw [hup_idx, hsbl1]; omega
                refine wp_join_group (ts := [i64])
                  (fun (ul', ()) ma' => ∃ sa' : FullState,
                    PreservesCoreSlice (fullSafetySlice c).coreProj sa sa' ∧ sa'.LengthsOk c ∧
                    ul'.toNat ≤ ncl.toNat ∧ FullExtScratchPres s sa' ∧
                    (∀ i < 2 * ncl.toNat, sa'.scratch.scratch_buf[i]? =
                      s.scratch.scratch_buf[i]?) ∧
                    (FullMem c sa' ⋆ R) ma')
                  (fun _ ⟨ul', ⟨⟩⟩ ma' ⟨sa', hcore', hs', hul', hpres', hscr', hm'⟩ => by
                    c0_hsteps
                    exact hJgt0 (ul', _, ()) ma' ⟨sa', hcore', hs', hul', hpres', hscr', hm'⟩)
                  (fun Jsc0 hJsc0 => ?_)
                c0_hsteps_nogrp
                · have hula_lt : ula.toNat < ncl.toNat := by assumption
                  have hul_idx : ((max_cl <<< (2 : Nat)) + ula).toNat =
                      4 * max_cl.toNat + ula.toNat := by
                    rw [BitVec.toNat_add, hsh_mc4, Nat.mod_eq_of_lt (by omega)]
                  have hul_lt : ((max_cl <<< (2 : Nat)) + ula).toNat <
                      sa1v.scratch.scratch_buf.length := by rw [hul_idx, hsbl1]; omega
                  have hula1 : (ula + 1#64).toNat = ula.toNat + 1 := m6_add1_64 (by omega)
                  c0_hsteps
                  exact hJsc0 (ula + 1#64, ()) _ ⟨_,
                    m6_core_set_sb (m6_core_set_sb hsa1_core),
                    m6_len_set_sb (m6_len_set_sb hsa1_len),
                    by omega,
                    m6_extPres_set_sb (m6_extPres_set_sb hsa1_pres),
                    m6_scr_lo_set_st (m6_scr_lo_set_st hsa1_scr
                      (m6_up_hi hncl h5mc_bd _))
                      (m6_ul_hi hncl h5mc_bd _ (by omega)), hm⟩
                · exact hJsc0 (ula, ()) _
                    ⟨sa1v, hsa1_core, hsa1_len, hula_le, hsa1_pres, hsa1_scr, hm_sa1⟩
                · exact hJsc0 (ula, ()) _
                    ⟨sa1v, hsa1_core, hsa1_len, hula_le, hsa1_pres, hsa1_scr, hm_sa1⟩
                · exact hJsc0 (ula, ()) _
                    ⟨sa1v, hsa1_core, hsa1_len, hula_le, hsa1_pres, hsa1_scr, hm_sa1⟩
              · exact hJgt0 (ula, _, ()) ma ⟨sa, rfl, hsa, hula_le, hpresa, hscra, hma⟩
            · exact hJk1 (ula, ()) ma ⟨sa, rfl, hsa, hula_le, hpresa, hscra, hma⟩
          · exact hJ1 (ula, ()) ma ⟨sa, hceqa, hsa, hula_le, hpresa, hscra, hma⟩
        · exact hJ1 (ulen, ()) _ ⟨s1v, hs1_core, hs1_len, hulen, hs1_pres, hs1_scr, hm_s1⟩
        · exact hJ1 (ulen, ()) _ ⟨s1v, hs1_core, hs1_len, hulen, hs1_pres, hs1_scr, hm_s1⟩
    · c0_hsteps
      · exact hJt (pos_lit, ()) m ⟨rfl, by dsimp only [pos_lit]; rw [hpos_eq]; omega⟩
      · exact hJt (pos_lit ^^^ 1#64, ()) m ⟨rfl, by
          rw [BitVec.toNat_xor, show (1#64 : BitVec 64).toNat = 1 from rfl]
          dsimp only [pos_lit]; rw [hpos_eq]
          have := fullInv_var_xor1 (2 * (lit >>> (1 : Nat)).toNat); omega⟩

end WalkFlipProof

/-! ## 4. `full_walk_core_m6` (`Full.fullWalkSpec`) & `full_walk_m6` (`m6WalkSpec`) -/

section WalkCoreAndTopProof

open scoped FullArenaTactics

private def M6WithFuel (k : FullCoreState) (f : BitVec 64) : FullCoreState :=
  { k with fuel := f }

private theorem m6_withFuel_self (k : FullCoreState) : k = M6WithFuel k k.fuel := rfl

private theorem m6_withFuel_fuel (k : FullCoreState) (f : BitVec 64) :
    (M6WithFuel k f).fuel = f := rfl

private theorem m6_withFuel_upd {k0 k : FullCoreState} {f1 f2 : BitVec 64}
    (h : k = M6WithFuel k0 f1) : { k with fuel := f2 } = M6WithFuel k0 f2 := by
  cases h; rfl

private theorem m6_withFuel_inv {c : FullCfg} {F0 : CNF Nat} {s s' : FullState} {f : BitVec 64}
    (hinv : FullCoreInv c F0 s) (hs' : s'.LengthsOk c) (hc : s'.core = M6WithFuel s.core f) :
    FullCoreInv c F0 s' :=
  hinv.with_fuel_scratch_spec hs' hc

private theorem m6_lt_mod64 {x n : Nat} (hn : n < 2 ^ 64) (h : x < n % 2 ^ 64) : x < n := by
  rwa [Nat.mod_eq_of_lt hn] at h

private theorem m6_lt_2mod64 {x n : Nat} (hn : 2 * n < 2 ^ 64)
    (h : x < 2 * (n % 2 ^ 64) % 2 ^ 64) : x < 2 * n := by
  rwa [Nat.mod_eq_of_lt (by omega : n < 2 ^ 64), Nat.mod_eq_of_lt hn] at h

private theorem m6_sub1_64 {x : BitVec 64} (h : 0 < x.toNat) :
    (x - 1#64).toNat = x.toNat - 1 := by
  rw [BitVec.toNat_sub, show (1#64 : BitVec 64).toNat = 1 from rfl]; omega

private theorem m6_mul5_64 {x : BitVec 64} (h : 5 * x.toNat < 2 ^ 64) :
    (x * 5#64).toNat = 5 * x.toNat := by
  rw [BitVec.toNat_mul, show (5#64 : BitVec 64).toNat = 5 from rfl,
    Nat.mod_eq_of_lt (by omega)]; omega

private theorem m6_shl1_64 {x : BitVec 64} (h : 2 * x.toNat < 2 ^ 64) :
    (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]; omega

private theorem m6_len_upd_fuel {c : FullCfg} {s : FullState} {f : BitVec 64}
    (hs : s.LengthsOk c) :
    ({ s with core := { s.core with fuel := f } }).LengthsOk c :=
  ⟨{ hs.core_ok with }, hs.scratch_ok⟩

private theorem m6_walk_end_step {c : FullCfg} {s sp : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {Q : Post []}
    (hQ : ∀ fuel' sc' m',
      let s' : FullState := { core := { s.core with fuel := fuel' }, scratch := sc' }
      s'.LengthsOk c → fuel'.toNat ≤ s.core.fuel.toNat →
      FullExtScratchPres s s' → (FullMem c s' ⋆ R) m' → Q () m')
    (hcorep : sp.core = M6WithFuel s.core sp.core.fuel)
    (hsp : sp.LengthsOk c) (hfu : sp.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hpres : FullExtScratchPres s sp)
    (hm : (FullMem c { sp with scratch :=
      { sp.scratch with walk_cnt_stat := sp.scratch.walk_cnt_stat + 1 } } ⋆ R) m) :
    Q () m := by
  let sc_end : FullScratch := { sp.scratch with walk_cnt_stat := sp.scratch.walk_cnt_stat + 1 }
  have hsp_eq : { sp with scratch := sc_end } =
      { core := { s.core with fuel := sp.core.fuel }, scratch := sc_end } := by
    cases sp; dsimp only [M6WithFuel] at hcorep ⊢; rw [hcorep]
  refine hQ sp.core.fuel sc_end m ?_ hfu ?_ ?_
  · rw [← hsp_eq]; exact hsp.with_scratch { hsp.scratch_ok with }
  · rw [← hsp_eq]; exact hpres
  · rw [← hsp_eq]; exact hm

private theorem m6_core_set_wb {s0 s : FullState} {i : Nat} {v : BitVec 8}
    (hc : PreservesCoreSlice FullState.core s0 s) :
    PreservesCoreSlice FullState.core s0
      { s with scratch := { s.scratch with walk_best := s.scratch.walk_best.set i v } } := hc

private theorem m6_core_set_wv {s0 s : FullState} {i : Nat} {v : BitVec 8}
    (hc : PreservesCoreSlice FullState.core s0 s) :
    PreservesCoreSlice FullState.core s0
      { s with scratch := { s.scratch with walk_vals := s.scratch.walk_vals.set i v } } := hc

private theorem m6_core_set_ph {s0 s : FullState} {i : Nat} {v : BitVec 8}
    (hc : PreservesCoreSlice FullState.core s0 s) :
    PreservesCoreSlice FullState.core s0
      { s with scratch := { s.scratch with phases := s.scratch.phases.set i v } } := hc

private theorem m6_extPres_set_wb {s0 s : FullState} {i : Nat} {v : BitVec 8}
    (hp : FullExtScratchPres s0 s) :
    FullExtScratchPres s0
      { s with scratch := { s.scratch with walk_best := s.scratch.walk_best.set i v } } := hp

private theorem m6_extPres_set_wv {s0 s : FullState} {i : Nat} {v : BitVec 8}
    (hp : FullExtScratchPres s0 s) :
    FullExtScratchPres s0
      { s with scratch := { s.scratch with walk_vals := s.scratch.walk_vals.set i v } } := hp

private theorem m6_extPres_set_ph {s0 s : FullState} {i : Nat} {v : BitVec 8}
    (hp : FullExtScratchPres s0 s) :
    FullExtScratchPres s0
      { s with scratch := { s.scratch with phases := s.scratch.phases.set i v } } := hp

private theorem m6_extPres_set_tr {s0 s : FullState} {i : Nat} {v : BitVec 32}
    (hp : FullExtScratchPres s0 s) :
    FullExtScratchPres s0
      { s with scratch := { s.scratch with tarjan_reach := s.scratch.tarjan_reach.set i v } } := hp

private theorem m6_sb_set_wb {s0 s : FullState} {i : Nat} {v : BitVec 8}
    (hsb : s.scratch.scratch_buf = s0.scratch.scratch_buf) :
    ({ s with scratch :=
      { s.scratch with walk_best := s.scratch.walk_best.set i v } }).scratch.scratch_buf =
      s0.scratch.scratch_buf := hsb

private theorem m6_sb_set_wv {s0 s : FullState} {i : Nat} {v : BitVec 8}
    (hsb : s.scratch.scratch_buf = s0.scratch.scratch_buf) :
    ({ s with scratch :=
      { s.scratch with walk_vals := s.scratch.walk_vals.set i v } }).scratch.scratch_buf =
      s0.scratch.scratch_buf := hsb

private theorem m6_walkEntriesOk_set_tr {s : FullState} {n i : Nat} {v : BitVec 32}
    (hok : FullWalkEntriesOk s n) :
    FullWalkEntriesOk
      { s with scratch := { s.scratch with tarjan_reach := s.scratch.tarjan_reach.set i v } } n :=
  m6_walkEntriesOk_with_scratch hok rfl

private theorem m6_walkEntriesOk_fuel_rng {s0 sf sr : FullState} {n : Nat} {f1 f2 : BitVec 64}
    (hok : FullWalkEntriesOk sf n)
    (hcf : sf.core = M6WithFuel s0.core f1)
    (hcr : sr.core = M6WithFuel s0.core f2)
    (hrng : sr.scratch = { sf.scratch with rng_state := sr.scratch.rng_state }) :
    FullWalkEntriesOk sr n := by
  intro ci hci
  have h := hok ci hci
  have hsb := congrArg FullScratch.scratch_buf hrng
  dsimp only at hsb
  have hcv : sr.core.cur_vars = sf.core.cur_vars := by
    rw [hcr, hcf]; rfl
  have hal : sr.core.arena_len = sf.core.arena_len := by
    rw [hcr, hcf]; rfl
  have har : sr.core.arena = sf.core.arena := by
    rw [hcr, hcf]; rfl
  unfold FullWalkEntryOk at h ⊢
  dsimp only [fullArenaClauseRefs, fullArenaClauseRefsCore, fullArenaClauseGarb,
    fullArenaClauseGarbCore, fullArenaHdrCore] at h ⊢
  rw [hsb, hcv, hal, har]
  exact h

/-- `full_walk_core_m6` satisfies exact canonical `Full.fullWalkSpec` (adaptive ProbSAT V3b). -/
theorem full_walk_core_m6_wp (Γ : Env)
    (hCollect : ∀ a m Q X,
      m6WalkCollectSpec a m Q X → Γ "full_walk_collect_m6" [i64, i64, i64] [i64] a m Q X)
    (hBuildCsr : ∀ a m Q X,
      m6WalkBuildCsrSpec a m Q X → Γ "full_walk_build_csr_m6" [i64, i64, i64, i64] [i64] a m Q X)
    (hCbInv : ∀ a m Q X,
      m6WalkCbInvSpec a m Q X → Γ "full_walk_cb_inv_m6" [i64, i64, i64] [i64] a m Q X)
    (hRng : ∀ a m Q X,
      fullRngNextSpec a m Q X → Γ "full_rng_next" [i64] [i64] a m Q X)
    (hPick : ∀ a m Q X,
      m6WalkPickSpec a m Q X →
        Γ "full_walk_pick_m6" [i64, i64, i64, i64, i64, i64] [i32] a m Q X)
    (hFlip : ∀ a m Q X,
      m6WalkFlipSpec a m Q X →
        Γ "full_walk_flip_m6" [i64, i32, i64, i64, i64, i64] [i64] a m Q X) :
    ∀ a m Q X, fullWalkSpec a m Q X → Func.wp Γ full_walk_core_m6_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hm, hQ⟩
  obtain hlen := hinv.lengths
  obtain hmax : c.max_vars < 2 * dimacsBound := c.hmaxv
  obtain hsca : c.scratch_cap < dimacsBound := c.hscr
  unfold dimacsBound at hmax hsca
  obtain hcv_le := hlen.core_ok.cur_vars_le
  have hret_same : Q () m := hQ s.core.fuel s.scratch m hlen (Nat.le_refl _) ⟨rfl, rfl⟩ hm
  c0_hsteps_nogrp
  · exact hret_same
  · exact hret_same
  · have hcv_pos : 0 < s.core.cur_vars := Nat.pos_of_ne_zero fun h0 => by
      have hne : BitVec.ofNat 64 s.core.cur_vars ≠ 0#64 := by assumption
      exact hne (by rw [h0])
    have hcap_ge : 20 ≤ c.scratch_cap := by
      have : ¬c.scratch_cap % 2 ^ 64 < 20 := by assumption
      rw [Nat.mod_eq_of_lt (by omega)] at this; omega
    -- Join after `if (max_cl > 65536ULL) { max_cl = 65536ULL; }`
    refine wp_join_group (ts := [i64])
      (fun (max_cl, ()) m0 => m0 = m ∧ 5 * max_cl.toNat ≤ c.scratch_cap)
      (fun _ ⟨max_cl, ⟨⟩⟩ m0 ⟨rfl, h5mc⟩ => ?_)
      (fun Jmc hJmc => ?_)
    · let occ_cap := BitVec.ofNat 64 c.scratch_cap - max_cl * 5#64
      have h5mc_eq : (max_cl * 5#64).toNat = 5 * max_cl.toNat := m6_mul5_64 (by omega)
      have hocc_eq : occ_cap.toNat = c.scratch_cap - 5 * max_cl.toNat := by
        dsimp only [occ_cap]
        rw [BitVec.toNat_sub, bv64_ofNat_toNat (by omega), h5mc_eq]; omega
      have hcap_sum : 5 * max_cl.toNat + occ_cap.toNat ≤ c.scratch_cap := by omega
      c0_hsteps_nogrp
      c0_call hCollect
      refine ⟨c, s, R, ⟨rfl, ⟨F0, hinv⟩, hcap_sum⟩, hlen, hm, ?_⟩
      rintro ⟨ncl, ⟨⟩⟩ s1 m1 hcore1 hs1 ⟨hpres1, hncl_le, hok1⟩ hm1
      dsimp only [fullSafetySlice] at hs1 hm1
      have hceq1 : s1.core = s.core := hcore1
      have hinv1 : FullCoreInv c F0 s1 :=
        hinv.with_fuel_scratch_spec hs1 (by rw [hceq1])
      c0_hsteps_nogrp
      · have hs1_eq : s1 = { core := s.core, scratch := s1.scratch } := by
          cases s1; dsimp only at hceq1; subst hceq1; rfl
        exact hQ s.core.fuel s1.scratch m1 (hs1_eq ▸ hs1) (Nat.le_refl _)
          (hs1_eq ▸ hpres1) (hs1_eq ▸ hm1)
      · have hnl_eq : ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat =
            2 * s.core.cur_vars := by
          rw [BitVec.toNat_shiftLeft, bv64_ofNat_toNat (by omega), Nat.shiftLeft_eq,
            Nat.mod_eq_of_lt (by omega)]; omega
        obtain hws2l1 := hs1.scratch_ok.work_stk2_len
        c0_hsteps_nogrp
        -- Loop 1: sum `total_lits`
        refine wp_loop_group (ts := [i64, i64])
          (fun rem (_tot, li, ()) ml => ml = m1 ∧ li.toNat ≤ 2 * s.core.cur_vars ∧
            rem = 2 * s.core.cur_vars - li.toNat) ?_ ?_
        · rintro _ rem ⟨tot, li, ⟨⟩⟩ ml ih ⟨rfl, hli_le, rfl⟩
          c0_hsteps_nogrp
          · have hli_lt : li.toNat < 2 * s.core.cur_vars := by
              have h1 : li.toNat < 2 * (s.core.cur_vars % 2 ^ 64) % 2 ^ 64 := by assumption
              rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64),
                Nat.mod_eq_of_lt (by omega : 2 * s.core.cur_vars < 2 ^ 64)] at h1
              exact h1
            have hli_w2 : li.toNat < s1.scratch.work_stk2.length := by rw [hws2l1]; omega
            have hli1 : (li + 1#64).toNat = li.toNat + 1 := m6_add1_64 (by omega)
            c0_hsteps
            exact ih (2 * s.core.cur_vars - (li + 1#64).toNat) (_, li + 1#64, ()) ml
              (by rw [hli1]; omega) ⟨rfl, by rw [hli1]; omega, rfl⟩
          · -- Loop 2: init `walk_vals` and `walk_best`
            clear ih hli_le hws2l1 hnl_eq hinv1 hret_same hcap_ge hcv_pos h5mc_eq hocc_eq
            c0_hsteps_nogrp
            refine wp_loop_safety_slice_pure (fullSafetySlice c) s1 R
              (fun s2 (v, ()) =>
                v.toNat ≤ s.core.cur_vars ∧
                s2.scratch.scratch_buf = s1.scratch.scratch_buf ∧ FullExtScratchPres s s2)
              (fun (v, ()) => s.core.cur_vars - v.toNat)
              (fun J2 hJ2 => by
                c0_hsteps; exact hJ2 s1 (0#64, ()) ml hm1 rfl hs1 ⟨Nat.zero_le _, rfl, hpres1⟩)
              (fun J2 s2 (v, ()) m2 hcore2 hs2 ⟨hvle, hsb2, hpres2⟩ hm2 hJ2 => ?_)
            dsimp only [fullSafetySlice] at hs2 hm2
            have hceq2 : s2.core = s.core := Eq.trans hcore2 hceq1
            obtain hvl2 := hs2.core_ok.vals_len
            obtain hphl2 := hs2.scratch_ok.phases_len
            obtain hwvl2 := hs2.scratch_ok.walk_vals_len
            obtain hwbl2 := hs2.scratch_ok.walk_best_len
            c0_hsteps_nogrp
            · have hvlt : v.toNat < s.core.cur_vars := by
                have h1 : v.toNat < s.core.cur_vars % 2 ^ 64 := by assumption
                rwa [Nat.mod_eq_of_lt (by omega)] at h1
              have h2v : (v <<< (1 : Nat)).toNat = 2 * v.toNat := m6_shl1_64 (by omega)
              have h2v_v : (v <<< (1 : Nat)).toNat < s2.core.vals.length := by
                rw [h2v, hvl2]; omega
              have hv_ph : v.toNat < s2.scratch.phases.length := by rw [hphl2]; omega
              have h2v_wv : (v <<< (1 : Nat)).toNat < s2.scratch.walk_vals.length := by
                rw [h2v, hwvl2]; omega
              have h2v1_eq : ((v <<< (1 : Nat)) + 1#64).toNat = 2 * v.toNat + 1 := by
                rw [BitVec.toNat_add, h2v, show (1#64 : BitVec 64).toNat = 1 from rfl,
                  Nat.mod_eq_of_lt (by omega)]
              have h2v1_wv : ((v <<< (1 : Nat)) + 1#64).toNat < s2.scratch.walk_vals.length := by
                rw [h2v1_eq, hwvl2]; omega
              have hv_wb : v.toNat < s2.scratch.walk_best.length := by rw [hwbl2]; omega
              have hv1 : (v + 1#64).toNat = v.toNat + 1 := m6_add1_64 (by omega)
              c0_hsteps
              all_goals
                exact hJ2 _ (v + 1#64, ()) _ hm (by dsimp only; omega)
                  (m6_core_set_wb (m6_core_set_wv (m6_core_set_wv rfl)))
                  (m6_len_set_wb (m6_len_set_wv (m6_len_set_wv hs2)))
                  ⟨by omega, m6_sb_set_wb (m6_sb_set_wv (m6_sb_set_wv hsb2)),
                    m6_extPres_set_wb (m6_extPres_set_wv (m6_extPres_set_wv hpres2))⟩
            · -- Build CSR + compute `inv_q16` + clamp `max_flips` + main flip loop
              clear J2 hJ2 hvl2 hphl2 hwvl2 hwbl2
              have hinv2 : FullCoreInv c F0 s2 :=
                hinv.with_fuel_scratch_spec hs2 (by rw [hceq2])
              have hok2 : FullWalkEntriesOk s2 ncl.toNat :=
                m6_walkEntriesOk_of_scr_eq hok1 (Eq.trans hceq2 hceq1.symm)
                  (fun i _ => by rw [hsb2])
              c0_call hBuildCsr
              refine ⟨c, s2, R, ⟨rfl, ⟨F0, hinv2⟩, hncl_le, hcap_sum, hok2⟩, hs2, hm2, ?_⟩
              rintro ⟨ulen0, ⟨⟩⟩ s3 m3 hcore3 hs3 ⟨hpres3_step, hul0_le, hok3⟩ hm3
              dsimp only [fullSafetySlice] at hs3 hm3
              have hceq3 : s3.core = s.core := Eq.trans hcore3 hceq2
              have hpres3 : FullExtScratchPres s s3 := m6_extPres_trans hpres2 hpres3_step
              clear hinv2 hok2 hcore2 hceq2 hs2 hsb2 hpres2 hm2 hcore1 hceq1 hs1 hpres1 hok1 hm1
                hcore3 hpres3_step
              c0_hsteps_nogrp
              c0_call hCbInv
              intro inv_q16
              c0_hsteps_nogrp
              -- Clamp `max_flips` lower bound (`256`) then upper bound (`4096`)
              refine wp_join_group (ts := [i64]) (fun (_mf1, ()) m_f1 => m_f1 = m3)
                (fun _ ⟨mf1, ⟨⟩⟩ m_f1 hm_f1 => ?_) (fun Jf1 hJf1 => ?_)
              · subst m_f1
                c0_hsteps_nogrp
                refine wp_join_group (ts := [i64])
                  (fun (max_flips, ()) m_f2 => m_f2 = m3 ∧ max_flips.toNat ≤ 4096)
                  (fun _ ⟨max_flips, ⟨⟩⟩ m_f2 ⟨rfl, hmf_le⟩ => ?_)
                  (fun Jf2 hJf2 => ?_)
                · c0_hsteps_nogrp
                  -- Join after flip loop (`while (flip < max_flips && ulen > 0 && h->fuel > 0)`)
                  let sh_mc4 : (max_cl <<< (2 : Nat)).toNat = 4 * max_cl.toNat := by
                    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
                      Nat.mod_eq_of_lt (by omega)]; omega
                  refine wp_loop_break_group
                    (fun (_vf, _ulen_f, best_unsat, _tlen, best_pos, trail_valid, _flip, ()) mf =>
                      ∃ sf : FullState,
                        sf.core = M6WithFuel s.core sf.core.fuel ∧
                        sf.LengthsOk c ∧ sf.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                        best_pos.toNat ≤ 2 * s.core.cur_vars ∧
                        FullExtScratchPres s sf ∧ (FullMem c sf ⋆ R) mf)
                    (fun rem (_vf, ul, best_u, tlen, bpos, tval, flip, ()) mf =>
                      ∃ sf : FullState,
                        sf.core = M6WithFuel s.core sf.core.fuel ∧
                        sf.LengthsOk c ∧ sf.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                        ul.toNat ≤ ncl.toNat ∧ flip.toNat ≤ max_flips.toNat ∧
                        rem = max_flips.toNat - flip.toNat ∧
                        bpos.toNat ≤ tlen.toNat ∧ tlen.toNat ≤ 2 * s.core.cur_vars ∧
                        FullWalkEntriesOk sf ncl.toNat ∧ FullExtScratchPres s sf ∧
                        (FullMem c sf ⋆ R) mf)
                    ?_ ?_ ?_
                  · -- Post-flip-loop: flush `ftrail`, copy `wb` to `ph`, increment `walk_cnt_stat`
                    rintro _ ⟨_vf, _ul_f, best_u, _tlen, bpos, tval, _flip, ⟨⟩⟩ mf
                      ⟨sf, hcoref, hsf, hfu_f, hbpos_le, hpresf, hmf⟩
                    clear hCollect hBuildCsr hCbInv hRng hPick hFlip hinv hcap_sum hncl_le
                      hul0_le hmf_le sh_mc4 hceq3 hs3 hok3 hpres3 hm3 h5mc
                    -- Join after `if (trail_valid && best_pos > 0)`
                    refine wp_join_group (ts := [])
                      (fun () m_t => ∃ st : FullState,
                        st.core = M6WithFuel s.core st.core.fuel ∧
                        st.LengthsOk c ∧ st.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                        FullExtScratchPres s st ∧ (FullMem c st ⋆ R) m_t)
                      (fun _ () m_t ⟨st, hcoret, hst, hfu_t, hprest, hmt⟩ => ?_)
                      (fun Jt hJt => ?_)
                    · -- `if (best_unsat < init_unsat)` copy `wb` to `ph`, then `walk_cnt_stat++`
                      refine wp_join_group (ts := [i64])
                        (fun (_vp, ()) m_p => ∃ sp : FullState,
                          sp.core = M6WithFuel s.core sp.core.fuel ∧
                          sp.LengthsOk c ∧ sp.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                          FullExtScratchPres s sp ∧ (FullMem c sp ⋆ R) m_p)
                        (fun _ ⟨_vp, ⟨⟩⟩ m_p ⟨sp, hcorep, hsp, hfu_p, hpresp, hmp⟩ => by
                          c0_hsteps
                          exact m6_walk_end_step hQ hcorep hsp hfu_p hpresp hm)
                        (fun Jp hJp => ?_)
                      c0_hsteps_nogrp
                      · refine wp_loop_safety_slice_pure (fullSafetySlice c) st R
                          (fun sp (vp, ()) =>
                            vp.toNat ≤ s.core.cur_vars ∧ FullExtScratchPres s sp)
                          (fun (vp, ()) => s.core.cur_vars - vp.toNat)
                          (fun Jv hJv => by
                            c0_hsteps
                            exact hJv st (0#64, ()) m_t hmt rfl hst ⟨Nat.zero_le _, hprest⟩)
                          (fun Jv sp (vp, ()) mp hcorep hsp ⟨hvple, hpresp⟩ hmp hJv => ?_)
                        dsimp only [fullSafetySlice] at hsp hmp
                        have hceqp : sp.core = M6WithFuel s.core st.core.fuel :=
                          Eq.trans hcorep hcoret
                        obtain hwblp := hsp.scratch_ok.walk_best_len
                        obtain hphlp := hsp.scratch_ok.phases_len
                        c0_hsteps_nogrp
                        · have hvplt : vp.toNat < s.core.cur_vars :=
                            m6_lt_mod64 (by omega) (by assumption)
                          have hvp_wb : vp.toNat < sp.scratch.walk_best.length := by
                            rw [hwblp]; omega
                          have hvp_ph : vp.toNat < sp.scratch.phases.length := by
                            rw [hphlp]; omega
                          have hvp1 : (vp + 1#64).toNat = vp.toNat + 1 := m6_add1_64 (by omega)
                          c0_hsteps
                          exact hJv _ (vp + 1#64, ()) _ hm (by dsimp only; omega)
                            (m6_core_set_ph rfl) (m6_len_set_ph hsp)
                            ⟨by omega, m6_extPres_set_ph hpresp⟩
                        · exact hJp (vp, ()) mp ⟨sp, by rw [hceqp, m6_withFuel_fuel], hsp,
                            by rw [hceqp, m6_withFuel_fuel]; exact hfu_t, hpresp, hmp⟩
                      · exact hJp (_vf, ()) m_t ⟨st, hcoret, hst, hfu_t, hprest, hmt⟩
                    · -- Flush `ftrail[0 ..< best_pos)` if `trail_valid && best_pos > 0`
                      c0_hsteps_nogrp
                      · refine wp_loop_safety_slice_pure (fullSafetySlice c) sf R
                          (fun st (ti, ()) => ti.toNat ≤ bpos.toNat ∧ FullExtScratchPres s st)
                          (fun (ti, ()) => bpos.toNat - ti.toNat)
                          (fun Jti hJti => by
                            c0_hsteps
                            exact hJti sf (0#64, ()) mf hmf rfl hsf ⟨Nat.zero_le _, hpresf⟩)
                          (fun Jti st (ti, ()) mt hcoret hst ⟨htile, hprest⟩ hmt hJti => ?_)
                        dsimp only [fullSafetySlice] at hst hmt
                        have hceqt : st.core = M6WithFuel s.core sf.core.fuel :=
                          Eq.trans hcoret hcoref
                        obtain htrl := hst.scratch_ok.tarjan_reach_len
                        obtain hwbl := hst.scratch_ok.walk_best_len
                        c0_hsteps_nogrp
                        · have htilt : ti.toNat < bpos.toNat := by assumption
                          have hti_tr : ti.toNat < st.scratch.tarjan_reach.length := by
                            rw [htrl]; omega
                          have hti1 : (ti + 1#64).toNat = ti.toNat + 1 := m6_add1_64 (by omega)
                          c0_hsteps_nogrp
                          refine wp_join_group (ts := [])
                            (fun () mt' => ∃ st' : FullState,
                              PreservesCoreSlice (fullSafetySlice c).coreProj st st' ∧
                              st'.LengthsOk c ∧ FullExtScratchPres s st' ∧
                              (FullMem c st' ⋆ R) mt')
                            (fun _ () mt' ⟨st', hcore', hs', hpres', hm'⟩ => by
                              c0_hsteps
                              exact hJti st' (ti + 1#64, ()) mt' hm' (by dsimp only; omega) hcore'
                                hs' ⟨by omega, hpres'⟩)
                            (fun Jfv hJfv => ?_)
                          c0_hsteps_nogrp
                          · have hfv_lt : (st.scratch.tarjan_reach[ti.toNat]'hti_tr).toNat <
                                s.core.cur_vars := m6_lt_mod64 (by omega) (by assumption)
                            have hfv_wb : (st.scratch.tarjan_reach[ti.toNat]'hti_tr).toNat <
                                st.scratch.walk_best.length := by rw [hwbl]; omega
                            c0_hsteps
                            refine hJfv () _ ⟨_, ?_, ?_, ?_, hm⟩
                            · exact m6_core_set_wb rfl
                            · exact m6_len_set_wb hst
                            · exact m6_extPres_set_wb hprest
                          · exact hJfv () mt ⟨st, rfl, hst, hprest, hmt⟩
                        · exact hJt () mt ⟨st, by rw [hceqt, m6_withFuel_fuel], hst,
                            by rw [hceqt, m6_withFuel_fuel]; exact hfu_f, hprest, hmt⟩
                      · exact hJt () mf ⟨sf, hcoref, hsf, hfu_f, hpresf, hmf⟩
                      · exact hJt () mf ⟨sf, hcoref, hsf, hfu_f, hpresf, hmf⟩
                  · -- Flip loop body
                    rintro B _ rem ⟨vf, ul, best_u, tlen, bpos, tval, flip, ⟨⟩⟩ mf hB ih
                      ⟨sf, hcoref, hsf, hfu_f, hul_le, hfl_le, rfl, hbpos_le, htlen_le,
                        hokf, hpresf, hmf⟩
                    have hbreak_sf : B (vf, ul, best_u, tlen, bpos, tval, flip, ()) mf :=
                      hB (vf, ul, best_u, tlen, bpos, tval, flip, ()) mf
                        ⟨sf, hcoref, hsf, hfu_f, by omega, hpresf, hmf⟩
                    c0_hsteps_nogrp
                    · have hfl_lt : flip.toNat < max_flips.toNat := by assumption
                      have hul_pos : 0 < ul.toNat := by c0_bound
                      have hfu_pos : 0 < sf.core.fuel.toNat := by c0_bound
                      have hfu_sub : (sf.core.fuel - 1#64).toNat = sf.core.fuel.toNat - 1 :=
                        m6_sub1_64 hfu_pos
                      let sf1 : FullState :=
                        { sf with core := { sf.core with fuel := sf.core.fuel - 1#64 } }
                      have hsf1_core : sf1.core = M6WithFuel s.core (sf.core.fuel - 1#64) :=
                        m6_withFuel_upd hcoref
                      have hsf1_len : sf1.LengthsOk c := m6_len_upd_fuel hsf
                      have hsf1_fu : (sf.core.fuel - 1#64).toNat ≤ s.core.fuel.toNat := by omega
                      have hul_nz : ul ≠ 0#64 := fun h0 => by
                        subst h0; exact Nat.lt_irrefl 0 hul_pos
                      c0_hsteps_nogrp
                      c0_call hRng
                      refine ⟨c, sf1, R, rfl, hsf1_len, hm, ?_⟩
                      rintro ⟨rv, ⟨⟩⟩ sr mr hcorer hsr hrng_eq hmr
                      dsimp only [fullSafetySlice] at hsr hmr
                      have hsr_core : sr.core = M6WithFuel s.core (sf.core.fuel - 1#64) :=
                        Eq.trans hcorer hsf1_core
                      have hsr_fu : sr.core.fuel.toNat ≤ s.core.fuel.toNat := by
                        rw [hsr_core, m6_withFuel_fuel]; exact hsf1_fu
                      have hpresr : FullExtScratchPres s sr :=
                        m6_extPres_trans hpresf (m6_extPres_of_rng hrng_eq)
                      have hokr : FullWalkEntriesOk sr ncl.toNat :=
                        m6_walkEntriesOk_fuel_rng hokf hcoref hsr_core hrng_eq
                      have hinvr : FullCoreInv c F0 sr :=
                        m6_withFuel_inv hinv hsr hsr_core
                      obtain hsblr := hsr.scratch_ok.scratch_buf_len
                      have hrem_lt : (rv % ul).toNat < ul.toNat := by
                        rw [BitVec.toNat_umod]; exact Nat.mod_lt _ hul_pos
                      have hridx_eq : ((max_cl <<< (2 : Nat)) + rv % ul).toNat =
                          4 * max_cl.toNat + (rv % ul).toNat := by
                        rw [BitVec.toNat_add, sh_mc4, Nat.mod_eq_of_lt (by omega)]
                      have hridx_lt : ((max_cl <<< (2 : Nat)) + rv % ul).toNat <
                          sr.scratch.scratch_buf.length := by rw [hridx_eq, hsblr]; omega
                      c0_hsteps_nogrp
                      · exact hB (vf, ul, best_u, tlen, bpos, tval, flip, ()) mr
                          ⟨sr, by rw [hsr_core, m6_withFuel_fuel], hsr, hsr_fu, by omega,
                            hpresr, hmr⟩
                      · let ci32 := sr.scratch.scratch_buf[
                            ((max_cl <<< (2 : Nat)) + rv % ul).toNat]'hridx_lt
                        have hci_lt : ci32.toNat < ncl.toNat := by
                          have : ¬ncl.toNat ≤ ci32.toNat := by assumption
                          omega
                        c0_call hPick
                        refine ⟨c, sr, R,
                          ⟨rfl, ⟨F0, hinvr⟩, by rw [zext_toNat _ (by decide)]; exact hci_lt,
                            hncl_le, hcap_sum, hokr⟩, hsr, hmr, ?_⟩
                        rintro ⟨lit, ⟨⟩⟩ sp mp hcorep hsp ⟨hpresp_step, hsbp_eq, hlit_ok⟩ hmp
                        dsimp only [fullSafetySlice] at hsp hmp
                        have hsp_core : sp.core = M6WithFuel s.core (sf.core.fuel - 1#64) :=
                          Eq.trans hcorep hsr_core
                        have hpresp : FullExtScratchPres s sp :=
                          m6_extPres_trans hpresr hpresp_step
                        have hokp : FullWalkEntriesOk sp ncl.toNat :=
                          m6_walkEntriesOk_of_scr_eq hokr hcorep (fun i _ => by rw [hsbp_eq])
                        c0_hsteps_nogrp
                        · exact hB (vf, ul, best_u, tlen, bpos, tval, flip, ()) mp
                            ⟨sp, by rw [hsp_core, m6_withFuel_fuel], hsp,
                              by rw [hsp_core, m6_withFuel_fuel]; exact hsf1_fu,
                              by omega, hpresp, hmp⟩
                        · c0_call hFlip
                          refine ⟨c, sp, R, ⟨rfl, hncl_le, hul_le, hcap_sum⟩, hsp, hmp, ?_⟩
                          rintro ⟨ul_new, ⟨⟩⟩ sq mq hcoreq hsq ⟨hpresq_step, huln_le, hscrq_lo⟩ hmq
                          dsimp only [fullSafetySlice] at hsq hmq
                          have hsq_core : sq.core = M6WithFuel s.core (sf.core.fuel - 1#64) :=
                            Eq.trans hcoreq hsp_core
                          have hpresq : FullExtScratchPres s sq :=
                            m6_extPres_trans hpresp hpresq_step
                          have hokq : FullWalkEntriesOk sq ncl.toNat :=
                            m6_walkEntriesOk_of_scr_eq hokp hcoreq hscrq_lo
                          have hfl1 : (flip + 1#64).toNat = flip.toNat + 1 := m6_add1_64 (by omega)
                          clear hsf1_len hinvr hsblr hrem_lt hridx_eq hci_lt
                            hcorer hrng_eq hmr hpresr hokr hcorep hsp hpresp_step hsbp_eq
                            hlit_ok hmp hpresp hokp hcoreq hpresq_step hscrq_lo
                          -- Join after `if (trail_valid)` block
                          refine wp_join_group (ts := [i64, i64, .bool])
                            (fun (tlen1, bpos1, tval1, ()) m_tr => ∃ s_tr : FullState,
                              s_tr.core = M6WithFuel s.core (sf.core.fuel - 1#64) ∧
                              s_tr.LengthsOk c ∧ bpos1.toNat ≤ tlen1.toNat ∧
                              tlen1.toNat ≤ 2 * s.core.cur_vars ∧
                              FullWalkEntriesOk s_tr ncl.toNat ∧ FullExtScratchPres s s_tr ∧
                              (FullMem c s_tr ⋆ R) m_tr)
                            (fun _ ⟨tlen1, bpos1, tval1, ⟨⟩⟩ m_tr
                                ⟨s_tr, hcore_tr, hs_tr, hbpos1, htlen1, hok_tr,
                                  hpres_tr, hm_tr⟩ => ?_)
                            (fun Jtr hJtr => ?_)
                          · -- `if (ulen < best_unsat)` block -> `flip = flip + 1; ih`
                            refine wp_join_group (ts := [i64, i64, i64, i64, .bool])
                              (fun (_v2, best2, tlen2, bpos2, tval2, ()) m_u => ∃ s_u : FullState,
                                s_u.core = M6WithFuel s.core (sf.core.fuel - 1#64) ∧
                                s_u.LengthsOk c ∧ bpos2.toNat ≤ tlen2.toNat ∧
                                tlen2.toNat ≤ 2 * s.core.cur_vars ∧
                                FullWalkEntriesOk s_u ncl.toNat ∧ FullExtScratchPres s s_u ∧
                                (FullMem c s_u ⋆ R) m_u)
                              (fun _ ⟨v2, best2, tlen2, bpos2, tval2, ⟨⟩⟩ m_u
                                  ⟨s_u, hcore_u, hs_u, hbpos2, htlen2, hok_u,
                                    hpres_u, hm_u⟩ => by
                                c0_hsteps
                                exact ih (max_flips.toNat - (flip + 1#64).toNat)
                                  (v2, ul_new, best2, tlen2, bpos2, tval2, flip + 1#64, ()) m_u
                                  (by rw [hfl1]; omega)
                                  ⟨s_u, by rw [hcore_u, m6_withFuel_fuel], hs_u,
                                    by rw [hcore_u, m6_withFuel_fuel]; exact hsf1_fu,
                                    huln_le, by rw [hfl1]; omega, rfl, hbpos2, htlen2,
                                    hok_u, hpres_u, hm_u⟩)
                              (fun Ju hJu => ?_)
                            c0_hsteps_nogrp
                            · refine wp_join_group (ts := [i64, i64, i64, .bool])
                                (fun (_v2, tlen2, bpos2, tval2, ()) m_u => ∃ s_u : FullState,
                                  s_u.core = M6WithFuel s.core (sf.core.fuel - 1#64) ∧
                                  s_u.LengthsOk c ∧ bpos2.toNat ≤ tlen2.toNat ∧
                                  tlen2.toNat ≤ 2 * s.core.cur_vars ∧
                                  FullWalkEntriesOk s_u ncl.toNat ∧ FullExtScratchPres s s_u ∧
                                  (FullMem c s_u ⋆ R) m_u)
                                (fun _ ⟨v2, tlen2, bpos2, tval2, ⟨⟩⟩ m_u
                                    ⟨s_u, hcore_u, hs_u, hbpos2, htlen2, hok_u,
                                      hpres_u, hm_u⟩ => by
                                  c0_hsteps
                                  exact hJu (v2, ul_new, tlen2, bpos2, tval2, ()) m_u
                                    ⟨s_u, hcore_u, hs_u, hbpos2, htlen2, hok_u, hpres_u, hm_u⟩)
                                (fun Jtv hJtv => ?_)
                              c0_hsteps_nogrp
                              · exact hJtv (vf, tlen1, tlen1, tval1, ()) m_tr
                                  ⟨s_tr, hcore_tr, hs_tr, Nat.le_refl _, htlen1, hok_tr,
                                    hpres_tr, hm_tr⟩
                              · -- `else`: full copy `wb[v] = wv[v << 1]`
                                clear hCollect hBuildCsr hCbInv hRng hPick hFlip hinv hQ
                                  hB ih hbreak_sf hJu hsq hsq_core hpresq hokq hmq
                                refine wp_loop_safety_slice_pure (fullSafetySlice c) s_tr R
                                  (fun sc (vc, ()) =>
                                    vc.toNat ≤ s.core.cur_vars ∧
                                    sc.scratch.scratch_buf = s_tr.scratch.scratch_buf ∧
                                    FullExtScratchPres s sc)
                                  (fun (vc, ()) => s.core.cur_vars - vc.toNat)
                                  (fun Jc hJc => by
                                    c0_hsteps
                                    exact hJc s_tr (0#64, ()) m_tr hm_tr rfl hs_tr
                                      ⟨Nat.zero_le _, rfl, hpres_tr⟩)
                                  (fun Jc sc (vc, ()) mc hcorec hsc ⟨hvcle, hsbc, hpresc⟩
                                      hmc hJc => ?_)
                                dsimp only [fullSafetySlice] at hsc hmc
                                have hceqc : sc.core = M6WithFuel s.core (sf.core.fuel - 1#64) :=
                                  Eq.trans hcorec hcore_tr
                                obtain hwvlc := hsc.scratch_ok.walk_vals_len
                                obtain hwblc := hsc.scratch_ok.walk_best_len
                                c0_hsteps_nogrp
                                · have hvclt : vc.toNat < s.core.cur_vars :=
                                    m6_lt_mod64 (by omega) (by assumption)
                                  have h2vc : (vc <<< (1 : Nat)).toNat = 2 * vc.toNat :=
                                    m6_shl1_64 (by omega)
                                  have h2vc_wv : (vc <<< (1 : Nat)).toNat <
                                      sc.scratch.walk_vals.length := by rw [h2vc, hwvlc]; omega
                                  have hvc_wb : vc.toNat < sc.scratch.walk_best.length := by
                                    rw [hwblc]; omega
                                  have hvc1 : (vc + 1#64).toNat = vc.toNat + 1 :=
                                    m6_add1_64 (by omega)
                                  c0_hsteps
                                  exact hJc _ (vc + 1#64, ()) _ hm (by dsimp only; omega)
                                    (m6_core_set_wb rfl) (m6_len_set_wb hsc)
                                    ⟨by omega, m6_sb_set_wb hsbc, m6_extPres_set_wb hpresc⟩
                                · exact hJtv (vc, 0#64, 0#64, true, ()) mc
                                    ⟨sc, hceqc, hsc, Nat.zero_le _, Nat.zero_le _,
                                      m6_walkEntriesOk_of_scr_eq hok_tr hcorec
                                        (fun i _ => by rw [hsbc]),
                                      hpresc, hmc⟩
                            · exact hJu (vf, best_u, tlen1, bpos1, tval1, ()) m_tr
                                ⟨s_tr, hcore_tr, hs_tr, hbpos1, htlen1, hok_tr, hpres_tr, hm_tr⟩
                          · -- `if (trail_valid)` update or overflow flush
                            c0_hsteps_nogrp
                            · refine wp_join_group (ts := [i64, i64, .bool])
                                (fun (tlen1, bpos1, tval1, ()) m_tr => ∃ s_tr : FullState,
                                  s_tr.core = M6WithFuel s.core (sf.core.fuel - 1#64) ∧
                                  s_tr.LengthsOk c ∧ bpos1.toNat ≤ tlen1.toNat ∧
                                  tlen1.toNat ≤ 2 * s.core.cur_vars ∧
                                  FullWalkEntriesOk s_tr ncl.toNat ∧ FullExtScratchPres s s_tr ∧
                                  (FullMem c s_tr ⋆ R) m_tr)
                                (fun _ ⟨tlen1, bpos1, tval1, ⟨⟩⟩ m_tr h => by
                                  c0_hsteps; exact hJtr (tlen1, bpos1, tval1, ()) m_tr h)
                                (fun Jtr2 hJtr2 => ?_)
                              c0_hsteps_nogrp
                              · have htl_lt : tlen.toNat < 2 * s.core.cur_vars :=
                                  m6_lt_2mod64 (by omega) (by assumption)
                                obtain htrlq := hsq.scratch_ok.tarjan_reach_len
                                have htl_tr : tlen.toNat < sq.scratch.tarjan_reach.length := by
                                  rw [htrlq]; omega
                                have htl1 : (tlen + 1#64).toNat = tlen.toNat + 1 :=
                                  m6_add1_64 (by omega)
                                c0_hsteps
                                refine hJtr2 (tlen + 1#64, bpos, tval, ()) _
                                  ⟨_, ?_, ?_, by omega, by omega, ?_, ?_, hm⟩
                                · exact hsq_core
                                · exact m6_len_set_tr hsq
                                · exact m6_walkEntriesOk_set_tr hokq
                                · exact m6_extPres_set_tr hpresq
                              · -- Overflow flush `while (ti < best_pos)`
                                clear hCollect hBuildCsr hCbInv hRng hPick hFlip hinv hQ
                                  hB ih hbreak_sf hceq3 hs3 hok3 hpres3 hm3 hJtr
                                refine wp_loop_safety_slice_pure (fullSafetySlice c) sq R
                                  (fun sf2 (ti, ()) =>
                                    ti.toNat ≤ bpos.toNat ∧
                                    sf2.scratch.scratch_buf = sq.scratch.scratch_buf ∧
                                    FullExtScratchPres s sf2)
                                  (fun (ti, ()) => bpos.toNat - ti.toNat)
                                  (fun Jfl hJfl => by
                                    c0_hsteps
                                    exact hJfl sq (0#64, ()) mq hmq rfl hsq
                                      ⟨Nat.zero_le _, rfl, hpresq⟩)
                                  (fun Jfl sf2 (ti, ()) mf2 hcoref2 hsf2
                                      ⟨htile, hsbf2, hpresf2⟩ hmf2 hJfl => ?_)
                                dsimp only [fullSafetySlice] at hsf2 hmf2
                                have hceqf2 : sf2.core = M6WithFuel s.core (sf.core.fuel - 1#64) :=
                                  Eq.trans hcoref2 hsq_core
                                obtain htrlf2 := hsf2.scratch_ok.tarjan_reach_len
                                obtain hwblf2 := hsf2.scratch_ok.walk_best_len
                                c0_hsteps_nogrp
                                · have htilt : ti.toNat < bpos.toNat := by assumption
                                  have hti_tr : ti.toNat < sf2.scratch.tarjan_reach.length := by
                                    rw [htrlf2]; omega
                                  have hti1 : (ti + 1#64).toNat = ti.toNat + 1 :=
                                    m6_add1_64 (by omega)
                                  c0_hsteps_nogrp
                                  refine wp_join_group (ts := [])
                                    (fun () mf2' => ∃ sf2' : FullState,
                                      PreservesCoreSlice (fullSafetySlice c).coreProj sf2 sf2' ∧
                                      sf2'.LengthsOk c ∧
                                      sf2'.scratch.scratch_buf = sq.scratch.scratch_buf ∧
                                      FullExtScratchPres s sf2' ∧ (FullMem c sf2' ⋆ R) mf2')
                                    (fun _ () mf2' ⟨sf2', hcore', hs', hsb', hpres', hm'⟩ => by
                                      c0_hsteps
                                      exact hJfl sf2' (ti + 1#64, ()) mf2' hm'
                                        (by dsimp only; omega) hcore' hs' ⟨by omega, hsb', hpres'⟩)
                                    (fun Jfv hJfv => ?_)
                                  c0_hsteps_nogrp
                                  · have hfv_lt : (sf2.scratch.tarjan_reach[ti.toNat]'hti_tr).toNat
                                        < s.core.cur_vars := m6_lt_mod64 (by omega) (by assumption)
                                    have hfv_wb : (sf2.scratch.tarjan_reach[ti.toNat]'hti_tr).toNat
                                        < sf2.scratch.walk_best.length := by rw [hwblf2]; omega
                                    c0_hsteps
                                    refine hJfv () _ ⟨_, ?_, ?_, ?_, ?_, hm⟩
                                    · exact m6_core_set_wb rfl
                                    · exact m6_len_set_wb hsf2
                                    · exact m6_sb_set_wb hsbf2
                                    · exact m6_extPres_set_wb hpresf2
                                  · exact hJfv () mf2 ⟨sf2, rfl, hsf2, hsbf2, hpresf2, hmf2⟩
                                · exact hJtr2 (0#64, 0#64, false, ()) mf2
                                    ⟨sf2, hceqf2, hsf2, Nat.zero_le _, Nat.zero_le _,
                                      m6_walkEntriesOk_of_scr_eq hokq hcoref2
                                        (fun i _ => by rw [hsbf2]),
                                      hpresf2, hmf2⟩
                            · exact hJtr (tlen, bpos, tval, ()) mq
                                ⟨sq, hsq_core, hsq, hbpos_le, htlen_le, hokq, hpresq, hmq⟩
                    · exact hbreak_sf
                    · exact hbreak_sf
                    · exact hbreak_sf
                  · intro _ _ _ hL; c0_hsteps
                    exact hL max_flips.toNat (_, ulen0, ulen0, 0#64, 0#64, true, 0#64, ()) m_f2
                      ⟨s3, by rw [hceq3]; exact m6_withFuel_self _, hs3,
                        by rw [hceq3]; exact Nat.le_refl _, hul0_le,
                        Nat.zero_le _, (Nat.sub_zero _).symm, Nat.zero_le _, Nat.zero_le _,
                        hok3, hpres3, hm3⟩
                · c0_hsteps
                  · exact hJf2 (4096#64, ()) m3 ⟨rfl, by decide⟩
                  · exact hJf2 (mf1, ()) m3 ⟨rfl, by c0_bound⟩
              · c0_hsteps
                · exact hJf1 (256#64, ()) m3 rfl
                · exact hJf1 (_, ()) m3 rfl
        · intro _ hL; c0_hsteps
          exact hL (2 * s.core.cur_vars) (0#64, 0#64, ()) m1
            ⟨rfl, Nat.zero_le _, (Nat.sub_zero _).symm⟩
    · c0_hsteps
      · have h5 : 5 * (65536#64 : BitVec 64).toNat ≤ c.scratch_cap := by
          have hgt : 65536 < (BitVec.ofNat 64 c.scratch_cap / 10#64).toNat := by assumption
          rw [BitVec.toNat_udiv, bv64_ofNat_toNat (by omega),
            show (10#64 : BitVec 64).toNat = 10 from rfl] at hgt
          show 5 * 65536 ≤ c.scratch_cap; omega
        exact hJmc (65536#64, ()) m ⟨rfl, h5⟩
      · have h5 : 5 * (BitVec.ofNat 64 c.scratch_cap / 10#64).toNat ≤ c.scratch_cap := by
          rw [BitVec.toNat_udiv, bv64_ofNat_toNat (by omega),
            show (10#64 : BitVec 64).toNat = 10 from rfl]; omega
        exact hJmc (_, ()) m ⟨rfl, h5⟩

/-- Top-level `full_walk_m6` satisfies exact canonical `Full.fullWarmupSpec` (`m6WalkSpec`):
runs `full_warmup` at level 0 sparse mode (when unassigned & fuel > 0 & !oom), then
`full_walk_core_m6`. -/
theorem full_walk_m6_wp (Γ : Env)
    (hWarmup : ∀ a m Q X,
      fullWarmupSpec a m Q X → Γ "full_warmup" [i64] [] a m Q X)
    (hWalkCore : ∀ a m Q X,
      fullWalkSpec a m Q X → Γ "full_walk_core_m6" [i64] [] a m Q X) :
    ∀ a m Q X, m6WalkSpec a m Q X → Func.wp Γ full_walk_m6_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hdm0, hm, hQ⟩
  refine wp_join_group (ts := [])
    (fun () m1 => ∃ vals' flags' lvl' rsns' trl' tp' ftrl' fdec' te' prop' prob' unass' unfl'
        wvec' arena' wstk' wlen' wu' fuel' ctype' cref' c0' c1' oom' sc',
      let s1 : FullState :=
        { core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                trl := trl', trail_pos := tp', frame_trail := ftrl',
                                frame_dec := fdec', trail_end := te', propagated := prop',
                                probing := prob', unassigned := unass', unflushed := unfl',
                                wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
                                wusable := wu', fuel := fuel', confl_type := ctype',
                                confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
                                oom := oom' }
          scratch := sc' }
      FullCoreInv c F0 s1 ∧ FullArenaPermEq s.core s1.core ∧
      fuel'.toNat ≤ s.core.fuel.toNat ∧ FullExtScratchPres s s1 ∧
      (s.core.probing = 0#64 → prob' = 0#64) ∧ (FullMem c s1 ⋆ R) m1)
    (fun _ () m1 ⟨vals', flags', lvl', rsns', trl', tp', ftrl', fdec', te', prop', prob', unass',
        unfl', wvec', arena', wstk', wlen', wu', fuel', ctype', cref', c0', c1', oom', sc',
        hinv1, hperm1, hfu1, hpres1, hprob1, hm1⟩ => ?_)
    (fun Jw hJw => ?_)
  · let s1 : FullState :=
      { core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                              trl := trl', trail_pos := tp', frame_trail := ftrl',
                              frame_dec := fdec', trail_end := te', propagated := prop',
                              probing := prob', unassigned := unass', unflushed := unfl',
                              wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
                              wusable := wu', fuel := fuel', confl_type := ctype',
                              confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
                              oom := oom' }
        scratch := sc' }
    c0_call hWalkCore
    refine ⟨c, F0, s1, R, rfl, hinv1, hm1, ?_⟩
    intro fuel2 sc2 m2
    dsimp only
    intro hlen2 hfu2 hpres2 hm2
    let s2 : FullState :=
      { core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                              trl := trl', trail_pos := tp', frame_trail := ftrl',
                              frame_dec := fdec', trail_end := te', propagated := prop',
                              probing := prob', unassigned := unass', unflushed := unfl',
                              wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
                              wusable := wu', fuel := fuel2, confl_type := ctype',
                              confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
                              oom := oom' }
        scratch := sc2 }
    have hs2_eq : { s1 with core := { s1.core with fuel := fuel2 }, scratch := sc2 } = s2 := rfl
    have hinv2 : FullCoreInv c F0 s2 :=
      hinv1.with_fuel_scratch_spec (hs2_eq ▸ hlen2) rfl
    have hperm2 : FullArenaPermEq s.core s2.core := hperm1
    c0_hsteps
    exact hQ vals' flags' lvl' rsns' trl' tp' ftrl' fdec' te' prop' prob' unass' unfl'
      wvec' arena' wstk' wlen' wu' fuel2 ctype' cref' c0' c1' oom' sc2 m2
      hinv2 hperm2 (Nat.le_trans hfu2 hfu1) (m6_extPres_trans hpres1 (hs2_eq ▸ hpres2))
      hprob1 (hs2_eq ▸ hm2)
  · have hskip : Jw () m :=
      hJw () m ⟨s.core.vals, s.core.flags, s.core.lvl, s.core.rsns, s.core.trl, s.core.trail_pos,
        s.core.frame_trail, s.core.frame_dec, s.core.trail_end, s.core.propagated,
        s.core.probing, s.core.unassigned, s.core.unflushed, s.core.wvec, s.core.arena,
        s.core.wstk, s.core.wlen, s.core.wusable, s.core.fuel, s.core.confl_type,
        s.core.confl_ref, s.core.confl_lit0, s.core.confl_lit1, s.core.oom, s.scratch,
        hinv, m6_arenaPerm_refl s.core, Nat.le_refl _, ⟨rfl, rfl⟩, id, hm⟩
    c0_hsteps_nogrp
    · c0_call hWarmup
      refine ⟨c, F0, s, R, rfl, hinv, hdm0, hm, ?_⟩
      intro vals' flags' lvl' rsns' trl' tp' ftrl' fdec' te' prop' prob' unass' unfl'
        wvec' arena' wstk' wlen' wu' fuel' ctype' cref' c0' c1' oom' sc' m1
      dsimp only
      intro hinv1 hperm1 hfu1 hpres1 hprob1 hm1
      c0_hsteps
      exact hJw () m1 ⟨vals', flags', lvl', rsns', trl', tp', ftrl', fdec', te', prop', prob',
        unass', unfl', wvec', arena', wstk', wlen', wu', fuel', ctype', cref', c0', c1', oom',
        sc', hinv1, hperm1, hfu1, hpres1, hprob1, hm1⟩
    · exact hskip
    · exact hskip
    · exact hskip
    · exact hskip

end WalkCoreAndTopProof

end LeanQbe.T.Examples.Kissat.FullM6WalkParse
