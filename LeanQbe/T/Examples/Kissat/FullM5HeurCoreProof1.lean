module

public import LeanQbe.T.Examples.Kissat.FullM5HeurCore
public import LeanQbe.T.Examples.Kissat.FullSpec
import LeanQbe.T.Examples.Kissat.FullWalkExtLemmas1

/-!
# Kissat M5 Heuristics `Func.wp` Proofs — Part 1 (`FullM5HeurCoreProof1`)

Proves UNSAT-only parametric `Func.wp` contracts (`XPost := False`, `0` SAT proofs) for the
probing-isolation & analyzed-variable bumping functions:
1. `full_bump_analyzed_m5_wp` against canonical `Full.fullBumpAnalyzedSpec` (`probing == 0` guard,
   `FL_ACTIVE` filter, `stable == 0` guard on `full_queue_mtf`).
2. `fullRestoreBumpAnaSpec` + `full_restore_bump_ana_m5_wp` (compacting `work_stk1[0..min(res_sz,
   cur_vars))`, restoring `FullAnaMarksCov`, calling `full_bump_analyzed` + `full_clear_ana`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM5HeurCore

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.C0Step
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

/-! ## 1. `full_bump_analyzed_m5` (`Full.fullBumpAnalyzedSpec`) -/

section BumpAnalyzedProof

open FullWalkExtHelpers
open scoped FullArenaTactics FullWalkExtTactics

private def M5BumpAnaInv (c : FullCfg) (s s1 : FullState) (saved : Nat) : Prop :=
  s1.LengthsOk c ∧
  s1.core = { s.core with mrk := s1.core.mrk, min_clr_len := s1.core.min_clr_len } ∧
  s1.scratch = { s.scratch with work_stk1 := s1.scratch.work_stk1 } ∧
  saved ≤ s1.core.min_clr_len ∧ FullAnaMarksCov c s1 ∧
  (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 ≠ 0#8 →
    s1.core.mrk[v]?.getD 0#8 = s.core.mrk[v]?.getD 0#8) ∧
  (∀ k, saved ≤ k → k < s1.core.min_clr_len →
    (s1.scratch.work_stk1[k]?.getD 0#32).toNat < s.core.cur_vars ∧
    s.core.mrk[(s1.scratch.work_stk1[k]?.getD 0#32).toNat]?.getD 0#8 = 0#8)

private theorem m5BumpAnaInv_init {c : FullCfg} {s : FullState}
    (hlen : s.LengthsOk c) (hcov : FullAnaMarksCov c s) :
    M5BumpAnaInv c s s s.core.min_clr_len :=
  ⟨hlen, rfl, rfl, Nat.le_refl _, hcov, fun _ _ _ => rfl, fun _ hk1 hk2 => by omega⟩

private theorem m5BumpAnaInv_step {c : FullCfg} {s s1 : FullState} {saved ov : Nat}
    (hinv : M5BumpAnaInv c s s1 saved)
    (hov : ov < s.core.cur_vars)
    (hmrk0 : s1.core.mrk[ov]?.getD 0#8 = 0#8)
    (hmcl : s1.core.min_clr_len < s.core.cur_vars) :
    let ov32 := BitVec.ofNat 32 ov
    let s2 : FullState :=
      { core :=
          { s1.core with mrk := s1.core.mrk.set ov 1#8, min_clr_len := s1.core.min_clr_len + 1 }
        scratch :=
          { s1.scratch with work_stk1 := s1.scratch.work_stk1.set s1.core.min_clr_len ov32 } }
    M5BumpAnaInv c s s2 saved := by
  rcases hinv with ⟨hlen1, hcore1, hscr1, hsav, ⟨_, hnd, helem, hcov⟩, hpres, hnew⟩
  have hcv_le := hlen1.core_ok.cur_vars_le
  have hcv1 : s1.core.cur_vars = s.core.cur_vars := by rw [hcore1]
  have hmax : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmax
  have hov_max : ov < c.max_vars := by omega
  have hov32_toNat : (BitVec.ofNat 32 ov).toNat = ov := bv32_ofNat_toNat (by omega)
  have hmcl_lt_ws : s1.core.min_clr_len < s1.scratch.work_stk1.length := by
    rw [hlen1.scratch_ok.work_stk1_len]; omega
  have hov_lt_mrk : ov < s1.core.mrk.length := by rw [hlen1.core_ok.mrk_len]; omega
  refine ⟨⟨{ hlen1.core_ok with
      mrk_len := by simp [hlen1.core_ok.mrk_len]
      min_clr_len_le := by dsimp only; omega },
    { hlen1.scratch_ok with work_stk1_len := by simp [hlen1.scratch_ok.work_stk1_len] }⟩,
    by rw [hcore1], by rw [hscr1], by dsimp only; omega, ⟨by dsimp only; omega, ?_, ?_, ?_⟩,
    ?_, ?_⟩
  · exact nodup_map_take_append hmcl_lt_ws hnd fun k hk he =>
      (helem k hk).2 (by rw [he, hov32_toNat]; exact hmrk0)
  · intro k hk; dsimp only at hk ⊢
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hlt | rfl
    · rw [List.getElem?_set_ne (by omega)]
      have hne : (s1.scratch.work_stk1[k]?.getD 0#32).toNat ≠ ov := fun he =>
        (helem k hlt).2 (he ▸ hmrk0)
      exact ⟨(helem k hlt).1, by rw [List.getElem?_set_ne (Ne.symm hne)]; exact (helem k hlt).2⟩
    · rw [List.getElem?_set_self hmcl_lt_ws, Option.getD_some, hov32_toNat,
        List.getElem?_set_self hov_lt_mrk, Option.getD_some]
      exact ⟨by omega, by decide⟩
  · intro v hv hnz
    by_cases hveq : v = ov
    · subst v; refine ⟨s1.core.min_clr_len, by dsimp only; omega, ?_⟩
      dsimp only; rw [List.getElem?_set_self hmcl_lt_ws, Option.getD_some, hov32_toNat]
    · have hnz1 : s1.core.mrk[v]?.getD 0#8 ≠ 0#8 := by
        dsimp only at hnz; rwa [List.getElem?_set_ne (Ne.symm hveq)] at hnz
      obtain ⟨k, hk, hkeq⟩ := hcov v hv hnz1
      exact ⟨k, by dsimp only; omega, by
        dsimp only; rw [List.getElem?_set_ne (by omega)]; exact hkeq⟩
  · intro v hv hnz
    by_cases hveq : v = ov
    · subst v; rw [hpres ov hv hnz] at hmrk0; exact absurd hmrk0 hnz
    · dsimp only; rw [List.getElem?_set_ne (Ne.symm hveq)]; exact hpres v hv hnz
  · intro k hks hkm
    by_cases hkeq : k = s1.core.min_clr_len
    · subst k; dsimp only; rw [List.getElem?_set_self hmcl_lt_ws, Option.getD_some, hov32_toNat]
      refine ⟨hov, Classical.byContradiction fun hnz => by
        have heq := hpres ov hov_max hnz; rw [heq] at hmrk0; exact hnz hmrk0⟩
    · dsimp only at hkm ⊢; rw [List.getElem?_set_ne (Ne.symm hkeq)]
      exact hnew k hks (by omega)

private theorem m5BumpAnaInv_rollback {c : FullCfg} {s s1 : FullState} {saved : Nat}
    (hinv : M5BumpAnaInv c s s1 saved) (hlt : saved < s1.core.min_clr_len) :
    let mcl' := s1.core.min_clr_len - 1
    let rv := (s1.scratch.work_stk1[mcl']?.getD 0#32).toNat
    rv < s.core.cur_vars ∧
    let s2 : FullState :=
      { core := { s1.core with mrk := s1.core.mrk.set rv 0#8, min_clr_len := mcl' }
        scratch := s1.scratch }
    M5BumpAnaInv c s s2 saved := by
  rcases hinv with ⟨hlen1, hcore1, hscr1, hsav, ⟨hmcl_le, hnd, helem, hcov⟩, hpres, hnew⟩
  have hcv_le := hlen1.core_ok.cur_vars_le
  have hcv1 : s1.core.cur_vars = s.core.cur_vars := by rw [hcore1]
  have hmcl' : s1.core.min_clr_len - 1 < s1.core.min_clr_len := by omega
  obtain ⟨hrv_lt, hrv_mrk0⟩ := hnew (s1.core.min_clr_len - 1) (by omega) hmcl'
  refine ⟨hrv_lt, ⟨{ hlen1.core_ok with
      mrk_len := by simp [hlen1.core_ok.mrk_len]
      min_clr_len_le := by dsimp only; omega },
    hlen1.scratch_ok⟩, by rw [hcore1], hscr1, by dsimp only; omega,
    ⟨by dsimp only; omega, nodup_map_take_sub1 hnd, ?_, ?_⟩, ?_, ?_⟩
  · intro k hk; dsimp only at hk ⊢
    have hne := nodup_map_take_ne (by rw [hlen1.scratch_ok.work_stk1_len]; omega) hnd hk
    exact ⟨(helem k (by omega)).1,
      by rw [List.getElem?_set_ne (Ne.symm hne)]; exact (helem k (by omega)).2⟩
  · intro v hv hnz
    have hne : v ≠ (s1.scratch.work_stk1[s1.core.min_clr_len - 1]?.getD 0#32).toNat := by
      intro he; dsimp only at hnz; rw [he, List.getElem?_set_self (by
        rw [hlen1.core_ok.mrk_len]; omega), Option.getD_some] at hnz
      exact hnz rfl
    have hnz1 : s1.core.mrk[v]?.getD 0#8 ≠ 0#8 := by
      dsimp only at hnz; rwa [List.getElem?_set_ne (Ne.symm hne)] at hnz
    obtain ⟨k, hk, hkeq⟩ := hcov v hv hnz1
    refine ⟨k, ?_, hkeq⟩
    have hkne : k ≠ s1.core.min_clr_len - 1 := by
      intro hke; subst hke; exact hne hkeq.symm
    dsimp only; omega
  · intro v hv hnz
    have hne : v ≠ (s1.scratch.work_stk1[s1.core.min_clr_len - 1]?.getD 0#32).toNat := by
      intro he; rw [he] at hnz; exact hnz hrv_mrk0
    dsimp only; rw [List.getElem?_set_ne (Ne.symm hne)]; exact hpres v hv hnz
  · intro k hks hkm; exact hnew k hks (by dsimp only at hkm; omega)

private theorem m5_setWidth32_eq_zero {x : BitVec 8}
    (h : BitVec.setWidth 32 x = 0#32) : x = 0#8 := by
  ext i hi
  have h1 := congrArg (·[i]) h
  simpa [BitVec.getElem_setWidth, hi, show i < 32 by omega] using h1

/-- `full_bump_analyzed_m5` isolates probing (`h->probing != 0ULL` early return), filters
`FL_ACTIVE`, and skips `full_queue_mtf` when `stable != 0`, satisfying canonical
`Full.fullBumpAnalyzedSpec`. -/
theorem full_bump_analyzed_m5_wp (Γ : Env)
    (hBump : ∀ a m Q X, fullBumpVarSpec a m Q X → Γ "full_bump_var" [i64, i32] [] a m Q X)
    (hMtf : ∀ a m Q X, fullQueueMtfSpec a m Q X → Γ "full_queue_mtf" [i64, i32] [] a m Q X)
    (hDecay : ∀ a m Q X, fullBumpDecaySpec a m Q X → Γ "full_bump_decay" [i64] [] a m Q X) :
    ∀ a m Q X, fullBumpAnalyzedSpec a m Q X →
      Func.wp Γ full_bump_analyzed_m5_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hcov0, hm, hQ⟩
  obtain hmcl_cv := hcov0.1
  c0_steps
  · exact hQ s.core.mrk s.core.min_clr_len s.scratch m hlen hcov0 ⟨rfl, rfl⟩ rfl hm
  · c0_to_group
    obtain hmax : c.max_vars < 2 * dimacsBound := c.hmaxv
    obtain haca : c.arena_cap < 2 * dimacsBound := c.harena
    unfold dimacsBound at hmax haca
    obtain hcv_le := hlen.core_ok.cur_vars_le
    let saved := s.core.min_clr_len
    let lim := BitVec.ofNat 64 saved * 10
    have hlim_eq : lim.toNat = saved * 10 := by
      have hs32 : saved < 2 ^ 30 := by omega
      dsimp only [lim]
      rw [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : saved < 2 ^ 64),
        show (10 : BitVec 64).toNat = 10 from rfl, Nat.mod_eq_of_lt (by omega)]
    refine wp_loop_inv
      (fun (i, ()) m1 => i.toNat ≤ s.core.tmp_len ∧ ∃ s1 : FullState,
        M5BumpAnaInv c s s1 saved ∧ (FullMem c s1 ⋆ R) m1)
      (fun (i, ()) _ => s.core.tmp_len - i.toNat) (fun Jloop hLoop => ?_)
      (fun Jloop (i, ()) m1 ⟨hle_tl, s1, hinv1, hm1⟩ hLoop => ?_)
    · c0_steps; exact hLoop _ _ ⟨by simp, s, m5BumpAnaInv_init hlen hcov0, hm⟩
    · have hinv1_pk := hinv1
      rcases hinv1 with ⟨hlen1, hcore1, hscr1, hsav1, hcov1, hpres1, hnew1⟩
      have hcveq : s1.core.cur_vars = s.core.cur_vars := by rw [hcore1]
      have hmcl1 : s1.core.min_clr_len ≤ s.core.cur_vars := by rw [← hcveq]; exact hcov1.1
      have hteq : s1.core.tmp_len = s.core.tmp_len := by rw [hcore1]
      have hareq : s1.core.arena_len = s.core.arena_len := by rw [hcore1]
      obtain hcv_le1 := hlen1.core_ok.cur_vars_le
      obtain harl1 := hlen1.core_ok.arena_len_arr
      obtain hale1 := hlen1.core_ok.arena_len_le
      obtain htll1 := hlen1.core_ok.tmp_len_arr
      obtain htl_le1 := hlen1.core_ok.tmp_len_le
      obtain hrsnl1 := hlen1.core_ok.rsns_len
      obtain hlvll1 := hlen1.core_ok.lvl_len
      obtain hmrl1 := hlen1.core_ok.mrk_len
      obtain hwsl1 := hlen1.scratch_ok.work_stk1_len
      rw [Blocks.get_here]; try dsimp only
      refine wp_join_group (ts := [])
        (fun _ m1 => ∃ s1 : FullState, M5BumpAnaInv c s s1 saved ∧ (FullMem c s1 ⋆ R) m1)
        (fun J1 _ m1 ⟨s1, hinv1, hm1⟩ => ?_)
        (fun J1 hJ1 => ?_)
      · clear hm hlen hmcl_cv hcov0
        rw [Blocks.get_here]; try dsimp only
        c0_to_group
        refine wp_join_group (ts := [])
          (fun _ m2 => ∃ s2 : FullState, M5BumpAnaInv c s s2 saved ∧ (FullMem c s2 ⋆ R) m2)
          (fun J2 _ m2 ⟨s2, hinv2, hm2⟩ => ?_)
          (fun J2 hJ2 => ?_)
        · rw [Blocks.get_here]; try dsimp only
          c0_to_group
          refine wp_loop_inv
            (fun (iv, ()) m3 => iv.toNat ≤ s2.core.min_clr_len ∧ ∃ s3 : FullState,
              s3.LengthsOk c ∧
              s3.core = { s.core with mrk := s2.core.mrk, min_clr_len := s2.core.min_clr_len } ∧
              s3.scratch.work_stk1 = s2.scratch.work_stk1 ∧
              s3.scratch.work_stk2 = s.scratch.work_stk2 ∧
              s3.scratch.last_learned = s.scratch.last_learned ∧
              s3.scratch.extend_len = s.scratch.extend_len ∧
              (FullMem c s3 ⋆ R) m3)
            (fun (iv, ()) _ => s2.core.min_clr_len - iv.toNat) (fun J3 hJ3 => ?_)
            (fun J3 (iv, ()) m3 ⟨hiv_le, s3, hlen3, hcore3, hws3, hws23, hll3, hel3, hm3⟩ hJ3 => ?_)
          · c0_steps
            refine hJ3 _ _ ⟨by simp, s2, hinv2.1, hinv2.2.1,
              by rw [hinv2.2.2.1], by rw [hinv2.2.2.1], by rw [hinv2.2.2.1],
              by rw [hinv2.2.2.1], hm2⟩
          · obtain hwsl3 := hlen3.scratch_ok.work_stk1_len
            obtain hcv_le3 := hlen3.core_ok.cur_vars_le
            obtain hfll3 := hlen3.core_ok.flags_len
            c0_steps
            · have hmcl2 : s2.core.min_clr_len ≤ s.core.cur_vars := by
                have hcv2 : s2.core.cur_vars = s.core.cur_vars := by rw [hinv2.2.1]
                rw [← hcv2]; exact hinv2.2.2.2.2.1.1
              have hiv_lt : iv.toNat < s2.core.min_clr_len := by
                rw [hcore3, Nat.mod_eq_of_lt (by omega : s2.core.min_clr_len < 2 ^ 64)] at hc
                exact hc
              have hiv_ws : iv.toNat < s3.scratch.work_stk1.length := by rw [hwsl3]; omega
              let bv := s3.scratch.work_stk1[iv.toNat]'hiv_ws
              refine wp_load_of (FullArenaTactics.c0_load_full_work_stk1 (s := s3) hiv_ws hm3) ?_
              refine wp_join_group (ts := [])
                (fun _ m5 => ∃ s5 : FullState, s5.LengthsOk c ∧
                  s5.core = { s.core with mrk := s2.core.mrk, min_clr_len := s2.core.min_clr_len } ∧
                  s5.scratch.work_stk1 = s2.scratch.work_stk1 ∧
                  s5.scratch.work_stk2 = s.scratch.work_stk2 ∧
                  s5.scratch.last_learned = s.scratch.last_learned ∧
                  s5.scratch.extend_len = s.scratch.extend_len ∧
                  (FullMem c s5 ⋆ R) m5)
                (fun Jw _ m5 ⟨s5, hs5, hcore5, hws5, hws25, hll5, hel5, hm5⟩ => by
                  c0_steps
                  exact hJ3 _ _ (by c0_bound)
                    ⟨by c0_bound, s5, hs5, hcore5, hws5, hws25, hll5, hel5, hm5⟩)
                (fun Jw hJw => ?_)
              c0_steps
              · c0_call hBump
                refine ⟨c, s3, R, rfl, hlen3, hm3, ?_⟩
                intro _ s4 m4 hcore4 hs4 hp4 hm4
                have heq4 := fullCoreState_agrees_with_scratch hcore4
                change (FullMem c s4 ⋆ R) m4 at hm4
                refine wp_unroll_group fun Jm hJm => ?_
                c0_steps
                · c0_call hMtf
                  refine ⟨c, s4, R, rfl, hs4, hm4, ?_⟩
                  intro _ s5 m5 hcore5 hs5 hp5 hm5
                  have heq5 := fullCoreState_agrees_with_scratch hcore5
                  change (FullMem c s5 ⋆ R) m5 at hm5
                  c0_steps; apply hJm; rw [Blocks.get_here]; c0_steps
                  exact hJw _ _ ⟨s5, hs5, by rw [heq5, heq4, hcore3],
                    by rw [hp5.2.1, hp4.2.1, hws3], by rw [hp5.2.2.1, hp4.2.2.1, hws23],
                    by rw [hp5.1.1, hp4.1.1, hll3], by rw [hp5.1.2, hp4.1.2, hel3], hm5⟩
                · exact hJw _ _ ⟨s4, hs4, by rw [heq4, hcore3],
                    by rw [hp4.2.1, hws3], by rw [hp4.2.2.1, hws23],
                    by rw [hp4.1.1, hll3], by rw [hp4.1.2, hel3], hm4⟩
              · exact hJw _ _ ⟨s3, hlen3, hcore3, hws3, hws23, hll3, hel3, hm3⟩
              · exact hJw _ _ ⟨s3, hlen3, hcore3, hws3, hws23, hll3, hel3, hm3⟩
            · c0_call hDecay
              refine ⟨c, s3, R, rfl, hlen3, hm3, ?_⟩
              intro _ s4 m4 hcore4 hs4 hp4 hm4
              have heq4 := fullCoreState_agrees_with_scratch hcore4
              have hcore4' : s4.core =
                  { s.core with mrk := s2.core.mrk, min_clr_len := s2.core.min_clr_len } := by
                rw [heq4, hcore3]
              have hcov2 := hinv2.2.2.2.2.1
              have hs4_ws : s4.scratch.work_stk1 = s2.scratch.work_stk1 := by rw [hp4.2.1, hws3]
              have heq_st : FullState.mk
                  { s.core with mrk := s4.core.mrk, min_clr_len := s4.core.min_clr_len }
                  s4.scratch = s4 := by
                cases s4; dsimp only at hcore4' ⊢; congr 1; rw [hcore4']
              exact hQ s4.core.mrk s4.core.min_clr_len s4.scratch m4
                (by rw [heq_st]; exact hs4)
                (by
                  rw [heq_st]; unfold FullAnaMarksCov at hcov2 ⊢
                  rw [hs4_ws, hcore4', ← hinv2.2.1]; exact hcov2)
                ⟨by rw [hp4.1.1, hll3], by rw [hp4.1.2, hel3]⟩
                (by rw [hp4.2.2.1, hws23])
                (by rw [heq_st]; exact hm4)
        · c0_to_group
          · refine wp_loop_inv
              (fun _ m2 => ∃ s2 : FullState, M5BumpAnaInv c s s2 saved ∧ (FullMem c s2 ⋆ R) m2)
              (fun _ m2 => ((loadVal m2 i64 (c.hdr + 272)).getD 0#64).toNat - saved)
              (fun Jrb hJrb => ?_) (fun Jrb () m2 ⟨s2, hinv2, hm2⟩ hJrb => ?_)
            · c0_steps; exact hJrb _ _ ⟨s1, hinv1, hm1⟩
            · have hinv2_pk := hinv2
              rcases hinv2 with ⟨hlen2, hcore2, hscr2, hsav2, hcov2, hpres2, hnew2⟩
              have hcveq2 : s2.core.cur_vars = s.core.cur_vars := by rw [hcore2]
              have hmcl2 : s2.core.min_clr_len ≤ s.core.cur_vars := by rw [← hcveq2]; exact hcov2.1
              obtain hcv_le2 := hlen2.core_ok.cur_vars_le
              obtain hwsl2 := hlen2.scratch_ok.work_stk1_len
              obtain hmrl2 := hlen2.core_ok.mrk_len
              rw [Blocks.get_here]; dsimp only
              rw [wp_let_add64_2]; dsimp only
              refine wp_load_of (FullArenaTactics.load_full_min_clr_len hm2) ?_
              rw [wp_let_ugt64_2]; dsimp only
              refine wp_jnz_of (fun hc_gt => ?_) (fun _ => ?_)
              · simp only [Arg.val_var] at hc_gt
                have hsav_lt : saved < s2.core.min_clr_len := by
                  have h1 : (BitVec.ofNat 64 saved).toNat <
                      (BitVec.ofNat 64 s2.core.min_clr_len).toNat := by
                    simpa [BitVec.ult] using hc_gt
                  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
                    Nat.mod_eq_of_lt (by omega)] at h1
                  exact h1
                have hmcl_sub : (BitVec.ofNat 64 s2.core.min_clr_len - 1).toNat =
                    s2.core.min_clr_len - 1 := bv64_ofNat_sub1 (by omega) (by omega)
                have hrv_idx : (BitVec.ofNat 64 (s2.core.min_clr_len - 1)).toNat =
                    s2.core.min_clr_len - 1 := bv64_ofNat_toNat (by omega)
                obtain ⟨hrv_lt, hinv3⟩ := m5BumpAnaInv_rollback hinv2_pk hsav_lt
                have hrv_lt' : (s2.scratch.work_stk1[s2.core.min_clr_len - 1]'(by
                    rw [hwsl2]; omega)).toNat < s2.core.cur_vars := by
                  rw [hcveq2]; simpa [List.getElem?_eq_getElem (by rw [hwsl2]; omega :
                    s2.core.min_clr_len - 1 < s2.scratch.work_stk1.length)] using hrv_lt
                rw [wp_let_add64_2]; dsimp only
                refine wp_load_of (FullArenaTactics.load_full_min_clr_len hm2) ?_
                rw [wp_let_sub64_2, wp_let_add64_2]; dsimp only
                refine wp_store_sep (FullArenaTactics.c0_store_full_min_clr_len _ hm2) ?_
                intro m2' hm2'
                simp only [Arg.val_var, Arg.val_imm] at hm2'
                rw [hmcl_sub] at hm2'
                let s2' : FullState :=
                  { s2 with core := { s2.core with min_clr_len := s2.core.min_clr_len - 1 } }
                have hm2'' : (FullMem c s2' ⋆ R) m2' := hm2'
                rw [wp_let_add64_2]; dsimp only
                refine wp_load_of (FullArenaTactics.load_full_min_clr_len hm2'') ?_
                rw [wp_let_mul64_2, wp_let_add64_2]; dsimp only
                have hm1_ws : (BitVec.ofNat 64 (s2.core.min_clr_len - 1)).toNat <
                    s2'.scratch.work_stk1.length := by rw [hrv_idx, hwsl2]; omega
                refine wp_load_of (FullArenaTactics.c0_load_full_work_stk1 hm1_ws hm2'') ?_
                refine wp_unroll_group (fun Js hJs => ?_)
                rw [wp_let_zext32_2, wp_let_ult64_2]; dsimp only
                refine wp_jnz_of (fun _ => ?_) (fun hrv_false => ?_)
                · rw [wp_let_zext32_2, wp_let_add64_2, wp_let_trunc32_8_2]; dsimp only
                  refine wp_store_sep (FullArenaTactics.c0_store_full_mrk 0#8 (by
                    have hrv_z : (BitVec.setWidth 64 (s2'.scratch.work_stk1[(BitVec.ofNat 64
                        (s2.core.min_clr_len - 1)).toNat]'hm1_ws)).toNat =
                        (s2.scratch.work_stk1[s2.core.min_clr_len - 1]'(by rw [hwsl2]; omega)).toNat
                        := by
                      simp only [s2', hrv_idx]; exact zext_toNat _ (by decide)
                    simp only [Arg.val_var, hrv_z]; dsimp only [s2']; rw [hmrl2]
                    exact Nat.lt_of_lt_of_le (hcveq2 ▸ hrv_lt') hcv_le2) hm2'') ?_
                  intro m3 hm3_raw
                  apply hJs; rw [Blocks.get_here]
                  let rv := (s2.scratch.work_stk1[s2.core.min_clr_len - 1]?.getD 0#32).toNat
                  let s3 : FullState :=
                    { core := { s2.core with
                        mrk := s2.core.mrk.set rv 0#8
                        min_clr_len := s2.core.min_clr_len - 1 }
                      scratch := s2.scratch }
                  have hm3 : (FullMem c s3 ⋆ R) m3 := by
                    have hrv_eq : (BitVec.setWidth 64
                        (s2'.scratch.work_stk1[(BitVec.ofNat 64
                          (s2.core.min_clr_len - 1)).toNat]'hm1_ws)).toNat = rv := by
                      simp only [s2', hrv_idx]; rw [zext_toNat _ (by decide)]
                      simp [rv, List.getElem?_eq_getElem (by rw [hwsl2]; omega :
                        s2.core.min_clr_len - 1 < s2.scratch.work_stk1.length)]
                    simp only [Arg.val_var] at hm3_raw
                    rw [hrv_eq] at hm3_raw
                    exact hm3_raw
                  have hdec : ((loadVal m3 i64 (c.hdr + 272)).getD 0#64).toNat - saved <
                      ((loadVal m2 i64 (c.hdr + 272)).getD 0#64).toNat - saved := by
                    rw [FullArenaTactics.load_full_min_clr_len hm3,
                      FullArenaTactics.load_full_min_clr_len hm2]
                    dsimp only [Option.getD_some, s3]
                    rw [bv64_ofNat_toNat (by omega), bv64_ofNat_toNat (by omega)]; omega
                  exact hJrb _ _ hdec ⟨s3, hinv3, hm3⟩
                · simp only [Arg.val_var] at hrv_false
                  have hge : (BitVec.ofNat 64 s.core.cur_vars).toNat ≤
                      (BitVec.setWidth 64 (s2'.scratch.work_stk1[(BitVec.ofNat 64
                        (s2.core.min_clr_len - 1)).toNat]'hm1_ws)).toNat := by
                    have hnot : ¬ (BitVec.setWidth 64 (s2'.scratch.work_stk1[(BitVec.ofNat 64
                        (s2.core.min_clr_len - 1)).toNat]'hm1_ws)).toNat <
                        (BitVec.ofNat 64 s.core.cur_vars).toNat := by
                      simpa [BitVec.ult] using hrv_false
                    omega
                  simp only [s2', hrv_idx] at hge
                  rw [zext_toNat _ (by decide), BitVec.toNat_ofNat,
                    Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hge
                  exact absurd hrv_lt' (by rw [hcveq2]; omega)
              · c0_steps; exact hJ2 _ _ ⟨s2, hinv2_pk, hm2⟩
          · exact hJ2 _ _ ⟨s1, hinv1, hm1⟩
      · c0_to_group
        have hi_lt : i.toNat < s1.core.tmp_len := by c0_bound
        have hi_tmp : i.toNat < s1.core.tmp.length := by rw [htll1]; omega
        refine wp_join_group (fun (rsn, ()) m1' => m1' = m1)
          (fun Jr (rsn, ()) m1' hm1' => ?_) (fun Jr hJr => ?_)
        · subst m1'
          c0_to_group
          refine wp_join_group
            (fun _ m2 => ∃ s2 : FullState, M5BumpAnaInv c s s2 saved ∧ (FullMem c s2 ⋆ R) m2)
            (fun Jstep _ m2 ⟨s2, hinv2, hm2⟩ => ?_) (fun Jstep hJstep => ?_)
          · c0_steps
            exact hLoop _ _ (by c0_bound) ⟨by c0_bound, s2, hinv2, hm2⟩
          · refine wp_join_group (ts := []) (fun _ m' => m' = m1)
              (fun Jelse () m' hm' => ?_) (fun Jelse hJelse => ?_)
            · subst m'; rw [Blocks.get_here]; dsimp only
              refine wp_join_group (ts := [])
                (fun _ m2 => ∃ s2 : FullState, M5BumpAnaInv c s s2 saved ∧ (FullMem c s2 ⋆ R) m2)
                (fun Js () m2 ⟨s2, hinv2, hm2⟩ => by
                  rw [Blocks.get_here]; exact hJstep _ _ ⟨s2, hinv2, hm2⟩)
                (fun Js hJs => ?_)
              c0_steps
              · rename_i hrsn3_bd hsz3_bd
                have hrsn3 : rsn.toNat + 3 ≤ s1.core.arena_len := by
                  rw [Nat.mod_eq_of_lt (by omega : s1.core.arena_len < 2 ^ 64)] at hrsn3_bd
                  bv_omega
                have hrsn2_eq : (rsn.setWidth 64 + 2).toNat = rsn.toNat + 2 := by
                  rw [BitVec.toNat_add, zext_toNat _ (by decide),
                    show (2 : BitVec 64).toNat = 2 from rfl,
                    Nat.mod_eq_of_lt (by omega : rsn.toNat + 2 < 2 ^ 64)]
                have hrsn2_lt : (rsn.setWidth 64 + 2).toNat < s1.core.arena.length := by
                  rw [hrsn2_eq, harl1]; omega
                let sz := s1.core.arena[(rsn.setWidth 64 + 2).toNat]'hrsn2_lt
                have hrsn_sz : rsn.toNat + 3 + sz.toNat ≤ s1.core.arena_len := by
                  have h1 : (rsn.toNat + 3 + sz.toNat) % 2 ^ 64 ≤ s1.core.arena_len % 2 ^ 64 := by
                    have hidx2 : (rsn.setWidth 64 + 2).toNat =
                        (rsn.toNat + (2 : BitVec 64).toNat) % 2 ^ 64 := by
                      rw [BitVec.toNat_add, zext_toNat _ (by decide)]
                    simpa only [sz, hidx2, show (3 : BitVec 64).toNat = 3 from rfl] using hc
                  have hsz_lt := sz.isLt
                  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h1
                  exact h1
                refine wp_loop_inv (ts := [i32])
                  (fun (j, ()) m2 => j.toNat ≤ sz.toNat ∧ ∃ s2 : FullState,
                    M5BumpAnaInv c s s2 saved ∧ (FullMem c s2 ⋆ R) m2)
                  (fun (j, ()) _ => sz.toNat - j.toNat) (fun Jj hJj => ?_)
                  (fun Jj (j, ()) m2 ⟨hjle, s2, hinv2, hm2⟩ hJj => ?_)
                · c0_steps
                  exact hJj (0#32, ()) _ ⟨by simp, s1, hinv1_pk, hm1⟩
                · have hinv2_pk := hinv2
                  rcases hinv2 with ⟨hlen2, hcore2, hscr2, hsav2, hcov2, hpres2, hnew2⟩
                  have hcveq2 : s2.core.cur_vars = s.core.cur_vars := by rw [hcore2]
                  have hmcl2 : s2.core.min_clr_len ≤ s.core.cur_vars := by
                    rw [← hcveq2]; exact hcov2.1
                  have hareq2 : s2.core.arena = s1.core.arena := by rw [hcore2, hcore1]
                  have harl2 : s2.core.arena_len = s1.core.arena_len := by rw [hcore2, hcore1]
                  obtain hcv_le2 := hlen2.core_ok.cur_vars_le
                  obtain harl2_arr := hlen2.core_ok.arena_len_arr
                  obtain hale2 := hlen2.core_ok.arena_len_le
                  obtain hlvll2 := hlen2.core_ok.lvl_len
                  obtain hmrl2 := hlen2.core_ok.mrk_len
                  obtain hwsl2 := hlen2.scratch_ok.work_stk1_len
                  rw [Blocks.get_here]; dsimp only
                  rw [wp_let_ult32_2]; dsimp only
                  refine wp_jnz_of (fun hj_c => ?_) (fun _ =>
                    hJ () m2 (by rw [Blocks.get_here]; exact hJs () m2 ⟨s2, hinv2_pk, hm2⟩))
                  have hj_lt : j.toNat < sz.toNat := by
                    simp only [Arg.val_var] at hj_c
                    simpa [BitVec.ult, sz] using hj_c
                  rw [wp_let_add64_2]; dsimp only
                  refine wp_load_of (FullArenaTactics.load_full_min_clr_len hm2) ?_
                  rw [wp_let_ule64_2]; dsimp only
                  refine wp_jnz_of (fun _ => ?_) (fun _ =>
                    hJ () m2 (by rw [Blocks.get_here]; exact hJs () m2 ⟨s2, hinv2_pk, hm2⟩))
                  have har_li : (rsn.setWidth 64 + 3 + j.setWidth 64).toNat <
                      s2.core.arena.length := by
                    have : (rsn.setWidth 64 + 3 + j.setWidth 64).toNat =
                        rsn.toNat + 3 + j.toNat := by bv_omega
                    rw [this, harl2_arr]; omega
                  repeat (first | rw [wp_let_zext32_2] | rw [wp_let_mul64_2] | rw [wp_let_add64_2])
                  dsimp only
                  refine wp_load_of (FullArenaTactics.c0_load_full_arena (s := s2) (by
                    simpa only [Arg.val_var, Arg.val_imm] using har_li) hm2) ?_
                  rw [wp_let_lshr32_2]; dsimp only
                  let ov32 := (s2.core.arena[(rsn.setWidth 64 + 3 +
                    j.setWidth 64).toNat]'har_li) >>> (1 : Nat)
                  have hj1 : (j + 1).toNat = j.toNat + 1 := by
                    have hsz_lt := sz.isLt; bv_omega
                  refine wp_join_group (ts := [])
                    (fun _ m3 =>
                      ∃ s3 : FullState, M5BumpAnaInv c s s3 saved ∧ (FullMem c s3 ⋆ R) m3)
                    (fun Jnext () m3 ⟨s3, hinv3, hm3⟩ => by
                      rw [Blocks.get_here, wp_let_add32_2]; dsimp only
                      exact hJj (j + 1, ()) m3 (by dsimp only; rw [hj1]; omega)
                        ⟨by rw [hj1]; omega, s3, hinv3, hm3⟩)
                    (fun Jnext hJnext => ?_)
                  rw [wp_let_zext32_2, wp_let_ult64_2]; dsimp only
                  refine wp_jnz_of (fun hov_bd => ?_) (fun _ => hJnext () m2 ⟨s2, hinv2_pk, hm2⟩)
                  have h1m : (1 : BitVec 32).toNat % 32 = 1 := rfl
                  have hov_zext : (BitVec.setWidth 64 ov32).toNat = ov32.toNat :=
                    zext_toNat _ (by decide)
                  have hov_lt : ov32.toNat < s.core.cur_vars := by
                    simp only [Arg.val_var, Arg.val_imm, h1m] at hov_bd
                    have h1 : (BitVec.setWidth 64 ov32).toNat <
                        (BitVec.ofNat 64 s.core.cur_vars).toNat := by
                      simpa [BitVec.ult, ov32] using hov_bd
                    rw [hov_zext, BitVec.toNat_ofNat,
                      Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at h1
                    exact h1
                  rw [wp_let_zext32_2, wp_let_mul64_2, wp_let_add64_2]; dsimp only
                  refine wp_load_of (FullArenaTactics.c0_load_full_lvl (s := s2) (by
                    simp only [Arg.val_var, Arg.val_imm, h1m]; rw [hlvll2]
                    change (BitVec.setWidth 64 ov32).toNat < _; rw [hov_zext]; omega) hm2) ?_
                  rw [wp_let_ugt32_2]; dsimp only
                  refine wp_jnz_of (fun _ => ?_) (fun _ => hJnext () m2 ⟨s2, hinv2_pk, hm2⟩)
                  rw [wp_let_zext32_2, wp_let_add64_2]; dsimp only
                  refine wp_load_of (FullArenaTactics.c0_load_full_mrk (s := s2) (by
                    simp only [Arg.val_var, Arg.val_imm, h1m]; rw [hmrl2]
                    change (BitVec.setWidth 64 ov32).toNat < _; rw [hov_zext]; omega) hm2) ?_
                  repeat (first
                    | rw [wp_let_trunc32_8_2] | rw [wp_let_zext8_32_2] | rw [wp_let_eq32_2])
                  dsimp only
                  refine wp_jnz_of (fun hmrk_raw => ?_) (fun _ => hJnext () m2 ⟨s2, hinv2_pk, hm2⟩)
                  have hmrk0 : s2.core.mrk[ov32.toNat]?.getD 0#8 = 0#8 := by
                    rw [List.getElem?_eq_getElem (by rw [hmrl2]; omega), Option.getD_some]
                    have heq0 :
                        BitVec.setWidth 32 (s2.core.mrk[ov32.toNat]'(by rw [hmrl2]; omega)) =
                        0#32 := by
                      simp only [Arg.val_var, Arg.val_imm, beq_iff_eq, h1m] at hmrk_raw
                      simpa only [ov32, hov_zext, show BitVec.setWidth 32 (BitVec.setWidth 8
                        (0 : BitVec 32)) = 0#32 from rfl] using hmrk_raw
                    exact m5_setWidth32_eq_zero heq0
                  rw [wp_let_add64_2]; dsimp only
                  refine wp_load_of (FullArenaTactics.load_full_min_clr_len hm2) ?_
                  rw [wp_let_ult64_2]; dsimp only
                  refine wp_jnz_of (fun hmcl_raw => ?_) (fun _ => hJnext () m2 ⟨s2, hinv2_pk, hm2⟩)
                  have hmcl_lt : s2.core.min_clr_len < s.core.cur_vars := by
                    simp only [Arg.val_var] at hmcl_raw
                    have h1 : (BitVec.ofNat 64 s2.core.min_clr_len).toNat <
                        (BitVec.ofNat 64 s.core.cur_vars).toNat := by
                      simpa [BitVec.ult] using hmcl_raw
                    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h1
                    exact h1
                  rw [wp_let_zext32_2, wp_let_add64_2, wp_let_trunc32_8_2]; dsimp only
                  refine wp_store_sep (FullArenaTactics.c0_store_full_mrk (s := s2) 1#8 (by
                    simp only [Arg.val_var, Arg.val_imm, h1m]; rw [hmrl2]
                    change (BitVec.setWidth 64 ov32).toNat < _; rw [hov_zext]; omega) hm2) ?_
                  intro m3a hm3a
                  simp only [Arg.val_var, Arg.val_imm, h1m] at hm3a
                  rw [show (BitVec.setWidth 64 ((s2.core.arena[(rsn.setWidth 64 + 3 +
                    j.setWidth 64).toNat]'har_li) >>> 1)).toNat = ov32.toNat from hov_zext] at hm3a
                  let s3a : FullState := { s2 with core := { s2.core with
                    mrk := s2.core.mrk.set ov32.toNat 1#8 } }
                  have hm3a' : (FullMem c s3a ⋆ R) m3a := hm3a
                  rw [wp_let_add64_2]; dsimp only
                  refine wp_load_of (FullArenaTactics.load_full_min_clr_len hm3a') ?_
                  rw [wp_let_mul64_2, wp_let_add64_2]; dsimp only
                  have hmcl_to : (BitVec.ofNat 64 s2.core.min_clr_len).toNat =
                      s2.core.min_clr_len := bv64_ofNat_toNat (by omega)
                  refine wp_store_sep (FullArenaTactics.c0_store_full_work_stk1 (s := s3a) ov32 (by
                    simp only [Arg.val_var]; dsimp only [s3a]; rw [hmcl_to, hwsl2]; omega) hm3a') ?_
                  intro m3b hm3b
                  simp only [Arg.val_var] at hm3b
                  rw [hmcl_to] at hm3b
                  let s3b : FullState := { s3a with scratch := { s3a.scratch with
                    work_stk1 := s2.scratch.work_stk1.set s2.core.min_clr_len ov32 } }
                  have hm3b' : (FullMem c s3b ⋆ R) m3b := hm3b
                  rw [wp_let_add64_2]; dsimp only
                  refine wp_load_of (FullArenaTactics.load_full_min_clr_len hm3b') ?_
                  rw [wp_let_add64_2, wp_let_add64_2]; dsimp only
                  refine wp_store_sep (FullArenaTactics.c0_store_full_min_clr_len _ hm3b') ?_
                  intro m3c hm3c
                  simp only [Arg.val_var, Arg.val_imm] at hm3c
                  rw [bv64_ofNat_add1 (by dsimp only [s3b, s3a]; omega)] at hm3c
                  have hinv3 := m5BumpAnaInv_step hinv2_pk hov_lt hmrk0 hmcl_lt
                  have hbv_ov : BitVec.ofNat 32 ov32.toNat = ov32 :=
                    BitVec.eq_of_toNat_eq
                      (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ov32.isLt])
                  let s3 : FullState :=
                    { core := { s2.core with
                        mrk := s2.core.mrk.set ov32.toNat 1#8
                        min_clr_len := s2.core.min_clr_len + 1 }
                      scratch := { s2.scratch with
                        work_stk1 := s2.scratch.work_stk1.set s2.core.min_clr_len ov32 } }
                  have hinv3' : M5BumpAnaInv c s s3 saved := by simpa only [s3, hbv_ov] using hinv3
                  exact hJnext () m3c ⟨s3, hinv3', hm3c⟩
              all_goals exact hJs _ _ ⟨s1, hinv1_pk, hm1⟩
            · rw [wp_let_ne32_2]; dsimp only
              refine wp_jnz_of (fun _ => ?_) (fun _ => hJelse () m1 rfl)
              rw [wp_let_and32_2, wp_let_ne32_2]; dsimp only
              refine wp_jnz_of (fun _ => ?_) (fun _ => hJelse () m1 rfl)
              rw [wp_let_and32_2, wp_let_lshr32_2]; dsimp only
              let ov32 := (rsn &&& 0x7FFFFFFF#32) >>> (1 : Nat)
              refine wp_join_group (ts := [])
                (fun _ m2 => ∃ s2 : FullState, M5BumpAnaInv c s s2 saved ∧ (FullMem c s2 ⋆ R) m2)
                (fun Jb () m2 ⟨s2, hinv2, hm2⟩ => by
                  rw [Blocks.get_here]; exact hJstep _ _ ⟨s2, hinv2, hm2⟩)
                (fun Jb hJb => ?_)
              rw [wp_let_zext32_2, wp_let_ult64_2]; dsimp only
              refine wp_jnz_of (fun hov_bd => ?_) (fun _ => hJb () m1 ⟨s1, hinv1_pk, hm1⟩)
              have hov_lt : ov32.toNat < s.core.cur_vars := by
                simp only [Arg.val_var] at hov_bd
                have h1 : (BitVec.setWidth 64 ov32).toNat <
                    (BitVec.ofNat 64 s.core.cur_vars).toNat := by
                  simpa [BitVec.ult, ov32] using hov_bd
                rw [zext_toNat _ (by decide), BitVec.toNat_ofNat,
                  Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at h1
                exact h1
              have hov_zext : (BitVec.setWidth 64 ov32).toNat = ov32.toNat :=
                zext_toNat _ (by decide)
              rw [wp_let_zext32_2, wp_let_mul64_2, wp_let_add64_2]; dsimp only
              refine wp_load_of (FullArenaTactics.c0_load_full_lvl (s := s1) (by
                simp only [Arg.val_var]; rw [hlvll1]; change (BitVec.setWidth 64 ov32).toNat < _
                rw [hov_zext]; omega) hm1) ?_
              rw [wp_let_ugt32_2]; dsimp only
              refine wp_jnz_of (fun _ => ?_) (fun _ => hJb () m1 ⟨s1, hinv1_pk, hm1⟩)
              rw [wp_let_zext32_2, wp_let_add64_2]; dsimp only
              refine wp_load_of (FullArenaTactics.c0_load_full_mrk (s := s1) (by
                simp only [Arg.val_var]; rw [hmrl1]; change (BitVec.setWidth 64 ov32).toNat < _
                rw [hov_zext]; omega) hm1) ?_
              repeat (first
                | rw [wp_let_trunc32_8_2] | rw [wp_let_zext8_32_2] | rw [wp_let_eq32_2])
              dsimp only
              refine wp_jnz_of (fun hmrk_raw => ?_) (fun _ => hJb () m1 ⟨s1, hinv1_pk, hm1⟩)
              have hmrk0 : s1.core.mrk[ov32.toNat]?.getD 0#8 = 0#8 := by
                rw [List.getElem?_eq_getElem (by rw [hmrl1]; omega), Option.getD_some]
                have heq0 : BitVec.setWidth 32 (s1.core.mrk[ov32.toNat]'(by rw [hmrl1]; omega)) =
                    0#32 := by
                  have hzv : (BitVec.setWidth 64 ((rsn &&& 2147483647) >>> 1)).toNat =
                      ov32.toNat := hov_zext
                  simp only [Arg.val_var, Arg.val_imm, beq_iff_eq,
                    show (1 : BitVec 32).toNat % 32 = 1 from rfl] at hmrk_raw
                  simpa only [hzv, show BitVec.setWidth 32 (BitVec.setWidth 8
                    (0 : BitVec 32)) = 0#32 from rfl] using hmrk_raw
                exact m5_setWidth32_eq_zero heq0
              rw [wp_let_add64_2]; dsimp only
              refine wp_load_of (FullArenaTactics.load_full_min_clr_len hm1) ?_
              rw [wp_let_ult64_2]; dsimp only
              refine wp_jnz_of (fun hmcl_raw => ?_) (fun _ => hJb () m1 ⟨s1, hinv1_pk, hm1⟩)
              have hmcl_lt : s1.core.min_clr_len < s.core.cur_vars := by
                simp only [Arg.val_var] at hmcl_raw
                have h1 : (BitVec.ofNat 64 s1.core.min_clr_len).toNat <
                    (BitVec.ofNat 64 s.core.cur_vars).toNat := by
                  simpa [BitVec.ult] using hmcl_raw
                rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                  Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h1
                exact h1
              rw [wp_let_zext32_2, wp_let_add64_2, wp_let_trunc32_8_2]; dsimp only
              refine wp_store_sep (FullArenaTactics.c0_store_full_mrk (s := s1) 1#8 (by
                simp only [Arg.val_var]; rw [hmrl1]; change (BitVec.setWidth 64 ov32).toNat < _
                rw [hov_zext]; omega) hm1) ?_
              intro m2a hm2a
              simp only [Arg.val_var, Arg.val_imm,
                show (1 : BitVec 32).toNat % 32 = 1 from rfl] at hm2a
              rw [show (BitVec.setWidth 64 ((rsn &&& 2147483647) >>> 1)).toNat = ov32.toNat
                from hov_zext] at hm2a
              let s2a : FullState := { s1 with core := { s1.core with
                mrk := s1.core.mrk.set ov32.toNat 1#8 } }
              have hm2a' : (FullMem c s2a ⋆ R) m2a := hm2a
              rw [wp_let_add64_2]; dsimp only
              refine wp_load_of (FullArenaTactics.load_full_min_clr_len hm2a') ?_
              rw [wp_let_mul64_2, wp_let_add64_2]; dsimp only
              have hmcl_to : (BitVec.ofNat 64 s1.core.min_clr_len).toNat =
                  s1.core.min_clr_len := bv64_ofNat_toNat (by omega)
              refine wp_store_sep (FullArenaTactics.c0_store_full_work_stk1 (s := s2a) ov32 (by
                simp only [Arg.val_var]; dsimp only [s2a]; rw [hmcl_to, hwsl1]; omega) hm2a') ?_
              intro m2b hm2b
              simp only [Arg.val_var] at hm2b
              rw [hmcl_to] at hm2b
              let s2b : FullState := { s2a with scratch := { s2a.scratch with
                work_stk1 := s1.scratch.work_stk1.set s1.core.min_clr_len ov32 } }
              have hm2b' : (FullMem c s2b ⋆ R) m2b := hm2b
              rw [wp_let_add64_2]; dsimp only
              refine wp_load_of (FullArenaTactics.load_full_min_clr_len hm2b') ?_
              rw [wp_let_add64_2, wp_let_add64_2]; dsimp only
              refine wp_store_sep (FullArenaTactics.c0_store_full_min_clr_len _ hm2b') ?_
              intro m2c hm2c
              simp only [Arg.val_var, Arg.val_imm] at hm2c
              rw [bv64_ofNat_add1 (by dsimp only [s2b, s2a]; omega)] at hm2c
              have hinv2 := m5BumpAnaInv_step hinv1_pk hov_lt hmrk0 hmcl_lt
              have hbv_ov : BitVec.ofNat 32 ov32.toNat = ov32 :=
                BitVec.eq_of_toNat_eq
                  (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ov32.isLt])
              let s2 : FullState :=
                { core := { s1.core with
                    mrk := s1.core.mrk.set ov32.toNat 1#8
                    min_clr_len := s1.core.min_clr_len + 1 }
                  scratch := { s1.scratch with
                    work_stk1 := s1.scratch.work_stk1.set s1.core.min_clr_len ov32 } }
              have hinv2' : M5BumpAnaInv c s s2 saved := by simpa only [s2, hbv_ov] using hinv2
              exact hJb () m2c ⟨s2, hinv2', hm2c⟩
        · rw [wp_let_zext32_2, wp_let_ult64_2]; dsimp only
          refine wp_jnz_of (fun hc_uv => ?_) (fun _ => hJr _ _ rfl)
          rw [wp_let_zext32_2, wp_let_mul64_2, wp_let_add64_2]; dsimp only
          refine wp_load_of (FullArenaTactics.c0_load_full_rsns (s := s1) (by
            simp only [Arg.val_var] at hc_uv ⊢
            rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc_uv
            rw [hrsnl1]; omega) hm1) ?_
          exact hJr _ _ rfl
        all_goals exact hJ1 _ _ ⟨s1, hinv1_pk, hm1⟩

/-! ## 2. `full_restore_bump_ana_m5` (`fullRestoreBumpAnaSpec`) -/

/-- Specification of `full_restore_bump_ana_m5(h)`: restores analyzed marks from `work_stk1`,
bumps analyzed variables (only when `probing == 0`), and clears marks back to `FullMrkZero`. -/
@[expose] def fullRestoreBumpAnaSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullMrkZero c s ∧ (FullMem c s ⋆ R) m ∧
    ∀ mrk' mcl' sc' m',
      let s' : FullState :=
        { s with core := { s.core with mrk := mrk', min_clr_len := mcl' }, scratch := sc' }
      s'.LengthsOk c → FullMrkZero c s' → FullExtScratchPres s s' →
      sc'.work_stk2 = s.scratch.work_stk2 → (FullMem c s' ⋆ R) m' → Q () m'

private theorem m5_anaMarksCov_empty {c : FullCfg} {s : FullState}
    (hm0 : FullMrkZero c s) :
    FullAnaMarksCov c { s with core := { s.core with min_clr_len := 0 } } :=
  ⟨Nat.zero_le _, by simp, fun _ hk => by dsimp only at hk; omega,
    fun v hv hnz => absurd (hm0 v hv) hnz⟩

private theorem m5_anaMarksCov_push {c : FullCfg} {s : FullState} {w : Nat}
    {mrk1 : List (BitVec 8)} {ws1 : List (BitVec 32)} {av : BitVec 32}
    (hlen : s.LengthsOk c) (hmrk1 : mrk1.length = c.max_vars)
    (hws1 : ws1.length = 2 * c.max_vars)
    (hcov : FullAnaMarksCov c { core := { s.core with mrk := mrk1, min_clr_len := w }
                                scratch := { s.scratch with work_stk1 := ws1 } })
    (hw_lt : w < s.core.cur_vars) (hav_lt : av.toNat < s.core.cur_vars)
    (hm0 : mrk1[av.toNat]?.getD 0#8 = 0#8) :
    FullAnaMarksCov c
      { core := { s.core with mrk := mrk1.set av.toNat 1#8, min_clr_len := w + 1 }
        scratch := { s.scratch with work_stk1 := ws1.set w av } } := by
  obtain ⟨_, hnd, helem, hcov'⟩ := hcov
  have hcv_le := hlen.core_ok.cur_vars_le
  have hw_ws : w < ws1.length := by omega
  have hav_mrk : av.toNat < mrk1.length := by omega
  refine ⟨by dsimp only; omega, ?_, ?_, ?_⟩
  · exact nodup_map_take_append hw_ws hnd fun j hj he =>
      (helem j hj).2 (by rw [he]; exact hm0)
  · intro j hj; dsimp only at hj ⊢
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hlt | rfl
    · rw [List.getElem?_set_ne (by omega)]
      have hne : (ws1[j]?.getD 0#32).toNat ≠ av.toNat := fun he => (helem j hlt).2 (he ▸ hm0)
      exact ⟨(helem j hlt).1, by rw [List.getElem?_set_ne (Ne.symm hne)]; exact (helem j hlt).2⟩
    · rw [List.getElem?_set_self hw_ws, Option.getD_some,
        List.getElem?_set_self hav_mrk, Option.getD_some]
      exact ⟨hav_lt, by decide⟩
  · intro v hv hnz
    by_cases hveq : v = av.toNat
    · subst v; refine ⟨w, by dsimp only; omega, ?_⟩
      dsimp only; rw [List.getElem?_set_self hw_ws, Option.getD_some]
    · have hnz1 : mrk1[v]?.getD 0#8 ≠ 0#8 := by
        dsimp only at hnz; rwa [List.getElem?_set_ne (Ne.symm hveq)] at hnz
      obtain ⟨j, hj, hjeq⟩ := hcov' v hv hnz1
      dsimp only at hj hjeq
      exact ⟨j, by dsimp only; omega, by
        dsimp only; rw [List.getElem?_set_ne (by omega)]; exact hjeq⟩

/-- `full_restore_bump_ana_m5` satisfies `fullRestoreBumpAnaSpec` parametrically in `Γ`. -/
theorem full_restore_bump_ana_m5_wp (Γ : Env)
    (hBumpAna : ∀ a m Q X, fullBumpAnalyzedSpec a m Q X →
      Γ "full_bump_analyzed" [i64] [] a m Q X)
    (hClearAna : ∀ a m Q X, fullClearAnaSpec a m Q X →
      Γ "full_clear_ana" [i64] [] a m Q X) :
    ∀ a m Q X, fullRestoreBumpAnaSpec a m Q X →
      Func.wp Γ full_restore_bump_ana_m5_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm0, hm, hQ⟩
  c0_step; c0_split
  · exact hQ s.core.mrk s.core.min_clr_len s.scratch m hlen hm0 ⟨rfl, rfl⟩ rfl hm
  · c0_to_group
    have hmax : c.max_vars < 2 * dimacsBound := c.hmaxv
    unfold dimacsBound at hmax
    have hcv_le := hlen.core_ok.cur_vars_le
    refine wp_join_group (ts := [i64])
      (fun (ana_n, ()) ma => ana_n.toNat ≤ s.core.cur_vars ∧ m = ma) ?_ ?_
    · rintro _ ⟨ana_n, ⟨⟩⟩ _ ⟨hana_le, rfl⟩
      c0_to_group
      refine wp_loop_inv (ts := [i64, i64])
        (fun (w, k, ()) ml => w.toNat ≤ k.toNat ∧ k.toNat ≤ ana_n.toNat ∧
          ∃ (mrk1 : List (BitVec 8)) (ws1 : List (BitVec 32)),
            mrk1.length = c.max_vars ∧ ws1.length = 2 * c.max_vars ∧
            FullAnaMarksCov c { core := { s.core with mrk := mrk1, min_clr_len := w.toNat }
                                scratch := { s.scratch with work_stk1 := ws1 } } ∧
            (FullMem c { core := { s.core with mrk := mrk1 }
                         scratch := { s.scratch with work_stk1 := ws1 } } ⋆ R) ml)
        (fun (_, k, ()) _ => ana_n.toNat - k.toNat)
        (fun J hLoop => ?_)
        (fun J (w, k, ()) ml ⟨hwk, hka, mrk1, ws1, hml1, hws1, hcov1, hml⟩ hLoop => ?_)
      · c0_steps
        exact hLoop (0#64, 0#64, ()) m ⟨by simp, by simp, s.core.mrk, s.scratch.work_stk1,
          hlen.core_ok.mrk_len, hlen.scratch_ok.work_stk1_len, m5_anaMarksCov_empty hm0, hm⟩
      · rw [Blocks.get_here]; dsimp only
        c0_split
        · have hk_lt : k.toNat < ana_n.toNat := by assumption
          have hk_ws : k.toNat < ws1.length := by omega
          have hw_lt : w.toNat < s.core.cur_vars := by omega
          have hw_ws : w.toNat < ws1.length := by omega
          have hk1 : (k + 1#64).toNat = k.toNat + 1 := by bv_omega
          let s1 : FullState :=
            { core := { s.core with mrk := mrk1 }, scratch := { s.scratch with work_stk1 := ws1 } }
          change (FullMem c s1 ⋆ R) ml at hml
          c0_steps
          refine wp_load_of (FullArenaTactics.c0_load_full_work_stk1 (s := s1) hk_ws hml) ?_
          let av := ws1[k.toNat]'hk_ws
          refine wp_join_group (ts := [i64])
            (fun (w', ()) m2 => w'.toNat ≤ k.toNat + 1 ∧
              ∃ (mrk2 : List (BitVec 8)) (ws2 : List (BitVec 32)),
                mrk2.length = c.max_vars ∧ ws2.length = 2 * c.max_vars ∧
                FullAnaMarksCov c { core := { s.core with mrk := mrk2, min_clr_len := w'.toNat }
                                    scratch := { s.scratch with work_stk1 := ws2 } } ∧
                (FullMem c { core := { s.core with mrk := mrk2 }
                             scratch := { s.scratch with work_stk1 := ws2 } } ⋆ R) m2)
            (fun Jn (w', ()) m2 ⟨hw'le, mrk2, ws2, hml2, hws2, hcov2, hm2⟩ => by
              c0_steps
              exact hLoop (w', k + 1#64, ()) m2 (by dsimp only; rw [hk1]; omega)
                ⟨by rw [hk1]; exact hw'le, by rw [hk1]; omega, mrk2, ws2, hml2, hws2, hcov2, hm2⟩)
            (fun Jn hJn => ?_)
          c0_split
          · have hav_z : (BitVec.setWidth 64 av).toNat = av.toNat := zext_toNat av (by decide)
            have hav_lt : av.toNat < s.core.cur_vars := by
              have h1 : (s1.scratch.work_stk1[k.toNat]'hk_ws).toNat <
                  s.core.cur_vars % 2 ^ 64 := by assumption
              rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at h1; exact h1
            have hav_mrk : av.toNat < s1.core.mrk.length := by dsimp only [s1]; omega
            have hav_mrk' : (BitVec.setWidth 64 av).toNat < s1.core.mrk.length := by
              rw [hav_z]; exact hav_mrk
            have hw_ws1 : w.toNat < s1.scratch.work_stk1.length := by dsimp only [s1]; omega
            c0_steps
            refine wp_load_of (FullArenaTactics.c0_load_full_mrk (s := s1) hav_mrk' hml) ?_
            c0_split
            · have hmrk_av0 : mrk1[av.toNat]?.getD 0#8 = 0#8 := by
                rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                have h0 : BitVec.setWidth 32 (s1.core.mrk[av.toNat]'hav_mrk) = 0#32 := by
                  simpa only [hav_z] using (by assumption :
                    BitVec.setWidth 32 (s1.core.mrk[(BitVec.setWidth 64 av).toNat]'hav_mrk') =
                      0#32)
                exact m5_setWidth32_eq_zero h0
              have hw1 : (w + 1#64).toNat = w.toNat + 1 := by bv_omega
              have hcov_next := m5_anaMarksCov_push hlen hml1 hws1 hcov1 hw_lt hav_lt hmrk_av0
              refine wp_store_sep (FullArenaTactics.c0_store_full_mrk (s := s1) 1#8 hav_mrk' hml)
                fun m_a hm_a => ?_
              let s1a : FullState :=
                { s1 with core := { s1.core with mrk := mrk1.set av.toNat 1#8 } }
              have hm_a' : (FullMem c s1a ⋆ R) m_a := by simpa only [s1a, s1, av, hav_z] using hm_a
              have hw_ws1a : w.toNat < s1a.scratch.work_stk1.length := hw_ws1
              c0_let_simp
              refine wp_store_sep (FullArenaTactics.c0_store_full_work_stk1 (s := s1a) av hw_ws1a
                hm_a') fun m_b hm_b => ?_
              c0_let_simp
              refine hJn (w + 1#64, ()) m_b ⟨by rw [hw1]; omega, mrk1.set av.toNat 1#8,
                ws1.set w.toNat av, by simp [hml1], by simp [hws1], by rw [hw1]; exact hcov_next,
                hm_b⟩
            · c0_steps; exact hJn (w, ()) ml ⟨by omega, mrk1, ws1, hml1, hws1, hcov1, hml⟩
          · c0_steps; exact hJn (w, ()) ml ⟨by omega, mrk1, ws1, hml1, hws1, hcov1, hml⟩
        · -- Exit loop: store `h->min_clr_len = w`, optionally call `bump_analyzed` + `clear_ana`
          c0_to_jnz
          let s_post : FullState :=
            { core := { s.core with mrk := mrk1, min_clr_len := w.toNat }
              scratch := { s.scratch with work_stk1 := ws1 } }
          have hlen_post : s_post.LengthsOk c :=
            ⟨{ hlen.core_ok with mrk_len := hml1, min_clr_len_le := by dsimp only [s_post]; omega },
             { hlen.scratch_ok with work_stk1_len := hws1 }⟩
          have hm_post : (FullMem c s_post ⋆ R) m := hm
          refine wp_jnz_of (fun hc => ?_) (fun hc => ?_)
          · c0_call hBumpAna
            refine ⟨c, s_post, R, rfl, hlen_post, hcov1, hm_post, ?_⟩
            intro mrk2 mcl2 sc2 m2 _ hlen2 hcov2 hpres2 hws22 hm2
            let s2 : FullState :=
              { s_post with core := { s_post.core with mrk := mrk2, min_clr_len := mcl2 }
                            scratch := sc2 }
            c0_call hClearAna
            refine ⟨c, s2, R, rfl, hlen2, hm2, ?_⟩
            intro mrk3 m3 hml3 _ _ hclr3 hm3
            apply hJ; rw [Blocks.get_here, wp_ret]
            exact hQ mrk3 0 sc2 m3
              ⟨{ hlen2.core_ok with mrk_len := hml3, min_clr_len_le := Nat.zero_le _ },
               hlen2.scratch_ok⟩
              (hclr3 hcov2) hpres2 hws22 hm3
          · have hw0 : w.toNat = 0 := by
              simp only [Arg.val_var, BitVec.ult, decide_eq_false_iff_not] at hc
              have h0 : (0 : BitVec 64).toNat = 0 := rfl; omega
            have hmz : FullMrkZero c s_post := fun v hv =>
              Classical.byContradiction fun hnz => by
                obtain ⟨j, hj, _⟩ := hcov1.2.2.2 v hv hnz
                dsimp only [s_post] at hj; omega
            rw [wp_jump]; apply hJ; rw [Blocks.get_here]; rw [wp_ret]
            exact hQ mrk1 w.toNat s_post.scratch m hlen_post hmz ⟨rfl, rfl⟩ rfl hm_post
    · intro Jana hJana; c0_split
      · c0_steps; exact hJana (BitVec.ofNat 64 s.core.cur_vars, ()) m
          ⟨by rw [bv64_ofNat_toNat (by omega)]; exact Nat.le_refl _, rfl⟩
      · c0_steps; exact hJana (s.scratch.res_sz, ()) m ⟨by
          have hnot : ¬ s.core.cur_vars % 2 ^ 64 < s.scratch.res_sz.toNat := by assumption
          rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hnot; omega, rfl⟩

end BumpAnalyzedProof

end LeanQbe.T.Examples.Kissat.FullM5HeurCore
