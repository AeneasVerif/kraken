module

public import LeanQbe.T.Examples.Kissat.FullWalkExtLemmas1
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` Walk, Mode, Restart & Extend `Func.wp` Proofs — Part 2 (`Stage 4`)

Proves `full_walk_pick_lit_wp`, `full_next_dec_var_wp`, and `full_bump_analyzed_wp`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.C0Step
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test
open FullWalkExtSpecs
open FullWalkExtHelpers
open scoped FullArenaTactics
open scoped FullWalkExtTactics

/-! ## 1. `full_walk_pick_lit` -/

theorem full_walk_pick_lit_wp (Γ : Env)
    (hRng : ∀ a m Q X, fullRngNextSpec a m Q X → Γ "full_rng_next" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullWalkPickLitSpec a m Q X → Func.wp Γ full_walk_pick_lit_body a m Q X := by
  rintro ⟨h, scr, idx, ⟨⟩⟩ m Q X ⟨c, s, R, ⟨rfl, rfl, ⟨F0, hinv⟩, hidx, hok⟩, hlen, hm, hQ⟩
  obtain ⟨F_cur, hw_inv⟩ := hinv.witness
  obtain ha := hw_inv.arena
  dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj, fullSafetySlice_safe] at hlen hm hQ
  c0_steps
  obtain hmax : c.max_vars < 2 * dimacsBound := c.hmaxv
  obtain haca : c.arena_cap < 2 * dimacsBound := c.harena
  obtain hsca : c.scratch_cap < dimacsBound := c.hscr
  unfold dimacsBound at hmax haca hsca
  obtain hcv_le := hlen.core_ok.cur_vars_le
  obtain hvl0 := hlen.core_ok.vals_len
  obtain hfl0 := hlen.core_ok.flags_len
  obtain hvl := hlen.core_ok.vals_len
  obtain harl := hlen.core_ok.arena_len_arr
  obtain hale := hlen.core_ok.arena_len_le
  obtain hsbl := hlen.scratch_ok.scratch_buf_len
  have hi2 : (idx <<< (1 : Nat)).toNat = 2 * idx.toNat := by
    rw [BitVec.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega
  have hi2p1 : ((idx <<< (1 : Nat)) + 1).toNat = 2 * idx.toNat + 1 := by
    rw [BitVec.toNat_add, hi2]; simp; omega
  have hi2_lt : (idx <<< (1 : Nat)).toNat < s.scratch.scratch_buf.length := by rw [hsbl, hi2]; omega
  have hi2p1_lt : ((idx <<< (1 : Nat)) + 1).toNat < s.scratch.scratch_buf.length := by
    rw [hsbl, hi2p1]; omega
  refine wp_load_of (FullArenaTactics.c0_load_full_scratch_buf hi2_lt hm) ?_
  c0_split
  · have hbin' :
        (s.scratch.scratch_buf[2 * idx.toNat]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32 := by
      simpa [hi2, Nat.mod_eq_of_lt (by omega : 2 * idx.toNat < 2 ^ 64),
        List.getElem?_eq_getElem (by omega : 2 * idx.toNat < s.scratch.scratch_buf.length)]
        using hc
    clear hc
    obtain ⟨ha_lt, hb_lt⟩ := walk_entry_bin_bounds hok hbin'
    let w0 := s.scratch.scratch_buf[2 * idx.toNat]'(by omega)
    let aLit := w0 &&& 0x7FFFFFFF#32
    let bLit := s.scratch.scratch_buf[2 * idx.toNat + 1]'(by omega)
    have ha_v : aLit.toNat < 2 * s.core.cur_vars := by
      simpa [aLit, w0,
        List.getElem?_eq_getElem (by omega : 2 * idx.toNat < s.scratch.scratch_buf.length)]
        using ha_lt
    have hb_v : bLit.toNat < 2 * s.core.cur_vars := by
      simpa [bLit,
        List.getElem?_eq_getElem (by omega : 2 * idx.toNat + 1 < s.scratch.scratch_buf.length)]
        using hb_lt
    have haLit_eq :
        aLit = s.scratch.scratch_buf[(idx <<< (1 : Nat)).toNat]'hi2_lt &&& 0x7FFFFFFF#32 := by
      simp only [aLit, w0, hi2]
    have hbLit_eq : bLit = s.scratch.scratch_buf[((idx <<< (1 : Nat)) + 1).toNat]'hi2p1_lt := by
      simp only [bLit, hi2p1]
    have ha_vals :
        ((s.scratch.scratch_buf[(idx <<< (1 : Nat)).toNat]'hi2_lt &&& 0x7FFFFFFF#32).setWidth
          64).toNat < s.core.vals.length := by
      rw [hvl, zext_toNat _ (by decide), ← haLit_eq]; omega
    refine wp_load_of (FullArenaTactics.c0_load_full_scratch_buf hi2p1_lt hm) ?_
    refine wp_join_safety_slice (ts := [i32, i64]) (fullSafetySlice c) s R (fun _ => True) trivial
      (fun s1 (ch', seen', ()) =>
        (ch' = 0xFFFFFFFF#32 ∨ ch'.toNat < 2 * s.core.cur_vars) ∧
        seen'.toNat ≤ 1 ∧
        s1.scratch = { s.scratch with rng_state := s1.scratch.rng_state })
      (fun J1 s1 (ch', seen', ()) m1 hcore1 hs1 _ ⟨hch1, hsle1, hsc1⟩ hm1 => ?_)
      (fun J1 hJ1 => ?_)
    · dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj, fullSafetySlice_safe] at hs1 hm1
      have hcv1 : s1.core.cur_vars = s.core.cur_vars := by
        rw [fullCoreState_agrees_with_scratch hcore1]
      have hvl1 : s1.core.vals.length = 2 * c.max_vars := hs1.core_ok.vals_len
      have hb_vals1 :
          ((s.scratch.scratch_buf[((idx <<< (1 : Nat)) + 1).toNat]'hi2p1_lt).setWidth 64).toNat <
            s1.core.vals.length := by
        rw [hvl1, zext_toNat _ (by decide), ← hbLit_eq]; omega
      rw [Blocks.get_here]; dsimp only
      refine wp_join_group (ts := [i32, i64])
        (fun (r', _seen2, ()) m2 => ∃ s2 : FullState,
          PreservesCoreSlice FullState.core s1 s2 ∧ s2.LengthsOk c ∧
          (r' = 0xFFFFFFFF#32 ∨ r'.toNat < 2 * s.core.cur_vars) ∧
          s2.scratch = { s.scratch with rng_state := s2.scratch.rng_state } ∧
          (FullMem c s2 ⋆ R) m2)
        (fun J2 (r', _seen2, ()) m2 ⟨s2, hcore2, hs2, hr2, hsc2, hm2⟩ => ?_)
        (fun J2 hJ2 => ?_)
      · c0_steps
        exact hQ (r', ()) s2 m2 (hcore1.trans hcore2) hs2
          ⟨⟨by rw [hsc2], by rw [hsc2]⟩, by rw [hsc2], hr2⟩ hm2
      · c0_steps
        · have hb_v' :
              (s.scratch.scratch_buf[((idx <<< (1 : Nat)) + 1).toNat]'hi2p1_lt).toNat <
                2 * s.core.cur_vars := by
            rw [← hbLit_eq]; exact hb_v
          exact hJ2 (s.scratch.scratch_buf[((idx <<< (1 : Nat)) + 1).toNat]'hi2p1_lt,
              seen' + 1, ()) m1 ⟨s1, rfl, hs1, Or.inr hb_v', hsc1, hm1⟩
        · have hne0 : seen' + 1 ≠ 0 := by bv_omega
          have hb_v' :
              (s.scratch.scratch_buf[((idx <<< (1 : Nat)) + 1).toNat]'hi2p1_lt).toNat <
                2 * s.core.cur_vars := by
            rw [← hbLit_eq]; exact hb_v
          c0_call hRng
          refine ⟨c, s1, R, rfl, hs1, hm1, ?_⟩
          intro rngr s2 m2 hcore2 hs2 hsc2 hm2
          have hsc12 : s2.scratch = { s.scratch with rng_state := s2.scratch.rng_state } := by
            rw [hsc2, hsc1]
          rw [wp_let_urem64_2 (by simpa using hne0), wp_let_eq64_2]; dsimp only
          refine wp_jnz_of (fun _ => ?_) (fun _ => ?_)
          · c0_steps
            exact hJ2 (s.scratch.scratch_buf[((idx <<< (1 : Nat)) + 1).toNat]'hi2p1_lt,
                seen' + 1, ()) m2 ⟨s2, hcore2, hs2, Or.inr hb_v', hsc12, hm2⟩
          · c0_steps
            exact hJ2 (ch', seen' + 1, ()) m2 ⟨s2, hcore2, hs2, hch1, hsc12, hm2⟩
        · exact hJ2 (ch', seen', ()) m1 ⟨s1, rfl, hs1, hch1, hsc1, hm1⟩
    · c0_split
      · refine hJ1 s _ m hm rfl hlen ⟨Or.inr ?_, by simp, rfl⟩
        simpa [haLit_eq] using ha_v
      · exact hJ1 s (0xFFFFFFFF#32, 0#64, ()) m hm rfl hlen ⟨Or.inl rfl, by simp, rfl⟩
  · have hlrg' :
        (s.scratch.scratch_buf[2 * idx.toNat]?.getD 0#32 &&& 0x80000000#32) = 0#32 := by
      simpa [hi2, Nat.mod_eq_of_lt (by omega : 2 * idx.toNat < 2 ^ 64),
        List.getElem?_eq_getElem (by omega : 2 * idx.toNat < s.scratch.scratch_buf.length)]
        using hc
    clear hc
    let w0 := s.scratch.scratch_buf[2 * idx.toNat]'(by omega)
    have hw0_ref : w0.toNat ∈ fullArenaClauseRefs s := by
      unfold FullWalkEntryOk at hok
      simp only [hlrg', ne_eq, not_true_eq_false, ↓reduceIte] at hok
      simpa [w0, List.getElem?_eq_getElem (by omega : 2 * idx.toNat < s.scratch.scratch_buf.length)]
        using hok.1
    have hw0_ng : fullArenaClauseGarb s w0.toNat = false := by
      unfold FullWalkEntryOk at hok
      simp only [hlrg', ne_eq, not_true_eq_false, ↓reduceIte] at hok
      simpa [w0, List.getElem?_eq_getElem (by omega : 2 * idx.toNat < s.scratch.scratch_buf.length)]
        using hok.2
    have hwf := ha.refs_wf w0.toNat hw0_ref
    have hw0_2_lt : (w0.setWidth 64 + 2).toNat < s.core.arena.length := by c0_bound
    have hw0_2_lt' :
        ((s.scratch.scratch_buf[(idx <<< (1 : Nat)).toNat]'hi2_lt).setWidth 64 + 2).toNat <
          s.core.arena.length := by
      simpa [w0, hi2] using hw0_2_lt
    refine wp_load_of (FullArenaTactics.c0_load_full_arena hw0_2_lt' hm) ?_
    let sz := s.core.arena[(w0.setWidth 64 + 2).toNat]'hw0_2_lt
    have hsz_eq : sz.toNat = fullArenaClauseSize s w0.toNat := by
      unfold fullArenaClauseSize fullArenaClauseSizeCore
      have hw2 : (w0.setWidth 64 + 2).toNat = w0.toNat + 2 := by c0_bound
      simp only [sz, hw2, List.getElem?_eq_getElem (by omega : w0.toNat + 2 < s.core.arena.length),
        Option.getD_some]
    have hw0_bd' :
        w0.toNat + 3 + fullArenaClauseSizeCore s.core w0.toNat ≤ s.core.arena.length := by
      have hle := Nat.le_trans hwf.2.2.1 hwf.2.2.2.1; omega
    have hw0_bd : w0.toNat + 3 + sz.toNat ≤ s.core.arena.length := by
      unfold fullArenaClauseSize at hsz_eq; dsimp only [sz] at hsz_eq ⊢; rw [hsz_eq]; exact hw0_bd'
    refine wp_loop_safety_slice (fullSafetySlice c) s R (fun _ => True) trivial
      (fun s1 (chosen, seen, i, ()) =>
        i.toNat ≤ sz.toNat ∧ seen.toNat ≤ i.toNat ∧
        (chosen = 0xFFFFFFFF#32 ∨ chosen.toNat < 2 * s.core.cur_vars) ∧
        s1.scratch = { s.scratch with rng_state := s1.scratch.rng_state })
      (fun (_, _, i, ()) => sz.toNat - i.toNat) (fun J hLoop => ?_)
      (fun J s1 (chosen, seen, i, ()) m1 hcore1 hs1 _ ⟨hile, hsle, hch, hsc1⟩ hm1 hLoop => ?_)
    · c0_steps
      exact hLoop s (0xFFFFFFFF#32, 0#64, 0#32, ()) m hm rfl hlen
        ⟨by simp, by simp, Or.inl rfl, rfl⟩
    · dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj, fullSafetySlice_safe] at hs1 hm1
      have heq1 := fullCoreState_agrees_with_scratch hcore1
      obtain harl1 := hs1.core_ok.arena_len_arr
      obtain hvl1 := hs1.core_ok.vals_len
      rw [Blocks.get_here]; dsimp only
      c0_to_jnz
      refine wp_jnz_of (fun hc_i => ?_) (fun _ => ?_)
      · simp only [Arg.val_var, liftCmp, evalBits_ult_eq, BitVec.ult, decide_eq_true_eq] at hc_i
        have hw0_eq_sb : s.scratch.scratch_buf[(idx <<< (1 : Nat)).toNat]'hi2_lt = w0 := by
          dsimp only [w0]; congr 1
        have hw2_mod : (w0.toNat + 2) % 2 ^ 64 = w0.toNat + 2 := Nat.mod_eq_of_lt (by omega)
        have hi_lt : i.toNat < sz.toNat := by
          simpa [sz, w0, hi2, Nat.mod_eq_of_lt (by omega : 2 * idx.toNat < 2 ^ 64), hw2_mod]
            using hc_i
        have hli_eq : (w0.setWidth 64 + 3 + i.setWidth 64).toNat = w0.toNat + 3 + i.toNat := by
          c0_bound
        have hli_ar : (w0.setWidth 64 + 3 + i.setWidth 64).toNat < s1.core.arena.length := by
          rw [harl1]; omega
        have hli_ar' :
            ((s.scratch.scratch_buf[(idx <<< (1 : Nat)).toNat]'hi2_lt).setWidth 64 + 3 +
              i.setWidth 64).toNat < s1.core.arena.length := by
          rw [hw0_eq_sb]; exact hli_ar
        have hlit_mem : (s.core.arena[w0.toNat + 3 + i.toNat]'(by omega)).toNat ∈
            fullArenaClauseLits s w0.toNat :=
          (mem_fullArenaClauseLitsCore_iff hw0_bd').mpr
            ⟨i.toNat, by unfold fullArenaClauseSize at hsz_eq; rw [← hsz_eq]; exact hi_lt, rfl⟩
        have hlit_lt : (s.core.arena[w0.toNat + 3 + i.toNat]'(by omega)).toNat <
            2 * s.core.cur_vars := ha.lits_lt w0.toNat hw0_ref hw0_ng _ hlit_mem
        have hli_el :
            s1.core.arena[((s.scratch.scratch_buf[(idx <<< (1 : Nat)).toNat]'hi2_lt).setWidth 64 +
              3 + i.setWidth 64).toNat]'hli_ar' =
            s.core.arena[w0.toNat + 3 + i.toNat]'(by omega) := by
          simp only [heq1, hw0_eq_sb, hli_eq]
        have hlit_v :
            (s1.core.arena[((s.scratch.scratch_buf[(idx <<< (1 : Nat)).toNat]'hi2_lt).setWidth 64 +
              3 + i.setWidth 64).toNat]'hli_ar').toNat < 2 * s.core.cur_vars := by
          rw [hli_el]; exact hlit_lt
        have hseen_pos : 0 < (seen + 1).toNat := by c0_bound
        have hi1 : (i + 1).toNat = i.toNat + 1 := by
          have hsz_lt := sz.isLt; bv_omega
        have hlit_vals1 :
            ((s1.core.arena[((s.scratch.scratch_buf[(idx <<< (1 : Nat)).toNat]'hi2_lt).setWidth 64 +
              3 + i.setWidth 64).toNat]'hli_ar').setWidth 64).toNat < s1.core.vals.length := by
          rw [hvl1, zext_toNat _ (by decide), hli_el]; omega
        repeat (first | rw [wp_let_zext32_2] | rw [wp_let_mul64_2] | rw [wp_let_add64_2])
        dsimp only
        refine wp_load_of (FullArenaTactics.c0_load_full_arena (s := s1) hli_ar' hm1) ?_
        refine wp_join_group (ts := [i32, i64])
          (fun (ch', seen', ()) m' => ∃ s2 : FullState,
            PreservesCoreSlice FullState.core s1 s2 ∧ s2.LengthsOk c ∧
            seen'.toNat ≤ i.toNat + 1 ∧
            (ch' = 0xFFFFFFFF#32 ∨ ch'.toNat < 2 * s.core.cur_vars) ∧
            s2.scratch = { s.scratch with rng_state := s2.scratch.rng_state } ∧
            (FullMem c s2 ⋆ R) m')
          (fun Ji (ch', seen', ()) m' ⟨s2, hcore2, hs2, hsle2, hch2, hsc2, hm2⟩ => ?_)
          (fun Ji hJi => ?_)
        · rw [Blocks.get_here]; dsimp only
          rw [wp_let_add32_2]; dsimp only
          exact hLoop s2 (ch', seen', i + 1, ()) m' hm2 (by dsimp only; rw [hi1]; omega)
            hcore2 hs2 ⟨by rw [hi1]; omega, by rw [hi1]; exact hsle2, hch2, hsc2⟩
        · rw [wp_let_zext32_2, wp_let_add64_2]; dsimp only
          refine wp_load_of (FullArenaTactics.c0_load_full_vals (s := s1) hlit_vals1 hm1) ?_
          repeat (first
            | rw [wp_let_trunc32_8_2] | rw [wp_let_sext8_32_2] | rw [wp_let_eq32_2])
          dsimp only
          refine wp_jnz_of (fun _ => ?_) (fun _ => ?_)
          · rw [wp_let_add64_2]; dsimp only
            refine wp_join_group (ts := [i32])
              (fun (ch', ()) m' => ∃ s2 : FullState,
                PreservesCoreSlice FullState.core s1 s2 ∧ s2.LengthsOk c ∧
                (ch' = 0xFFFFFFFF#32 ∨ ch'.toNat < 2 * s.core.cur_vars) ∧
                s2.scratch = { s.scratch with rng_state := s2.scratch.rng_state } ∧
                (FullMem c s2 ⋆ R) m')
              (fun Js (ch', ()) m' ⟨s2, hcore2, hs2, hch2, hsc2, hm2⟩ =>
                hJi (ch', seen + 1, ()) m' ⟨s2, hcore2, hs2, by c0_bound, hch2, hsc2, hm2⟩)
              (fun Js hJs => ?_)
            rw [wp_let_eq32_2]; dsimp only
            refine wp_jnz_of (fun _ => ?_) (fun _ => ?_)
            · exact hJs (_, ()) m1 ⟨s1, rfl, hs1, Or.inr (heq1 ▸ hlit_v), hsc1, hm1⟩
            · c0_call hRng
              refine ⟨c, s1, R, rfl, hs1, hm1, ?_⟩
              intro rngr s2 m2 hcore2 hs2 hsc2 hm2
              have hsc12 : s2.scratch = { s.scratch with rng_state := s2.scratch.rng_state } := by
                rw [hsc2, hsc1]
              have hne0 : seen + 1 ≠ 0 := by bv_omega
              rw [wp_let_urem64_2 (by simpa using hne0), wp_let_eq64_2]; dsimp only
              refine wp_jnz_of (fun _ => ?_) (fun _ => ?_)
              · exact hJs (_, ()) m2 ⟨s2, hcore2, hs2, Or.inr hlit_v, hsc12, hm2⟩
              · exact hJs (chosen, ()) m2 ⟨s2, hcore2, hs2, hch, hsc12, hm2⟩
          · exact hJi (chosen, seen, ()) m1 ⟨s1, rfl, hs1, by c0_bound, hch, hsc1, hm1⟩
      · exact hQ (chosen, ()) s1 m1 hcore1 hs1
          ⟨⟨by rw [hsc1], by rw [hsc1]⟩, by rw [hsc1], hch⟩ hm1

/-! ## 2. `full_next_dec_var` -/

theorem full_next_dec_var_wp (Γ : Env)
    (hPop : ∀ a m Q X, fullHeapPopSpec a m Q X → Γ "full_heap_pop" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullNextDecVarSpec a m Q X → Func.wp Γ full_next_dec_var_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj, fullSafetySlice_safe] at hlen hm hQ
  obtain hmax : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmax
  obtain hcv_le := hlen.core_ok.cur_vars_le
  obtain hvl0 := hlen.core_ok.vals_len
  obtain hfl0 := hlen.core_ok.flags_len
  c0_to_group
  refine wp_join_safety_slice (ts := []) (fullSafetySlice c) s R (fun _ => True) trivial
    (fun s1 _ => s1.scratch.last_learned = s.scratch.last_learned ∧
      s1.scratch.extend_len = s.scratch.extend_len)
    (fun Jf s1 _ m1 hcore1 hs1 _ ⟨hll1, hel1⟩ hm1 => ?_) (fun Jf hJf => ?_)
  · dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj, fullSafetySlice_safe] at hs1 hm1
    have heq1 := fullCoreState_agrees_with_scratch hcore1
    obtain hcv_le1 := hs1.core_ok.cur_vars_le
    obtain hfl1 := hs1.core_ok.flags_len
    obtain hvl1 := hs1.core_ok.vals_len
    c0_steps
    refine wp_loop_safety_slice (fullSafetySlice c) s1 R (fun _ => True) trivial
      (fun s2 ((v : BitVec 64), ()) => v.toNat ≤ s.core.cur_vars ∧
        s2.scratch.last_learned = s.scratch.last_learned ∧
        s2.scratch.extend_len = s.scratch.extend_len)
      (fun ((v : BitVec 64), ()) => s.core.cur_vars - v.toNat)
      (fun Jv hJv => ?_)
      (fun Jv s2 ((v : BitVec 64), ()) m2 hcore2 hs2 _ ⟨hvle, hll2, hel2⟩ hm2 hJv => ?_)
    · c0_steps; exact hJv s1 (0#64, ()) m1 hm1 rfl hs1 ⟨by simp, hll1, hel1⟩
    · dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj, fullSafetySlice_safe] at hs2 hm2
      have heq2 := fullCoreState_agrees_with_scratch hcore2
      obtain hfl2 := hs2.core_ok.flags_len
      obtain hvl2 := hs2.core_ok.vals_len
      rw [Blocks.get_here]; dsimp only
      rw [wp_let_ult64_2]
      refine wp_jnz_of (fun hc_v => ?_) (fun _ => ?_)
      · simp only [Arg.val_var] at hc_v; c0_cond hc_v
        have hv_lt : v.toNat < s.core.cur_vars := by omega
        have hv_fl : v.toNat < s2.core.flags.length := by rw [hfl2]; omega
        have hv2_lt : (v <<< (1 : Nat)).toNat < s2.core.vals.length := by
          rw [hvl2, BitVec.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega
        have hv1 : (v + 1).toNat = v.toNat + 1 := by bv_omega
        refine wp_join_safety_slice (ts := []) (fullSafetySlice c) s2 R (fun _ => True) trivial
          (fun s3 _ => s3.scratch.last_learned = s.scratch.last_learned ∧
            s3.scratch.extend_len = s.scratch.extend_len)
          (fun Js s3 _ m3 hcore3 hs3 _ ⟨hll3, hel3⟩ hm3 => ?_) (fun Js hJs => ?_)
        · dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj,
            fullSafetySlice_safe] at hs3 hm3
          c0_steps
          exact hJv s3 (v + 1, ()) m3 hm3 (by dsimp only; rw [hv1]; omega) hcore3 hs3
            ⟨by rw [hv1]; omega, hll3, hel3⟩
        · have hv2_lt' : (2 * v.toNat % 2 ^ 64) < s2.core.vals.length := by
            rw [hvl2, Nat.mod_eq_of_lt (by omega)]; omega
          repeat (first
            | rw [wp_let_sext32_64_2] | rw [wp_let_mul64_2]
            | rw [wp_let_shl64_2] | rw [wp_let_add64_2])
          dsimp only
          refine wp_load_of (FullArenaTactics.c0_load_full_flags hv_fl hm2) ?_
          rw [wp_let_and32_2, wp_let_ne32_2]; dsimp only
          refine wp_jnz_of (fun hc_fl => ?_) (fun _ => ?_)
          · simp only [Arg.val_var, Arg.val_imm, bne_iff_ne, ne_eq] at hc_fl
            have hfl_v : s2.core.flags[v.toNat]'hv_fl &&& 1#32 ≠ 0#32 := hc_fl
            repeat (first
              | rw [wp_let_sext32_64_2] | rw [wp_let_shl64_2] | rw [wp_let_add64_2])
            dsimp only
            refine wp_load_of (FullArenaTactics.c0_load_full_vals (s := s2) ?_ hm2) ?_
            · simp only [BitVec.toNat_shiftLeft, Arg.val_var, Arg.val_imm]
              rw [show (BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64 = 1 from rfl]
              simp only [Nat.shiftLeft_eq, Nat.pow_one]
              rw [Nat.mul_comm]; exact hv2_lt'
            · repeat (first
                | rw [wp_let_trunc32_8_2] | rw [wp_let_sext8_32_2] | rw [wp_let_eq32_2])
              dsimp only
              refine wp_jnz_of (fun hc_val => ?_) (fun _ => ?_)
              · simp only [Arg.val_var] at hc_val; c0_cond hc_val
                have h2v : (v <<< (1 : Nat)).toNat = 2 * v.toNat := by
                  rw [BitVec.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega
                have hval_v : s2.core.vals[2 * v.toNat % 2 ^ 64]'(by
                    rw [hvl2, Nat.mod_eq_of_lt (by omega)]; omega) = 0#8 :=
                  sext32_eq_zero hc_val
                simp only [heq2, heq1, Nat.mod_eq_of_lt (by omega : 2 * v.toNat < 2 ^ 64)]
                  at hval_v
                exact hQ (v, ()) s2 m2 (hcore1.trans hcore2) hs2
                  ⟨⟨hll2, hel2⟩, Or.inr ⟨hv_lt,
                    by rw [List.getElem?_eq_getElem (by omega : 2 * v.toNat < _)]
                       simpa using hval_v⟩⟩ hm2
              · exact hJs s2 () m2 hm2 rfl hs2 ⟨hll2, hel2⟩
          · exact hJs s2 () m2 hm2 rfl hs2 ⟨hll2, hel2⟩
      · exact hQ (0xFFFFFFFFFFFFFFFF#64, ()) s2 m2 (hcore1.trans hcore2) hs2
          ⟨⟨hll2, hel2⟩, Or.inl rfl⟩ hm2
  · c0_split
    · clear hc
      refine wp_join_safety_slice (ts := []) (fullSafetySlice c) s R (fun _ => True) trivial
        (fun s1 _ => s1.scratch.last_learned = s.scratch.last_learned ∧
          s1.scratch.extend_len = s.scratch.extend_len)
        (fun Js s1 _ m1 hcore1 hs1 _ ⟨hll1, hel1⟩ hm1 => ?_) (fun Js hJs => ?_)
      · dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj,
          fullSafetySlice_safe] at hs1 hm1
        c0_steps; exact hJf s1 () m1 hm1 hcore1 hs1 ⟨hll1, hel1⟩
      · let s0 : FullState :=
          { s with scratch := { s.scratch with heap_len := s.scratch.heap_len % 2 ^ 64 } }
        have hm0 : (FullMem c s0 ⋆ R) m := by rwa [FullMem_with_heap_len_mod]
        refine wp_loop_safety_slice_state (ts := []) (fullSafetySlice c) s0 R
          (fun _ => True) trivial
          (fun s1 _ => s1.scratch.heap_len < 2 ^ 64 ∧
            s1.scratch.last_learned = s.scratch.last_learned ∧
            s1.scratch.extend_len = s.scratch.extend_len)
          (fun s1 _ => s1.scratch.heap_len)
          (fun Jh hJh => ?_)
          (fun Jh s1 _ m1 hcore1 hs1 _ ⟨hhl_lt1, hll1, hel1⟩ hm1 hJh => ?_)
        · c0_steps
          exact hJh s0 () m hm0 rfl
            ⟨hlen.core_ok, { hlen.scratch_ok with walk_vals_len := hlen.scratch_ok.walk_vals_len }⟩
            ⟨Nat.mod_lt _ (by decide), rfl, rfl⟩
        · dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj,
            fullSafetySlice_safe] at hs1 hm1
          have heq1 := fullCoreState_agrees_with_scratch hcore1
          obtain hhl1 := hs1.scratch_ok.heap_len_arr
          obtain hfl1 := hs1.core_ok.flags_len
          obtain hvl1 := hs1.core_ok.vals_len
          rw [Blocks.get_here]; try dsimp only
          rw [wp_let_add64_2]
          refine wp_load_of (FullArenaTactics.load_full_heap_len hm1) ?_
          rw [wp_let_ugt64_2]; dsimp only
          refine wp_jnz_of (fun hc_gt0 => ?_) (fun _ => ?_)
          · simp only [Arg.val_var] at hc_gt0; c0_cond hc_gt0
            have hpos1 : 0 < s1.scratch.heap_len := by
              rw [Nat.mod_eq_of_lt hhl_lt1] at hc_gt0; exact hc_gt0
            rw [wp_let_add64_2]
            refine wp_load_of (FullArenaTactics.load_full_heap_len hm1) ?_
            rw [wp_let_ule64_2]; dsimp only
            refine wp_jnz_of (fun hc_lecv => ?_) (fun _ => ?_)
            · simp only [Arg.val_var] at hc_lecv; c0_cond hc_lecv
              have hle1 : s1.scratch.heap_len ≤ s.core.cur_vars := by
                rw [Nat.mod_eq_of_lt hhl_lt1,
                  Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc_lecv
                exact hc_lecv
              let top := s1.scratch.heap[0]'(by omega)
              have hhp0 : loadVal m1 i32
                  (c.pHeap + (BitVec.signExtend 64 (0 : BitVec 32)) * 4) = some top := by
                have hraw := FullArenaTactics.c0_load_full_heap (s := s1)
                  (i := BitVec.signExtend 64 0)
                  (by rw [show (BitVec.signExtend 64 (0 : BitVec 32)).toNat = 0 from rfl]; omega)
                  hm1
                simpa only [show (BitVec.signExtend 64 (0 : BitVec 32)).toNat = 0 from rfl] using
                  hraw
              rw [wp_let_sext32_64_2, wp_let_mul64_2, wp_let_add64_2]; dsimp only
              refine wp_load_of hhp0 ?_
              rw [wp_let_zext32_2, wp_let_uge64_2]; dsimp only
              refine wp_jnz_of (fun _ => ?_) (fun hc_tlt => ?_)
              · exact hJs s1 () m1 hm1 hcore1 hs1 ⟨hll1, hel1⟩
              · simp only [Arg.val_var] at hc_tlt
                have htop_lt : top.toNat < s.core.cur_vars := by
                  have h1 :
                      ¬ (BitVec.ofNat 64 s.core.cur_vars).toNat ≤ (top.setWidth 64).toNat := by
                    simpa [BitVec.ule] using hc_tlt
                  rw [zext_toNat _ (by decide), BitVec.toNat_ofNat,
                    Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at h1
                  omega
                have htop2_lt : ((top.setWidth 64) <<< (1 : Nat)).toNat < s1.core.vals.length := by
                  rw [hvl1, BitVec.toNat_shiftLeft, zext_toNat _ (by decide)]
                  simp [Nat.shiftLeft_eq]; omega
                refine wp_join_safety_slice (ts := []) (fullSafetySlice c) s1 R
                  (fun _ => True) trivial
                  (fun s2 _ => s2.scratch.heap_len = s1.scratch.heap_len ∧
                    s2.scratch.last_learned = s.scratch.last_learned ∧
                    s2.scratch.extend_len = s.scratch.extend_len)
                  (fun Jpop s2 _ m2 hcore2 hs2 _ ⟨hhl_eq2, hll2, hel2⟩ hm2 => ?_)
                  (fun Jpop hJpop => ?_)
                · dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj,
                    fullSafetySlice_safe] at hs2 hm2
                  have heq2 := fullCoreState_agrees_with_scratch hcore2
                  c0_steps
                  c0_call hPop
                  refine ⟨c, s2, R, rfl, hs2, hm2, ?_⟩
                  intro _ s3 m3 hcore3 hs3 ⟨_, hdec, hpres3⟩ hm3
                  have hs3_eq := hdec ⟨by rw [hhl_eq2]; exact hpos1,
                    by rw [hhl_eq2, heq2, heq1]; exact hle1⟩
                  exact hJh s3 () m3 hm3 (by rw [hs3_eq, hhl_eq2]; omega)
                    (hcore2.trans hcore3) hs3
                    ⟨by rw [hs3_eq, hhl_eq2]; omega,
                      hpres3.1.1.trans hll2, hpres3.1.2.trans hel2⟩
                · repeat (first
                    | rw [wp_let_sext32_64_2] | rw [wp_let_zext32_2]
                    | rw [wp_let_mul64_2] | rw [wp_let_shl64_2] | rw [wp_let_add64_2])
                  dsimp only
                  refine wp_load_of (FullArenaTactics.c0_load_full_flags
                    (s := s1) (by
                      simp only [Arg.val_var]; rw [hfl1, zext_toNat _ (by decide)]; omega) hm1) ?_
                  rw [wp_let_and32_2, wp_let_ne32_2]; dsimp only
                  refine wp_jnz_of (fun hc_flt => ?_) (fun _ => ?_)
                  · simp only [Arg.val_var, Arg.val_imm, bne_iff_ne, ne_eq] at hc_flt
                    have hzt0 : (BitVec.setWidth 64 top).toNat = top.toNat :=
                      zext_toNat top (by decide)
                    have hfl_t : s1.core.flags[top.toNat]'(by omega) &&& 1#32 ≠ 0#32 := by
                      simp only [hzt0] at hc_flt; exact hc_flt
                    repeat (first
                      | rw [wp_let_sext32_64_2] | rw [wp_let_zext32_2]
                      | rw [wp_let_shl64_2] | rw [wp_let_add64_2])
                    dsimp only
                    refine wp_load_of (FullArenaTactics.c0_load_full_vals
                      (s := s1) htop2_lt hm1) ?_
                    repeat (first
                      | rw [wp_let_trunc32_8_2] | rw [wp_let_sext8_32_2] | rw [wp_let_eq32_2])
                    dsimp only
                    refine wp_jnz_of (fun hc_valt => ?_) (fun _ => ?_)
                    · simp only [Arg.val_var] at hc_valt; c0_cond hc_valt
                      have hval_t : s1.core.vals[((top.setWidth 64) <<< (1 : Nat)).toNat]'(by
                          omega) = 0#8 := sext32_eq_zero hc_valt
                      have h2t : ((top.setWidth 64) <<< (1 : Nat)).toNat = 2 * top.toNat := by
                        rw [BitVec.toNat_shiftLeft, zext_toNat _ (by decide)]
                        simp [Nat.shiftLeft_eq]; omega
                      have hzt : (top.setWidth 64).toNat = top.toNat := zext_toNat _ (by decide)
                      simp only [heq1] at hval_t
                      rw [wp_let_zext32_2]; dsimp only
                      exact hQ (top.setWidth 64, ()) s1 m1 hcore1 hs1 ⟨⟨hll1, hel1⟩, Or.inr ⟨by
                        rw [hzt]; exact htop_lt,
                        by rw [hzt, List.getElem?_eq_getElem (by omega : 2 * top.toNat < _)]
                           simpa [h2t] using hval_t⟩⟩ hm1
                    · exact hJpop s1 () m1 hm1 rfl hs1 ⟨rfl, hll1, hel1⟩
                  · exact hJpop s1 () m1 hm1 rfl hs1 ⟨rfl, hll1, hel1⟩
            · exact hJs s1 () m1 hm1 hcore1 hs1 ⟨hll1, hel1⟩
          · exact hJs s1 () m1 hm1 hcore1 hs1 ⟨hll1, hel1⟩
    · clear hc
      c0_steps
      refine wp_loop_safety_slice (ts := [i64, i64]) (fullSafetySlice c) s R
        (fun _ => True) trivial
        (fun s1 ((cur : BitVec 64), (steps : BitVec 64), ()) =>
          steps.toNat ≤ s.core.cur_vars ∧
          s1.scratch.last_learned = s.scratch.last_learned ∧
          s1.scratch.extend_len = s.scratch.extend_len)
        (fun (_, (steps : BitVec 64), ()) => s.core.cur_vars - steps.toNat)
        (fun J1 hJ1 => ?_)
        (fun J1 s1 ((cur : BitVec 64), (steps : BitVec 64), ()) m1 hcore1 hs1 _
            ⟨hst1, hll1, hel1⟩ hm1 hJ1 => ?_)
      · c0_steps; exact hJ1 s (s.scratch.q_search_idx, 0#64, ()) m hm rfl hlen ⟨by simp, rfl, rfl⟩
      · dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj,
          fullSafetySlice_safe] at hs1 hm1
        have heq1 := fullCoreState_agrees_with_scratch hcore1
        obtain hfl1 := hs1.core_ok.flags_len
        obtain hvl1 := hs1.core_ok.vals_len
        obtain hqpl1 := hs1.scratch_ok.q_prev_len
        obtain hqsl1 := hs1.scratch_ok.q_stamp_len
        rw [Blocks.get_here]; dsimp only
        refine wp_join_safety_slice (ts := []) (fullSafetySlice c) s1 R (fun _ => True) trivial
          (fun s2 _ => s2.scratch.last_learned = s.scratch.last_learned ∧
            s2.scratch.extend_len = s.scratch.extend_len)
          (fun J2w s2 _ m2 hcore2 hs2 _ ⟨hll2, hel2⟩ hm2 => ?_) (fun J2w hJ2w => ?_)
        · dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj,
            fullSafetySlice_safe] at hs2 hm2
          have heq2 := fullCoreState_agrees_with_scratch hcore2
          obtain hfl2 := hs2.core_ok.flags_len
          obtain hvl2 := hs2.core_ok.vals_len
          obtain hqpl2 := hs2.scratch_ok.q_prev_len
          obtain hqsl2 := hs2.scratch_ok.q_stamp_len
          rw [Blocks.get_here]; try dsimp only
          rw [wp_let_add64_2]
          refine wp_load_of (FullArenaTactics.load_full_q_last hm2) ?_
          refine wp_loop_safety_slice (ts := [i64, i64]) (fullSafetySlice c) s2 R
            (fun _ => True) trivial
            (fun s3 ((cur2 : BitVec 64), (steps2 : BitVec 64), ()) =>
              steps2.toNat ≤ s.core.cur_vars ∧
              s3.scratch.last_learned = s.scratch.last_learned ∧
              s3.scratch.extend_len = s.scratch.extend_len)
            (fun (_, (steps2 : BitVec 64), ()) => s.core.cur_vars - steps2.toNat)
            (fun J2 hJ2 => ?_)
            (fun J2 s3 ((cur2 : BitVec 64), (steps2 : BitVec 64), ()) m3 hcore3 hs3 _
                ⟨hst3, hll3, hel3⟩ hm3 hJ2 => ?_)
          · c0_steps
            exact hJ2 s2 (s2.scratch.q_last, 0#64, ()) m2 hm2 rfl hs2 ⟨by simp, hll2, hel2⟩
          · dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj,
              fullSafetySlice_safe] at hs3 hm3
            have heq3 := fullCoreState_agrees_with_scratch hcore3
            obtain hfl3 := hs3.core_ok.flags_len
            obtain hvl3 := hs3.core_ok.vals_len
            obtain hqpl3 := hs3.scratch_ok.q_prev_len
            obtain hqsl3 := hs3.scratch_ok.q_stamp_len
            rw [Blocks.get_here]; dsimp only
            rw [wp_let_ult64_2]; dsimp only
            refine wp_jnz_of (fun hc_c2 => ?_) (fun _ => ?_)
            · simp only [Arg.val_var] at hc_c2; c0_cond hc_c2
              have hcur2_lt : cur2.toNat < s.core.cur_vars := by
                rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc_c2
                exact hc_c2
              rw [wp_let_ult64_2]; dsimp only
              refine wp_jnz_of (fun hc_st2 => ?_) (fun _ => ?_)
              · simp only [Arg.val_var] at hc_st2; c0_cond hc_st2
                rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc_st2
                have hcur22_lt : (cur2 <<< (1 : Nat)).toNat < s3.core.vals.length := by
                  rw [hvl3, BitVec.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega
                have hst2' : (steps2 + 1).toNat = steps2.toNat + 1 := by bv_omega
                refine wp_join_safety_slice (ts := []) (fullSafetySlice c) s3 R
                  (fun _ => True) trivial
                  (fun s4 _ => s4.scratch.last_learned = s.scratch.last_learned ∧
                    s4.scratch.extend_len = s.scratch.extend_len)
                  (fun Jnxt s4 _ m4 hcore4 hs4 _ ⟨hll4, hel4⟩ hm4 => ?_) (fun Jnxt hJnxt => ?_)
                · dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj,
                    fullSafetySlice_safe] at hs4 hm4
                  obtain hqpl4 := hs4.scratch_ok.q_prev_len
                  c0_steps
                  exact hJ2 s4 ((s4.scratch.q_prev[cur2.toNat]'(by omega)).setWidth 64,
                    steps2 + 1, ()) m4 hm4 (by dsimp only; rw [hst2']; omega) hcore4 hs4
                    ⟨by rw [hst2']; omega, hll4, hel4⟩
                · repeat (first
                    | rw [wp_let_sext32_64_2] | rw [wp_let_mul64_2]
                    | rw [wp_let_shl64_2] | rw [wp_let_add64_2])
                  dsimp only
                  refine wp_load_of (FullArenaTactics.c0_load_full_flags
                    (s := s3) (by simp only [Arg.val_var]; rw [hfl3]; omega) hm3) ?_
                  rw [wp_let_and32_2, wp_let_ne32_2]; dsimp only
                  refine wp_jnz_of (fun hc_fl2 => ?_) (fun _ => ?_)
                  · simp only [Arg.val_var, Arg.val_imm, bne_iff_ne, ne_eq] at hc_fl2
                    have hfl_c2 : s3.core.flags[cur2.toNat]'(by omega) &&& 1#32 ≠ 0#32 := hc_fl2
                    repeat (first
                      | rw [wp_let_sext32_64_2] | rw [wp_let_shl64_2] | rw [wp_let_add64_2])
                    dsimp only
                    refine wp_load_of (FullArenaTactics.c0_load_full_vals
                      (s := s3) hcur22_lt hm3) ?_
                    repeat (first
                      | rw [wp_let_trunc32_8_2] | rw [wp_let_sext8_32_2] | rw [wp_let_eq32_2])
                    dsimp only
                    refine wp_jnz_of (fun hc_val2 => ?_) (fun _ => ?_)
                    · simp only [Arg.val_var] at hc_val2; c0_cond hc_val2
                      have hval_c2 : s3.core.vals[(cur2 <<< (1 : Nat)).toNat]'(by omega) =
                          0#8 := sext32_eq_zero hc_val2
                      have h2c : (cur2 <<< (1 : Nat)).toNat = 2 * cur2.toNat := by
                        rw [BitVec.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega
                      let qss2 := (s3.scratch.q_stamp[cur2.toNat]'(by rw [hqsl3]; omega)).setWidth
                        64
                      let s3' : FullState :=
                        { s3 with scratch :=
                          { s3.scratch with q_search_idx := cur2, q_search_stamp := qss2 } }
                      rw [wp_let_add64_2]; dsimp only
                      refine wp_store_sep (FullArenaTactics.store_full_q_search_idx cur2 hm3) ?_
                      intro m3a hm3a
                      repeat (first | rw [wp_let_mul64_2] | rw [wp_let_add64_2])
                      dsimp only
                      refine wp_load_of (FullArenaTactics.c0_load_full_q_stamp
                        (s := _) (by simp only [Arg.val_var]; rw [hqsl3]; omega) hm3a) ?_
                      repeat (first | rw [wp_let_zext32_2] | rw [wp_let_add64_2])
                      dsimp only
                      refine wp_store_sep (FullArenaTactics.store_full_q_search_stamp _ hm3a) ?_
                      intro m3b hm3b
                      simp only [heq3, heq2, heq1] at hval_c2
                      exact hQ (cur2, ()) s3' m3b (hcore1.trans (hcore2.trans hcore3))
                        ⟨hs3.core_ok,
                          { hs3.scratch_ok with walk_vals_len := hs3.scratch_ok.walk_vals_len }⟩
                        ⟨⟨hll3, hel3⟩, Or.inr ⟨hcur2_lt,
                          by rw [List.getElem?_eq_getElem (by omega : 2 * cur2.toNat < _)]
                             simpa [h2c] using hval_c2⟩⟩ hm3b
                    · exact hJnxt s3 () m3 hm3 rfl hs3 ⟨hll3, hel3⟩
                  · exact hJnxt s3 () m3 hm3 rfl hs3 ⟨hll3, hel3⟩
              · exact hJf s3 () m3 hm3 (hcore1.trans (hcore2.trans hcore3)) hs3 ⟨hll3, hel3⟩
            · exact hJf s3 () m3 hm3 (hcore1.trans (hcore2.trans hcore3)) hs3 ⟨hll3, hel3⟩
        · rw [wp_let_ult64_2]; dsimp only
          refine wp_jnz_of (fun hc_c1 => ?_) (fun _ => ?_)
          · simp only [Arg.val_var] at hc_c1; c0_cond hc_c1
            have hcur_lt : cur.toNat < s.core.cur_vars := by
              rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc_c1
              exact hc_c1
            rw [wp_let_ult64_2]; dsimp only
            refine wp_jnz_of (fun hc_st1 => ?_) (fun _ => ?_)
            · simp only [Arg.val_var] at hc_st1; c0_cond hc_st1
              rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc_st1
              have hcur2_lt : (cur <<< (1 : Nat)).toNat < s1.core.vals.length := by
                rw [hvl1, BitVec.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega
              have hst1' : (steps + 1).toNat = steps.toNat + 1 := by bv_omega
              refine wp_join_safety_slice (ts := []) (fullSafetySlice c) s1 R
                (fun _ => True) trivial
                (fun s2 _ => s2.scratch.last_learned = s.scratch.last_learned ∧
                  s2.scratch.extend_len = s.scratch.extend_len)
                (fun Jnxt s2 _ m2 hcore2 hs2 _ ⟨hll2, hel2⟩ hm2 => ?_) (fun Jnxt hJnxt => ?_)
              · dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj,
                  fullSafetySlice_safe] at hs2 hm2
                obtain hqpl2 := hs2.scratch_ok.q_prev_len
                c0_steps
                exact hJ1 s2 ((s2.scratch.q_prev[cur.toNat]'(by omega)).setWidth 64,
                  steps + 1, ()) m2 hm2 (by dsimp only; rw [hst1']; omega) hcore2 hs2
                  ⟨by rw [hst1']; omega, hll2, hel2⟩
              · repeat (first
                  | rw [wp_let_sext32_64_2] | rw [wp_let_mul64_2]
                  | rw [wp_let_shl64_2] | rw [wp_let_add64_2])
                dsimp only
                refine wp_load_of (FullArenaTactics.c0_load_full_flags
                  (s := s1) (by simp only [Arg.val_var]; rw [hfl1]; omega) hm1) ?_
                rw [wp_let_and32_2, wp_let_ne32_2]; dsimp only
                refine wp_jnz_of (fun hc_fl1 => ?_) (fun _ => ?_)
                · simp only [Arg.val_var, Arg.val_imm, bne_iff_ne, ne_eq] at hc_fl1
                  have hfl_c1 : s1.core.flags[cur.toNat]'(by omega) &&& 1#32 ≠ 0#32 := hc_fl1
                  repeat (first
                    | rw [wp_let_sext32_64_2] | rw [wp_let_shl64_2] | rw [wp_let_add64_2])
                  dsimp only
                  refine wp_load_of (FullArenaTactics.c0_load_full_vals
                    (s := s1) hcur2_lt hm1) ?_
                  repeat (first
                    | rw [wp_let_trunc32_8_2] | rw [wp_let_sext8_32_2] | rw [wp_let_eq32_2])
                  dsimp only
                  refine wp_jnz_of (fun hc_val1 => ?_) (fun _ => ?_)
                  · simp only [Arg.val_var] at hc_val1; c0_cond hc_val1
                    have hval_c1 : s1.core.vals[(cur <<< (1 : Nat)).toNat]'(by omega) =
                        0#8 := sext32_eq_zero hc_val1
                    have h2c : (cur <<< (1 : Nat)).toNat = 2 * cur.toNat := by
                      rw [BitVec.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega
                    let qss1 := (s1.scratch.q_stamp[cur.toNat]'(by rw [hqsl1]; omega)).setWidth
                      64
                    let s1' : FullState :=
                      { s1 with scratch :=
                        { s1.scratch with q_search_idx := cur, q_search_stamp := qss1 } }
                    rw [wp_let_add64_2]; dsimp only
                    refine wp_store_sep (FullArenaTactics.store_full_q_search_idx cur hm1) ?_
                    intro m1a hm1a
                    repeat (first | rw [wp_let_mul64_2] | rw [wp_let_add64_2])
                    dsimp only
                    refine wp_load_of (FullArenaTactics.c0_load_full_q_stamp
                      (s := _) (by simp only [Arg.val_var]; rw [hqsl1]; omega) hm1a) ?_
                    repeat (first | rw [wp_let_zext32_2] | rw [wp_let_add64_2])
                    dsimp only
                    refine wp_store_sep (FullArenaTactics.store_full_q_search_stamp _ hm1a) ?_
                    intro m1b hm1b
                    simp only [heq1] at hval_c1
                    exact hQ (cur, ()) s1' m1b hcore1
                      ⟨hs1.core_ok,
                        { hs1.scratch_ok with walk_vals_len := hs1.scratch_ok.walk_vals_len }⟩
                      ⟨⟨hll1, hel1⟩, Or.inr ⟨hcur_lt,
                        by rw [List.getElem?_eq_getElem (by omega : 2 * cur.toNat < _)]
                           simpa [h2c] using hval_c1⟩⟩ hm1b
                  · exact hJnxt s1 () m1 hm1 rfl hs1 ⟨hll1, hel1⟩
                · exact hJnxt s1 () m1 hm1 rfl hs1 ⟨hll1, hel1⟩
            · exact hJ2w s1 () m1 hm1 rfl hs1 ⟨hll1, hel1⟩
          · exact hJ2w s1 () m1 hm1 rfl hs1 ⟨hll1, hel1⟩

/-! ## 3. `full_bump_analyzed` -/

private def BumpAnaInv (c : FullCfg) (s s1 : FullState) (saved : Nat) : Prop :=
  s1.LengthsOk c ∧
  s1.core = { s.core with mrk := s1.core.mrk, min_clr_len := s1.core.min_clr_len } ∧
  s1.scratch = { s.scratch with work_stk1 := s1.scratch.work_stk1 } ∧
  saved ≤ s1.core.min_clr_len ∧ FullAnaMarksCov c s1 ∧
  (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 ≠ 0#8 →
    s1.core.mrk[v]?.getD 0#8 = s.core.mrk[v]?.getD 0#8) ∧
  (∀ k, saved ≤ k → k < s1.core.min_clr_len →
    (s1.scratch.work_stk1[k]?.getD 0#32).toNat < s.core.cur_vars ∧
    s.core.mrk[(s1.scratch.work_stk1[k]?.getD 0#32).toNat]?.getD 0#8 = 0#8)

private theorem bumpAnaInv_init {c : FullCfg} {s : FullState}
    (hlen : s.LengthsOk c) (hcov : FullAnaMarksCov c s) :
    BumpAnaInv c s s s.core.min_clr_len :=
  ⟨hlen, rfl, rfl, Nat.le_refl _, hcov, fun _ _ _ => rfl, fun _ hk1 hk2 => by omega⟩

private theorem bumpAnaInv_step {c : FullCfg} {s s1 : FullState} {saved ov : Nat}
    (hinv : BumpAnaInv c s s1 saved)
    (hov : ov < s.core.cur_vars)
    (hmrk0 : s1.core.mrk[ov]?.getD 0#8 = 0#8)
    (hmcl : s1.core.min_clr_len < s.core.cur_vars) :
    let ov32 := BitVec.ofNat 32 ov
    let s2 : FullState :=
      { core :=
          { s1.core with mrk := s1.core.mrk.set ov 1#8, min_clr_len := s1.core.min_clr_len + 1 }
        scratch :=
          { s1.scratch with work_stk1 := s1.scratch.work_stk1.set s1.core.min_clr_len ov32 } }
    BumpAnaInv c s s2 saved := by
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
      refine ⟨hov, ?_⟩
      exact Classical.byContradiction fun hnz => by
        have heq := hpres ov hov_max hnz
        rw [heq] at hmrk0; exact hnz hmrk0
    · dsimp only at hkm ⊢; rw [List.getElem?_set_ne (Ne.symm hkeq)]
      exact hnew k hks (by omega)

private theorem bumpAnaInv_rollback {c : FullCfg} {s s1 : FullState} {saved : Nat}
    (hinv : BumpAnaInv c s s1 saved) (hlt : saved < s1.core.min_clr_len) :
    let mcl' := s1.core.min_clr_len - 1
    let rv := (s1.scratch.work_stk1[mcl']?.getD 0#32).toNat
    rv < s.core.cur_vars ∧
    let s2 : FullState :=
      { core := { s1.core with mrk := s1.core.mrk.set rv 0#8, min_clr_len := mcl' }
        scratch := s1.scratch }
    BumpAnaInv c s s2 saved := by
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

private theorem setWidth32_eq_zero {x : BitVec 8} (h : BitVec.setWidth 32 x = 0#32) : x = 0#8 := by
  ext i hi
  have h1 := congrArg (·[i]) h
  simpa [BitVec.getElem_setWidth, hi, show i < 32 by omega] using h1

theorem full_bump_analyzed_wp (Γ : Env)
    (hBump : ∀ a m Q X, fullBumpVarSpec a m Q X → Γ "full_bump_var" [i64, i32] [] a m Q X)
    (hMtf : ∀ a m Q X, fullQueueMtfSpec a m Q X → Γ "full_queue_mtf" [i64, i32] [] a m Q X)
    (hDecay : ∀ a m Q X, fullBumpDecaySpec a m Q X → Γ "full_bump_decay" [i64] [] a m Q X) :
    ∀ a m Q X, fullBumpAnalyzedSpec a m Q X → Func.wp Γ full_bump_analyzed_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hcov0, hm, hQ⟩
  obtain hmcl_cv := hcov0.1
  c0_steps
  c0_to_group
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
      BumpAnaInv c s s1 saved ∧ (FullMem c s1 ⋆ R) m1)
    (fun (i, ()) _ => s.core.tmp_len - i.toNat) (fun Jloop hLoop => ?_)
    (fun Jloop (i, ()) m1 ⟨hle_tl, s1, hinv1, hm1⟩ hLoop => ?_)
  · c0_steps; exact hLoop _ _ ⟨by simp, s, bumpAnaInv_init hlen hcov0, hm⟩
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
      (fun _ m1 => ∃ s1 : FullState, BumpAnaInv c s s1 saved ∧ (FullMem c s1 ⋆ R) m1)
      (fun J1 _ m1 ⟨s1, hinv1, hm1⟩ => ?_)
      (fun J1 hJ1 => ?_)
    · clear hm hlen hmcl_cv hcov0
      rw [Blocks.get_here]; try dsimp only
      c0_to_group
      refine wp_join_group (ts := [])
        (fun _ m2 => ∃ s2 : FullState, BumpAnaInv c s s2 saved ∧ (FullMem c s2 ⋆ R) m2)
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
              c0_call hMtf
              refine ⟨c, s4, R, rfl, hs4, hm4, ?_⟩
              intro _ s5 m5 hcore5 hs5 hp5 hm5
              have heq5 := fullCoreState_agrees_with_scratch hcore5
              c0_steps
              exact hJw _ _ ⟨s5, hs5, by rw [heq5, heq4, hcore3],
                by rw [hp5.2.1, hp4.2.1, hws3], by rw [hp5.2.2.1, hp4.2.2.1, hws23],
                by rw [hp5.1.1, hp4.1.1, hll3], by rw [hp5.1.2, hp4.1.2, hel3], hm5⟩
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
            (fun _ m2 => ∃ s2 : FullState, BumpAnaInv c s s2 saved ∧ (FullMem c s2 ⋆ R) m2)
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
              obtain ⟨hrv_lt, hinv3⟩ := bumpAnaInv_rollback hinv2_pk hsav_lt
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
          (fun _ m2 => ∃ s2 : FullState, BumpAnaInv c s s2 saved ∧ (FullMem c s2 ⋆ R) m2)
          (fun Jstep _ m2 ⟨s2, hinv2, hm2⟩ => ?_) (fun Jstep hJstep => ?_)
        · c0_steps
          exact hLoop _ _ (by c0_bound) ⟨by c0_bound, s2, hinv2, hm2⟩
        · refine wp_join_group (ts := []) (fun _ m' => m' = m1)
            (fun Jelse () m' hm' => ?_) (fun Jelse hJelse => ?_)
          · subst m'; rw [Blocks.get_here]; dsimp only
            refine wp_join_group (ts := [])
              (fun _ m2 => ∃ s2 : FullState, BumpAnaInv c s s2 saved ∧ (FullMem c s2 ⋆ R) m2)
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
                  BumpAnaInv c s s2 saved ∧ (FullMem c s2 ⋆ R) m2)
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
                refine wp_jnz_of (fun hj_c => ?_)
                  (fun _ => hJ () m2 (by rw [Blocks.get_here]; exact hJs () m2 ⟨s2, hinv2_pk, hm2⟩))
                have hj_lt : j.toNat < sz.toNat := by
                  simp only [Arg.val_var] at hj_c
                  simpa [BitVec.ult, sz] using hj_c
                rw [wp_let_add64_2]; dsimp only
                refine wp_load_of (FullArenaTactics.load_full_min_clr_len hm2) ?_
                rw [wp_let_ule64_2]; dsimp only
                refine wp_jnz_of (fun _ => ?_)
                  (fun _ => hJ () m2 (by rw [Blocks.get_here]; exact hJs () m2 ⟨s2, hinv2_pk, hm2⟩))
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
                let ov32 :=
                  (s2.core.arena[(rsn.setWidth 64 + 3 + j.setWidth 64).toNat]'har_li) >>> (1 : Nat)
                have hj1 : (j + 1).toNat = j.toNat + 1 := by
                  have hsz_lt := sz.isLt; bv_omega
                refine wp_join_group (ts := [])
                  (fun _ m3 => ∃ s3 : FullState, BumpAnaInv c s s3 saved ∧ (FullMem c s3 ⋆ R) m3)
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
                  have heq0 : BitVec.setWidth 32 (s2.core.mrk[ov32.toNat]'(by rw [hmrl2]; omega)) =
                      0#32 := by
                    simp only [Arg.val_var, Arg.val_imm, beq_iff_eq, h1m] at hmrk_raw
                    simpa only [ov32, hov_zext, show BitVec.setWidth 32 (BitVec.setWidth 8
                      (0 : BitVec 32)) = 0#32 from rfl] using hmrk_raw
                  exact setWidth32_eq_zero heq0
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
                have hinv3 := bumpAnaInv_step hinv2_pk hov_lt hmrk0 hmcl_lt
                have hbv_ov : BitVec.ofNat 32 ov32.toNat = ov32 :=
                  BitVec.eq_of_toNat_eq
                    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ov32.isLt])
                let s3 : FullState :=
                  { core := { s2.core with
                      mrk := s2.core.mrk.set ov32.toNat 1#8
                      min_clr_len := s2.core.min_clr_len + 1 }
                    scratch := { s2.scratch with
                      work_stk1 := s2.scratch.work_stk1.set s2.core.min_clr_len ov32 } }
                have hinv3' : BumpAnaInv c s s3 saved := by simpa only [s3, hbv_ov] using hinv3
                exact hJnext () m3c ⟨s3, hinv3', hm3c⟩
            all_goals exact hJs _ _ ⟨s1, hinv1_pk, hm1⟩
          · rw [wp_let_ne32_2]; dsimp only
            refine wp_jnz_of (fun _ => ?_) (fun _ => hJelse () m1 rfl)
            rw [wp_let_and32_2, wp_let_ne32_2]; dsimp only
            refine wp_jnz_of (fun _ => ?_) (fun _ => hJelse () m1 rfl)
            rw [wp_let_and32_2, wp_let_lshr32_2]; dsimp only
            let ov32 := (rsn &&& 0x7FFFFFFF#32) >>> (1 : Nat)
            refine wp_join_group (ts := [])
              (fun _ m2 => ∃ s2 : FullState, BumpAnaInv c s s2 saved ∧ (FullMem c s2 ⋆ R) m2)
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
              exact setWidth32_eq_zero heq0
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
            have hinv2 := bumpAnaInv_step hinv1_pk hov_lt hmrk0 hmcl_lt
            have hbv_ov : BitVec.ofNat 32 ov32.toNat = ov32 :=
              BitVec.eq_of_toNat_eq
                (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ov32.isLt])
            let s2 : FullState :=
              { core := { s1.core with
                  mrk := s1.core.mrk.set ov32.toNat 1#8
                  min_clr_len := s1.core.min_clr_len + 1 }
                scratch := { s1.scratch with
                  work_stk1 := s1.scratch.work_stk1.set s1.core.min_clr_len ov32 } }
            have hinv2' : BumpAnaInv c s s2 saved := by simpa only [s2, hbv_ov] using hinv2
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
