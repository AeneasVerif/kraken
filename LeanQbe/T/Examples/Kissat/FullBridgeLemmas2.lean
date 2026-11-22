module

public import LeanQbe.T.Examples.Kissat.FullSpec
import LeanQbe.T.Examples.Kissat.FullBinLuckyLemmas
import LeanQbe.T.Examples.Kissat.FullAssignAddLemmas
import LeanQbe.T.Examples.Kissat.FullIngestLemmas
import LeanQbe.T.Examples.Kissat.FullParseInitLemmas
import LeanQbe.T.Examples.Kissat.FullLearnAnaLemmas
import LeanQbe.T.Examples.Kissat.FullSweepVarLemmas
import LeanQbe.T.Examples.Kissat.FullSccLemmas

/-!
# Kissat `D-Full` Canonical `FullSpec` Bridge Lemmas — Parts 6–12 (`Stage 4`)

Parametric `(Γ : Env)` table-entry bridge lemmas `full_<fn>_bridge_wp` adapting landed shards
6–12 to canonical `FullSpec2`/`FullSpec3` contracts (`32` functions):
- Part 6 (`FullBinLuckyLemmas`, `6` fns): `full_has_bin`, `full_add_bin`, `full_delete_bin_side`,
  `full_delete_binary`, `full_set_inactive`, `full_add_unit`.
- Part 7 (`FullAssignAddLemmas`, `4` fns): `full_assign_lvl`, `full_assign`, `full_watch_push`,
  `full_add_clause`.
- Part 8 (`FullIngestLemmas`, `4` fns): `full_arena_next`, `full_alloc_cl`, `full_wstack_defrag`,
  `full_backtrack`.
- Part 9 (`FullParseInitLemmas`, `10` fns): `full_fixed_bytes`, `full_calc_ext_cap`,
  `full_calc_scr_cap`, `full_calc_max_v`, `full_init_ptrs`, `full_init_hdr`, `full_init_arenas`,
  `full_zero_tables1`, `full_zero_tables2`, `full_init_state`.
- Part 10 (`FullLearnAnaLemmas`, `3` fns): `full_eager_subsume`, `full_learn_clause`,
  `full_analyze`.
- Part 11 (`FullSweepVarLemmas`, `3` fns): `full_sweep_seed_sim`, `full_sweep_var`,
  `full_sweep_sat`.
- Part 12 (`FullSccLemmas`, `2` fns): `full_tarjan_pop_scc`, `full_tarjan_scc`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat Kraken.Bedrock2.Test

/-! ## Part 6: `FullBinLuckyLemmas` (`6` fns) -/

section Part6

open scoped FullArenaTactics FullBinLuckyTactics

theorem full_has_bin_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullHasBinSpec a m Q X → Func.wp Γ full_has_bin_body a m Q X := by
  rintro ⟨h, a, b, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hm, hQ⟩
  refine full_has_bin_wp Γ _ m Q X ⟨c, F0, s, R, rfl, ⟨hlen, F_cur, hw⟩, hm, fun r hr => ?_⟩
  exact hQ r fun hrt => let ⟨ha, hb, hab, hneg, hent⟩ := hr hrt; ⟨ha, hb, hab, hneg, hent F_cur hw⟩

theorem full_add_bin_bridge_wp (Γ : Env)
    (hHas : ∀ a m Q X, fullHasBinSpec a m Q X →
      Γ "full_has_bin" [i64, i32, i32] [.bool] a m Q X)
    (hAlvl : ∀ a m Q X, fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X)
    (hPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullAddBinSpec a m Q X → Func.wp Γ full_add_bin_body a m Q X := by
  rintro ⟨h, a, b, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hcl0, hent, hm, hQ⟩
  have hcl := hlen.core_ok
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hcl.cur_vars_le; have hvl := hcl.vals_len
  have hret0 : Q (0#64, ()) m :=
    hQ 0#64 s.core.vals s.core.flags s.core.lvl s.core.rsns s.core.trl s.core.trail_pos
      s.core.trail_end s.core.unassigned s.core.unflushed s.core.wvec s.core.wstk s.core.wlen
      s.core.wusable s.core.num_binary s.core.oom s.core.inconsistent s.scratch.phases
      s.scratch.wsort m hlen hw (Or.inl rfl) (fun h2 => by cases h2) (fun h2 => by cases h2) hm
  fbl_group
  · exact hret0
  · exact hret0
  · exact hret0
  · exact hret0
  · exact hret0
  · have ha_lt : a.toNat < 2 * s.core.cur_vars := by c0_bound
    have hb_lt : b.toNat < 2 * s.core.cur_vars := by c0_bound
    have hent_ab := hent ha_lt hb_lt
    have hdom_a := hw.vals_domain a.toNat ha_lt
    have hdom_b := hw.vals_domain b.toNat hb_lt
    refine wp_join_group
      (fun () mJ => mJ = m ∧
        ¬ (s.core.vals[a.toNat]?.getD 0#8 = 0xFF#8 ∧
           s.core.vals[b.toNat]?.getD 0#8 = 0xFF#8) ∧
        s.core.vals[a.toNat]?.getD 0#8 ≠ 1#8 ∧
        s.core.vals[b.toNat]?.getD 0#8 ≠ 1#8)
      ?_ (fun J hJ => by
        have ha_pos : s.core.vals[a.toNat]?.getD 0#8 ≠ 1#8 := by
          have h0 : BitVec.slt 0#32
              (BitVec.signExtend 32 (s.core.vals[a.toNat]'(by omega))) = false := by assumption
          intro heq; rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at heq
          rw [heq] at h0; revert h0; decide
        have hb_pos : s.core.vals[b.toNat]?.getD 0#8 ≠ 1#8 := by
          have h0 : BitVec.slt 0#32
              (BitVec.signExtend 32 (s.core.vals[b.toNat]'(by omega))) = false := by assumption
          intro heq; rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at heq
          rw [heq] at h0; revert h0; decide
        fbl_group
        · have hva_neg : s.core.vals[a.toNat]?.getD 0#8 = 0xFF#8 := by
            have hlt : BitVec.slt (BitVec.signExtend 32
                (s.core.vals[a.toNat]'(by omega))) 0#32 = true := by assumption
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hdom_a ⊢
            rcases hdom_a with h | h | h <;> rw [h] at hlt
            · exact absurd hlt (by decide)
            · exact absurd hlt (by decide)
            · exact h
          have hvb_neg : s.core.vals[b.toNat]?.getD 0#8 = 0xFF#8 := by
            have hlt : BitVec.slt (BitVec.signExtend 32
                (s.core.vals[b.toNat]'(by omega))) 0#32 = true := by assumption
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hdom_b ⊢
            rcases hdom_b with h | h | h <;> rw [h] at hlt
            · exact absurd hlt (by decide)
            · exact absurd hlt (by decide)
            · exact h
          have hFcur_unsat : (cnfOfClauses F_cur).Unsat := by
            refine unsat_of_entails_nil (entails_of_mem_or_false hent_ab fun l hl => Or.inr ?_)
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
            rcases hl with rfl | rfl
            · obtain ⟨ia, hia, haeq⟩ := (hw.vals_false_iff _ ha_lt).mp hva_neg
              have hs := hw.level0_sound ia hia (by have := hw.lvl_le ia hia; omega)
              rwa [haeq] at hs
            · obtain ⟨ib, hib, hbeq⟩ := (hw.vals_false_iff _ hb_lt).mp hvb_neg
              have hs := hw.level0_sound ib hib (by have := hw.lvl_le ib hib; omega)
              rwa [hbeq] at hs
          have hF0_unsat : F0.Unsat := hw.ext_sound.2 hFcur_unsat
          have hlen_inc : ({ s with core := { s.core with inconsistent := 1#64 } } :
              FullState).LengthsOk c := ⟨{ hcl with }, hlen.scratch_ok⟩
          have hw' : FullWitnessInv c F0 F_cur { s.core with inconsistent := 1#64 } :=
            { hw with
              inconsistent_sound := fun _ => hFcur_unsat
              arena := { hw.arena with len_ok := hw.arena.len_ok }
              watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }
          exact hQ 20#64 s.core.vals s.core.flags s.core.lvl s.core.rsns s.core.trl
            s.core.trail_pos s.core.trail_end s.core.unassigned s.core.unflushed s.core.wvec
            s.core.wstk s.core.wlen s.core.wusable s.core.num_binary s.core.oom 1#64
            s.scratch.phases s.scratch.wsort _ hlen_inc hw'
            (Or.inr (Or.inr (Or.inr rfl))) (fun _ => ⟨hF0_unsat, by decide⟩)
            (fun h2 => by cases h2) (by assumption)
        · have hnb : s.core.vals[b.toNat]?.getD 0#8 ≠ 0xFF#8 := by
            have h0 : BitVec.slt (BitVec.signExtend 32
                (s.core.vals[b.toNat]'(by omega))) 0#32 = false := by assumption
            intro heq; rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at heq
            rw [heq] at h0; revert h0; decide
          exact hJ () _ ⟨rfl, fun ⟨_, hb⟩ => hnb hb, ha_pos, hb_pos⟩
        · have hna : s.core.vals[a.toNat]?.getD 0#8 ≠ 0xFF#8 := by
            have h0 : BitVec.slt (BitVec.signExtend 32
                (s.core.vals[a.toNat]'(by omega))) 0#32 = false := by assumption
            intro heq; rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at heq
            rw [heq] at h0; revert h0; decide
          exact hJ () _ ⟨rfl, fun ⟨ha, _⟩ => hna ha, ha_pos, hb_pos⟩)
    rintro _ _ mJ ⟨rfl, hnot_both, ha_pos, hb_pos⟩
    have hassign_lit : ∀ (lit : BitVec 32), lit.toNat < 2 * s.core.cur_vars →
        s.core.vals[lit.toNat]?.getD 0#8 = 0#8 →
        (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat]) →
        wp Γ Q X (Expr.call (as := [i64, i32, i32, i32]) (bs := []) "full_assign_lvl"
          (Arg.var c.hdr, Arg.var lit, Arg.imm (4294967295#32 : Val i32),
            Arg.imm (0#32 : Val i32), ())
          fun _ => Expr.ret (Arg.imm (1#64 : Val i64), ())) mJ := by
      intro lit hlit hun hunit
      c0_call hAlvl
      refine ⟨c, s, R, rfl, hlen, hm, ?_⟩
      have hte_lt : s.core.trail_end < c.max_vars := by
        have := hw.trail_end_lt_of_unassigned hlit hun; omega
      have hnot_cond : ¬ (s.core.cur_vars ≤ lit.toNat / 2 ∨
          c.max_vars ≤ s.core.trail_end ∨ s.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8) := by
        intro h; rcases h with h1 | h2 | h3
        · omega
        · omega
        · exact h3 hun
      rw [ite_eq_right hnot_cond]; dsimp only
      intro flags' unassigned' phases' m' hfll hphl hm'
      obtain ⟨hlen', hw'⟩ :=
        fbl_assignLevel0_preserves_fullWitness hlen hw hcl0 hfll hphl hlit hun hunit
      fbl_group
      exact hQ 1#64 _ flags' _ _ _ _ _ unassigned' _ s.core.wvec s.core.wstk s.core.wlen
        s.core.wusable s.core.num_binary s.core.oom s.core.inconsistent phases' s.scratch.wsort m'
        hlen' hw' (Or.inr (Or.inl rfl)) (fun h2 => by cases h2) (fun h2 => by cases h2) hm'
    fbl_group
    refine wp_join_group (fun _ mK => mK = mJ ∧
      (s.core.vals[a.toNat]?.getD 0#8 = 0xFF#8 ∨ a = b))
      ?_ (fun J hJ => by
        fbl_group
        · have hva_neg : s.core.vals[a.toNat]?.getD 0#8 = 0xFF#8 := by
            have hlt : BitVec.slt (BitVec.signExtend 32
                (s.core.vals[a.toNat]'(by omega))) 0#32 = true := by assumption
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hdom_a ⊢
            rcases hdom_a with h | h | h <;> rw [h] at hlt
            · exact absurd hlt (by decide)
            · exact absurd hlt (by decide)
            · exact h
          exact hJ () _ ⟨rfl, Or.inl hva_neg⟩
        · exact hJ () _ ⟨rfl, Or.inr (by assumption)⟩
        · have hna_neg : s.core.vals[a.toNat]?.getD 0#8 ≠ 0xFF#8 := by
            have h0 : BitVec.slt (BitVec.signExtend 32
                (s.core.vals[a.toNat]'(by omega))) 0#32 = false := by assumption
            intro heq; rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at heq
            rw [heq] at h0; revert h0; decide
          have hva0 : s.core.vals[a.toNat]?.getD 0#8 = 0#8 := by
            rcases hdom_a with h | h | h <;> first | exact h | contradiction
          have hvb_neg : s.core.vals[b.toNat]?.getD 0#8 = 0xFF#8 := by
            have hlt : BitVec.slt (BitVec.signExtend 32
                (s.core.vals[b.toNat]'(by omega))) 0#32 = true := by assumption
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hdom_b ⊢
            rcases hdom_b with h | h | h <;> rw [h] at hlt
            · exact absurd hlt (by decide)
            · exact absurd hlt (by decide)
            · exact h
          have hunit_a : (cnfOfClauses F_cur).EntailsClause (cnfClause [a.toNat]) := by
            refine entails_of_mem_or_false hent_ab fun l hl => ?_
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
            rcases hl with rfl | rfl
            · exact Or.inl (by simp)
            · obtain ⟨ib, hib, hbeq⟩ := (hw.vals_false_iff _ hb_lt).mp hvb_neg
              have hs := hw.level0_sound ib hib (by have := hw.lvl_le ib hib; omega)
              right; rwa [hbeq] at hs
          exact hassign_lit a ha_lt hva0 hunit_a
        · c0_call hHas
          refine ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hm, ?_⟩
          intro r _
          fbl_group
          · exact hret0
          · have hwpc := fbl_bv32_mask_bin b (by omega)
            have hwpc1 := fbl_bv32_mask_bin a (by omega)
            refine wp_join_group
              (fun _ mO => ∃ wvecO wstkO wlenO wuO wsortO,
                let sO : FullState :=
                  { s with
                    core := { s.core with wvec := wvecO, wstk := wstkO,
                                          wlen := wlenO, wusable := wuO }
                    scratch := { s.scratch with wsort := wsortO } }
                sO.LengthsOk c ∧ ModeWatchesInv F_cur sO.core ∧ (FullMem c sO ⋆ R) mO)
              ?_ (fun J hJ => by
                c0_call hPush
                refine ⟨c, s, R, rfl, hlen, hw.watches.layout, fun _ => hwpc.1,
                  fun h2 => absurd h2 (by decide), hm, ?_⟩
                dsimp only
                intro ok1 wvec1 wstk1 wlen1 wu1 wsort1 m1 hlen1 hlay1 hother1 hok1t hok1f hm1
                let s1 : FullState :=
                  { s with
                    core := { s.core with wvec := wvec1, wstk := wstk1,
                                          wlen := wlen1, wusable := wu1 }
                    scratch := { s.scratch with wsort := wsort1 } }
                fbl_group
                · obtain ⟨_, _, hsz1, hpref1, hw0_1, _⟩ := hok1t (by assumption)
                  have hok1 : ok1 = true := by assumption
                  have hw1_ok : ModeWatchesInv F_cur s1.core :=
                    fbl_watchPush_bin_preserves_modeWatches (ok := ok1) hw.watches hlay1 rfl rfl
                      (fun _ r => r) ⟨hwpc.2.1, hwpc.1, hwpc.2.2 ▸ hb_lt, hwpc.2.2 ▸ hent_ab⟩
                      hother1 (fun _ => ⟨ha_lt, hsz1, hpref1, hw0_1⟩)
                      (fun hf => by rw [hok1] at hf; cases hf)
                  c0_call hPush
                  refine ⟨c, s1, R, rfl, hlen1, hlay1, fun _ => hwpc1.1,
                    fun h2 => absurd h2 (by decide), hm1, ?_⟩
                  dsimp only
                  intro ok2 wvec2 wstk2 wlen2 wu2 wsort2 m2 hlen2 hlay2 hother2 hok2t hok2f hm2
                  let s2 : FullState :=
                    { s1 with
                      core := { s1.core with wvec := wvec2, wstk := wstk2, wlen := wlen2,
                                             wusable := wu2 }
                      scratch := { s.scratch with wsort := wsort2 } }
                  fbl_group
                  · obtain ⟨_, _, hsz2, hpref2, hw0_2, _⟩ := hok2t (by assumption)
                    have hok2 : ok2 = true := by assumption
                    have hw2_ok : ModeWatchesInv F_cur s2.core :=
                      fbl_watchPush_bin_preserves_modeWatches (ok := ok2) hw1_ok hlay2 rfl rfl
                        (fun _ r => r) ⟨hwpc1.2.1, hwpc1.1, hwpc1.2.2 ▸ ha_lt,
                          hwpc1.2.2 ▸ fbl_entailsClause_swap2 hent_ab⟩
                        hother2 (fun _ => ⟨hb_lt, hsz2, hpref2, hw0_2⟩)
                        (fun hf => by rw [hok2] at hf; cases hf)
                    have hlen2' : ({ s2 with core := { s2.core with
                        num_binary := s.core.num_binary + 1#64 } } : FullState).LengthsOk c :=
                      ⟨{ hlen2.core_ok with }, hlen2.scratch_ok⟩
                    have hw2' : FullWitnessInv c F0 F_cur
                        { s2.core with num_binary := s.core.num_binary + 1#64 } :=
                      { hw with
                        arena := { hw.arena with len_ok := hw.arena.len_ok }
                        watches := hw2_ok.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }
                    exact hQ 1#64 s.core.vals s.core.flags s.core.lvl s.core.rsns s.core.trl
                      s.core.trail_pos s.core.trail_end s.core.unassigned s.core.unflushed
                      wvec2 wstk2 wlen2 wu2 (s.core.num_binary + 1#64) s.core.oom
                      s.core.inconsistent s.scratch.phases wsort2 _ hlen2' hw2'
                      (Or.inr (Or.inl rfl)) (fun h2 => by cases h2) (fun h2 => by cases h2)
                      (by assumption)
                  · have hw2_fail : ModeWatchesInv F_cur s2.core := by
                      refine fbl_watchPush_fail_preserves_modeWatches hw1_ok hlay2 rfl rfl
                        (fun _ r => r) fun l hl => ?_
                      by_cases hle : l = b.toNat
                      · subst hle; exact (hok2f (by assumption)).1 hb_lt
                      · exact hother2 l hl hle
                    exact hJ () m2 ⟨wvec2, wstk2, wlen2, wu2, wsort2, hlen2, hw2_fail, hm2⟩
                · have hw1_fail : ModeWatchesInv F_cur s1.core := by
                    refine fbl_watchPush_fail_preserves_modeWatches hw.watches hlay1 rfl rfl
                      (fun _ r => r) fun l hl => ?_
                    by_cases hle : l = a.toNat
                    · subst hle; exact (hok1f (by assumption)).1 ha_lt
                    · exact hother1 l hl hle
                  exact hJ () m1 ⟨wvec1, wstk1, wlen1, wu1, wsort1, hlen1, hw1_fail, hm1⟩)
            rintro _ _ mO ⟨wvecO, wstkO, wlenO, wuO, wsortO, hlenO, hwO, hmO⟩
            have hlenO' : ({ s with
                core := { s.core with wvec := wvecO, wstk := wstkO, wlen := wlenO,
                                      wusable := wuO, oom := 1#64 }
                scratch := { s.scratch with wsort := wsortO } } :
                FullState).LengthsOk c := ⟨{ hlenO.core_ok with }, hlenO.scratch_ok⟩
            have hwO' : FullWitnessInv c F0 F_cur
                { s.core with wvec := wvecO, wstk := wstkO, wlen := wlenO,
                              wusable := wuO, oom := 1#64 } :=
              { hw with
                arena := { hw.arena with len_ok := hw.arena.len_ok }
                watches := hwO.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }
            fbl_group
            exact hQ 2#64 s.core.vals s.core.flags s.core.lvl s.core.rsns s.core.trl
              s.core.trail_pos s.core.trail_end s.core.unassigned s.core.unflushed wvecO wstkO
              wlenO wuO s.core.num_binary 1#64 s.core.inconsistent
              s.scratch.phases wsortO _ hlenO' hwO'
              (Or.inr (Or.inr (Or.inl rfl))) (fun h2 => by cases h2) (fun _ => by decide)
              (by assumption))
    rintro _ _ mK ⟨rfl, hcond⟩
    have hvb0 : s.core.vals[b.toNat]?.getD 0#8 = 0#8 := by
      have hnb : s.core.vals[b.toNat]?.getD 0#8 ≠ 0xFF#8 := by
        rcases hcond with hva_neg | rfl
        · exact fun hb => hnot_both ⟨hva_neg, hb⟩
        · exact fun hb => hnot_both ⟨hb, hb⟩
      rcases hdom_b with h | h | h <;> first | exact h | contradiction
    have hunit_b : (cnfOfClauses F_cur).EntailsClause (cnfClause [b.toNat]) := by
      rcases hcond with hva_neg | rfl
      · refine entails_of_mem_or_false hent_ab fun l hl => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl
        · obtain ⟨ia, hia, haeq⟩ := (hw.vals_false_iff _ ha_lt).mp hva_neg
          have hs := hw.level0_sound ia hia (by have := hw.lvl_le ia hia; omega)
          right; rwa [haeq] at hs
        · exact Or.inl (by simp)
      · refine entails_of_mem_or_false hent_ab fun l hl => Or.inl ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl ⊢
        rcases hl with rfl | rfl <;> rfl
    exact hassign_lit b hb_lt hvb0 hunit_b

theorem full_delete_bin_side_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullDeleteBinSideSpec a m Q X → Func.wp Γ full_delete_bin_side_body a m Q X :=
  full_delete_bin_side_wp Γ

theorem full_delete_binary_bridge_wp (Γ : Env)
    (hDbs : ∀ a m Q X, fullDeleteBinSideSpec a m Q X →
      Γ "full_delete_bin_side" [i64, i32, i32] [] a m Q X) :
    ∀ a m Q X, fullDeleteBinarySpec a m Q X → Func.wp Γ full_delete_binary_body a m Q X :=
  full_delete_binary_wp Γ hDbs

theorem full_set_inactive_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullSetInactiveSpec a m Q X → Func.wp Γ full_set_inactive_body a m Q X :=
  full_set_inactive_wp Γ

theorem full_add_unit_bridge_wp (Γ : Env)
    (hBt : ∀ a m Q X, fullBacktrackSpec a m Q X → Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hAlvl : ∀ a m Q X, fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X) :
    ∀ a m Q X, fullAddUnitSpec a m Q X → Func.wp Γ full_add_unit_body a m Q X := by
  rintro ⟨h, lit, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hent, hm, hQ⟩
  have hcl := hlen.core_ok
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  fbl_group
  refine wp_join_group
    (fun _ mJ => ∃ valsJ lvlJ rsnsJ trlJ tpJ teJ propJ unassJ taJ baJ ptJ pbJ hpJ psJ hlJ qsiJ qssJ,
      let sJ : FullState :=
        { s with
          core := { s.core with
            vals := valsJ, lvl := lvlJ, rsns := rsnsJ, trl := trlJ, trail_pos := tpJ,
            trail_end := teJ, propagated := propJ, cur_level := 0, unassigned := unassJ }
          scratch := { s.scratch with
            target_assigned := taJ, best_assigned := baJ, phases_target := ptJ,
            phases_best := pbJ, heap := hpJ, pos := psJ, heap_len := hlJ,
            q_search_idx := qsiJ, q_search_stamp := qssJ } }
      sJ.LengthsOk c ∧ FullWitnessInv c F0 F_cur sJ.core ∧ (FullMem c sJ ⋆ R) mJ)
    ?_ (fun J hJ => by
      fbl_group
      · have hcl_lt64 : s.core.cur_level < 2 ^ 64 := by
          have := hw.cur_level_le; have := hcl.trail_end_le; have := hcl.cur_vars_le; omega
        have hmx_pos : (0#64).toNat < s.core.cur_level → (0#64).toNat < c.max_vars := by
          intro _; have := hw.cur_level_le; have := hcl.trail_end_le; have := hcl.cur_vars_le; omega
        c0_call hBt
        refine ⟨c, s, R, rfl, hlen, hcl_lt64, hmx_pos, hw.trail_lits_lt, hm,
          fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m'
            hlen' _ _ hcl' _ ⟨ta', ba', pt', pb', hp', ps', hl', qsi', qss', hsc'⟩
            _ _ hw' _ hm' => ?_⟩
        have hcl'0 : cl' = 0 := by rw [hcl']; exact Nat.min_zero _
        subst hcl'0; subst hsc'
        fbl_group
        exact hJ () m' ⟨vals', lvl', rsns', trl', tp', te', prop', unass',
          ta', ba', pt', pb', hp', ps', hl', qsi', qss', hlen',
          hw' F0 F_cur hw (Nat.zero_le _), hm'⟩
      · have hcl0 : s.core.cur_level = 0 := by
          have := hw.cur_level_le; have := hcl.trail_end_le; have := hcl.cur_vars_le; c0_bound
        have hs_eq :
            ({ s with
              core := { s.core with
                vals := s.core.vals, lvl := s.core.lvl, rsns := s.core.rsns, trl := s.core.trl,
                trail_pos := s.core.trail_pos, trail_end := s.core.trail_end,
                propagated := s.core.propagated, cur_level := 0, unassigned := s.core.unassigned }
              scratch := { s.scratch with
                target_assigned := s.scratch.target_assigned,
                best_assigned := s.scratch.best_assigned,
                phases_target := s.scratch.phases_target, phases_best := s.scratch.phases_best,
                heap := s.scratch.heap, pos := s.scratch.pos, heap_len := s.scratch.heap_len,
                q_search_idx := s.scratch.q_search_idx,
                q_search_stamp := s.scratch.q_search_stamp } } : FullState) = s := by
          cases s with | mk sc ssc =>
          cases sc; cases ssc; dsimp only at hcl0; subst hcl0; rfl
        have hcore_eq :
            ({ s.core with
              vals := s.core.vals, lvl := s.core.lvl, rsns := s.core.rsns, trl := s.core.trl,
              trail_pos := s.core.trail_pos, trail_end := s.core.trail_end,
              propagated := s.core.propagated, cur_level := 0,
              unassigned := s.core.unassigned } : FullCoreState) = s.core :=
          congrArg FullState.core hs_eq
        exact hJ () m ⟨s.core.vals, s.core.lvl, s.core.rsns, s.core.trl, s.core.trail_pos,
          s.core.trail_end, s.core.propagated, s.core.unassigned, s.scratch.target_assigned,
          s.scratch.best_assigned, s.scratch.phases_target, s.scratch.phases_best, s.scratch.heap,
          s.scratch.pos, s.scratch.heap_len, s.scratch.q_search_idx, s.scratch.q_search_stamp,
          by simpa only [hs_eq] using hlen, by simpa only [hcore_eq] using hw,
          by simpa only [hs_eq] using hm⟩)
  rintro _ _ mJ ⟨valsJ, lvlJ, rsnsJ, trlJ, tpJ, teJ, propJ, unassJ,
    taJ, baJ, ptJ, pbJ, hpJ, psJ, hlJ, qsiJ, qssJ, hlenJ, hwJ, hmJ⟩
  let sJ : FullState :=
    { s with
      core := { s.core with
        vals := valsJ, lvl := lvlJ, rsns := rsnsJ, trl := trlJ, trail_pos := tpJ,
        trail_end := teJ, propagated := propJ, cur_level := 0, unassigned := unassJ }
      scratch := { s.scratch with
        target_assigned := taJ, best_assigned := baJ, phases_target := ptJ,
        phases_best := pbJ, heap := hpJ, pos := psJ, heap_len := hlJ,
        q_search_idx := qsiJ, q_search_stamp := qssJ } }
  change sJ.LengthsOk c at hlenJ
  change FullWitnessInv c F0 F_cur sJ.core at hwJ
  change (FullMem c sJ ⋆ R) mJ at hmJ
  have hclJ := hlenJ.core_ok; have hcvJ := hclJ.cur_vars_le; have hvlJ := hclJ.vals_len
  have hshr1 : (lit >>> (1 : Nat)).toNat = lit.toNat / 2 := by simp [Nat.shiftRight_eq_div_pow]
  fbl_group
  · have hge : 2 * s.core.cur_vars ≤ lit.toNat := by
      have h1 : sJ.core.cur_vars ≤ lit.toNat / 2 := by c0_bound
      change s.core.cur_vars ≤ lit.toNat / 2 at h1; omega
    exact hQ false valsJ s.core.flags lvlJ rsnsJ trlJ tpJ teJ propJ 0 unassJ s.core.unflushed
      s.core.inconsistent s.scratch.phases taJ baJ ptJ pbJ hpJ psJ hlJ qsiJ qssJ mJ
      hlenJ hwJ rfl (fun hlt _ => absurd hlt (by omega)) (fun _ => Or.inl hge) hmJ
  · exact hQ true valsJ s.core.flags lvlJ rsnsJ trlJ tpJ teJ propJ 0 unassJ s.core.unflushed
      s.core.inconsistent s.scratch.phases taJ baJ ptJ pbJ hpJ psJ hlJ qsiJ qssJ mJ
      hlenJ hwJ rfl (fun _ hf => by cases hf) (fun hf => by cases hf) hmJ
  · have hv_lt : lit.toNat / 2 < s.core.cur_vars := by
      change lit.toNat / 2 < sJ.core.cur_vars; c0_bound
    have hlit_lt : lit.toNat < 2 * sJ.core.cur_vars := by omega
    have hdom := hwJ.vals_domain lit.toNat hlit_lt
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hdom
    have hva_neg : sJ.core.vals[lit.toNat]?.getD 0#8 = 0xFF#8 := by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      exact (fbl_bv8_vals_pos hdom).2.mp (by assumption)
    have hFcur_unsat : (cnfOfClauses F_cur).Unsat := by
      refine unsat_of_entails_nil (entails_of_mem_or_false (hent (by omega)) fun l hl => Or.inr ?_)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl; subst hl
      obtain ⟨i, hi, heq⟩ := (hwJ.vals_false_iff _ hlit_lt).mp hva_neg
      have hs := hwJ.level0_sound i hi (by have := hwJ.lvl_le i hi; simp only [sJ] at *; omega)
      rwa [heq] at hs
    have hF0_unsat : F0.Unsat := hwJ.ext_sound.2 hFcur_unsat
    have hlen_inc : ({ sJ with core := { sJ.core with inconsistent := 1#64 } } :
        FullState).LengthsOk c := ⟨{ hclJ with }, hlenJ.scratch_ok⟩
    have hwJ' : FullWitnessInv c F0 F_cur { sJ.core with inconsistent := 1#64 } :=
      { hwJ with
        inconsistent_sound := fun _ => hFcur_unsat
        arena := { hwJ.arena with len_ok := hwJ.arena.len_ok }
        watches := hwJ.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }
    exact hQ false valsJ s.core.flags lvlJ rsnsJ trlJ tpJ teJ propJ 0 unassJ s.core.unflushed
      1#64 s.scratch.phases taJ baJ ptJ pbJ hpJ psJ hlJ qsiJ qssJ _
      hlen_inc hwJ' rfl (fun _ _ => ⟨hF0_unsat, by decide⟩)
      (fun _ => Or.inr ⟨hF0_unsat, by decide⟩) (by assumption)
  · have hv_lt : lit.toNat / 2 < s.core.cur_vars := by
      change lit.toNat / 2 < sJ.core.cur_vars; c0_bound
    have hlit_lt : lit.toNat < 2 * sJ.core.cur_vars := by omega
    have hdom := hwJ.vals_domain lit.toNat hlit_lt
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hdom
    have hval0 : sJ.core.vals[lit.toNat]?.getD 0#8 = 0#8 := by
      have hpos_f : BitVec.slt 0#32
          (BitVec.signExtend 32 (sJ.core.vals[lit.toNat]'(by omega))) = false := by assumption
      have hneg_f : BitVec.slt (BitVec.signExtend 32
          (sJ.core.vals[lit.toNat]'(by omega))) 0#32 = false := by assumption
      have hfb := fbl_bv8_vals_pos hdom
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      rcases hdom with h | h | h
      · exact h
      · exact absurd (hfb.1.mpr h) (by rw [hpos_f]; decide)
      · exact absurd (hfb.2.mpr h) (by rw [hneg_f]; decide)
    have hte_lt : sJ.core.trail_end < c.max_vars := by
      have := hwJ.trail_end_lt_of_unassigned hlit_lt hval0; omega
    c0_call hAlvl
    refine ⟨c, sJ, R, rfl, hlenJ, hmJ, ?_⟩
    have hnot_cond : ¬ (sJ.core.cur_vars ≤ lit.toNat / 2 ∨ c.max_vars ≤ sJ.core.trail_end ∨
        sJ.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8) := by
      intro h; rcases h with h1 | h2 | h3
      · change s.core.cur_vars ≤ lit.toNat / 2 at h1; omega
      · omega
      · exact h3 hval0
    rw [ite_eq_right hnot_cond]; dsimp only
    intro flags' unass' phases' m' hfll hphl hm'
    obtain ⟨hlen', hw'⟩ :=
      fbl_assignLevel0_preserves_fullWitness hlenJ hwJ rfl hfll hphl hlit_lt hval0 (hent (by omega))
    fbl_group
    exact hQ true ((valsJ.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8) flags'
      (lvlJ.set (lit.toNat / 2) 0#32) (rsnsJ.set (lit.toNat / 2) 0xFFFFFFFF#32)
      (trlJ.set teJ lit) (tpJ.set (lit.toNat / 2) (BitVec.ofNat 32 teJ)) (teJ + 1) propJ 0
      unass' (s.core.unflushed + 1#64) s.core.inconsistent phases' taJ baJ ptJ pbJ hpJ psJ hlJ
      qsiJ qssJ m' hlen' hw' rfl (fun _ hf => by cases hf) (fun hf => by cases hf) hm'

end Part6

/-! ## Part 7: `FullAssignAddLemmas` (`4` fns) -/

section Part7

theorem full_assign_lvl_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullAssignLvlSpec a m Q X → Func.wp Γ full_assign_lvl_body a m Q X :=
  full_assign_lvl_wp Γ

theorem full_assign_bridge_wp (Γ : Env)
    (hAssignLvl : ∀ a m Q X, fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X) :
    ∀ a m Q X, fullAssignSpec a m Q X → Func.wp Γ full_assign_body a m Q X :=
  full_assign_wp Γ hAssignLvl

theorem full_watch_push_bridge_wp (Γ : Env)
    (hDefrag : ∀ a m Q X, fullWstackDefragSpec a m Q X → Γ "full_wstack_defrag" [i64] [] a m Q X) :
    ∀ a m Q X, fullWatchPushSpec a m Q X → Func.wp Γ full_watch_push_body a m Q X :=
  full_watch_push_wp Γ hDefrag

theorem full_add_clause_bridge_wp (Γ : Env)
    (hAlloc : ∀ a m Q X, fullAllocClSpec a m Q X →
      Γ "full_alloc_cl" [i64, i32, i32, .bool] [i64] a m Q X)
    (hPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullAddClauseSpec a m Q X → Func.wp Γ full_add_clause_body a m Q X := by
  rintro ⟨h, len, glue, red, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm, hle, hlits, hm, hQ⟩
  refine full_add_clause_wp Γ hAlloc hPush _ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm, hle, hlits, hm, ?_⟩
  split
  · next h1 => simp only [h1, ↓reduceIte] at hQ; exact hQ
  · next h1 =>
    simp only [h1, ↓reduceIte] at hQ
    split
    · next h2 => simp only [h2, ↓reduceIte] at hQ; exact hQ
    · next h2 =>
      simp only [h2, ↓reduceIte] at hQ
      exact fun r arena' alen' wvec' wstk' wlen' wusable' fred' ni' nr' wsort' m'
        hr hlen' hw' hrefs hnd halloc hm' =>
        hQ r arena' alen' wvec' wstk' wlen' wusable' fred' ni' nr' wsort' m'
          hr hlen' hw' hrefs (fun h => hnd h) halloc hm'

end Part7

/-! ## Part 8: `FullIngestLemmas` (`4` fns) -/

section Part8

theorem full_arena_next_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullArenaNextSpec a m Q X → Func.wp Γ full_arena_next_body a m Q X :=
  full_arena_next_wp Γ

theorem full_alloc_cl_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullAllocClSpec a m Q X → Func.wp Γ full_alloc_cl_body a m Q X :=
  full_alloc_cl_wp Γ

theorem full_wstack_defrag_bridge_wp (Γ : Env)
    (hSift : ∀ a m Q X, fullWsortSiftSpec a m Q X →
      Γ "full_wsort_sift" [i64, i64, i64, i64] [] a m Q X) :
    ∀ a m Q X, fullWstackDefragSpec a m Q X → Func.wp Γ full_wstack_defrag_body a m Q X := by
  refine full_wstack_defrag_wp Γ ?_
  rintro ⟨wvp, wsp, start, n, ⟨⟩⟩ m Q X
    ⟨nlits, wvec, ws, R, hwv, _hst62, hn62, hstn, hnws, hlt, hhp, hm, hQ⟩
  exact hSift (wvp, wsp, start, n, ()) m Q X
    ⟨nlits, wvec, ws, R, hwv, hstn, hn62, hnws, hlt, hhp, hm, hQ⟩

private theorem canonOtfs_to_ingest {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (h : FullOtfsWitnessInv c F0 F_cur k) :
    FullIngestSpecs.FullOtfsWitnessInv c F0 F_cur k :=
  ⟨h.ext_sound, h.inconsistent_sound, h.arena, h.watches, h.cur_level_le, h.trail_lits_lt,
   h.trail_vars_nodup, h.vals_domain, h.vals_true_iff, h.vals_false_iff, h.lvl_le,
   h.dec_earliest, h.levels_inhabited, h.level0_sound, h.trail_pos_inv, h.level0_rsn_none,
   h.frame_trail_lt, h.frame_trail_mono, h.frame_trail_before_lt, h.frame_dec_lt,
   h.reason_inv_below, h.reason_lit_mem_below⟩

theorem full_backtrack_bridge_wp (Γ : Env)
    (hSave : ∀ a m Q X, fullSaveTargetBestSpec a m Q X →
      Γ "full_save_target_best" [i64] [] a m Q X)
    (hHeapPush : ∀ a m Q X, fullHeapPushSpec a m Q X →
      Γ "full_heap_push" [i64, i32] [] a m Q X) :
    ∀ a m Q X, fullBacktrackSpec a m Q X → Func.wp Γ full_backtrack_body a m Q X := by
  rintro ⟨h, tgt, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hcl64, htgt, htrl, hm, hQ⟩
  refine full_backtrack_wp Γ hSave
    (fun a' m' Q' X' ⟨c', s', R', hh', hl', hm', hQ'⟩ =>
      hHeapPush a' m' Q' X' ⟨c', s', R', hh', hl', hm', fun r' s'' m'' hc' hl'' hp' hm'' =>
        hQ' r' s'' m'' hc' hl''
          ⟨⟨hp'.1, hp'.2.1, hp'.2.2.1, hp'.2.2.2.1, hp'.2.2.2.2.1, hp'.2.2.2.2.2.1,
            hp'.2.2.2.2.2.2.1, hp'.2.2.2.2.2.2.2.1⟩, hp'.2.2.2.2.2.2.2.2⟩ hm''⟩)
    _ m Q X ⟨c, s, R, rfl, hlen, hcl64, htgt, htrl, hm, ?_⟩
  dsimp only
  intro vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m'
    hlen' hte hprop hcl hfr htrl' _ _ hclr hw_w hw_o hm'
  exact hQ vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m'
    hlen' hte hprop hcl hfr.1 hfr.2 htrl'
    (fun ⟨F0, Fc, hw⟩ => hclr ⟨F0, Fc, hw.elim Or.inl (Or.inr ∘ canonOtfs_to_ingest)⟩)
    hw_w (fun F0 Fc ho => hw_o F0 Fc (canonOtfs_to_ingest ho)) hm'

end Part8

/-! ## Part 9: `FullParseInitLemmas` (`10` fns) -/

section Part9

theorem full_fixed_bytes_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullFixedBytesSpec a m Q X → Func.wp Γ full_fixed_bytes_body a m Q X :=
  full_fixed_bytes_wp Γ

theorem full_calc_ext_cap_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullCalcExtCapSpec a m Q X → Func.wp Γ full_calc_ext_cap_body a m Q X :=
  full_calc_ext_cap_wp Γ

theorem full_calc_scr_cap_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullCalcScrCapSpec a m Q X → Func.wp Γ full_calc_scr_cap_body a m Q X :=
  full_calc_scr_cap_wp Γ

theorem full_calc_max_v_bridge_wp (Γ : Env)
    (hFixed : ∀ a m Q X, fullFixedBytesSpec a m Q X → Γ "full_fixed_bytes" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullCalcMaxVSpec a m Q X → Func.wp Γ full_calc_max_v_body a m Q X :=
  full_calc_max_v_wp Γ hFixed

theorem full_init_ptrs_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullInitPtrsSpec a m Q X → Func.wp Γ full_init_ptrs_body a m Q X :=
  full_init_ptrs_wp Γ

theorem full_init_hdr_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullInitHdrSpec a m Q X → Func.wp Γ full_init_hdr_body a m Q X :=
  full_init_hdr_wp Γ

theorem full_init_arenas_bridge_wp (Γ : Env)
    (hPtrs : ∀ a m Q X, fullInitPtrsSpec a m Q X →
      Γ "full_init_ptrs" [i64, i64, i64] [] a m Q X) :
    ∀ a m Q X, fullInitArenasSpec a m Q X → Func.wp Γ full_init_arenas_body a m Q X :=
  full_init_arenas_wp Γ hPtrs

theorem full_zero_tables1_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullZeroTables1Spec a m Q X → Func.wp Γ full_zero_tables1_body a m Q X :=
  full_zero_tables1_wp Γ

theorem full_zero_tables2_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullZeroTables2Spec a m Q X → Func.wp Γ full_zero_tables2_body a m Q X :=
  full_zero_tables2_wp Γ

theorem full_init_state_bridge_wp (Γ : Env)
    (hHdr : ∀ a m Q X, kissatParseHeaderSpec a m Q X →
      Γ "kissat_parse_header" [i64, i64, i64] [.bool] a m Q X)
    (hFixed : ∀ a m Q X, fullFixedBytesSpec a m Q X → Γ "full_fixed_bytes" [i64] [i64] a m Q X)
    (hMaxV : ∀ a m Q X, fullCalcMaxVSpec a m Q X →
      Γ "full_calc_max_v" [i64, i64, i64, i64] [i64] a m Q X)
    (hExt : ∀ a m Q X, fullCalcExtCapSpec a m Q X → Γ "full_calc_ext_cap" [i64] [i64] a m Q X)
    (hScr : ∀ a m Q X, fullCalcScrCapSpec a m Q X → Γ "full_calc_scr_cap" [i64] [i64] a m Q X)
    (hArenas : ∀ a m Q X, fullInitArenasSpec a m Q X →
      Γ "full_init_arenas" [i64, i64, i64, i64] [] a m Q X)
    (hInitHdr : ∀ a m Q X, fullInitHdrSpec a m Q X →
      Γ "full_init_hdr" [i64, i64, i64, i64] [] a m Q X)
    (hZt1 : ∀ a m Q X, fullZeroTables1Spec a m Q X → Γ "full_zero_tables1" [i64] [] a m Q X)
    (hZt2 : ∀ a m Q X, fullZeroTables2Spec a m Q X → Γ "full_zero_tables2" [i64] [] a m Q X) :
    ∀ a m Q X, fullInitStateSpec a m Q X → Func.wp Γ full_init_state_body a m Q X :=
  full_init_state_wp Γ hHdr hFixed hMaxV hExt hScr hArenas hInitHdr hZt1 hZt2

end Part9

/-! ## Part 10: `FullLearnAnaLemmas` (`3` fns) -/

section Part10

private theorem laOtfs_to_canon {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (h : FullLearnAnaSpecs.FullOtfsWitnessInv c F0 F_cur k) :
    FullOtfsWitnessInv c F0 F_cur k :=
  ⟨h.ext_sound, h.inconsistent_sound, h.arena, h.watches, h.cur_level_le, h.trail_lits_lt,
    h.trail_vars_nodup, h.vals_domain, h.vals_true_iff, h.vals_false_iff, h.lvl_le, h.dec_earliest,
    h.levels_inhabited, h.level0_sound, h.trail_pos_inv, h.level0_rsn_none, h.frame_trail_lt,
    h.frame_trail_mono, h.frame_trail_before_lt, h.frame_dec_lt, h.reason_inv_below,
    h.reason_lit_mem_below⟩

private theorem canon_to_laOtfs {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (h : FullOtfsWitnessInv c F0 F_cur k) :
    FullLearnAnaSpecs.FullOtfsWitnessInv c F0 F_cur k :=
  ⟨h.ext_sound, h.inconsistent_sound, h.arena, h.watches, h.cur_level_le, h.trail_lits_lt,
    h.trail_vars_nodup, h.vals_domain, h.vals_true_iff, h.vals_false_iff, h.lvl_le, h.dec_earliest,
    h.levels_inhabited, h.level0_sound, h.trail_pos_inv, h.level0_rsn_none, h.frame_trail_lt,
    h.frame_trail_mono, h.frame_trail_before_lt, h.frame_dec_lt, h.reason_inv_below,
    h.reason_lit_mem_below⟩

private theorem laCut_to_canon {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (h : FullLearnAnaSpecs.FullWitnessCutInv c F0 F_cur cut k) :
    FullWitnessCutInv c F0 F_cur cut k :=
  ⟨laOtfs_to_canon h.toFullOtfsWitnessInv, h.cut_le, h.reason_inv_cut, h.reason_lit_mem_cut⟩

private theorem canon_to_laCut {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {k : FullCoreState} (h : FullWitnessCutInv c F0 F_cur cut k) :
    FullLearnAnaSpecs.FullWitnessCutInv c F0 F_cur cut k :=
  ⟨canon_to_laOtfs h.toFullOtfsWitnessInv, h.cut_le, h.reason_inv_cut, h.reason_lit_mem_cut⟩

private theorem laOtfsInv_to_canon {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullLearnAnaSpecs.FullOtfsInvW c F0 F_cur s) :
    FullOtfsInvW c F0 F_cur s :=
  ⟨h.1, laOtfs_to_canon h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

private theorem canon_to_laOtfsInv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullOtfsInvW c F0 F_cur s) :
    FullLearnAnaSpecs.FullOtfsInvW c F0 F_cur s :=
  ⟨h.1, canon_to_laOtfs h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

private theorem laCutInv_to_canon {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {s : FullState} (h : FullLearnAnaSpecs.FullCutInvW c F0 F_cur cut s) :
    FullCutInvW c F0 F_cur cut s :=
  ⟨h.1, laCut_to_canon h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

private theorem canon_to_laCutInv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {s : FullState} (h : FullCutInvW c F0 F_cur cut s) :
    FullLearnAnaSpecs.FullCutInvW c F0 F_cur cut s :=
  ⟨h.1, canon_to_laCut h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem full_eager_subsume_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullEagerSubsumeSpec a m Q X → Func.wp Γ full_eager_subsume_body a m Q X :=
  full_eager_subsume_wp Γ

theorem full_learn_clause_bridge_wp (Γ : Env)
    (hBt : ∀ a m Q X, fullBacktrackSpec a m Q X → Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hAsgn : ∀ a m Q X, fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X)
    (hDnl : ∀ a m Q X, fullDetNewLevelSpec a m Q X →
      Γ "full_det_new_level" [i64, i64] [i64] a m Q X)
    (hDefrag : ∀ a m Q X, fullWstackDefragSpec a m Q X → Γ "full_wstack_defrag" [i64] [] a m Q X)
    (hRed : ∀ a m Q X, fullReduceSpec a m Q X → Γ "full_reduce" [i64, .bool] [i64] a m Q X)
    (hAddCl : ∀ a m Q X, fullAddClauseSpec a m Q X →
      Γ "full_add_clause" [i64, i32, i32, .bool] [i64] a m Q X)
    (hEsub : ∀ a m Q X, fullEagerSubsumeSpec a m Q X →
      Γ "full_eager_subsume" [i64, i64] [] a m Q X) :
    ∀ a m Q X, fullLearnClauseSpec a m Q X → Func.wp Γ full_learn_clause_body a m Q X := by
  rintro ⟨h, gl, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, ho, hcl, ht1, htcv, hnd, htv, htl, hent, hm, hQ⟩
  refine full_learn_clause_wp Γ ?_ hAsgn hDnl hDefrag hRed hAddCl hEsub _ m Q X
    ⟨c, F0, F_cur, s, R, rfl, canon_to_laOtfsInv ho, hcl, ht1, htcv, hnd, htv, htl, hent, hm, hQ⟩
  rintro ⟨h', tgt, ⟨⟩⟩ m' Q' X' ⟨c', s', R', rfl, hl', hcl64, htgt, htrl, hm', hQ'⟩
  refine hBt _ m' Q' X' ⟨c', s', R', rfl, hl', hcl64, htgt, htrl, hm',
    fun vals' lvl' rsns' trl' tp' te' prop' cl' un' sc' m'' hl'' hte hpr hcl' hps hsc htr' hvl
      hw_w hw_o hm'' =>
      hQ' vals' lvl' rsns' trl' tp' te' prop' cl' un' sc' m'' hl'' hte hpr hcl' hps hsc htr'
        (fun ⟨F0', Fc', hw⟩ => hvl ⟨F0', Fc', hw.elim Or.inl fun ho => Or.inr (laOtfs_to_canon ho)⟩)
        hw_w (fun F0' Fc' ho hlt => hw_o F0' Fc' (laOtfs_to_canon ho) hlt) hm''⟩

theorem full_analyze_bridge_wp (Γ : Env)
    (hOneLit : ∀ a m Q X, fullOneLitConflSpec a m Q X →
      Γ "full_one_lit_confl" [i64] [i64] a m Q X)
    (hDeduce : ∀ a m Q X, fullDeduce1uipSpec a m Q X →
      Γ "full_deduce_1uip" [i64] [i64] a m Q X)
    (hMinShrink : ∀ a m Q X, fullMinShrinkSpec a m Q X →
      Γ "full_min_shrink" [i64] [] a m Q X)
    (hTickRel : ∀ a m Q X, fullTickRelSpec a m Q X → Γ "full_tick_rel" [i64] [] a m Q X)
    (hEma : ∀ a m Q X, fullEmaUpdateSpec a m Q X → Γ "full_ema_update" [i64, i64] [] a m Q X)
    (hLearnCl : ∀ a m Q X, fullLearnClauseSpec a m Q X →
      Γ "full_learn_clause" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, fullAnalyzeSpec a m Q X → Func.wp Γ full_analyze_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hsp, hcf, hm, hQ⟩
  refine full_analyze_wp Γ ?_ ?_ ?_ hTickRel hEma ?_ _ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hsp, hcf, hm, ?_⟩
  · rintro ⟨h', ⟨⟩⟩ m' Q' X' ⟨c', F0', Fc', cut, s', R', rfl, hcut, hcf', hm', hQ'⟩
    refine hOneLit _ m' Q' X' ⟨c', F0', Fc', cut, s', R', rfl, laCutInv_to_canon hcut, hcf', hm',
      fun r s'' m'' hl'' hr hcv hfu hws h20 h1 h2 h0 hm'' =>
        hQ' r s'' m'' hl'' hr hcv hfu hws
          (fun h => let ⟨hu, ho, hcl, hdm⟩ := h20 h; ⟨hu, canon_to_laOtfsInv ho, hcl, hdm⟩)
          h1 (fun h => canon_to_laOtfsInv (h2 h))
          (fun h => let ⟨cut', hle, hc', hpos, hcl, hcf''⟩ := h0 h
            ⟨cut', hle, canon_to_laCutInv hc', hpos, hcl, hcf''⟩) hm''⟩
  · rintro ⟨h', ⟨⟩⟩ m' Q' X' ⟨c', F0', Fc', cut, s', R', rfl, hcut, hpos, hcf', hm', hQ'⟩
    refine hDeduce _ m' Q' X' ⟨c', F0', Fc', cut, s', R', rfl, laCutInv_to_canon hcut, hpos, hcf',
      hm', fun r s'' m'' hl'' hr hcv hfu hws h20 h0 h1 h2 hm'' =>
        hQ' r s'' m'' hl'' hr hcv hfu hws
          (fun h => let ⟨hu, ho, hcl, hdm⟩ := h20 h; ⟨hu, canon_to_laOtfsInv ho, hcl, hdm⟩)
          (fun h => canon_to_laOtfsInv (h0 h))
          (fun h => let ⟨ho, rest⟩ := h1 h; ⟨canon_to_laOtfsInv ho, rest⟩)
          (fun h => let ⟨cut', hle, hc', hcl, hcf''⟩ := h2 h
            ⟨cut', hle, canon_to_laCutInv hc', hcl, hcf''⟩) hm''⟩
  · rintro ⟨h', ⟨⟩⟩ m' Q' X'
      ⟨c', F0', Fc', s', R', rfl, hl', ho', hlm, ht1, htcv, hnd, hent, htv, htl, ht0, hm', hQ'⟩
    refine hMinShrink _ m' Q' X' ⟨c', F0', Fc', s', R', rfl, hl', laOtfs_to_canon ho', hlm,
      ht1, htcv, hnd, hent, htv, htl, ht0, hm',
      fun tmp' tl' mrk' mstk' mclr' mcl' mcf' conf' ll' mr' sstk' m''
        hl'' ho'' hlm' h1 hle h0 hnd' hlv hent' hm'' =>
        hQ' tmp' tl' mrk' mstk' mclr' mcl' mcf' conf' ll' mr' sstk' m''
          hl'' (canon_to_laOtfs ho'') hlm' h1 hle h0 hnd' hlv hent' hm''⟩
  · rintro ⟨h', gl, ⟨⟩⟩ m' Q' X'
      ⟨c', F0', Fc', s', R', rfl, ho', hpos, ht1, htcv, hnd, htv, htl, hent, hm', hQ'⟩
    exact hLearnCl _ m' Q' X' ⟨c', F0', Fc', s', R', rfl, laOtfsInv_to_canon ho', hpos,
      ht1, htcv, hnd, htv, htl, hent, hm', hQ'⟩
  · intro r s' m' hlen' hr hcv hfu hws h20 h0 h1 hm'
    exact hQ r s' m' hlen' hr hcv hfu
      ⟨hws, fun h => let ⟨_, ho, hcl, hdm⟩ := h20 h; ⟨laOtfsInv_to_canon ho, hcl, hdm⟩⟩
      (fun h => (h20 h).1) (fun h => laOtfsInv_to_canon (h0 h)) h1 hm'

end Part10

/-! ## Part 11: `FullSweepVarLemmas` (`3` fns) -/

section Part11

private theorem swOtfs_to_canon {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (h : FullSweepVarSpecs.FullOtfsWitnessInv c F0 F_cur k) :
    FullOtfsWitnessInv c F0 F_cur k :=
  ⟨h.ext_sound, h.inconsistent_sound, h.arena, h.watches, h.cur_level_le, h.trail_lits_lt,
    h.trail_vars_nodup, h.vals_domain, h.vals_true_iff, h.vals_false_iff, h.lvl_le, h.dec_earliest,
    h.levels_inhabited, h.level0_sound, h.trail_pos_inv, h.level0_rsn_none, h.frame_trail_lt,
    h.frame_trail_mono, h.frame_trail_before_lt, h.frame_dec_lt, h.reason_inv_below,
    h.reason_lit_mem_below⟩

theorem full_sweep_seed_sim_bridge_wp (Γ : Env)
    (hDpll : ∀ a m Q X, fullSweepDpllSpec a m Q X →
      Γ "full_sweep_dpll" [i64, i32, i32, i32, i32] [i64] a m Q X)
    (hRef : ∀ a m Q X, fullSweepRefineSpec a m Q X →
      Γ "full_sweep_refine" [i64, i32, i32] [] a m Q X) :
    ∀ a m Q X, fullSweepSeedSimSpec a m Q X → Func.wp Γ full_sweep_seed_sim_body a m Q X :=
  full_sweep_seed_sim_wp Γ hDpll hRef

theorem full_sweep_var_bridge_wp (Γ : Env)
    (hCone : ∀ a m Q X, fullSweepConeSpec a m Q X →
      Γ "full_sweep_cone" [i64, i32] [i64] a m Q X)
    (hSeed : ∀ a m Q X, fullSweepSeedSimSpec a m Q X →
      Γ "full_sweep_seed_sim" [i64, i32, i32] [i32] a m Q X)
    (hDpll : ∀ a m Q X, fullSweepDpllSpec a m Q X →
      Γ "full_sweep_dpll" [i64, i32, i32, i32, i32] [i64] a m Q X)
    (hRef : ∀ a m Q X, fullSweepRefineSpec a m Q X →
      Γ "full_sweep_refine" [i64, i32, i32] [] a m Q X)
    (hAddU : ∀ a m Q X, fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X)
    (hAddB : ∀ a m Q X, fullAddBinSpec a m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] a m Q X) :
    ∀ a m Q X, fullSweepVarSpec a m Q X → Func.wp Γ full_sweep_var_body a m Q X := by
  refine full_sweep_var_wp Γ hCone hSeed hDpll hRef ?_ hAddB
  rintro ⟨h, lit, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hent, hm, hQ⟩
  refine hAddU _ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hent, hm,
    fun ok vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl' inc'
      ph' ta' ba' pt' pb' hp' ps' hl' qsi' qss' m' hlen' hw' hcl0 hlt hfa hm' =>
      hQ ok vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl' inc'
        { s.scratch with
          phases := ph', target_assigned := ta', best_assigned := ba',
          phases_target := pt', phases_best := pb', heap := hp', pos := ps',
          heap_len := hl', q_search_idx := qsi', q_search_stamp := qss' }
        m' hlen' hw' ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hcl0 hlt hfa hm'⟩

theorem full_sweep_sat_bridge_wp (Γ : Env)
    (hBt : ∀ a m Q X, fullBacktrackSpec a m Q X → Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hEnter : ∀ a m Q X, fullEnterDenseSpec a m Q X →
      Γ "full_enter_dense" [i64] [.bool] a m Q X)
    (hSvar : ∀ a m Q X, fullSweepVarSpec a m Q X →
      Γ "full_sweep_var" [i64, i32] [i64] a m Q X)
    (hReb : ∀ a m Q X, fullRebuildWatchesSpec a m Q X →
      Γ "full_rebuild_watches" [i64] [i64] a m Q X)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullSweepSatSpec a m Q X → Func.wp Γ full_sweep_sat_body a m Q X := by
  refine full_sweep_sat_wp Γ ?_ hEnter hSvar hReb ?_
  · rintro ⟨h, tgt, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hcl64, htgt, htrl, hm, hQ⟩
    refine hBt _ m Q X ⟨c, s, R, rfl, hlen, hcl64, htgt, htrl, hm,
      fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m'
        hlen' hte hpr hcl' hps _ htrl' _ hw_w hw_o hm' =>
        hQ vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m'
          hlen' hte hpr hcl' hps htrl' hw_w
          (fun F0 Fc ho hlt => hw_o F0 Fc (swOtfs_to_canon ho) hlt) hm'⟩
  · rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hnd, hdm, hm, hQ⟩
    refine hProp _ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm, hm, ?_⟩
    dsimp only
    intro r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
      fuel' ct' cr' c0' c1' oom' ticks' wsort' phases' m'
      hlen' hw' htr hperm hfu hr hr0 hr1 hr2 hnp hm'
    have hnd' : FullArenaVarsNodup { s with
        core := { s.core with
          vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
          trail_pos := tp', trail_end := te', propagated := prop', unassigned := unass',
          unflushed := unfl', wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
          wusable := wu', fuel := fuel', confl_type := ct', confl_ref := cr', confl_lit0 := c0',
          confl_lit1 := c1', oom := oom' }
        scratch := { s.scratch with
          search_ticks := ticks', wsort := wsort', phases := phases' } } := by
      intro ref href hng
      have href0 : ref ∈ fullArenaClauseRefsCore s.core := hperm.2.1 ▸ href
      obtain ⟨_, hgb, hp⟩ := hperm.2.2 ref href0
      exact (hp.map (· / 2)).nodup_iff.mpr (hnd ref href0 (hgb.symm.trans hng))
    exact hQ r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
      fuel' ct' cr' c0' c1' oom'
      { s.scratch with search_ticks := ticks', wsort := wsort', phases := phases' } m'
      hlen' hw' hnd' ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      htr.1 hfu (fun ref href => by
        change ref ∈ fullArenaClauseRefsCore _; rw [hperm.2.1]; exact href)
      htr.2.1 hr hr0
      (fun h1 => let ⟨hf, ho, hc⟩ := hr1 h1
        ⟨hf, ho, hc.elim Or.inl fun ⟨ht2, hrest⟩ => Or.inr ⟨by rw [ht2]; decide, hrest⟩⟩)
      hr2 hnp hm'

end Part11

/-! ## Part 12: `FullSccLemmas` (`2` fns) -/

section Part12

theorem full_tarjan_pop_scc_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullTarjanPopSccSpec a m Q X → Func.wp Γ full_tarjan_pop_scc_body a m Q X :=
  full_tarjan_pop_scc_wp Γ

theorem full_tarjan_scc_bridge_wp (Γ : Env)
    (hPop : ∀ a m Q X, fullTarjanPopSccSpec a m Q X →
      Γ "full_tarjan_pop_scc" [i64, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullTarjanSccSpec a m Q X → Func.wp Γ full_tarjan_scc_body a m Q X :=
  full_tarjan_scc_wp Γ hPop

end Part12

end LeanQbe.T.Examples.Kissat.Full
