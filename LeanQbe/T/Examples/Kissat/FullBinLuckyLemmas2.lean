module

public import LeanQbe.T.Examples.Kissat.FullBinLuckyLemmas1
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` Binary Watch / Unit Helpers (`Stage 4`, Part 2)

Parametric `(Γ : Env)` `Func.wp` proofs for:
- `full_add_bin`
- `full_delete_bin_side`
- `full_delete_binary`
- `full_set_inactive`
- `full_add_unit`
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test
open FullBinLuckySpecs
open scoped FullArenaTactics FullBinLuckyTactics

theorem full_add_bin_wp (Γ : Env) (hhas : EnvSpec Γ "full_has_bin" fullHasBinSpec)
    (halvl : EnvSpec Γ "full_assign_lvl" fullAssignLvlSpec)
    (hwpush : EnvSpec Γ "full_watch_push" fullWatchPushSpec) :
    ∀ args m Q X, fullAddBinSpec args m Q X → Func.wp Γ full_add_bin_body args m Q X := by
  rintro ⟨h, a, b, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hcl0, hent, hm, hQ⟩
  have hcl := hlen.core_ok
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hcl.cur_vars_le; have hvl := hcl.vals_len
  have hret0 : Q (0#64, ()) m :=
    hQ 0#64 s.core.vals s.core.flags s.core.lvl s.core.rsns s.core.trl s.core.trail_pos
      s.core.trail_end s.core.unflushed s.core.wvec s.core.wstk s.core.wlen s.core.wusable
      s.core.num_binary s.core.oom s.core.inconsistent s.core.unassigned s.scratch.phases
      s.scratch.wsort m hlen hw (Or.inl rfl) (fun _ => rfl) (fun h2 => by cases h2)
      (fun h2 => by cases h2) hm
  fbl_group
  · exact hret0
  · exact hret0
  · exact hret0
  · exact hret0
  · exact hret0
  · have ha_lt : a.toNat < 2 * s.core.cur_vars := by c0_bound
    have hb_lt : b.toNat < 2 * s.core.cur_vars := by c0_bound
    have hne_neg : a ≠ b ^^^ 1#32 := by c0_bound
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
            s.core.trail_pos s.core.trail_end s.core.unflushed s.core.wvec s.core.wstk
            s.core.wlen s.core.wusable s.core.num_binary s.core.oom 1#64 s.core.unassigned
            s.scratch.phases s.scratch.wsort _ hlen_inc hw'
            (Or.inr (Or.inr (Or.inr rfl))) (fun h0 => by cases h0) (fun h2 => by cases h2)
            (fun _ => ⟨hF0_unsat, rfl⟩) (by assumption)
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
      c0_call halvl
      refine ⟨c, s, R, rfl, hlen, hm, ?_⟩
      have hte_lt : s.core.trail_end < c.max_vars := by
        have := hw.trail_end_lt_of_unassigned hlit hun; omega
      have hnot_cond : ¬ (s.core.cur_vars ≤ lit.toNat / 2 ∨
          c.max_vars ≤ s.core.trail_end ∨ s.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8) := by
        intro h; rcases h with h1 | h2 | h3
        · omega
        · omega
        · exact h3 hun
      rw [ite_eq_right hnot_cond]
      dsimp only
      intro flags' unassigned' phases' m' hfll hphl hm'
      obtain ⟨hlen', hw'⟩ :=
        fbl_assignLevel0_preserves_fullWitness hlen hw hcl0 hfll hphl hlit hun hunit
      fbl_group
      refine hQ 1#64 _ flags' _ _ _ _ _ _ s.core.wvec s.core.wstk s.core.wlen s.core.wusable
        s.core.num_binary s.core.oom s.core.inconsistent unassigned' phases' s.scratch.wsort m'
        hlen' hw' (Or.inr (Or.inl rfl)) (fun h0 => by cases h0) (fun h2 => by cases h2)
        (fun h2 => by cases h2) hm'
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
        · have hna_neg : s.core.vals[a.toNat]?.getD 0#8 ≠ 0xFF#8 := by
            have h0 : BitVec.slt (BitVec.signExtend 32
                (s.core.vals[a.toNat]'(by omega))) 0#32 = false := by assumption
            intro heq; rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at heq
            rw [heq] at h0; revert h0; decide
          have hva0 : s.core.vals[a.toNat]?.getD 0#8 = 0#8 := by
            rcases hdom_a with h | h | h <;> first | exact h | contradiction
          c0_call hhas
          refine ⟨c, F0, s, R, rfl, ⟨hlen, ⟨F_cur, hw⟩⟩, hm, ?_⟩
          intro r hr
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
                c0_call hwpush
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
                  c0_call hwpush
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
                      s.core.trail_pos s.core.trail_end s.core.unflushed wvec2 wstk2 wlen2 wu2
                      (s.core.num_binary + 1#64) s.core.oom s.core.inconsistent s.core.unassigned
                      s.scratch.phases wsort2 _ hlen2' hw2' (Or.inr (Or.inl rfl))
                      (fun h0 => by cases h0) (fun h2 => by cases h2) (fun h2 => by cases h2)
                      (by assumption)
                  · have hw2_fail : ModeWatchesInv F_cur s2.core := by
                      refine fbl_watchPush_fail_preserves_modeWatches hw1_ok hlay2 rfl rfl
                        (fun _ r => r) ?_
                      intro l hl
                      by_cases hle : l = b.toNat
                      · subst hle; exact (hok2f (by assumption)).1 hb_lt
                      · exact hother2 l hl hle
                    exact hJ () m2 ⟨wvec2, wstk2, wlen2, wu2, wsort2, hlen2, hw2_fail, hm2⟩
                · have hw1_fail : ModeWatchesInv F_cur s1.core := by
                    refine fbl_watchPush_fail_preserves_modeWatches hw.watches hlay1 rfl rfl
                      (fun _ r => r) ?_
                    intro l hl
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
              s.core.trail_pos s.core.trail_end s.core.unflushed wvecO wstkO
              wlenO wuO s.core.num_binary 1#64 s.core.inconsistent
              s.core.unassigned s.scratch.phases wsortO _ hlenO' hwO'
              (Or.inr (Or.inr (Or.inl rfl))) (fun h0 => by cases h0)
              (fun _ => rfl) (fun h2 => by cases h2) (by assumption))
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

theorem full_set_inactive_wp (Γ : Env) :
    ∀ args m Q X, fullSetInactiveSpec args m Q X → Func.wp Γ full_set_inactive_body args m Q X := by
  rintro ⟨h, v, flag, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  have hcl := hlen.core_ok
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hcl.cur_vars_le; have hfll := hcl.flags_len; have hvl := hcl.vals_len
  fbl_group
  · rw [ite_eq_left (by c0_bound)] at hQ; exact hQ
  · have hv_lt : v.toNat < s.core.cur_vars := by c0_bound
    rw [ite_eq_right (by omega)] at hQ
    have h2v : ((v.setWidth 64) <<< (1 : Nat)).toNat = 2 * v.toNat := by
      have : v.toNat < 2 ^ 30 := by omega
      bv_omega
    refine wp_join_group
      (fun _ mJ => ∃ unass',
        (FullMem c { s with core := { s.core with unassigned := unass' } } ⋆ R) mJ)
      ?_ (fun J hJ => by
        fbl_group
        · exact hJ () _ ⟨_, by assumption⟩
        · exact hJ () _ ⟨_, by assumption⟩
        · exact hJ () _ ⟨_, by assumption⟩
        · exact hJ () _ ⟨_, by assumption⟩)
    rintro _ _ mJ ⟨unass', hmJ⟩
    fbl_group
    have hvn : (v.setWidth 64).toNat = v.toNat := by bv_omega
    exact hQ (s.core.flags.set (v.setWidth 64).toNat
      (s.core.flags[(v.setWidth 64).toNat]'(by rw [hfll, hvn]; omega) &&& ~~~1 ||| flag)) unass' m
      (by rw [List.length_set, hfll]) (by assumption)

private theorem full_add_unit_wp_gen (Γ : Env) (P : FullState → FullScratch → Prop)
    (hP_refl : ∀ s, P s s.scratch)
    (hP_phases : ∀ s sc ph', P s sc → P s { sc with phases := ph' })
    (hbt : ∀ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
        (R : Mem 64 → Prop) (m : Mem 64) {Q : Post []} {X : XPost},
      s.LengthsOk c → FullWitnessInv c F0 F_cur s.core → 0 < s.core.cur_level →
      (FullMem c s ⋆ R) m →
      (∀ vals' lvl' rsns' trl' tp' te' prop' cl' unass' (sc' : FullScratch) m',
        let s' : FullState :=
          { s with
            core := { s.core with
              vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
              trail_end := te', propagated := prop', cur_level := cl', unassigned := unass' }
            scratch := sc' }
        s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core → cl' = 0 → P s sc' →
        (FullMem c s' ⋆ R) m' → Q () m') →
      Γ "full_backtrack" [i64, i64] [] (c.hdr, 0#64, ()) m Q X)
    (halvl : EnvSpec Γ "full_assign_lvl" fullAssignLvlSpec) :
    ∀ c F0 F_cur s R lit m (Q : Post [.bool]) (X : XPost),
      s.LengthsOk c → FullWitnessInv c F0 F_cur s.core →
      (lit.toNat < 2 * s.core.cur_vars →
        (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat])) →
      (FullMem c s ⋆ R) m →
      (∀ (ok : Bool) vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl' inc'
        (sc' : FullScratch) m',
        let s' : FullState :=
          { s with
            core :=
              { s.core with
                vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
                trail_pos := tp', trail_end := te', propagated := prop', cur_level := cl',
                unassigned := unass', unflushed := unfl', inconsistent := inc' }
            scratch := sc' }
        s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core → cl' = 0 → P s sc' →
        (lit.toNat < 2 * s.core.cur_vars → ok = false → F0.Unsat ∧ inc' ≠ 0#64) →
        (ok = false → 2 * s.core.cur_vars ≤ lit.toNat ∨ (F0.Unsat ∧ inc' ≠ 0#64)) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m') →
      Func.wp Γ full_add_unit_body (c.hdr, lit, ()) m Q X := by
  intro c F0 F_cur s R lit m Q X hlen hw hent hm hQ
  have hcl := hlen.core_ok
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  fbl_group
  · refine wp_join_group
      (fun _ mJ => ∃ valsJ lvlJ rsnsJ trlJ tpJ teJ propJ clJ unassJ, ∃ scJ : FullScratch,
        let sJ : FullState :=
          { s with
            core := { s.core with
              vals := valsJ, lvl := lvlJ, rsns := rsnsJ, trl := trlJ, trail_pos := tpJ,
              trail_end := teJ, propagated := propJ, cur_level := clJ, unassigned := unassJ }
            scratch := scJ }
        sJ.LengthsOk c ∧ FullWitnessInv c F0 F_cur sJ.core ∧ clJ = 0 ∧ P s scJ ∧
        (FullMem c sJ ⋆ R) mJ)
      ?_ (fun J hJ => by
        fbl_group
        · refine wp_call_of_spec _ _ (hbt c F0 F_cur s R m hlen hw (by c0_bound) hm ?_)
          dsimp only
          intro vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m' hlen' hw' hcl' hP' hm'
          fbl_group
          exact hJ () m' ⟨vals', lvl', rsns', trl', tp', te', prop', cl', unass', sc',
            hlen', hw', hcl', hP', hm'⟩
        · have hcl0 : s.core.cur_level = 0 := by
            have := hw.cur_level_le; have := hcl.trail_end_le; have := hcl.cur_vars_le
            c0_bound
          have hs_self : ({ s with
              core := { s.core with
                vals := s.core.vals, lvl := s.core.lvl, rsns := s.core.rsns, trl := s.core.trl,
                trail_pos := s.core.trail_pos, trail_end := s.core.trail_end,
                propagated := s.core.propagated, cur_level := s.core.cur_level,
                unassigned := s.core.unassigned }
              scratch := s.scratch } : FullState) = s := by cases s; rfl
          exact hJ () m ⟨s.core.vals, s.core.lvl, s.core.rsns, s.core.trl, s.core.trail_pos,
            s.core.trail_end, s.core.propagated, s.core.cur_level, s.core.unassigned, s.scratch,
            by simpa only [hs_self] using hlen, by simpa only [hs_self] using hw, hcl0,
            hP_refl s, by simpa only [hs_self] using hm⟩)
    rintro _ _ mJ ⟨valsJ, lvlJ, rsnsJ, trlJ, tpJ, teJ, propJ, clJ, unassJ, scJ,
      hlenJ, hwJ, hclJ0, hPJ, hmJ⟩
    let sJ : FullState :=
      { s with
        core := { s.core with
          vals := valsJ, lvl := lvlJ, rsns := rsnsJ, trl := trlJ, trail_pos := tpJ,
          trail_end := teJ, propagated := propJ, cur_level := clJ, unassigned := unassJ }
        scratch := scJ }
    change sJ.LengthsOk c at hlenJ
    change FullWitnessInv c F0 F_cur sJ.core at hwJ
    change (FullMem c sJ ⋆ R) mJ at hmJ
    have hclJ := hlenJ.core_ok
    have hcvJ := hclJ.cur_vars_le; have hvlJ := hclJ.vals_len
    have hshr1 : (lit >>> (1 : Nat)).toNat = lit.toNat / 2 := by
      simp [Nat.shiftRight_eq_div_pow]
    fbl_group
    · have hge : 2 * s.core.cur_vars ≤ lit.toNat := by
        have h1 : sJ.core.cur_vars ≤ lit.toNat / 2 := by c0_bound
        change s.core.cur_vars ≤ lit.toNat / 2 at h1
        omega
      exact hQ false valsJ s.core.flags lvlJ rsnsJ trlJ tpJ teJ propJ clJ unassJ s.core.unflushed
        s.core.inconsistent scJ mJ hlenJ hwJ hclJ0 hPJ
        (fun hlt _ => absurd hlt (by omega)) (fun _ => Or.inl hge) hmJ
    · exact hQ true valsJ s.core.flags lvlJ rsnsJ trlJ tpJ teJ propJ clJ unassJ s.core.unflushed
        s.core.inconsistent scJ mJ hlenJ hwJ hclJ0 hPJ
        (fun _ hf => by cases hf) (fun hf => by cases hf) hmJ
    · have hv_lt : lit.toNat / 2 < s.core.cur_vars := by
        change lit.toNat / 2 < sJ.core.cur_vars; c0_bound
      have hlit_lt : lit.toNat < 2 * sJ.core.cur_vars := by omega
      have hdom := hwJ.vals_domain lit.toNat hlit_lt
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hdom
      have hva_neg : sJ.core.vals[lit.toNat]?.getD 0#8 = 0xFF#8 := by
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
        exact (fbl_bv8_vals_pos hdom).2.mp (by assumption)
      have hent_lit := hent (by omega)
      have hFcur_unsat : (cnfOfClauses F_cur).Unsat := by
        refine unsat_of_entails_nil (entails_of_mem_or_false hent_lit fun l hl => Or.inr ?_)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        subst hl
        obtain ⟨i, hi, heq⟩ := (hwJ.vals_false_iff _ hlit_lt).mp hva_neg
        have hs := hwJ.level0_sound i hi
          (by have := hwJ.lvl_le i hi; simp only [sJ, hclJ0] at *; omega)
        rwa [heq] at hs
      have hF0_unsat : F0.Unsat := hwJ.ext_sound.2 hFcur_unsat
      have hlen_inc : ({ sJ with core := { sJ.core with inconsistent := 1#64 } } :
          FullState).LengthsOk c := ⟨{ hclJ with }, hlenJ.scratch_ok⟩
      have hwJ' : FullWitnessInv c F0 F_cur { sJ.core with inconsistent := 1#64 } :=
        { hwJ with
          inconsistent_sound := fun _ => hFcur_unsat
          arena := { hwJ.arena with len_ok := hwJ.arena.len_ok }
          watches := hwJ.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }
      exact hQ false valsJ s.core.flags lvlJ rsnsJ trlJ tpJ teJ propJ clJ unassJ s.core.unflushed
        1#64 scJ _ hlen_inc hwJ' hclJ0 hPJ
        (fun _ _ => ⟨hF0_unsat, by decide⟩) (fun _ => Or.inr ⟨hF0_unsat, by decide⟩)
        (by assumption)
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
      have hent_lit := hent (by omega)
      c0_call halvl
      refine ⟨c, sJ, R, rfl, hlenJ, hmJ, ?_⟩
      have hte_lt : sJ.core.trail_end < c.max_vars := by
        have := hwJ.trail_end_lt_of_unassigned hlit_lt hval0; omega
      have hnot_cond : ¬ (sJ.core.cur_vars ≤ lit.toNat / 2 ∨
          c.max_vars ≤ sJ.core.trail_end ∨ sJ.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8) := by
        intro h; rcases h with h1 | h2 | h3
        · omega
        · omega
        · exact h3 hval0
      rw [ite_eq_right hnot_cond]
      dsimp only
      intro flags' unassigned' phases' m' hfll hphl hm'
      obtain ⟨hlen', hw'⟩ :=
        fbl_assignLevel0_preserves_fullWitness hlenJ hwJ hclJ0 hfll hphl hlit_lt hval0 hent_lit
      exact hQ true ((sJ.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8)
        flags' (sJ.core.lvl.set (lit.toNat / 2) 0#32)
        (sJ.core.rsns.set (lit.toNat / 2) 0xFFFFFFFF#32) (sJ.core.trl.set sJ.core.trail_end lit)
        (sJ.core.trail_pos.set (lit.toNat / 2) (BitVec.ofNat 32 sJ.core.trail_end))
        (sJ.core.trail_end + 1) propJ clJ unassigned' (s.core.unflushed + 1#64) s.core.inconsistent
        { scJ with phases := phases' } m' hlen' hw' hclJ0 (hP_phases s scJ phases' hPJ)
        (fun _ hf => by cases hf) (fun hf => by cases hf) hm'

theorem full_add_unit_wp (Γ : Env)
    (hbt : EnvSpec Γ "full_backtrack" fullBacktrackSpec)
    (halvl : EnvSpec Γ "full_assign_lvl" fullAssignLvlSpec) :
    ∀ args m Q X, fullAddUnitSpec args m Q X → Func.wp Γ full_add_unit_body args m Q X := by
  let P : FullState → FullScratch → Prop := fun s sc =>
    ∃ ph ta ba pt pb hp ps hl qsi qss,
      sc = { s.scratch with
        phases := ph, target_assigned := ta, best_assigned := ba, phases_target := pt,
        phases_best := pb, heap := hp, pos := ps, heap_len := hl,
        q_search_idx := qsi, q_search_stamp := qss }
  rintro ⟨h, lit, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hent, hm, hQ⟩
  refine full_add_unit_wp_gen Γ P
    (fun s => ⟨s.scratch.phases, s.scratch.target_assigned, s.scratch.best_assigned,
      s.scratch.phases_target, s.scratch.phases_best, s.scratch.heap, s.scratch.pos,
      s.scratch.heap_len, s.scratch.q_search_idx, s.scratch.q_search_stamp,
      by cases s.scratch; rfl⟩)
    (fun s sc ph' ⟨_, ta, ba, pt, pb, hp, ps, hl, qsi, qss, hsc⟩ => by
      subst hsc; exact ⟨ph', ta, ba, pt, pb, hp, ps, hl, qsi, qss, by cases s.scratch; rfl⟩)
    (fun c F0 F_cur s R m Q X hlen hw hpos hm hk => by
      refine hbt _ m Q X ⟨c, s, R, rfl, hlen, hw.trail_lits_lt, hm, ?_⟩
      have hnot : ¬ s.core.cur_level ≤ (0#64).toNat := by
        simpa [BitVec.toNat_zero] using Nat.not_le_of_lt hpos
      rw [ite_eq_right hnot]; dsimp only
      intro vals' lvl' rsns' trl' tp' te' prop' unass' ta' ba' pt' pb' hp' ps' hl' qsi' qss' m'
        hlen' _ _ _ _ hw' hm'
      have hs_eq :
          ({ s with
            core := { s.core with
              vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
              trail_end := te', propagated := prop', cur_level := (0#64).toNat,
              unassigned := unass' }
            scratch := { s.scratch with
              target_assigned := ta', best_assigned := ba', phases_target := pt',
              phases_best := pb', heap := hp', pos := ps', heap_len := hl',
              q_search_idx := qsi', q_search_stamp := qss' } } : FullState) =
          { s with
            core := { s.core with
              vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
              trail_end := te', propagated := prop', cur_level := 0, unassigned := unass' }
            scratch := { s.scratch with
              phases := s.scratch.phases, target_assigned := ta', best_assigned := ba',
              phases_target := pt', phases_best := pb', heap := hp', pos := ps', heap_len := hl',
              q_search_idx := qsi', q_search_stamp := qss' } } := by
        cases s.scratch; simp
      rw [hs_eq] at hlen' hm'
      have hw'' : FullWitnessInv c F0 F_cur
          { s.core with
            vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
            trail_end := te', propagated := prop', cur_level := 0, unassigned := unass' } := by
        simpa only [BitVec.toNat_zero] using hw' F0 F_cur hw
      exact hk vals' lvl' rsns' trl' tp' te' prop' 0 unass' _ m' hlen' hw'' rfl
        ⟨s.scratch.phases, ta', ba', pt', pb', hp', ps', hl', qsi', qss', rfl⟩ hm')
    halvl c F0 F_cur s R lit m Q X hlen hw hent hm ?_
  dsimp only
  rintro ok vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl' inc' sc' m'
    hlen' hw' hcl' ⟨ph', ta', ba', pt', pb', hp', ps', hl', qsi', qss', rfl⟩ hlt hfa hm'
  exact hQ ok vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl' inc'
    ph' ta' ba' pt' pb' hp' ps' hl' qsi' qss' m' hlen' hw' hcl' hlt hfa hm'

theorem full_add_unit_ext_wp (Γ : Env)
    (hbt : EnvSpec Γ "full_backtrack" fullBacktrackExtSpec)
    (halvl : EnvSpec Γ "full_assign_lvl" fullAssignLvlSpec) :
    ∀ args m Q X, fullAddUnitExtSpec args m Q X → Func.wp Γ full_add_unit_body args m Q X := by
  let P : FullState → FullScratch → Prop := fun s sc =>
    FullProbeScratchPres s { s with scratch := sc } ∧ sc.shrink_stk = s.scratch.shrink_stk
  rintro ⟨h, lit, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hent, hm, hQ⟩
  refine full_add_unit_wp_gen Γ P
    (fun _ => ⟨⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩)
    (fun _ _ _ ⟨hp, hs⟩ => ⟨hp, hs⟩)
    (fun c F0 F_cur s R m Q X hlen hw hpos hm hk => by
      have hmx := c.hmaxv; unfold dimacsBound at hmx
      have hcl := hlen.core_ok
      have hcl_lt : s.core.cur_level < 2 ^ 64 := by
        have := hw.cur_level_le; have := hcl.trail_end_le; have := hcl.cur_vars_le; omega
      have hmax_pos : (0#64).toNat < s.core.cur_level → (0#64).toNat < c.max_vars := by
        intro _; have := hw.cur_level_le; have := hcl.trail_end_le; have := hcl.cur_vars_le; omega
      refine hbt _ m Q X ⟨c, s, R, rfl, hlen, hcl_lt, hmax_pos, hw.trail_lits_lt, hm, ?_⟩
      have hnot : ¬ s.core.cur_level ≤ (0#64).toNat := by
        simpa [BitVec.toNat_zero] using Nat.not_le_of_lt hpos
      rw [ite_eq_right hnot]; dsimp only
      intro vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m'
        hlen' _ _ hcl_eq hpres hshrk _ _ hw' hm'
      have hcl0 : cl' = 0 := by simpa [BitVec.toNat_zero] using hcl_eq
      exact hk vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m' hlen'
        (hw' F0 F_cur hw (Nat.zero_le _)) hcl0 ⟨hpres, hshrk⟩ hm')
    halvl c F0 F_cur s R lit m Q X hlen hw hent hm ?_
  dsimp only
  rintro ok vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl' inc' sc' m'
    hlen' hw' hcl' ⟨hpres, hshrk⟩ hlt hfa hm'
  exact hQ ok vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl' inc' sc' m'
    hlen' hw' hcl' hpres hshrk hlt hfa hm'

private abbrev BoolSlice (sp : Bool) (F_cur : List (List Nat)) (k : FullCoreState)
    (lit p rem : Nat) : Prop :=
  if sp then WatchSliceOk F_cur k lit p rem else DenseWatchSliceOk F_cur k lit p rem

private theorem boolSlice_relocate {sp : Bool} {F_cur : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat} (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ idx < rem, k'.wstk[p' + idx]? = k.wstk[p + idx]?)
    (h : BoolSlice sp F_cur k lit p rem) : BoolSlice sp F_cur k' lit p' rem := by
  have hent : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
    rw [CNF.entails_def]; exact fun _ x => x
  cases sp <;> simp only [BoolSlice, ↓reduceIte, Bool.false_eq_true] at h ⊢
  · exact h.fbl_relocate hent hvars hsub hwstk
  · exact h.fbl_relocate hent hvars hsub hwstk

private theorem boolSlice_bin_tail {sp : Bool} {F_cur : List (List Nat)} {k : FullCoreState}
    {src p rem : Nat} {w0 : BitVec 32} (hsl : BoolSlice sp F_cur k src p rem)
    (hpos : 0 < rem) (hp : k.wstk[p]? = some w0) (hbin : (w0 &&& 0x80000000#32) ≠ 0#32) :
    BoolSlice sp F_cur k src (p + 1) (rem - 1) := by
  cases sp <;> simp only [BoolSlice, ↓reduceIte, Bool.false_eq_true] at hsl ⊢
  · cases hsl with
    | empty => omega
    | bin _ _ _ _ _ hrest => exact hrest
    | occ hp0 _ hfl _ _ _ _ => rw [hp] at hp0; cases hp0; exact absurd hfl hbin
  · cases hsl with
    | empty => omega
    | bin _ _ _ _ _ hrest => exact hrest
    | large hp0 _ hfl _ _ _ => rw [hp] at hp0; cases hp0; exact absurd hfl hbin

private theorem boolSlice_large_tail {sp : Bool} {F_cur : List (List Nat)} {k : FullCoreState}
    {src p rem : Nat} {w0 : BitVec 32} (hsl : BoolSlice sp F_cur k src p rem)
    (hpos : 0 < rem) (hp : k.wstk[p]? = some w0) (hlg : (w0 &&& 0x80000000#32) = 0#32) :
    2 ≤ rem ∧ BoolSlice sp F_cur k src (p + 2) (rem - 2) := by
  cases sp <;> simp only [BoolSlice, ↓reduceIte, Bool.false_eq_true] at hsl ⊢
  · cases hsl with
    | empty => omega
    | bin hp0 hfl _ _ _ _ => rw [hp] at hp0; cases hp0; exact absurd hlg hfl
    | occ _ _ _ _ _ _ hrest => exact ⟨by omega, by simpa using hrest⟩
  · cases hsl with
    | empty => omega
    | bin hp0 hfl _ _ _ _ => rw [hp] at hp0; cases hp0; exact absurd hlg hfl
    | large _ _ _ _ _ hrest => exact ⟨by omega, by simpa using hrest⟩

private theorem boolSlice_copy_bin {sp : Bool} {F_cur : List (List Nat)} {k : FullCoreState}
    {wstk_q wstk' : List (BitVec 32)} {lit off q p rem : Nat} {w0 : BitVec 32}
    (hq : off ≤ q) (hpos : 0 < rem)
    (hp0 : k.wstk[p]? = some w0) (hbin : (w0 &&& 0x80000000#32) ≠ 0#32)
    (hw_q : ∀ idx < q - off, wstk'[off + idx]? = wstk_q[off + idx]?)
    (hw_new : wstk'[q]? = some w0)
    (hsl_q : BoolSlice sp F_cur { k with wstk := wstk_q } lit off (q - off))
    (hsl_p : BoolSlice sp F_cur k lit p rem) :
    BoolSlice sp F_cur { k with wstk := wstk' } lit off (q + 1 - off) := by
  let k' : FullCoreState := { k with wstk := wstk' }
  have hrel := boolSlice_relocate (k := { k with wstk := wstk_q }) (k' := k') (p := off)
    (p' := off) (Nat.le_refl _) (fun _ r => r) hw_q hsl_q
  have hq1 : off + (q - off) = q := by omega
  have hq_sub : q + 1 - off = (q - off) + 1 := by omega
  cases sp <;> simp only [BoolSlice, ↓reduceIte, Bool.false_eq_true, k'] at hrel hsl_p ⊢ <;>
    rw [hq_sub]
  · cases hsl_p with
    | empty => omega
    | bin hp hflag hne hlt hent _ =>
      rw [hp0] at hp; cases hp
      exact hrel.fbl_append_slice
        (DenseWatchSliceOk.bin (by simpa [hq1] using hw_new) hflag hne hlt hent .empty)
    | occ hp _ hfl _ _ _ _ => rw [hp0] at hp; cases hp; exact absurd hfl hbin
  · cases hsl_p with
    | empty => omega
    | bin hp hflag hne hlt hent _ =>
      rw [hp0] at hp; cases hp
      exact hrel.fbl_append_slice
        (WatchSliceOk.bin (by simpa [hq1] using hw_new) hflag hne hlt hent .empty)
    | large hp _ hfl _ _ _ => rw [hp0] at hp; cases hp; exact absurd hfl hbin

private theorem boolSlice_copy_large {sp : Bool} {F_cur : List (List Nat)} {k : FullCoreState}
    {wstk_q wstk' : List (BitVec 32)} {lit off q p rem : Nat} {w0 cr : BitVec 32}
    (hq : off ≤ q) (hpos : 0 < rem)
    (hp0 : k.wstk[p]? = some w0) (hp1 : k.wstk[p + 1]? = some cr)
    (hlg : (w0 &&& 0x80000000#32) = 0#32)
    (hw_q : ∀ idx < q - off, wstk'[off + idx]? = wstk_q[off + idx]?)
    (hw_new0 : wstk'[q]? = some w0) (hw_new1 : wstk'[q + 1]? = some cr)
    (hsl_q : BoolSlice sp F_cur { k with wstk := wstk_q } lit off (q - off))
    (hsl_p : BoolSlice sp F_cur k lit p rem) :
    BoolSlice sp F_cur { k with wstk := wstk' } lit off (q + 2 - off) := by
  let k' : FullCoreState := { k with wstk := wstk' }
  have hrel := boolSlice_relocate (k := { k with wstk := wstk_q }) (k' := k') (p := off)
    (p' := off) (Nat.le_refl _) (fun _ r => r) hw_q hsl_q
  have hq1 : off + (q - off) = q := by omega
  have hq_sub : q + 2 - off = (q - off) + 2 := by omega
  cases sp <;> simp only [BoolSlice, ↓reduceIte, Bool.false_eq_true, k'] at hrel hsl_p ⊢ <;>
    rw [hq_sub]
  · cases hsl_p with
    | empty => omega
    | bin hp hfl _ _ _ _ => rw [hp0] at hp; cases hp; exact absurd hlg hfl
    | occ hp hpc hflag hsz hlt href _ =>
      rw [hp0] at hp; rw [hp1] at hpc; cases hp; cases hpc
      exact hrel.fbl_append_slice
        (DenseWatchSliceOk.occ (by simpa [hq1] using hw_new0)
          (by simpa [hq1] using hw_new1) hflag hsz hlt href .empty)
  · cases hsl_p with
    | empty => omega
    | bin hp hfl _ _ _ _ => rw [hp0] at hp; cases hp; exact absurd hlg hfl
    | large hp hpc hflag hlt href _ =>
      rw [hp0] at hp; rw [hp1] at hpc; cases hp; cases hpc
      exact hrel.fbl_append_slice
        (WatchSliceOk.large (by simpa [hq1] using hw_new0)
          (by simpa [hq1] using hw_new1) hflag hlt href .empty)

theorem full_delete_bin_side_wp (Γ : Env) :
    ∀ args m Q X, fullDeleteBinSideSpec args m Q X →
      Func.wp Γ full_delete_bin_side_body args m Q X := by
  rintro ⟨h, lit, other, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hbd_arg, hm, hQ⟩
  have hcl := hlen.core_ok
  have hmx := c.hmaxv; have hwc := c.hwcap; unfold dimacsBound at hmx hwc
  have hcv_le := hcl.cur_vars_le; have hwvl := hcl.wvec_len; have hwl := hcl.wstk_len_arr
  have hwle := hcl.wlen_le
  have hret_same : Q () m := by
    have hlen_id : ({ s with core :=
        { s.core with wvec := s.core.wvec, wstk := s.core.wstk, wusable := s.core.wusable } } :
        FullState).LengthsOk c := ⟨{ hcl with }, hlen.scratch_ok⟩
    exact hQ s.core.wvec s.core.wstk s.core.wusable m hlen_id
      (fun _ => ⟨rfl, Nat.le_refl _⟩) (fun _ _ _ => ⟨rfl, rfl⟩) (fun _ _ _ => rfl)
      (fun _ hw => hw) (fun _ hw => hw) (fun hl => hl) (fun _ hmw => hmw) hm
  fbl_group
  · exact hret_same
  · exact hret_same
  · have hlit_lt : lit.toNat < 2 * s.core.cur_vars := by c0_bound
    have hidx0 : (lit.setWidth 64 <<< (1 : Nat)).toNat = 2 * lit.toNat := by
      have : lit.toNat < 2 ^ 30 := by omega
      bv_omega
    have hidx1 : ((lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat = 2 * lit.toNat + 1 := by
      have : lit.toNat < 2 ^ 30 := by omega
      bv_omega
    have hoff_eq : (s.core.wvec[2 * lit.toNat]'(by omega)).toNat =
        fullWatchOffCore s.core lit.toNat := by
      unfold fullWatchOffCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    have hsz_eq : (s.core.wvec[2 * lit.toNat + 1]'(by omega)).toNat =
        fullWatchSizeCore s.core lit.toNat := by
      unfold fullWatchSizeCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    have hbd_slice : fullWatchOffCore s.core lit.toNat + fullWatchSizeCore s.core lit.toNat ≤
        s.core.wlen := hbd_arg hlit_lt
    have hs0 : 2 * lit.toNat % 2 ^ 64 = 2 * lit.toNat := by omega
    have h1_64 : BitVec.toNat (1 : BitVec 64) = 1 := rfl
    have hs1 : (2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = 2 * lit.toNat + 1 := by
      rw [h1_64]; omega
    have h_off : (BitVec.setWidth 64
        (s.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'(by rw [hidx0]; omega))).toNat =
        fullWatchOffCore s.core lit.toNat := by
      simp only [hidx0, BitVec.toNat_setWidth, hoff_eq]; omega
    have h_sz : (BitVec.setWidth 64
        (s.core.wvec[2 * lit.toNat + 1]'(by omega))).toNat =
        fullWatchSizeCore s.core lit.toNat := by
      simp only [BitVec.toNat_setWidth, hsz_eq]; omega
    have h_end : (BitVec.setWidth 64 s.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat] +
        BitVec.setWidth 64 s.core.wvec[(2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) %
          2 ^ 64]).toNat =
        fullWatchOffCore s.core lit.toNat + fullWatchSizeCore s.core lit.toNat := by
      simp only [hidx0, hs1, BitVec.toNat_add, BitVec.toNat_setWidth, hoff_eq, hsz_eq]; omega
    have hsz_pos : 0 < fullWatchSizeCore s.core lit.toNat := by
      refine Nat.pos_of_ne_zero fun h0 => hc (BitVec.eq_of_toNat_eq ?_)
      simp only [h1_64, Nat.mod_eq_of_lt (by omega : 2 * lit.toNat + 1 < 2 ^ 64),
        BitVec.toNat_setWidth, hsz_eq, h0]
      rfl
    let off := fullWatchOffCore s.core lit.toNat
    let sz := fullWatchSizeCore s.core lit.toNat
    let end_ := off + sz
    have h_cond_lt : (s.core.wvec[2 * lit.toNat % 2 ^ 64].toNat +
        s.core.wvec[(2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64].toNat) % 2 ^ 64 =
        end_ := by
      simp only [hs0, hs1, hoff_eq, hsz_eq]; omega
    refine wp_loop_inv
        (fun (p, q, _rem, ()) ml => ∃ wstk1 : List (BitVec 32),
          off ≤ q.toNat ∧ q.toNat ≤ p.toNat ∧ p.toNat ≤ end_ ∧ wstk1.length = c.wcap ∧
          (∀ idx, idx < off ∨ p.toNat ≤ idx → wstk1[idx]? = s.core.wstk[idx]?) ∧
          (∀ idx < q.toNat - off,
            ∃ src < end_ - off, wstk1[off + idx]? = s.core.wstk[off + src]?) ∧
          (∀ sp F_cur, BoolSlice sp F_cur s.core lit.toNat off (end_ - off) →
            BoolSlice sp F_cur { s.core with wstk := wstk1 } lit.toNat off (q.toNat - off) ∧
            BoolSlice sp F_cur s.core lit.toNat p.toNat (end_ - p.toNat)) ∧
          (FullMem c { s with core := { s.core with wstk := wstk1 } } ⋆ R) ml)
        (fun (p, _, _, ()) _ => end_ - p.toNat)
        (fun J hJ => by
          fbl_group
          have h_off_eq : (BitVec.setWidth 64
              (s.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'(by
                rw [hidx0]; omega))).toNat = off := h_off
          refine hJ _ _ ⟨s.core.wstk, h_off_eq ▸ Nat.le_refl _, le_refl _,
            by rw [h_off_eq]; omega, hwl, fun _ _ => rfl,
            fun _ h => by rw [h_off_eq] at h; omega, fun sp F_cur hs => ?_, hm⟩
          rw [h_off_eq]
          have heq0 : off - off = 0 := Nat.sub_self off
          have heqs : end_ - off = sz := by omega
          rw [heq0]; refine ⟨?_, by simpa [heqs] using hs⟩
          cases sp <;> simp only [BoolSlice, ↓reduceIte, Bool.false_eq_true] <;> exact .empty)
        (fun J (p, q, rem, ()) ml ⟨wstk1, hq_lo, hqp, hp_hi, hwl1, hrest1, hsrc1, hsl1, hm1⟩ ih =>
          ?_)
    fbl_group
    · have hp_lt : p.toNat < end_ := by rw [← h_cond_lt]; assumption
      have hrem_pos : 0 < end_ - p.toNat := by omega
      have hp_lt_cap : p.toNat < c.wcap := by omega
      have hw0_val : wstk1[p.toNat]'(by omega) = s.core.wstk[p.toNat]'(by omega) := by
        have := hrest1 p.toNat (Or.inr (le_refl _))
        rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at this
        exact Option.some.inj this
      have hw0_eq : s.core.wstk[p.toNat]? = some (s.core.wstk[p.toNat]'(by omega)) :=
        List.getElem?_eq_getElem (by omega)
      have hp1_eq : (p + 1).toNat = p.toNat + 1 := by
        simp [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega : p.toNat + 1 < 2 ^ 64)]
      refine wp_join_group
        (fun (p', q', rem', ()) mJ => ∃ wstk2 : List (BitVec 32),
          off ≤ q'.toNat ∧ q'.toNat ≤ p'.toNat ∧ p'.toNat ≤ end_ ∧ p.toNat < p'.toNat ∧
          wstk2.length = c.wcap ∧
          (∀ idx, idx < off ∨ p'.toNat ≤ idx → wstk2[idx]? = s.core.wstk[idx]?) ∧
          (∀ idx < q'.toNat - off,
            ∃ src < end_ - off, wstk2[off + idx]? = s.core.wstk[off + src]?) ∧
          (∀ sp F_cur, BoolSlice sp F_cur s.core lit.toNat off (end_ - off) →
            BoolSlice sp F_cur { s.core with wstk := wstk2 } lit.toNat off (q'.toNat - off) ∧
            BoolSlice sp F_cur s.core lit.toNat p'.toNat (end_ - p'.toNat)) ∧
          (FullMem c { s with core := { s.core with wstk := wstk2 } } ⋆ R) mJ)
        (by
          rintro _ ⟨p', q', rem', ⟨⟩⟩ mJ
            ⟨wstk2, hq'lo, hq'p', hp'hi, hpgt, hwl2, hr2, hsrc2, hs2, hm2⟩
          dsimp only at hq'lo hq'p' hp'hi hpgt hr2 hsrc2 hs2 ⊢
          exact ih (p', q', rem', ()) mJ (by dsimp only; omega)
            ⟨wstk2, hq'lo, hq'p', hp'hi, hwl2, hr2, hsrc2, hs2, hm2⟩)
        (fun J1 hJ1 => by
          fbl_group
          · refine wp_join_group
              (fun (q'', rem'', ()) mJ1 => ∃ wstk2 : List (BitVec 32),
                off ≤ q''.toNat ∧ q''.toNat ≤ p.toNat + 1 ∧ wstk2.length = c.wcap ∧
                (∀ idx, idx < off ∨ p.toNat + 1 ≤ idx → wstk2[idx]? = s.core.wstk[idx]?) ∧
                (∀ idx < q''.toNat - off,
                  ∃ src < end_ - off, wstk2[off + idx]? = s.core.wstk[off + src]?) ∧
                (∀ sp F_cur, BoolSlice sp F_cur s.core lit.toNat off (end_ - off) →
                  BoolSlice sp F_cur { s.core with wstk := wstk2 } lit.toNat off
                    (q''.toNat - off)) ∧
                (FullMem c { s with core := { s.core with wstk := wstk2 } } ⋆ R) mJ1)
              (by
                rintro _ ⟨q'', rem'', ⟨⟩⟩ mJ1
                  ⟨wstk2, hq''lo, hq''le, hwl2, hr2, hsrc2, hsq2, hm2⟩
                dsimp only at hq''lo hq''le hsrc2 hsq2 ⊢
                refine hJ1 (p + 1, q'', rem'', ()) mJ1 ⟨wstk2, hq''lo,
                  by rw [hp1_eq]; exact hq''le,
                  by rw [hp1_eq]; omega,
                  by rw [hp1_eq]; exact Nat.lt_succ_self p.toNat, hwl2,
                  fun idx hidx => hr2 idx (by rw [hp1_eq] at hidx; exact hidx),
                  hsrc2, fun sp F_cur hs => ⟨hsq2 sp F_cur hs, by
                    rw [hp1_eq, show end_ - (p.toNat + 1) = (end_ - p.toNat) - 1 by omega]
                    exact boolSlice_bin_tail (hsl1 sp F_cur hs).2 hrem_pos hw0_eq
                      (by rw [← hw0_val]; assumption)⟩, hm2⟩)
              (fun J2 hJ2 => by
                refine wp_join_group (fun () mJ2 => mJ2 = ml)
                  (by
                    rintro _ _ mJ2 rfl
                    fbl_group
                    have hq1 : (q + 1).toNat = q.toNat + 1 := by
                      simp [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega : q.toNat + 1 < 2 ^ 64)]
                    let wstk2 := wstk1.set q.toNat (wstk1[p.toNat]'(by omega))
                    refine hJ2 (q + 1, rem, ()) _ ⟨wstk2, by rw [hq1]; omega,
                      by rw [hq1]; omega, by rw [List.length_set, hwl1],
                      fun idx hidx => ?_, fun idx hidx => ?_, fun sp F_cur hs => ?_,
                      by assumption⟩
                    · rw [List.getElem?_set_ne (by rcases hidx with h | h <;> omega)]
                      exact hrest1 idx
                        (by rcases hidx with h | h; exact Or.inl h; exact Or.inr (by omega))
                    · rw [hq1] at hidx
                      by_cases hlt_idx : idx < q.toNat - off
                      · rw [List.getElem?_set_ne (by omega)]; exact hsrc1 idx hlt_idx
                      · have heq_idx : idx = q.toNat - off := by omega
                        have hsum : off + idx = q.toNat := by omega
                        refine ⟨p.toNat - off, by omega, ?_⟩
                        rw [hsum, List.getElem?_eq_getElem (by rw [List.length_set]; omega),
                          List.getElem_set_self, hw0_val,
                          show off + (p.toNat - off) = p.toNat by omega, hw0_eq]
                    · rw [hq1]
                      refine boolSlice_copy_bin (wstk' := wstk2) hq_lo hrem_pos hw0_eq
                        (by rw [← hw0_val]; assumption)
                        (fun idx hidx => by rw [List.getElem?_set_ne (by omega)])
                        (by rw [List.getElem?_eq_getElem (by rw [List.length_set]; omega),
                          List.getElem_set_self, hw0_val])
                        (hsl1 sp F_cur hs).1 (hsl1 sp F_cur hs).2)
                  (fun J3 hJ3 => by
                    fbl_group
                    · exact hJ3 () ml rfl
                    · refine hJ2 (q, true, ()) _ ⟨wstk1, hq_lo, by omega, hwl1,
                        fun idx hidx => hrest1 idx
                          (by rcases hidx with h | h; exact Or.inl h; exact Or.inr (by omega)),
                        hsrc1, fun sp F_cur hs => (hsl1 sp F_cur hs).1, hm1⟩
                    · exact hJ3 () ml rfl))
          · -- large clause branch
            refine wp_join_group
              (fun (p'', q'', ()) mJ1 => ∃ wstk2 : List (BitVec 32),
                off ≤ q''.toNat ∧ q''.toNat ≤ p''.toNat ∧ p''.toNat ≤ end_ ∧ p.toNat < p''.toNat ∧
                wstk2.length = c.wcap ∧
                (∀ idx, idx < off ∨ p''.toNat ≤ idx → wstk2[idx]? = s.core.wstk[idx]?) ∧
                (∀ idx < q''.toNat - off,
                  ∃ src < end_ - off, wstk2[off + idx]? = s.core.wstk[off + src]?) ∧
                (∀ sp F_cur, BoolSlice sp F_cur s.core lit.toNat off (end_ - off) →
                  BoolSlice sp F_cur { s.core with wstk := wstk2 } lit.toNat off
                    (q''.toNat - off) ∧
                  BoolSlice sp F_cur s.core lit.toNat p''.toNat (end_ - p''.toNat)) ∧
                (FullMem c { s with core := { s.core with wstk := wstk2 } } ⋆ R) mJ1)
              (by
                rintro _ ⟨p'', q'', ⟨⟩⟩ mJ1
                  ⟨wstk2, hq''lo, hq''p'', hp''hi, hpgt, hwl2, hr2, hsrc2, hs2, hm2⟩
                dsimp only at hq''lo hq''p'' hp''hi hpgt hr2 hsrc2 hs2 ⊢
                exact hJ1 _ mJ1 ⟨wstk2, hq''lo, hq''p'', hp''hi, hpgt, hwl2, hr2, hsrc2, hs2, hm2⟩)
              (fun J2 hJ2 => by
                fbl_unmdata; repeat fbl_strip
                fbl_split_jnz
                · have hp1_lt_end : (p + 1).toNat < end_ := by rw [← h_cond_lt]; assumption
                  have hp1_lt_wstk : (p + 1).toNat <
                      ({ s with core := { s.core with wstk := wstk1 } } :
                        FullState).core.wstk.length := by
                    dsimp only; omega
                  fbl_group
                  have hcr_val : wstk1[p.toNat + 1]'(by omega) =
                      s.core.wstk[p.toNat + 1]'(by omega) := by
                    have := hrest1 (p.toNat + 1) (Or.inr (by omega))
                    rw [List.getElem?_eq_getElem (by omega),
                        List.getElem?_eq_getElem (by omega)] at this
                    exact Option.some.inj this
                  have hcr_eq : s.core.wstk[p.toNat + 1]? =
                      some (s.core.wstk[p.toNat + 1]'(by omega)) :=
                    List.getElem?_eq_getElem (by omega)
                  have hp2_eq : (p + 1 + 1).toNat = p.toNat + 2 := by
                    simp [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega : p.toNat + 2 < 2 ^ 64)]
                  have hq1_eq : (q + 1).toNat = q.toNat + 1 := by
                    simp [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega : q.toNat + 1 < 2 ^ 64)]
                  have hq2_eq : (q + 2).toNat = q.toNat + 2 := by
                    simp [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega : q.toNat + 2 < 2 ^ 64)]
                  let wstk2 := (wstk1.set q.toNat (wstk1[p.toNat]'(by omega))).set
                    (q.toNat + 1) (wstk1[p.toNat + 1]'(by omega))
                  refine hJ2 (p + 1 + 1, q + 2, ()) _ ⟨wstk2, by rw [hq2_eq]; omega,
                    by rw [hp2_eq, hq2_eq]; omega, by rw [hp2_eq]; omega, by rw [hp2_eq]; omega,
                    by rw [List.length_set, List.length_set, hwl1],
                    fun idx hidx => ?_, fun idx hidx => ?_, fun sp F_cur hs => ⟨?_, ?_⟩, ?_⟩
                  · rw [hp2_eq] at hidx
                    rw [List.getElem?_set_ne (by rcases hidx with h | h <;> omega),
                        List.getElem?_set_ne (by rcases hidx with h | h <;> omega)]
                    exact hrest1 idx
                      (by rcases hidx with h | h; exact Or.inl h; exact Or.inr (by omega))
                  · rw [hq2_eq] at hidx
                    by_cases hlt1 : idx < q.toNat - off
                    · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
                      exact hsrc1 idx hlt1
                    · by_cases hlt2 : idx = q.toNat - off
                      · have hsum : off + idx = q.toNat := by omega
                        refine ⟨p.toNat - off, by omega, ?_⟩
                        rw [hsum, List.getElem?_set_ne (by omega),
                          List.getElem?_eq_getElem (by rw [List.length_set]; omega),
                          List.getElem_set_self, hw0_val,
                          show off + (p.toNat - off) = p.toNat by omega, hw0_eq]
                      · have hsum : off + idx = q.toNat + 1 := by omega
                        refine ⟨p.toNat + 1 - off, by omega, ?_⟩
                        rw [hsum, List.getElem?_eq_getElem
                            (by rw [List.length_set, List.length_set]; omega),
                          List.getElem_set_self, hcr_val,
                          show off + (p.toNat + 1 - off) = p.toNat + 1 by omega, hcr_eq]
                  · rw [hq2_eq]
                    refine boolSlice_copy_large (wstk' := wstk2) hq_lo hrem_pos hw0_eq hcr_eq
                      (by rw [← hw0_val]; assumption)
                      (fun idx hidx => by
                        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)])
                      (by rw [List.getElem?_set_ne (by omega),
                        List.getElem?_eq_getElem (by rw [List.length_set]; omega),
                        List.getElem_set_self, hw0_val])
                      (by rw [List.getElem?_eq_getElem
                          (by rw [List.length_set, List.length_set]; omega),
                        List.getElem_set_self, hcr_val])
                      (hsl1 sp F_cur hs).1 (hsl1 sp F_cur hs).2
                  · rw [hp2_eq, show end_ - (p.toNat + 2) = (end_ - p.toNat) - 2 by omega]
                    exact (boolSlice_large_tail (hsl1 sp F_cur hs).2 hrem_pos hw0_eq
                      (by rw [← hw0_val]; assumption)).2
                  · simp only [wstk2, ← hp1_eq, ← hq1_eq]
                    assumption
                · have hp1_not_lt : ¬ (p + 1).toNat < end_ := by rw [← h_cond_lt]; assumption
                  refine hJ2 (p + 1, q, ()) _ ⟨wstk1, hq_lo, by rw [hp1_eq]; omega,
                    by rw [hp1_eq]; omega, by rw [hp1_eq]; omega, hwl1,
                    fun idx hidx => hrest1 idx
                      (by rcases hidx with h | h; exact Or.inl h; exact Or.inr (by omega)),
                    hsrc1, fun sp F_cur hs => False.elim (by
                      have h2 := (boolSlice_large_tail (hsl1 sp F_cur hs).2 hrem_pos hw0_eq
                        (by rw [← hw0_val]; assumption)).1
                      omega), hm1⟩))
    · -- Loop 1 exit: `!(p < end)`, so `p.toNat = end_`
      have hp_end : p.toNat = end_ := by
        have hnot : ¬ p.toNat < end_ := by rw [← h_cond_lt]; assumption
        omega
      have hsl_q : ∀ sp F_cur, BoolSlice sp F_cur s.core lit.toNat off (end_ - off) →
          BoolSlice sp F_cur { s.core with wstk := wstk1 } lit.toNat off (q.toNat - off) :=
        fun sp F_cur hs => (hsl1 sp F_cur hs).1
      have hrest_out : ∀ idx, idx < off ∨ end_ ≤ idx → wstk1[idx]? = s.core.wstk[idx]? := by
        intro idx hidx; exact hrest1 idx (by rw [hp_end]; exact hidx)
      refine wp_loop_inv
        (fun (k, ()) ml2 => ∃ wstk2 : List (BitVec 32),
          q.toNat ≤ k.toNat ∧ k.toNat ≤ end_ ∧ wstk2.length = c.wcap ∧
          (∀ idx < q.toNat - off, wstk2[off + idx]? = wstk1[off + idx]?) ∧
          (∀ idx < q.toNat - off,
            ∃ src < end_ - off, wstk2[off + idx]? = s.core.wstk[off + src]?) ∧
          (∀ idx, idx < off ∨ end_ ≤ idx → wstk2[idx]? = s.core.wstk[idx]?) ∧
          (FullMem c { s with core := { s.core with wstk := wstk2 } } ⋆ R) ml2)
        (fun (k, ()) _ => end_ - k.toNat)
        (fun J2 hJ2 => hJ2 (q, ()) ml ⟨wstk1, le_refl _, by omega, hwl1, fun _ _ => rfl,
          hsrc1, hrest_out, hm1⟩)
        (fun J2 (k, ()) ml2 ⟨wstk2, hqk, hk_hi, hwl2, hpref2, hsrc2, hout2, hm2⟩ ih2 => ?_)
      fbl_group
      · have hk_lt : k.toNat < end_ := by rw [← h_cond_lt]; assumption
        have hk1_eq : (k + 1).toNat = k.toNat + 1 := by
          simp [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega : k.toNat + 1 < 2 ^ 64)]
        let wstk3 := wstk2.set k.toNat 0xFFFFFFFF#32
        refine ih2 (k + 1, ()) _ (by dsimp only; omega)
          ⟨wstk3, by rw [hk1_eq]; omega, by rw [hk1_eq]; omega,
          by rw [List.length_set, hwl2], fun idx hidx => ?_, fun idx hidx => ?_,
          fun idx hidx => ?_, by assumption⟩
        · rw [List.getElem?_set_ne (by omega)]; exact hpref2 idx hidx
        · rw [List.getElem?_set_ne (by omega)]; exact hsrc2 idx hidx
        · rw [List.getElem?_set_ne (by rcases hidx with h | h <;> omega)]; exact hout2 idx hidx
      · have hk_end : k.toNat = end_ := by
          have hnot : ¬ k.toNat < end_ := by rw [← h_cond_lt]; assumption
          omega
        have hidx0' : (lit.setWidth 64 <<< (1 : Nat)).toNat = 2 * lit.toNat := hidx0
        have hidx1' : (lit.setWidth 64 <<< (1 : Nat) + (1 : BitVec 64)).toNat =
            2 * lit.toNat + 1 := by simpa using hidx1
        have hq_sub_lt : q.toNat - off < 2 ^ 32 := by omega
        have hq_trunc : (BitVec.setWidth 32 (q -
            BitVec.setWidth 64 (s.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'(by
              rw [hidx0']; omega)))).toNat =
            q.toNat - off := by
          have hwo_le : BitVec.setWidth 64
              (s.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'(by rw [hidx0']; omega)) ≤
              q :=
            BitVec.le_def.mpr (by rw [h_off]; exact hq_lo)
          rw [BitVec.toNat_setWidth, BitVec.toNat_sub_of_le hwo_le, h_off,
            Nat.mod_eq_of_lt hq_sub_lt]
        let wvec' := s.core.wvec.set (lit.setWidth 64 <<< (1 : Nat) + (1 : BitVec 64)).toNat
          (BitVec.setWidth 32 (q -
            BitVec.setWidth 64 (s.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'(by
              rw [hidx0']; omega))))
        let wu' := s.core.wusable +
          (BitVec.setWidth 64 (s.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'(by
              rw [hidx0']; omega)) +
            BitVec.setWidth 64 (s.core.wvec[(lit.setWidth 64 <<< (1 : Nat) +
              (1 : BitVec 64)).toNat]'(by rw [hidx1']; omega)) - q)
        let s' : FullState :=
          { s with core := { s.core with wvec := wvec', wstk := wstk2, wusable := wu' } }
        have hlen' : s'.LengthsOk c :=
          ⟨{ hcl with wvec_len := by simp [s', wvec', hwvl], wstk_len_arr := hwl2 },
           hlen.scratch_ok⟩
        have hwvec_self : fullWatchOffCore s'.core lit.toNat = off ∧
            fullWatchSizeCore s'.core lit.toNat = q.toNat - off := by
          constructor
          · unfold fullWatchOffCore; simp only [s', wvec']
            rw [List.getElem?_set_ne (by rw [hidx1']; omega)]; rfl
          · unfold fullWatchSizeCore; simp only [s', wvec']
            rw [hidx1', List.getElem?_eq_getElem (by rw [List.length_set]; omega),
              List.getElem_set_self, Option.getD_some, hq_trunc]
        have hwvec_other : ∀ l < 2 * s.core.cur_vars, l ≠ lit.toNat →
            fullWatchOffCore s'.core l = fullWatchOffCore s.core l ∧
            fullWatchSizeCore s'.core l = fullWatchSizeCore s.core l := by
          intro l _ hne; unfold fullWatchOffCore fullWatchSizeCore; simp only [s', wvec']
          rw [List.getElem?_set_ne (by rw [hidx1']; omega),
              List.getElem?_set_ne (by rw [hidx1']; omega)]
          exact ⟨rfl, rfl⟩
        have h_wvec_le : ∀ l < 2 * s.core.cur_vars,
            fullWatchOffCore s'.core l = fullWatchOffCore s.core l ∧
            fullWatchSizeCore s'.core l ≤ fullWatchSizeCore s.core l := by
          intro l hl_lt
          by_cases hll : l = lit.toNat
          · subst hll; exact ⟨hwvec_self.1, by rw [hwvec_self.2]; omega⟩
          · obtain ⟨ho, hs⟩ := hwvec_other l hl_lt hll; exact ⟨ho, by omega⟩
        have hws_new : ∀ F_cur, WatchSliceOk F_cur s.core lit.toNat off sz →
            WatchSliceOk F_cur s'.core lit.toNat (fullWatchOff s' lit.toNat)
              (fullWatchSize s' lit.toNat) := fun F_cur hw => by
          dsimp only [fullWatchOff, fullWatchSize]
          rw [hwvec_self.1, hwvec_self.2]
          exact boolSlice_relocate (sp := true) (k := { s.core with wstk := wstk1 }) (k' := s'.core)
            (p := off) (p' := off) (Nat.le_refl _) (fun _ r => r) hpref2
            (hsl_q true F_cur (show BoolSlice true F_cur s.core lit.toNat off (end_ - off) by
              simpa [BoolSlice, end_] using hw))
        have hdws_new : ∀ F_cur, DenseWatchSliceOk F_cur s.core lit.toNat off sz →
            DenseWatchSliceOk F_cur s'.core lit.toNat (fullWatchOff s' lit.toNat)
              (fullWatchSize s' lit.toNat) := fun F_cur hw => by
          dsimp only [fullWatchOff, fullWatchSize]
          rw [hwvec_self.1, hwvec_self.2]
          exact boolSlice_relocate (sp := false) (k := { s.core with wstk := wstk1 })
            (k' := s'.core) (p := off) (p' := off) (Nat.le_refl _) (fun _ r => r) hpref2
            (hsl_q false F_cur (show BoolSlice false F_cur s.core lit.toNat off (end_ - off) by
              simpa [BoolSlice, end_] using hw))
        have hlayout' : WatchStackLayout s.core → WatchStackLayout s'.core := fun hlay =>
          ⟨fun l hl_lt => by
            obtain ⟨ho, hs⟩ := h_wvec_le l hl_lt
            have := hlay.bounds l hl_lt
            have hwl_eq : s'.core.wlen = s.core.wlen := rfl
            rw [ho, hwl_eq]; omega,
           fun l hl_lt hpos => by
            obtain ⟨ho, hs⟩ := h_wvec_le l hl_lt
            rw [ho]; exact hlay.pos_off l hl_lt (by omega),
           fun l1 l2 h1 h2 hne hp1 hp2 => by
            obtain ⟨ho1, hs1⟩ := h_wvec_le l1 h1; obtain ⟨ho2, hs2⟩ := h_wvec_le l2 h2
            rcases hlay.disjoint l1 l2 h1 h2 hne (by omega) (by omega) with hl1 | hl2
            · left; rw [ho1, ho2]; omega
            · right; rw [ho1, ho2]; omega,
           fun l hl_lt idx hidx => by
            by_cases hll : l = lit.toNat
            · subst hll
              rw [hwvec_self.2] at hidx
              rw [hwvec_self.1]
              obtain ⟨src, hsrc, heq⟩ := hsrc2 idx hidx
              rw [heq]; exact hlay.no_sentinel lit.toNat hlit_lt src (by omega)
            · obtain ⟨ho, hs⟩ := hwvec_other l hl_lt hll
              rw [ho]; rw [hs] at hidx
              have hout_idx : fullWatchOffCore s.core l + idx < off ∨
                  end_ ≤ fullWatchOffCore s.core l + idx := by
                rcases hlay.disjoint l lit.toNat hl_lt hlit_lt hll (by omega) hsz_pos with h1 | h2
                · left; omega
                · right; omega
              rw [hout2 _ hout_idx]; exact hlay.no_sentinel l hl_lt idx hidx⟩
        have hmw' : ∀ F_cur, ModeWatchesInv F_cur s.core → ModeWatchesInv F_cur s'.core :=
          fun F_cur hmw => by
            have hslice_mode : if s.core.dense_mode = 0#64 then
                WatchSliceOk F_cur s'.core lit.toNat off (q.toNat - off)
              else DenseWatchSliceOk F_cur s'.core lit.toNat off (q.toNat - off) := by
              by_cases hdm : s.core.dense_mode = 0#64 <;>
                simp only [ModeWatchesInv, hdm, ↓reduceIte] at hmw ⊢
              · simpa [fullWatchOff, fullWatchSize, hwvec_self.1, hwvec_self.2] using
                  hws_new F_cur (hmw.slices lit.toNat hlit_lt)
              · simpa [fullWatchOff, fullWatchSize, hwvec_self.1, hwvec_self.2] using
                  hdws_new F_cur (hmw.slices lit.toNat hlit_lt)
            exact fbl_compactSlice_preserves_modeWatches hmw rfl rfl rfl (fun _ r => r) hlit_lt
              hq_lo (by omega) hwvec_self hwvec_other hout2 hslice_mode
        refine hQ wvec' wstk2 wu' _ hlen' (fun _ => ⟨hwvec_self.1, ?_⟩)
          hwvec_other (fun idx _ hidx => hout2 idx (by have := hidx hlit_lt; omega))
          hws_new hdws_new hlayout' hmw' (by assumption)
        change fullWatchSizeCore s'.core lit.toNat ≤ fullWatchSizeCore s.core lit.toNat
        rw [hwvec_self.2]; omega

theorem full_delete_binary_wp (Γ : Env)
    (hdbs : EnvSpec Γ "full_delete_bin_side" fullDeleteBinSideSpec) :
    ∀ args m Q X, fullDeleteBinarySpec args m Q X →
      Func.wp Γ full_delete_binary_body args m Q X := by
  rintro ⟨h, a, b, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hlay, hm, hQ⟩
  fbl_group
  c0_call hdbs
  refine ⟨c, s, R, rfl, hlen, fun ha => hlay.bounds a.toNat ha, hm, ?_⟩
  dsimp only
  intro wvec1 wstk1 wu1 m1 hlen1 _ _ _ _ _ hlay1_fn hmw1_fn hm1
  let s1 : FullState :=
    { s with core := { s.core with wvec := wvec1, wstk := wstk1, wusable := wu1 } }
  have hlay1 : WatchStackLayout s1.core := hlay1_fn hlay
  c0_call hdbs
  refine ⟨c, s1, R, rfl, hlen1, fun hb => hlay1.bounds b.toNat hb, hm1, ?_⟩
  dsimp only
  intro wvec2 wstk2 wu2 m2 hlen2 _ _ _ _ _ hlay2_fn hmw2_fn hm2
  let s2 : FullState :=
    { s with core := { s.core with wvec := wvec2, wstk := wstk2, wusable := wu2 } }
  have hlay2 : WatchStackLayout s2.core := hlay2_fn hlay1
  refine wp_join_group
    (fun _ mJ => ∃ nb',
      let s' : FullState :=
        { s with core := { s.core with wvec := wvec2, wstk := wstk2,
                                       wusable := wu2, num_binary := nb' } }
      s'.LengthsOk c ∧ WatchStackLayout s'.core ∧
      (∀ F_cur, ModeWatchesInv F_cur s.core → ModeWatchesInv F_cur s'.core) ∧
      (FullMem c s' ⋆ R) mJ)
    (by
      rintro _ _ mJ ⟨nb', hlen', hlay', hmw', hm'⟩
      exact hQ wvec2 wstk2 wu2 nb' mJ hlen' hlay' hmw' hm')
    (fun J hJ => by
      fbl_group
      · exact hJ () _ ⟨s.core.num_binary - 1#64, ⟨{ hlen2.core_ok with }, hlen2.scratch_ok⟩,
          hlay2.with_wstk rfl rfl rfl rfl,
          fun F_cur hmw =>
            (hmw2_fn F_cur (hmw1_fn F_cur hmw)).with_wstk rfl rfl rfl rfl rfl (fun _ r => r),
          by assumption⟩
      · exact hJ () m2 ⟨s.core.num_binary, hlen2, hlay2.with_wstk rfl rfl rfl rfl,
          fun F_cur hmw =>
            (hmw2_fn F_cur (hmw1_fn F_cur hmw)).with_wstk rfl rfl rfl rfl rfl (fun _ r => r),
          hm2⟩)

end LeanQbe.T.Examples.Kissat.Full
