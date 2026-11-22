/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM5
public import LeanQbe.T.Examples.Kissat.FullM4Proof
public import LeanQbe.T.Examples.Kissat.FullM4VivBceProof
public import LeanQbe.T.Examples.Kissat.FullM4SweepProof
public import LeanQbe.T.Examples.Kissat.FullM4InprocHotProof
public import LeanQbe.T.Examples.Kissat.FullM5DenseSafeProof
public import LeanQbe.T.Examples.Kissat.FullM5OtfsLemmas
public import LeanQbe.T.Examples.Kissat.FullM5KittenDefFixProof
public import LeanQbe.T.Examples.Kissat.FullM5HeurCoreProof
public import LeanQbe.T.Examples.Kissat.FullM5ProbePropProof
public import LeanQbe.T.Examples.Kissat.FullM5SchedLemmas
public import LeanQbe.T.Examples.Kissat.FullM5CongBinsLemmas
public import LeanQbe.T.Examples.Kissat.FullM5CongFixProof
public import LeanQbe.T.Examples.Kissat.FullM5HbrProof
public import LeanQbe.T.Examples.Kissat.FullM5OrchProof
import LeanQbe.T.Examples.Kissat.FullBinLuckyLemmas1
import LeanQbe.T.Examples.Kissat.FullBinLuckyLemmas2
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullParseInitLemmas3
import LeanQbe.T.Examples.Kissat.FullVivTopLemmas1
import LeanQbe.T.Examples.Kissat.FullFastTmkLemmas
import LeanQbe.T.Examples.Kissat.FullFastAdapters
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat `D-Full` Unified M5 Proof — Part 1 (Component Bridges & Orchestrators)

Defines parametric `(Γ : Env)` `Func.wp` proofs for Unified Kissat M5 components requiring
canonical `Full` / `FullM4` bridges:
1. `m5_add_bin_wp`: atomic binary-clause insertion rolling back `full_delete_bin_side(h, a, b)` on
   2nd `full_watch_push` OOM so watches never become asymmetric (`Full.fullAddBinSpec`).
2. `m5_bce_m4_wp`: `FullM4VivBce.full_bce_m4_body` under `FullFastSched.schedEnterDenseSpec`.
3. `m5_search_m5_wp`: `full_search_m5` against `FullM4.m4SearchSpec` under
   `FullM5Sched.m5RephaseSpec`.
4. Canonical forwarding wrappers (`full_init_state`, `full_reduce`, `full_preprocess`,
   `full_search`, `kissat_solve_bytes`) and cross-slice adapters (`full_extend_push_cl`,
   `full_add_bin` cong, `full_init_state_m5`, `full_find_definition`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM5

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full hiding
  full_init_state_body full_init_state_wf
  full_reduce_body full_reduce_wf
  full_preprocess_body full_preprocess_wf
  full_search_body full_search_wf
  kissat_solve_bytes_body kissat_solve_bytes_full_wf
  full_add_bin_body full_add_bin_wf
open Kraken.Bedrock2.Test

/-! ## 1. Atomic `m5_add_bin_wp` (`Full.fullAddBinSpec`) -/

section AddBinSection

open scoped FullArenaTactics FullBinLuckyTactics

/-- `Func.wp` proof for M5's atomic `full_add_bin` (`FullM5.full_add_bin_body`), rolling back
`full_delete_bin_side(h, a, b)` on 2nd `full_watch_push` OOM so watches stay symmetric. -/
theorem m5_add_bin_wp (Γ : Env)
    (hhas : ∀ xs m Q X, fullHasBinSpec xs m Q X →
      Γ "full_has_bin" [i64, i32, i32] [.bool] xs m Q X)
    (halvl : ∀ xs m Q X, fullAssignLvlSpec xs m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] xs m Q X)
    (hwpush : ∀ xs m Q X, fullWatchPushSpec xs m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] xs m Q X)
    (hdel : ∀ xs m Q X, fullDeleteBinSideSpec xs m Q X →
      Γ "full_delete_bin_side" [i64, i32, i32] [] xs m Q X) :
    ∀ args m Q X, fullAddBinSpec args m Q X → Func.wp Γ full_add_bin_body args m Q X := by
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
        · c0_call hhas
          refine ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hm, ?_⟩
          intro r _
          fbl_group
          · exact hret0
          · have hwpc := fbl_bv32_mask_bin b (by omega)
            have hwpc1 := fbl_bv32_mask_bin a (by omega)
            have hoom_ret2 : ∀ (wvecO wstkO : List (BitVec 32)) (wlenO : Nat)
                (wuO : BitVec 64) (wsortO : List (BitVec 32)) (mO : Mem 64),
                let sO : FullState :=
                  { s with
                    core := { s.core with wvec := wvecO, wstk := wstkO,
                                          wlen := wlenO, wusable := wuO }
                    scratch := { s.scratch with wsort := wsortO } }
                sO.LengthsOk c → ModeWatchesInv F_cur sO.core → (FullMem c sO ⋆ R) mO →
                wp Γ Q X
                  (Expr.let_ (op2 (.add i64) (Arg.var c.hdr) (Arg.imm 760)) fun p =>
                    Expr.store (t := i64) (Arg.imm 1) (Arg.var p.fst)
                      (Expr.ret (Arg.imm 2, ()))) mO := by
              intro wvecO wstkO wlenO wuO wsortO mO sO hlenO hwO hmO
              dsimp only [sO] at hlenO hwO hmO
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
                (by assumption)
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
            refine ⟨fun (hok1 : ok1 = true) => ?_, fun (hok1 : ok1 = false) => ?_⟩
            · obtain ⟨_, _, hsz1, hpref1, hw0_1, _⟩ := hok1t hok1
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
              refine ⟨fun (hok2 : ok2 = true) => ?_, fun (hok2 : ok2 = false) => ?_⟩
              · obtain ⟨_, _, hsz2, hpref2, hw0_2, _⟩ := hok2t hok2
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
                fbl_group
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
                  · subst hle; exact (hok2f hok2).1 hb_lt
                  · exact hother2 l hl hle
                c0_call hdel
                refine ⟨c, s2, R, rfl, hlen2, (fun ha => hlay2.bounds a.toNat ha), hm2, ?_⟩
                intro wvec3 wstk3 wu3 m3 s3 hlen3 _ _ _ _ _ _ hw_pres3 hm3
                exact hoom_ret2 wvec3 wstk3 wlen2 wu3 wsort2 m3 hlen3
                  (hw_pres3 F_cur hw2_fail) hm3
            · have hw1_fail : ModeWatchesInv F_cur s1.core := by
                refine fbl_watchPush_fail_preserves_modeWatches hw.watches hlay1 rfl rfl
                  (fun _ r => r) fun l hl => ?_
                by_cases hle : l = a.toNat
                · subst hle; exact (hok1f hok1).1 ha_lt
                · exact hother1 l hl hle
              exact hoom_ret2 wvec1 wstk1 wlen1 wu1 wsort1 m1 hlen1 hw1_fail hm1)
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

end AddBinSection

/-! ## 2. `m5_bce_m4_wp` (`schedEnterDenseSpec`) -/

section BceM5Section

open LeanQbe.T.Examples.Kissat.FullM4VivBce
open FullBveVarTactics FullBveVarHelpers FullVivTopTactics
open scoped FullArenaTactics FullBveVarTactics FullVivTopTactics M4Tactics

/-- `Func.wp` proof for `FullM4VivBce.full_bce_m4_body` directly against
`FullFastSched.schedEnterDenseSpec`. -/
theorem m5_bce_m4_wp (Γ : Env)
    (hEnterDense : ∀ a m Q X, FullFastSched.schedEnterDenseSpec a m Q X →
      Γ "full_enter_dense" [i64] [.bool] a m Q X)
    (hBceVar : ∀ a m Q X, fullBceVarM4Spec a m Q X →
      Γ "full_bce_var_m4" [i64, i32] [] a m Q X)
    (hRebuild : ∀ a m Q X, Full.fullRebuildWatchesSpec a m Q X →
      Γ "full_rebuild_watches" [i64] [i64] a m Q X)
    (hProp : ∀ a m Q X, Full.fullPropagateSpec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullBceM4Spec a m Q X → Func.wp Γ full_bce_m4_body a m Q X := by
  rintro ⟨h, budget, ⟨⟩⟩ m0 Q X ⟨c, F0, s, R, rfl, hsp0, hcl0, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  unfold Func.wp full_bce_m4_body
  fvt_to_group
  · fvt_steps
    exact hQ 1#64 s m0 hsp0 hcl0 (Nat.le_refl _) (Or.inl rfl) (fun h => by cases h) hm0
  · fvt_steps
    exact hQ 1#64 s m0 hsp0 hcl0 (Nat.le_refl _) (Or.inl rfl) (fun h => by cases h) hm0
  · fvt_steps
    c0_call hEnterDense
    refine ⟨c, F0, s, R, rfl, hsp0, hm0, fun ok s1 m1 hcl1 hfl1 hok_t hok_f hm1 => ?_⟩
    fvt_to_group
    · have hdn1 : FullDenseInv c F0 s1 := hok_t (by c0_bound)
      obtain ⟨F_cur1, hdw1⟩ := fullDenseInv_exists_witness hdn1
      have hcv1_le : s1.core.cur_vars ≤ c.max_vars := hdw1.1.core_ok.cur_vars_le
      fvt_steps
      refine wp_loop_inv (ts := [i64, i64])
        (fun (v, done, ()) ml => ∃ sl : FullState,
          FullDenseInvW c F0 F_cur1 sl ∧ sl.core.cur_vars = s1.core.cur_vars ∧
          sl.core.fuel.toNat ≤ s.core.fuel.toNat ∧ v.toNat ≤ s1.core.cur_vars ∧
          (FullMem c sl ⋆ R) ml)
        (fun (v, _, _) _ => s1.core.cur_vars - v.toNat) ?_ ?_
      · intro J hJ; fvt_steps
        exact hJ (0#64, 0#64, ()) m1 ⟨s1, hdw1, rfl, hfl1, Nat.zero_le _, hm1⟩
      · intro J ⟨v, done, ⟨⟩⟩ ml ⟨sl, hinvl, hcvl, hfll, hv_le, hml⟩ ih
        have hv_lt_cv_of : v.toNat < (BitVec.ofNat 64 s1.core.cur_vars).toNat →
            v.toNat < s1.core.cur_vars := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact id
        fvt_to_group
        refine wp_join_group (ts := [])
          (fun () m_ex => ∃ s_ex : FullState,
            FullDenseInvW c F0 F_cur1 s_ex ∧ s_ex.core.fuel.toNat ≤ s.core.fuel.toNat ∧
            (FullMem c s_ex ⋆ R) m_ex) ?_ ?_
        · rintro _ ⟨⟩ m_ex ⟨s_ex, hinv_ex, hfl_ex, hm_ex⟩
          c0_call hRebuild
          refine ⟨c, F0, s_ex, R, rfl, hinv_ex.toDense, hm_ex,
            fun rr s3 m3 hsp3 hcl3 hfl3 _ h20_3 hm3 => ?_⟩
          fvt_steps
          · exact hQ 20#64 s3 m3 hsp3 hcl3 (Nat.le_trans hfl3 hfl_ex) (Or.inr rfl)
              (fun _ => h20_3 (by c0_bound)) hm3
          · exact hQ 20#64 s3 m3 hsp3 hcl3 (Nat.le_trans hfl3 hfl_ex) (Or.inr rfl)
              (fun _ => m4_unsat_of_inconsistent hsp3 (by c0_bound)) hm3
          · obtain ⟨F_cur3, hsw3⟩ := hsp3.exists_witness
            c0_call hProp
            refine ⟨c, F0, F_cur3, s3, R, rfl, hsw3.1, hsw3.2.1, hsw3.2.2.2.2.2, hm3,
              fun pr vals_p flags_p lvl_p rsns_p trl_p tp_p te_p prop_p unass_p unfl_p
                wvec_p arena_p wstk_p wlen_p wu_p fuel_p ctype_p cref_p c0_p c1_p oom_p
                ticks_p wsort_p phases_p m_p hlen_p hw_p _ hperm_p hfl_p _ _ hpr1 _ _
                hm_p => ?_⟩
            let s4 : FullState :=
              { s3 with
                core := { s3.core with
                  vals := vals_p, flags := flags_p, lvl := lvl_p, rsns := rsns_p,
                  trl := trl_p, trail_pos := tp_p, trail_end := te_p, propagated := prop_p,
                  unassigned := unass_p, unflushed := unfl_p, wvec := wvec_p,
                  arena := arena_p, wstk := wstk_p, wlen := wlen_p, wusable := wu_p,
                  fuel := fuel_p, confl_type := ctype_p, confl_ref := cref_p,
                  confl_lit0 := c0_p, confl_lit1 := c1_p, oom := oom_p }
                scratch := { s3.scratch with
                  search_ticks := ticks_p, wsort := wsort_p, phases := phases_p } }
            have hsw4 : FullSparseInvW c F0 F_cur3 s4 :=
              m4_sparseInvW_of_prop_canon hsw3 hlen_p hw_p hperm_p
            have hfl4 : s4.core.fuel.toNat ≤ s.core.fuel.toNat :=
              Nat.le_trans hfl_p (Nat.le_trans hfl3 hfl_ex)
            fvt_steps
            all_goals first
              | exact hQ 1#64 s4 m_p hsw4.toSparse hcl3 hfl4 (Or.inl rfl)
                  (fun h => by cases h) hm_p
              | exact hQ 20#64 s4 m_p hsw4.toSparse hcl3 hfl4 (Or.inr rfl)
                  (fun _ => FullVivTopSpecs.level0_unsat_of_conflict_okW hw_p hcl3
                    (hpr1 (by c0_bound)).2.2) hm_p
        · intro Jex hJex
          fvt_to_group
          · have hv_lt : v.toNat < s1.core.cur_vars := hv_lt_cv_of (by c0_bound)
            have hv_fl : v.toNat < sl.core.flags.length := by
              rw [hinvl.1.core_ok.flags_len]; omega
            have hv2_lt : (v <<< (BitVec.toNat (1 : BitVec 64) % 64)).toNat <
                sl.core.vals.length := by
              rw [show BitVec.toNat (1 : BitVec 64) % 64 = 1 from rfl, BitVec.toNat_shiftLeft,
                Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega), hinvl.1.core_ok.vals_len]
              omega
            have hv1 : (v + 1#64).toNat = v.toNat + 1 := by bv_omega
            refine wp_join_group (ts := [i64])
              (fun (done', ()) mj => ∃ sj : FullState,
                FullDenseInvW c F0 F_cur1 sj ∧ sj.core.cur_vars = s1.core.cur_vars ∧
                sj.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c sj ⋆ R) mj) ?_ ?_
            · rintro _ ⟨done', ⟨⟩⟩ mj ⟨sj, hinvj, hcvj, hflj, hmj⟩
              fvt_steps
              exact ih (v + 1#64, done', ()) mj (by dsimp only; omega)
                ⟨sj, hinvj, hcvj, hflj, by omega, hmj⟩
            · intro Jv hJv
              fvt_steps
              · c0_call hBceVar
                refine ⟨c, F0, F_cur1, sl, R, rfl, hinvl,
                  by rw [bv64_toNat_setWidth32_lt (by omega), hcvl]; exact hv_lt, hml,
                  fun sv mv hinvv hcvv hflv hmv =>
                    hJv (done + 1#64, ()) mv ⟨sv, hinvv, hcvv.trans hcvl,
                      by rw [hflv]; exact hfll, hmv⟩⟩
              · exact hJv (done, ()) ml ⟨sl, hinvl, hcvl, hfll, hml⟩
              · exact hJv (done, ()) ml ⟨sl, hinvl, hcvl, hfll, hml⟩
          all_goals exact hJex () ml ⟨sl, hinvl, hfll, hml⟩
    · have hsp1 : FullSparseInv c F0 s1 := hok_f (by c0_bound)
      fvt_steps
      · exact hQ 20#64 s1 m1 hsp1 hcl1 hfl1 (Or.inr rfl)
          (fun _ => m4_unsat_of_inconsistent hsp1 (by c0_bound)) hm1
      · exact hQ 1#64 s1 m1 hsp1 hcl1 hfl1 (Or.inl rfl)
          (fun h => by cases h) hm1

end BceM5Section

/-! ## 3. Cross-Slice Bridges, `m5_search_m5_wp`, & Forwarders -/

section BridgesAndSearch

open scoped FullArenaTactics

theorem m5_extend_push_cl_adapter {Γ : Env}
    (h : ∀ xs m Q X, FullFastBveBudgets.fullExtendPushClTmkSpec xs m Q X →
      Γ "full_extend_push_cl" [i64, i32, i32] [.bool] xs m Q X) :
    ∀ xs m Q X, Full.fullExtendPushClSpec xs m Q X →
      Γ "full_extend_push_cl" [i64, i32, i32] [.bool] xs m Q X := by
  rintro ⟨h_ptr, blk, cref, ⟨⟩⟩ m Q X ⟨c, s, R, hpre, hlen, hm, hQ⟩
  exact h _ m Q X ⟨c, s, R, hpre, hlen, hm,
    fun r s' m' hcore hlen' ⟨h1, h2, h3, _⟩ hm' => hQ r s' m' hcore hlen' ⟨h1, h2, h3⟩ hm'⟩

theorem m5_add_bin_cong_adapter {Γ : Env}
    (h : ∀ xs m Q X, fullAddBinSpec xs m Q X → Γ "full_add_bin" [i64, i32, i32] [i64] xs m Q X) :
    ∀ xs m Q X, FullCongSpecs.fullAddBinSpec xs m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] xs m Q X := by
  rintro ⟨h_ptr, a, b, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hcl0, _, _, hent, hm, hQ⟩
  refine h _ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hcl0, (fun _ _ => hent), hm, ?_⟩
  intro r vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' wlen' wu' nb' oom' inc'
    phases' wsort' m' s' hlen' hw' _ hr20 _ hm'
  exact hQ r _ m' hlen' hw' hcl0 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (fun h20 => (hr20 h20).2) hm'

theorem m5_init_state_m5_wp (Γ : Env)
    (hHdr : ∀ a m Q X, Kissat.kissatParseHeaderSpec a m Q X →
      Γ "kissat_parse_header" [i64, i64, i64] [.bool] a m Q X)
    (hFixed : ∀ a m Q X, fullFixedBytesSpec a m Q X →
      Γ "full_fixed_bytes" [i64] [i64] a m Q X)
    (hMaxV : ∀ a m Q X, fullCalcMaxVSpec a m Q X →
      Γ "full_calc_max_v" [i64, i64, i64, i64] [i64] a m Q X)
    (hExt : ∀ a m Q X, FullM5Orch.fullCalcExtCapM5Spec a m Q X →
      Γ "full_calc_ext_cap_m5" [i64] [i64] a m Q X)
    (hScr : ∀ a m Q X, FullM5Orch.fullCalcScrCapM5Spec a m Q X →
      Γ "full_calc_scr_cap_m5" [i64] [i64] a m Q X)
    (hArenas : ∀ a m Q X, fullInitArenasSpec a m Q X →
      Γ "full_init_arenas" [i64, i64, i64, i64] [] a m Q X)
    (hInitHdr : ∀ a m Q X, FullFastBveBudgets.fullFastInitHdrSpec a m Q X →
      Γ "full_init_hdr" [i64, i64, i64, i64] [] a m Q X)
    (hZt1 : ∀ a m Q X, fullZeroTables1Spec a m Q X →
      Γ "full_zero_tables1" [i64] [] a m Q X)
    (hZt2 : ∀ a m Q X, fullZeroTables2Spec a m Q X →
      Γ "full_zero_tables2" [i64] [] a m Q X) :
    ∀ a m Q X, fullInitStateSpec a m Q X →
      Func.wp Γ FullM5Orch.full_init_state_m5_body a m Q X :=
  FullM5Orch.full_init_state_m5_wp Γ hHdr hFixed hMaxV hExt hScr hArenas
    (fun _ _ _ _ h => hInitHdr _ _ _ _ (FullFastBveBudgets.fullFastInitHdrSpec_of_canon h))
    hZt1 hZt2

theorem m5_find_definition_wp (Γ : Env)
    (hInit : ∀ a m Q X, fullKittenInitSpec a m Q X →
      Γ "full_kitten_init" [i64, i32, i32] [] a m Q X)
    (hAddCl : ∀ a m Q X, fullKittenAddClauseSpec a m Q X →
      Γ "full_kitten_add_clause_m5" [i64, i32, i64, i32] [.bool] a m Q X)
    (hSolve : ∀ a m Q X, fullKittenSolveSpec a m Q X →
      Γ "full_kitten_solve_m5" [i64, i64] [i64] a m Q X)
    (hCore : ∀ a m Q X, fullKittenCoreSpec a m Q X →
      Γ "full_kitten_core_m5" [i64] [i32] a m Q X)
    (hShrink : ∀ a m Q X, fullKittenShrinkSpec a m Q X →
      Γ "full_kitten_shrink" [i64] [] a m Q X) :
    ∀ a m Q X, FullDefSweep.fullFindDefinitionSpec a m Q X →
      Func.wp Γ FullM5KittenDefFix.full_find_definition_m5_body a m Q X := by
  have hAddA : ∀ a m Q X, FullDefSweep.fullKittenAddClauseSpec FullFast.fastKInv a m Q X →
      Γ "full_kitten_add_clause_m5" [i64, i32, i64, i32] [.bool] a m Q X := by
    let Γ' : Env := fun f as bs =>
      if f == "full_kitten_add_clause" then Γ "full_kitten_add_clause_m5" as bs else Γ f as bs
    exact FullFast.fast_kitten_add_clause_adapter (Γ := Γ') hAddCl
  have hSolvA : ∀ a m Q X, FullDefSweep.fullKittenSolveSpec FullFast.fastKInv a m Q X →
      Γ "full_kitten_solve_m5" [i64, i64] [i64] a m Q X := by
    let Γ' : Env := fun f as bs =>
      if f == "full_kitten_solve" then Γ "full_kitten_solve_m5" as bs else Γ f as bs
    exact FullFast.fast_kitten_solve_adapter (Γ := Γ') hSolve
  have hCoreA : ∀ a m Q X, FullDefSweep.fullKittenCoreSpec FullFast.fastKInv a m Q X →
      Γ "full_kitten_core_m5" [i64] [i32] a m Q X := by
    let Γ' : Env := fun f as bs =>
      if f == "full_kitten_core" then Γ "full_kitten_core_m5" as bs else Γ f as bs
    exact FullFast.fast_kitten_core_adapter (Γ := Γ') hCore
  exact FullM5KittenDefFix.full_find_definition_m5_wp Γ FullM5KittenDefFix.fastKInv_laws_m5
    (FullFast.fast_kitten_init_adapter hInit) hAddA hSolvA hCoreA
    (FullFast.fast_kitten_shrink_adapter hShrink)

private def m5SearchVariant (st : FullState) : Nat :=
  2 * st.core.fuel.toNat + if st.core.propagated = st.core.trail_end then 1 else 0

private theorem m5_sparseInv_of_same_arena {c : FullCfg} {F0 : CNF Nat} {s s' : FullState}
    (h : FullSparseInv c F0 s) (hcore' : FullCoreInv c F0 s')
    (hmrk : s'.core.mrk = s.core.mrk) (hlm : s'.core.lit_mark = s.core.lit_mark)
    (har : s'.core.arena = s.core.arena) (hal : s'.core.arena_len = s.core.arena_len)
    (hdm : s'.core.dense_mode = s.core.dense_mode)
    (hpres : FullExtScratchPres s s') : FullSparseInv c F0 s' := by
  refine ⟨hcore', ?_, ?_, ?_, hdm.trans h.2.2.2.2⟩
  · exact ⟨fun v hv => by rw [hmrk]; exact h.2.1.1 v hv,
      fun l hl => by rw [hlm]; exact h.2.1.2 l hl⟩
  · intro ref href hng
    have hrefs : fullArenaClauseRefs s' = fullArenaClauseRefs s := by
      unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [har, hal]
    have hgb : fullArenaClauseGarb s' ref = fullArenaClauseGarb s ref := by
      unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore; rw [har]
    have hlits : fullArenaClauseLits s' ref = fullArenaClauseLits s ref := by
      unfold fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore; rw [har]
    rw [hrefs] at href; rw [hgb] at hng; rw [hlits]; exact h.2.2.1 ref href hng
  · exact h.2.2.2.1.of_pres hpres fun ref href => by
      change ref ∈ fullArenaClauseRefsCore s'.core
      unfold fullArenaClauseRefsCore; rw [har, hal]; exact href

private theorem m5_sparseInvW_of_perm {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} (h : FullSparseInvW c F0 F_cur s) (hlen' : s'.LengthsOk c)
    (hw' : FullWitnessInv c F0 F_cur s'.core) (hperm : FullArenaPermEq s.core s'.core)
    (hmrk : s'.core.mrk = s.core.mrk) (hlm : s'.core.lit_mark = s.core.lit_mark)
    (hdm : s'.core.dense_mode = s.core.dense_mode)
    (hpres : FullExtScratchPres s s') : FullSparseInvW c F0 F_cur s' := by
  refine ⟨hlen', hw', ?_, ?_, ?_, hdm.trans h.2.2.2.2.2⟩
  · exact ⟨fun v hv => by rw [hmrk]; exact h.2.2.1.1 v hv,
      fun l hl => by rw [hlm]; exact h.2.2.1.2 l hl⟩
  · intro ref href hng
    have href0 : ref ∈ fullArenaClauseRefsCore s.core := hperm.2.1 ▸ href
    obtain ⟨_, hgb, hp⟩ := hperm.2.2 ref href0
    exact (hp.map (· / 2)).nodup_iff.mpr (h.2.2.2.1 ref href0 (hgb.symm.trans hng))
  · exact h.2.2.2.2.1.of_pres hpres fun ref href => by
      change ref ∈ fullArenaClauseRefsCore s'.core; rw [hperm.2.1]; exact href

/-- Unified M5 `full_search_m5` proof against `FullM4.m4SearchSpec` directly under
`FullM5Sched.m5RephaseSpec`. -/
theorem m5_search_m5_wp (Γ : Env)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hAna : ∀ a m Q X, fullAnalyzeSpec a m Q X → Γ "full_analyze" [i64] [i64] a m Q X)
    (hRed : ∀ a m Q X, fullReduceSpec a m Q X → Γ "full_reduce_m5" [i64, .bool] [i64] a m Q X)
    (hSw : ∀ a m Q X, fullSwitchModeSpec a m Q X → Γ "full_switch_mode" [i64] [] a m Q X)
    (hRdue : ∀ a m Q X, fullRestartDueSpec a m Q X → Γ "full_restart_due" [i64] [i64] a m Q X)
    (hRst : ∀ a m Q X, fullRestartSpec a m Q X → Γ "full_restart" [i64] [] a m Q X)
    (hReord : ∀ a m Q X, FullM4.m4ReorderSpec a m Q X →
      Γ "full_reorder_m5" [i64, i64] [i64] a m Q X)
    (hReph : ∀ a m Q X, FullM5Sched.m5RephaseSpec a m Q X →
      Γ "full_rephase" [i64] [] a m Q X)
    (hSimp : ∀ a m Q X, FullM4.m4SimplifySpec a m Q X →
      Γ "full_simplify_m5" [i64, .bool, .bool] [i64] a m Q X)
    (hDec : ∀ a m Q X, fullDecideSpec a m Q X → Γ "full_decide" [i64] [i64] a m Q X) :
    ∀ a m Q X, FullM4.m4SearchSpec a m Q X →
      Func.wp Γ FullM5Orch.full_search_m5_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hcl0, hm, hQ⟩
  unfold Func.wp FullM5Orch.full_search_m5_body
  c0_hsteps_nogrp
  refine wp_while_state1 (α := BitVec 64 × FullCfg × FullState) Prod.fst
    (fun p => m5SearchVariant p.2.2)
    (fun ⟨_, cc, st⟩ ml =>
      FullM4Compact.FullCfgCompat c cc ∧ FullSparseInv cc F0 st ∧ (FullMem cc st ⋆ R) ml)
    (fun _ hL => by
      c0_hsteps; exact hL (10000#64, c, s) m ⟨FullM4Compact.FullCfgCompat.refl c, hinv, hm⟩)
    (fun _ ⟨rlim, cc, st⟩ ml ⟨hcc, hst, hml⟩ ih => ?_)
  have hch_cc : cc.hdr = c.hdr := hcc.hdr
  rw [← hch_cc]
  c0_hsplit
  rotate_left; · cases hc
  c0_hsteps
  · exact hQ 0#64 cc st ml hcc hst.lengths (Or.inl rfl)
      (fun h => by cases h) (fun h => by cases h) hml
  · exact hQ 0#64 cc st ml hcc hst.lengths (Or.inl rfl)
      (fun h => by cases h) (fun h => by cases h) hml
  obtain ⟨F_cur, hspW⟩ := hst.exists_witness
  c0_call hProp; refine ⟨cc, F0, F_cur, st, R, rfl, hspW.1, hspW.2.1, hspW.2.2.2.2.2, hml, ?_⟩
  intro pr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 s3
    hlen3 hw3 _ hperm3 hfu3 hpr_dom hpr0 hpr1 _ _ hm3
  have hspW3 : FullSparseInvW cc F0 F_cur s3 :=
    m5_sparseInvW_of_perm hspW hlen3 hw3 hperm3 rfl rfl rfl ⟨rfl, rfl⟩
  c0_hsteps
  · exact hQ 0#64 cc s3 m3 hcc hlen3 (Or.inl rfl)
      (fun h => by cases h) (fun h => by cases h) hm3
  · obtain ⟨hfu3_lt, _, hconf3⟩ := hpr1 hc
    c0_call hAna; refine ⟨cc, F0, F_cur, s3, R, rfl, hspW3, hconf3, hm3, ?_⟩
    intro ast s4 m4 hlen4 _ _ hfu4 _ hua4 _ hsp4 hm4
    c0_hsteps_nogrp
    · exact hQ 20#64 cc s4 m4 hcc hlen4 (Or.inr (Or.inr rfl))
        (fun _ => hua4 hc) (fun h => by cases h) hm4
    · exact hQ 0#64 cc s4 m4 hcc hlen4 (Or.inl rfl)
        (fun h => by cases h) (fun h => by cases h) hm4
    have hspW4 : FullSparseInvW cc F0 F_cur s4 := (hsp4 hc).1
    have hinv4 : FullSparseInv cc F0 s4 := hspW4.toSparse
    have hfu4_lt : s4.core.fuel.toNat < st.core.fuel.toNat := by dsimp only [s3] at hfu4; omega
    let ContInv : BitVec 64 × FullCfg × FullState → Mem 64 → Prop :=
      fun ⟨_, c8, s8⟩ m8 => FullM4Compact.FullCfgCompat c c8 ∧ FullSparseInv c8 F0 s8 ∧
        s8.core.fuel.toNat < st.core.fuel.toNat ∧ (FullMem c8 s8 ⋆ R) m8
    let ContInv0 : FullCfg × FullState → Mem 64 → Prop :=
      fun ⟨c8, s8⟩ m8 => ContInv (rlim, c8, s8) m8
    refine wp_join_state_pure (ts := [i32]) (α := BitVec 32)
      (fun v => (v, ())) (fun _ => True) ?_ ?_
    · intro _ mode_due _
      c0_hsteps_nogrp
      refine wp_join_state1 (α := BitVec 64 × FullCfg × FullState) Prod.fst ContInv ?_ ?_
      · intro _ ⟨r8, c8, s8⟩ m8 ⟨hc8, hinv8, _, hm8⟩
        c0_hsteps
        have hv_lt : m5SearchVariant s8 < m5SearchVariant st := by
          unfold m5SearchVariant; split <;> split <;> omega
        exact ih (r8, c8, s8) m8 hv_lt ⟨hc8, hinv8, hm8⟩
      · intro Jr1 hJr1
        c0_hsplit
        · c0_hsteps; c0_call hRed
          refine ⟨cc, F0, F_cur, s4, R, rfl, hspW4, hm4, ?_⟩
          intro rr s5 m5 hsp5 hrr_dom _ hfu5 _ _ _ _ hur5 _ _ hm5
          c0_hsteps
          · exact hQ 20#64 cc s5 m5 hcc hsp5.1 (Or.inr (Or.inr rfl))
              (fun _ => hur5 hc) (fun h => by cases h) hm5
          · exact hQ 0#64 cc s5 m5 hcc hsp5.1 (Or.inl rfl)
              (fun h => by cases h) (fun h => by cases h) hm5
          exact hJr1 (rlim, cc, s5) m5 ⟨hcc, hsp5.toSparse, by omega, hm5⟩
        · refine wp_join_state1 (α := BitVec 64 × FullCfg × FullState) Prod.fst ContInv ?_ ?_
          · intro _ p mp hp; c0_hsteps; exact hJr1 p mp hp
          · intro Jr2 hJr2
            c0_hsplit
            · c0_hsteps; c0_call hSw; refine ⟨cc, s4, R, rfl, hinv4.lengths, hm4, ?_⟩
              intro ⟨⟩ s5 m5 hcore5 hlen5 hpres5 hm5
              dsimp only [fullSafetySlice, SafetySlice.ofMask] at hm5
              have hinv5 : FullSparseInv cc F0 s5 := hinv4.of_safetySlice hlen5 hcore5 hpres5.1
              have hfu5 : s5.core.fuel.toNat < st.core.fuel.toNat := by
                have heq : s5.core = s4.core := fullCoreState_agrees_with_scratch hcore5
                rw [heq]; exact hfu4_lt
              c0_hsteps; exact hJr2 (rlim, cc, s5) m5 ⟨hcc, hinv5, hfu5, hm5⟩
            · refine wp_join_state1 (α := BitVec 64 × FullCfg × FullState) Prod.fst ContInv ?_ ?_
              · intro _ p mp hp; c0_hsteps; exact hJr2 p mp hp
              · intro Jr3 hJr3
                c0_hsteps; c0_call hRdue; refine ⟨cc, s4, R, rfl, hinv4.lengths, hm4, ?_⟩
                intro ⟨rd, ⟨⟩⟩ s4r m4r hcore4r hlen4r ⟨_, hpres4r⟩ hm4r
                dsimp only [fullSafetySlice, SafetySlice.ofMask] at hm4r
                have hinv4r : FullSparseInv cc F0 s4r :=
                  hinv4.of_safetySlice hlen4r hcore4r hpres4r
                have hfu4r : s4r.core.fuel.toNat < st.core.fuel.toNat := by
                  have heq : s4r.core = s4.core := fullCoreState_agrees_with_scratch hcore4r
                  rw [heq]; exact hfu4_lt
                c0_hsplit
                · c0_hsteps; c0_call hRst
                  refine ⟨cc, F0, s4r, R, rfl, hinv4r.1, hm4r, ?_⟩
                  intro _ _ _ _ _ _ _ _ _ _ m5 s5 hcore5 _ hpres5 hm5
                  have hinv5 : FullSparseInv cc F0 s5 :=
                    m5_sparseInv_of_same_arena hinv4r hcore5 rfl rfl rfl rfl rfl hpres5
                  c0_hsteps; exact hJr3 (rlim, cc, s5) m5 ⟨hcc, hinv5, hfu4r, hm5⟩
                · refine wp_join_state1 (α := BitVec 64 × FullCfg × FullState)
                    Prod.fst ContInv ?_ ?_
                  · intro _ p mp hp; c0_hsteps; exact hJr3 p mp hp
                  · intro Jr4 hJr4
                    c0_hsplit
                    · c0_hsteps; c0_call hReord
                      refine ⟨cc, F0, s4r, R, rfl, hinv4r, hm4r, ?_⟩
                      intro _ s5 m5 hinv5 _ _ hfu5 hm5
                      c0_hsteps
                      exact hJr4 (s4r.scratch.conflicts + 10000#64, cc, s5) m5
                        ⟨hcc, hinv5, by rw [hfu5]; exact hfu4r, hm5⟩
                    · refine wp_join_state0 ContInv0 ?_ ?_
                      · intro _ ⟨c8, s8⟩ m8 h8; c0_hsteps; exact hJr4 (rlim, c8, s8) m8 h8
                      · intro Jr5 hJr5
                        c0_hsplit
                        · c0_hsteps; c0_call hReph
                          refine ⟨cc, F0, s4r, R, rfl, hinv4r.1, hm4r, ?_⟩
                          intro _ _ _ _ _ _ _ cl5 _ _ _ m5 s5 hcore5 _ _ hfu5 hpres5 hm5
                          have hinv5 : FullSparseInv cc F0 s5 :=
                            m5_sparseInv_of_same_arena hinv4r hcore5 rfl rfl rfl rfl rfl hpres5
                          c0_hsteps
                          exact hJr5 (cc, s5) m5
                            ⟨hcc, hinv5, by dsimp only [s5] at hfu5 ⊢; omega, hm5⟩
                        · refine wp_join_state0 ContInv0 ?_ ?_
                          · intro _ p mp hp; c0_hsteps; exact hJr5 p mp hp
                          · intro Jr6 hJr6
                            c0_hsplit
                            · c0_hsteps; c0_call hSimp
                              refine ⟨cc, F0, s4r, R, rfl, hinv4r, hm4r, ?_⟩
                              intro sr c5 s5 m5 hcomp5 hlen5 hfu5 _ hus5 hsp5 hm5
                              have hc5 := hcc.trans hcomp5
                              c0_hsteps
                              · exact hQ 20#64 c5 s5 m5 hc5 hlen5 (Or.inr (Or.inr rfl))
                                  (fun _ => hus5 hc) (fun h => by cases h) hm5
                              · exact hQ 0#64 c5 s5 m5 hc5 hlen5 (Or.inl rfl)
                                  (fun h => by cases h) (fun h => by cases h) hm5
                              exact hJr6 (c5, s5) m5 ⟨hc5, (hsp5 hc).1, by omega, hm5⟩
                            · c0_hsteps
                              · c0_call hSimp
                                refine ⟨cc, F0, s4r, R, rfl, hinv4r, hm4r, ?_⟩
                                intro sr c5 s5 m5 hcomp5 hlen5 hfu5 _ hus5 hsp5 hm5
                                have hc5 := hcc.trans hcomp5
                                c0_hsteps
                                · exact hQ 20#64 c5 s5 m5 hc5 hlen5 (Or.inr (Or.inr rfl))
                                    (fun _ => hus5 hc) (fun h => by cases h) hm5
                                · exact hQ 0#64 c5 s5 m5 hc5 hlen5 (Or.inl rfl)
                                    (fun h => by cases h) (fun h => by cases h) hm5
                                exact hJr6 (c5, s5) m5 ⟨hc5, (hsp5 hc).1, by omega, hm5⟩
                              · exact hJr6 (cc, s4r) m4r ⟨hcc, hinv4r, hfu4r, hm4r⟩
    · intro _ hJmd; c0_hsteps <;> exact hJmd _ trivial
  · exact hQ 10#64 cc s3 m3 hcc hlen3 (Or.inr (Or.inl rfl)) (fun h => by cases h)
      (fun _ => hspW3.2.2.2.2.1.2) hm3
  · have hpr_eq0 : pr = 0#64 := by
      rcases hpr_dom with h0 | h1 | h2
      · exact h0
      · exact absurd h1 (by assumption)
      · exact absurd h2 (by assumption)
    obtain ⟨hprop3, _, hfu3_lt_if⟩ := hpr0 hpr_eq0
    have hinv3 : FullSparseInv cc F0 s3 := hspW3.toSparse
    c0_call hDec; refine ⟨cc, F0, s3, R, rfl, hinv3.1, hm3, ?_⟩
    intro dr _ _ _ _ _ _ _ _ _ _ _ _ _ m4 s4 hcore4 hpres4 hdr_dom _ hd1 hm4
    have hinv4 : FullSparseInv cc F0 s4 :=
      m5_sparseInv_of_same_arena hinv3 hcore4 rfl rfl rfl rfl rfl hpres4
    c0_hsteps
    · exact hQ 10#64 cc s4 m4 hcc hinv4.lengths (Or.inr (Or.inl rfl)) (fun h => by cases h)
        (fun _ => hinv4.2.2.2.1.2) hm4
    · exact hQ 0#64 cc s4 m4 hcc hinv4.lengths (Or.inl rfl) (fun h => by cases h)
        (fun h => by cases h) hm4
    · have hdr1 : dr = 1#64 := hdr_dom.resolve_left hc
      have hte4 : s4.core.trail_end = s3.core.trail_end + 1 := (hd1 hdr1).2
      have hv_lt : m5SearchVariant s4 < m5SearchVariant st := by
        have hfu3' : s3.core.fuel.toNat ≤ st.core.fuel.toNat := hfu3
        have hprop3' : s3.core.propagated = s3.core.trail_end := hprop3
        have hne4 : s4.core.propagated ≠ s4.core.trail_end := by
          change s3.core.propagated ≠ s4.core.trail_end; omega
        have hle_st := hst.lengths.core_ok.propagated_le
        have hfu4 : s4.core.fuel = s3.core.fuel := rfl
        unfold m5SearchVariant
        simp only [hne4, ↓reduceIte, Nat.add_zero, hfu4]
        by_cases heq_st : st.core.propagated = st.core.trail_end
        · simp only [heq_st, ↓reduceIte]; omega
        · simp only [heq_st, ↓reduceIte, Nat.add_zero]
          have hlt_f : s3.core.fuel.toNat < st.core.fuel.toNat := hfu3_lt_if (by omega)
          omega
      exact ih (rlim, cc, s4) m4 hv_lt ⟨hcc, hinv4, hm4⟩

theorem m5_init_state_fwd_wp (Γ : Env)
    (h : ∀ a m Q X, fullInitStateSpec a m Q X →
      Γ "full_init_state_m5" [i64, i64, i64, i64, i64] [.bool] a m Q X) :
    ∀ a m Q X, fullInitStateSpec a m Q X → Func.wp Γ full_init_state_body a m Q X := by
  intro a m Q X hs; unfold Func.wp full_init_state_body
  c0_hsteps; c0_call h; exact hs

theorem m5_reduce_fwd_wp (Γ : Env)
    (h : ∀ a m Q X, fullReduceSpec a m Q X → Γ "full_reduce_m5" [i64, .bool] [i64] a m Q X) :
    ∀ a m Q X, fullReduceSpec a m Q X → Func.wp Γ full_reduce_body a m Q X := by
  intro a m Q X hs; unfold Func.wp full_reduce_body
  c0_hsteps; c0_call h; exact hs

theorem m5_preprocess_fwd_wp (Γ : Env)
    (h : ∀ a m Q X, FullM4.m4PreprocessSpec a m Q X →
      Γ "full_preprocess_m5" [i64] [i64] a m Q X) :
    ∀ a m Q X, FullM4.m4PreprocessSpec a m Q X → Func.wp Γ full_preprocess_body a m Q X := by
  intro a m Q X hs; unfold Func.wp full_preprocess_body
  c0_hsteps; c0_call h; exact hs

theorem m5_search_fwd_wp (Γ : Env)
    (h : ∀ a m Q X, FullM4.m4SearchSpec a m Q X → Γ "full_search_m5" [i64] [i64] a m Q X) :
    ∀ a m Q X, FullM4.m4SearchSpec a m Q X → Func.wp Γ full_search_body a m Q X := by
  intro a m Q X hs; unfold Func.wp full_search_body
  c0_hsteps; c0_call h; exact hs

theorem m5_solve_bytes_fwd_wp (Γ : Env) {S : Spec [i64, i64, i64, i64, i64] [i64]}
    (h : ∀ a m Q X, S a m Q X → Γ "kissat_solve_bytes_m5" [i64, i64, i64, i64, i64] [i64] a m Q X) :
    ∀ a m Q X, S a m Q X → Func.wp Γ kissat_solve_bytes_body a m Q X := by
  intro a m Q X hs; unfold Func.wp kissat_solve_bytes_body
  c0_hsteps; c0_call h; exact hs

end BridgesAndSearch

end LeanQbe.T.Examples.Kissat.FullM5
