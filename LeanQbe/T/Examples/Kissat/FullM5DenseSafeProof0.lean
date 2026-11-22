module

public import LeanQbe.T.Examples.Kissat.FullM5DenseSafe
public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Examples.Kissat.FullFastSchedLemmas
import LeanQbe.T.Examples.Kissat.FullSubstLemmas2
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1
import LeanQbe.T.Examples.Kissat.FullReduceLemmas2
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.C0Agrees

/-!
# Kissat M5 Dense-Safe Proofs — Part 0 (`enter_dense`, `substitute`, `subst_rewrite_{bins,ar}`)

Parametric `(Γ : Env)` `Func.wp` UNSAT-only proofs against exact canonical contracts:
1. `full_enter_dense_m5_wp` (`FullFastSched.schedEnterDenseSpec`): preserves pre-existing
   `h->oom != 0ULL` without wiping it; only clears `h->oom = 0ULL` on local dense watch-push
   failure before any clause mutation.
2. `full_substitute_m5_wp` (`Full.fullSubstituteSpec`): aborts immediately before
   `full_propagate`/`full_arena_sweep` whenever `h->oom != 0ULL`.
3. `full_subst_rewrite_bins_m5_wp` (`Full.fullSubstRewriteBinsSpec`): deduplicates rewritten
   binaries via `lit_mark` bit 1, sets `h->oom = 1ULL` and aborts cleanly on overflow or
   `full_add_bin == 2ULL`, keeping `return false` strictly for `F0.Unsat`.
4. `full_subst_rewrite_ar_m5_wp` (`Full.fullSubstRewriteArSpec`): aborts cleanly with
   `h->oom = 1ULL` on `full_add_bin == 2ULL` while keeping `return false` strictly for `F0.Unsat`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullM5DenseSafe

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullSubstHelpers
open LeanQbe.T.Examples.Kissat.Full.FullDenseWatchHelpers
open LeanQbe.T.Examples.Kissat.Full.FullReduceHelpers
open Kraken.Bedrock2.Test
open scoped FullArenaTactics FullSubstTactics

/-! ## 1. Shared Sparse/Witness Transition Helpers -/

section Helpers

private theorem fullSparseInvW_with_oom {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s) (oom' : BitVec 64) :
    FullSparseInvW c F0 F_cur { s with core := { s.core with oom := oom' } } :=
  ⟨⟨{ hsp.1.core_ok with vals_len := hsp.1.core_ok.vals_len }, hsp.1.scratch_ok⟩,
    fullWitnessInv_with_oom hsp.2.1 oom',
    hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩

private theorem fullWitnessInv_with_inc {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k)
    (hu : (cnfOfClauses F_cur).Unsat) (inc' : BitVec 64) :
    FullWitnessInv c F0 F_cur { k with inconsistent := inc' } :=
  { hw with
    inconsistent_sound := fun _ => hu
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }

private theorem fullSparseInvW_with_inc {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    (hu : (cnfOfClauses F_cur).Unsat) (inc' : BitVec 64) :
    FullSparseInvW c F0 F_cur { s with core := { s.core with inconsistent := inc' } } :=
  ⟨⟨{ hsp.1.core_ok with vals_len := hsp.1.core_ok.vals_len }, hsp.1.scratch_ok⟩,
    fullWitnessInv_with_inc hsp.2.1 hu inc',
    hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩

private theorem bv8_trunc_or1 (x : BitVec 8) :
    BitVec.setWidth 8 (BitVec.setWidth 32 x ||| 1#32) = x ||| 1#8 := by revert x; decide

private theorem bv8_trunc_or2 (x : BitVec 8) :
    BitVec.setWidth 8 (BitVec.setWidth 32 x ||| 2#32) = x ||| 2#8 := by revert x; decide

private theorem level0_fcur_unsat_of_confl {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core)
    (hl0 : s.core.cur_level = 0) (hc : FullConflictOkW F_cur s) :
    (cnfOfClauses F_cur).Unsat := by
  rcases hc with ⟨_, h0lt, h1lt, hf0, hf1, hent⟩ | ⟨_, href, hng, hfals⟩
  · refine unsat_of_entails_nil (entails_of_mem_or_false hent fun l hl => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    right; rcases hl with rfl | rfl
    · obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff _ h0lt).mp hf0
      have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega)
      rwa [heq] at hs
    · obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff _ h1lt).mp hf1
      have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega)
      rwa [heq] at hs
  · refine unsat_of_entails_nil
      (entails_of_mem_or_false (hw.arena.entails _ href hng) fun l hl => ?_)
    right
    have hlt := hw.arena.lits_lt _ href hng l hl
    obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff l hlt).mp (hfals l hl)
    have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega)
    rwa [heq] at hs

private theorem level0_unsat_of_confl {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core)
    (hl0 : s.core.cur_level = 0) (hc : FullConflictOkW F_cur s) : F0.Unsat :=
  hw.ext_sound.2 (level0_fcur_unsat_of_confl hw hl0 hc)

private theorem fullSparseInvW_after_bt0 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s' : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    (hlen' : s'.LengthsOk c) (hw' : FullWitnessInv c F0 F_cur s'.core)
    (hpres : FullExtScratchPres s s') (hmrk : s'.core.mrk = s.core.mrk)
    (hlm : s'.core.lit_mark = s.core.lit_mark) (har : s'.core.arena = s.core.arena)
    (hal : s'.core.arena_len = s.core.arena_len) (hdm : s'.core.dense_mode = s.core.dense_mode) :
    FullSparseInvW c F0 F_cur s' := by
  refine ⟨hlen', hw',
    ⟨fun v hv => by rw [hmrk]; exact hsp.2.2.1.1 v hv,
     fun l hl => by rw [hlm]; exact hsp.2.2.1.2 l hl⟩, ?_, ?_, hdm.trans hsp.2.2.2.2.2⟩
  · intro r hr hng
    have hr0 : r ∈ fullArenaClauseRefsCore s.core := by
      change r ∈ fullArenaClauseRefsCore s'.core at hr
      unfold fullArenaClauseRefsCore at hr ⊢; rw [har, hal] at hr; exact hr
    have hng0 : fullArenaClauseGarb s r = false := by
      unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore at hng ⊢
      rwa [har] at hng
    have hl : fullArenaClauseLits s' r = fullArenaClauseLits s r := by
      unfold fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore; rw [har]
    rw [hl]; exact hsp.2.2.2.1 r hr0 hng0
  · exact hsp.2.2.2.2.1.of_pres hpres fun ref href => by
      change ref ∈ fullArenaClauseRefsCore s'.core
      unfold fullArenaClauseRefsCore; rw [har, hal]; exact href

private theorem fullSparseInvW_of_perm {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s' : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    (hlen' : s'.LengthsOk c) (hw' : FullWitnessInv c F0 F_cur s'.core)
    (hperm : FullArenaPermEq s.core s'.core) (hmrk : s'.core.mrk = s.core.mrk)
    (hlm : s'.core.lit_mark = s.core.lit_mark) (hdm : s'.core.dense_mode = s.core.dense_mode)
    (hpres : FullExtScratchPres s s') : FullSparseInvW c F0 F_cur s' := by
  refine ⟨hlen', hw',
    ⟨fun v hv => by rw [hmrk]; exact hsp.2.2.1.1 v hv,
     fun l hl => by rw [hlm]; exact hsp.2.2.1.2 l hl⟩, ?_, ?_, hdm.trans hsp.2.2.2.2.2⟩
  · intro r hr hng
    have hr0 : r ∈ fullArenaClauseRefsCore s.core := by rw [← hperm.2.1]; exact hr
    obtain ⟨_, hgb, hp⟩ := hperm.2.2 r hr0
    exact (hsp.2.2.2.1 r hr0 (hgb.symm.trans hng)).perm (hp.symm.map (· / 2))
  · exact hsp.2.2.2.2.1.of_pres hpres fun r hr => by
      change r ∈ fullArenaClauseRefsCore s'.core; rw [hperm.2.1]; exact hr

private theorem fullSparseInvW_after_sweep {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s' : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    (hlen' : s'.LengthsOk c) (hw' : FullWitnessInv c F0 F_cur s'.core)
    (hnd' : FullArenaVarsNodup s') (hll' : FullLastLearnedWf s')
    (hext' : s'.scratch.extend_len = s.scratch.extend_len)
    (hmrk : s'.core.mrk = s.core.mrk) (hlm : s'.core.lit_mark = s.core.lit_mark)
    (hdm : s'.core.dense_mode = s.core.dense_mode) : FullSparseInvW c F0 F_cur s' :=
  ⟨hlen', hw',
    ⟨fun v hv => by rw [hmrk]; exact hsp.2.2.1.1 v hv,
     fun l hl => by rw [hlm]; exact hsp.2.2.1.2 l hl⟩,
    hnd', ⟨hll', hext' ▸ hsp.2.2.2.2.1.2⟩, hdm.trans hsp.2.2.2.2.2⟩

private theorem bv32_ofNat_toNat_lt {n : Nat} (h : n < 2 ^ 32) :
    (BitVec.ofNat 32 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

private theorem bv64_one_nat : (1#64 : BitVec 64).toNat = 1 := rfl
private theorem bv64_two_nat : (2#64 : BitVec 64).toNat = 2 := rfl

private theorem bv8_or1_ne0 (x : BitVec 8) : (x ||| 1#8) ≠ 0#8 := by
  revert x; decide

private theorem bv8_or2_ne0 (x : BitVec 8) : (x ||| 2#8) ≠ 0#8 := by
  revert x; decide

private theorem bv32_and_bin_ne0_of_ne {w : BitVec 32} (h : (w &&& 0x80000000#32) ≠ 0#32) :
    (w &&& 0x80000000#32) ≠ 0#32 := h

end Helpers

/-! ## 2. `full_enter_dense_m5_wp` (`FullFastSched.schedEnterDenseSpec`) -/

section EnterDenseProof

private def M5EnterOk (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s st : FullState) : Prop :=
  st.LengthsOk c ∧ FullWitnessInv c F0 F_cur st.core ∧ FullLitMarksClear c st ∧
  FullArenaVarsNodup st ∧ FullExtScratchOk c st ∧
  st.core.cur_level = 0 ∧ st.core.fuel.toNat ≤ s.core.fuel.toNat

/-- `full_enter_dense_m5` satisfies canonical `FullFastSched.schedEnterDenseSpec` parametrically
in `Γ`, returning `false` immediately if `h->oom != 0ULL` on entry (or after level-0 propagation)
without wiping a pre-existing `h->oom = 1ULL`. -/
public theorem full_enter_dense_m5_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hSweepBins : ∀ a m Q X, fullSweepBinsSpec a m Q X → Γ "full_sweep_bins" [i64] [] a m Q X)
    (hWatchPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X → Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hArenaNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X) :
    ∀ a m Q X, FullFastSched.schedEnterDenseSpec a m Q X →
      Func.wp Γ full_enter_dense_m5_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hsp0, hm, hQ⟩
  obtain ⟨F_cur, hspw0⟩ := hsp0.exists_witness
  have har_cap : c.arena_cap < 2 * 2 ^ 28 := c.harena
  have hmaxv : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  have hclv_lt : s.core.cur_level < 2 ^ 64 := by
    have := hspw0.2.1.cur_level_le; have := hspw0.1.core_ok.trail_end_le
    have := hspw0.1.core_ok.cur_vars_le; omega
  unfold Func.wp full_enter_dense_m5_body
  c0_hsteps_nogrp
  refine wp_join_state0 (α := FullState)
    (fun s1 m1 => M5EnterOk c F0 F_cur s s1 ∧ s1.core.dense_mode = 0#64 ∧
      (FullMem c s1 ⋆ R) m1) ?_ ?_
  · rintro _ s1 m1 ⟨hok1, hdm1, hm1⟩
    clear hm hsp0 hspw0
    have hspw1 : FullSparseInvW c F0 F_cur s1 :=
      ⟨hok1.1, hok1.2.1, hok1.2.2.1, hok1.2.2.2.1, hok1.2.2.2.2.1, hdm1⟩
    c0_hsplit
    · -- Pre-existing `h->oom != 0ULL`: return `false` immediately without wiping `h->oom`.
      c0_hsteps
      exact hQ false s1 m1 hok1.2.2.2.2.2.1 hok1.2.2.2.2.2.2 (by simp) (fun _ => hspw1.toSparse) hm1
    · c0_hsplit
      · exact absurd hdm1 hc
      · -- `dense_mode == 0`: flush level-0 units before `full_sweep_bins`.
        c0_hsteps; c0_call hProp
        refine ⟨c, F0, F_cur, s1, R, rfl, hok1.1, hok1.2.1, hdm1, hm1, ?_⟩
        intro pr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fuel1p _ _ _ _ _ _ _ _ m1p s1p
          hlen1p hw1p _ hperm1p hfl1p _ _ hpr1 _ _ hm1p
        have hspw1p := fullSparseInvW_of_perm hspw1 hlen1p hw1p hperm1p rfl rfl rfl ⟨rfl, rfl⟩
        have hcl1p : s1p.core.cur_level = 0 := hok1.2.2.2.2.2.1
        have hfl1p' : s1p.core.fuel.toNat ≤ s.core.fuel.toNat := by
          have h1 : s1.core.fuel.toNat ≤ s.core.fuel.toNat := hok1.2.2.2.2.2.2
          dsimp only [s1p]; omega
        c0_hsplit
        · -- Conflict at level 0: set `inconsistent = 1#64`, return `false`.
          c0_hsteps
          let s_inc : FullState := { s1p with core := { s1p.core with inconsistent := 1#64 } }
          have hu_fc := level0_fcur_unsat_of_confl hw1p hcl1p (hpr1 hc).2.2
          have hspw_inc : FullSparseInvW c F0 F_cur s_inc :=
            fullSparseInvW_with_inc hspw1p hu_fc 1#64
          exact hQ false s_inc _ hcl1p hfl1p' (by simp) (fun _ => hspw_inc.toSparse) hm
        · c0_hsplit
          · -- `h->oom != 0ULL` after `full_propagate`: return `false` without wiping `h->oom`.
            c0_hsteps
            exact hQ false s1p m1p hcl1p hfl1p' (by simp) (fun _ => hspw1p.toSparse) hm1p
          · -- `h->oom == 0ULL`: sweep bins and populate dense watches.
            c0_hsteps; c0_call hSweepBins
            refine ⟨c, F0, F_cur, s1p, R, rfl, hspw1p.1, hspw1p.2.1, hm1p,
              fun wvec2 wstk2 wlen2 nb2 wsort2 m2 hlen2 _ hd2 hw2 hm2 => ?_⟩
            let s2 : FullState :=
              { s1p with
                core := { s1p.core with
                  wvec := wvec2, wstk := wstk2, wlen := wlen2, wusable := 0#64, num_binary := nb2 }
                scratch := { s1p.scratch with wsort := wsort2 } }
            have hok2 : M5EnterOk c F0 F_cur s s2 :=
              ⟨hlen2, hw2, hspw1p.2.2.1, hspw1p.2.2.2.1, hspw1p.2.2.2.2.1, hcl1p, hfl1p'⟩
            c0_hsteps_nogrp
            refine wp_loop_inv
              (fun (p, ()) mP =>
                p.toNat ≤ s2.core.arena_len ∧
                (p.toNat = s2.core.arena_len ∨ p.toNat ∈ fullArenaClauseRefs s2) ∧
                ∃ sP : FullState,
                  M5EnterOk c F0 F_cur s sP ∧ DenseWatchesInv F_cur sP.core ∧
                  sP.core.arena = s2.core.arena ∧ sP.core.arena_len = s2.core.arena_len ∧
                  sP.core.dense_mode = 0#64 ∧ (FullMem c sP ⋆ R) mP)
              (fun (p, ()) _ => s2.core.arena_len - p.toNat)
              (fun JP hLoopP => by
                c0_hsteps
                refine hLoopP (0#64, ()) m2 ⟨Nat.zero_le _, ?_, s2, hok2, hd2, rfl, rfl, hdm1, hm2⟩
                by_cases hz : s2.core.arena_len = 0
                · exact Or.inl hz.symm
                · exact Or.inr (FullDenseWatchHelpers.fullArenaClauseRefs_zero_mem hw2.arena
                    (Nat.pos_of_ne_zero hz)))
              (fun JP ⟨p, ⟨⟩⟩ mP ⟨hp_le, hp_mem, sP, hokP, hdP, harP, halenP, hdmP, hmP⟩
                  hLoopP => ?_)
            have halP := hokP.1.core_ok.arena_len_le
            have haarP := hokP.1.core_ok.arena_len_arr
            have hrefsP : fullArenaClauseRefs sP = fullArenaClauseRefs s2 := by
              unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [harP, halenP]
            c0_hsplit
            · have hp_lt : p.toNat < sP.core.arena_len := by c0_bound
              have hp_in : p.toNat ∈ fullArenaClauseRefs sP := by
                rw [hrefsP]; exact hp_mem.resolve_left (by omega)
              have hp_wf := hokP.2.1.arena.refs_wf p.toNat hp_in
              have hp_lt32 : p.toNat < 2 ^ 32 := by omega
              have hp_trunc : (p.setWidth 32).toNat = p.toNat := by bv_omega
              have hnb := fullArenaNextOff_bounds (ar := sP.core.arena) (alen := sP.core.arena_len)
                (cref := p.toNat) hp_wf.1
              have hnxt_mem := fullArenaClauseRefs_next_mem hokP.2.1.arena hp_in
              c0_hsteps_nogrp
              refine wp_join_state0 (α := FullState)
                (fun sN mN => M5EnterOk c F0 F_cur s sN ∧ DenseWatchesInv F_cur sN.core ∧
                  sN.core.arena = s2.core.arena ∧ sN.core.arena_len = s2.core.arena_len ∧
                  sN.core.dense_mode = 0#64 ∧ (FullMem c sN ⋆ R) mN)
                (fun _ sN mN ⟨hokN, hdN, harN, halenN, hdmN, hmN⟩ => by
                  c0_hsteps; c0_call hArenaNext
                  refine ⟨c, sN, R, rfl, hokN.1, hmN, ?_⟩
                  have hn_eq : ((BitVec.ofNat 32 (fullArenaNextOff sN.core.arena sN.core.arena_len
                      (p.setWidth 32).toNat)).setWidth 64).toNat =
                      fullArenaNextOff sP.core.arena sP.core.arena_len p.toNat := by
                    rw [harN, halenN, ← harP, ← halenP, hp_trunc, BitVec.toNat_setWidth,
                      bv32_ofNat_toNat_lt (by omega)]
                    exact Nat.mod_eq_of_lt (by omega)
                  c0_hsteps
                  exact hLoopP (_, ()) mN (by dsimp only; rw [hn_eq]; omega)
                    ⟨by rw [hn_eq]; omega,
                      by rw [hn_eq]
                         rcases hnxt_mem with hend | hmem
                         · exact Or.inl (hend.trans halenP)
                         · exact Or.inr (hrefsP ▸ hmem),
                      sN, hokN, hdN, harN, halenN, hdmN, hmN⟩)
                (fun JN hJN => ?_)
              c0_hsteps_nogrp
              · have hsz_eq : (sP.core.arena[(p + 2#64).toNat]'(by c0_bound)).toNat =
                    fullArenaClauseSizeCore sP.core p.toNat := by
                  have hp2 : (p + 2#64).toNat = p.toNat + 2 := by c0_bound
                  unfold fullArenaClauseSizeCore
                  rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; simp only [hp2]
                have hsz_ge3 : 3 ≤ (sP.core.arena[(p + 2#64).toNat]'(by c0_bound)).toNat := by
                  rw [hsz_eq]; exact hp_wf.2.1
                have hsz_lt31 : (sP.core.arena[(p + 2#64).toNat]'(by c0_bound)).toNat < 2 ^ 31 := by
                  rw [hsz_eq]; have := hp_wf.2.2.1; have := hp_wf.2.2.2.1; omega
                have hmask := bv32_mask_7fffffff_props hsz_ge3 hsz_lt31
                have hp_lt31 : (p.setWidth 32).toNat < 0x80000000 := by rw [hp_trunc]; omega
                have hp_neff : p.setWidth 32 ≠ 0xFFFFFFFF#32 := fun heq => by
                  rw [heq] at hp_lt31; revert hp_lt31; decide
                refine wp_loop_inv
                  (fun (k, ()) mK =>
                    k.toNat ≤ (sP.core.arena[(p + 2#64).toNat]'(by c0_bound)).toNat ∧
                    ∃ sK : FullState,
                      M5EnterOk c F0 F_cur s sK ∧ DenseWatchesInv F_cur sK.core ∧
                      sK.core.arena = s2.core.arena ∧ sK.core.arena_len = s2.core.arena_len ∧
                      sK.core.dense_mode = 0#64 ∧ (FullMem c sK ⋆ R) mK)
                  (fun (k, ()) _ => (sP.core.arena[(p + 2#64).toNat]'(by c0_bound)).toNat - k.toNat)
                  (fun JK hLoopK => by
                    c0_hsteps
                    exact hLoopK (0#32, ()) mP
                      ⟨Nat.zero_le _, sP, hokP, hdP, harP, halenP, hdmP, hmP⟩)
                  (fun JK ⟨k, ⟨⟩⟩ mK ⟨hk_le, sK, hokK, hdK, harK, halenK, hdmK, hmK⟩ hLoopK => ?_)
                have haarK := hokK.1.core_ok.arena_len_arr
                c0_hsplit
                · have hk_lt : k.toNat < (sP.core.arena[(p + 2#64).toNat]'(by c0_bound)).toNat := by
                    c0_bound
                  have hidx_eq : (p + 3#64 + k.setWidth 64).toNat = p.toNat + 3 + k.toNat := by
                    have := hp_wf.2.2.1; have := hp_wf.2.2.2.1; bv_omega
                  have hidx_lt : (p + 3#64 + k.setWidth 64).toNat < sK.core.arena.length := by
                    rw [hidx_eq]; rw [hsz_eq] at hk_lt
                    have := hp_wf.2.2.1; have := hp_wf.2.2.2.1
                    have := hokK.1.core_ok.arena_len_le; omega
                  c0_hsteps; c0_call hWatchPush
                  refine ⟨c, sK, R, rfl, hokK.1, hdK.layout, by simp,
                    fun _ => ⟨hmask.2.1, hp_neff⟩, hmK,
                    fun ok wvecK' wstkK' wlenK' wuK' wsortK' mK' hlenK' hlayK' hothK' hokT
                      hokF hmK' => ?_⟩
                  let sK' : FullState :=
                    { sK with
                      core := { sK.core with wvec := wvecK', wstk := wstkK', wlen := wlenK',
                                             wusable := wuK' }
                      scratch := { sK.scratch with wsort := wsortK' } }
                  have hp_inK : (p.setWidth 32).toNat ∈ fullArenaClauseRefsCore sK.core := by
                    rw [hp_trunc]; unfold fullArenaClauseRefsCore
                    rw [harK, halenK, ← harP, ← halenP]
                    exact hp_in
                  have hdK' : DenseWatchesInv F_cur sK'.core :=
                    fullWatchPush_preserves_denseWatchesInv hdK hlayK' rfl (fun _ r => r)
                      hmask.1 hmask.2.2 hp_lt31 hp_inK hothK'
                      (fun ht => by
                        obtain ⟨hl, _, hsz', hpre', hw0', hw1'⟩ := hokT ht
                        exact ⟨hl, hsz', hpre', hw0', hw1' rfl⟩) (fun hf => (hokF hf).1)
                  have hwK' : FullWitnessInv c F0 F_cur sK'.core :=
                    { hokK.2.1 with
                      arena := { hokK.2.1.arena with len_ok := hokK.2.1.arena.len_ok }
                      watches := by
                        rw [ModeWatchesInv, ite_eq_left hdmK]
                        exact denseWatchesInv_toWatchesInv hdK' }
                  have hokK' : M5EnterOk c F0 F_cur s sK' :=
                    ⟨hlenK', hwK', hokK.2.2.1, hokK.2.2.2.1, hokK.2.2.2.2.1, hokK.2.2.2.2.2.1,
                      hokK.2.2.2.2.2.2⟩
                  c0_hsplit
                  · have hk1 : (k + 1#32).toNat = k.toNat + 1 := by c0_bound
                    c0_hsteps
                    exact hLoopK (k + 1#32, ()) mK' (by dsimp only; omega)
                      ⟨by omega, sK', hokK', hdK', harK, halenK, hdmK, hmK'⟩
                  · c0_hsteps
                    let sOom : FullState := { sK' with core := { sK'.core with oom := 0#64 } }
                    have hlenOom : sOom.LengthsOk c :=
                      ⟨{ hlenK'.core_ok with vals_len := hlenK'.core_ok.vals_len },
                        hlenK'.scratch_ok⟩
                    have hwOom := fullWitnessInv_with_oom hwK' 0#64
                    c0_call hSweep
                    refine ⟨c, F0, F_cur, sOom, R, rfl, hlenOom, hwOom, hokK'.2.2.2.1, hdmK,
                      fun hpos => by
                        change 0 < sK.core.cur_level at hpos; have := hokK.2.2.2.2.2.1; omega,
                      hm, ?_⟩
                    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ scS mS sS hlenS _ hextS _ hllS
                      hwS hndS _ _ _ _ _ hmS
                    have hspS : FullSparseInv c F0 sS :=
                      ⟨⟨hlenS, F_cur, hwS⟩, hokK'.2.2.1, hndS, ⟨hllS, hextS ▸ hokK'.2.2.2.2.1.2⟩,
                        hdmK⟩
                    c0_hsteps
                    exact hQ false sS mS hokK'.2.2.2.2.2.1 hokK'.2.2.2.2.2.2
                      (by simp) (fun _ => hspS) hmS
                · c0_hsteps; exact hJN sK mK ⟨hokK, hdK, harK, halenK, hdmK, hmK⟩
              all_goals exact hJN sP mP ⟨hokP, hdP, harP, halenP, hdmP, hmP⟩
            · -- Outer loop exit: set `dense_mode = 1#64`, return `true`.
              c0_hsteps
              let sFin : FullState := { sP with core := { sP.core with dense_mode := 1#64 } }
              have hlenFin : sFin.LengthsOk c :=
                ⟨{ hokP.1.core_ok with vals_len := hokP.1.core_ok.vals_len }, hokP.1.scratch_ok⟩
              have hwFin : FullWitnessInv c F0 F_cur sFin.core :=
                fullWitnessInv_with_dense_mode_nz hokP.2.1 hdP (by decide)
              have hdenFin : FullDenseInv c F0 sFin :=
                ⟨⟨hlenFin, F_cur, hwFin⟩, hokP.2.2.1, hokP.2.2.2.1, hokP.2.2.2.2.1,
                  hokP.2.2.2.2.2.1, show (1#64 : BitVec 64) ≠ 0#64 by decide⟩
              exact hQ true sFin _ hokP.2.2.2.2.2.1 hokP.2.2.2.2.2.2
                (fun _ => hdenFin) (by simp) hm
  · intro J1 hJ1; c0_hsplit
    · c0_hsteps; c0_call hBacktrack
      refine ⟨c, s, R, rfl, hspw0.1, hclv_lt, fun _ => by
        have := hspw0.2.1.cur_level_le; have := hspw0.1.core_ok.trail_end_le
        have := hspw0.1.core_ok.cur_vars_le; omega,
        hspw0.2.1.trail_lits_lt, hm, ?_⟩
      intro _ _ _ _ _ _ _ cl1 _ sc1 m1 s1 hlen1 _ _ hcl1 hprsc1 _ _ _ hw_le _ hm1
      have hw1 := hw_le F0 F_cur hspw0.2.1 (Nat.zero_le _)
      have hl01 : s1.core.cur_level = 0 := by dsimp only [s1]; rw [hcl1]; simp
      have hsp1 := fullSparseInvW_after_bt0 hspw0 hlen1 hw1 hprsc1.1 rfl rfl rfl rfl rfl
      c0_hsteps
      exact hJ1 s1 m1 ⟨⟨hsp1.1, hsp1.2.1, hsp1.2.2.1, hsp1.2.2.2.1, hsp1.2.2.2.2.1, hl01,
        Nat.le_refl _⟩, hsp1.2.2.2.2.2, hm1⟩
    · have hl00 : s.core.cur_level = 0 := by
        have hnat := congrArg BitVec.toNat hc
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hclv_lt] at hnat; exact hnat
      c0_hsteps
      exact hJ1 s m ⟨⟨hspw0.1, hspw0.2.1, hspw0.2.2.1, hspw0.2.2.2.1, hspw0.2.2.2.2.1, hl00,
        Nat.le_refl _⟩, hspw0.2.2.2.2.2, hm⟩

end EnterDenseProof

/-! ## 3. `full_substitute_m5_wp` (`Full.fullSubstituteSpec`) -/

section SubstituteProof

/-- `full_substitute_m5` satisfies canonical `Full.fullSubstituteSpec` parametrically in `Γ`,
aborting immediately before `full_propagate`/`full_arena_sweep` whenever `h->oom != 0ULL`. -/
public theorem full_substitute_m5_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hTarjan : ∀ a m Q X, fullTarjanSccSpec a m Q X → Γ "full_tarjan_scc" [i64] [i64] a m Q X)
    (hElimVars : ∀ a m Q X, fullSubstElimVarsSpec a m Q X →
      Γ "full_subst_elim_vars" [i64, i64] [.bool] a m Q X)
    (hRewriteBins : ∀ a m Q X, fullSubstRewriteBinsSpec a m Q X →
      Γ "full_subst_rewrite_bins" [i64] [.bool] a m Q X)
    (hRewriteAr : ∀ a m Q X, fullSubstRewriteArSpec a m Q X →
      Γ "full_subst_rewrite_ar" [i64] [.bool] a m Q X)
    (hArenaSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullSubstituteSpec a m Q X → Func.wp Γ full_substitute_m5_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s0, R, rfl, hsp0, hm, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  obtain ⟨F_cur0, hw0⟩ := hsp0.exists_witness
  have hcl0 := hsp0.1.lengths.core_ok
  have hclv_lt : s0.core.cur_level < 2 ^ 64 := by
    have := hw0.2.1.cur_level_le; have := hcl0.trail_end_le; have := hcl0.cur_vars_le; omega
  unfold Func.wp full_substitute_m5_body
  c0_hsteps_nogrp
  refine wp_join_state0 (α := FullState)
    (fun st m1 => FullSparseInv c F0 st ∧ st.core.cur_level = 0 ∧
      st.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ (FullMem c st ⋆ R) m1) ?_ ?_
  · rintro _ st1 m1 ⟨hsp1, hl01, hfl1, hm1⟩
    c0_hsplit
    · c0_hsteps
      exact hQ 1#64 st1 m1 hsp1 hl01 hfl1 (Or.inl rfl) (fun h => by cases h) hm1
    · c0_hsplit
      · c0_hsteps
        exact hQ 1#64 st1 m1 hsp1 hl01 hfl1 (Or.inl rfl) (fun h => by cases h) hm1
      · c0_hsteps_nogrp
        refine wp_while_break_state (α := BitVec 64 × FullState) (β := BitVec 64 × FullState)
          (fun p => (p.1, ()))
          (fun p mb => FullSparseInv c F0 p.2 ∧ p.2.core.cur_level = 0 ∧
            p.2.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ (FullMem c p.2 ⋆ R) mb)
          (fun p => (p.1, ()))
          (fun p => 4 - p.1.toNat)
          (fun p ml => FullSparseInv c F0 p.2 ∧ p.2.core.cur_level = 0 ∧
            p.2.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ p.1.toNat ≤ 4 ∧ (FullMem c p.2 ⋆ R) ml)
          ?_ ?_ ?_
        · rintro _ ⟨_r, stb⟩ mb ⟨hspb, hl0b, hflb, hmb⟩
          c0_hsteps
          exact hQ 1#64 stb mb hspb hl0b hflb (Or.inl rfl) (fun h => by cases h) hmb
        · rintro B L ⟨round, st⟩ ml hB hL ⟨hsp, hl0_st, hfl_st, hr_le, hml⟩
          c0_hsplit
          · have hr_lt : round.toNat < 4 := hc
            have hr1 : (round + 1#64).toNat = round.toNat + 1 := by bv_omega
            c0_hsplit
            · c0_hsplit
              · obtain ⟨F_cur, hspw⟩ := hsp.exists_witness
                c0_hsteps; c0_call hTarjan
                refine ⟨c, F0, F_cur, st, R, rfl, hspw, hl0_st, hml, ?_⟩
                intro ucnt _ _ inc1 _ _ _ _ _ sstk1 _ m1 st1 hspw1 huc_le hus1 hrepr1 hm1
                have hl01' : st1.core.cur_level = 0 := hl0_st
                have hfl1' : st1.core.fuel.toNat ≤ s0.core.fuel.toNat := hfl_st
                c0_hsplit
                · c0_hsteps; exact hQ 20#64 st1 m1 hspw1.toSparse hl01' hfl1' (Or.inr rfl)
                    (fun _ => hspw1.2.1.ext_sound.2 (hspw1.2.1.inconsistent_sound hc)) hm1
                · c0_hsteps; c0_call hElimVars
                  refine ⟨c, F0, F_cur, st1, R, rfl, hspw1, hl01', hrepr1 hc, huc_le, hus1, hm1, ?_⟩
                  intro ok2 st2 m2 hspw2 hl02 _ hfl2 hrepr2 hfail2 hm2
                  have hfl2' : st2.core.fuel.toNat ≤ s0.core.fuel.toNat := by omega
                  c0_hsplit
                  · c0_hsplit
                    · c0_hsteps; exact hB (round, st2) m2 ⟨hspw2.toSparse, hl02, hfl2', hm2⟩
                    · c0_hsteps; c0_call hRewriteBins
                      refine ⟨c, F0, F_cur, st2, R, rfl, hspw2, hl02, hrepr2, hm2, ?_⟩
                      intro ok3 st3 m3 hspw3 hl03 _ hfl3 hrepr3 hfail3 hm3
                      have hfl3' : st3.core.fuel.toNat ≤ s0.core.fuel.toNat := by
                        rw [hfl3]; exact hfl2'
                      c0_hsplit
                      · c0_hsplit
                        · -- `h->oom != 0ULL` after `rewrite_bins`: abort early.
                          c0_hsteps
                          exact hQ 1#64 st3 m3 hspw3.toSparse hl03 hfl3' (Or.inl rfl)
                            (fun h => by cases h) hm3
                        · c0_hsteps; c0_call hRewriteAr
                          refine ⟨c, F0, F_cur, st3, R, rfl, hspw3, hl03, hrepr3, hm3, ?_⟩
                          intro ok4 st4 m4 hspw4 hl04 _ hfl4 hfail4 hm4
                          have hfl4' : st4.core.fuel.toNat ≤ s0.core.fuel.toNat := hfl4 ▸ hfl3'
                          c0_hsplit
                          · c0_hsplit
                            · -- `h->oom != 0ULL` after `rewrite_ar`: abort early.
                              c0_hsteps
                              exact hQ 1#64 st4 m4 hspw4.toSparse hl04 hfl4' (Or.inl rfl)
                                (fun h => by cases h) hm4
                            · -- Pre-sweep `full_propagate(h)` flush
                              c0_hsteps; c0_call hProp
                              refine ⟨c, F0, F_cur, st4, R, rfl, hspw4.1, hspw4.2.1,
                                hspw4.2.2.2.2.2, hm4, ?_⟩
                              intro pr4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fuel4p _ _ _ _ _ _ _ _ m4p
                                st4p hlen4p hw4p _ hperm4p hfl4p _ _ hpr4_1 _ _ hm4p
                              have hspw4p : FullSparseInvW c F0 F_cur st4p :=
                                fullSparseInvW_of_perm hspw4 hlen4p hw4p hperm4p rfl rfl rfl
                                  ⟨rfl, rfl⟩
                              have hl04p : st4p.core.cur_level = 0 := hl04
                              have hfl4p' : st4p.core.fuel.toNat ≤ s0.core.fuel.toNat := by
                                have h1 : st4.core.fuel.toNat ≤ s0.core.fuel.toNat := hfl4'
                                dsimp only [st4p]; omega
                              c0_hsplit
                              · c0_hsteps
                                exact hQ 20#64 st4p m4p hspw4p.toSparse hl04p hfl4p' (Or.inr rfl)
                                  (fun _ => level0_unsat_of_confl hw4p hl04p (hpr4_1 hc).2.2) hm4p
                              · c0_hsplit
                                · -- `h->oom != 0ULL` after pre-sweep propagate: abort before sweep.
                                  c0_hsteps
                                  exact hQ 1#64 st4p m4p hspw4p.toSparse hl04p hfl4p' (Or.inl rfl)
                                    (fun h => by cases h) hm4p
                                · c0_hsteps; c0_call hArenaSweep
                                  refine ⟨c, F0, F_cur, st4p, R, rfl, hspw4p.1, hspw4p.2.1,
                                    hspw4p.2.2.2.1, hspw4p.2.2.2.2.2, fun hpos => by omega,
                                    hm4p, ?_⟩
                                  intro sr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sc5 m5 st5
                                    hlen5 _ hext5 _ hll5 hw5 hnd5 _ _ _ hsr2 _ hm5
                                  have hspw5 := fullSparseInvW_after_sweep hspw4p hlen5 hw5 hnd5
                                    hll5 hext5 rfl rfl rfl
                                  have hl05 : st5.core.cur_level = 0 := hl04p
                                  c0_hsplit
                                  · c0_hsteps
                                    exact hQ 20#64 st5 m5 hspw5.toSparse hl05 hfl4p' (Or.inr rfl)
                                      (fun _ => (hsr2 hc).2) hm5
                                  · c0_hsplit
                                    · c0_hsteps
                                      exact hQ 1#64 st5 m5 hspw5.toSparse hl05 hfl4p' (Or.inl rfl)
                                        (fun h => by cases h) hm5
                                    · c0_hsplit
                                      · c0_hsteps
                                        exact hQ 1#64 st5 m5 hspw5.toSparse hl05 hfl4p' (Or.inl rfl)
                                          (fun h => by cases h) hm5
                                      · c0_hsteps; c0_call hProp
                                        refine ⟨c, F0, F_cur, st5, R, rfl, hspw5.1, hspw5.2.1,
                                          hspw5.2.2.2.2.2, hm5, ?_⟩
                                        intro pr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fuel6 _ _ _ _ _ _ _ _
                                          m6 st6 hlen6 hw6 _ hperm6 hfl6 _ _ hpr1 _ _ hm6
                                        have hspw6 := fullSparseInvW_of_perm hspw5 hlen6 hw6 hperm6
                                          rfl rfl rfl ⟨rfl, rfl⟩
                                        have hfl6' : st6.core.fuel.toNat ≤ s0.core.fuel.toNat := by
                                          have h5 : st5.core.fuel.toNat ≤ s0.core.fuel.toNat :=
                                            hfl4p'
                                          dsimp only [st6]; omega
                                        c0_hsplit
                                        · c0_hsteps
                                          exact hQ 20#64 st6 m6 hspw6.toSparse hl05 hfl6'
                                            (Or.inr rfl) (fun _ =>
                                              level0_unsat_of_confl hw6 hl05 (hpr1 hc).2.2) hm6
                                        · c0_hsteps
                                          exact hL (round + 1#64, st6) m6 (by dsimp only; omega)
                                            ⟨hspw6.toSparse, hl05, hfl6', by dsimp only; omega, hm6⟩
                          · c0_hsteps; exact hQ 20#64 st4 m4 hspw4.toSparse hl04 hfl4' (Or.inr rfl)
                              (fun _ => hfail4 (by
                                cases ok4 <;>
                                  first | rfl | contradiction | exact absurd rfl hc)) hm4
                      · c0_hsteps; exact hQ 20#64 st3 m3 hspw3.toSparse hl03 hfl3' (Or.inr rfl)
                          (fun _ => hfail3 (by
                            cases ok3 <;> first | rfl | contradiction | exact absurd rfl hc)) hm3
                  · c0_hsteps; exact hQ 20#64 st2 m2 hspw2.toSparse hl02 hfl2' (Or.inr rfl)
                      (fun _ => hfail2 (by
                        cases ok2 <;> first | rfl | contradiction | exact absurd rfl hc)) hm2
              · c0_hsteps; exact hB (round, st) ml ⟨hsp, hl0_st, hfl_st, hml⟩
            · c0_hsteps; exact hB (round, st) ml ⟨hsp, hl0_st, hfl_st, hml⟩
          · c0_hsteps; exact hB (round, st) ml ⟨hsp, hl0_st, hfl_st, hml⟩
        · intro B L _ hL; c0_hsteps
          exact hL (0#64, st1) m1 ⟨hsp1, hl01, hfl1, Nat.zero_le _, hm1⟩
  · intro Jbt hJbt; c0_hsplit
    · c0_hsteps; c0_call hBacktrack
      refine ⟨c, s0, R, rfl, hsp0.1.lengths, hclv_lt, fun _ => by
        have := hw0.2.1.cur_level_le; have := hcl0.trail_end_le; have := hcl0.cur_vars_le; omega,
        hw0.2.1.trail_lits_lt, hm, ?_⟩
      intro _ _ _ _ _ _ _ cl1 _ sc1 m1 st1 hlen1 _ _ hcl1 hprsc1 _ _ _ hw_le _ hm1
      have hw1 := hw_le F0 F_cur0 hw0.2.1 (Nat.zero_le _)
      have hl01 : st1.core.cur_level = 0 := by dsimp only [st1]; rw [hcl1]; simp
      c0_hsteps; exact hJbt st1 m1
        ⟨(fullSparseInvW_after_bt0 hw0 hlen1 hw1 hprsc1.1 rfl rfl rfl rfl rfl).toSparse,
         hl01, Nat.le_refl _, hm1⟩
    · have hl00 : s0.core.cur_level = 0 := by
        have hnat := congrArg BitVec.toNat hc
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hclv_lt] at hnat; exact hnat
      c0_hsteps; exact hJbt s0 m ⟨hsp0, hl00, Nat.le_refl _, hm⟩

end SubstituteProof

/-! ## 4. `full_subst_rewrite_bins_m5_wp` (`Full.fullSubstRewriteBinsSpec`) -/

section RewriteBinsProof

private def rbMask (s : FullState) : FullState :=
  { s with
    core := { s.core with lit_mark := [], wstk := [], num_binary := 0#64 }
    scratch := { s.scratch with work_stk1 := [], work_stk2 := [] } }

private def withWstk (k : FullCoreState) (ws : List (BitVec 32)) : FullCoreState :=
  { k with wstk := ws }

private def RbOuterInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s0 : FullState) (l : BitVec 64) (ml : Mem 64) (R : Mem 64 → Prop) : Prop :=
  ∃ st : FullState,
    FullSparseInvW c F0 F_cur st ∧
    st.core.cur_vars = s0.core.cur_vars ∧ st.core.cur_level = 0 ∧
    st.core.fuel = s0.core.fuel ∧ FullReprEquiv F_cur st ∧
    l.toNat ≤ 2 * s0.core.cur_vars ∧ (FullMem c st ⋆ R) ml

private def RbLmCov (c : FullCfg) (st1 : FullState) (off q_n pn_n : Nat) : Prop :=
  ∀ x < 2 * c.max_vars, st1.core.lit_mark[x]?.getD 0#8 ≠ 0#8 →
    (∃ idx, off ≤ idx ∧ idx < q_n ∧
      (st1.core.wstk[idx]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32 ∧
      (st1.core.wstk[idx]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat = x) ∨
    (∃ k, k < pn_n ∧ (st1.scratch.work_stk2[k]?.getD 0#32).toNat = x)

private def RbPaOk (F_cur : List (List Nat)) (st st1 : FullState) (pn_n : Nat) : Prop :=
  ∀ k < pn_n,
    (st1.scratch.work_stk1[k]?.getD 0#32).toNat < 2 * st.core.cur_vars ∧
    (st1.scratch.work_stk2[k]?.getD 0#32).toNat < 2 * st.core.cur_vars ∧
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause [(st1.scratch.work_stk1[k]?.getD 0#32).toNat,
                  (st1.scratch.work_stk2[k]?.getD 0#32).toNat])

private def RbInner1Inv (c : FullCfg) (F_cur : List (List Nat)) (st : FullState)
    (l off sz : Nat) (pn p q : BitVec 64) (m1 : Mem 64) (R : Mem 64 → Prop) : Prop :=
  ∃ st1 : FullState,
    AgreesExcept rbMask st st1 ∧ st1.LengthsOk c ∧
    off ≤ q.toNat ∧ q.toNat ≤ p.toNat ∧ p.toNat ≤ off + sz ∧
    pn.toNat ≤ 2 * st.core.cur_vars ∧
    (∀ idx, p.toNat ≤ idx → st1.core.wstk[idx]? = st.core.wstk[idx]?) ∧
    (∀ idx, (idx < off ∨ off + sz ≤ idx) → st1.core.wstk[idx]? = st.core.wstk[idx]?) ∧
    WatchSliceOk F_cur st.core l p.toNat (off + sz - p.toNat) ∧
    WatchSliceOk F_cur (withWstk st.core st1.core.wstk) l off (q.toNat - off) ∧
    RbLmCov c st1 off q.toNat pn.toNat ∧ RbPaOk F_cur st st1 pn.toNat ∧
    (FullMem c st1 ⋆ R) m1

private theorem rb_st4_eq (st st3 : FullState) (hag : AgreesExcept rbMask st st3)
    (wv' : List (BitVec 32)) (wu' : BitVec 64) :
    ({ st3 with core := { st3.core with wvec := wv', wusable := wu' } } : FullState) =
      { st with
        core := { st.core with
          lit_mark := st3.core.lit_mark, wvec := wv', wstk := st3.core.wstk,
          wusable := wu', num_binary := st3.core.num_binary }
        scratch := { st.scratch with
          work_stk1 := st3.scratch.work_stk1, work_stk2 := st3.scratch.work_stk2 } } := by
  have hc := congrArg (rbMask · |>.core) hag
  have hs := congrArg (rbMask · |>.scratch) hag
  cases st3 with | mk c3 sc3 => cases st with | mk cs scs =>
  cases c3; cases cs; simp only [rbMask] at hc; cases hc
  cases sc3; cases scs; simp only [rbMask] at hs; cases hs; rfl

/-- `full_subst_rewrite_bins_m5` satisfies canonical `Full.fullSubstRewriteBinsSpec`
parametrically in `Γ`, deduplicating rewritten binaries via `lit_mark` bit 1 and setting
`h->oom = 1ULL` (aborting cleanly without dropping clauses or falsely returning `false`) on
overflow or `full_add_bin == 2ULL`. -/
public theorem full_subst_rewrite_bins_m5_wp (Γ : Env)
    (hAddUnit : ∀ args m Q X, fullAddUnitSpec args m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] args m Q X)
    (hAddBin : ∀ args m Q X, fullAddBinSpec args m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] args m Q X) :
    ∀ args m Q X, fullSubstRewriteBinsSpec args m Q X →
      Func.wp Γ full_subst_rewrite_bins_m5_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s0, R, rfl, hsp0, hl0, hrepr0, hm, hQ⟩
  have hmx := c.hmaxv; have hwcap := c.hwcap; unfold dimacsBound at hmx hwcap
  unfold Func.wp full_subst_rewrite_bins_m5_body
  s_split
  · s_steps; exact hQ true s0 m hsp0 hl0 rfl rfl hrepr0 (fun h => by cases h) hm
  · s_to_group
    refine wp_loop_inv
      (fun (l, ()) ml => RbOuterInv c F0 F_cur s0 l ml R)
      (fun (l, ()) _ => 2 * s0.core.cur_vars - l.toNat) ?_ ?_
    · intro J hJ; s_steps
      exact hJ (0#64, ()) m ⟨s0, hsp0, rfl, hl0, rfl, hrepr0, Nat.zero_le _, hm⟩
    · rintro J ⟨l, ⟨⟩⟩ ml ⟨st, hsp, hcv, hl0_st, hfl, hrepr, hl_le, hml⟩ hJ
      have hcl := hsp.1.core_ok; have hsl := hsp.1.scratch_ok
      have hcv_le := hcl.cur_vars_le
      have hwvl := hcl.wvec_len; have hwsl := hcl.wstk_len_arr
      have hrpl := hcl.repr_len; have hlml := hcl.lit_mark_len
      have hws1l := hsl.work_stk1_len; have hws2l := hsl.work_stk2_len
      have hwle := hcl.wlen_le
      have hwat : WatchesInv F_cur st.core := by
        have hm_w := hsp.2.1.watches; unfold ModeWatchesInv at hm_w
        simp only [hsp.2.2.2.2.2, ↓reduceIte] at hm_w; exact hm_w
      s_split
      · have hl_lt : l.toNat < 2 * s0.core.cur_vars := by
          rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hc; omega
        have hl1 : (l + 1#64).toNat = l.toNat + 1 := by
          rw [BitVec.toNat_add, bv64_one_nat, Nat.mod_eq_of_lt (by omega)]
        have h2l_eq : (l <<< (1 : BitVec 64)).toNat = 2 * l.toNat := by
          rw [FullSubstTactics.bv64_shl_one, Nat.mod_eq_of_lt (by omega)]
        have h2l1_eq : ((l <<< (1 : BitVec 64)) + 1).toNat = 2 * l.toNat + 1 := by
          rw [BitVec.toNat_add, h2l_eq, FullSubstTactics.bv64_one_toNat,
            Nat.mod_eq_of_lt (by omega)]
        have h2l_lt : (l <<< (1 : BitVec 64)).toNat < st.core.wvec.length := by
          rw [h2l_eq, hwvl]; omega
        have h2l1_lt : ((l <<< (1 : BitVec 64)) + 1).toNat < st.core.wvec.length := by
          rw [h2l1_eq, hwvl]; omega
        let off := fullWatchOff st l.toNat
        let sz := fullWatchSize st l.toNat
        have hoff_eq : (st.core.wvec[(l <<< (1 : BitVec 64)).toNat]'h2l_lt).toNat = off := by
          dsimp only [off, fullWatchOff, fullWatchOffCore]
          rw [← h2l_eq, List.getElem?_eq_getElem h2l_lt, Option.getD_some]
        have hsz_eq : (st.core.wvec[((l <<< (1 : BitVec 64)) + 1).toNat]'h2l1_lt).toNat = sz := by
          dsimp only [sz, fullWatchSize, fullWatchSizeCore]
          rw [← h2l1_eq, List.getElem?_eq_getElem h2l1_lt, Option.getD_some]
        have hwv0_eq : ∀ h, (st.core.wvec[2 * l.toNat % 2 ^ 64]'h).toNat = off := fun h => by
          have heq : 2 * l.toNat % 2 ^ 64 = (l <<< (1 : BitVec 64)).toNat := by omega
          have := congrArg (Option.getD · 0#32)
            ((List.getElem?_eq_getElem h).symm.trans (by rw [heq, List.getElem?_eq_getElem h2l_lt]))
          exact (congrArg BitVec.toNat this).trans hoff_eq
        have hwv1_eq : ∀ h, (st.core.wvec[(2 * l.toNat + 1) % 2 ^ 64]'h).toNat = sz := fun h => by
          have heq : (2 * l.toNat + 1) % 2 ^ 64 = ((l <<< (1 : BitVec 64)) + 1).toNat := by omega
          have := congrArg (Option.getD · 0#32)
            ((List.getElem?_eq_getElem h).symm.trans
              (by rw [heq, List.getElem?_eq_getElem h2l1_lt]))
          exact (congrArg BitVec.toNat this).trans hsz_eq
        have hbound := hwat.layout.bounds l.toNat (hcv ▸ hl_lt)
        have hslice_orig := hwat.slices l.toNat (hcv ▸ hl_lt)
        change off + sz ≤ st.core.wlen at hbound
        change WatchSliceOk F_cur st.core l.toNat off sz at hslice_orig
        have hend_lt : off + sz ≤ c.wcap := by omega
        s_split
        · s_steps
          exact hJ (l + 1#64, ()) ml (by dsimp only; omega)
            ⟨st, hsp, hcv, hl0_st, hfl, hrepr, by omega, hml⟩
        · have hrl_lt : (st.core.repr[l.toNat]'(by omega)).toNat < 2 * st.core.cur_vars := by
            have := FullReprEquiv.lt hrepr (hcv ▸ hl_lt)
            rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
          have hrl_eqv : LitEquiv (cnfOfClauses F_cur) l.toNat
              (st.core.repr[l.toNat]'(by omega)).toNat := by
            have := FullReprEquiv.litEquiv hrepr (hcv ▸ hl_lt)
            rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
          s_to_group
          refine wp_loop_inv
            (fun (pn, ovf, p, q, ()) m1 => RbInner1Inv c F_cur st l.toNat off sz pn p q m1 R)
            (fun (_, _, p, _, ()) _ => off + sz - p.toNat) ?_ ?_
          · intro J1 hJ1; s_steps
            have h0_eq : ∀ (h : (l <<< (1 : BitVec 64)).toNat < st.core.wvec.length),
                (BitVec.setWidth 64 (st.core.wvec[(l <<< (1 : BitVec 64)).toNat]'h)).toNat =
                off :=
              fun _ => by rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega), hoff_eq]
            refine hJ1 _ _ ⟨st, AgreesExcept.refl _ _, hsp.1,
              Nat.le_of_eq (h0_eq _).symm, Nat.le_refl _,
              Nat.le_trans (Nat.le_of_eq (h0_eq _)) (Nat.le_add_right _ _), Nat.zero_le _,
              fun _ _ => rfl, fun _ _ => rfl, ?_, ?_, ?_, fun _ h => by simp at h, hml⟩
            · refine Eq.subst
                (motive := fun x => WatchSliceOk F_cur st.core l.toNat x (off + sz - x))
                (h0_eq _).symm ?_
              rw [Nat.add_sub_cancel_left]; exact hslice_orig
            · refine Eq.subst
                (motive := fun x =>
                  WatchSliceOk F_cur (withWstk st.core st.core.wstk) l.toNat off (x - off))
                (h0_eq _).symm ?_
              rw [Nat.sub_self]; exact .empty
            · intro x hx hnz; exfalso; exact hnz (hsp.2.2.1.2 x hx)
          · rintro J1 ⟨pn, ovf, p, q, ⟨⟩⟩ m1
              ⟨st1, hag1, hlen1, hq_lo, hqp, hp_hi, hpn_le, htail1, hout1,
               hrem1, hkept1, hlm1, hpa1, hm1⟩ hJ1
            have hcl1 := hlen1.core_ok; have hsl1 := hlen1.scratch_ok
            have hwsl1 := hcl1.wstk_len_arr; have hlml1 := hcl1.lit_mark_len
            have hrpl1 := hcl1.repr_len
            have hws1l1 := hsl1.work_stk1_len; have hws2l1 := hsl1.work_stk2_len
            have hcv1 : st1.core.cur_vars = st.core.cur_vars := hag1.get (·.core.cur_vars)
            have hrp1 : st1.core.repr = st.core.repr := hag1.get (·.core.repr)
            s_split
            · have hp_lt : p.toNat < off + sz := by
                rw [hwv0_eq, hwv1_eq, Nat.mod_eq_of_lt (by omega)] at hc; omega
              have hp1 : (p + (1 : BitVec 64)).toNat = p.toNat + 1 := by
                rw [BitVec.toNat_add, FullSubstTactics.bv64_one_toNat, Nat.mod_eq_of_lt (by omega)]
              let w0 := st1.core.wstk[p.toNat]'(by omega)
              have hw0_eq : st.core.wstk[p.toNat]? = some w0 := by
                rw [← htail1 p.toNat (Nat.le_refl _), List.getElem?_eq_getElem (by omega)]
              s_split
              · have hfl0 : (w0 &&& 0x80000000#32) = 0#32 := by assumption
                obtain ⟨w0', cref, hrem2, hw0_s, hcr_s, _, hcr_lt, hcr_ref, hrem_next⟩ :=
                  wsStepNonbin hrem1 (by omega) (by rw [hw0_eq, Option.getD_some]; exact hfl0)
                have hw0_id : w0' = w0 := Option.some.inj (hw0_s.symm.trans hw0_eq)
                subst hw0_id
                have hcr_eq1 :
                    st1.core.wstk[(p + (1 : BitVec 64)).toNat]'(by rw [hp1]; omega) = cref := by
                  have hs : st1.core.wstk[p.toNat + 1]? = some cref :=
                    (htail1 (p.toNat + 1) (by omega)).trans hcr_s
                  rw [← hp1, List.getElem?_eq_getElem (by rw [hp1]; omega)] at hs
                  exact Option.some.inj hs
                s_to_group
                refine wp_join_group (ts := [i64, i64])
                  (fun (p', q', ()) m2 =>
                    p.toNat < p'.toNat ∧ RbInner1Inv c F_cur st l.toNat off sz pn p' q' m2 R)
                  (fun _ ⟨p', q', ⟨⟩⟩ m2 ⟨hpp', h2⟩ => by
                    s_steps; exact hJ1 (pn, ovf, p', q', ()) m2 (by dsimp only; omega) h2)
                  (fun Jnb hNb => ?_)
                s_split
                · have hq1 : (q + (1 : BitVec 64)).toNat = q.toNat + 1 := by
                    rw [BitVec.toNat_add, FullSubstTactics.bv64_one_toNat,
                      Nat.mod_eq_of_lt (by omega)]
                  have hq2 : (q + (2 : BitVec 64)).toNat = q.toNat + 2 := by
                    rw [BitVec.toNat_add, FullSubstTactics.bv64_two_toNat,
                      Nat.mod_eq_of_lt (by omega)]
                  have hp11 : (p + (1 : BitVec 64) + (1 : BitVec 64)).toNat = p.toNat + 2 := by
                    rw [BitVec.toNat_add, hp1, FullSubstTactics.bv64_one_toNat,
                      Nat.mod_eq_of_lt (by omega)]
                  s_steps
                  let wstk2 := (st1.core.wstk.set q.toNat w0).set (q.toNat + 1) cref
                  let st2 : FullState := { st1 with core := { st1.core with wstk := wstk2 } }
                  have hwstk2_len : wstk2.length = c.wcap := by simp [wstk2, hwsl1]
                  have hlen2 : st2.LengthsOk c := ⟨{ hcl1 with wstk_len_arr := hwstk2_len }, hsl1⟩
                  have hkept2 : WatchSliceOk F_cur (withWstk st.core st2.core.wstk) l.toNat off
                      ((q + (2 : BitVec 64)).toNat - off) := by
                    rw [hq2, show q.toNat + 2 - off = (q.toNat - off) + 2 by omega]
                    refine wsAppendLarge (k := withWstk st.core st1.core.wstk)
                      (Nat.le_refl _) (fun _ r => r) (fun idx hidx => by
                        dsimp only [st2, wstk2, withWstk]
                        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)])
                      hkept1
                      (by dsimp only [st2, wstk2, withWstk]
                          rw [show off + (q.toNat - off) = q.toNat by omega]
                          rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega)])
                      (by dsimp only [st2, wstk2, withWstk]
                          rw [show off + (q.toNat - off) + 1 = q.toNat + 1 by omega]
                          exact List.getElem?_set_self (by rw [List.length_set, hwsl1]; omega))
                      hfl0 hcr_lt hcr_ref
                  have hlm2 : RbLmCov c st2 off (q + (2 : BitVec 64)).toNat pn.toNat := by
                    intro x hx hnz
                    rcases hlm1 x hx hnz with ⟨idx, hi1, hi2, hf, hv⟩ | hpb
                    · left; refine ⟨idx, hi1, by omega, ?_, ?_⟩
                      · dsimp only [st2, wstk2]
                        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
                        exact hf
                      · dsimp only [st2, wstk2]
                        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
                        exact hv
                    · exact Or.inr hpb
                  have hm2_eq : wstk2 = (st1.core.wstk.set q.toNat w0).set
                      (q + (1 : BitVec 64)).toNat
                      ((st1.core.wstk.set q.toNat w0)[(p + (1 : BitVec 64)).toNat]'(by
                        rw [List.length_set, hp1]; omega)) := by
                    have hval : (st1.core.wstk.set q.toNat w0)[(p + (1 : BitVec 64)).toNat]'(by
                        rw [List.length_set, hp1]; omega) = cref := by
                      rw [List.getElem_set_ne (by rw [hp1]; omega)]; exact hcr_eq1
                    dsimp only [wstk2]; rw [hq1, hval]
                  refine hNb _ _ ⟨by rw [hp11]; omega, st2, hag1, hlen2,
                    by rw [hq2]; omega, by rw [hp11, hq2]; omega, by rw [hp11]; omega, hpn_le,
                    fun idx hidx => by
                      dsimp only [st2, wstk2]
                      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
                      exact htail1 idx (by rw [hp11] at hidx; omega),
                    fun idx hidx => by
                      dsimp only [st2, wstk2]
                      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
                      exact hout1 idx hidx,
                    by rw [hp11, show off + sz - (p.toNat + 2) = off + sz - p.toNat - 2 by omega]
                       exact hrem_next,
                    hkept2, hlm2, hpa1, ?_⟩
                  dsimp only [st2]; rw [hm2_eq]; assumption
                · exfalso
                  try rw [hwv0_eq, hwv1_eq] at hc
                  try rw [BitVec.toNat_add, FullSubstTactics.bv64_one_toNat] at hc
                  rw [Nat.mod_eq_of_lt (by omega)] at hc
                  try rw [Nat.mod_eq_of_lt (by omega)] at hc
                  omega
              · have hfl_ne : (w0 &&& 0x80000000#32) ≠ 0#32 := by assumption
                obtain ⟨w0', hw0_s, hfl_bin, hne_ff, hot_lt, hent_bin, hrem_next⟩ :=
                  wsStepBin hrem1 (by omega) (by rw [hw0_eq, Option.getD_some]; exact hfl_ne)
                have hw0_id : w0' = w0 := Option.some.inj (hw0_s.symm.trans hw0_eq)
                subst hw0_id
                let ot := w0 &&& 0x7FFFFFFF#32
                have hot_nat : ot.toNat < 2 * st.core.cur_vars := hot_lt
                let rot := st1.core.repr[ot.toNat]'(by omega)
                have hrot_eq : st.core.repr[ot.toNat]?.getD 0#32 = rot := by
                  have hget1 : st1.core.repr[ot.toNat]?.getD 0#32 = rot := by
                    dsimp only [rot]; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                  rw [hrp1] at hget1; exact hget1
                have hrot_lt : rot.toNat < 2 * st.core.cur_vars := by
                  rw [← hrot_eq]; exact FullReprEquiv.lt hrepr hot_lt
                have hrot_eqv : LitEquiv (cnfOfClauses F_cur) ot.toNat rot.toNat := by
                  rw [← hrot_eq]; exact FullReprEquiv.litEquiv hrepr hot_lt
                have hent_sub : (cnfOfClauses F_cur).EntailsClause
                    (cnfClause [(st.core.repr[l.toNat]'(by omega)).toNat, rot.toNat]) :=
                  entails_bin_subst hrl_eqv hrot_eqv hent_bin
                have hrem_p1 : WatchSliceOk F_cur st.core l.toNat
                    (p + (1 : BitVec 64)).toNat (off + sz - (p + (1 : BitVec 64)).toNat) := by
                  rw [hp1, show off + sz - (p.toNat + 1) = off + sz - p.toNat - 1 by omega]
                  exact hrem_next
                s_to_group
                refine wp_join_group (ts := [i32])
                  (fun (rot_v, ()) m_r => rot_v = rot ∧ (FullMem c st1 ⋆ R) m_r)
                  (fun _ ⟨rot_v, ⟨⟩⟩ m_r ⟨hrot_v, hm_r⟩ => ?_)
                  (fun Jrot hJrot => ?_)
                · subst hrot_v; s_to_group
                  refine wp_join_group (ts := [i64, .bool, i64])
                    (fun (pn', _ovf', q', ()) m2 =>
                      RbInner1Inv c F_cur st l.toNat off sz pn' (p + (1 : BitVec 64)) q' m2 R)
                    (fun _ ⟨pn', ovf', q', ⟨⟩⟩ m2 h2 => by
                      s_steps
                      exact hJ1 (pn', ovf', p + (1 : BitVec 64), q', ()) m2 (by dsimp only; omega)
                        h2)
                    (fun Jbin hBin => ?_)
                  s_to_group
                  refine wp_join_group (ts := []) (fun () m_e => (FullMem c st1 ⋆ R) m_e)
                    (fun _ ⟨⟩ m_e hm_e => ?_)
                    (fun Jelse hElse => ?_)
                  · s_to_group
                    refine wp_join_group (ts := [i64, .bool])
                      (fun (pn', _ovf', ()) m2 =>
                        RbInner1Inv c F_cur st l.toNat off sz pn' (p + (1 : BitVec 64)) q m2 R)
                      (fun _ ⟨pn', ovf', ⟨⟩⟩ m2 h2 => by
                        s_steps; exact hBin (pn', ovf', q, ()) m2 h2)
                      (fun Jlc hLc => ?_)
                    s_split
                    · s_to_group
                      refine wp_join_group (ts := [])
                        (fun () m_nb => ∃ nb' : BitVec 64,
                          (FullMem c { st1 with core := { st1.core with num_binary := nb' } } ⋆ R)
                            m_nb)
                        (fun _ ⟨⟩ m_nb ⟨nb', hnb⟩ => ?_)
                        (fun Jnb hNb => ?_)
                      · let st2 : FullState :=
                          { st1 with core := { st1.core with num_binary := nb' } }
                        have hlen2 : st2.LengthsOk c := ⟨{ hcl1 with wstk_len_arr := hwsl1 }, hsl1⟩
                        s_to_group
                        refine wp_join_group (ts := [i64, .bool])
                          (fun (pn', _ovf', ()) m2 =>
                            RbInner1Inv c F_cur st l.toNat off sz pn' (p + (1 : BitVec 64)) q m2 R)
                          (fun _ ⟨pn', ovf', ⟨⟩⟩ m2 h2 => by
                            s_steps; exact hLc (pn', ovf', ()) m2 h2)
                          (fun Jsc hSc => ?_)
                        s_split
                        · s_to_group
                          refine wp_join_group (ts := [i64, .bool])
                            (fun (pn', _ovf', ()) m2 =>
                              RbInner1Inv c F_cur st l.toNat off sz pn'
                                (p + (1 : BitVec 64)) q m2 R)
                            (fun _ ⟨pn', ovf', ⟨⟩⟩ m2 h2 => by
                              s_steps; exact hSc (pn', ovf', ()) m2 h2)
                            (fun Jrot2 hRot2 => ?_)
                          s_split
                          · have hrot_lm :
                                (BitVec.setWidth 64 rot).toNat < st1.core.lit_mark.length := by
                              rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega), hlml1]; omega
                            s_to_group
                            refine wp_join_group (ts := [i64, .bool])
                              (fun (pn', _ovf', ()) m2 =>
                                RbInner1Inv c F_cur st l.toNat off sz pn'
                                  (p + (1 : BitVec 64)) q m2 R)
                              (fun _ ⟨pn', ovf', ⟨⟩⟩ m2 h2 => by
                                s_steps; exact hRot2 (pn', ovf', ()) m2 h2)
                              (fun Jlm hLm => ?_)
                            s_split
                            · s_to_group
                              refine wp_join_group (ts := [i64, .bool])
                                (fun (pn', _ovf', ()) m2 =>
                                  RbInner1Inv c F_cur st l.toNat off sz pn'
                                    (p + (1 : BitVec 64)) q m2 R)
                                (fun _ ⟨pn', ovf', ⟨⟩⟩ m2 h2 => by
                                  s_steps; exact hLm (pn', ovf', ()) m2 h2)
                                (fun Jpn hPn => ?_)
                              s_split
                              · have hpn_lt : pn.toNat < 2 * st.core.cur_vars := by
                                  rw [Nat.mod_eq_of_lt (by omega),
                                    Nat.mod_eq_of_lt (by omega)] at hc
                                  omega
                                have hpn1 : (pn + 1#64).toNat = pn.toNat + 1 := by
                                  rw [BitVec.toNat_add, bv64_one_nat, Nat.mod_eq_of_lt (by omega)]
                                s_steps
                                let lm3 := st1.core.lit_mark.set rot.toNat
                                  (st1.core.lit_mark[rot.toNat]'(by omega) ||| 2#8)
                                let ws1' := st1.scratch.work_stk1.set pn.toNat
                                  (st.core.repr[l.toNat]'(by omega))
                                let ws2' := st1.scratch.work_stk2.set pn.toNat rot
                                let st3 : FullState :=
                                  { core := { st1.core with lit_mark := lm3, num_binary := nb' }
                                    scratch := { st1.scratch with work_stk1 := ws1',
                                                                  work_stk2 := ws2' } }
                                have hlen3 : st3.LengthsOk c :=
                                  ⟨{ hcl1 with lit_mark_len := by simp [st3, lm3, hlml1] },
                                   { hsl1 with work_stk1_len := by simp [st3, ws1', hws1l1],
                                               work_stk2_len := by simp [st3, ws2', hws2l1] }⟩
                                have hlm3 : RbLmCov c st3 off q.toNat (pn + 1#64).toNat := by
                                  intro x hx hnz; dsimp only [st3, lm3, ws2'] at hnz ⊢
                                  by_cases hxr : x = rot.toNat
                                  · subst hxr; right; refine ⟨pn.toNat, by omega, ?_⟩
                                    rw [List.getElem?_set_self (by omega), Option.getD_some]
                                  · rw [List.getElem?_set_ne (Ne.symm hxr)] at hnz
                                    rcases hlm1 x hx hnz with h1 | ⟨k, hk, hkeq⟩
                                    · exact Or.inl h1
                                    · right; refine ⟨k, by omega, ?_⟩
                                      rw [List.getElem?_set_ne (by omega)]; exact hkeq
                                have hpa3 : RbPaOk F_cur st st3 (pn + 1#64).toNat := by
                                  intro k hk; dsimp only [st3, ws1', ws2']
                                  by_cases hkp : k = pn.toNat
                                  · subst hkp
                                    rw [List.getElem?_set_self (by omega),
                                      List.getElem?_set_self (by omega),
                                      Option.getD_some, Option.getD_some]
                                    exact ⟨hrl_lt, hrot_lt, hent_sub⟩
                                  · rw [List.getElem?_set_ne (Ne.symm hkp),
                                      List.getElem?_set_ne (Ne.symm hkp)]
                                    exact hpa1 k (by omega)
                                have hrot64 : (BitVec.setWidth 64 rot).toNat = rot.toNat := by
                                  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                                have hlm3_eq : st1.core.lit_mark.set
                                    (BitVec.setWidth 64 rot).toNat
                                    (BitVec.setWidth 8 (BitVec.setWidth 32
                                      (st1.core.lit_mark[(BitVec.setWidth 64 rot).toNat]'hrot_lm)
                                      ||| 2#32)) = lm3 := by
                                  dsimp only [lm3]
                                  have hget : st1.core.lit_mark[(BitVec.setWidth 64 rot).toNat]'
                                      hrot_lm = st1.core.lit_mark[rot.toNat]'(by omega) :=
                                    Option.some.inj (by
                                      rw [← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem,
                                        hrot64])
                                  rw [bv8_trunc_or2, hget]
                                  exact congrArg (st1.core.lit_mark.set · _) hrot64
                                refine hPn (pn + 1#64, ovf, ()) _
                                  ⟨st3, hag1, hlen3, hq_lo, by omega, by omega, by omega,
                                   fun idx hidx => htail1 idx (by omega), hout1, hrem_p1,
                                   hkept1, hlm3, hpa3, ?_⟩
                                dsimp only [st3, ws1', ws2']; rw [← hlm3_eq]; assumption
                              · s_steps
                                exact hPn (pn, true, ()) m_nb
                                  ⟨st2, hag1, hlen2, hq_lo, by omega, by omega, hpn_le,
                                   fun idx hidx => htail1 idx (by omega), hout1, hrem_p1,
                                   hkept1, hlm1, hpa1, hnb⟩
                            · s_steps
                              exact hLm (pn, ovf, ()) m_nb
                                ⟨st2, hag1, hlen2, hq_lo, by omega, by omega, hpn_le,
                                 fun idx hidx => htail1 idx (by omega), hout1, hrem_p1,
                                 hkept1, hlm1, hpa1, hnb⟩
                          · s_steps
                            exact hRot2 (pn, true, ()) m_nb
                              ⟨st2, hag1, hlen2, hq_lo, by omega, by omega, hpn_le,
                               fun idx hidx => htail1 idx (by omega), hout1, hrem_p1,
                               hkept1, hlm1, hpa1, hnb⟩
                        · s_steps
                          exact hSc (pn, ovf, ()) m_nb
                            ⟨st2, hag1, hlen2, hq_lo, by omega, by omega, hpn_le,
                             fun idx hidx => htail1 idx (by omega), hout1, hrem_p1,
                             hkept1, hlm1, hpa1, hnb⟩
                      · s_split
                        · s_steps; exact hNb () _ ⟨st1.core.num_binary - 1#64, by assumption⟩
                        · s_steps; exact hNb () m_e ⟨st1.core.num_binary, hm_e⟩
                    · s_steps
                      exact hLc (pn, ovf, ()) m_e
                        ⟨st1, hag1, hlen1, hq_lo, by omega, by omega, hpn_le,
                         fun idx hidx => htail1 idx (by omega), hout1, hrem_p1,
                         hkept1, hlm1, hpa1, hm_e⟩
                  · s_split
                    · s_split
                      · have hot_lm :
                            (BitVec.setWidth 64 ot).toNat < st1.core.lit_mark.length := by
                          rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega), hlml1]; omega
                        have hot64 : (BitVec.setWidth 64 ot).toNat = ot.toNat := by
                          rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                        s_to_group
                        refine wp_join_group (ts := [i64])
                          (fun (q', ()) m2 =>
                            RbInner1Inv c F_cur st l.toNat off sz pn (p + (1 : BitVec 64)) q' m2 R)
                          (fun _ ⟨q', ⟨⟩⟩ m2 h2 => by s_steps; exact hBin (pn, ovf, q', ()) m2 h2)
                          (fun Jth hTh => ?_)
                        s_split
                        · have hq1 : (q + (1 : BitVec 64)).toNat = q.toNat + 1 := by
                            rw [BitVec.toNat_add, FullSubstTactics.bv64_one_toNat,
                              Nat.mod_eq_of_lt (by omega)]
                          s_steps
                          let lm2 := st1.core.lit_mark.set ot.toNat
                            (st1.core.lit_mark[ot.toNat]'(by omega) ||| 1#8)
                          let st2 : FullState :=
                            { st1 with core := { st1.core with
                                lit_mark := lm2, wstk := st1.core.wstk.set q.toNat w0 } }
                          have hlen2 : st2.LengthsOk c :=
                            ⟨{ hcl1 with lit_mark_len := by simp [st2, lm2, hlml1],
                                         wstk_len_arr := by simp [st2, hwsl1] }, hsl1⟩
                          have hkept2 : WatchSliceOk F_cur (withWstk st.core st2.core.wstk)
                              l.toNat off ((q + (1 : BitVec 64)).toNat - off) := by
                            rw [hq1, show q.toNat + 1 - off = (q.toNat - off) + 1 by omega]
                            exact wsAppendBin (k := withWstk st.core st1.core.wstk)
                              (Nat.le_refl _) (fun _ r => r)
                              (fun idx hidx => by
                                dsimp only [st2, withWstk]; rw [List.getElem?_set_ne (by omega)])
                              hkept1
                              (by dsimp only [st2, withWstk]
                                  rw [show off + (q.toNat - off) = q.toNat by omega]
                                  exact List.getElem?_set_self (by omega))
                              hfl_bin hne_ff hot_lt hent_bin
                          have hlm2 : RbLmCov c st2 off (q + (1 : BitVec 64)).toNat pn.toNat := by
                            intro x hx hnz; dsimp only [st2, lm2] at hnz ⊢
                            by_cases hxot : x = ot.toNat
                            · subst hxot; left; refine ⟨q.toNat, hq_lo, by omega, ?_, ?_⟩
                              · rw [List.getElem?_set_self (by omega), Option.getD_some]
                                exact hfl_bin
                              · rw [List.getElem?_set_self (by omega), Option.getD_some]
                            · rw [List.getElem?_set_ne (Ne.symm hxot)] at hnz
                              rcases hlm1 x hx hnz with ⟨idx, hi1, hi2, hf, hv⟩ | hpb
                              · left; refine ⟨idx, hi1, by omega, ?_, ?_⟩
                                · rw [List.getElem?_set_ne (by omega)]; exact hf
                                · rw [List.getElem?_set_ne (by omega)]; exact hv
                              · exact Or.inr hpb
                          have hlm2_eq : st1.core.lit_mark.set (BitVec.setWidth 64 ot).toNat
                              (BitVec.setWidth 8 (BitVec.setWidth 32
                                (st1.core.lit_mark[(BitVec.setWidth 64 ot).toNat]'hot_lm)
                                ||| 1#32)) = lm2 := by
                            dsimp only [lm2]
                            have hget : st1.core.lit_mark[(BitVec.setWidth 64 ot).toNat]'hot_lm =
                                st1.core.lit_mark[ot.toNat]'(by omega) :=
                              Option.some.inj (by
                                rw [← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem, hot64])
                            rw [bv8_trunc_or1, hget]
                            exact congrArg (st1.core.lit_mark.set · _) hot64
                          refine hTh (q + (1 : BitVec 64), ()) _
                            ⟨st2, hag1, hlen2, by omega, by omega, by omega, hpn_le,
                             fun idx hidx => by
                               dsimp only [st2]; rw [List.getElem?_set_ne (by omega)]
                               exact htail1 idx (by omega),
                             fun idx hidx => by
                               dsimp only [st2]; rw [List.getElem?_set_ne (by omega)]
                               exact hout1 idx hidx,
                             hrem_p1, hkept2, hlm2, hpa1, ?_⟩
                          dsimp only [st2]; rw [← hlm2_eq]; assumption
                        · s_to_group
                          refine wp_join_group (ts := [])
                            (fun () m_nb => ∃ nb' : BitVec 64,
                              (FullMem c { st1 with core := { st1.core with num_binary := nb' } }
                                ⋆ R) m_nb)
                            (fun _ ⟨⟩ m_nb ⟨nb', hnb⟩ => by
                              let st2 : FullState :=
                                { st1 with core := { st1.core with num_binary := nb' } }
                              exact hTh (q, ()) m_nb
                                ⟨st2, hag1, ⟨{ hcl1 with wstk_len_arr := hwsl1 }, hsl1⟩,
                                 hq_lo, by omega, by omega, hpn_le,
                                 fun idx hidx => htail1 idx (by omega), hout1, hrem_p1,
                                 hkept1, hlm1, hpa1, hnb⟩)
                            (fun Jt3 hT3 => by
                              s_split
                              · s_split
                                · s_steps
                                  exact hT3 () _ ⟨st1.core.num_binary - 1#64, by assumption⟩
                                · s_steps; exact hT3 () m_r ⟨st1.core.num_binary, hm_r⟩
                              · s_steps; exact hT3 () m_r ⟨st1.core.num_binary, hm_r⟩)
                      · s_steps; exact hElse () m_r hm_r
                    · s_steps; exact hElse () m_r hm_r
                · s_split
                  · s_steps; exact hJrot (rot, ()) m1 ⟨rfl, hm1⟩
                  · exfalso
                    change ¬ ot.toNat < 2 * (s0.core.cur_vars % 2 ^ 64) % 2 ^ 64 at hc
                    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hc; omega
            · rw [hwv0_eq, hwv1_eq, Nat.mod_eq_of_lt (by omega)] at hc
              have hp_end : p.toNat = off + sz := by omega
              have hq_hi : q.toNat ≤ off + sz := by omega
              clear hrem1 htail1 hJ1 hqp hp_hi
              s_to_group
              refine wp_loop_inv
                (fun (ci, ()) m2 => ∃ st2 : FullState,
                  AgreesExcept rbMask st st2 ∧ st2.LengthsOk c ∧
                  st2.core.wstk = st1.core.wstk ∧ st2.core.num_binary = st1.core.num_binary ∧
                  st2.scratch.work_stk1 = st1.scratch.work_stk1 ∧
                  st2.scratch.work_stk2 = st1.scratch.work_stk2 ∧
                  off ≤ ci.toNat ∧ ci.toNat ≤ q.toNat ∧
                  (∀ x < 2 * c.max_vars, st2.core.lit_mark[x]?.getD 0#8 ≠ 0#8 →
                    (∃ idx, ci.toNat ≤ idx ∧ idx < q.toNat ∧
                      (st2.core.wstk[idx]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32 ∧
                      (st2.core.wstk[idx]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat = x) ∨
                    (∃ k, k < pn.toNat ∧ (st2.scratch.work_stk2[k]?.getD 0#32).toNat = x)) ∧
                  (FullMem c st2 ⋆ R) m2)
                (fun (ci, ()) _ => q.toNat - ci.toNat) ?_ ?_
              · intro J2 hJ2; s_steps
                have h0_eq : ∀ (h : (l <<< (1 : BitVec 64)).toNat < st.core.wvec.length),
                    (BitVec.setWidth 64 (st.core.wvec[(l <<< (1 : BitVec 64)).toNat]'h)).toNat =
                    off :=
                  fun _ => by rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega), hoff_eq]
                refine hJ2 _ m1 ⟨st1, hag1, hlen1, rfl, rfl, rfl, rfl,
                  Nat.le_of_eq (h0_eq _).symm,
                  Nat.le_trans (Nat.le_of_eq (h0_eq _)) hq_lo, ?_, hm1⟩
                intro x hx hnz
                rcases hlm1 x hx hnz with ⟨idx, hi1, hi2, hf, hv⟩ | hpb
                · exact Or.inl ⟨idx, Nat.le_trans (Nat.le_of_eq (h0_eq _)) hi1, hi2, hf, hv⟩
                · exact Or.inr hpb
              · rintro J2 ⟨ci, ⟨⟩⟩ m2
                  ⟨st2, hag2, hlen2, hws_eq2, hnb_eq2, hws1_eq2, hws2_eq2, hci_lo, hci_hi,
                   hlm2, hm2⟩ hJ2
                have hcl2 := hlen2.core_ok; have hsl2 := hlen2.scratch_ok
                have hwsl2 := hcl2.wstk_len_arr; have hlml2 := hcl2.lit_mark_len
                s_split
                · have hci_lt : ci.toNat < q.toNat := hc
                  have hci1 : (ci + 1#64).toNat = ci.toNat + 1 := by
                    rw [BitVec.toNat_add, bv64_one_nat, Nat.mod_eq_of_lt (by omega)]
                  s_to_group
                  refine wp_join_group (ts := [])
                    (fun () m2' => ∃ st2' : FullState,
                      AgreesExcept rbMask st st2' ∧ st2'.LengthsOk c ∧
                      st2'.core.wstk = st1.core.wstk ∧ st2'.core.num_binary = st1.core.num_binary ∧
                      st2'.scratch.work_stk1 = st1.scratch.work_stk1 ∧
                      st2'.scratch.work_stk2 = st1.scratch.work_stk2 ∧
                      off ≤ (ci + 1#64).toNat ∧ (ci + 1#64).toNat ≤ q.toNat ∧
                      (∀ x < 2 * c.max_vars, st2'.core.lit_mark[x]?.getD 0#8 ≠ 0#8 →
                        (∃ idx, (ci + 1#64).toNat ≤ idx ∧ idx < q.toNat ∧
                          (st2'.core.wstk[idx]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32 ∧
                          (st2'.core.wstk[idx]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat = x) ∨
                        (∃ k, k < pn.toNat ∧ (st2'.scratch.work_stk2[k]?.getD 0#32).toNat = x)) ∧
                      (FullMem c st2' ⋆ R) m2')
                    (fun _ ⟨⟩ m2' h2' => by
                      s_steps; exact hJ2 (ci + 1#64, ()) m2' (by dsimp only; omega) h2')
                    (fun Jc hC => ?_)
                  s_split
                  · have hf_ne : (st2.core.wstk[ci.toNat]'(by omega) &&& 0x80000000#32) ≠ 0#32 := by
                      assumption
                    have hbin_lt : (st2.core.wstk[ci.toNat]'(by omega) &&& 0x7FFFFFFF#32).toNat <
                        2 * st.core.cur_vars := by
                      have hb := wsBinLtOfFlag hkept1 ci.toNat hci_lo (by omega)
                        (by dsimp only [withWstk]
                            rw [← hws_eq2, List.getElem?_eq_getElem (by omega), Option.getD_some]
                            exact hf_ne)
                      dsimp only [withWstk] at hb
                      rwa [← hws_eq2, List.getElem?_eq_getElem (by omega), Option.getD_some] at hb
                    have hbin_lt_b : (BitVec.setWidth 64
                        (st2.core.wstk[ci.toNat]'(by omega) &&& 0x7FFFFFFF#32)).toNat <
                        st2.core.lit_mark.length := by
                      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; omega
                    s_steps
                    let clit := (st2.core.wstk[ci.toNat]'(by omega) &&& 0x7FFFFFFF#32).toNat
                    have hclit64 : ∀ h, (BitVec.setWidth 64
                        (st2.core.wstk[ci.toNat]'h &&& 0x7FFFFFFF#32)).toNat = clit := fun _ => by
                      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                    let st2' : FullState :=
                      { st2 with core :=
                          { st2.core with lit_mark := st2.core.lit_mark.set clit 0#8 } }
                    have hlm2' : ∀ x < 2 * c.max_vars, st2'.core.lit_mark[x]?.getD 0#8 ≠ 0#8 →
                        (∃ idx, (ci + 1#64).toNat ≤ idx ∧ idx < q.toNat ∧
                          (st2'.core.wstk[idx]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32 ∧
                          (st2'.core.wstk[idx]?.getD 0#32 &&& 0x7FFFFFFF#32).toNat = x) ∨
                        (∃ k, k < pn.toNat ∧ (st2'.scratch.work_stk2[k]?.getD 0#32).toNat = x) := by
                      intro x hx hnz; dsimp only [st2'] at hnz ⊢
                      by_cases hxc : x = clit
                      · subst hxc; rw [List.getElem?_set_self (by omega), Option.getD_some] at hnz
                        exact absurd rfl hnz
                      · rw [List.getElem?_set_ne (Ne.symm hxc)] at hnz
                        rcases hlm2 x hx hnz with ⟨idx, hi1, hi2, hf, hv⟩ | hpb
                        · left; have hne_ci : idx ≠ ci.toNat := by
                            rintro rfl
                            rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hv
                            exact hxc hv.symm
                          exact ⟨idx, by omega, hi2, hf, hv⟩
                        · exact Or.inr hpb
                    refine hC () _
                      ⟨st2', hag2, ⟨{ hcl2 with lit_mark_len := by simp [st2', hlml2] }, hsl2⟩,
                       hws_eq2, hnb_eq2, hws1_eq2, hws2_eq2, by omega, by omega, hlm2', ?_⟩
                    dsimp only [st2']; rw [← hclit64]
                    try rw [show (0#8 : BitVec 8) = BitVec.setWidth 8 (0 : BitVec 32) from rfl]
                    assumption
                  · have hf_eq : (st2.core.wstk[ci.toNat]'(by omega) &&& 0x80000000#32) = 0#32 := by
                      assumption
                    s_steps
                    exact hC () m2
                      ⟨st2, hag2, hlen2, hws_eq2, hnb_eq2, hws1_eq2, hws2_eq2, by omega, by omega,
                       fun x hx hnz => by
                         rcases hlm2 x hx hnz with ⟨idx, hi1, hi2, hf, hv⟩ | hpb
                         · left; have hne_ci : idx ≠ ci.toNat := by
                             rintro rfl
                             rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hf
                             exact hf hf_eq
                           exact ⟨idx, by omega, hi2, hf, hv⟩
                         · exact Or.inr hpb,
                       hm2⟩
                · have hlm2a : ∀ x < 2 * c.max_vars, st2.core.lit_mark[x]?.getD 0#8 ≠ 0#8 →
                      ∃ k, 0 ≤ k ∧ k < pn.toNat ∧
                        (st2.scratch.work_stk2[k]?.getD 0#32).toNat = x := by
                    intro x hx hnz
                    rcases hlm2 x hx hnz with ⟨idx, hi1, hi2, _⟩ | ⟨k, hk, heq⟩
                    · have : ¬ ci.toNat < q.toNat := hc; omega
                    · exact ⟨k, Nat.zero_le _, hk, heq⟩
                  s_to_group
                  refine wp_loop_inv
                    (fun (ci2, ()) m2b => ∃ st2b : FullState,
                      AgreesExcept rbMask st st2b ∧ st2b.LengthsOk c ∧
                      st2b.core.wstk = st1.core.wstk ∧ st2b.core.num_binary = st1.core.num_binary ∧
                      st2b.scratch.work_stk1 = st1.scratch.work_stk1 ∧
                      st2b.scratch.work_stk2 = st1.scratch.work_stk2 ∧
                      ci2.toNat ≤ pn.toNat ∧
                      (∀ x < 2 * c.max_vars, st2b.core.lit_mark[x]?.getD 0#8 ≠ 0#8 →
                        ∃ k, ci2.toNat ≤ k ∧ k < pn.toNat ∧
                          (st2b.scratch.work_stk2[k]?.getD 0#32).toNat = x) ∧
                      (FullMem c st2b ⋆ R) m2b)
                    (fun (ci2, ()) _ => pn.toNat - ci2.toNat) ?_ ?_
                  · intro J2b hJ2b; s_steps
                    exact hJ2b (0#64, ()) m2 ⟨st2, hag2, hlen2, hws_eq2, hnb_eq2, hws1_eq2,
                      hws2_eq2, Nat.zero_le _, hlm2a, hm2⟩
                  · rintro J2b ⟨ci2, ⟨⟩⟩ m2b
                      ⟨st2b, hag2b, hlen2b, hws2b, hnb2b, hw1_2b, hw2_2b, hci2_le, hlm2b, hm2b⟩
                      hJ2b
                    have hcl2b := hlen2b.core_ok; have hsl2b := hlen2b.scratch_ok
                    have hlml2b := hcl2b.lit_mark_len; have hws2l2b := hsl2b.work_stk2_len
                    s_split
                    · have hci2_lt : ci2.toNat < pn.toNat := hc
                      have hci2_1 : (ci2 + 1#64).toNat = ci2.toNat + 1 := by
                        rw [BitVec.toNat_add, bv64_one_nat, Nat.mod_eq_of_lt (by omega)]
                      have hpb_lt_v : (st2b.scratch.work_stk2[ci2.toNat]'(by omega)).toNat <
                          2 * st.core.cur_vars := by
                        have h0 := (hpa1 ci2.toNat hci2_lt).2.1
                        rwa [← hw2_2b, List.getElem?_eq_getElem (by omega), Option.getD_some] at h0
                      have hpb_lm : (BitVec.setWidth 64
                          (st2b.scratch.work_stk2[ci2.toNat]'(by omega))).toNat <
                          st2b.core.lit_mark.length := by
                        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega), hlml2b]; omega
                      s_steps
                      let pblit := (st2b.scratch.work_stk2[ci2.toNat]'(by omega)).toNat
                      have hpblit64 : ∀ h, (BitVec.setWidth 64
                          (st2b.scratch.work_stk2[ci2.toNat]'h)).toNat = pblit := fun _ => by
                        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                      let st2b' : FullState :=
                        { st2b with core := { st2b.core with
                            lit_mark := st2b.core.lit_mark.set pblit 0#8 } }
                      refine hJ2b (ci2 + 1#64, ()) _ (by dsimp only; omega)
                        ⟨st2b', hag2b, ⟨{ hcl2b with lit_mark_len := by simp [st2b', hlml2b] },
                            hsl2b⟩,
                         hws2b, hnb2b, hw1_2b, hw2_2b, by omega,
                         fun x hx hnz => by
                           dsimp only [st2b'] at hnz ⊢
                           by_cases hxp : x = pblit
                           · subst hxp
                             rw [List.getElem?_set_self (by omega), Option.getD_some] at hnz
                             exact absurd rfl hnz
                           · rw [List.getElem?_set_ne (Ne.symm hxp)] at hnz
                             obtain ⟨k, hk1, hk2, hkeq⟩ := hlm2b x hx hnz
                             have hne_k : k ≠ ci2.toNat := by
                               rintro rfl
                               rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hkeq
                               exact hxp hkeq.symm
                             exact ⟨k, by omega, hk2, hkeq⟩,
                         ?_⟩
                      dsimp only [st2b']; rw [← hpblit64]
                      try rw [show (0#8 : BitVec 8) = BitVec.setWidth 8 (0 : BitVec 32) from rfl]
                      assumption
                    · have hlm_zero : ∀ x < 2 * c.max_vars,
                          st2b.core.lit_mark[x]?.getD 0#8 = 0#8 :=
                        fun x hx => Classical.byContradiction fun hnz => by
                          obtain ⟨k, hk1, hk2, _⟩ := hlm2b x hx hnz
                          have : ¬ ci2.toNat < pn.toNat := hc; omega
                      s_to_group
                      refine wp_loop_inv
                        (fun (ci3, ()) m3 => ∃ st3 : FullState,
                          AgreesExcept rbMask st st3 ∧ st3.LengthsOk c ∧
                          st3.core.lit_mark = st2b.core.lit_mark ∧
                          st3.core.num_binary = st1.core.num_binary ∧
                          st3.scratch.work_stk1 = st1.scratch.work_stk1 ∧
                          st3.scratch.work_stk2 = st1.scratch.work_stk2 ∧
                          q.toNat ≤ ci3.toNat ∧ ci3.toNat ≤ off + sz ∧
                          (∀ idx, (idx < q.toNat ∨ off + sz ≤ idx) →
                            st3.core.wstk[idx]? = st1.core.wstk[idx]?) ∧
                          (FullMem c st3 ⋆ R) m3)
                        (fun (ci3, ()) _ => off + sz - ci3.toNat) ?_ ?_
                      · intro J3 hJ3; s_steps
                        exact hJ3 (q, ()) m2b ⟨st2b, hag2b, hlen2b, rfl, hnb2b, hw1_2b, hw2_2b,
                          Nat.le_refl _, hq_hi, fun _ _ => by rw [hws2b], hm2b⟩
                      · rintro J3 ⟨ci3, ⟨⟩⟩ m3
                          ⟨st3, hag3, hlen3, hlm_eq3, hnb_eq3, hw1_eq3, hw2_eq3, hci3_lo, hci3_hi,
                           hwstk3, hm3⟩ hJ3
                        have hcl3 := hlen3.core_ok; have hsl3 := hlen3.scratch_ok
                        have hwsl3 := hcl3.wstk_len_arr
                        s_split
                        · have hci3_lt : ci3.toNat < off + sz := by
                            rw [hwv0_eq, hwv1_eq, Nat.mod_eq_of_lt (by omega)] at hc; omega
                          have hci3_1 : (ci3 + 1#64).toNat = ci3.toNat + 1 := by
                            rw [BitVec.toNat_add, bv64_one_nat, Nat.mod_eq_of_lt (by omega)]
                          s_steps
                          let st3' : FullState := { st3 with core := { st3.core with
                              wstk := st3.core.wstk.set ci3.toNat 0xFFFFFFFF#32 } }
                          exact hJ3 (ci3 + 1#64, ()) _ (by dsimp only; omega)
                            ⟨st3', hag3, ⟨{ hcl3 with wstk_len_arr := by simp [st3', hwsl3] },
                                hsl3⟩,
                             hlm_eq3, hnb_eq3, hw1_eq3, hw2_eq3, by omega, by omega,
                             fun idx hidx => by
                               dsimp only [st3']; rw [List.getElem?_set_ne (by omega)]
                               exact hwstk3 idx hidx,
                             by assumption⟩
                        · have hwvl3 := hcl3.wvec_len
                          have hwu_idx : (2 * l.toNat + 1) % 2 ^ 64 < st3.core.wvec.length := by
                            have : st3.core.wvec = st.core.wvec := hag3.get (·.core.wvec)
                            rw [this, hwvl, Nat.mod_eq_of_lt (by omega)]; omega
                          let wu4 := st3.core.wusable +
                            ((st.core.wvec[(l <<< (1 : BitVec 64)).toNat]'h2l_lt).setWidth 64 +
                             (st.core.wvec[((l <<< (1 : BitVec 64)) + 1).toNat]'h2l1_lt).setWidth
                               64 - q)
                          let st4 : FullState :=
                            { st with
                              core := { st.core with
                                lit_mark := st3.core.lit_mark
                                wvec := st.core.wvec.set (2 * l.toNat + 1)
                                  (BitVec.ofNat 32 (q.toNat - off))
                                wstk := st3.core.wstk, wusable := wu4
                                num_binary := st3.core.num_binary }
                              scratch := { st.scratch with
                                work_stk1 := st3.scratch.work_stk1
                                work_stk2 := st3.scratch.work_stk2 } }
                          have hsp4 : FullSparseInvW c F0 F_cur st4 :=
                            rewriteBins_slice_preserves_fullSparse hsp (hcv ▸ hl_lt) hq_lo hq_hi
                              hcl3.wstk_len_arr hcl3.lit_mark_len hsl3.work_stk1_len
                              hsl3.work_stk2_len
                              (fun x hx => by rw [hlm_eq3]; exact hlm_zero x hx)
                              (fun idx hidx => by
                                have hidx' : idx < q.toNat ∨ off + sz ≤ idx :=
                                  hidx.elim (fun h1 => Or.inl (by omega)) (fun h2 => Or.inr h2)
                                rw [hwstk3 idx hidx']; exact hout1 idx hidx)
                              (wsRelocate (k := withWstk st.core st1.core.wstk)
                                (by rw [CNF.entails_def]; exact fun _ h => h) (Nat.le_refl _)
                                (fun _ r => r)
                                (fun idx hidx => by
                                  dsimp only [withWstk]
                                  exact hwstk3 (off + idx) (Or.inl (by omega)))
                                hkept1)
                          have hwvec_eq4 :
                              st3.core.wvec.set ((l <<< (1 : BitVec 64)) + 1).toNat
                                (BitVec.setWidth 32 (q -
                                  (st.core.wvec[(l <<< (1 : BitVec 64)).toNat]'h2l_lt).setWidth
                                    64)) =
                              st.core.wvec.set (2 * l.toNat + 1)
                                (BitVec.ofNat 32 (q.toNat - off)) := by
                            have hw3 : st3.core.wvec = st.core.wvec := hag3.get (·.core.wvec)
                            have hbv_eq : BitVec.setWidth 32 (q -
                                (st.core.wvec[(l <<< (1 : BitVec 64)).toNat]'h2l_lt).setWidth 64) =
                                BitVec.ofNat 32 (q.toNat - off) := by
                              apply BitVec.eq_of_toNat_eq
                              have hoff_s : (BitVec.setWidth 64
                                  (st.core.wvec[(l <<< (1 : BitVec 64)).toNat]'h2l_lt)).toNat =
                                  off := by
                                rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega), hoff_eq]
                              have hsub : (q -
                                  (st.core.wvec[(l <<< (1 : BitVec 64)).toNat]'h2l_lt).setWidth
                                    64).toNat = q.toNat - off := by
                                rw [BitVec.toNat_sub]; omega
                              rw [BitVec.toNat_setWidth, hsub, BitVec.toNat_ofNat]
                            rw [hw3, h2l1_eq, hbv_eq]
                          have heq_s : ({ st3 with core := { st3.core with
                              wvec := st3.core.wvec.set ((l <<< (1 : BitVec 64)) + 1).toNat
                                (BitVec.setWidth 32 (q -
                                  (st.core.wvec[(l <<< (1 : BitVec 64)).toNat]'h2l_lt).setWidth 64))
                              wusable := wu4 } } : FullState) = st4 := by
                            rw [hwvec_eq4]; exact rb_st4_eq st st3 hag3 _ _
                          have hpa4 : RbPaOk F_cur st st4 pn.toNat := by
                            intro k hk; dsimp only [st4]; rw [hw1_eq3, hw2_eq3]; exact hpa1 k hk
                          s_split
                          · c0_hsteps
                            let st_oom : FullState :=
                              { st4 with core := { st4.core with oom := 1#64 } }
                            have hsp_oom := fullSparseInvW_with_oom hsp4 1#64
                            have heq_oom : ({ ({ st3 with core := { st3.core with
                                wvec := st3.core.wvec.set ((l <<< (1 : BitVec 64)) + 1).toNat
                                  (BitVec.setWidth 32 (q -
                                    (st.core.wvec[(l <<< (1 : BitVec 64)).toNat]'h2l_lt).setWidth
                                      64))
                                wusable := wu4 } } : FullState) with
                                core := { ({ st3 with core := { st3.core with
                                  wvec := st3.core.wvec.set ((l <<< (1 : BitVec 64)) + 1).toNat
                                    (BitVec.setWidth 32 (q -
                                      (st.core.wvec[(l <<< (1 : BitVec 64)).toNat]'h2l_lt).setWidth
                                        64))
                                  wusable := wu4 } } : FullState).core with
                                  oom := 1#64 } } : FullState) = st_oom := by
                              rw [heq_s]
                            exact hQ true st_oom _ hsp_oom hl0_st hcv hfl hrepr
                              (fun h => by cases h) (by rw [← heq_oom]; assumption)
                          · have hm4 : (FullMem c st4 ⋆ R) m := by rw [← heq_s]; assumption
                            s_to_group
                            refine wp_loop_inv
                              (fun (ci4, ()) m5 => ∃ st5 : FullState,
                                FullSparseInvW c F0 F_cur st5 ∧
                                st5.core.cur_vars = s0.core.cur_vars ∧ st5.core.cur_level = 0 ∧
                                st5.core.fuel = s0.core.fuel ∧ FullReprEquiv F_cur st5 ∧
                                st5.scratch.work_stk1 = st4.scratch.work_stk1 ∧
                                st5.scratch.work_stk2 = st4.scratch.work_stk2 ∧
                                ci4.toNat ≤ pn.toNat ∧ (FullMem c st5 ⋆ R) m5)
                              (fun (ci4, ()) _ => pn.toNat - ci4.toNat) ?_ ?_
                            · intro J4 hJ4; s_steps
                              exact hJ4 (0#64, ()) _
                                ⟨st4, hsp4, hcv, hl0_st, hfl, hrepr, rfl, rfl, Nat.zero_le _, hm4⟩
                            · rintro J4 ⟨ci4, ⟨⟩⟩ m5
                                ⟨st5, hsp5, hcv5, hl05, hfl5, hrepr5, hw1_5, hw2_5, hci4_le, hm5⟩
                                hJ4
                              have hcl5 := hsp5.1.core_ok; have hsl5 := hsp5.1.scratch_ok
                              have hws1l5 := hsl5.work_stk1_len; have hws2l5 := hsl5.work_stk2_len
                              have hcv_le5 := hcl5.cur_vars_le
                              s_split
                              · have hci4_lt : ci4.toNat < pn.toNat := hc
                                have hci4_1 : (ci4 + 1#64).toNat = ci4.toNat + 1 := by
                                  rw [BitVec.toNat_add, bv64_one_nat, Nat.mod_eq_of_lt (by omega)]
                                obtain ⟨ha_lt, hb_lt, hab_ent⟩ := hpa4 ci4.toNat hci4_lt
                                have h1_get : st5.scratch.work_stk1[ci4.toNat]'(by omega) =
                                    st4.scratch.work_stk1[ci4.toNat]?.getD 0#32 := by
                                  rw [← hw1_5, List.getElem?_eq_getElem (by omega),
                                    Option.getD_some]
                                have h2_get : st5.scratch.work_stk2[ci4.toNat]'(by omega) =
                                    st4.scratch.work_stk2[ci4.toNat]?.getD 0#32 := by
                                  rw [← hw2_5, List.getElem?_eq_getElem (by omega),
                                    Option.getD_some]
                                have hpa_lt5 :
                                    (st5.scratch.work_stk1[ci4.toNat]'(by omega)).toNat <
                                      2 * st5.core.cur_vars := by
                                  rw [h1_get, hcv5, ← hcv]; exact ha_lt
                                have hab_ent5 : (cnfOfClauses F_cur).EntailsClause
                                    (cnfClause
                                      [(st5.scratch.work_stk1[ci4.toNat]'(by omega)).toNat,
                                       (st5.scratch.work_stk2[ci4.toNat]'(by omega)).toNat]) := by
                                  rw [h1_get, h2_get]; exact hab_ent
                                s_to_group
                                refine wp_join_group (ts := [])
                                  (fun () m6 => ∃ st6 : FullState,
                                    FullSparseInvW c F0 F_cur st6 ∧
                                    st6.core.cur_vars = s0.core.cur_vars ∧
                                    st6.core.cur_level = 0 ∧ st6.core.fuel = s0.core.fuel ∧
                                    FullReprEquiv F_cur st6 ∧
                                    st6.scratch.work_stk1 = st4.scratch.work_stk1 ∧
                                    st6.scratch.work_stk2 = st4.scratch.work_stk2 ∧
                                    (FullMem c st6 ⋆ R) m6)
                                  (fun _ ⟨⟩ m6 ⟨st6, hsp6, hcv6, hl06, hfl6, hrepr6, hw1_6, hw2_6,
                                      hm6⟩ => by
                                    s_steps
                                    exact hJ4 (ci4 + 1#64, ()) m6 (by dsimp only; omega)
                                      ⟨st6, hsp6, hcv6, hl06, hfl6, hrepr6, hw1_6, hw2_6, by omega,
                                       hm6⟩)
                                  (fun J4s hJ4s => ?_)
                                s_split
                                · have heq_ab : st5.scratch.work_stk1[ci4.toNat]'(by omega) =
                                      st5.scratch.work_stk2[ci4.toNat]'(by omega) := by assumption
                                  s_steps; s_call hAddUnit
                                  refine ⟨c, F0, F_cur, st5, R, rfl, hsp5.1, hsp5.2.1,
                                    fun _ => entails_unit_of_dup (by simpa [heq_ab] using hab_ent5),
                                    hm5, ?_⟩
                                  intro ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 st6 hlen6
                                    hw6 hcl6 hfail6 _ hm6
                                  have hsp6 := fullSparseInvW_afterAddUnit hsp5 hlen6 hw6
                                  have hrepr6 : FullReprEquiv F_cur st6 :=
                                    fun l' hl' => hrepr5 l' hl'
                                  s_split
                                  · s_steps
                                    exact hJ4s () m6
                                      ⟨st6, hsp6, hcv5, hcl6, hfl5, hrepr6, hw1_5, hw2_5, hm6⟩
                                  · s_steps
                                    exact hQ false st6 m6 hsp6 hcl6 hcv5 hfl5 hrepr6
                                      (fun _ => (hfail6 hpa_lt5
                                        (by cases ok <;>
                                          first | rfl | contradiction | exact absurd rfl hc)).1)
                                      hm6
                                · s_steps; s_call hAddBin
                                  refine ⟨c, F0, F_cur, st5, R, rfl, hsp5.1, hsp5.2.1, hl05,
                                    fun _ _ => hab_ent5, hm5, ?_⟩
                                  intro r _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 st6 hlen6 hw6 _
                                    hr20 _ hm6
                                  have hsp6 := fullSparseInvW_afterAddBin hsp5 hlen6 hw6
                                  have hrepr6 : FullReprEquiv F_cur st6 :=
                                    fun l' hl' => hrepr5 l' hl'
                                  s_split
                                  · s_steps
                                    exact hQ false st6 m6 hsp6 hl05 hcv5 hfl5 hrepr6
                                      (fun _ => (hr20 hc).1) hm6
                                  · s_to_group
                                    refine wp_join_group (ts := [])
                                      (fun () m6' => (FullMem c st6 ⋆ R) m6')
                                      (fun _ ⟨⟩ m6' hm6' => by
                                        c0_hsteps
                                        let st6o : FullState :=
                                          { st6 with core := { st6.core with oom := 1#64 } }
                                        exact hQ true st6o _ (fullSparseInvW_with_oom hsp6 1#64)
                                          hl05 hcv5 hfl5 hrepr6 (fun h => by cases h)
                                          (by assumption))
                                      (fun Joom hOom => ?_)
                                    s_split
                                    · s_steps; exact hOom () m6 hm6
                                    · s_split
                                      · s_steps; exact hOom () m6 hm6
                                      · s_steps
                                        exact hJ4s () m6
                                          ⟨st6, hsp6, hcv5, hl05, hfl5, hrepr6, hw1_5, hw2_5, hm6⟩
                              · s_steps
                                exact hJ (l + 1#64, ()) m5 (by dsimp only; omega)
                                  ⟨st5, hsp5, hcv5, hl05, hfl5, hrepr5, by omega, hm5⟩
      · s_steps
        exact hQ true st ml hsp hl0_st hcv hfl hrepr (fun h => by cases h) hml

end RewriteBinsProof

/-! ## 5. `full_subst_rewrite_ar_m5_wp` (`Full.fullSubstRewriteArSpec`) -/

section RewriteArProof

private theorem arenaBlockReplace_l0 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s' : FullState} {cref : Nat}
    (hsp : FullSparseInvW c F0 F_cur s) (hl0 : s.core.cur_level = 0) (hsc : s'.scratch = s.scratch)
    (hc : { s'.core with
        arena := s.core.arena, lit_mark := s.core.lit_mark,
        arena_garbage := s.core.arena_garbage } = s.core)
    (href : cref ∈ fullArenaClauseRefs s) (har'_len : s'.core.arena.length = c.arena_cap)
    (hlm'_len : s'.core.lit_mark.length = 2 * c.max_vars)
    (hlm'_zero : ∀ x < 2 * c.max_vars, s'.core.lit_mark[x]?.getD 0#8 = 0#8)
    (hout : ∀ i, i < cref ∨ cref + 3 + fullArenaClauseSize s cref ≤ i →
      s'.core.arena[i]? = s.core.arena[i]?)
    (hnxt_cref : fullArenaNextOff s'.core.arena s.core.arena_len cref =
      fullArenaNextOff s.core.arena s.core.arena_len cref)
    (hsz_cref : 3 ≤ (s'.core.arena[cref + 2]?.getD 0#32).toNat ∧
      (s'.core.arena[cref + 2]?.getD 0#32).toNat ≤ fullArenaClauseSize s cref)
    (hshrk_cref : (s'.core.arena[cref]?.getD 0#32 &&& 0x00800000#32) ≠ 0#32 →
      ∃ t, cref + 3 + (s'.core.arena[cref + 2]?.getD 0#32).toNat ≤ t ∧ t < s.core.arena_len ∧
        s'.core.arena[t]? = some 0xFFFFFFFF#32)
    (hlive_cref : (s'.core.arena[cref]?.getD 0#32 &&& 0x00080000#32) = 0#32 →
      (∀ j < (s'.core.arena[cref + 2]?.getD 0#32).toNat,
        (s'.core.arena[cref + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
      (∀ i j, i < j → j < (s'.core.arena[cref + 2]?.getD 0#32).toNat →
        (s'.core.arena[cref + 3 + i]?.getD 0#32).toNat / 2 ≠
        (s'.core.arena[cref + 3 + j]?.getD 0#32).toNat / 2) ∧
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause ((List.range (s'.core.arena[cref + 2]?.getD 0#32).toNat).map fun j =>
          (s'.core.arena[cref + 3 + j]?.getD 0#32).toNat))) :
    FullSparseInvW c F0 F_cur s' ∧ fullArenaClauseRefs s' = fullArenaClauseRefs s ∧
      s'.core.arena_len = s.core.arena_len := by
  have hout' : ∀ i, i < cref ∨ cref + 3 + fullArenaClauseSizeCore s.core cref ≤ i →
      s'.core.arena[i]? = s.core.arena[i]? := hout
  have hsz_le' : (s'.core.arena[cref + 2]?.getD 0#32).toNat ≤
      fullArenaClauseSizeCore s.core cref := hsz_cref.2
  rw [fullState_eq_replace_arena_lm_ag hsc hc]
  let s1 : FullState :=
    { s with core := { s.core with
        arena := s'.core.arena, lit_mark := s'.core.lit_mark,
        arena_garbage := s'.core.arena_garbage } }
  have hcl := hsp.1.core_ok; have hw := hsp.2.1; have ha := hw.arena
  have hcref_wf := ha.refs_wf cref href
  have hblk_eq : ∀ r ∈ fullArenaClauseRefsCore s.core, r ≠ cref →
      ∀ i, r ≤ i → i < fullArenaNextOff s.core.arena s.core.arena_len r →
        s'.core.arena[i]? = s.core.arena[i]? := fun r hr hne i hi1 hi2 => by
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have := fullArenaScanRefs_disjoint hr href hlt; exact hout' i (Or.inl (by omega))
    · have := fullArenaScanRefs_disjoint href hr hgt
      have := hcref_wf.2.2.1; exact hout' i (Or.inr (by omega))
  have hnxt : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaNextOff s1.core.arena s.core.arena_len r =
        fullArenaNextOff s.core.arena s.core.arena_len r := fun r hr => by
    by_cases hrc : r = cref
    · subst r; exact hnxt_cref
    · have hrwf := ha.refs_wf r hr; have hbe := hblk_eq r hr hrc
      exact fullArenaNextOff_congr_block (hbe r (Nat.le_refl r) (by omega))
        (hbe (r + 2) (by omega) (by omega)) fun i hi1 hi2 => hbe i (by omega) hi2
  have hrefs : fullArenaClauseRefsCore s1.core = fullArenaClauseRefsCore s.core :=
    fullArenaClauseRefsCore_congr rfl hnxt
  have hother : ∀ r ∈ fullArenaClauseRefsCore s.core, r ≠ cref →
      fullArenaClauseSizeCore s1.core r = fullArenaClauseSizeCore s.core r ∧
      fullArenaClauseGarbCore s1.core r = fullArenaClauseGarbCore s.core r ∧
      fullArenaClauseLitsCore s1.core r = fullArenaClauseLitsCore s.core r := fun r hr hne => by
    have hrwf := ha.refs_wf r hr; have hbe := hblk_eq r hr hne
    have hszr : fullArenaClauseSizeCore s1.core r = fullArenaClauseSizeCore s.core r := by
      unfold fullArenaClauseSizeCore s1; rw [hbe (r + 2) (by omega) (by omega)]
    refine ⟨hszr,
      by unfold fullArenaClauseGarbCore fullArenaHdrCore s1; rw [hbe r (Nat.le_refl r) (by omega)],
      fullArenaClauseLitsCore_eq_of_hold
        (by have := hcl.arena_len_le; have := hcl.arena_len_arr; omega)
        (by dsimp only [s1]; rw [har'_len]; have := hcl.arena_len_le; omega) hszr
        fun j hj => hbe (r + 3 + j) (by omega) (by omega)⟩
  have hclits : fullArenaClauseLitsCore s1.core cref =
      (List.range (s'.core.arena[cref + 2]?.getD 0#32).toNat).map fun j =>
        (s'.core.arena[cref + 3 + j]?.getD 0#32).toNat := by
    unfold fullArenaClauseLitsCore fullArenaClauseSizeCore
    exact list_drop_take_map_toNat_eq_range
      (by dsimp only [s1]; rw [har'_len]; have := hcl.arena_len_le; omega)
  have hc_ng_z : fullArenaClauseGarbCore s1.core cref = false →
      (s'.core.arena[cref]?.getD 0#32 &&& 0x00080000#32) = 0#32 := fun hng => by
    unfold fullArenaClauseGarbCore fullArenaHdrCore s1 at hng; simpa [bne_iff_ne] using hng
  have ha1 : FullArenaClausesInv c F_cur s1.core := by
    refine ⟨ha.len_ok, ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs] at hr; dsimp only [s1] at hnxt ⊢; rw [hnxt r hr]
      by_cases hrc : r = cref
      · subst r; unfold fullArenaClauseSizeCore; dsimp only [s1]
        exact ⟨hcref_wf.1, hsz_cref.1, by omega, hcref_wf.2.2.2.1, hcref_wf.2.2.2.2⟩
      · rw [(hother r hr hrc).1]; exact ha.refs_wf r hr
    · intro r hr hsh; rw [hrefs] at hr
      by_cases hrc : r = cref
      · subst r; exact hshrk_cref hsh
      · have hrwf := ha.refs_wf r hr; have hbe := hblk_eq r hr hrc
        have hsh0 : (fullArenaHdrCore s.core r &&& 0x00800000#32) ≠ 0#32 := by
          unfold fullArenaHdrCore s1 at hsh; rwa [hbe r (Nat.le_refl r) (by omega)] at hsh
        obtain ⟨t, ht1, ht2, hsent⟩ := ha.shrk_term r hr hsh0
        obtain ⟨t0, ht0_lo, _, _, ht0_sent⟩ :=
          fullArenaNextOff_hits_sentinel hrwf.1 hsh0 ht1 ht2 hsent
        rw [(hother r hr hrc).1]
        exact ⟨t0, ht0_lo, by dsimp only [s1]; omega,
          by dsimp only [s1]; rw [hbe t0 (by omega) (by omega)]; exact ht0_sent⟩
    · intro r hr hng1; rw [hrefs] at hr
      by_cases hrc : r = cref
      · subst r; intro l hl; rw [hclits, List.mem_map] at hl; rcases hl with ⟨j, hj, rfl⟩
        exact (hlive_cref (hc_ng_z hng1)).1 j (List.mem_range.mp hj)
      · rw [(hother r hr hrc).2.1] at hng1; rw [(hother r hr hrc).2.2]; exact ha.lits_lt r hr hng1
    · intro r hr hng1; rw [hrefs] at hr
      by_cases hrc : r = cref
      · subst r; rw [hclits]; exact (hlive_cref (hc_ng_z hng1)).2.2
      · rw [(hother r hr hrc).2.1] at hng1; rw [(hother r hr hrc).2.2]; exact ha.entails r hr hng1
  have hnd1 : FullArenaVarsNodup s1 := fun r hr hng1 => by
    change r ∈ fullArenaClauseRefsCore s1.core at hr; rw [hrefs] at hr
    by_cases hrc : r = cref
    · subst r; change ((fullArenaClauseLitsCore s1.core cref).map (· / 2)).Nodup
      rw [hclits, List.map_map]; exact nodup_range_map_of_pairwise (hlive_cref (hc_ng_z hng1)).2.1
    · obtain ⟨_, hgb, hlt⟩ := hother r hr hrc
      change fullArenaClauseGarbCore s1.core r = false at hng1; rw [hgb] at hng1
      change ((fullArenaClauseLitsCore s1.core r).map (· / 2)).Nodup; rw [hlt]
      exact hsp.2.2.2.1 r hr hng1
  have hw1 : FullWitnessInv c F0 F_cur s1.core :=
    { hw with
      arena := ha1
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl
        (fun r hr => by change r ∈ fullArenaClauseRefsCore s1.core; rw [hrefs]; exact hr)
      reason_inv := fun idx hidx hne => absurd
        (hw.level0_rsn_none idx hidx (by have := hw.lvl_le idx hidx; omega)) hne
      reason_lit_mem := fun idx hidx hne => absurd
        (hw.level0_rsn_none idx hidx (by have := hw.lvl_le idx hidx; omega)) hne }
  exact ⟨⟨⟨{ hcl with arena_len_arr := har'_len, lit_mark_len := hlm'_len }, hsp.1.scratch_ok⟩,
    hw1, ⟨hsp.2.2.1.1, hlm'_zero⟩, hnd1,
    hsp.2.2.2.2.1.of_pres ⟨rfl, rfl⟩
      (fun r hr => by change r ∈ fullArenaClauseRefsCore s1.core; rw [hrefs]; exact hr),
    hsp.2.2.2.2.2⟩, hrefs, rfl⟩

private theorem overwriteGarb_l0 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s' : FullState} {cref : Nat}
    (hsp : FullSparseInvW c F0 F_cur s) (hl0 : s.core.cur_level = 0) (hsc : s'.scratch = s.scratch)
    (hc : { s'.core with
        arena := s.core.arena, lit_mark := s.core.lit_mark,
        arena_garbage := s.core.arena_garbage } = s.core)
    (href : cref ∈ fullArenaClauseRefs s) (har'_len : s'.core.arena.length = c.arena_cap)
    (hlm'_len : s'.core.lit_mark.length = 2 * c.max_vars)
    (hlm'_zero : ∀ x < 2 * c.max_vars, s'.core.lit_mark[x]?.getD 0#8 = 0#8)
    (hhdr' : s'.core.arena[cref]? = some (fullArenaHdr s cref ||| 0x00080000#32))
    (hsz' : s'.core.arena[cref + 2]? = s.core.arena[cref + 2]?)
    (hout : ∀ i, i < cref ∨ cref + 3 + fullArenaClauseSize s cref ≤ i →
      s'.core.arena[i]? = s.core.arena[i]?) :
    FullSparseInvW c F0 F_cur s' ∧ fullArenaClauseRefs s' = fullArenaClauseRefs s ∧
      s'.core.arena_len = s.core.arena_len := by
  have hcl := hsp.1.core_ok; have ha := hsp.2.1.arena; have hwf := ha.refs_wf cref href
  have hget_c : s.core.arena[cref]? = some (fullArenaHdr s cref) := by
    have : cref < s.core.arena.length := by
      have := hcl.arena_len_le; have := hcl.arena_len_arr; omega
    unfold fullArenaHdr fullArenaHdrCore; rw [List.getElem?_eq_getElem this, Option.getD_some]
  refine arenaBlockReplace_l0 hsp hl0 hsc hc href
    har'_len hlm'_len hlm'_zero hout ?_ (by rw [hsz']; exact ⟨hwf.2.1, Nat.le_refl _⟩) ?_ ?_
  · have h1 : ¬ (cref + 3 > s.core.arena_len) := by omega
    have h2 : ¬ (cref + 3 + (s.core.arena[cref + 2]?.getD 0#32).toNat > s.core.arena_len) := by
      unfold fullArenaClauseSizeCore at hwf; omega
    unfold fullArenaNextOff
    simp only [h1, ↓reduceIte, hsz', h2, hhdr', Option.getD_some, bit23_or_garb]
    rw [hget_c, Option.getD_some]; split
    · exact fullArenaSkipShrk_congr fun i hi _ => hout i (Or.inr hi)
    · rfl
  · intro hsh; rw [hhdr', Option.getD_some, bit23_or_garb] at hsh
    obtain ⟨t, ht1, ht2, hsent⟩ := ha.shrk_term cref href hsh
    refine ⟨t, by rw [hsz']; exact ht1, ht2, ?_⟩
    rw [hout t (Or.inr (by
      change cref + 3 + (s.core.arena[cref + 2]?.getD 0#32).toNat ≤ t; exact ht1))]
    exact hsent
  · intro hng; rw [hhdr', Option.getD_some] at hng; exact absurd hng (bit19_or_garb_ne0 _)

private theorem inPlaceShrink_l0 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s' : FullState} {cref nsz : Nat}
    (hsp : FullSparseInvW c F0 F_cur s) (hl0 : s.core.cur_level = 0) (hsc : s'.scratch = s.scratch)
    (hc : { s'.core with arena := s.core.arena, lit_mark := s.core.lit_mark } = s.core)
    (hcref : cref ∈ fullArenaClauseRefs s) (hng : fullArenaClauseGarb s cref = false)
    (hnsz3 : 3 ≤ nsz) (hnsz_le : nsz ≤ fullArenaClauseSize s cref)
    (har'_len : s'.core.arena.length = c.arena_cap)
    (hlm'_len : s'.core.lit_mark.length = 2 * c.max_vars)
    (hlm'_zero : ∀ x < 2 * c.max_vars, s'.core.lit_mark[x]?.getD 0#8 = 0#8)
    (hhdr' : s'.core.arena[cref]? = some
      (if nsz < fullArenaClauseSize s cref ∧ (fullArenaHdr s cref &&& 0x00800000#32) = 0#32 then
        fullArenaHdr s cref ||| 0x00800000#32 else fullArenaHdr s cref))
    (hsz' : s'.core.arena[cref + 2]? = some (BitVec.ofNat 32 nsz))
    (hpad_old : ∀ j, nsz ≤ j → j < fullArenaClauseSize s cref - 1 →
      s'.core.arena[cref + 3 + j]? = s.core.arena[cref + 3 + j]?)
    (hlast_sent : nsz < fullArenaClauseSize s cref →
      (fullArenaHdr s cref &&& 0x00800000#32) = 0#32 →
      s'.core.arena[cref + 3 + fullArenaClauseSize s cref - 1]? = some 0xFFFFFFFF#32)
    (hlast_keep : nsz < fullArenaClauseSize s cref →
      (fullArenaHdr s cref &&& 0x00800000#32) ≠ 0#32 →
      s'.core.arena[cref + 3 + fullArenaClauseSize s cref - 1]? =
        s.core.arena[cref + 3 + fullArenaClauseSize s cref - 1]?)
    (hout : ∀ i, i < cref ∨ cref + 3 + fullArenaClauseSize s cref ≤ i →
      s'.core.arena[i]? = s.core.arena[i]?)
    (hlits_lt' : ∀ j < nsz, (s'.core.arena[cref + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hpw' : ∀ i j, i < j → j < nsz →
      (s'.core.arena[cref + 3 + i]?.getD 0#32).toNat / 2 ≠
      (s'.core.arena[cref + 3 + j]?.getD 0#32).toNat / 2)
    (hent' : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((List.range nsz).map fun j => (s'.core.arena[cref + 3 + j]?.getD 0#32).toNat))) :
    FullSparseInvW c F0 F_cur s' ∧ fullArenaClauseRefs s' = fullArenaClauseRefs s ∧
      s'.core.arena_len = s.core.arena_len := by
  have hcl := hsp.1.core_ok; have ha := hsp.2.1.arena; have hwf := ha.refs_wf cref hcref
  let old_sz := fullArenaClauseSizeCore s.core cref
  have hold_eq : fullArenaClauseSize s cref = old_sz := rfl
  have hwf' : cref + 3 ≤ s.core.arena_len ∧ 3 ≤ old_sz ∧
      cref + 3 + old_sz ≤ fullArenaNextOff s.core.arena s.core.arena_len cref ∧
      fullArenaNextOff s.core.arena s.core.arena_len cref ≤ s.core.arena_len ∧
      (fullArenaNextOff s.core.arena s.core.arena_len cref = s.core.arena_len ∨
        fullArenaNextOff s.core.arena s.core.arena_len cref + 3 ≤ s.core.arena_len) := hwf
  rw [hold_eq] at hnsz_le hhdr' hpad_old hlast_sent hlast_keep hout
  have hnsz_lt32 : nsz < 2 ^ 32 := by
    have := (s.core.arena[cref + 2]?.getD 0#32).isLt
    have hold_sz_eq : (s.core.arena[cref + 2]?.getD 0#32).toNat = old_sz := rfl; omega
  have hsz_n : (s'.core.arena[cref + 2]?.getD 0#32).toNat = nsz := by
    rw [hsz', Option.getD_some, bv32_ofNat_toNat_lt hnsz_lt32]
  have hold_ne : ∀ j, j < old_sz →
      s.core.arena[cref + 3 + j]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := fun j hj => by
    have hbd : cref + 3 + old_sz ≤ s.core.arena.length := by
      have := hcl.arena_len_le; have := hcl.arena_len_arr; omega
    have hlt_j : cref + 3 + j < s.core.arena.length := by omega
    rw [List.getElem?_eq_getElem hlt_j, Option.getD_some]
    have hlt_v :=
      ha.lits_lt cref hcref hng _ ((mem_fullArenaClauseLitsCore_iff hbd).mpr ⟨j, hj, rfl⟩)
    have hmx := c.hmaxv; have hcv := hcl.cur_vars_le; unfold dimacsBound at hmx
    intro heq; rw [heq] at hlt_v; simp at hlt_v; omega
  refine arenaBlockReplace_l0 hsp hl0 hsc (core_eq_of_arena_lm hc)
    hcref har'_len hlm'_len hlm'_zero hout ?_ (by rw [hsz_n]; exact ⟨hnsz3, hnsz_le⟩) ?_ ?_
  · have h1 : ¬ (cref + 3 > s.core.arena_len) := by omega
    have h2 : ¬ (cref + 3 + old_sz > s.core.arena_len) := by omega
    have h2' : ¬ (cref + 3 + nsz > s.core.arena_len) := by omega
    have hold_sz_eq : (s.core.arena[cref + 2]?.getD 0#32).toNat = old_sz := rfl
    have hhdr_get : fullArenaHdr s cref = s.core.arena[cref]?.getD 0#32 := rfl
    rw [hhdr_get] at hhdr'
    by_cases hcond : nsz < old_sz ∧ (s.core.arena[cref]?.getD 0#32 &&& 0x00800000#32) = 0#32
    · simp only [hcond.1, hcond.2, and_self, ite_true] at hhdr'
      have hsh0 : (s.core.arena[cref]?.getD 0#32 &&& 0x00800000#32) = 0#32 := hcond.2
      unfold fullArenaNextOff
      simp only [h1, h2, h2', hsz_n, hold_sz_eq, hhdr', Option.getD_some, hsh0,
        bit23_or_shrk, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte]
      have hts := FullSubstHelpers.fullArenaSkipShrk_of_first_sentinel (ar := s'.core.arena)
        (alen := s.core.arena_len) (t := cref + 3 + old_sz - 1)
        (fuel := s.core.arena_len - (cref + 3 + nsz)) (p := cref + 3 + nsz) (by omega)
        (by omega) (hlast_sent hcond.1 hcond.2)
        (fun i hi1 hi2 => by
          have hj : i = cref + 3 + (i - (cref + 3)) := by omega
          rw [hj, hpad_old (i - (cref + 3)) (by omega) (by omega)]
          exact hold_ne (i - (cref + 3)) (by omega)) (by omega)
      have h3old : 3 ≤ old_sz := hwf'.2.1; omega
    · simp only [hcond, ite_false] at hhdr'
      by_cases hsh0 : (s.core.arena[cref]?.getD 0#32 &&& 0x00800000#32) = 0#32
      · have hnsz_eq : nsz = old_sz := by
          have : ¬ nsz < old_sz := fun hlt => hcond ⟨hlt, hsh0⟩; omega
        unfold fullArenaNextOff
        simp only [h1, h2, hsz_n, hold_sz_eq, hhdr', Option.getD_some, hsh0, ↓reduceIte, hnsz_eq]
        rfl
      · obtain ⟨t, ht1, ht2, hsent⟩ := ha.shrk_term cref hcref hsh0
        obtain ⟨t0, ht0_lo, _, ht0_nxt, ht0_sent, ht0_first⟩ :=
          FullSubstHelpers.fullArenaSkipShrk_first_sentinel (ar := s.core.arena)
            (alen := s.core.arena_len) (t := t) (fuel := s.core.arena_len - (cref + 3 + old_sz))
            (p := cref + 3 + old_sz) ht1 ht2 hsent (by omega)
        unfold fullArenaNextOff
        simp only [h1, h2, h2', hsz_n, hold_sz_eq, hhdr', Option.getD_some, hsh0, ne_eq,
          not_false_eq_true, ↓reduceIte]
        rw [ht0_nxt]
        refine FullSubstHelpers.fullArenaSkipShrk_of_first_sentinel (ar := s'.core.arena)
          (alen := s.core.arena_len) (t := t0) (fuel := s.core.arena_len - (cref + 3 + nsz))
          (p := cref + 3 + nsz) (by omega) (by omega)
          (by rw [hout t0 (Or.inr ht0_lo)]; exact ht0_sent) (fun i hi1 hi2 => ?_) (by omega)
        by_cases hmid : i < cref + 3 + old_sz
        · by_cases hlast : i = cref + 3 + old_sz - 1
          · subst i; by_cases hlt_n : nsz < old_sz
            · rw [hlast_keep hlt_n hsh0,
                show cref + 3 + old_sz - 1 = cref + 3 + (old_sz - 1) by omega]
              exact hold_ne (old_sz - 1) (by omega)
            · omega
          · have hj : i = cref + 3 + (i - (cref + 3)) := by omega
            rw [hj, hpad_old (i - (cref + 3)) (by omega) (by omega)]
            exact hold_ne (i - (cref + 3)) (by omega)
        · rw [hout i (Or.inr (by omega))]; exact ht0_first i (by omega) hi2
  · intro hsh; rw [hsz_n]; rw [hhdr', Option.getD_some] at hsh
    split at hsh
    · rename_i hcond; exact ⟨cref + 3 + old_sz - 1, by omega, by omega, hlast_sent hcond.1 hcond.2⟩
    · obtain ⟨t, ht1, ht2, hsent⟩ := ha.shrk_term cref hcref hsh
      exact ⟨t, by omega, ht2, by rw [hout t (Or.inr ht1)]; exact hsent⟩
  · intro _; rw [hsz_n]; exact ⟨hlits_lt', hpw', hent'⟩

private def RaOuterInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s0 : FullState) (p : BitVec 64) (m : Mem 64) (R : Mem 64 → Prop) : Prop :=
  ∃ st : FullState,
    FullSparseInvW c F0 F_cur st ∧
    st.core.cur_vars = s0.core.cur_vars ∧ st.core.cur_level = 0 ∧
    st.core.fuel = s0.core.fuel ∧ st.core.repr = s0.core.repr ∧
    st.core.arena_len = s0.core.arena_len ∧
    (p.toNat = st.core.arena_len ∨ p.toNat ∈ fullArenaClauseRefs st) ∧
    (FullMem c st ⋆ R) m

private def RaLoop2Core (c : FullCfg) (st st2 : FullState)
    (p : BitVec 64) (sz : Nat) (nsz : BitVec 32) (m : Mem 64) (R : Mem 64 → Prop) : Prop :=
  st2.LengthsOk c ∧ st2.scratch = st.scratch ∧
  { st2.core with arena := st.core.arena, lit_mark := st.core.lit_mark } = st.core ∧
  nsz.toNat ≤ sz ∧
  (∀ j, nsz.toNat ≤ j → j < sz →
    st2.core.arena[p.toNat + 3 + j]? = st.core.arena[p.toNat + 3 + j]?) ∧
  (∀ i, i < p.toNat + 3 ∨ p.toNat + 3 + sz ≤ i → st2.core.arena[i]? = st.core.arena[i]?) ∧
  (∀ j < sz, (st2.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat < 2 * st.core.cur_vars) ∧
  (∀ i j, i < j → j < nsz.toNat →
    (st2.core.arena[p.toNat + 3 + i]?.getD 0#32).toNat / 2 ≠
    (st2.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat / 2) ∧
  (∀ x < 2 * c.max_vars, st2.core.lit_mark[x]?.getD 0#8 ≠ 0#8 ↔
    ∃ m < nsz.toNat, (st2.core.arena[p.toNat + 3 + m]?.getD 0#32).toNat = x) ∧
  (∀ v < c.max_vars, st2.core.mrk[v]?.getD 0#8 = 0#8) ∧ (FullMem c st2 ⋆ R) m

private def RaLoop2Inv (c : FullCfg) (F_cur : List (List Nat)) (st : FullState)
    (p : BitVec 64) (sz : Nat) (k nsz : BitVec 32) (m : Mem 64) (R : Mem 64 → Prop) : Prop :=
  ∃ st2 : FullState,
    RaLoop2Core c st st2 p sz nsz m R ∧
    k.toNat ≤ sz ∧ nsz.toNat ≤ k.toNat ∧ (0 < k.toNat → 1 ≤ nsz.toNat) ∧
    (∀ j < k.toNat, ∃ m < nsz.toNat,
      LitEquiv (cnfOfClauses F_cur)
        (st.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat
        (st2.core.arena[p.toNat + 3 + m]?.getD 0#32).toNat)

private def RaLoop2Brk (c : FullCfg) (F_cur : List (List Nat)) (st : FullState)
    (p : BitVec 64) (sz : Nat) (taut : Bool) (nsz : BitVec 32)
    (m : Mem 64) (R : Mem 64 → Prop) : Prop :=
  ∃ st2 : FullState,
    RaLoop2Core c st st2 p sz nsz m R ∧
    (taut = false → 1 ≤ nsz.toNat) ∧
    (taut = false → ∀ j < sz, ∃ m < nsz.toNat,
      LitEquiv (cnfOfClauses F_cur)
        (st.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat
        (st2.core.arena[p.toNat + 3 + m]?.getD 0#32).toNat)

private def RaDoneInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s0 st : FullState) (m : Mem 64) (R : Mem 64 → Prop) : Prop :=
  ∃ st4 : FullState,
    FullSparseInvW c F0 F_cur st4 ∧
    st4.core.cur_vars = s0.core.cur_vars ∧ st4.core.cur_level = 0 ∧
    st4.core.fuel = s0.core.fuel ∧ st4.core.repr = s0.core.repr ∧
    st4.core.arena_len = s0.core.arena_len ∧
    fullArenaClauseRefs st4 = fullArenaClauseRefs st ∧
    (FullMem c st4 ⋆ R) m

private theorem ra_push_step {c : FullCfg} {F_cur : List (List Nat)}
    {st st2 : FullState} {p : BitVec 64} {sz : Nat} {k nsz l2 rl2 : BitVec 32}
    {m2' : Mem 64} {R : Mem 64 → Prop}
    (hk_lt : k.toNat < sz) (hk1 : (k + 1#32).toNat = k.toNat + 1)
    (hnsz1 : (nsz + 1#32).toNat = nsz.toNat + 1)
    (hlen2 : st2.LengthsOk c) (hsc2 : st2.scratch = st.scratch)
    (hcore2 : { st2.core with arena := st.core.arena, lit_mark := st.core.lit_mark } = st.core)
    (hnsz_le : nsz.toNat ≤ k.toNat)
    (hpad2 : ∀ j, nsz.toNat ≤ j → j < sz →
      st2.core.arena[p.toNat + 3 + j]? = st.core.arena[p.toNat + 3 + j]?)
    (hout2 : ∀ i, i < p.toNat + 3 ∨ p.toNat + 3 + sz ≤ i →
      st2.core.arena[i]? = st.core.arena[i]?)
    (hlt2 : ∀ j < sz, (st2.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat < 2 * st.core.cur_vars)
    (hpw2 : ∀ i j, i < j → j < nsz.toNat →
      (st2.core.arena[p.toNat + 3 + i]?.getD 0#32).toNat / 2 ≠
      (st2.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat / 2)
    (hent2 : ∀ j < k.toNat, ∃ m < nsz.toNat,
      LitEquiv (cnfOfClauses F_cur)
        (st.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat
        (st2.core.arena[p.toNat + 3 + m]?.getD 0#32).toNat)
    (hlm2 : ∀ x < 2 * c.max_vars, st2.core.lit_mark[x]?.getD 0#8 ≠ 0#8 ↔
      ∃ m < nsz.toNat, (st2.core.arena[p.toNat + 3 + m]?.getD 0#32).toNat = x)
    (hmrk2 : ∀ v < c.max_vars, st2.core.mrk[v]?.getD 0#8 = 0#8)
    (hcv_le : st.core.cur_vars ≤ c.max_vars)
    (hp_bd : p.toNat + 3 + sz ≤ st2.core.arena.length)
    (hl2_orig_eq : st2.core.arena[p.toNat + 3 + k.toNat]? = some l2)
    (hrl2_lt_v : rl2.toNat < 2 * st.core.cur_vars)
    (hrl2_eqv : LitEquiv (cnfOfClauses F_cur) l2.toNat rl2.toNat)
    (hlm_neg0 : st2.core.lit_mark[rl2.toNat ^^^ 1]?.getD 0#8 = 0#8)
    (hlm_pos0 : st2.core.lit_mark[rl2.toNat]?.getD 0#8 = 0#8)
    (hm2' : (FullMem c { st2 with
      core := { st2.core with
        lit_mark := st2.core.lit_mark.set rl2.toNat 1#8,
        arena := st2.core.arena.set (p.toNat + 3 + nsz.toNat) rl2 } } ⋆ R) m2') :
    RaLoop2Inv c F_cur st p sz (k + 1#32) (nsz + 1#32) m2' R := by
  have hcl2 := hlen2.core_ok; have harl2 := hcl2.arena_len_arr; have hlml2 := hcl2.lit_mark_len
  let lm2' := st2.core.lit_mark.set rl2.toNat 1#8
  let ar2' := st2.core.arena.set (p.toNat + 3 + nsz.toNat) rl2
  let st2' : FullState := { st2 with core := { st2.core with lit_mark := lm2', arena := ar2' } }
  refine ⟨st2', ⟨⟨{ hcl2 with
        arena_len_arr := by simp [st2', ar2', harl2]
        lit_mark_len := by simp [st2', lm2', hlml2] }, hlen2.scratch_ok⟩,
      hsc2, hcore2, by omega, ?_, ?_, ?_, ?_, ?_, by simpa [st2'] using hmrk2, hm2'⟩,
    by omega, by omega, fun _ => by omega, ?_⟩
  · intro j hj1 hj2; dsimp only [st2', ar2']; rw [List.getElem?_set_ne (by omega)]
    exact hpad2 j (by omega) hj2
  · intro i hi; dsimp only [st2', ar2']; rw [List.getElem?_set_ne (by omega)]; exact hout2 i hi
  · intro j hj; dsimp only [st2', ar2']
    by_cases hjn : j = nsz.toNat
    · subst hjn; rw [List.getElem?_set_self (by omega), Option.getD_some]; exact hrl2_lt_v
    · rw [List.getElem?_set_ne (by omega)]; exact hlt2 j hj
  · intro i j hij hj; dsimp only [st2', ar2']
    by_cases hj_last : j = nsz.toNat
    · subst hj_last
      rw [List.getElem?_set_self (by omega), List.getElem?_set_ne (by omega), Option.getD_some]
      intro hdv; rcases (litVar_eq_iff _ rl2.toNat).mp hdv with heq | heq
      · exact (hlm2 rl2.toNat (by omega)).mpr ⟨i, by omega, heq⟩ hlm_pos0
      · have hnx := litNeg_lt_two_mul hrl2_lt_v
        exact (hlm2 (rl2.toNat ^^^ 1) (by omega)).mpr ⟨i, by omega, heq⟩ hlm_neg0
    · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      exact hpw2 i j hij (by omega)
  · intro x hx; dsimp only [st2', lm2', ar2']; constructor
    · intro hnz
      by_cases hxr : x = rl2.toNat
      · subst hxr; refine ⟨nsz.toNat, by omega, ?_⟩
        rw [List.getElem?_set_self (by omega), Option.getD_some]
      · rw [List.getElem?_set_ne (Ne.symm hxr)] at hnz
        obtain ⟨m', hm', hm'_eq⟩ := (hlm2 x hx).mp hnz
        refine ⟨m', by omega, ?_⟩; rw [List.getElem?_set_ne (by omega)]; exact hm'_eq
    · rintro ⟨m', hm', hm'_eq⟩
      by_cases hmn : m' = nsz.toNat
      · subst hmn; rw [List.getElem?_set_self (by omega), Option.getD_some] at hm'_eq
        subst hm'_eq; rw [List.getElem?_set_self (by rw [hlml2]; exact hx), Option.getD_some]
        decide
      · rw [List.getElem?_set_ne (by omega)] at hm'_eq
        have hnz := (hlm2 x hx).mpr ⟨m', by omega, hm'_eq⟩
        by_cases hxr : x = rl2.toNat
        · subst hxr; rw [List.getElem?_set_self (by rw [hlml2]; exact hx), Option.getD_some]
          decide
        · rw [List.getElem?_set_ne (Ne.symm hxr)]; exact hnz
  · intro j hj; dsimp only [st2', ar2']
    by_cases hjk : j = k.toNat
    · subst hjk; refine ⟨nsz.toNat, by omega, ?_⟩
      rw [List.getElem?_set_self (by omega), Option.getD_some]
      have hpad_k := hpad2 k.toNat hnsz_le hk_lt
      have hl2_orig : (st.core.arena[p.toNat + 3 + k.toNat]?.getD 0#32).toNat = l2.toNat := by
        rw [← hpad_k, hl2_orig_eq, Option.getD_some]
      rwa [hl2_orig]
    · obtain ⟨m', hm', heqv⟩ := hent2 j (by omega)
      refine ⟨m', by omega, ?_⟩; rw [List.getElem?_set_ne (by omega)]; exact heqv

private theorem ra_shrink_done {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st st3 : FullState} {p : BitVec 64} {sz nsz : Nat} {ar4 : List (BitVec 32)}
    {m4 : Mem 64} {R : Mem 64 → Prop}
    (hsp : FullSparseInvW c F0 F_cur st) (hl0 : st.core.cur_level = 0)
    (hcv : st.core.cur_vars = s0.core.cur_vars) (hfl : st.core.fuel = s0.core.fuel)
    (hrp : st.core.repr = s0.core.repr) (hal : st.core.arena_len = s0.core.arena_len)
    (hp_ref : p.toNat ∈ fullArenaClauseRefs st)
    (hng : fullArenaClauseGarb st p.toNat = false) (hsz_eq : sz = fullArenaClauseSize st p.toNat)
    (hnsz3 : 3 ≤ nsz) (hnsz_le : nsz ≤ sz) (hsc3 : st3.scratch = st.scratch)
    (hcore3 : { st3.core with arena := st.core.arena, lit_mark := st.core.lit_mark } = st.core)
    (har4_len : ar4.length = c.arena_cap)
    (hlm3_len : st3.core.lit_mark.length = 2 * c.max_vars)
    (hlm3_zero : ∀ x < 2 * c.max_vars, st3.core.lit_mark[x]?.getD 0#8 = 0#8)
    (hhdr4 : ar4[p.toNat]? = some
      (if nsz < fullArenaClauseSize st p.toNat ∧
          (fullArenaHdr st p.toNat &&& 0x00800000#32) = 0#32 then
        fullArenaHdr st p.toNat ||| 0x00800000#32 else fullArenaHdr st p.toNat))
    (hsz4 : ar4[p.toNat + 2]? = some (BitVec.ofNat 32 nsz))
    (hlast_sent : nsz < fullArenaClauseSize st p.toNat →
      (fullArenaHdr st p.toNat &&& 0x00800000#32) = 0#32 →
      ar4[p.toNat + 3 + fullArenaClauseSize st p.toNat - 1]? = some 0xFFFFFFFF#32)
    (hlast_keep : nsz < fullArenaClauseSize st p.toNat →
      (fullArenaHdr st p.toNat &&& 0x00800000#32) ≠ 0#32 →
      ar4[p.toNat + 3 + fullArenaClauseSize st p.toNat - 1]? =
        st.core.arena[p.toNat + 3 + fullArenaClauseSize st p.toNat - 1]?)
    (har4_eq : ∀ i, i ≠ p.toNat → i ≠ p.toNat + 1 → i ≠ p.toNat + 2 →
      (nsz < sz → i ≠ p.toNat + 3 + sz - 1) → ar4[i]? = st3.core.arena[i]?)
    (har3_pad : ∀ j, nsz ≤ j → j < sz →
      st3.core.arena[p.toNat + 3 + j]? = st.core.arena[p.toNat + 3 + j]?)
    (har3_out : ∀ i, i < p.toNat ∨ p.toNat + 3 + sz ≤ i → st3.core.arena[i]? = st.core.arena[i]?)
    (har3_lt : ∀ j < sz, (st3.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat < 2 * st.core.cur_vars)
    (har3_pw : ∀ i j, i < j → j < nsz →
      (st3.core.arena[p.toNat + 3 + i]?.getD 0#32).toNat / 2 ≠
      (st3.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat / 2)
    (hent_n : (cnfOfClauses F_cur).EntailsClause (cnfClause
      ((List.range nsz).map fun j => (st3.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat)))
    (hm4 : (FullMem c { st3 with core := { st3.core with arena := ar4 } } ⋆ R) m4) :
    RaDoneInv c F0 F_cur s0 st m4 R := by
  let st4 : FullState := { st3 with core := { st3.core with arena := ar4 } }
  have hwf := hsp.2.1.arena.refs_wf p.toNat hp_ref
  have hsz3 : 3 ≤ sz := by rw [hsz_eq]; exact hwf.2.1
  have hcore4' :
      { st4.core with arena := st.core.arena, lit_mark := st.core.lit_mark } = st.core := by
    rcases st with ⟨c0, _⟩; rcases st3 with ⟨c3, _⟩; rcases c0; rcases c3; cases hcore3; rfl
  have har4_s : st4.core.arena = ar4 := rfl
  have hmap_eq : ((List.range nsz).map fun j => (ar4[p.toNat + 3 + j]?.getD 0#32).toNat) =
      ((List.range nsz).map fun j => (st3.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat) :=
    List.map_congr_left fun j hj => by
      have hj' := List.mem_range.mp hj
      rw [har4_eq _ (by omega) (by omega) (by omega) (fun _ => by omega)]
  obtain ⟨hsp4, hrefs4, hal4⟩ := inPlaceShrink_l0 (s' := st4)
    hsp hl0 hsc3 hcore4'
    hp_ref hng hnsz3 (hsz_eq ▸ hnsz_le) (by rw [har4_s]; exact har4_len) hlm3_len hlm3_zero
    (by rw [har4_s]; exact hhdr4) (by rw [har4_s]; exact hsz4)
    (fun j hj1 hj2 => by
      rw [hsz_eq] at hnsz_le; rw [← hsz_eq] at hj2
      rw [har4_s, har4_eq _ (by omega) (by omega) (by omega) (fun _ => by omega)]
      exact har3_pad j hj1 (by omega))
    (by rw [har4_s]; exact hlast_sent) (by rw [har4_s]; exact hlast_keep)
    (fun i hi => by
      rw [← hsz_eq] at hi
      rw [har4_s, har4_eq _ (by omega) (by omega) (by omega) (fun _ => by omega)]
      exact har3_out i hi)
    (fun j hj => by
      rw [har4_s, har4_eq _ (by omega) (by omega) (by omega) (fun _ => by omega)]
      exact har3_lt j (by omega))
    (fun i j hij hj => by
      rw [har4_s, har4_eq _ (by omega) (by omega) (by omega) (fun _ => by omega),
        har4_eq _ (by omega) (by omega) (by omega) (fun _ => by omega)]
      exact har3_pw i j hij hj)
    (by rw [har4_s, hmap_eq]; exact hent_n)
  exact ⟨st4, hsp4, (congrArg FullCoreState.cur_vars hcore4').trans hcv,
    (congrArg FullCoreState.cur_level hcore4').trans hl0,
    (congrArg FullCoreState.fuel hcore4').trans hfl,
    (congrArg FullCoreState.repr hcore4').trans hrp, hal4.trans hal, hrefs4, hm4⟩

private theorem list_getElem_of_getElem? {xs ys : List (BitVec 32)} {i j : Nat}
    {hi : i < xs.length} {hj : j < ys.length} (hij : i = j) (hq : xs[j]? = ys[j]?) :
    xs[i]'hi = ys[j]'hj := by
  subst hij; rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj] at hq
  exact Option.some.inj hq

private theorem ra_lm_zero {lm : List (BitVec 8)} {i j : Nat}
    {hi : i < lm.length} {hj : j < lm.length} (hij : i = j)
    (hc : BitVec.setWidth 32 (lm[j]'hj) = 0#32) : lm[i]?.getD 0#8 = 0#8 := by
  rw [List.getElem?_eq_getElem hi, Option.getD_some,
    show lm[i]'hi = lm[j]'hj by subst hij; rfl]
  exact bv8_setWidth32_eq_zero hc

private theorem ra_lm_ne {lm : List (BitVec 8)} {i j : Nat}
    {hi : i < lm.length} {hj : j < lm.length} (hij : i = j)
    (hc : ¬ BitVec.setWidth 32 (lm[j]'hj) = 0#32) : lm[i]?.getD 0#8 ≠ 0#8 := by
  rw [List.getElem?_eq_getElem hi, Option.getD_some,
    show lm[i]'hi = lm[j]'hj by subst hij; rfl]
  intro heq; exact hc (congrArg (BitVec.setWidth 32) heq)

/-- `full_subst_rewrite_ar_m5` satisfies canonical `Full.fullSubstRewriteArSpec` parametrically
in `Γ`, aborting immediately with `h->oom = 1ULL` on `full_add_bin == 2ULL` (`h->oom != 0ULL`)
while keeping `return false` strictly for `F0.Unsat`. -/
public theorem full_subst_rewrite_ar_m5_wp (Γ : Env)
    (hArenaNext : ∀ args m Q X, fullArenaNextSpec args m Q X →
      Γ "full_arena_next" [i64, i32] [i32] args m Q X)
    (hAddUnit : ∀ args m Q X, fullAddUnitSpec args m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] args m Q X)
    (hAddBin : ∀ args m Q X, fullAddBinSpec args m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] args m Q X) :
    ∀ args m Q X, fullSubstRewriteArSpec args m Q X →
      Func.wp Γ full_subst_rewrite_ar_m5_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s0, R, rfl, hsp0, hl0, hrepr0, hm, hQ⟩
  have hmx := c.hmaxv; have har_cap := c.harena; unfold dimacsBound at hmx har_cap
  unfold Func.wp full_subst_rewrite_ar_m5_body
  s_split
  · s_steps; exact hQ true s0 m hsp0 hl0 rfl rfl (fun h => by cases h) hm
  · s_to_group
    refine wp_loop_inv (fun (p, ()) ml => RaOuterInv c F0 F_cur s0 p ml R)
      (fun (p, ()) _ => s0.core.arena_len - p.toNat) ?_ ?_
    · intro J hJ; s_steps
      exact hJ (0#64, ()) m
        ⟨s0, hsp0, rfl, hl0, rfl, rfl, rfl, fullArenaClauseRefs_zero_mem hsp0.2.1.arena, hm⟩
    · rintro J ⟨p, ⟨⟩⟩ ml ⟨st, hsp, hcv, hl0_st, hfl, hrp, hal, hp_pos, hml⟩ hJ
      have hcl := hsp.1.core_ok; have hsl := hsp.1.scratch_ok
      have harl := hcl.arena_len_arr; have hale := hcl.arena_len_le
      have hcv_le := hcl.cur_vars_le; have hlml := hcl.lit_mark_len; have hrpl := hcl.repr_len
      have hrepr_st : FullReprEquiv F_cur st := fun l hl => by
        rw [hcv] at hl; have h0 := hrepr0 l hl; rw [hrp, hcv]; exact h0
      s_split
      · have hp_lt_alen : p.toNat < st.core.arena_len := by
          rw [Nat.mod_eq_of_lt (by omega)] at hc; omega
        have hp_ref : p.toNat ∈ fullArenaClauseRefs st := hp_pos.elim (fun he => by omega) id
        have hpwf := hsp.2.1.arena.refs_wf p.toNat hp_ref
        have hp2_eq : (p + 2#64).toNat = p.toNat + 2 := by
          rw [BitVec.toNat_add, bv64_two_nat, Nat.mod_eq_of_lt (by omega)]
        have hp2_lt : (p + 2#64).toNat < st.core.arena.length := by rw [hp2_eq, harl]; omega
        have hp_trunc : (BitVec.setWidth 32 p).toNat = p.toNat := bv32_trunc_toNat (by omega)
        have hnp_lt_next := FullSubstHelpers.fullArenaClauseRefs_next_or_end hsp.2.1.arena hp_ref
        s_steps; s_call hArenaNext
        refine ⟨c, st, R, rfl, hsp.1, hml, ?_⟩; dsimp only
        let np := BitVec.setWidth 64 (BitVec.ofNat 32
          (fullArenaNextOff st.core.arena st.core.arena_len (BitVec.setWidth 32 p).toNat))
        have hnp_nat : np.toNat = fullArenaNextOff st.core.arena st.core.arena_len p.toNat := by
          dsimp only [np]; rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, hp_trunc]
          have hnb := (fullArenaNextOff_bounds (ar := st.core.arena) (alen := st.core.arena_len)
            (cref := p.toNat) hpwf.1).2
          rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        have hnp_meas : s0.core.arena_len - np.toNat < s0.core.arena_len - p.toNat := by
          rw [hnp_nat, ← hal]
          have := fullArenaNextOff_bounds (ar := st.core.arena) (alen := st.core.arena_len)
            (cref := p.toNat) hpwf.1; omega
        have hnp_pos : np.toNat = st.core.arena_len ∨ np.toNat ∈ fullArenaClauseRefs st :=
          hnp_nat ▸ hnp_lt_next
        let hdr := st.core.arena[p.toNat]'(by omega)
        let sz32 := st.core.arena[(p + 2#64).toNat]'hp2_lt
        have hp2_get : st.core.arena[p.toNat + 2]? = some sz32 := by
          dsimp only [sz32]; rw [← hp2_eq, List.getElem?_eq_getElem hp2_lt]
        have hsz_eq : sz32.toNat = fullArenaClauseSize st p.toNat := by
          unfold fullArenaClauseSize fullArenaClauseSizeCore; rw [hp2_get, Option.getD_some]
        have hsz_core : fullArenaClauseSizeCore st.core p.toNat = sz32.toNat := hsz_eq.symm
        have hp_blk_le : p.toNat + 3 + sz32.toNat ≤ st.core.arena_len := by
          change fullArenaClauseSizeCore st.core p.toNat = sz32.toNat at hsz_core
          have := hpwf.2.2.1; have := hpwf.2.2.2.1; omega
        have hhdr_eq : fullArenaHdr st p.toNat = hdr := by
          dsimp only [hdr, fullArenaHdr, fullArenaHdrCore]
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
        s_split
        · s_steps
          exact hJ (np, ()) ml hnp_meas ⟨st, hsp, hcv, hl0_st, hfl, hrp, hal, hnp_pos, hml⟩
        · s_split
          · s_steps
            exact hJ (np, ()) ml hnp_meas ⟨st, hsp, hcv, hl0_st, hfl, hrp, hal, hnp_pos, hml⟩
          · have hng : fullArenaClauseGarb st p.toNat = false := by
              unfold fullArenaClauseGarb fullArenaClauseGarbCore
              rw [show fullArenaHdrCore st.core p.toNat = hdr from hhdr_eq,
                (by assumption : (hdr &&& 0x00080000#32) = 0#32)]; decide
            have hsz3 : 3 ≤ sz32.toNat := by have := hpwf.2.1; omega
            s_to_group
            refine wp_loop_break_group
              (fun (chg, _k1, ()) m1 => (chg = true ∨ chg = false) ∧ (FullMem c st ⋆ R) m1)
              (fun n (k, ()) m1 =>
                n = sz32.toNat - k.toNat ∧ k.toNat ≤ sz32.toNat ∧ (FullMem c st ⋆ R) m1)
              ?_ ?_ ?_
            · rintro B ⟨chg, _k1, ⟨⟩⟩ m1 ⟨_, hm1⟩
              s_split
              · s_to_group
                refine wp_loop_break_group
                  (fun (_k2, taut, nsz, ()) m2 =>
                    RaLoop2Brk c F_cur st p sz32.toNat taut nsz m2 R)
                  (fun n (k, nsz, ()) m2 =>
                    n = sz32.toNat - k.toNat ∧ RaLoop2Inv c F_cur st p sz32.toNat k nsz m2 R)
                  ?_ ?_ ?_
                · rintro B2 ⟨_k2, taut, nsz, ⟨⟩⟩ m2
                    ⟨st2, ⟨hlen2, hsc2, hcore2, hnsz_le, hpad2, hout2, hlt2, hpw2, hlm2, hmrk2,
                       hm2⟩, hnsz_pos, hent2⟩
                  s_to_group
                  refine wp_loop_inv
                    (fun (k3, ()) m3 => ∃ st3 : FullState,
                      st3.LengthsOk c ∧ st3.scratch = st.scratch ∧
                      { st3.core with arena := st.core.arena, lit_mark := st.core.lit_mark } =
                        st.core ∧
                      st3.core.arena = st2.core.arena ∧ k3.toNat ≤ nsz.toNat ∧
                      (∀ x < 2 * c.max_vars, st3.core.lit_mark[x]?.getD 0#8 ≠ 0#8 →
                        ∃ i, k3.toNat ≤ i ∧ i < nsz.toNat ∧
                          (st3.core.arena[p.toNat + 3 + i]?.getD 0#32).toNat = x) ∧
                      (∀ v < c.max_vars, st3.core.mrk[v]?.getD 0#8 = 0#8) ∧ (FullMem c st3 ⋆ R) m3)
                    (fun (k3, ()) _ => nsz.toNat - k3.toNat) ?_ ?_
                  · intro J3 hJ3; s_steps
                    refine hJ3 (0#32, ()) m2
                      ⟨st2, hlen2, hsc2, hcore2, rfl, Nat.zero_le _, ?_, hmrk2, hm2⟩
                    intro x hx hnz; obtain ⟨m', hm1', hm2'⟩ := (hlm2 x hx).mp hnz
                    exact ⟨m', Nat.zero_le _, hm1', hm2'⟩
                  · rintro J3 ⟨k3, ⟨⟩⟩ m3
                      ⟨st3, hlen3, hsc3, hcore3, har3, hk3_le, hlm3, hmrk3, hm3⟩ hJ3
                    have hcl3 := hlen3.core_ok; have harl3 := hcl3.arena_len_arr
                    have hlml3 := hcl3.lit_mark_len
                    s_split
                    · have hk3_lt : k3.toNat < nsz.toNat := hc
                      have hk3_1 := fullSubst_add_u32_toNat (k := k3) (by omega)
                      have hpk3_eq := fullSubst_off3_toNat (p := p) (k := k3) (by omega)
                      have hpk3_lt : (p + 3#64 + BitVec.setWidth 64 k3).toNat <
                          st3.core.arena.length := by rw [hpk3_eq, harl3]; omega
                      have hrl3_lt_v : (st3.core.arena[(p + 3#64 +
                          BitVec.setWidth 64 k3).toNat]'hpk3_lt).toNat < 2 * st.core.cur_vars := by
                        have hg := hlt2 k3.toNat (by omega)
                        rw [← har3, List.getElem?_eq_getElem
                          (by rw [hpk3_eq] at hpk3_lt; exact hpk3_lt), Option.getD_some] at hg
                        simpa only [hpk3_eq] using hg
                      have hrl3_lt_lm : (BitVec.setWidth 64 (st3.core.arena[(p + 3#64 +
                          BitVec.setWidth 64 k3).toNat]'hpk3_lt)).toNat <
                          st3.core.lit_mark.length := by
                        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega), hlml3]; omega
                      s_steps
                      let lm3' := st3.core.lit_mark.set (BitVec.setWidth 64 (st3.core.arena[(p +
                        3#64 + BitVec.setWidth 64 k3).toNat]'hpk3_lt)).toNat 0#8
                      let st3' : FullState :=
                        { st3 with core := { st3.core with lit_mark := lm3' } }
                      have hset_idx : (BitVec.setWidth 64 (st3.core.arena[(p + 3#64 +
                          BitVec.setWidth 64 k3).toNat]'hpk3_lt)).toNat =
                          (st3.core.arena[p.toNat + 3 + k3.toNat]'(by
                            rw [harl3]; omega)).toNat := by
                        have hlt32 := (st3.core.arena[(p + 3#64 +
                          BitVec.setWidth 64 k3).toNat]'hpk3_lt).isLt
                        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                        exact congrArg BitVec.toNat (bv32_getElem_congr hpk3_eq)
                      refine hJ3 (k3 + 1#32, ()) _ (by dsimp only; omega)
                        ⟨st3', ⟨{ hcl3 with lit_mark_len := by simp [st3', lm3', hlml3] },
                            hlen3.scratch_ok⟩,
                          hsc3, hcore3, har3, by omega, ?_, by simpa [st3'] using hmrk3,
                          by assumption⟩
                      intro x hx hnz; dsimp only [st3', lm3'] at hnz; rw [hset_idx] at hnz
                      by_cases hxeq :
                          x = (st3.core.arena[p.toNat + 3 + k3.toNat]'(by rw [harl3]; omega)).toNat
                      · rw [hxeq, List.getElem?_set_self (by rw [hlml3, ← hxeq]; exact hx)] at hnz
                        exact absurd rfl hnz
                      · rw [List.getElem?_set_ne (Ne.symm hxeq)] at hnz
                        obtain ⟨i, hi1, hi2, hieq⟩ := hlm3 x hx hnz
                        have hine : i ≠ k3.toNat := by
                          intro hieq'; subst hieq'
                          rw [List.getElem?_eq_getElem (by rw [harl3]; omega),
                            Option.getD_some] at hieq
                          exact hxeq hieq.symm
                        exact ⟨i, by omega, hi2, hieq⟩
                    · have hk3_eq : k3.toNat = nsz.toNat := by
                        have hnl : ¬ k3.toNat < nsz.toNat := hc; omega
                      have hlm3_zero : ∀ x < 2 * c.max_vars,
                          st3.core.lit_mark[x]?.getD 0#8 = 0#8 :=
                        fun x hx => Classical.byContradiction fun hnz => by
                          obtain ⟨i, hi1, hi2, _⟩ := hlm3 x hx hnz; omega
                      have har3_lt : ∀ j < sz32.toNat,
                          (st3.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat <
                            2 * st.core.cur_vars :=
                        fun j hj => har3 ▸ hlt2 j hj
                      have har3_pw : ∀ i j, i < j → j < nsz.toNat →
                          (st3.core.arena[p.toNat + 3 + i]?.getD 0#32).toNat / 2 ≠
                          (st3.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat / 2 :=
                        fun i j hij hj => har3 ▸ hpw2 i j hij hj
                      have har3_out : ∀ i, i < p.toNat + 3 ∨ p.toNat + 3 + sz32.toNat ≤ i →
                          st3.core.arena[i]? = st.core.arena[i]? := fun i hi => har3 ▸ hout2 i hi
                      have har3_pad : ∀ j, nsz.toNat ≤ j → j < sz32.toNat →
                          st3.core.arena[p.toNat + 3 + j]? = st.core.arena[p.toNat + 3 + j]? :=
                        fun j hj1 hj2 => har3 ▸ hpad2 j hj1 hj2
                      have har3_in_out : ∀ i, i < p.toNat ∨ p.toNat + 3 + sz32.toNat ≤ i →
                          st3.core.arena[i]? = st.core.arena[i]? := fun i hi =>
                        hi.elim (fun h1 => har3_out i (Or.inl (by omega)))
                          (fun h2 => har3_out i (Or.inr h2))
                      s_to_group
                      refine wp_join_group (ts := [])
                        (fun () m4 => RaDoneInv c F0 F_cur s0 st m4 R) ?_ ?_
                      · rintro _ ⟨⟩ m4 ⟨st4, hsp4, hcv4, hl04, hfl4, hrp4, hal4, hrefs4, hm4⟩
                        s_steps
                        exact hJ (np, ()) m4 hnp_meas
                          ⟨st4, hsp4, hcv4, hl04, hfl4, hrp4, hal4,
                           by rw [hal4, ← hal, hrefs4]; exact hnp_pos, hm4⟩
                      · intro Jdone hDone; s_to_group
                        refine wp_join_group (ts := [])
                          (fun () mg =>
                            st3.LengthsOk c ∧ (FullMem c st3 ⋆ R) mg ∧
                              (taut = true ∨ nsz.toNat ≤ 2))
                          ?_ ?_
                        · rintro _ ⟨⟩ mg ⟨_, hmg, hcond⟩
                          have hp_lt3 : p.toNat < st3.core.arena.length := by rw [harl3]; omega
                          s_steps
                          let st4 : FullState :=
                            { st3 with core := { st3.core with
                                arena := st3.core.arena.set p.toNat (hdr ||| 0x00080000#32)
                                arena_garbage := st3.core.arena_garbage + 3#64 +
                                  BitVec.setWidth 64 sz32 } }
                          obtain ⟨hsp4, hrefs4, hal4⟩ :=
                            overwriteGarb_l0 (s' := st4) hsp hl0_st hsc3 (replace_ag_eq hcore3)
                              hp_ref
                                (by show st4.core.arena.length = c.arena_cap; simp [st4, harl3])
                              hlml3 hlm3_zero
                              (by show st4.core.arena[p.toNat]? = _
                                  dsimp only [st4]; rw [List.getElem?_set_self hp_lt3, hhdr_eq])
                              (by show st4.core.arena[p.toNat + 2]? = _
                                  dsimp only [st4]
                                  rw [List.getElem?_set_ne (by omega : p.toNat ≠ p.toNat + 2)]
                                  exact har3_out (p.toNat + 2) (Or.inl (by omega)))
                              (fun i hi => by
                                show st4.core.arena[i]? = _
                                have hne : p.toNat ≠ i := by rw [← hsz_eq] at hi; omega
                                dsimp only [st4]; rw [List.getElem?_set_ne hne]
                                exact har3_in_out i (by rw [← hsz_eq] at hi; exact hi))
                          have ⟨hcv4, hl04, hfl4, hrp4⟩ : st4.core.cur_vars = s0.core.cur_vars ∧
                              st4.core.cur_level = 0 ∧ st4.core.fuel = s0.core.fuel ∧
                              st4.core.repr = s0.core.repr :=
                            ⟨(congrArg FullCoreState.cur_vars hcore3).trans hcv,
                             (congrArg FullCoreState.cur_level hcore3).trans hl0_st,
                             (congrArg FullCoreState.fuel hcore3).trans hfl,
                             (congrArg FullCoreState.repr hcore3).trans hrp⟩
                          have hal4' : st4.core.arena_len = s0.core.arena_len := hal4.trans hal
                          have hm4 : (FullMem c st4 ⋆ R) m := by assumption
                          have hp3_eq : (p + 3#64).toNat = p.toNat + 3 := by
                            rw [BitVec.toNat_add, show (3#64).toNat = 3 from rfl,
                              Nat.mod_eq_of_lt (by omega)]
                          have hp4_eq : (p + 4#64).toNat = p.toNat + 4 := by
                            rw [BitVec.toNat_add, show (4#64).toNat = 4 from rfl,
                              Nat.mod_eq_of_lt (by omega)]
                          s_to_group
                          refine wp_join_group (ts := [])
                            (fun () m4a => (taut = true ∨ 1 ≤ nsz.toNat) ∧ (FullMem c st4 ⋆ R) m4a)
                            ?_ ?_
                          · rintro _ ⟨⟩ m4a ⟨_, hm4a⟩
                            s_to_group
                            refine wp_join_group (ts := [])
                              (fun () m5 => ∃ st5 : FullState,
                                st5.core.arena = st4.core.arena ∧ FullSparseInvW c F0 F_cur st5 ∧
                                st5.core.cur_vars = s0.core.cur_vars ∧ st5.core.cur_level = 0 ∧
                                st5.core.fuel = s0.core.fuel ∧ st5.core.repr = s0.core.repr ∧
                                st5.core.arena_len = s0.core.arena_len ∧
                                fullArenaClauseRefs st5 = fullArenaClauseRefs st ∧
                                (FullMem c st5 ⋆ R) m5)
                              ?_ ?_
                            · rintro _ ⟨⟩ m5 ⟨st5, har5_eq, hsp5, hcv5, hl05, hfl5, hrp5, hal5,
                                hrefs5, hm5⟩
                              s_to_group
                              refine wp_join_group (ts := [])
                                (fun () m6 => RaDoneInv c F0 F_cur s0 st m6 R)
                                (fun _ ⟨⟩ m6 h6 => by s_steps; exact hDone () m6 h6)
                                (fun J2b hJ2b => ?_)
                              s_split
                              · s_steps; exact hJ2b () m5
                                  ⟨st5, hsp5, hcv5, hl05, hfl5, hrp5, hal5, hrefs5, hm5⟩
                              · have htaut_f2 : taut = false := by
                                  cases taut <;> first | rfl | contradiction | exact absurd rfl hc
                                s_split
                                · have hnsz2 : nsz.toNat = 2 := by
                                    have hbe : nsz = 2#32 := hc; rw [hbe]; rfl
                                  have harl5 := hsp5.1.core_ok.arena_len_arr
                                  have hp3_lt5 : (p + 3#64).toNat < st5.core.arena.length := by
                                    rw [hp3_eq, harl5]; omega
                                  have hp4_lt5 : (p + 4#64).toNat < st5.core.arena.length := by
                                    rw [hp4_eq, harl5]; omega
                                  have hget_p3 : st5.core.arena[(p + 3#64).toNat]'hp3_lt5 =
                                      st3.core.arena[p.toNat + 3]'(by rw [harl3]; omega) :=
                                    list_getElem_of_getElem? hp3_eq (by
                                      rw [har5_eq]; dsimp only [st4]
                                      rw [List.getElem?_set_ne (by omega)])
                                  have hget_p4 : st5.core.arena[(p + 4#64).toNat]'hp4_lt5 =
                                      st3.core.arena[p.toNat + 4]'(by rw [harl3]; omega) :=
                                    list_getElem_of_getElem? hp4_eq (by
                                      rw [har5_eq]; dsimp only [st4]
                                      rw [List.getElem?_set_ne (by omega)])
                                  have hent_b : (cnfOfClauses F_cur).EntailsClause
                                      (cnfClause
                                        [(st5.core.arena[(p + 3#64).toNat]'hp3_lt5).toNat,
                                         (st5.core.arena[(p + 4#64).toNat]'hp4_lt5).toNat]) := by
                                    refine entails_clause_subst (fun l hl => ?_)
                                      (hsp.2.1.arena.entails p.toNat hp_ref hng)
                                    obtain ⟨j, hj, rfl⟩ := (mem_fullArenaClauseLitsCore_iff
                                      (by rw [harl]; omega)).mp hl
                                    rw [hsz_core] at hj
                                    obtain ⟨m', hm', heqv⟩ := hent2 htaut_f2 j (by omega)
                                    rcases (by omega : m' = 0 ∨ m' = 1) with rfl | rfl
                                    · refine ⟨_, List.mem_cons_self, ?_⟩
                                      rw [hget_p3]
                                      rw [← har3, Nat.add_zero,
                                        List.getElem?_eq_getElem (by rw [harl]; omega),
                                        List.getElem?_eq_getElem (by rw [harl3]; omega),
                                        Option.getD_some, Option.getD_some] at heqv; exact heqv
                                    · refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
                                      rw [hget_p4]
                                      rw [← har3, show p.toNat + 3 + 1 = p.toNat + 4 by omega,
                                        List.getElem?_eq_getElem (by rw [harl]; omega),
                                        List.getElem?_eq_getElem (by rw [harl3]; omega),
                                        Option.getD_some, Option.getD_some] at heqv; exact heqv
                                  s_steps; s_call hAddBin
                                  refine ⟨c, F0, F_cur, st5, R, rfl, hsp5.1, hsp5.2.1, hl05,
                                    fun _ _ => hent_b, hm5, ?_⟩
                                  intro r _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 st6
                                    hlen6 hw6 _ hr20 _ hm6
                                  have hsp6 := fullSparseInvW_afterAddBin hsp5 hlen6 hw6
                                  s_split
                                  · s_steps
                                    exact hQ false st6 m6 hsp6 hl05 hcv5 hfl5
                                      (fun _ => (hr20 hc).1) hm6
                                  · s_to_group
                                    refine wp_join_group (ts := [])
                                      (fun () m6' => (FullMem c st6 ⋆ R) m6')
                                      (fun _ ⟨⟩ m6' hm6' => by
                                        c0_hsteps
                                        let st6o : FullState :=
                                          { st6 with core := { st6.core with oom := 1#64 } }
                                        exact hQ true st6o _ (fullSparseInvW_with_oom hsp6 1#64)
                                          hl05 hcv5 hfl5 (fun h => by cases h) (by assumption))
                                      (fun Joom hOom => ?_)
                                    s_split
                                    · s_steps; exact hOom () m6 hm6
                                    · s_split
                                      · s_steps; exact hOom () m6 hm6
                                      · s_steps
                                        exact hJ2b () m6
                                          ⟨st6, hsp6, hcv5, hl05, hfl5, hrp5, hal5, hrefs5, hm6⟩
                                · s_steps; exact hJ2b () m5
                                    ⟨st5, hsp5, hcv5, hl05, hfl5, hrp5, hal5, hrefs5, hm5⟩
                            · intro J_1 hJ_1; s_split
                              · s_steps; exact hJ_1 () m4a
                                  ⟨st4, rfl, hsp4, hcv4, hl04, hfl4, hrp4, hal4', hrefs4, hm4a⟩
                              · have htaut_f1 : taut = false := by
                                  cases taut <;> first | rfl | contradiction | exact absurd rfl hc
                                s_split
                                · have hnsz1 : nsz.toNat = 1 := by
                                    have hbe : nsz = 1#32 := hc; rw [hbe]; rfl
                                  have hp3_lt4 : (p + 3#64).toNat < st4.core.arena.length := by
                                    rw [hp3_eq, show st4.core.arena.length =
                                      st3.core.arena.length by simp [st4], harl3]; omega
                                  have hlit_get : st4.core.arena[(p + 3#64).toNat]'hp3_lt4 =
                                      st3.core.arena[p.toNat + 3]'(by rw [harl3]; omega) :=
                                    list_getElem_of_getElem? hp3_eq (by
                                      dsimp only [st4]; rw [List.getElem?_set_ne (by omega)])
                                  have hlit_lt_cv : (st4.core.arena[(p + 3#64).toNat]'hp3_lt4).toNat
                                      < 2 * st4.core.cur_vars := by
                                    rw [hlit_get, hcv4, ← hcv]
                                    have h0 := har3_lt 0 (by omega)
                                    rwa [Nat.add_zero,
                                      List.getElem?_eq_getElem (by rw [harl3]; omega),
                                      Option.getD_some] at h0
                                  have hlit_ent : (cnfOfClauses F_cur).EntailsClause (cnfClause
                                      [(st4.core.arena[(p + 3#64).toNat]'hp3_lt4).toNat]) := by
                                    refine entails_clause_subst (fun l hl => ?_)
                                      (hsp.2.1.arena.entails p.toNat hp_ref hng)
                                    obtain ⟨j, hj, rfl⟩ := (mem_fullArenaClauseLitsCore_iff
                                      (by rw [harl]; omega)).mp hl
                                    rw [hsz_core] at hj
                                    obtain ⟨m', hm', heqv⟩ := hent2 htaut_f1 j (by omega)
                                    have hm0 : m' = 0 := by omega
                                    subst hm0; refine ⟨_, List.mem_singleton.mpr rfl, ?_⟩
                                    rw [hlit_get]
                                    rw [← har3, Nat.add_zero,
                                      List.getElem?_eq_getElem (by rw [harl]; omega),
                                      List.getElem?_eq_getElem (by rw [harl3]; omega),
                                      Option.getD_some, Option.getD_some] at heqv; exact heqv
                                  s_steps; s_call hAddUnit
                                  refine ⟨c, F0, F_cur, st4, R, rfl, hsp4.1, hsp4.2.1,
                                    fun _ => hlit_ent, hm4a, ?_⟩
                                  intro ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 st5
                                    hlen5 hw5 hcl5 hfail5 _ hm5
                                  have hsp5 := fullSparseInvW_afterAddUnit hsp4 hlen5 hw5
                                  s_split
                                  · s_steps; exact hJ_1 () m5
                                      ⟨st5, rfl, hsp5, hcv4, hcl5, hfl4, hrp4, hal4', hrefs4, hm5⟩
                                  · s_steps; exact hQ false st5 m5 hsp5 hcl5 hcv4 hfl4
                                      (fun _ => (hfail5 hlit_lt_cv (by
                                        cases ok <;>
                                          first | rfl | contradiction | exact absurd rfl hc)).1)
                                      hm5
                                · s_steps; exact hJ_1 () m4a
                                    ⟨st4, rfl, hsp4, hcv4, hl04, hfl4, hrp4, hal4', hrefs4, hm4a⟩
                          · intro J0 hJ0; s_split
                            · s_steps; exact hJ0 () _ ⟨Or.inl hc, by assumption⟩
                            · have htaut_f0 : taut = false := by
                                cases taut <;> first | rfl | contradiction | exact absurd rfl hc
                              s_split
                              · exfalso; have hnsz0 : nsz.toNat = 0 := by
                                  have hbe : nsz = 0#32 := hc; rw [hbe]; rfl
                                have := hnsz_pos htaut_f0; omega
                              · s_steps; exact hJ0 () _ ⟨Or.inr (hnsz_pos htaut_f0), by assumption⟩
                        · intro Jgarb hGarb; s_split
                          · s_steps; exact hGarb () m3 ⟨hlen3, hm3, Or.inl hc⟩
                          · s_split
                            · s_steps; exact hGarb () m3 ⟨hlen3, hm3, Or.inr hc⟩
                            · have htaut_f : taut = false := by
                                cases taut <;> first | rfl | contradiction | exact absurd rfl hc
                              have hnsz3 : 3 ≤ nsz.toNat := by
                                have hnot : ¬ nsz.toNat ≤ 2 := hc; omega
                              have hent_n : (cnfOfClauses F_cur).EntailsClause
                                  (cnfClause ((List.range nsz.toNat).map fun j =>
                                    (st3.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat)) :=
                                entails_clause_subst (fun l hl => by
                                  obtain ⟨j, hj, rfl⟩ := (mem_fullArenaClauseLitsCore_iff
                                    (by rw [harl]; omega)).mp hl
                                  rw [hsz_core] at hj
                                  obtain ⟨m', hm', heqv⟩ := hent2 htaut_f j (by omega)
                                  refine ⟨_, List.mem_map.mpr ⟨m', List.mem_range.mpr hm', rfl⟩, ?_⟩
                                  rw [← har3, List.getElem?_eq_getElem (by rw [harl]; omega),
                                    Option.getD_some] at heqv; exact heqv)
                                  (hsp.2.1.arena.entails p.toNat hp_ref hng)
                              have hp1_eq : (p + 1#64).toNat = p.toNat + 1 := by
                                rw [BitVec.toNat_add, bv64_one_nat, Nat.mod_eq_of_lt (by omega)]
                              have hnsz_ofNat : BitVec.ofNat 32 nsz.toNat = nsz :=
                                BitVec.eq_of_toNat_eq (by
                                  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt nsz.isLt])
                              s_to_group
                              refine wp_join_group (ts := [])
                                (fun () m4 => RaDoneInv c F0 F_cur s0 st m4 R)
                                (fun _ ⟨⟩ m4 h4 => by s_steps; exact hDone () m4 h4)
                                (fun Jshr hShr => ?_)
                              s_split
                              · have hnsz_lt : nsz.toNat < sz32.toNat := hc
                                have hp2_lt3 : (p + 2#64).toNat < st3.core.arena.length := by
                                  rw [hp2_eq, harl3]; omega
                                have hp1_lt3 : (p + 1#64).toNat < st3.core.arena.length := by
                                  rw [hp1_eq, harl3]; omega
                                s_to_group
                                let ar4a := (st3.core.arena.set (p + 2#64).toNat nsz).set
                                  (p + 1#64).toNat 2#32
                                have har4a_def : ar4a = (st3.core.arena.set (p.toNat + 2) nsz).set
                                    (p.toNat + 1) 2#32 := by
                                  dsimp only [ar4a]; rw [hp2_eq, hp1_eq]
                                refine wp_join_group (ts := [])
                                  (fun () m4 => RaDoneInv c F0 F_cur s0 st m4 R)
                                  (fun _ ⟨⟩ m4 h4 => by s_steps; exact hShr () m4 h4)
                                  (fun Jshrk hShrk => ?_)
                                s_split
                                · have hshrk_z : (hdr &&& 0x00800000#32) = 0#32 := hc
                                  have hp_lt3 : p.toNat < st3.core.arena.length := by
                                    rw [harl3]; omega
                                  have hsent_idx :
                                      (p + 3#64 + BitVec.setWidth 64
                                        (st.core.arena[(p + 2#64).toNat]'hp2_lt) - 1#64).toNat =
                                        p.toNat + 3 + sz32.toNat - 1 := by
                                    change (p + 3#64 + BitVec.setWidth 64 sz32 - 1#64).toNat = _
                                    have hoff3 := fullSubst_off3_toNat (p := p) (k := sz32)
                                      (by omega)
                                    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by
                                        rw [hoff3, bv64_one_nat]; omega)), hoff3, bv64_one_nat]
                                  have hsent_lt3 :
                                      (p + 3#64 + BitVec.setWidth 64
                                        (st.core.arena[(p + 2#64).toNat]'hp2_lt) - 1#64).toNat <
                                        st3.core.arena.length := by rw [hsent_idx, harl3]; omega
                                  s_steps
                                  let ar4b := ((ar4a.set p.toNat (hdr ||| 0x00800000#32)).set
                                    (p + 3#64 + BitVec.setWidth 64
                                      (st.core.arena[(p + 2#64).toNat]'hp2_lt) - 1#64).toNat
                                    0xFFFFFFFF#32)
                                  have har4b_def : ar4b = ((ar4a.set p.toNat
                                      (hdr ||| 0x00800000#32)).set
                                      (p.toNat + 3 + sz32.toNat - 1) 0xFFFFFFFF#32) := by
                                    dsimp only [ar4b]; rw [hsent_idx]
                                  refine hShrk () _ (ra_shrink_done (ar4 := ar4b)
                                    hsp hl0_st hcv hfl hrp hal hp_ref hng hsz_eq hnsz3 (by omega)
                                    hsc3 hcore3 (by rw [har4b_def, har4a_def]; simp [harl3])
                                    hlml3 hlm3_zero ?_ ?_ ?_ ?_ ?_ har3_pad har3_in_out har3_lt
                                    har3_pw hent_n ?_)
                                  · rw [har4b_def, ← hsz_eq, hhdr_eq]
                                    simp only [hnsz_lt, hshrk_z, and_self, ite_true]
                                    rw [List.getElem?_set_ne (by omega),
                                      List.getElem?_set_self (by
                                        dsimp only [ar4a]; simp [harl3]; omega)]
                                  · rw [har4b_def, har4a_def, List.getElem?_set_ne (by omega),
                                      List.getElem?_set_ne (by omega),
                                      List.getElem?_set_ne (by omega),
                                      List.getElem?_set_self (by rw [harl3]; omega), hnsz_ofNat]
                                  · intro _ _; rw [har4b_def, ← hsz_eq]
                                    exact List.getElem?_set_self (by
                                      dsimp only [ar4a]; simp [harl3]; omega)
                                  · intro _ hne; exact absurd (hhdr_eq.symm ▸ hshrk_z) hne
                                  · intro i h0 h1 h2 h3; rw [har4b_def, har4a_def,
                                      List.getElem?_set_ne (h3 hnsz_lt).symm,
                                      List.getElem?_set_ne h0.symm, List.getElem?_set_ne h1.symm,
                                      List.getElem?_set_ne h2.symm]
                                  · assumption
                                · have hshrk_ne : (hdr &&& 0x00800000#32) ≠ 0#32 := hc
                                  s_steps
                                  refine hShrk () _ (ra_shrink_done (ar4 := ar4a)
                                    hsp hl0_st hcv hfl hrp hal hp_ref hng hsz_eq hnsz3 (by omega)
                                    hsc3 hcore3 (by rw [har4a_def]; simp [harl3]) hlml3 hlm3_zero
                                    ?_ ?_ ?_ ?_ ?_ har3_pad har3_in_out har3_lt har3_pw hent_n ?_)
                                  · rw [har4a_def, hhdr_eq]; simp only [hshrk_ne, and_false,
                                      ite_false]
                                    rw [List.getElem?_set_ne (by omega),
                                      List.getElem?_set_ne (by omega)]
                                    exact (har3_out p.toNat (Or.inl (by omega))).trans
                                      (List.getElem?_eq_getElem (by rw [harl]; omega))
                                  · rw [har4a_def, List.getElem?_set_ne (by omega),
                                      List.getElem?_set_self (by rw [harl3]; omega), hnsz_ofNat]
                                  · intro _ hz; exact absurd (hhdr_eq ▸ hz) hshrk_ne
                                  · intro _ _; rw [har4a_def, ← hsz_eq,
                                      List.getElem?_set_ne (by omega),
                                      List.getElem?_set_ne (by omega),
                                      show p.toNat + 3 + sz32.toNat - 1 =
                                        p.toNat + 3 + (sz32.toNat - 1) by omega]
                                    exact har3_pad (sz32.toNat - 1) (by omega) (by omega)
                                  · intro i _ h1 h2 _; rw [har4a_def,
                                      List.getElem?_set_ne h1.symm, List.getElem?_set_ne h2.symm]
                                  · assumption
                              · have hnsz_eq : nsz.toNat = sz32.toNat := by
                                  have hnot : ¬ nsz.toNat < sz32.toNat := hc; omega
                                s_steps
                                refine hShr () m3 (ra_shrink_done (ar4 := st3.core.arena)
                                  hsp hl0_st hcv hfl hrp hal hp_ref hng hsz_eq hnsz3 (by omega)
                                  hsc3 hcore3 harl3 hlml3 hlm3_zero ?_ ?_ ?_ ?_
                                  (fun _ _ _ _ _ => rfl) har3_pad har3_in_out har3_lt har3_pw
                                  hent_n hm3)
                                · simp only [hhdr_eq, ← hsz_eq, hnsz_eq, Nat.lt_irrefl, false_and,
                                    ite_false]
                                  exact (har3_out p.toNat (Or.inl (by omega))).trans
                                    (List.getElem?_eq_getElem (by rw [harl]; omega))
                                · rw [hnsz_eq, show BitVec.ofNat 32 sz32.toNat = sz32 from
                                    BitVec.eq_of_toNat_eq (by
                                      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt sz32.isLt])]
                                  rw [← hp2_get]; exact har3_out (p.toNat + 2) (Or.inl (by omega))
                                · intro hlt; rw [← hsz_eq, hnsz_eq] at hlt; omega
                                · intro hlt; rw [← hsz_eq, hnsz_eq] at hlt; omega
                · rintro B2 L2 _ ⟨k, nsz, ⟨⟩⟩ m2 hB2 hL2
                    ⟨hk_n, ⟨st2, ⟨hlen2, hsc2, hcore2, hnsz_le, hpad2, hout2, hlt2, hpw2, hlm2,
                       hmrk2, hm2⟩, hk_le, hnsz_k, hnsz_pos, hent2⟩⟩
                  subst hk_n
                  have hcl2 := hlen2.core_ok; have harl2 := hcl2.arena_len_arr
                  have hlml2 := hcl2.lit_mark_len; have hrpl2 := hcl2.repr_len
                  have hrp2 : st2.core.repr = st.core.repr := by
                    rcases st with ⟨c0, _⟩; rcases st2 with ⟨c2, _⟩; rcases c0; rcases c2
                    cases hcore2; rfl
                  s_split
                  · have hk_lt : k.toNat < sz32.toNat := hc
                    have hk1 := fullSubst_add_u32_toNat (k := k) (by omega)
                    have hpk_eq := fullSubst_off3_toNat (p := p) (k := k) (by omega)
                    have hpk_lt : (p + 3#64 + BitVec.setWidth 64 k).toNat <
                        st2.core.arena.length := by rw [hpk_eq, harl2]; omega
                    let l2 := st2.core.arena[(p + 3#64 + BitVec.setWidth 64 k).toNat]'hpk_lt
                    have hl2_orig_eq : st2.core.arena[p.toNat + 3 + k.toNat]? = some l2 := by
                      dsimp only [l2]; rw [← hpk_eq, List.getElem?_eq_getElem hpk_lt]
                    have hl2_lt_v : l2.toNat < 2 * st.core.cur_vars := by
                      have hg := hlt2 k.toNat hk_lt
                      rw [hl2_orig_eq, Option.getD_some] at hg; exact hg
                    have hl2_lt_rp : (BitVec.setWidth 64 l2).toNat < st2.core.repr.length := by
                      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega), hrpl2]; omega
                    let rl2 := st2.core.repr[(BitVec.setWidth 64 l2).toNat]'hl2_lt_rp
                    have hrl2_eq_get : st.core.repr[l2.toNat]?.getD 0#32 = rl2 := by
                      have hz : (BitVec.setWidth 64 l2).toNat = l2.toNat := by
                        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                      dsimp only [rl2]; rw [← hrp2]
                      rw [bv32_getElem_congr (xs := st2.core.repr) hz
                          (hi := hl2_lt_rp) (hj := by rw [hrpl2]; omega),
                        List.getElem?_eq_getElem (by omega), Option.getD_some]
                    have hrl2_lt_v : rl2.toNat < 2 * st.core.cur_vars := by
                      rw [← hrl2_eq_get]; exact FullReprEquiv.lt hrepr_st hl2_lt_v
                    have hrl2_eqv : LitEquiv (cnfOfClauses F_cur) l2.toNat rl2.toNat := by
                      rw [← hrl2_eq_get]; exact FullReprEquiv.litEquiv hrepr_st hl2_lt_v
                    have hidx_rl2 :
                        st2.core.repr[(st2.core.arena[(p.toNat + 3 + k.toNat) % 2 ^ 64]'(by
                          rw [Nat.mod_eq_of_lt (by omega), harl2]; omega)).toNat]'(by
                          have heq_l : st2.core.arena[(p.toNat + 3 + k.toNat) % 2 ^ 64]'(by
                              rw [Nat.mod_eq_of_lt (by omega), harl2]; omega) = l2 := by
                            dsimp only [l2]
                            exact bv32_getElem_congr (by rw [hpk_eq, Nat.mod_eq_of_lt (by omega)])
                          rw [heq_l, hrpl2]; omega) = rl2 := by
                      dsimp only [rl2]; refine bv32_getElem_congr ?_
                      have hsw : (BitVec.setWidth 64 l2).toNat = l2.toNat := by
                        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                      exact (congrArg BitVec.toNat (bv32_getElem_congr (by
                        show (p.toNat + 3 + k.toNat) % 2 ^ 64 =
                          (p + 3#64 + BitVec.setWidth 64 k).toNat
                        rw [Nat.mod_eq_of_lt (by omega), hpk_eq]))).trans hsw.symm
                    have hrl2_1_z64 : (BitVec.setWidth 64 (rl2 ^^^ 1#32)).toNat =
                        rl2.toNat ^^^ 1 := by
                      have hnx := litNeg_lt_two_mul hrl2_lt_v
                      rw [BitVec.toNat_setWidth, bv32_xor1_toNat, Nat.mod_eq_of_lt (by omega)]
                    have hrl2_1_lt_lm :
                        (BitVec.setWidth 64 (rl2 ^^^ 1#32)).toNat < st2.core.lit_mark.length := by
                      have hnx := litNeg_lt_two_mul hrl2_lt_v; rw [hrl2_1_z64, hlml2]; omega
                    s_split
                    · s_steps; exact hB2 (k, true, nsz, ()) m2
                        ⟨st2, ⟨hlen2, hsc2, hcore2, by omega, hpad2, hout2, hlt2, hpw2, hlm2,
                           hmrk2, hm2⟩, fun h => Bool.noConfusion h, fun h => Bool.noConfusion h⟩
                    · have hlm_neg0 : st2.core.lit_mark[rl2.toNat ^^^ 1]?.getD 0#8 = 0#8 :=
                        ra_lm_zero (hi := by rw [← hrl2_1_z64]; exact hrl2_1_lt_lm)
                          (hrl2_1_z64.trans (congrArg (·.toNat ^^^ 1) hidx_rl2.symm)) hc
                      have hrl_z64 : (BitVec.setWidth 64 rl2).toNat = rl2.toNat := by
                        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                      have hrl2_lt_lm : (BitVec.setWidth 64 rl2).toNat <
                          st2.core.lit_mark.length := by rw [hrl_z64, hlml2]; omega
                      s_to_group
                      refine wp_join_group (ts := [i32])
                        (fun (nsz', ()) m2' =>
                          RaLoop2Inv c F_cur st p sz32.toNat (k + 1#32) nsz' m2' R)
                        (fun _ ⟨nsz', ⟨⟩⟩ m2' h2' => by
                          s_steps
                          exact hL2 (sz32.toNat - (k + 1#32).toNat) (k + 1#32, nsz', ()) m2'
                            (by omega) ⟨rfl, h2'⟩)
                        (fun Jnsz hJnsz => ?_)
                      s_split
                      · have hlm_pos0 : st2.core.lit_mark[rl2.toNat]?.getD 0#8 = 0#8 :=
                          ra_lm_zero (hi := by rw [← hrl_z64]; exact hrl2_lt_lm)
                            (hrl_z64.trans (congrArg BitVec.toNat hidx_rl2.symm)) hc
                        have hpnsz_eq := fullSubst_off3_toNat (p := p) (k := nsz) (by omega)
                        have hpnsz_lt : (p + 3#64 + BitVec.setWidth 64 nsz).toNat <
                            st2.core.arena.length := by rw [hpnsz_eq, harl2]; omega
                        have hnsz1 := fullSubst_add_u32_toNat (k := nsz) (by omega)
                        s_steps
                        refine hJnsz (nsz + 1#32, ()) _ (ra_push_step hk_lt hk1 hnsz1 hlen2 hsc2
                          hcore2 hnsz_k hpad2 hout2 hlt2 hpw2 hent2 hlm2 hmrk2 hcv_le
                          (by rw [harl2]; omega) hl2_orig_eq hrl2_lt_v hrl2_eqv hlm_neg0 hlm_pos0
                          ?_)
                        rw [← hrl_z64, ← hpnsz_eq]; assumption
                      · have hlm_nz : st2.core.lit_mark[rl2.toNat]?.getD 0#8 ≠ 0#8 :=
                          ra_lm_ne (hi := by rw [← hrl_z64]; exact hrl2_lt_lm)
                            (hrl_z64.trans (congrArg BitVec.toNat hidx_rl2.symm)) hc
                        obtain ⟨m_dup, hm_dup_lt, hm_dup_eq⟩ :=
                          (hlm2 rl2.toNat (by omega)).mp hlm_nz
                        s_steps; refine hJnsz (nsz, ()) m2
                          ⟨st2, ⟨hlen2, hsc2, hcore2, by omega, hpad2, hout2, hlt2, hpw2, hlm2,
                             hmrk2, hm2⟩, by omega, by omega, fun _ => by omega, ?_⟩
                        intro j hj
                        by_cases hjk : j = k.toNat
                        · subst hjk; refine ⟨m_dup, hm_dup_lt, ?_⟩
                          have hpad_k := hpad2 k.toNat hnsz_k hk_lt
                          have hl2_orig : (st.core.arena[p.toNat + 3 + k.toNat]?.getD 0#32).toNat =
                              l2.toNat := by rw [← hpad_k, hl2_orig_eq, Option.getD_some]
                          rw [hl2_orig, hm_dup_eq]; exact hrl2_eqv
                        · exact hent2 j (by omega)
                  · have hk_eq : k.toNat = sz32.toNat := by
                      have hnl : ¬ k.toNat < sz32.toNat := hc; omega
                    s_steps
                    exact hB2 (k, false, nsz, ()) m2
                      ⟨st2, ⟨hlen2, hsc2, hcore2, hnsz_le, hpad2, hout2, hlt2, hpw2, hlm2, hmrk2,
                         hm2⟩,
                       fun _ => hnsz_pos (by omega), fun _ j hj => hent2 j (by omega)⟩
                · intro B2 L2 _ hL2; s_steps
                  refine hL2 sz32.toNat (0#32, 0#32, ()) m1
                    ⟨rfl, st, ⟨hsp.1, rfl, rfl, Nat.zero_le _, fun _ _ _ => rfl, fun _ _ => rfl, ?_,
                       fun _ _ _ h => by
                         rw [show (0#32 : BitVec 32).toNat = 0 from rfl] at h; omega,
                       ?_, hsp.2.2.1.1, hm1⟩,
                     Nat.zero_le _, Nat.zero_le _,
                     fun h => by rw [show (0#32 : BitVec 32).toNat = 0 from rfl] at h; omega,
                     fun _ h => by rw [show (0#32 : BitVec 32).toNat = 0 from rfl] at h; omega⟩
                  · intro j hj
                    have hm_lt : (st.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat ∈
                        fullArenaClauseLits st p.toNat := by
                      unfold fullArenaClauseLits
                      have hm_elt := (mem_fullArenaClauseLitsCore_iff (k := st.core)
                        (cref := p.toNat) (by rw [harl, hsz_core]; omega)).mpr
                        ⟨j, by rw [hsz_core]; exact hj, rfl⟩
                      rw [List.getElem?_eq_getElem (by rw [harl]; omega), Option.getD_some]
                      exact hm_elt
                    exact hsp.2.1.arena.lits_lt p.toNat hp_ref hng _ hm_lt
                  · intro x hx; constructor
                    · intro hnz; exact absurd (hsp.2.2.1.2 x hx) hnz
                    · rintro ⟨m', hm', _⟩
                      rw [show (0#32 : BitVec 32).toNat = 0 from rfl] at hm'; omega
              · s_steps
                exact hJ (np, ()) m1 hnp_meas ⟨st, hsp, hcv, hl0_st, hfl, hrp, hal, hnp_pos, hm1⟩
            · rintro B1 L1 _ ⟨k, ⟨⟩⟩ m1 hB1 hL1 ⟨hk_n, hk_le, hm1⟩; subst hk_n
              s_split
              · have hk_lt : k.toNat < sz32.toNat := hc
                have hk1 := fullSubst_add_u32_toNat (k := k) (by omega)
                have hpk_eq := fullSubst_off3_toNat (p := p) (k := k) (by omega)
                have hpk_lt : (p + 3#64 + BitVec.setWidth 64 k).toNat < st.core.arena.length := by
                  rw [hpk_eq, harl]; omega
                s_to_group
                refine wp_join_group (ts := []) (fun () mi => (FullMem c st ⋆ R) mi)
                  (fun _ ⟨⟩ mi hmi => by
                    s_steps
                    exact hL1 (sz32.toNat - (k + 1#32).toNat) (k + 1#32, ()) mi (by omega)
                      ⟨rfl, by omega, hmi⟩)
                  (fun Ji hJi => ?_)
                s_split
                · have hl_lt_v :
                      (st.core.arena[(p + 3#64 + BitVec.setWidth 64 k).toNat]'hpk_lt).toNat <
                        2 * st.core.cur_vars := by
                    have hmem : (st.core.arena[p.toNat + 3 + k.toNat]'(by rw [harl]; omega)).toNat
                        ∈ fullArenaClauseLits st p.toNat := by
                      unfold fullArenaClauseLits
                      exact (mem_fullArenaClauseLitsCore_iff (k := st.core) (cref := p.toNat)
                        (by rw [harl, hsz_core]; omega)).mpr
                          ⟨k.toNat, by rw [hsz_core]; exact hk_lt, rfl⟩
                    have hl := hsp.2.1.arena.lits_lt p.toNat hp_ref hng _ hmem
                    rw [bv32_getElem_congr hpk_eq]; exact hl
                  have hl_lt_nl : (BitVec.setWidth 64
                      (st.core.arena[(p + 3#64 + BitVec.setWidth 64 k).toNat]'hpk_lt)).toNat <
                      st.core.repr.length := by
                    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega), hrpl]; omega
                  s_split
                  · s_steps; exact hB1 (true, k, ()) m1 ⟨Or.inl rfl, hm1⟩
                  · s_steps; exact hJi () m1 hm1
                · s_steps; exact hJi () m1 hm1
              · s_steps; exact hB1 (false, k, ()) m1 ⟨Or.inr rfl, hm1⟩
            · intro B1 L1 _ hL1; s_steps
              exact hL1 sz32.toNat (0#32, ()) ml ⟨rfl, Nat.zero_le _, hml⟩
      · s_steps
        exact hQ true st ml hsp hl0_st hcv (by rw [hfl]) (fun h => by cases h) hml

end RewriteArProof

end LeanQbe.T.Examples.Kissat.FullM5DenseSafe
