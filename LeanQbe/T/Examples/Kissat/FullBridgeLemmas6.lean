module

public import LeanQbe.T.Examples.Kissat.FullSpec
import LeanQbe.T.Examples.Kissat.FullSubstLemmas
import LeanQbe.T.Examples.Kissat.FullBveVarLemmas
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas

/-!
# Kissat `D-Full` Canonical `FullSpec` Bridge Proofs — Shards 12–14 (`Stage 4`)

Adapts three landed Stage-4 shards onto canonical `FullSpec2` / `FullSpec3` contracts (`10` fns,
all `10 / 10` fully canonical against `fullSpecTable fullSolveBytesSpec`):
- Part 4 (`FullSubstLemmas`, `4 / 4` canonical): `full_subst_elim_vars`, `full_subst_rewrite_bins`,
  `full_subst_rewrite_ar`, `full_substitute`.
- Part 5 (`FullBveVarLemmas`, `3 / 3` canonical): `full_bve_ext_need`, `full_bve_commit_res`,
  `full_bve_var`.
- Part 6 (`FullDenseWatchLemmas`, `3 / 3` canonical): `full_reduce`, `full_enter_dense`,
  `full_rebuild_watches` (all `11` callees bridged directly onto canonical `FullSpec2` /
  `FullSpec3`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat

/-! ## Part 4: `FullSubstLemmas` (`4` fns, `4 / 4` canonical) -/

section Part4

open FullSubstTactics FullSubstHelpers
open scoped FullArenaTactics FullSubstTactics

private theorem substPropagate_adapter {Γ : Env}
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X) :
    ∀ a m Q X, FullSubstSpecs.fullPropagateSpec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm, hm, hQ⟩
  refine hProp _ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm, hm, ?_⟩
  dsimp only
  intro r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
    fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' m'
    hlen' hw' htr hperm hfl hr hr0 hr1 hr2 hnp hm'
  exact hQ r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
    fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' m'
    hlen' hw' htr hperm hfl hr hr0
    (fun h1 => let ⟨hf, ho, hc⟩ := hr1 h1
      ⟨hf, ho, hc.elim Or.inl fun ⟨ht2, hrest⟩ => Or.inr ⟨by rw [ht2]; decide, hrest⟩⟩)
    hr2 hnp hm'

theorem full_subst_elim_vars_bridge_wp (Γ : Env)
    (hAddUnit : ∀ a m Q X, fullAddUnitSpec a m Q X → Γ "full_add_unit" [i64, i32] [.bool] a m Q X)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hExtPush2 : ∀ a m Q X, fullExtendPush2Spec a m Q X →
      Γ "full_extend_push2" [i64, i32, i32] [.bool] a m Q X)
    (hSetInact : ∀ a m Q X, fullSetInactiveSpec a m Q X →
      Γ "full_set_inactive" [i64, i32, i32] [] a m Q X) :
    ∀ a m Q X, fullSubstElimVarsSpec a m Q X → Func.wp Γ full_subst_elim_vars_body a m Q X :=
  full_subst_elim_vars_wp Γ hAddUnit (substPropagate_adapter hProp) hExtPush2 hSetInact

theorem full_subst_rewrite_bins_bridge_wp (Γ : Env)
    (hAddUnit : ∀ a m Q X, fullAddUnitSpec a m Q X → Γ "full_add_unit" [i64, i32] [.bool] a m Q X)
    (hAddBin : ∀ a m Q X, fullAddBinSpec a m Q X → Γ "full_add_bin" [i64, i32, i32] [i64] a m Q X) :
    ∀ a m Q X, fullSubstRewriteBinsSpec a m Q X →
      Func.wp Γ full_subst_rewrite_bins_body a m Q X :=
  full_subst_rewrite_bins_wp Γ hAddUnit hAddBin

theorem full_subst_rewrite_ar_bridge_wp (Γ : Env)
    (hArenaNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hAddUnit : ∀ a m Q X, fullAddUnitSpec a m Q X → Γ "full_add_unit" [i64, i32] [.bool] a m Q X)
    (hAddBin : ∀ a m Q X, fullAddBinSpec a m Q X → Γ "full_add_bin" [i64, i32, i32] [i64] a m Q X) :
    ∀ a m Q X, fullSubstRewriteArSpec a m Q X → Func.wp Γ full_subst_rewrite_ar_body a m Q X :=
  full_subst_rewrite_ar_wp Γ hArenaNext hAddUnit hAddBin

private def SubstAfterBtInv (c : FullCfg) (F0 : CNF Nat) (s0 : FullState)
    (m : Mem 64) (R : Mem 64 → Prop) : Prop :=
  ∃ st : FullState,
    FullSparseInv c F0 st ∧ st.core.cur_level = 0 ∧
    st.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ (FullMem c st ⋆ R) m

private def SubstLoopInv (c : FullCfg) (F0 : CNF Nat) (s0 : FullState)
    (round : BitVec 64) (m : Mem 64) (R : Mem 64 → Prop) : Prop :=
  ∃ st : FullState,
    FullSparseInv c F0 st ∧ st.core.cur_level = 0 ∧
    st.core.fuel.toNat ≤ s0.core.fuel.toNat ∧ round.toNat ≤ 4 ∧ (FullMem c st ⋆ R) m

theorem full_substitute_bridge_wp (Γ : Env)
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
    ∀ a m Q X, fullSubstituteSpec a m Q X → Func.wp Γ full_substitute_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s0, R, rfl, hsp0, hm, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  obtain ⟨F_cur0, hw0⟩ := hsp0.exists_witness
  have hcl0 := hsp0.1.lengths.core_ok
  have hclv_lt : s0.core.cur_level < 2 ^ 64 := by
    have := hw0.2.1.cur_level_le; have := hcl0.trail_end_le; have := hcl0.cur_vars_le; omega
  s_to_group; refine wp_join_group (ts := []) (fun () m1 => SubstAfterBtInv c F0 s0 m1 R) ?_ ?_
  · rintro _ ⟨⟩ m1 ⟨st1, hsp1, hl01, hfl1, hm1⟩
    s_to_group; refine wp_loop_break_group
      (fun (_r, ()) mb => SubstAfterBtInv c F0 s0 mb R)
      (fun n (round, ()) ml => n = 4 - round.toNat ∧ SubstLoopInv c F0 s0 round ml R)
      ?_ ?_ ?_
    · rintro B ⟨_r, ⟨⟩⟩ mb ⟨stb, hspb, hl0b, hflb, hmb⟩
      s_steps; exact hQ 1#64 stb mb hspb hl0b hflb (Or.inl rfl) (fun h => by cases h) hmb
    · rintro B L _ ⟨round, ⟨⟩⟩ ml hB hL ⟨hr_n, ⟨st, hsp, hl0_st, hfl_st, hr_le, hml⟩⟩
      subst hr_n; s_split
      · have hr_lt : round.toNat < 4 := hc
        have hr1 : (round + 1#64).toNat = round.toNat + 1 := by
          rw [BitVec.toNat_add, show (1#64).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
        s_split
        · s_split
          · obtain ⟨F_cur, hspw⟩ := hsp.exists_witness
            s_steps; s_call hTarjan
            refine ⟨c, F0, F_cur, st, R, rfl, hspw, hl0_st, hml, ?_⟩
            intro ucnt _ _ inc1 _ _ _ _ _ sstk1 _ m1 st1 hspw1 huc_le hus1 hrepr1 hm1
            have hl01' : st1.core.cur_level = 0 := hl0_st
            have hfl1' : st1.core.fuel.toNat ≤ s0.core.fuel.toNat := hfl_st
            s_split
            · s_steps; exact hQ 20#64 st1 m1 hspw1.toSparse hl01' hfl1' (Or.inr rfl)
                (fun _ => hspw1.2.1.ext_sound.2 (hspw1.2.1.inconsistent_sound hc)) hm1
            · s_steps; s_call hElimVars
              refine ⟨c, F0, F_cur, st1, R, rfl, hspw1, hl01', hrepr1 hc, huc_le, hus1, hm1, ?_⟩
              intro ok2 st2 m2 hspw2 hl02 _ hfl2 hrepr2 hfail2 hm2
              have hfl2' : st2.core.fuel.toNat ≤ s0.core.fuel.toNat := by omega
              s_split
              · s_split
                · s_steps; exact hB (round, ()) m2 ⟨st2, hspw2.toSparse, hl02, hfl2', hm2⟩
                · s_steps; s_call hRewriteBins
                  refine ⟨c, F0, F_cur, st2, R, rfl, hspw2, hl02, hrepr2, hm2, ?_⟩
                  intro ok3 st3 m3 hspw3 hl03 _ hfl3 hrepr3 hfail3 hm3
                  have hfl3' : st3.core.fuel.toNat ≤ s0.core.fuel.toNat := by
                    rw [hfl3]; exact hfl2'
                  s_split
                  · s_steps; s_call hRewriteAr
                    refine ⟨c, F0, F_cur, st3, R, rfl, hspw3, hl03, hrepr3, hm3, ?_⟩
                    intro ok4 st4 m4 hspw4 hl04 _ hfl4 hfail4 hm4
                    have hfl4' : st4.core.fuel.toNat ≤ s0.core.fuel.toNat := hfl4 ▸ hfl3'
                    s_split
                    · s_steps; s_call hArenaSweep
                      refine ⟨c, F0, F_cur, st4, R, rfl, hspw4.1, hspw4.2.1, hspw4.2.2.2.1,
                        hspw4.2.2.2.2.2, fun hpos => by omega, hm4, ?_⟩
                      intro sr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sc5 m5 st5
                        hlen5 _ hext5 _ hll5 hw5 hnd5 _ _ _ hsr2 _ hm5
                      have hspw5 :=
                        fullSparseInvW_afterArenaSweep hspw4 hlen5 hext5 hll5 hw5 hnd5 rfl rfl rfl
                      have hl05 : st5.core.cur_level = 0 := hl04
                      s_split
                      · s_steps; exact hQ 20#64 st5 m5 hspw5.toSparse hl05 hfl4' (Or.inr rfl)
                          (fun _ => (hsr2 hc).2) hm5
                      · s_steps; s_call hProp
                        refine ⟨c, F0, F_cur, st5, R, rfl, hspw5.1, hspw5.2.1,
                          hspw5.2.2.2.2.2, hm5, ?_⟩
                        intro pr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fuel6 _ _ _ _ _ _ _ _ m6 st6
                          hlen6 hw6 _ hperm6 hfl6 _ _ hpr1 _ _ hm6
                        have hspw6 := fullSparseInvW_afterPropagate hspw5 hlen6 hw6 hperm6
                        have hfl6' : st6.core.fuel.toNat ≤ s0.core.fuel.toNat := by
                          have hfl5' : st5.core.fuel.toNat ≤ s0.core.fuel.toNat := hfl4'
                          dsimp only [st6]; omega
                        s_split
                        · s_steps; exact hQ 20#64 st6 m6 hspw6.toSparse hl05 hfl6' (Or.inr rfl)
                            (fun _ => level0_unsat_of_conflict_okW (s := st6) hw6 hl05
                              (hpr1 hc).2.2) hm6
                        · s_steps; exact hL (4 - (round + 1#64).toNat) (round + 1#64, ()) m6
                            (by omega) ⟨rfl, st6, hspw6.toSparse, hl05, hfl6', by omega, hm6⟩
                    · s_steps; exact hQ 20#64 st4 m4 hspw4.toSparse hl04 hfl4' (Or.inr rfl)
                        (fun _ => hfail4 (by
                          cases ok4 <;> first | rfl | contradiction | exact absurd rfl hc)) hm4
                  · s_steps; exact hQ 20#64 st3 m3 hspw3.toSparse hl03 hfl3' (Or.inr rfl)
                      (fun _ => hfail3 (by
                        cases ok3 <;> first | rfl | contradiction | exact absurd rfl hc)) hm3
              · s_steps; exact hQ 20#64 st2 m2 hspw2.toSparse hl02 hfl2' (Or.inr rfl)
                  (fun _ => hfail2 (by
                    cases ok2 <;> first | rfl | contradiction | exact absurd rfl hc)) hm2
          · s_steps; exact hB (round, ()) ml ⟨st, hsp, hl0_st, hfl_st, hml⟩
        · s_steps; exact hB (round, ()) ml ⟨st, hsp, hl0_st, hfl_st, hml⟩
      · s_steps; exact hB (round, ()) ml ⟨st, hsp, hl0_st, hfl_st, hml⟩
    · intro B L _ hL; s_steps
      exact hL 4 (0#64, ()) m1 ⟨rfl, st1, hsp1, hl01, hfl1, Nat.zero_le _, hm1⟩
  · intro Jbt hJbt; s_split
    · s_steps; s_call hBacktrack
      refine ⟨c, s0, R, rfl, hsp0.1.lengths, hclv_lt, fun _ => by
        have := hw0.2.1.cur_level_le; have := hcl0.trail_end_le; have := hcl0.cur_vars_le; omega,
        hw0.2.1.trail_lits_lt, hm, ?_⟩
      intro _ _ _ _ _ _ _ cl1 _ sc1 m1 st1 hlen1 _ _ hcl1 hprsc1 _ _ _ hw_le _ hm1
      have hw1 := hw_le F0 F_cur0 hw0.2.1 (Nat.zero_le _)
      have hl01 : st1.core.cur_level = 0 := by dsimp only [st1]; rw [hcl1]; simp
      s_steps; exact hJbt () m1
        ⟨st1, fullSparseInv_afterBacktrack hsp0 hlen1 hprsc1 hw1 rfl rfl rfl rfl rfl,
         hl01, Nat.le_refl _, hm1⟩
    · have hl00 : s0.core.cur_level = 0 := by
        have hnat := congrArg BitVec.toNat hc
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hclv_lt] at hnat; exact hnat
      s_steps; exact hJbt () m ⟨s0, hsp0, hl00, Nat.le_refl _, hm⟩

end Part4

/-! ## Part 5: `FullBveVarLemmas` (`3` fns, `3 / 3` canonical) -/

section Part5

private theorem resBuf_to_bve {F_cur : List (List Nat)} {s : FullState} {r_end p : Nat}
    (h : FullResBufOkW F_cur s r_end p) : FullBveVarSpecs.FullResBufOkW F_cur s r_end p := by
  induction h with
  | nil => exact .nil
  | cons hbd hsz hlts hnd hent _ ih => exact .cons hbd hsz hlts hnd hent ih

private theorem resBuf_of_bve {F_cur : List (List Nat)} {s : FullState} {r_end p : Nat}
    (h : FullBveVarSpecs.FullResBufOkW F_cur s r_end p) : FullResBufOkW F_cur s r_end p := by
  induction h with
  | nil => exact .nil
  | cons hbd hsz hlts hnd hent _ ih => exact .cons hbd hsz hlts hnd hent ih

private theorem bveAddUnit_adapter {Γ : Env}
    (hAddUnit : ∀ a m Q X, fullAddUnitSpec a m Q X → Γ "full_add_unit" [i64, i32] [.bool] a m Q X) :
    ∀ a m Q X, FullBveVarSpecs.fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X := by
  rintro ⟨h, lit, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hent, hm, hQ⟩
  refine hAddUnit _ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hent, hm,
    fun ok vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl' inc'
      phases' ta' ba' pt' pb' hp' ps' hl' qsi' qss' m' hlen' hw' hcl0 hltf hof hm' => ?_⟩
  exact hQ ok vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl' inc'
    { s.scratch with
      phases := phases', target_assigned := ta', best_assigned := ba',
      phases_target := pt', phases_best := pb', heap := hp', pos := ps',
      heap_len := hl', q_search_idx := qsi', q_search_stamp := qss' }
    m' hlen' hw' ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hcl0 hltf hof hm'

private theorem bveSetInactive_adapter {Γ : Env}
    (hSetInact : ∀ a m Q X, fullSetInactiveSpec a m Q X →
      Γ "full_set_inactive" [i64, i32, i32] [] a m Q X) :
    ∀ a m Q X, FullBveVarSpecs.fullSetInactiveSpec a m Q X →
      Γ "full_set_inactive" [i64, i32, i32] [] a m Q X := by
  rintro ⟨h, v, flag, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  refine hSetInact _ m Q X ⟨c, s, R, rfl, hlen, hm, ?_⟩
  split
  · exact hQ s.core.flags s.core.unassigned m hlen.core_ok.flags_len hm
  · exact hQ

private theorem bveCommitRes_adapter {Γ : Env}
    (hCommitRes : ∀ a m Q X, fullBveCommitResSpec a m Q X →
      Γ "full_bve_commit_res" [i64, i64, i64] [i64] a m Q X) :
    ∀ a m Q X, FullBveVarSpecs.fullBveCommitResSpec a m Q X →
      Γ "full_bve_commit_res" [i64, i64, i64] [i64] a m Q X := by
  rintro ⟨h, r_off, r_end, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hdense, hle, hcap, hbuf, hm, hQ⟩
  exact hCommitRes _ m Q X ⟨c, F0, F_cur, s, R, rfl, hdense, hle, hcap, resBuf_of_bve hbuf, hm, hQ⟩

private theorem bveTryBce_adapter {Γ : Env}
    (hTryBce : ∀ a m Q X, fullBveTryBceSpec a m Q X →
      Γ "full_bve_try_bce" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, FullBveVarSpecs.fullBveTryBceSpec a m Q X →
      Γ "full_bve_try_bce" [i64, i32, i32, i32, i32] [.bool] a m Q X := by
  rintro ⟨h, blk_lit, cr, opp_off, opp_n, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hdense, hblk, hcr, hoff, hopp, hm, hQ⟩
  have hcr_w : FullBveBceWeakOk c s cr := by
    unfold FullBveBceWeakOk; unfold FullBveVarSpecs.FullBveTryBceEntryOk at hcr
    by_cases hmsb : (cr &&& 0x80000000#32) ≠ 0#32
    · rw [ite_eq_left hmsb] at hcr ⊢; exact hcr
    · rw [ite_eq_right hmsb] at hcr ⊢; exact ⟨hcr.1, hcr.2.1, hcr.2.2.1⟩
  have hcr_nd : (cr &&& 0x80000000#32) = 0#32 →
      ((fullArenaClauseLits s cr.toNat).map (· / 2)).Nodup := by
    intro h0; unfold FullBveVarSpecs.FullBveTryBceEntryOk at hcr
    rw [ite_eq_right (Classical.not_not.mpr h0)] at hcr; exact hcr.2.2.2
  exact hTryBce _ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hdense, hblk, hcr_w, hcr_nd, hoff, hopp, hm, hQ⟩

theorem full_bve_ext_need_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullBveExtNeedSpec a m Q X → Func.wp Γ full_bve_ext_need_body a m Q X :=
  full_bve_ext_need_wp Γ

theorem full_bve_commit_res_bridge_wp (Γ : Env)
    (hAlloc : ∀ a m Q X, fullAllocClSpec a m Q X →
      Γ "full_alloc_cl" [i64, i32, i32, .bool] [i64] a m Q X)
    (hWPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hAddBin : ∀ a m Q X, fullAddBinSpec a m Q X → Γ "full_add_bin" [i64, i32, i32] [i64] a m Q X)
    (hAddUnit : ∀ a m Q X, fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullBveCommitResSpec a m Q X → Func.wp Γ full_bve_commit_res_body a m Q X := by
  rintro ⟨h, r_off, r_end, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hdense, hle, hcap, hbuf, hm, hQ⟩
  exact full_bve_commit_res_wp Γ hAlloc hWPush hAddBin (bveAddUnit_adapter hAddUnit) _ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hdense, hle, hcap, resBuf_to_bve hbuf, hm, hQ⟩

theorem full_bve_var_bridge_wp (Γ : Env)
    (hCollect : ∀ a m Q X, fullBveCollectSpec a m Q X →
      Γ "full_bve_collect" [i64, i32, i64, i32] [i32] a m Q X)
    (hExtNeed : ∀ a m Q X, fullBveExtNeedSpec a m Q X →
      Γ "full_bve_ext_need" [i64, i32, i32] [i64] a m Q X)
    (hWeaken : ∀ a m Q X, fullBveWeakenSpec a m Q X →
      Γ "full_bve_weaken" [i64, i32, i32, i32] [.bool] a m Q X)
    (hSetInact : ∀ a m Q X, fullSetInactiveSpec a m Q X →
      Γ "full_set_inactive" [i64, i32, i32] [] a m Q X)
    (hGates : ∀ a m Q X, fullBveGatesSpec a m Q X →
      Γ "full_bve_gates" [i64, i32, i32, i32] [] a m Q X)
    (hResolve : ∀ a m Q X, fullBveResolvePairSpec a m Q X →
      Γ "full_bve_resolve_pair" [i64, i32, i32, i32] [.bool] a m Q X)
    (hCommitRes : ∀ a m Q X, fullBveCommitResSpec a m Q X →
      Γ "full_bve_commit_res" [i64, i64, i64] [i64] a m Q X)
    (hTryBce : ∀ a m Q X, fullBveTryBceSpec a m Q X →
      Γ "full_bve_try_bce" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hExtPush2 : ∀ a m Q X, fullExtendPush2Spec a m Q X →
      Γ "full_extend_push2" [i64, i32, i32] [.bool] a m Q X)
    (hDelBin : ∀ a m Q X, fullDeleteBinarySpec a m Q X →
      Γ "full_delete_binary" [i64, i32, i32] [] a m Q X)
    (hExtPushCl : ∀ a m Q X, fullExtendPushClSpec a m Q X →
      Γ "full_extend_push_cl" [i64, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullBveVarSpec a m Q X → Func.wp Γ full_bve_var_body a m Q X :=
  full_bve_var_wp Γ hCollect hExtNeed hWeaken
    (bveSetInactive_adapter hSetInact) hGates hResolve (bveCommitRes_adapter hCommitRes)
    (bveTryBce_adapter hTryBce) hExtPush2 hDelBin hExtPushCl

end Part5

/-! ## Part 6: `FullDenseWatchLemmas` (`3` fns) -/

section Part6

private theorem dwIsqrt_adapter {Γ : Env}
    (hIsqrt : ∀ a m Q X, fullIsqrtSpec a m Q X → Γ "full_isqrt" [i64] [i64] a m Q X) :
    ∀ a m Q X, FullDenseWatchSpecs.fullIsqrtSpec a m Q X →
      Γ "full_isqrt" [i64] [i64] a m Q X := by
  rintro ⟨x, ⟨⟩⟩ m Q X hQ
  exact hIsqrt _ m Q X fun r hsq _ _ => hQ r (Nat.le_trans (Nat.le_mul_self r.toNat) hsq)

private theorem dwRecomputeTiers_adapter {Γ : Env}
    (hRecomp : ∀ a m Q X, fullRecomputeTiersSpec a m Q X →
      Γ "full_recompute_tiers" [i64] [] a m Q X) :
    ∀ a m Q X, FullDenseWatchSpecs.fullRecomputeTiersSpec a m Q X →
      Γ "full_recompute_tiers" [i64] [] a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  refine hRecomp _ m Q X ⟨c, s, R, rfl, hlen, hm, fun _ s' m' hcore hlen' hpres hm' => ?_⟩
  rcases s' with ⟨c', sc'⟩
  change c' = s.core at hcore
  subst hcore
  exact hQ sc' m' hlen'.scratch_ok hpres.1.1 hpres.1.2 hpres.2.2.1 hm'

private theorem dwSortReds_adapter {Γ : Env}
    (hSortReds : ∀ a m Q X, fullSortRedsSpec a m Q X →
      Γ "full_sort_reds" [i64, i64] [] a m Q X) :
    ∀ a m Q X, FullDenseWatchSpecs.fullSortRedsSpec a m Q X →
      Γ "full_sort_reds" [i64, i64] [] a m Q X := by
  rintro ⟨h, n, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hn, hok, hm, hQ⟩
  refine hSortReds _ m Q X ⟨c, s, R, rfl, hlen, hn, hok, hm, fun rr' m' hrr hmem hm' => ?_⟩
  exact hQ { s.scratch with red_refs := rr' } m'
    { hlen.scratch_ok with red_refs_len := hrr } rfl rfl rfl hmem hm'

private theorem dwBacktrack_adapter {Γ : Env}
    (hBt : ∀ a m Q X, fullBacktrackSpec a m Q X → Γ "full_backtrack" [i64, i64] [] a m Q X) :
    ∀ a m Q X, FullDenseWatchSpecs.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X := by
  rintro ⟨h, tgt, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hle, hm, hQ⟩
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hcl_bd : s.core.cur_level < 2 ^ 64 := by
    have := hw.cur_level_le; have := hlen.core_ok.trail_end_le
    have := hlen.core_ok.cur_vars_le; omega
  have htg_bd : tgt.toNat < s.core.cur_level → tgt.toNat < c.max_vars := by
    intro _; have := hw.cur_level_le; have := hlen.core_ok.trail_end_le
    have := hlen.core_ok.cur_vars_le; omega
  refine hBt _ m Q X ⟨c, s, R, rfl, hlen, hcl_bd, htg_bd, hw.trail_lits_lt, hm,
    fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m'
      hlen' _ _ hcl' hps _ _ _ hwt _ hm' => ?_⟩
  have hmin : cl' = tgt.toNat := hcl'.trans (Nat.min_eq_right hle)
  subst hmin
  exact hQ vals' lvl' rsns' trl' tp' te' prop' unass' sc' m'
    hlen' (hwt F0 F_cur hw hle) hps.1.1 hps.1.2 hps.2.2.1 hm'

private theorem dwPropagate_adapter {Γ : Env}
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X) :
    ∀ a m Q X, FullDenseWatchSpecs.fullPropagateSpec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hnd, hdm, hm, hQ⟩
  refine hProp _ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm, hm, ?_⟩
  dsimp only
  intro r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
    fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' m'
    hlen' hw' htr hperm hfl hr hr0 hr1 _ _ hm'
  have hnd' : FullArenaVarsNodup
      { s with
        core := { s.core with
          vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
          trail_pos := tp', trail_end := te', propagated := prop', unassigned := unass',
          unflushed := unfl', wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
          wusable := wu', fuel := fuel', confl_type := ctype', confl_ref := cref',
          confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
        scratch := { s.scratch with
          search_ticks := ticks', wsort := wsort', phases := phases' } } := by
    intro ref href hng
    have href0 : ref ∈ fullArenaClauseRefsCore s.core := hperm.2.1 ▸ href
    obtain ⟨_, hgb, hp⟩ := hperm.2.2 ref href0
    exact (hp.map (· / 2)).nodup_iff.mpr (hnd ref href0 (hgb.symm.trans hng))
  exact hQ r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
    fuel' ctype' cref' c0' c1' oom'
    { s.scratch with search_ticks := ticks', wsort := wsort', phases := phases' } m'
    hlen' hw' hnd' (fun ref href => by
      change ref ∈ fullArenaClauseRefsCore _; rw [hperm.2.1]; exact href)
    rfl rfl rfl htr.1 hfl hr (fun h0 => (hr0 h0).2.1)
    (fun h1 => (hr1 h1).2.2.elim
      (fun ⟨ht, h0, h1', hf0, hf1, hent⟩ => Or.inl ⟨ht, h0, h1', hent, hf0, hf1⟩) Or.inr) hm'

private theorem dwSweepBins_adapter {Γ : Env}
    (hSweepBins : ∀ a m Q X, fullSweepBinsSpec a m Q X →
      Γ "full_sweep_bins" [i64] [] a m Q X) :
    ∀ a m Q X, FullDenseWatchSpecs.fullSweepBinsSpec a m Q X →
      Γ "full_sweep_bins" [i64] [] a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hm, hQ⟩
  refine hSweepBins _ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hm, ?_⟩
  dsimp only
  intro wvec' wstk' wlen' nb' wsort' m' hlen' _ hdw hw' hm'
  exact hQ wvec' wstk' wlen' nb' wsort' m' hlen' hw' hdw hm'

private theorem dwWatchPush_adapter {Γ : Env}
    (hWPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, FullDenseWatchSpecs.fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X := by
  rintro ⟨h, lit, w0, w1, cnt, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hlay, hc1, hc2, hm, hQ⟩
  refine hWPush _ m Q X ⟨c, s, R, rfl, hlen, hlay, hc1, hc2, hm,
    fun ok wvec' wstk' wlen' wu' wsort' m' hlen' hlay' hoth hT hF hm' => ?_⟩
  exact hQ ok wvec' wstk' wlen' wu' wsort' m' hlen' hlay' hoth hT (fun hf => (hF hf).1) hm'

private theorem dwArenaSweep_adapter {Γ : Env}
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X → Γ "full_arena_sweep" [i64] [i64] a m Q X) :
    ∀ a m Q X, FullDenseWatchSpecs.fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hnd, hdm, hrm, hm, hQ⟩
  refine hSweep _ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hnd, hdm, hrm, hm, ?_⟩
  dsimp only
  intro r vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' arena' alen' wlen' wu'
    fred' ni' nr' nb' oom' sc' m'
    hlen' hr hext hws hll hw' hnd' h01 hpos h1 h2 _ hm'
  exact hQ r vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' arena' alen' wlen' wu'
    fred' ni' nr' nb' oom' sc' m' hlen' hw' hnd' hll hext hws hr h01 hpos h1 h2 hm'

theorem full_reduce_bridge_wp (Γ : Env)
    (hIsqrt : ∀ a m Q X, fullIsqrtSpec a m Q X → Γ "full_isqrt" [i64] [i64] a m Q X)
    (hIlog10 : ∀ a m Q X, fullIlog10Spec a m Q X → Γ "full_ilog10" [i64] [i64] a m Q X)
    (hArenaNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hRecomp : ∀ a m Q X, fullRecomputeTiersSpec a m Q X →
      Γ "full_recompute_tiers" [i64] [] a m Q X)
    (hMarkRsn : ∀ a m Q X, fullMarkReasonsSpec a m Q X →
      Γ "full_mark_reasons" [i64, .bool] [] a m Q X)
    (hSortReds : ∀ a m Q X, fullSortRedsSpec a m Q X →
      Γ "full_sort_reds" [i64, i64] [] a m Q X)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullReduceSpec a m Q X → Func.wp Γ full_reduce_body a m Q X := by
  rintro ⟨h, force, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hspW, hm, hQ⟩
  rcases hspW with ⟨hlen, hw, hlm, hnd, hext, hdm⟩
  refine full_reduce_wp Γ (dwIsqrt_adapter hIsqrt) hIlog10 hArenaNext
    (dwRecomputeTiers_adapter hRecomp) hMarkRsn (dwSortReds_adapter hSortReds)
    (dwBacktrack_adapter hBacktrack) (dwPropagate_adapter hProp) (dwArenaSweep_adapter hSweep)
    _ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hlm, hnd, hext, hdm, hm,
      fun r s' m' hsp' hw' hr hu hoom hcl hfl hcv htmp htpl _ _ _ _ _ _ hws2 hpos hm' => ?_⟩
  exact hQ r s' m'
    ⟨hsp'.1.lengths, hw', hsp'.2.1, hsp'.2.2.1, hsp'.2.2.2.1, hsp'.2.2.2.2⟩
    hr hcl hfl hcv htmp htpl hws2 hu hoom (fun _ => hpos) hm'

theorem full_enter_dense_bridge_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hSweepBins : ∀ a m Q X, fullSweepBinsSpec a m Q X → Γ "full_sweep_bins" [i64] [] a m Q X)
    (hWatchPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X → Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hArenaNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X) :
    ∀ a m Q X, fullEnterDenseSpec a m Q X → Func.wp Γ full_enter_dense_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hsp, hm, hQ⟩
  rcases hsp.exists_witness with ⟨F_cur, hlen, hw, hlm, hnd, hext, _⟩
  exact full_enter_dense_wp Γ (dwBacktrack_adapter hBacktrack) (dwSweepBins_adapter hSweepBins)
    (dwWatchPush_adapter hWatchPush) (dwArenaSweep_adapter hSweep) hArenaNext _ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hlm, hnd, hext, hm,
      fun ok s' m' _ _ _ _ _ hcl0 hfl _ _ _ _ _ hd hf hm' =>
        hQ ok s' m' hcl0 hfl hd hf hm'⟩

theorem full_rebuild_watches_bridge_wp (Γ : Env)
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X → Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullRebuildWatchesSpec a m Q X →
      Func.wp Γ full_rebuild_watches_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hdn, hm, hQ⟩
  rcases hdn with ⟨⟨hlen, F_cur, hw⟩, hlm, hnd, hext, hcl0, _⟩
  exact full_rebuild_watches_wp Γ (dwArenaSweep_adapter hSweep) (dwPropagate_adapter hProp) _ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hlm, hnd, hext, hcl0, hm,
      fun r s' m' hsp' _ hcl0' hr hu hfl _ _ _ _ _ hm' =>
        hQ r s' m' hsp' hcl0' hfl hr hu hm'⟩

end Part6

end LeanQbe.T.Examples.Kissat.Full
