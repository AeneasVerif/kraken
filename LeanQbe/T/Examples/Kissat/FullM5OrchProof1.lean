module

public import LeanQbe.T.Examples.Kissat.FullM5Orch
public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Examples.Kissat.FullFastSchedLemmas
public import LeanQbe.T.Examples.Kissat.FullDefSweepLemmas1
public import LeanQbe.T.Examples.Kissat.FullM3CongBvaLemmas1
public import LeanQbe.T.Examples.Kissat.FullBvaHeapSpec
public import LeanQbe.T.Examples.Kissat.FullFastBveBudgetsLemmas1
public import LeanQbe.T.Examples.Kissat.FullM4VivBceProof1
public import LeanQbe.T.Examples.Kissat.FullM4Proof1
public import LeanQbe.T.Examples.Kissat.FullM4TernaryProof
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas2

/-!
# Kissat `D-Full` M5 Orchestration Proofs — Part 1 (`FullM5OrchProof1`, `4/19` Functions)

Proves parametric `(Γ : Env)` `Func.wp` UNSAT-only theorems (`XPost := False`, zero SAT/model
proofs, `M1`-clean `.olean` with zero `@[expose]` and zero `import all`) for the four M5
inprocessing / garbage-collection drivers:
1. `full_reduce_m5_wp` (against canonical `Full.fullReduceSpec` — drops `full_promote_reasons`,
   delegating directly to `Full.full_reduce_wp`).
2. `full_reorder_m5_wp` (against `FullM4.m4ReorderSpec` — queue reorder only, drops
   `full_reorder_heap` and `full_tumble_clauses`).
3. `full_probe_m5_wp` (against `FullFastSched.schedProbeSpec` — drops dense gate & `ternary`,
   runs `<= 2` `congruence -> sweep -> substitute` rounds while `unassigned` shrinks, then
   `full_probe_tail_m5`).
4. `full_eliminate_m5_wp` (against `FullFastSched.schedEliminateSpec` — uncapped
   `full_scale_delta_m5`, drops BVA skip, runs `forward_sub -> factor -> elim_bve ->
   rebuild_watches -> full_bce_m4`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM5Orch

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

/-! ## 1. `full_reduce_m5_wp` & `full_reorder_m5_wp` -/

section ReduceAndReorderProofs

private theorem full_reduce_m5_body_eq :
    full_reduce_m5_body = Full.full_reduce_body := by
  rfl

private theorem dwIsqrt_adapter {Γ : Env}
    (hIsqrt : ∀ a m Q X, Full.fullIsqrtSpec a m Q X → Γ "full_isqrt" [i64] [i64] a m Q X) :
    ∀ a m Q X, FullDenseWatchSpecs.fullIsqrtSpec a m Q X →
      Γ "full_isqrt" [i64] [i64] a m Q X := by
  rintro ⟨x, ⟨⟩⟩ m Q X hQ
  exact hIsqrt _ m Q X fun r hsq _ _ => hQ r (Nat.le_trans (Nat.le_mul_self r.toNat) hsq)

private theorem dwRecomputeTiers_adapter {Γ : Env}
    (hRecomp : ∀ a m Q X, Full.fullRecomputeTiersSpec a m Q X →
      Γ "full_recompute_tiers" [i64] [] a m Q X) :
    ∀ a m Q X, FullDenseWatchSpecs.fullRecomputeTiersSpec a m Q X →
      Γ "full_recompute_tiers" [i64] [] a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  refine hRecomp _ m Q X ⟨c, s, R, rfl, hlen, hm, fun _ s' m' hcore hlen' hpres hm' => ?_⟩
  rcases s' with ⟨c', sc'⟩
  change c' = s.core at hcore
  subst hcore
  exact hQ sc' m' hlen'.scratch_ok hpres.1.1 hpres.1.2 hpres.2.2.1 hm'

private theorem dwMarkReasons_adapter {Γ : Env}
    (hMarkRsn : ∀ a m Q X, Full.fullMarkReasonsSpec a m Q X →
      Γ "full_mark_reasons" [i64, .bool] [] a m Q X) :
    ∀ a m Q X, FullDenseWatchSpecs.fullMarkReasonsSpec a m Q X →
      Γ "full_mark_reasons" [i64, .bool] [] a m Q X := by
  rintro ⟨h, sf, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hm, hQ⟩
  refine hMarkRsn _ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hm,
    fun ar' m' hlen' hrefs' hper' hrm' hw' hm' => hQ ar' m' hlen' hrefs' hper' ?_ hw' hm'⟩
  intro hsf idx hidx
  exact hrm' hsf idx hidx

private theorem dwSortReds_adapter {Γ : Env}
    (hSortReds : ∀ a m Q X, Full.fullSortRedsSpec a m Q X →
      Γ "full_sort_reds" [i64, i64] [] a m Q X) :
    ∀ a m Q X, FullDenseWatchSpecs.fullSortRedsSpec a m Q X →
      Γ "full_sort_reds" [i64, i64] [] a m Q X := by
  rintro ⟨h, n, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hn, hok, hm, hQ⟩
  refine hSortReds _ m Q X ⟨c, s, R, rfl, hlen, hn, hok, hm, fun rr' m' hrr hmem hm' => ?_⟩
  exact hQ { s.scratch with red_refs := rr' } m'
    { hlen.scratch_ok with red_refs_len := hrr } rfl rfl rfl hmem hm'

private theorem dwBacktrack_adapter {Γ : Env}
    (hBt : ∀ a m Q X, Full.fullBacktrackSpec a m Q X → Γ "full_backtrack" [i64, i64] [] a m Q X) :
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
    (hProp : ∀ a m Q X, Full.fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X) :
    ∀ a m Q X, FullDenseWatchSpecs.fullPropagateSpec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hnd, hdm, hm, hQ⟩
  refine hProp _ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm, hm, ?_⟩
  dsimp only
  intro r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
    fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' m'
    hlen' hw' htr hperm hfl hr hr0 hr1 _ _ hm'
  have hnd' : FullDenseWatchSpecs.FullArenaVarsNodup
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

private theorem dwArenaSweep_adapter {Γ : Env}
    (hSweep : ∀ a m Q X, Full.fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X) :
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

/-- Parametric `Func.wp` theorem for `full_reduce_m5` against canonical `Full.fullReduceSpec`. -/
theorem full_reduce_m5_wp (Γ : Env)
    (hIsqrt : ∀ a m Q X, Full.fullIsqrtSpec a m Q X → Γ "full_isqrt" [i64] [i64] a m Q X)
    (hIlog10 : ∀ a m Q X, Full.fullIlog10Spec a m Q X → Γ "full_ilog10" [i64] [i64] a m Q X)
    (hArenaNext : ∀ a m Q X, Full.fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hRecomp : ∀ a m Q X, Full.fullRecomputeTiersSpec a m Q X →
      Γ "full_recompute_tiers" [i64] [] a m Q X)
    (hMarkRsn : ∀ a m Q X, Full.fullMarkReasonsSpec a m Q X →
      Γ "full_mark_reasons" [i64, .bool] [] a m Q X)
    (hSortReds : ∀ a m Q X, Full.fullSortRedsSpec a m Q X →
      Γ "full_sort_reds" [i64, i64] [] a m Q X)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hProp : ∀ a m Q X, Full.fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X)
    (hSweep : ∀ a m Q X, Full.fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X) :
    ∀ a m Q X, Full.fullReduceSpec a m Q X → Func.wp Γ full_reduce_m5_body a m Q X := by
  rintro ⟨h, force, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, ⟨hlen, hw, hlm, hnd, hext, hdm⟩, hm, hQ⟩
  rw [Func.wp, full_reduce_m5_body_eq]
  refine Full.full_reduce_wp Γ (dwIsqrt_adapter hIsqrt) hIlog10 hArenaNext
    (dwRecomputeTiers_adapter hRecomp) (dwMarkReasons_adapter hMarkRsn)
    (dwSortReds_adapter hSortReds) (dwBacktrack_adapter hBacktrack)
    (dwPropagate_adapter hProp) (dwArenaSweep_adapter hSweep)
    (c.hdr, force, ()) m Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hlm, hnd, hext, hdm, hm, ?_⟩
  intro r s' m' hdw hw' hr hu hoom hcl hfu hcv htmp htl _ _ _ _ _ _ hws2 hpos hm'
  exact hQ r s' m' ⟨hdw.1.lengths, hw', hdw.2.1, hdw.2.2.1, hdw.2.2.2.1, hdw.2.2.2.2⟩ hr hcl hfu
    hcv htmp htl hws2 hu hoom (fun _ => hpos) hm'

open scoped Full.FullArenaTactics

private theorem m5_arenaPermEq_refl (k : FullCoreState) : FullArenaPermEq k k :=
  ⟨rfl, rfl, fun _ _ => ⟨rfl, rfl, List.Perm.refl _⟩⟩

/-- Parametric `Func.wp` theorem for `full_reorder_m5` against `FullM4.m4ReorderSpec`. -/
theorem full_reorder_m5_wp (Γ : Env)
    (hQueue : ∀ a m Q X, FullM4Ternary.fullReorderQueueSpec a m Q X →
      Γ "full_reorder_queue" [i64] [i64] a m Q X) :
    ∀ a m Q X, FullM4.m4ReorderSpec a m Q X → Func.wp Γ full_reorder_m5_body a m Q X := by
  rintro ⟨h, _budget, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hsp, hm, hQ⟩
  unfold Func.wp full_reorder_m5_body
  c0_hsteps
  c0_call hQueue
  refine ⟨c, s, R, rfl, hsp.lengths, hm, ?_⟩
  rintro ⟨r, ⟨⟩⟩ s1 m1 hcore1 hlen1 hpres1 hm1
  change (FullMem c s1 ⋆ R) m1 at hm1
  have hsp1 := hsp.of_safetySlice hlen1 hcore1 hpres1
  have hce1 : s1.core = s.core := fullCoreState_agrees_with_scratch hcore1
  c0_hsteps
  exact hQ r s1 m1 hsp1 (hce1 ▸ m5_arenaPermEq_refl s.core) (by rw [hce1]) (by rw [hce1]) hm1

end ReduceAndReorderProofs

/-! ## 2. Local State & Invariant Helpers for `full_probe_m5` & `full_eliminate_m5` -/

section SharedHelpers

private theorem m5_sparseInv_with_scratch_keep {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) {sc' : FullScratch} (hok : sc'.LengthsOk c)
    (hll : sc'.last_learned = s.scratch.last_learned)
    (hext : sc'.extend_len = s.scratch.extend_len) :
    FullSparseInv c F0 { s with scratch := sc' } :=
  h.of_safetySlice (h.lengths.with_scratch hok) rfl ⟨hll, hext⟩

private theorem m5_denseInv_with_scratch_keep {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullDenseInv c F0 s) {sc' : FullScratch} (hok : sc'.LengthsOk c)
    (hll : sc'.last_learned = s.scratch.last_learned)
    (hext : sc'.extend_len = s.scratch.extend_len) :
    FullDenseInv c F0 { s with scratch := sc' } :=
  h.of_safetySlice (h.lengths.with_scratch hok) rfl ⟨hll, hext⟩

private theorem m5_tmkZero_of_init_loop {s : FullState}
    {tmki : List (BitVec 32)} (hinit : ∀ k < s.core.cur_vars, tmki[k]?.getD 0#32 = 0#32) :
    FullFastBveBudgets.TmkZero { s with scratch := { s.scratch with tarjan_mark := tmki } } :=
  fun v hv => hinit v hv

private theorem m5_bv64_add1 {x : BitVec 64} (hx : x.toNat + 1 < 2 ^ 64) :
    (x + 1#64).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt hx]

end SharedHelpers

/-! ## 3. `full_probe_m5_wp` (`<= 2` Rounds `cong -> sweep -> subst` + `full_probe_tail_m5`) -/

section ProbeM5Proofs

open scoped Full.FullArenaTactics

/-- Parametric `Func.wp` theorem for `full_probe_m5` against `FullFastSched.schedProbeSpec`. -/
theorem full_probe_m5_wp (Γ : Env)
    (hDticks : ∀ a m Q X, FullFastSched.schedProbeDticksSpec a m Q X →
      Γ "full_probe_dticks_m5" [i64, .bool] [i64] a m Q X)
    (hIlog : ∀ a m Q X, Full.fullIlog10Spec a m Q X → Γ "full_ilog10" [i64] [i64] a m Q X)
    (hScale : ∀ a m Q X, FullFastSched.schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta_m5" [i64, i64] [i64] a m Q X)
    (hEnter : ∀ a m Q X, FullFastSched.schedEnterDenseSpec a m Q X →
      Γ "full_enter_dense" [i64] [.bool] a m Q X)
    (hCongD : ∀ a m Q X, FullM3CongBva.m3CongruenceDenseSpec a m Q X →
      Γ "full_congruence_dense" [i64, i64] [i64] a m Q X)
    (hSweepD : ∀ a m Q X, FullDefSweep.fullSweepDenseSpec a m Q X →
      Γ "full_sweep_dense_m5" [i64, i64, i64] [i64] a m Q X)
    (hReb : ∀ a m Q X, Full.fullRebuildWatchesSpec a m Q X →
      Γ "full_rebuild_watches" [i64] [i64] a m Q X)
    (hSubst : ∀ a m Q X, Full.fullSubstituteSpec a m Q X → Γ "full_substitute" [i64] [i64] a m Q X)
    (hTail : ∀ a m Q X, FullFastSched.schedProbeTailSpec a m Q X →
      Γ "full_probe_tail_m5" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, FullFastSched.schedProbeSpec a m Q X →
      Func.wp Γ full_probe_m5_body a m Q X := by
  rintro ⟨h, initial, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hcl0, hm, hQ⟩
  unfold Func.wp full_probe_m5_body
  c0_hsteps
  c0_call hDticks
  refine ⟨c, s, R, rfl, hinv.lengths, hm, ?_⟩
  intro dticks
  c0_hsteps_nogrp
  refine wp_join_state0 (α := FullState)
    (fun s0 m0 => FullSparseInv c F0 s0 ∧ s0.core.cur_level = 0 ∧
      s0.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s0 ⋆ R) m0)
    (fun _ s0 m0 ⟨hinv0, hcl0', hfu0, hm0⟩ => by
      c0_hsteps_nogrp
      refine wp_while_break_state (α := BitVec 64 × FullState) (β := BitVec 64 × FullState)
        (fun p => (p.1, ()))
        (fun p mb => FullSparseInv c F0 p.2 ∧ p.2.core.cur_level = 0 ∧
          p.2.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c p.2 ⋆ R) mb)
        (fun p => (p.1, ()))
        (fun p => 2 - p.1.toNat)
        (fun p ml => FullSparseInv c F0 p.2 ∧ p.2.core.cur_level = 0 ∧
          p.2.core.fuel.toNat ≤ s.core.fuel.toNat ∧ p.1.toNat ≤ 2 ∧ (FullMem c p.2 ⋆ R) ml)
        ?_ ?_ ?_
      · rintro _ ⟨_r, st_ex⟩ m_ex ⟨hinv_ex, hcl_ex, hfu_ex, hm_ex⟩
        dsimp only at hfu_ex
        c0_hsteps
        c0_call hTail
        refine ⟨c, F0, st_ex, R, rfl, hinv_ex, hcl_ex, hm_ex, ?_⟩
        intro rt st_t mt hinv_t hcl_t hfu_t _ hut ht_m
        c0_hsteps
        · exact hQ 20#64 st_t mt hinv_t.lengths (by omega) (Or.inr rfl) (fun _ => hut ‹_›)
            (fun h => by cases h) ht_m
        · let st_f : FullState :=
            { st_t with scratch := { st_t.scratch with fwd_sub_cnt := st_t.scratch.search_ticks } }
          have hinv_f : FullSparseInv c F0 st_f :=
            m5_sparseInv_with_scratch_keep hinv_t { hinv_t.lengths.scratch_ok with } rfl rfl
          have hfu_f : st_f.core.fuel.toNat ≤ s.core.fuel.toNat := by
            change st_t.core.fuel.toNat ≤ s.core.fuel.toNat; omega
          exact hQ 1#64 st_f _ hinv_f.lengths hfu_f (Or.inl rfl) (fun h => by cases h)
            (fun _ => ⟨hinv_f, hcl_t⟩) hm
      · rintro B L ⟨round, st⟩ ml hB hL ⟨hsp, hcl_st, hfu_st, hr_le, hml⟩
        dsimp only at hfu_st
        c0_hsplit
        · have hr_lt : round.toNat < 2 := by bv_omega
          have hr1 : (round + 1#64).toNat = round.toNat + 1 := by bv_omega
          c0_hsteps_nogrp
          refine wp_join_state0 (α := FullState)
            (fun s1 m1 => FullSparseInv c F0 s1 ∧ s1.core.cur_level = 0 ∧
              s1.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s1 ⋆ R) m1)
            (fun _ s1 m1 ⟨hinv1, hcl1, hfu1, hm1⟩ => by
              c0_hsteps_nogrp
              refine wp_join_state0 (α := FullState)
                (fun s2 m2 => FullSparseInv c F0 s2 ∧ s2.core.cur_level = 0 ∧
                  s2.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s2 ⋆ R) m2)
                (fun _ s2 m2 ⟨hinv2, hcl2, hfu2, hm2⟩ => by
                  c0_hsteps
                  · exact hB (round, s2) m2 ⟨hinv2, hcl2, hfu2, hm2⟩
                  · exact hL (round + 1#64, s2) m2 (by dsimp only; omega)
                      ⟨hinv2, hcl2, hfu2, by dsimp only; omega, hm2⟩)
                (fun J2 hJ2 => by
                  c0_hsplit
                  · c0_hsteps; c0_call hSubst
                    refine ⟨c, F0, s1, R, rfl, hinv1, hm1, ?_⟩
                    intro rs s2 m2 hinv2 hcl2 hfu2 _ hus2 hm2
                    c0_hsteps
                    · exact hQ 20#64 s2 m2 hinv2.lengths (by omega) (Or.inr rfl)
                        (fun _ => hus2 ‹_›) (fun h => by cases h) hm2
                    · exact hJ2 s2 m2 ⟨hinv2, hcl2, by omega, hm2⟩
                  · c0_hsteps; exact hJ2 s1 m1 ⟨hinv1, hcl1, hfu1, hm1⟩))
            (fun J1 hJ1 => by
              c0_hsteps
              c0_call hEnter
              refine ⟨c, F0, st, R, rfl, hsp, hml, ?_⟩
              intro ok s2 m2 hcl2 hfu2 hok_d hfail_s hm2
              c0_hsplit
              · have hden2 : FullDenseInv c F0 s2 := hok_d ‹_›
                c0_hsteps; c0_call hCongD
                refine ⟨c, F0, s2, R, rfl, hden2, hm2, ?_⟩
                intro rc s3 m3 hden3 _ hfu3 _ huc3 hm3
                have hfu3' : s3.core.fuel.toNat ≤ s.core.fuel.toNat := by
                  rw [hfu3]; exact Nat.le_trans hfu2 hfu_st
                c0_hsplit
                · c0_hsteps; c0_call hReb
                  refine ⟨c, F0, s3, R, rfl, hden3, hm3, ?_⟩
                  intro _ s3r m3r hsp3r _ hfu3r _ _ hm3r
                  c0_hsteps
                  exact hQ 20#64 s3r m3r hsp3r.lengths (by omega) (Or.inr rfl)
                    (fun _ => huc3 ‹_›) (fun h => by cases h) hm3r
                · c0_hsteps; c0_call hSweepD
                  refine ⟨c, F0, s3, R, rfl, hden3, hm3, ?_⟩
                  intro rw4 s4 m4 hden4 _ hfu4 _ huw4 hm4
                  c0_hsplit
                  · c0_hsteps; c0_call hReb
                    refine ⟨c, F0, s4, R, rfl, hden4, hm4, ?_⟩
                    intro _ s4r m4r hsp4r _ hfu4r _ _ hm4r
                    c0_hsteps
                    exact hQ 20#64 s4r m4r hsp4r.lengths (by omega) (Or.inr rfl)
                      (fun _ => huw4 ‹_›) (fun h => by cases h) hm4r
                  · c0_hsteps; c0_call hReb
                    refine ⟨c, F0, s4, R, rfl, hden4, hm4, ?_⟩
                    intro rrb s4r m4r hsp4r hcl4r hfu4r _ hurb hm4r
                    c0_hsteps
                    · exact hQ 20#64 s4r m4r hsp4r.lengths (by omega) (Or.inr rfl)
                        (fun _ => hurb ‹_›) (fun h => by cases h) hm4r
                    · exact hJ1 s4r m4r ⟨hsp4r, hcl4r, by omega, hm4r⟩
              · have hsp2 : FullSparseInv c F0 s2 := hfail_s ‹_›
                c0_hsteps
                · exact hQ 20#64 s2 m2 hsp2.lengths (by omega) (Or.inr rfl)
                    (fun _ => hsp2.inconsistent_unsat ‹_›) (fun h => by cases h) hm2
                · exact hJ1 s2 m2 ⟨hsp2, hcl2, by omega, hm2⟩)
        · c0_hsteps; exact hB (round, st) ml ⟨hsp, hcl_st, hfu_st, hml⟩
      · intro _ L _ hL; c0_hsteps
        exact hL (0#64, s0) m0 ⟨hinv0, hcl0', hfu0, Nat.zero_le _, hm0⟩)
    (fun J0 hJ0 => by
      c0_hsplit
      · c0_hsteps; exact hJ0 s m ⟨hinv, hcl0, Nat.le_refl _, hm⟩
      · c0_hsteps
        let s0a : FullState :=
          { s with scratch := { s.scratch with probings := s.scratch.probings + 1#64 } }
        have hlen0a : s0a.LengthsOk c := ⟨hinv.lengths.core_ok, { hinv.lengths.scratch_ok with }⟩
        c0_call hIlog; intro logp _ _
        c0_hsteps; c0_call hScale; refine ⟨c, s0a, R, rfl, hlen0a, hm, ?_⟩
        intro delta
        c0_hsteps
        let s0b : FullState :=
          { s0a with scratch := { s0a.scratch with probe_limit := s0a.scratch.conflicts + delta } }
        have hinv0b : FullSparseInv c F0 s0b :=
          m5_sparseInv_with_scratch_keep hinv { hinv.lengths.scratch_ok with } rfl rfl
        exact hJ0 s0b _ ⟨hinv0b, hcl0, Nat.le_refl _, hm⟩)

end ProbeM5Proofs

/-! ## 4. `full_eliminate_m5_wp` (`fwd_sub -> factor -> elim_bve -> rebuild -> full_bce_m4`) -/

section EliminateM5Proofs

open scoped Full.FullArenaTactics

/-- Parametric `Func.wp` theorem for `full_eliminate_m5` against
`FullFastSched.schedEliminateSpec`. -/
theorem full_eliminate_m5_wp (Γ : Env)
    (hDticks : ∀ a m Q X, FullFastSched.schedElimDticksSpec a m Q X →
      Γ "full_elim_dticks_m5" [i64, .bool] [i64] a m Q X)
    (hIlog : ∀ a m Q X, Full.fullIlog10Spec a m Q X → Γ "full_ilog10" [i64] [i64] a m Q X)
    (hScale : ∀ a m Q X, FullFastSched.schedScaleDeltaSpec a m Q X →
      Γ "full_scale_delta_m5" [i64, i64] [i64] a m Q X)
    (hEnter : ∀ a m Q X, FullFastSched.schedEnterDenseSpec a m Q X →
      Γ "full_enter_dense" [i64] [.bool] a m Q X)
    (hFwd : ∀ a m Q X, FullFastBveBudgets.fullForwardSubFastSpec a m Q X →
      Γ "full_forward_sub" [i64, i64] [i64] a m Q X)
    (hMin : ∀ a m Q X, FullFastSched.schedMinU64Spec a m Q X →
      Γ "full_min_u64" [i64, i64] [i64] a m Q X)
    (hFact : ∀ a m Q X, FullBvaHeap.fullFactorHeapSpec a m Q X →
      Γ "full_factor" [i64, i64] [i64] a m Q X)
    (hBve : ∀ a m Q X, FullM3CongBva.m3ElimBveSpec a m Q X →
      Γ "full_elim_bve" [i64, i64] [i64] a m Q X)
    (hReb : ∀ a m Q X, Full.fullRebuildWatchesSpec a m Q X →
      Γ "full_rebuild_watches" [i64] [i64] a m Q X)
    (hBce : ∀ a m Q X, FullM4VivBce.fullBceM4Spec a m Q X →
      Γ "full_bce_m4" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, FullFastSched.schedEliminateSpec a m Q X →
      Func.wp Γ full_eliminate_m5_body a m Q X := by
  rintro ⟨h, initial, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hcl0, hm, hQ⟩
  unfold Func.wp full_eliminate_m5_body
  c0_hsteps; c0_call hDticks; refine ⟨c, s, R, rfl, hinv.lengths, hm, ?_⟩
  intro dticks
  c0_hsteps_nogrp
  refine wp_join_state0 (α := FullState)
    (fun s0 m0 => FullSparseInv c F0 s0 ∧ s0.core.cur_level = 0 ∧
      s0.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s0 ⋆ R) m0)
    (fun _ s0 m0 ⟨hinv0, _, hfu0, hm0⟩ => by
      c0_hsteps; c0_call hEnter; refine ⟨c, F0, s0, R, rfl, hinv0, hm0, ?_⟩
      intro ok s1 m1 hcl1 hfu1 hok_d hfail_s hm1
      c0_hsplit
      · have hden1 : FullDenseInv c F0 s1 := hok_d ‹_›
        c0_hsteps_nogrp
        refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
          (fun b => (b, ())) (fun _ => True)
          (fun _ _ _ => by
            c0_hsteps; c0_call hMin; intro _ _
            c0_hsteps; c0_call hFwd; refine ⟨c, F0, s1, R, rfl, hden1, hm1, ?_⟩
            intro fs s2 m2 hden2 _ hfu2 _ huf2 hm2
            let s2r : FullState :=
              { s2 with scratch := { s2.scratch with fwd_sub_cnt := s1.scratch.fwd_sub_cnt } }
            have hden2r : FullDenseInv c F0 s2r :=
              m5_denseInv_with_scratch_keep hden2 { hden2.lengths.scratch_ok with } rfl rfl
            have hfu2r : s2r.core.fuel.toNat ≤ s.core.fuel.toNat := by
              change s2.core.fuel.toNat ≤ s.core.fuel.toNat; rw [hfu2]; omega
            c0_hsplit
            · c0_hsteps; c0_call hReb; refine ⟨c, F0, s2r, R, rfl, hden2r, hm, ?_⟩
              intro _ s3 m3 hsp3 hcl3 hfu3 _ _ hm3; c0_hsteps
              exact hQ 20#64 s3 m3 hsp3 hcl3 (by omega) (Or.inr rfl) (fun _ => huf2 ‹_›) hm3
            · c0_hsteps_nogrp
              refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
                (fun b => (b, ())) (fun _ => True)
                (fun _ _ _ => by
                  c0_hsteps; c0_call hMin; intro _ _
                  c0_hsteps; c0_call hFact
                  refine ⟨c, F0, s2r, R, rfl, hden2r, hm, ?_⟩
                  intro _ s2f m2f hden2f _ hfu2f _ hm2f
                  let cv2 := s2f.core.cur_vars
                  have hcv2_le : cv2 ≤ c.max_vars := hden2f.lengths.core_ok.cur_vars_le
                  have hmx := c.hmaxv; unfold dimacsBound at hmx
                  have hcv2_64 : cv2 < 2 ^ 64 := by omega
                  have htl2 := hden2f.lengths.scratch_ok.tarjan_mark_len
                  c0_hsteps_nogrp
                  refine wp_loop_inv
                    (fun (ti, ()) mt => ∃ tmki : List (BitVec 32),
                      tmki.length = 2 * c.max_vars ∧ ti.toNat ≤ cv2 ∧
                      (∀ k < ti.toNat, tmki[k]?.getD 0#32 = 0#32) ∧
                      (FullMem c { s2f with scratch :=
                        { s2f.scratch with tarjan_mark := tmki } } ⋆ R) mt)
                    (fun (ti, ()) _ => cv2 - ti.toNat)
                    (fun _ hJt => by
                      c0_hsteps; exact hJt (0#64, ()) m2f
                        ⟨s2f.scratch.tarjan_mark, htl2, Nat.zero_le _,
                         fun _ h => by simp at h, hm2f⟩)
                    (fun _ (ti, ()) mt ⟨tmki, htli, hti_le, hinit, hmt⟩ iht => by
                      c0_hsplit
                      · have hti_lt : ti.toNat < cv2 := by
                          have hlt : ti.toNat < (BitVec.ofNat 64 cv2).toNat := by assumption
                          rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcv2_64] at hlt
                        have hti_arr : ti.toNat < tmki.length := by omega
                        have hti1 : (ti + 1#64).toNat = ti.toNat + 1 := m5_bv64_add1 (by omega)
                        c0_hsteps
                        exact iht (ti + 1#64, ()) _ (by dsimp only; omega)
                          ⟨tmki.set ti.toNat 0#32, by simp [htli], by omega,
                           fun k hk => by
                             rw [hti1] at hk
                             by_cases hkt : k = ti.toNat
                             · subst hkt; rw [List.getElem?_set_self (by omega), Option.getD_some]
                             · rw [List.getElem?_set_ne (Ne.symm hkt)]; exact hinit k (by omega),
                           hm⟩
                      · have hti_eq : ti.toNat = cv2 := by
                          have hnot : ¬ ti.toNat < (BitVec.ofNat 64 cv2).toNat := by assumption
                          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcv2_64] at hnot
                          omega
                        rw [hti_eq] at hinit
                        let s2t : FullState :=
                          { s2f with scratch := { s2f.scratch with tarjan_mark := tmki } }
                        have hden2t : FullDenseInv c F0 s2t :=
                          m5_denseInv_with_scratch_keep hden2f
                            { hden2f.lengths.scratch_ok with tarjan_mark_len := htli } rfl rfl
                        have htmk2 := m5_tmkZero_of_init_loop hinit
                        have hfu2t : s2t.core.fuel.toNat ≤ s.core.fuel.toNat := by
                          dsimp only [s2t]; rw [hfu2f]; exact hfu2r
                        c0_hsteps_nogrp
                        refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
                          (fun b => (b, ())) (fun _ => True)
                          (fun _ _ _ => by
                            c0_hsteps; c0_call hBve
                            refine ⟨c, F0, s2t, R, rfl, hden2t, htmk2, hmt, ?_⟩
                            intro res s3 m3 hden3 _ hfu3 _ hres_u hm3
                            c0_hsteps; c0_call hReb
                            refine ⟨c, F0, s3, R, rfl, hden3, hm3, ?_⟩
                            intro rr s4 m4 hsp4 hcl4 hfu4 _ hue4 hm4
                            have hfu4' : s4.core.fuel.toNat ≤ s.core.fuel.toNat := by omega
                            let s4' : FullState :=
                              { s4 with scratch :=
                                { s4.scratch with fwd_str_cnt := s4.scratch.search_ticks } }
                            have hsp4' : FullSparseInv c F0 s4' :=
                              m5_sparseInv_with_scratch_keep hsp4
                                { hsp4.lengths.scratch_ok with } rfl rfl
                            have hfu4s : s4'.core.fuel.toNat ≤ s.core.fuel.toNat := by
                              change s4.core.fuel.toNat ≤ s.core.fuel.toNat; exact hfu4'
                            c0_hsteps_nogrp
                            refine wp_join_group
                              (fun _ m_e =>
                                (res = 20#64 ∨ rr = 20#64 ∨ s4.core.inconsistent ≠ 0#64) ∧
                                m_e = m4)
                              (fun _ ⟨⟩ m_e ⟨hdisj, hm_e⟩ => by
                                subst hm_e
                                c0_hsteps
                                have huns : F0.Unsat := by
                                  rcases hdisj with rfl | rfl | hinc
                                  · exact hres_u rfl
                                  · exact hue4 rfl
                                  · exact hsp4.inconsistent_unsat hinc
                                exact hQ 20#64 s4' _ hsp4' hcl4 hfu4s (Or.inr rfl)
                                  (fun _ => huns) hm)
                              (fun Jex hJex => by
                                c0_hsteps_nogrp
                                · exact hJex () m4 ⟨Or.inl ‹_›, rfl⟩
                                · exact hJex () m4 ⟨Or.inr (Or.inl ‹_›), rfl⟩
                                · exact hJex () m4 ⟨Or.inr (Or.inr ‹_›), rfl⟩
                                · refine wp_join_state0 (α := FullState)
                                    (fun s5 m5 => FullSparseInv c F0 s5 ∧ s5.core.cur_level = 0 ∧
                                      s5.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                                      (FullMem c s5 ⋆ R) m5)
                                    (fun _ s5 m5 ⟨hsp5, hcl5, hfu5, hm5⟩ => by
                                      c0_hsteps
                                      let s5' : FullState :=
                                        { s5 with scratch :=
                                          { s5.scratch with
                                            fwd_str_cnt := s5.scratch.search_ticks } }
                                      have hsp5' : FullSparseInv c F0 s5' :=
                                        m5_sparseInv_with_scratch_keep hsp5
                                          { hsp5.lengths.scratch_ok with } rfl rfl
                                      exact hQ 1#64 s5' _ hsp5' hcl5 hfu5 (Or.inl rfl)
                                        (fun h => by cases h) hm)
                                    (fun Jbce hJbce => by
                                      c0_hsplit
                                      · c0_hsplit
                                        · c0_hsteps_nogrp
                                          refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
                                            (fun b => (b, ())) (fun _ => True)
                                            (fun _ _ _ => by
                                              c0_hsteps; c0_call hMin; intro bce_bud _
                                              c0_hsteps; c0_call hBce
                                              refine ⟨c, F0, s4, R, rfl, hsp4, hcl4, hm4, ?_⟩
                                              intro rb s5 m5 hsp5 hcl5 hfu5 _ hub5 hm5
                                              have hfu5' : s5.core.fuel.toNat ≤ s.core.fuel.toNat :=
                                                by omega
                                              let s5' : FullState :=
                                                { s5 with scratch :=
                                                  { s5.scratch with
                                                    fwd_str_cnt := s5.scratch.search_ticks } }
                                              have hsp5' : FullSparseInv c F0 s5' :=
                                                m5_sparseInv_with_scratch_keep hsp5
                                                  { hsp5.lengths.scratch_ok with } rfl rfl
                                              c0_hsteps
                                              · exact hQ 20#64 s5' _ hsp5' hcl5
                                                  (by change s5.core.fuel.toNat ≤ _; omega)
                                                  (Or.inr rfl) (fun _ => hub5 ‹_›) hm
                                              · exact hJbce s5 m5 ⟨hsp5, hcl5, hfu5', hm5⟩)
                                            (fun _ hJbb => by
                                              c0_hsteps
                                              · exact hJbb _ trivial
                                              · exact hJbb _ trivial)
                                        · c0_hsteps; exact hJbce s4 m4 ⟨hsp4, hcl4, hfu4', hm4⟩
                                      · c0_hsteps; exact hJbce s4 m4 ⟨hsp4, hcl4, hfu4', hm4⟩)))
                          (fun _ hJb => by
                            c0_hsteps
                            · exact hJb _ trivial
                            · c0_call hMin; intro b _; exact hJb b trivial)))
                (fun _ hJfb => by c0_hsteps <;> exact hJfb _ trivial))
          (fun _ hJfb => by c0_hsteps <;> exact hJfb _ trivial)
      · have hsp1 : FullSparseInv c F0 s1 := hfail_s ‹_›
        let s1' : FullState :=
          { s1 with scratch := { s1.scratch with fwd_str_cnt := s1.scratch.search_ticks } }
        have hsp1' : FullSparseInv c F0 s1' :=
          m5_sparseInv_with_scratch_keep hsp1 { hsp1.lengths.scratch_ok with } rfl rfl
        have hfu1' : s1'.core.fuel.toNat ≤ s.core.fuel.toNat := by
          change s1.core.fuel.toNat ≤ s.core.fuel.toNat; omega
        c0_hsteps
        · exact hQ 20#64 s1' _ hsp1' hcl1 hfu1' (Or.inr rfl)
            (fun _ => hsp1'.inconsistent_unsat ‹_›) hm
        · exact hQ 1#64 s1' _ hsp1' hcl1 hfu1' (Or.inl rfl) (fun h => by cases h) hm)
    (fun J1 hJ1 => by
      c0_hsplit
      · c0_hsteps; exact hJ1 s m ⟨hinv, hcl0, Nat.le_refl _, hm⟩
      · c0_hsteps
        let s0a : FullState :=
          { s with scratch := { s.scratch with eliminations := s.scratch.eliminations + 1#64 } }
        have hlen0a : s0a.LengthsOk c :=
          ⟨hinv.lengths.core_ok, { hinv.lengths.scratch_ok with }⟩
        c0_call hIlog; intro loge _ _
        c0_hsteps_nogrp
        refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
          (fun b => (b, ())) (fun _ => True)
          (fun _ _ _ => by
            c0_hsteps; c0_call hScale; refine ⟨c, s0a, R, rfl, hlen0a, hm, ?_⟩
            intro delta
            let s0b : FullState :=
              { s0a with scratch :=
                { s0a.scratch with elim_limit := s0a.scratch.conflicts + delta } }
            have hinv0b : FullSparseInv c F0 s0b :=
              m5_sparseInv_with_scratch_keep hinv { hinv.lengths.scratch_ok with } rfl rfl
            let s0c : FullState :=
              { s0b with scratch :=
                { s0b.scratch with elim_bound := s0b.scratch.elim_bound + 2#64 } }
            have hinv0c : FullSparseInv c F0 s0c :=
              m5_sparseInv_with_scratch_keep hinv0b { hinv0b.lengths.scratch_ok with } rfl rfl
            c0_hsteps
            · exact hJ1 s0c _ ⟨hinv0c, hcl0, Nat.le_refl _, hm⟩
            · exact hJ1 s0b _ ⟨hinv0b, hcl0, Nat.le_refl _, hm⟩
            · exact hJ1 s0b _ ⟨hinv0b, hcl0, Nat.le_refl _, hm⟩)
          (fun _ hJec => by c0_hsteps <;> exact hJec _ trivial))

end EliminateM5Proofs

end LeanQbe.T.Examples.Kissat.FullM5Orch
