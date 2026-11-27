/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S6aProof0

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S6aLiftsSpec
public import LeanQbe.T.Examples.Kissat.FullM7BcpHot
public import LeanQbe.T.Examples.Kissat.FullM6CompactFlush
public import LeanQbe.T.Examples.Kissat.FullM4Compact
public import LeanQbe.T.Examples.Kissat.FullFidelityStep9
public import LeanQbe.T.Examples.Kissat.FullFidelityStep10
public import LeanQbe.T.Examples.Kissat.FullM6Orch
public import LeanQbe.T.Examples.Kissat.FullM7Walk
public import LeanQbe.T.Examples.Kissat.FullM7Search
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullLuckyLemmas1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 13 Shard `S6a` — Proof Group 0

Callee-parametric `(Γ : Env)` Step-13 `Func.wp` lift theorems (`0` `@[expose]` on theorems/lemmas,
`0` `import all`, `0` cross-shard `S0..S5` imports, every theorem `<= 350` LOC, file `< 1,500` LOC):
1. `full_propagate_step13_wp` / `full_propagate_step13_s3_wp` (`FullM7BcpHot.full_bcp_hot_body`)
2. `full_flush_trail_step13_wp` (`FullM6CompactFlush.full_flush_trail_body`)
3. `full_compact_flush_step13_wp` (`FullFidelityStep9.full_compact_flush_body`)
4. `full_compact_step13_wp` (`FullM4Compact.full_compact_body`)
5. `full_rebuild_watches_nosort_fid_step13_wp`
   (`FullFidelityStep10.full_rebuild_watches_nosort_fid_body`)
6. `full_rebuild_watches_step13_wp` (`FullFidelityStep9.full_rebuild_watches_body`)
7. `full_parse_body_step13_wp` (`FullM6Orch.full_parse_body_body`)
8. `full_walk_step13_wp` (`FullM7Walk.full_walk_warmup_m7_body` — `full_walk` /
   `full_walk_warmup_m7`)
9. `full_simplify_m6_step13_wp` (`FullM6Orch.full_simplify_m6_body`)
10. `full_lucky_late_m7_step13_wp` (`FullM7Search.full_lucky_late_m7_body`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S6a

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6BcpS15
open LeanQbe.T.Examples.Kissat.FullM6CompactFlush
open LeanQbe.T.Examples.Kissat.FullM4Compact
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM7Search
open LeanQbe.T.Examples.Kissat.FullM7Walk
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open LeanQbe.T.Examples.Kissat.Full.FullDenseWatchHelpers
open Kraken.Bedrock2.Test

open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.FullM6ProofUtil.M6ProofUtilTactics

/-! ## 0. Shared Proof0 Tactics & Invariant Helpers -/

local macro "s6p0_strip" : tactic =>
  `(tactic| first | apply FullM6Hdr.m6h_strip_32_64 | apply FullM6Hdr.m6h_strip_8_32 |
    apply FullM6Hdr.m6h_strip_8_64)
local elab "s6p0_hsteps_ns" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, splitJnz := false } 10000
local macro "s6p0_steps" : tactic =>
  `(tactic| (
    (try change LeanQbe.T.Func.wp _ _ _ _ _ _)
    (first | (s6p0_strip; repeat s6p0_strip) | skip)
    s6p0_hsteps_ns
    repeat (any_goals (s6p0_strip; repeat s6p0_strip); s6p0_hsteps_ns)))
local macro "s6p0_jnz" h:ident : tactic =>
  `(tactic| (rw [wp_jnz]; dsimp only [Arg.val]; refine ⟨fun $h => ?_, fun $h => ?_⟩))

private structure S13RebuildOk (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s st : FullState) (ext : List (BitVec 64)) : Prop where
  spW : FullSparseInvW c F0 F_cur st
  extOk : M6HdrExtOk ext
  cl0 : st.core.cur_level = 0
  fuelLe : st.core.fuel.toNat ≤ s.core.fuel.toNat

private theorem s13RebuildOk_sweep {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {ext : List (BitVec 64)} (hok : S13RebuildOk c F0 F_cur s st ext)
    {vals' : List (BitVec 8)} {flags' lvl' rsns' trl' tp' wvec' wstk' arena' : List (BitVec 32)}
    {te' alen' wlen' : Nat} {unass' unfl' wu' fred' ni' nr' nb' oom' : BitVec 64}
    {sc' : FullScratch}
    (hlen' :
      ({ st with
          core :=
            { st.core with
              vals := vals', flags := flags', lvl := lvl', rsns := rsns',
              trl := trl', trail_pos := tp', trail_end := te', unassigned := unass',
              unflushed := unfl', wvec := wvec', wstk := wstk', arena := arena',
              arena_len := alen', wlen := wlen', wusable := wu', arena_garbage := 0#64,
              first_reducible := fred', num_irred := ni', num_redundant := nr',
              num_binary := nb', oom := oom' }
          scratch := sc' } : FullState).LengthsOk c)
    (hw' : FullWitnessInv c F0 F_cur
      { st.core with
        vals := vals', flags := flags', lvl := lvl', rsns := rsns',
        trl := trl', trail_pos := tp', trail_end := te', unassigned := unass', unflushed := unfl',
        wvec := wvec', wstk := wstk', arena := arena', arena_len := alen', wlen := wlen',
        wusable := wu', arena_garbage := 0#64, first_reducible := fred', num_irred := ni',
        num_redundant := nr', num_binary := nb', oom := oom' })
    (hnd' : FullArenaVarsNodup
      { st with
        core :=
          { st.core with
            vals := vals', flags := flags', lvl := lvl', rsns := rsns',
            trl := trl', trail_pos := tp', trail_end := te', unassigned := unass',
            unflushed := unfl', wvec := wvec', wstk := wstk', arena := arena', arena_len := alen',
            wlen := wlen', wusable := wu', arena_garbage := 0#64, first_reducible := fred',
            num_irred := ni', num_redundant := nr', num_binary := nb', oom := oom' }
        scratch := sc' })
    (hll' : FullLastLearnedWf
      { st with
        core :=
          { st.core with
            vals := vals', flags := flags', lvl := lvl', rsns := rsns',
            trl := trl', trail_pos := tp', trail_end := te', unassigned := unass',
            unflushed := unfl', wvec := wvec', wstk := wstk', arena := arena', arena_len := alen',
            wlen := wlen', wusable := wu', arena_garbage := 0#64, first_reducible := fred',
            num_irred := ni', num_redundant := nr', num_binary := nb', oom := oom' }
        scratch := sc' })
    (hext' : sc'.extend_len = st.scratch.extend_len) :
    S13RebuildOk c F0 F_cur s
      { st with
        core :=
          { st.core with
            vals := vals', flags := flags', lvl := lvl', rsns := rsns',
            trl := trl', trail_pos := tp', trail_end := te', unassigned := unass',
            unflushed := unfl', wvec := wvec', wstk := wstk', arena := arena', arena_len := alen',
            wlen := wlen', wusable := wu', arena_garbage := 0#64, first_reducible := fred',
            num_irred := ni', num_redundant := nr', num_binary := nb', oom := oom' }
        scratch := sc' } ext :=
  ⟨⟨hlen', hw', hok.spW.2.2.1, hnd', ⟨hll', hext' ▸ hok.spW.2.2.2.2.1.2⟩,
    hok.spW.2.2.2.2.2⟩, hok.extOk, hok.cl0, hok.fuelLe⟩

/-- Step-13 Option-A lift for `full_rebuild_watches_nosort_fid` against
`step13RebuildWatchesM6Spec`. -/
theorem full_rebuild_watches_nosort_fid_step13_wp (Γ : Env)
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hProp : ∀ a m Q X, step13BcpM6Spec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X) :
    ∀ a m Q X, step13RebuildWatchesM6Spec a m Q X →
      Func.wp Γ FullFidelityStep10.fidStep10RebuildWatchesNosortFn.body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m0 Q X ⟨c, F0, ext, s, R, rfl, hcfg, hext, hdn, hm0, hQ⟩
  obtain ⟨F_cur, hdw⟩ := hdn.exists_witness
  let s0 : FullState := { s with core := { s.core with dense_mode := 0#64 } }
  have hsp0 : FullSparseInvW c F0 F_cur s0 := hdw.toSparse_clear_dense
  have hok0 : S13RebuildOk c F0 F_cur s s0 ext :=
    ⟨hsp0, hext, hdw.2.2.2.2.2.1, Nat.le_refl _⟩
  unfold Func.wp FullFidelityStep10.fidStep10RebuildWatchesNosortFn; dsimp only
  unfold FullFidelityStep10.full_rebuild_watches_nosort_fid_body
  refine wp_m6Hdr_focus_frame hm0 fun _ => ?_
  c0_hsteps_nogrp
  refine wp_join_group (ts := [])
    (fun () m1 => ∃ (ext1 : List (BitVec 64)) (st : FullState),
      S13RebuildOk c F0 F_cur s st ext1 ∧ (FullM6HdrMem c ext1 st ⋆ R) m1)
    (fun _ () m1 ⟨ext1, st, hok, hm1⟩ => by
      refine wp_m6Hdr_focus_frame hm1 fun _ => ?_
      c0_hsteps_nogrp
      exact hQ 1#64 ext1 _ _ (FullM6HdrInvW.mk_inv hcfg hok.extOk hok.spW).toInv
        hok.cl0 hok.fuelLe (Or.inr (Or.inl rfl)) (fun h => by cases h)
        (fullM6HdrMem_unfocus_full (by assumption)))
    ?_
  intro Jbrk hJbrk
  c0_hsteps_nogrp
  refine wp_loop_group (ts := [])
    (fun rem () ml => ∃ (extl : List (BitVec 64)) (st : FullState),
      rem = c.max_vars - st.core.trail_end ∧
      S13RebuildOk c F0 F_cur s st extl ∧ (FullM6HdrMem c extl st ⋆ R) ml) ?_ ?_
  · rintro L rem ⟨⟩ ml ih ⟨extl, st, rfl, hok_st, hm_st⟩
    dsimp only [Blocks.get]
    refine wp_jnz_of (fun _ => ?_) (fun hc => by cases hc)
    refine wp_m6Hdr_focus_frame hm_st fun hmf => ?_
    c0_hsteps_nogrp; c0_call hSweep
    refine ⟨c, F0, F_cur, st, m6ExtMem (m6ExtAddr c.hdr) extl ⋆ R, rfl, hok_st.spW.1,
      hok_st.spW.2.1, hok_st.spW.2.2.2.1, hok_st.spW.2.2.2.2.2,
      fun hpos => by have := hok_st.cl0; omega, hmf,
      fun sr vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' arena' alen'
        wlen' wu' fred' ni' nr' nb' oom' sc' mA hlenA hsr_dom hextA _ hllA hwA hndA
        _ _ hsr1 hsr2 _ hmA => ?_⟩
    let sA : FullState :=
      { st with
        core :=
          { st.core with
            vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
            trail_pos := tp', trail_end := te', unassigned := unass', unflushed := unfl',
            wvec := wvec', wstk := wstk', arena := arena', arena_len := alen', wlen := wlen',
            wusable := wu', arena_garbage := 0#64, first_reducible := fred', num_irred := ni',
            num_redundant := nr', num_binary := nb', oom := oom' }
        scratch := sc' }
    have hokA := s13RebuildOk_sweep hok_st hlenA hwA hndA hllA hextA
    c0_hsteps_nogrp
    · exact hQ 20#64 extl sA _ (FullM6HdrInvW.mk_inv hcfg hokA.extOk hokA.spW).toInv
        hokA.cl0 hokA.fuelLe (Or.inr (Or.inr rfl)) (fun _ => (hsr2 (by c0_bound)).2)
        (fullM6HdrMem_unfocus_full hmA)
    · exact hQ 0#64 extl sA _ (FullM6HdrInvW.mk_inv hcfg hokA.extOk hokA.spW).toInv
        hokA.cl0 hokA.fuelLe (Or.inl rfl) (fun h => by cases h)
        (fullM6HdrMem_unfocus_full hmA)
    · refine wp_join_group (ts := [])
        (fun () mA0 => ∃ stA0 : FullState,
          S13RebuildOk c F0 F_cur s stA0 extl ∧ (sr = 0#64 → stA0.core.unflushed = 0#64) ∧
          (sr = 1#64 → st.core.trail_end < stA0.core.trail_end) ∧
          (FullM6HdrMem c extl stA0 ⋆ R) mA0) ?_ ?_
      · rintro _ ⟨⟩ mA0 ⟨stA0, hokA0, _hsr0_u, hst_lt_A0, hmA0⟩
        rw [Blocks.get_here]
        c0_hsteps_nogrp; c0_call hProp
        refine ⟨c, F0, F_cur, extl, stA0, R, rfl, hcfg, hokA0.extOk, hokA0.spW.1, hokA0.spW.2.1,
          hokA0.spW.2.2.2.2.2, hmA0, ?_⟩
        intro pr extB valsB flagsB lvlB rsnsB trlB tpB teB propB unassB unflB wvecB arenaB
          wstkB wlenB wuB fuelB ctypeB crefB c0B c1B oomB scB mB sB
          hextB _ hlenB hwB htrB hpermB hscpB _ _ _ _ hfuelB hdomB _ hpr1 _ _ hmB
        have hspWB := s6p0_sparseInv_of_bcp hokA0.spW hlenB hwB hpermB hscpB
        have hokB : S13RebuildOk c F0 F_cur s sB extB :=
          ⟨hspWB, hextB, hokA0.cl0, Nat.le_trans hfuelB hokA0.fuelLe⟩
        c0_hsteps_nogrp
        · exact hQ 20#64 extB sB mB (FullM6HdrInvW.mk_inv hcfg hokB.extOk hokB.spW).toInv
            hokB.cl0 hokB.fuelLe (Or.inr (Or.inr rfl))
            (fun _ => s6p0_level0_unsat hwB hokB.cl0 (hpr1 (by c0_bound)).2.2) hmB
        · c0_hsteps
          exact hJbrk () mB ⟨extB, sB, hokB, hmB⟩
        · have hsr1_eq : sr = 1#64 := by
            have hne0 : sr ≠ 0#64 := by c0_bound
            rcases hsr_dom with rfl | rfl | rfl | rfl <;>
              first | exact absurd rfl hne0 | rfl | contradiction
          have hte_bd : sB.core.trail_end ≤ c.max_vars :=
            Nat.le_trans hlenB.core_ok.trail_end_le hlenB.core_ok.cur_vars_le
          have hte_lt : st.core.trail_end < sB.core.trail_end :=
            Nat.lt_of_lt_of_le (hst_lt_A0 hsr1_eq)
              (by change stA0.core.trail_end ≤ teB; exact htrB.1)
          exact ih (c.max_vars - sB.core.trail_end) () mB (by omega)
            ⟨extB, sB, rfl, hokB, hmB⟩
      · intro _ hJ_unfl
        c0_hsteps_nogrp
        · have hsr0 : sr = 0#64 := by c0_bound
          let sA0 : FullState := { sA with core := { sA.core with unflushed := 0#64 } }
          have hlenA0 : sA0.LengthsOk c :=
            ⟨{ hlenA.core_ok with vals_len := hlenA.core_ok.vals_len }, hlenA.scratch_ok⟩
          have hwA0 : FullWitnessInv c F0 F_cur sA0.core :=
            fullWitnessInv_with_unflushed hwA 0#64
          have hokA0 : S13RebuildOk c F0 F_cur s sA0 extl :=
            ⟨⟨hlenA0, hwA0, hokA.spW.2.2.1, hokA.spW.2.2.2.1, hokA.spW.2.2.2.2.1,
              hokA.spW.2.2.2.2.2⟩, hokA.extOk, hokA.cl0, hokA.fuelLe⟩
          exact hJ_unfl () _ ⟨sA0, hokA0, fun _ => rfl,
            (fun h1 : sr = 1#64 => by rw [hsr0] at h1; cases h1),
            fullM6HdrMem_unfocus_full (by assumption)⟩
        · have hne0 : sr ≠ 0#64 := by c0_bound
          exact hJ_unfl () _ ⟨sA, hokA, fun h => absurd h hne0,
            fun h1 => (hsr1 h1).2, fullM6HdrMem_unfocus_full hmA⟩
  · intro L hL; c0_hsteps_nogrp
    exact hL (c.max_vars - s0.core.trail_end) () _
      ⟨ext, s0, rfl, hok0, fullM6HdrMem_unfocus_full (by assumption)⟩

/-- Step-13 Option-A lift for `full_rebuild_watches` (`FullFidelityStep9.full_rebuild_watches_body`)
against `step13RebuildWatchesM6Spec`. -/
theorem full_rebuild_watches_step13_wp (Γ : Env)
    (hNosort : ∀ a m Q X, step13RebuildWatchesM6Spec a m Q X →
      Γ "full_rebuild_watches_nosort_fid" [i64] [i64] a m Q X)
    (hSortBin : ∀ a m Q X, step13SortBinWatchesSpec a m Q X →
      Γ "full_sort_bin_watches_fid" [i64] [] a m Q X) :
    ∀ a m Q X, step13RebuildWatchesM6Spec a m Q X →
      Func.wp Γ FullFidelityStep9.fidStep9RebuildWatchesFn.body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m0 Q X ⟨c, F0, ext, s, R, rfl, hcfg, hext, hdn, hm0, hQ⟩
  unfold Func.wp FullFidelityStep9.fidStep9RebuildWatchesFn; dsimp only
  unfold FullFidelityStep9.full_rebuild_watches_body
  c0_hsteps; c0_call hNosort
  refine ⟨c, F0, ext, s, R, rfl, hcfg, hext, hdn, hm0,
    fun rr extr sr mr hinvr hclr hfur hdomr hunsr hmr => ?_⟩
  c0_hsteps
  · obtain ⟨F_cur, hspW⟩ := hinvr.sparse.exists_witness
    have hrr1 : rr = 1#64 := by c0_bound
    subst hrr1
    refine wp_m6Hdr_focus_frame hmr fun hmrf => ?_
    c0_hsteps; c0_call hSortBin
    refine ⟨c, F0, F_cur, sr, m6ExtMem (m6ExtAddr c.hdr) extr ⋆ R, rfl, hspW, hmrf,
      fun wstk' m2 _ hsp' _ hm2 => ?_⟩
    c0_hsteps
    exact hQ 1#64 extr _ m2 (FullM6HdrInvW.mk_inv hinvr.cfgOk hinvr.extOk hsp').toInv hclr hfur
      (Or.inr (Or.inl rfl)) (fun h => by cases h) (fullM6HdrMem_unfocus_full hm2)
  · exact hQ rr extr sr mr hinvr hclr hfur hdomr hunsr hmr

/-! ## 5. `full_parse_body`, `full_walk`, & `full_simplify_m6` -/

/-- Step-13 Option-A lift for `full_parse_body` (`FullM6Orch.full_parse_body_body`) against
`step13ParseBodyM6Spec`. -/
theorem full_parse_body_step13_wp (Γ : Env)
    (hSub : ∀ a m Q X, step13ParseBodyM6Spec a m Q X →
      Γ "full_parse_body_m6" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, step13ParseBodyM6Spec a m Q X →
      Func.wp Γ FullM6Orch.full_parse_body_body a m Q X := by
  intro ⟨h, cend, ⟨⟩⟩ m Q X hs
  unfold Func.wp FullM6Orch.full_parse_body_body
  refine wp_call_of_spec _ _ (hSub _ _ _ _ hs)

/-- Step-13 Option-A lift for `full_walk` / `full_walk_warmup_m7`
(`FullM7Walk.full_walk_warmup_m7_body`) against `step13WarmupM6Spec`. -/
theorem full_walk_step13_wp (Γ : Env)
    (hWarmup : ∀ a m Q X, step13WarmupM6Spec a m Q X → Γ "full_warmup_m7" [i64] [] a m Q X)
    (hWalk : ∀ a m Q X, step13WalkM7Spec a m Q X → Γ "full_walk_m7" [i64] [] a m Q X) :
    ∀ a m Q X, step13WarmupM6Spec a m Q X →
      Func.wp Γ FullM7Walk.full_walk_warmup_m7_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, ext, s, R, rfl, hinv, hm, hQ⟩
  dsimp only [Func.wp, FullM7Walk.full_walk_warmup_m7_body]
  refine wp_call_of_spec _ _ (hWarmup _ _ _ _ ⟨c, F0, ext, s, R, rfl, hinv, hm, ?_⟩)
  intro ext1 s1 m1 hinv1 hperm1 hcv1 hcl1 hfu1 hprob1 hpres1 hm1
  refine wp_m6Hdr_focus_frame hm1 fun hm1f => ?_
  refine wp_call_of_spec _ _ (hWalk _ _ _ _ ⟨c, F0, s1, _, rfl, hinv1.sparse, hm1f, ?_⟩)
  intro s2 m2 hsp2 hperm2 hcv2 hcl2 hfu2 hprob2 hpres2 hm2
  exact hQ ext1 s2 _ (FullM6HdrInv.mk_inv hinv1.cfgOk hinv1.extOk hsp2)
    (s6p0_arenaPermEq_trans hperm1 hperm2) (hcv2.trans hcv1) (hcl2.trans hcl1)
    (Nat.le_trans hfu2 hfu1) (fun h0 => (hprob2).trans (hprob1 h0))
    ⟨hpres2.1.trans hpres1.1, hpres2.2.trans hpres1.2⟩ (fullM6HdrMem_unfocus_full hm2)

/-- Step-13 Option-A lift for `full_simplify_m6` (`FullM6Orch.full_simplify_m6_body`) against
`fullM6SimplifySpec`. -/
theorem full_simplify_m6_step13_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hProbe : ∀ a m Q X, m6ProbeSpec a m Q X → Γ "full_probe_m6" [i64, .bool] [i64] a m Q X)
    (hElim : ∀ a m Q X, step13EliminateM6Spec a m Q X →
      Γ "full_eliminate_m6" [i64, .bool] [i64] a m Q X)
    (hCompNeed : ∀ a m Q X, FullM6CompactFlush.fullCompactNeededM6Spec a m Q X →
      Γ "full_compact_needed" [i64] [.bool] a m Q X)
    (hCompact : ∀ a m Q X, step13CompactM6Spec a m Q X → Γ "full_compact" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullM6SimplifySpec a m Q X → Func.wp Γ full_simplify_m6_body a m Q X := by
  rintro ⟨h, dp, de, ⟨⟩⟩ m Q X hs
  rcases fullM6SimplifySpec_elim hs with ⟨c, F0, ext, s, R, rfl, hinv, hm, hQ⟩
  unfold Func.wp full_simplify_m6_body
  refine wp_join_group (fun (_ : Tup Val []) m0 => ∃ s0, FullM6HdrInv c F0 ext s0 ∧
      s0.core.cur_level = 0 ∧ s0.core.fuel = s.core.fuel ∧ (FullM6HdrMem c ext s0 ⋆ R) m0) ?_ ?_
  · rintro _ _ m0 ⟨s0, hinv0, hcl0, hfu0, hm0⟩
    rw [Blocks.get_here]
    c0_hsteps_nogrp
    refine wp_join_group (fun (_ : Tup Val []) m1 => ∃ ext1 s1, FullM6HdrInv c F0 ext1 s1 ∧
        s1.core.cur_level = 0 ∧ s1.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        (FullM6HdrMem c ext1 s1 ⋆ R) m1) ?_ ?_
    · rintro _ _ m1 ⟨ext1, s1, hinv1, hcl1, hfu1, hm1⟩
      rw [Blocks.get_here]
      refine wp_m6Hdr_focus_frame hm1 fun _ => ?_
      c0_hsteps_nogrp
      · c0_hsteps
        exact hQ 0#64 c ext1 s1 _ (FullCfgCompat.refl c) hinv1.sparse.lengths hinv1.cfgOk
          hinv1.extOk (Or.inl rfl) hfu1 (fun h => by cases h)
          (fun h1 => absurd h1 (by decide)) (fullM6HdrMem_unfocus_full (by assumption))
      · c0_hsteps
        exact hQ 0#64 c ext1 s1 _ (FullCfgCompat.refl c) hinv1.sparse.lengths hinv1.cfgOk
          hinv1.extOk (Or.inl rfl) hfu1 (fun h => by cases h)
          (fun h1 => absurd h1 (by decide)) (fullM6HdrMem_unfocus_full (by assumption))
      · refine wp_join_group (fun (_ : Tup Val []) m2 => ∃ ext2 s2, FullM6HdrInv c F0 ext2 s2 ∧
            s2.core.cur_level = 0 ∧ s2.core.fuel.toNat ≤ s.core.fuel.toNat ∧
            (FullM6HdrMem c ext2 s2 ⋆ R) m2) ?_ ?_
        · rintro _ _ m2 ⟨ext2, s2, hinv2, hcl2, hfu2, hm2⟩
          rw [Blocks.get_here]
          refine wp_m6Hdr_focus_frame hm2 fun hm2f => ?_
          c0_hsteps_nogrp
          · c0_hsteps; exact hQ 20#64 c ext2 s2 _ (FullCfgCompat.refl c) hinv2.sparse.lengths
              hinv2.cfgOk hinv2.extOk (Or.inr (Or.inr rfl)) hfu2
              (fun _ => hinv2.sparse.1.witness.choose_spec.ext_sound.2
                (hinv2.sparse.1.witness.choose_spec.inconsistent_sound (by c0_bound)))
              (fun h => by cases h) (fullM6HdrMem_unfocus_full (by assumption))
          · c0_hsteps; exact hQ 0#64 c ext2 s2 _ (FullCfgCompat.refl c) hinv2.sparse.lengths
              hinv2.cfgOk hinv2.extOk (Or.inl rfl) hfu2 (fun h => by cases h)
              (fun h1 => absurd h1 (by decide)) (fullM6HdrMem_unfocus_full (by assumption))
          · refine wp_join_group (fun (_ : Tup Val []) m3 => ∃ c3 ext3 s3, FullCfgCompat c c3 ∧
                FullM6HdrInv c3 F0 ext3 s3 ∧ s3.core.cur_level = 0 ∧
                s3.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c3 ext3 s3 ⋆ R) m3) ?_ ?_
            · rintro _ _ m3 ⟨c3, ext3, s3, hc3, hinv3, hcl3, hfu3, hm3⟩
              rw [Blocks.get_here]; refine wp_m6Hdr_focus_frame hm3 fun _ => ?_
              rw [← hc3.hdr]; c0_hsteps_nogrp
              · c0_hsteps; exact hQ 20#64 c3 ext3 s3 _ hc3 hinv3.sparse.lengths hinv3.cfgOk
                  hinv3.extOk (Or.inr (Or.inr rfl)) hfu3
                  (fun _ => hinv3.sparse.1.witness.choose_spec.ext_sound.2
                    (hinv3.sparse.1.witness.choose_spec.inconsistent_sound (by c0_bound)))
                  (fun h => by cases h) (fullM6HdrMem_unfocus_full (by assumption))
              · c0_hsteps; exact hQ 0#64 c3 ext3 s3 _ hc3 hinv3.sparse.lengths hinv3.cfgOk
                  hinv3.extOk (Or.inl rfl) hfu3 (fun h => by cases h)
                  (fun h1 => absurd h1 (by decide)) (fullM6HdrMem_unfocus_full (by assumption))
              · c0_hsteps; exact hQ 1#64 c3 ext3 s3 _ hc3 hinv3.sparse.lengths hinv3.cfgOk
                  hinv3.extOk (Or.inr (Or.inl rfl)) hfu3 (fun h => by cases h)
                  (fun _ => ⟨hinv3, hcl3⟩) (fullM6HdrMem_unfocus_full (by assumption))
            · intro J3 hJ3; c0_hsteps_nogrp; c0_call hCompNeed
              refine ⟨c, s2, m6ExtMem (m6ExtAddr c.hdr) ext2 ⋆ R, rfl, hinv2.sparse.lengths,
                by have := hinv2.sparse.lengths.core_ok.cur_vars_le; have := c.hmaxv
                   unfold dimacsBound at *; omega, hm2f, fun b _ => ?_⟩
              c0_hsteps_nogrp
              · c0_call hCompact
                refine ⟨c, F0, ext2, s2, R, rfl, hinv2, fullM6HdrMem_unfocus_full hm2f,
                  fun r3 c3 ext3 s3 m3 hc3 hinv3 hr3 _ hfu3 hu3 hcl3 hm3 => ?_⟩
                c0_hsteps_nogrp
                · c0_hsteps; exact hQ 20#64 c3 ext3 s3 m3 hc3 hinv3.sparse.lengths hinv3.cfgOk
                    hinv3.extOk (Or.inr (Or.inr rfl)) (Nat.le_trans hfu3 hfu2)
                    (fun _ => hu3 (by c0_bound)) (fun h => by cases h) hm3
                · c0_hsteps; exact hQ 0#64 c3 ext3 s3 m3 hc3 hinv3.sparse.lengths hinv3.cfgOk
                    hinv3.extOk (Or.inl rfl) (Nat.le_trans hfu3 hfu2) (fun h => by cases h)
                    (fun h1 => absurd h1 (by decide)) hm3
                · c0_hsteps; exact hJ3 () m3 ⟨c3, ext3, s3, hc3, hinv3, hcl3 (by
                    rcases hr3 with rfl | rfl | rfl <;> first | rfl | contradiction),
                    Nat.le_trans hfu3 hfu2, hm3⟩
              · c0_hsteps; exact hJ3 () _ ⟨c, ext2, s2, FullCfgCompat.refl c, hinv2, hcl2, hfu2,
                  fullM6HdrMem_unfocus_full hm2f⟩
        · intro J2 hJ2; c0_hsteps_nogrp
          · c0_call hElim
            refine ⟨c, F0, ext1, s1, R, rfl, hinv1, hcl1, hm1,
              fun r2 ext2 s2 m2 hinv2 _ hcl2 hfu2 hr2 hu2 hm2 => ?_⟩
            c0_hsteps_nogrp
            · exact hQ 20#64 c ext2 s2 m2 (FullCfgCompat.refl c) hinv2.sparse.lengths hinv2.cfgOk
                hinv2.extOk (Or.inr (Or.inr rfl)) (Nat.le_trans hfu2 hfu1)
                (fun _ => hu2 (by c0_bound)) (fun h => by cases h) hm2
            · exact hJ2 () m2 ⟨ext2, s2, hinv2, hcl2, Nat.le_trans hfu2 hfu1, hm2⟩
          · exact hJ2 () m1 ⟨ext1, s1, hinv1, hcl1, hfu1, hm1⟩
    · intro J1 hJ1; c0_hsteps_nogrp
      · c0_call hProbe
        refine m6ProbeSpec_of hinv0 hcl0 hm0
          fun r1 ext1 s1 m1 hlen1 hext1 hfu1 hr1 hu1 hcl1 hm1 => ?_
        c0_hsteps_nogrp
        · have hfu1' : s1.core.fuel.toNat ≤ s.core.fuel.toNat := by rw [← hfu0]; exact hfu1
          exact hQ 20#64 c ext1 s1 m1 (FullCfgCompat.refl c) hlen1 hinv0.cfgOk hext1
            (Or.inr (Or.inr rfl)) hfu1' (fun _ => hu1 (by c0_bound)) (fun h => by cases h) hm1
        · have hr1_eq : r1 = 1#64 := by
            rcases hr1 with rfl | rfl <;> first | rfl | contradiction
          obtain ⟨hinv1, hcl1'⟩ := hcl1 hr1_eq
          exact hJ1 () m1 ⟨ext1, s1, hinv1, hcl1', by rw [← hfu0]; exact hfu1, hm1⟩
      · exact hJ1 () m0 ⟨ext, s0, hinv0, hcl0, by rw [hfu0]; exact Nat.le_refl _, hm0⟩
  · intro J0 hJ0
    refine wp_m6Hdr_focus_frame hm fun hmf => ?_
    c0_hsteps_nogrp
    · have hcv := hinv.sparse.lengths.core_ok.cur_vars_le; have hmx := c.hmaxv
      unfold dimacsBound at hmx
      obtain ⟨F_cur, hw⟩ := hinv.sparse.1.witness
      c0_call hBacktrack
      refine ⟨c, s, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hinv.sparse.lengths,
        by have := hw.cur_level_le; have := hinv.sparse.lengths.core_ok.trail_end_le; omega,
        (fun hpos => by
          have := hw.cur_level_le; have := hinv.sparse.lengths.core_ok.trail_end_le
          have := hinv.sparse.lengths.core_ok.cur_vars_le
          change 0 < c.max_vars; change (0#64 : BitVec 64).toNat < s.core.cur_level at hpos
          simp at hpos; omega),
        hw.trail_lits_lt, hmf, ?_⟩
      intro vals' lvl' rsns' trl' tp' te' prop' cl0' unass' sc' m0 s0 hlen0 _ _ hcl0 hpres0 _ _ _
        hwf0 _ hm0
      have hw0 := hwf0 F0 F_cur hw (Nat.zero_le _)
      have hsp0 : FullSparseInv c F0 s0 :=
        ⟨⟨hlen0, ⟨F_cur, hw0⟩⟩, hinv.sparse.2.1, hinv.sparse.2.2.1,
          FullExtScratchOk.of_pres hinv.sparse.2.2.2.1 hpres0.1 (fun _ hr => hr),
          hinv.sparse.2.2.2.2⟩
      exact hJ0 () _ ⟨s0, FullM6HdrInv.mk_inv hinv.cfgOk hinv.extOk hsp0,
        by dsimp only [s0]; rw [hcl0]; simp, rfl, fullM6HdrMem_unfocus hm0⟩
    · have hcl0 : s.core.cur_level = 0 := by
        have := hinv.sparse.1.witness.choose_spec.cur_level_le
        have := hinv.sparse.lengths.core_ok.trail_end_le
        have := hinv.sparse.lengths.core_ok.cur_vars_le; have := c.hmaxv; unfold dimacsBound at *
        have hnot : ¬ 0 < s.core.cur_level % 2 ^ 64 := by assumption
        rw [Nat.mod_eq_of_lt (by omega)] at hnot; omega
      exact hJ0 () m ⟨s, hinv, hcl0, rfl, hm⟩

/-! ## 6. `full_lucky_late_m7` (`FullM7Search.full_lucky_late_m7_body`) -/

private theorem s6p0_lucky_bt0 {Γ : Env}
    (hBt : ∀ a m Q X, fullBacktrackSpec a m Q X → Γ "full_backtrack" [i64, i64] [] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {Q : Post [i64]} {X : XPost} {h : BitVec 64}
    {k : Expr Val Cont [i64]}
    (hh : h = c.hdr) (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hK : ∀ s' m', s'.LengthsOk c → s'.core.fuel = s.core.fuel →
      FullM6HdrInv c F0 ext s' → s'.core.cur_level = 0 →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X k m') :
    wp Γ Q X (.call (as := [i64, i64]) (bs := []) "full_backtrack"
      (Arg.var h, Arg.imm 0#64, ()) (fun _ => k)) m := by
  subst hh
  obtain ⟨F_cur, hw⟩ := hinv.sparse.1.witness
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hcl_lt : s.core.cur_level < 2 ^ 64 := by
    have := hw.cur_level_le; have := hinv.sparse.lengths.core_ok.trail_end_le
    have := hinv.sparse.lengths.core_ok.cur_vars_le; omega
  have h0_toNat : (Arg.imm (t := i64) 0#64).val.toNat = 0 := rfl
  refine wp_m6Hdr_focus_frame hm fun hmf => ?_
  refine wp_call_of_spec _ _ ?_
  refine hBt _ _ _ X ⟨c, s, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hinv.sparse.lengths,
    hcl_lt, (fun hpos => by
      have := hw.cur_level_le; have := hinv.sparse.lengths.core_ok.trail_end_le
      have := hinv.sparse.lengths.core_ok.cur_vars_le; rw [h0_toNat] at hpos; omega),
    hw.trail_lits_lt, hmf, ?_⟩
  intro vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m' s' hlen' _ _ hcl' hps _ _ _ hwt _ hm'
  have hsp' : FullSparseInv c F0 s' :=
    fullSparseInv_of_fullBacktrack hinv.sparse hlen' (hwt F0 F_cur hw (Nat.zero_le _))
      rfl rfl rfl rfl rfl hps.1.1 hps.1.2
  have hcl0 : s'.core.cur_level = 0 := by
    dsimp only [s']; simpa [h0_toNat] using hcl'
  exact hK s' _ hlen' rfl (FullM6HdrInv.mk_inv hinv.cfgOk hinv.extOk hsp') hcl0
    (fullM6HdrMem_unfocus hm')

private theorem s6p0_bv64_shl1 {x : BitVec 64} (hx : 2 * x.toNat < 2 ^ 64) :
    (x <<< 1#64).toNat = 2 * x.toNat :=
  Full.FullLuckyTactics.bv64_shl1_toNat (by omega)

private theorem s6p0_bv32_trunc_shl1 {x : BitVec 64} (hx : x.toNat < 2 ^ 28) :
    ((x <<< 1#64).setWidth 32).toNat = 2 * x.toNat :=
  Full.FullLuckyTactics.bv32_shl1_trunc32_toNat (by omega)

private theorem s6p0_bv32_trunc_shl1_or1 {x : BitVec 64} (hx : x.toNat < 2 ^ 28) :
    (((x <<< 1#64).setWidth 32) ||| 1#32).toNat = 2 * x.toNat + 1 :=
  Full.FullLuckyTactics.bv32_shl1_or1_trunc32_toNat (by omega)

/-- Step-13 Option-A lift for `full_lucky_late_m7` (`FullM7Search.full_lucky_late_m7_body`)
against `step13LuckyLateM6Spec`. -/
theorem full_lucky_late_m7_step13_wp (Γ : Env)
    (hPolar : EnvSpec Γ "full_lucky_polar_m7" fullLuckyPolarSpec)
    (hScan : EnvSpec Γ "full_lucky_scan" step13LuckyScanM6Spec)
    (hAssign : EnvSpec Γ "full_assign" fullAssignSpec)
    (hBt : EnvSpec Γ "full_backtrack" fullBacktrackSpec)
    (hProp : EnvSpec Γ "full_propagate" step13BcpM6Spec) :
    ∀ a m Q X, step13LuckyLateM6Spec a m Q X → Func.wp Γ full_lucky_late_m7_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, ext, s, R, rfl, hinv, hm, hQ⟩
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  unfold Func.wp full_lucky_late_m7_body
  refine wp_m6Hdr_focus_frame hm fun hmf => ?_; s6p0_steps; s6p0_jnz hinc
  · have hunsat : F0.Unsat := hinv.sparse.inconsistent_unsat (by simpa using hinc)
    s6p0_steps
    let s' : FullState := { s with core := { s.core with probing := 0#64 } }
    have hsp' := fullSparseInv_with_probing hinv.sparse 0#64
    exact hQ 20#64 ext s' _ hsp'.lengths hinv.extOk (Or.inr (Or.inr (Or.inr rfl))) (Nat.le_refl _)
      rfl (fun _ => hunsat) (fun h => by rcases h with h | h <;> cases h) (fun h => by cases h)
      (fullM6HdrMem_unfocus_full (by assumption))
  · s6p0_steps
    refine wp_join_group (ts := []) (fun _ m1 => ∃ s1 : FullState,
        FullM6HdrInv c F0 ext s1 ∧ s1.core.cur_level = 0 ∧
        s1.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c ext s1 ⋆ R) m1) ?_ ?_
    · rintro _ ⟨⟩ m1 ⟨s1, hinv1, hcl1_0, hfl1, hm1⟩
      rw [Blocks.get_here]; refine wp_m6Hdr_focus_frame hm1 fun _ => ?_; s6p0_steps
      refine wp_join_group (ts := []) (fun _ m2 => ∃ (ext2 : List (BitVec 64)) (s2 : FullState),
          FullM6HdrInv c F0 ext2 s2 ∧ s2.core.cur_level = 0 ∧
          s2.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c ext2 s2 ⋆ R) m2) ?_ ?_
      · rintro _ ⟨⟩ m2 ⟨ext2, s2, hinv2, hcl2_0, hfl2, hm2⟩
        rw [Blocks.get_here]; refine wp_m6Hdr_focus_frame hm2 fun _ => ?_; s6p0_steps
        let s3 : FullState := { s2 with core := { s2.core with probing := 1#64 } }
        have hinv3 := FullM6HdrInv.mk_inv hinv2.cfgOk hinv2.extOk
          (fullSparseInv_with_probing hinv2.sparse 1#64)
        c0_call hPolar
        refine ⟨c, F0, s3, m6ExtMem (m6ExtAddr c.hdr) ext2 ⋆ R, rfl, hinv3.sparse.1,
          by assumption, ?_⟩
        intro pol hpol; s6p0_steps; s6p0_jnz hpol0
        · s6p0_steps; refine wp_loop_inv (ts := [i64]) (fun (idx, _) ml => ∃ extl st,
              idx.toNat ≤ s3.core.cur_vars ∧ st.core.cur_vars = s3.core.cur_vars ∧
              FullM6HdrInv c F0 extl st ∧ st.core.fuel.toNat ≤ s.core.fuel.toNat ∧
              (FullM6HdrMem c extl st ⋆ R) ml)
              (fun (idx, _) _ => s3.core.cur_vars - idx.toNat) ?_ ?_
          · intro _ hJloop; s6p0_steps; exact hJloop (0#64, ()) _
              ⟨ext2, s3, Nat.zero_le _, rfl, hinv3, hfl2, fullM6HdrMem_unfocus_full (by assumption)⟩
          · rintro _ ⟨idx, ⟨⟩⟩ ml ⟨extl, st, hidx_le, hcv_eq, hinvl, hfl, hml⟩ hJloop
            rw [Blocks.get_here]
            have hcl_ok := hinvl.sparse.lengths.core_ok; have hcv_st_le := hcl_ok.cur_vars_le
            have hmaxv_st : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
            refine wp_m6Hdr_focus_frame hml fun _ => ?_; s6p0_steps; s6p0_jnz hidx_lt_cv
            · have hidx_lt : idx.toNat < st.core.cur_vars := by
                have hlt : idx.toNat < st.core.cur_vars % 2 ^ 64 := by
                  simpa [BitVec.ult] using hidx_lt_cv
                rw [Nat.mod_eq_of_lt (by omega)] at hlt; exact hlt
              have hidx1_nat : (idx + 1#64).toNat = idx.toNat + 1 := s6p0_bv64_add1 (by omega)
              have hidx_fl : idx.toNat < st.core.flags.length := by rw [hcl_ok.flags_len]; omega
              have h2v : (idx <<< 1#64).toNat = 2 * idx.toNat := s6p0_bv64_shl1 (by omega)
              have hidx2_vl : (idx <<< 1#64).toNat < st.core.vals.length := by
                rw [h2v, hcl_ok.vals_len]; omega
              s6p0_steps
              refine wp_join_group (ts := []) (fun _ mn =>
                ∃ (ext' : List (BitVec 64)) (st' : FullState),
                  st'.core.cur_vars = s3.core.cur_vars ∧ FullM6HdrInv c F0 ext' st' ∧
                  st'.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c ext' st' ⋆ R) mn) ?_ ?_
              · rintro _ ⟨⟩ mn ⟨ext', st', hcv', hinv', hfl', hmn⟩
                rw [Blocks.get_here]; s6p0_steps
                exact hJloop (idx + 1#64, ()) mn (by dsimp only; rw [hidx1_nat]; omega)
                  ⟨ext', st', by rw [hidx1_nat]; omega, hcv', hinv', hfl', hmn⟩
              · intro _ hJnext
                s6p0_steps; s6p0_jnz hact
                · s6p0_steps; s6p0_jnz hval0_b
                  · have hval0 : st.core.vals[2 * idx.toNat]?.getD 0#8 = 0#8 := by
                      rw [← h2v, List.getElem?_eq_getElem hidx2_vl, Option.getD_some]
                      exact s6p0_sext8_32_eq0 _ (by simpa using hval0_b)
                    s6p0_steps; s6p0_jnz hfuel0
                    · s6p0_steps
                      refine s6p0_lucky_bt0 hBt rfl hinvl
                        (fullM6HdrMem_unfocus_full (by assumption))
                        fun s_bt mb _ hfl_b hinv_b hcl0_b hmb => ?_
                      refine wp_m6Hdr_focus_frame hmb fun _ => ?_
                      s6p0_steps
                      let s' : FullState := { s_bt with core := { s_bt.core with probing := 0#64 } }
                      have hsp' := fullSparseInv_with_probing hinv_b.sparse 0#64
                      have hfl' : s'.core.fuel.toNat ≤ s.core.fuel.toNat := by
                        change s_bt.core.fuel.toNat ≤ s.core.fuel.toNat; rw [hfl_b]; exact hfl
                      exact hQ 2#64 extl s' _ hsp'.lengths hinv_b.extOk
                        (Or.inr (Or.inl rfl)) hfl' rfl
                        (fun h => by cases h) (fun _ => ⟨FullM6HdrInv.mk_inv hinv_b.cfgOk
                          hinv_b.extOk hsp', hcl0_b⟩) (fun h => by cases h)
                        (fullM6HdrMem_unfocus_full (by assumption))
                    · have hfl_ne : st.core.fuel ≠ 0#64 := by simpa using hfuel0
                      have hfl_sub := s6p0_bv64_sub1 hfl_ne
                      let st1 : FullState :=
                        { st with core := { st.core with fuel := st.core.fuel - 1#64 } }
                      have hsp1 := fullSparseInv_with_fuel hinvl.sparse (st.core.fuel - 1#64)
                      have hinv1_st := FullM6HdrInv.mk_inv hinvl.cfgOk hinvl.extOk hsp1
                      have hfl1_le : st1.core.fuel.toNat ≤ s.core.fuel.toNat := by
                        change (st.core.fuel - 1#64).toNat ≤ s.core.fuel.toNat
                        rw [hfl_sub]; omega
                      s6p0_steps
                      refine wp_join_group (ts := [i32]) (fun (lit, _) mlit =>
                        (FullM6HdrMem c extl st1 ⋆ R) mlit ∧
                          (lit.toNat = 2 * idx.toNat ∨ lit.toNat = 2 * idx.toNat + 1)) ?_ ?_
                      · rintro _ ⟨lit, ⟨⟩⟩ mlit ⟨hmlit, hlit_eq⟩
                        rw [Blocks.get_here]
                        refine wp_m6Hdr_focus_frame hmlit fun _ => ?_
                        obtain ⟨_, hw_1⟩ := hsp1.1.witness
                        have hmx := c.hmaxv
                        have hcv1_le : st.core.cur_vars ≤ c.max_vars :=
                          hsp1.lengths.core_ok.cur_vars_le
                        have hcl1_le : st.core.cur_level ≤ st.core.trail_end := hw_1.cur_level_le
                        have hte1_le : st.core.trail_end ≤ st.core.cur_vars :=
                          hsp1.lengths.core_ok.trail_end_le
                        have hst1_cl : st1.core.cur_level = st.core.cur_level := rfl
                        have hst1_te : st1.core.trail_end = st.core.trail_end := rfl
                        have hst1_cv : st1.core.cur_vars = st.core.cur_vars := rfl
                        have hcl_lt64 : st.core.cur_level < 2 ^ 64 := by omega
                        have hcl1_lt64 : st.core.cur_level + 1 < 2 ^ 64 := by omega
                        have hnlvl_bv : (BitVec.ofNat 64 st1.core.cur_level + 1#64).toNat =
                            st1.core.cur_level + 1 := by
                          rw [hst1_cl, BitVec.toNat_add, BitVec.toNat_ofNat]
                          have : (1#64).toNat = 1 := rfl; omega
                        s6p0_steps; s6p0_jnz hnlvl_gt
                        · s6p0_steps; refine s6p0_lucky_bt0 hBt rfl hinv1_st hmlit
                            fun s_bt mb _ hfl_b hinv_b hcl0_b hmb => ?_
                          refine wp_m6Hdr_focus_frame hmb fun _ => ?_; s6p0_steps
                          let s' := { s_bt with core := { s_bt.core with probing := 0#64 } }
                          have hsp' := fullSparseInv_with_probing hinv_b.sparse 0#64
                          exact hQ 0#64 extl s' _ hsp'.lengths hinv_b.extOk (Or.inl rfl)
                            (by change s_bt.core.fuel.toNat ≤ s.core.fuel.toNat
                                rw [hfl_b]; exact hfl1_le) rfl (fun h => by cases h)
                            (fun _ => ⟨FullM6HdrInv.mk_inv hinv_b.cfgOk hinv_b.extOk hsp', hcl0_b⟩)
                            (fun h => by cases h) (fullM6HdrMem_unfocus_full (by assumption))
                        · have hlit_v : lit.toNat / 2 = idx.toNat := by omega
                          have hdec1 := Full.FullLuckyHelpers.lucky_decide_preserves_fullSparseInv
                            hinv1_st.sparse hidx_lt hval0 hlit_v
                            hinv1_st.sparse.lengths.core_ok.flags_len
                            hinv1_st.sparse.lengths.scratch_ok.phases_len
                            (unas' := st1.core.unassigned) (unfl' := st1.core.unflushed)
                          have hun := hdec1.2.2.2.2; have hte_lt := hdec1.2.2.1
                          have hnlvl_le := hdec1.2.2.2.1; let nlvl := st1.core.cur_level + 1
                          let ftrl' :=
                            st1.core.frame_trail.set nlvl (BitVec.ofNat 32 st1.core.trail_end)
                          let fdec' := st1.core.frame_dec.set nlvl lit
                          let s_dec :=
                            { st1 with
                              core :=
                                { st1.core with
                                  cur_level := nlvl, frame_trail := ftrl', frame_dec := fdec' } }
                          have hftrl1 := hsp1.lengths.core_ok.frame_trail_len
                          have hfdec1 := hsp1.lengths.core_ok.frame_dec_len
                          have hdec_len : s_dec.LengthsOk c := ⟨{ hsp1.lengths.core_ok with
                            frame_trail_len := by
                              dsimp [s_dec, ftrl']; rw [List.length_set]; exact hftrl1
                            frame_dec_len := by
                              dsimp [s_dec, fdec']; rw [List.length_set]; exact hfdec1 },
                            hsp1.lengths.scratch_ok⟩
                          have hte_bv : (BitVec.ofNat 64 st1.core.trail_end).setWidth 32 =
                              BitVec.ofNat 32 st1.core.trail_end := by
                            apply BitVec.eq_of_toNat_eq; rw [hst1_te, BitVec.toNat_setWidth,
                              BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), BitVec.toNat_ofNat,
                              Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
                          have hnlvl_lt_len : (BitVec.ofNat 64 st1.core.cur_level + 1#64).toNat <
                              st1.core.frame_trail.length := by
                            rw [hnlvl_bv, hst1_cl, hftrl1]; rw [hst1_cl] at hnlvl_le; omega
                          have hnlvl_lt_dlen : (BitVec.ofNat 64 st1.core.cur_level + 1#64).toNat <
                              st1.core.frame_dec.length := by
                            rw [hnlvl_bv, hst1_cl, hfdec1]; rw [hst1_cl] at hnlvl_le; omega
                          s6p0_steps
                          have hte_max : st1.core.trail_end < c.max_vars :=
                            Nat.lt_of_lt_of_le hte_lt (by rw [hst1_cv]; exact hcv1_le)
                          have hte_max' : st.core.trail_end < c.max_vars := by
                            rw [← hst1_te]; exact hte_max
                          have hng : ¬ (s_dec.core.cur_vars ≤ lit.toNat / 2 ∨
                              c.max_vars ≤ s_dec.core.trail_end ∨
                              s_dec.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8) := by
                            change ¬ (st1.core.cur_vars ≤ lit.toNat / 2 ∨
                              c.max_vars ≤ st1.core.trail_end ∨
                              st1.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8)
                            rw [hlit_v, hst1_cv, hst1_te]
                            rintro (h | h | h) <;> first | omega | exact h hun
                          c0_call hAssign
                          refine ⟨c, s_dec, m6ExtMem (m6ExtAddr c.hdr) extl ⋆ R, rfl, hdec_len,
                            by dsimp only [s_dec, nlvl]; rw [hst1_cl] at hnlvl_le; omega, ?_, ?_⟩
                          · dsimp only [s_dec, ftrl', fdec', nlvl]
                            rw [← show _ = st1.core.cur_level + 1 from hnlvl_bv, ← hte_bv]
                            assumption
                          · simp only [hng, ↓reduceIte]
                            intro flags' unas' phases' ma hfl_len hph_len hma
                            have hsp_asn0 :=
                              (Full.FullLuckyHelpers.lucky_decide_preserves_fullSparseInv
                                hsp1 hidx_lt hval0 hlit_v hfl_len hph_len
                                (unas' := unas') (unfl' := st1.core.unflushed)).1
                            let s_asn : FullState :=
                              { core :=
                                  { s_dec.core with
                                    vals := (st1.core.vals.set lit.toNat 1#8).set
                                      (lit.toNat ^^^ 1) 0xFF#8, flags := flags',
                                    lvl := st1.core.lvl.set (lit.toNat / 2)
                                      (BitVec.ofNat 32 nlvl),
                                    rsns := st1.core.rsns.set (lit.toNat / 2) 0xFFFFFFFF#32,
                                    trl := st1.core.trl.set st1.core.trail_end lit,
                                    trail_pos := st1.core.trail_pos.set (lit.toNat / 2)
                                      (BitVec.ofNat 32 st1.core.trail_end),
                                    trail_end := st1.core.trail_end + 1, unassigned := unas',
                                    unflushed := st1.core.unflushed },
                                scratch := { st1.scratch with phases := phases' } }
                            have hsp_asn : FullSparseInv c F0 s_asn := by
                              dsimp only [Full.FullLuckySpecs.FullSparseInv,
                                Full.FullLuckySpecs.FullLitMarksClear,
                                Full.FullLuckySpecs.FullMrkZero,
                                Full.FullLuckySpecs.FullArenaVarsNodup,
                                Full.FullLuckySpecs.FullExtScratchOk,
                                Full.FullLuckySpecs.FullLastLearnedWf, FullSparseInv,
                                FullLitMarksClear, FullMrkZero, FullArenaVarsNodup,
                                FullExtScratchOk, FullLastLearnedWf] at hsp_asn0 ⊢
                              simpa only [s_asn, s_dec, hlit_v] using hsp_asn0
                            obtain ⟨F_cur_a, hw_a⟩ := hsp_asn.1.witness
                            s6p0_steps; c0_call hProp
                            refine ⟨c, F0, F_cur_a, extl, s_asn, R, rfl, hinv1_st.cfgOk,
                              hinv1_st.extOk, hsp_asn.1.lengths, hw_a, hsp_asn.2.2.2.2,
                              fullM6HdrMem_unfocus_full hma, ?_⟩
                            intro pr ext_p vals'' flags'' lvl'' rsns'' trl'' tp'' te'' prop''
                              unass'' unfl'' wvec'' arena'' wstk'' wlen'' wu'' fuel'' ctype''
                              cref'' c0'' c1'' oom'' sc_p mp s_p
                              hext_p _ hlen_p hw_p _ hperm_p hscp_p _ _ _ _ hfl_p hr_or _ _ _ _ hmp
                            have hsp_p : FullSparseInv c F0 s_p :=
                              fullSparseInv_of_step13Bcp hsp_asn hlen_p hw_p hperm_p hscp_p
                            have hinv_p := FullM6HdrInv.mk_inv hinv1_st.cfgOk hext_p hsp_p
                            have hfl_p' : s_p.core.fuel.toNat ≤ s.core.fuel.toNat :=
                              Nat.le_trans hfl_p hfl1_le
                            have hcv_p : s_p.core.cur_vars = s3.core.cur_vars := hcv_eq
                            refine wp_m6Hdr_focus_frame hmp fun _ => ?_; s6p0_steps; s6p0_jnz hpr2
                            · s6p0_steps
                              refine s6p0_lucky_bt0 hBt rfl hinv_p hmp
                                fun s_bt mb _ hfl_b hinv_b hcl0_b hmb => ?_
                              refine wp_m6Hdr_focus_frame hmb fun _ => ?_; s6p0_steps
                              let s' := { s_bt with core := { s_bt.core with probing := 0#64 } }
                              have hsp' := fullSparseInv_with_probing hinv_b.sparse 0#64
                              exact hQ 2#64 ext_p s' _ hsp'.lengths hext_p (Or.inr (Or.inl rfl))
                                (by change s_bt.core.fuel.toNat ≤ s.core.fuel.toNat
                                    rw [hfl_b]; exact hfl_p') rfl (fun h => by cases h)
                                (fun _ => ⟨FullM6HdrInv.mk_inv hinv_b.cfgOk hext_p hsp', hcl0_b⟩)
                                (fun h => by cases h) (fullM6HdrMem_unfocus_full (by assumption))
                            · s6p0_steps; s6p0_jnz hpr1
                              · s6p0_steps
                                refine s6p0_lucky_bt0 hBt rfl hinv_p hmp
                                  fun s_bt mb _ hfl_b hinv_b hcl0_b hmb => ?_
                                refine wp_m6Hdr_focus_frame hmb fun _ => ?_; s6p0_steps
                                let s' := { s_bt with core := { s_bt.core with probing := 0#64 } }
                                have hsp' := fullSparseInv_with_probing hinv_b.sparse 0#64
                                exact hQ 0#64 ext_p s' _ hsp'.lengths hext_p (Or.inl rfl)
                                  (by change s_bt.core.fuel.toNat ≤ s.core.fuel.toNat
                                      rw [hfl_b]; exact hfl_p') rfl (fun h => by cases h)
                                  (fun _ => ⟨FullM6HdrInv.mk_inv hinv_b.cfgOk hext_p hsp', hcl0_b⟩)
                                  (fun h => by cases h) (fullM6HdrMem_unfocus_full (by assumption))
                              · s6p0_steps
                                exact hJnext () mp ⟨ext_p, s_p, hcv_p, hinv_p, hfl_p', hmp⟩
                      · intro _ hJlit; s6p0_steps; s6p0_jnz hcond
                        · s6p0_steps
                          exact hJlit (_, ()) _ ⟨fullM6HdrMem_unfocus_full (by assumption),
                            Or.inl (Full.FullLuckyTactics.bv32_shl1_trunc32_toNat (by omega))⟩
                        · s6p0_steps
                          exact hJlit (_, ()) _ ⟨fullM6HdrMem_unfocus_full (by assumption),
                            Or.inr (Full.FullLuckyTactics.bv32_shl1_or1_trunc32_toNat (by omega))⟩
                  · s6p0_steps; exact hJnext () ml ⟨extl, st, hcv_eq, hinvl, hfl, hml⟩
                · s6p0_steps; exact hJnext () ml ⟨extl, st, hcv_eq, hinvl, hfl, hml⟩
            · s6p0_steps
              let st' : FullState := { st with core := { st.core with probing := 0#64 } }
              have hsp' := fullSparseInv_with_probing hinvl.sparse 0#64
              exact hQ 10#64 extl st' _ hsp'.lengths hinvl.extOk (Or.inr (Or.inr (Or.inl rfl)))
                hfl rfl (fun h => absurd h (by decide))
                (fun h => by rcases h with h | h <;> cases h) (fun _ => hsp'.2.2.2.1.2)
                (fullM6HdrMem_unfocus_full (by assumption))
        · let LuckyRet : Tup Val [i64] → Mem 64 → Prop := fun (r, _) mr =>
            ∃ (extr : List (BitVec 64)) (sr : FullState), sr.LengthsOk c ∧ M6HdrExtOk extr ∧
              (r = 0#64 ∨ r = 2#64 ∨ r = 10#64 ∨ r = 20#64) ∧
              sr.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (r = 20#64 → F0.Unsat) ∧
              (r = 0#64 ∨ r = 2#64 → FullM6HdrInv c F0 extr sr ∧ sr.core.cur_level = 0) ∧
              (r = 10#64 → sr.scratch.extend_len ≤ c.extend_cap) ∧
              (FullM6HdrMem c extr sr ⋆ R) mr
          s6p0_steps; c0_call hScan
          refine ⟨c, F0, ext2, s3, R, rfl, hinv3.cfgOk, hinv3.extOk, hinv3.sparse, hcl2_0,
            fullM6HdrMem_unfocus_full (by assumption), ?_⟩
          intro r1 extr1 s1_ m1_ hext1 hlen1 hr1 hfl1 huns1 h02_1 h10_1 hm1_
          s6p0_steps
          refine wp_join_group (ts := [i64]) LuckyRet ?_ ?_
          · rintro _ ⟨rA, ⟨⟩⟩ mA ⟨extA, srA, hlenA, hextA, hrA, hflA, hunsA, h02A, h10A, hmA⟩
            rw [Blocks.get_here]; s6p0_steps
            refine wp_join_group (ts := [i64]) LuckyRet ?_ ?_
            · rintro _ ⟨rB, ⟨⟩⟩ mB ⟨extB, srB, hlenB, hextB, hrB, hflB, hunsB, h02B, h10B, hmB⟩
              rw [Blocks.get_here]; s6p0_steps
              refine wp_join_group (ts := [i64]) LuckyRet ?_ ?_
              · rintro _ ⟨rF, ⟨⟩⟩ mF ⟨extF, srF, hlenF, hextF, hrF, hflF, hunsF, h02F, h10F, hmF⟩
                rw [Blocks.get_here]
                refine wp_m6Hdr_focus_frame hmF fun _ => ?_
                s6p0_steps
                let sr' : FullState := { srF with core := { srF.core with probing := 0#64 } }
                have hlen' : sr'.LengthsOk c :=
                  ⟨{ hlenF.core_ok with vals_len := hlenF.core_ok.vals_len }, hlenF.scratch_ok⟩
                exact hQ rF extF sr' _ hlen' hextF hrF hflF rfl hunsF
                  (fun h => let ⟨hi, hcl⟩ := h02F h
                    ⟨FullM6HdrInv.mk_inv hi.cfgOk hi.extOk
                      (fullSparseInv_with_probing hi.sparse 0#64), hcl⟩)
                  h10F (fullM6HdrMem_unfocus_full (by assumption))
              · intro _ hJsF; s6p0_steps; s6p0_jnz hrb0
                · have hrb_eq : rB = 0#64 := by simpa using hrb0
                  obtain ⟨hinvB, hclB⟩ := h02B (Or.inl hrb_eq)
                  s6p0_steps; c0_call hScan
                  refine ⟨c, F0, extB, srB, R, rfl, hinvB.cfgOk, hinvB.extOk, hinvB.sparse, hclB,
                    hmB, ?_⟩
                  intro r3 ext3 sr3 m3 hext3 hlen3 hr3 hfl3 huns3 h02_3 h10_3 hm3
                  exact hJsF (r3, ()) m3 ⟨ext3, sr3, hlen3, hext3, hr3, Nat.le_trans hfl3 hflB,
                    huns3, (fun h => let ⟨hi, hc⟩ := h02_3 h
                      ⟨FullM6HdrInv.mk_inv hinvB.cfgOk hext3 hi, hc⟩), h10_3, hm3⟩
                · s6p0_steps
                  exact hJsF (rB, ()) mB
                    ⟨extB, srB, hlenB, hextB, hrB, hflB, hunsB, h02B, h10B, hmB⟩
            · intro _ hJsB; s6p0_steps; s6p0_jnz hra0
              · have hra_eq : rA = 0#64 := by simpa using hra0
                obtain ⟨hinvA, hclA⟩ := h02A (Or.inl hra_eq)
                s6p0_steps; c0_call hScan
                refine ⟨c, F0, extA, srA, R, rfl, hinvA.cfgOk, hinvA.extOk, hinvA.sparse, hclA,
                  hmA, ?_⟩
                intro r2 ext2 sr2 m2 hext2 hlen2 hr2 hfl2 huns2 h02_2 h10_2 hm2
                exact hJsB (r2, ()) m2 ⟨ext2, sr2, hlen2, hext2, hr2, Nat.le_trans hfl2 hflA,
                  huns2, (fun h => let ⟨hi, hc⟩ := h02_2 h
                    ⟨FullM6HdrInv.mk_inv hinvA.cfgOk hext2 hi, hc⟩), h10_2, hm2⟩
              · s6p0_steps
                exact hJsB (rA, ()) mA ⟨extA, srA, hlenA, hextA, hrA, hflA, hunsA, h02A, h10A, hmA⟩
          · intro _ hJsA; s6p0_steps; s6p0_jnz hr1_0
            · have hr1_eq : r1 = 0#64 := by simpa using hr1_0
              obtain ⟨hinv1_, hcl1_⟩ := h02_1 (Or.inl hr1_eq)
              have hinv1_m : FullM6HdrInv c F0 extr1 s1_ :=
                FullM6HdrInv.mk_inv hinv3.cfgOk hext1 hinv1_
              s6p0_steps; c0_call hScan
              refine ⟨c, F0, extr1, s1_, R, rfl, hinv1_m.cfgOk, hinv1_m.extOk, hinv1_m.sparse,
                hcl1_, hm1_, ?_⟩
              intro r1b ext1b sr1b m1b hext1b hlen1b hr1b hfl1b huns1b h02_1b h10_1b hm1b
              exact hJsA (r1b, ()) m1b ⟨ext1b, sr1b, hlen1b, hext1b, hr1b,
                Nat.le_trans hfl1b (Nat.le_trans hfl1 hfl2), huns1b,
                (fun h => let ⟨hi, hc⟩ := h02_1b h
                  ⟨FullM6HdrInv.mk_inv hinv1_m.cfgOk hext1b hi, hc⟩), h10_1b, hm1b⟩
            · s6p0_steps
              exact hJsA (r1, ()) m1_ ⟨extr1, s1_, hlen1, hext1, hr1, Nat.le_trans hfl1 hfl2,
                huns1, (fun h => let ⟨hi, hc⟩ := h02_1 h
                  ⟨FullM6HdrInv.mk_inv hinv3.cfgOk hext1 hi, hc⟩), h10_1, hm1_⟩
      · intro _ hJ2
        s6p0_steps; s6p0_jnz hpt_lt
        · obtain ⟨F_cur1, hw1⟩ := hinv1.sparse.1.witness
          c0_call hProp
          refine ⟨c, F0, F_cur1, ext, s1, R, rfl, hinv1.cfgOk, hinv1.extOk,
            hinv1.sparse.lengths, hw1, hinv1.sparse.2.2.2.2, hm1, ?_⟩
          intro pr ext_p vals'' flags'' lvl'' rsns'' trl'' tp'' te'' prop'' unass'' unfl''
            wvec'' arena'' wstk'' wlen'' wu'' fuel'' ctype'' cref'' c0'' c1'' oom'' sc_p mp
            s_p hext_p _ hlen_p hw_p _ hperm_p hscp_p _ _ _ _ hfl_p hr_or _ hpr1 _ _ hmp
          have hsp_p := fullSparseInv_of_step13Bcp hinv1.sparse hlen_p hw_p hperm_p hscp_p
          have hinv_p := FullM6HdrInv.mk_inv hinv1.cfgOk hext_p hsp_p
          have hfl_p' : s_p.core.fuel.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfl_p hfl1
          refine wp_m6Hdr_focus_frame hmp fun _ => ?_
          s6p0_steps; s6p0_jnz hpr1_t
          · have hpr1_eq : pr = 1#64 := by simpa using hpr1_t
            have hunsat : F0.Unsat := s6p0_level0_unsat hw_p hcl1_0 (hpr1 hpr1_eq).2.2
            s6p0_steps
            let s' : FullState :=
              { s_p with core := { s_p.core with inconsistent := 1#64, probing := 0#64 } }
            have hlen' : s'.LengthsOk c :=
              ⟨{ hlen_p.core_ok with vals_len := hlen_p.core_ok.vals_len }, hlen_p.scratch_ok⟩
            exact hQ 20#64 ext_p s' _ hlen' hext_p (Or.inr (Or.inr (Or.inr rfl))) hfl_p' rfl
              (fun _ => hunsat) (fun h => by rcases h with h | h <;> cases h)
              (fun h => by cases h) (fullM6HdrMem_unfocus_full (by assumption))
          · s6p0_steps; s6p0_jnz hpr2_t
            · s6p0_steps
              let s' : FullState := { s_p with core := { s_p.core with probing := 0#64 } }
              have hsp' := fullSparseInv_with_probing hsp_p 0#64
              exact hQ 2#64 ext_p s' _ hsp'.lengths hext_p (Or.inr (Or.inl rfl)) hfl_p' rfl
                (fun h => by cases h)
                (fun _ => ⟨FullM6HdrInv.mk_inv hinv1.cfgOk hext_p hsp', hcl1_0⟩)
                (fun h => by cases h) (fullM6HdrMem_unfocus_full (by assumption))
            · s6p0_steps
              exact hJ2 () mp ⟨ext_p, s_p, hinv_p, hcl1_0, hfl_p', hmp⟩
        · s6p0_steps; exact hJ2 () m1 ⟨ext, s1, hinv1, hcl1_0, hfl1, hm1⟩
    · intro _ hJ1
      s6p0_steps; s6p0_jnz hcl_gt
      · refine s6p0_lucky_bt0 hBt rfl hinv hm fun s1 m1 _ hfl1 hinv1 hcl1 hm1 => ?_
        exact hJ1 () m1 ⟨s1, hinv1, hcl1, by rw [hfl1]; exact Nat.le_refl _, hm1⟩
      · have hcl0 : s.core.cur_level = 0 := by
          have := hinv.sparse.1.witness.choose_spec.cur_level_le
          have := hinv.sparse.lengths.core_ok.trail_end_le
          have := hinv.sparse.lengths.core_ok.cur_vars_le
          have hnot : ¬ 0 < s.core.cur_level % 2 ^ 64 := by simpa [BitVec.ult] using hcl_gt
          rw [Nat.mod_eq_of_lt (by omega)] at hnot; omega
        exact hJ1 () m ⟨s, hinv, hcl0, Nat.le_refl _, hm⟩

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S6a

end
