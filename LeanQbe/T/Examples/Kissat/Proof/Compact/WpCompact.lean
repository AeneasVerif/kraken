/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Compact.Spec
public import LeanQbe.T.Examples.Kissat.Src.Compact
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Compact.Inv
import LeanQbe.T.Examples.Kissat.Proof.Lib.ContractLemmas
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Canonical WP Proof for Top-Level `full_compact` (`Proof.Compact.WpCompact`)

Proves `full_compact_wp` against the `FullM6HdrMem`-threaded `fullCompactSpec` (Step-13 Option-A),
focusing `FullM6HdrMem` onto `FullMem` across all `10` internal compaction helpers plus
`full_wstack_defrag` and `full_rewatch_arena`, then unfocusing back onto `FullM6HdrMem`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Compact

open Std Std.Sat
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Compact
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Compact.Spec
open Kraken.Bedrock2.Test
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics

local macro "cmp_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

private theorem compactBinsMask_elim {s s' : FullState}
    (h : AgreesExcept compactBinsMask s s') :
    s'.scratch = s.scratch ∧
    ∃ wvec' wstk' wu' nb', s'.core =
      { s.core with wvec := wvec', wstk := wstk', wusable := wu', num_binary := nb' } :=
  ⟨by rcases s with ⟨c1, sc1⟩; rcases s' with ⟨c2, sc2⟩
      dsimp only [AgreesExcept, compactBinsMask] at h
      have hsc := congrArg FullState.scratch h
      cases hsc; rfl,
   s'.core.wvec, s'.core.wstk, s'.core.wusable, s'.core.num_binary, by
     rcases s with ⟨c1, sc1⟩; rcases s' with ⟨c2, sc2⟩
     cases c1; cases c2
     dsimp only [AgreesExcept, compactBinsMask] at h
     have hc := congrArg FullState.core h
     cases hc; rfl⟩

private theorem compactArenaMask_elim {s s' : FullState}
    (h : AgreesExcept compactArenaMask s s') (hg : s'.core.arena_garbage = 0#64) :
    ∃ ar' al' fred' ni' nr' wvec' wstk' wlen' wu' nb' oom' ll' ws',
      s'.core = { s.core with
        arena := ar', arena_len := al', arena_garbage := 0#64, first_reducible := fred',
        num_irred := ni', num_redundant := nr', wvec := wvec', wstk := wstk',
        wlen := wlen', wusable := wu', num_binary := nb', oom := oom' } ∧
      s'.scratch = { s.scratch with last_learned := ll', wsort := ws' } :=
  ⟨s'.core.arena, s'.core.arena_len, s'.core.first_reducible, s'.core.num_irred,
   s'.core.num_redundant, s'.core.wvec, s'.core.wstk, s'.core.wlen, s'.core.wusable,
   s'.core.num_binary, s'.core.oom, s'.scratch.last_learned, s'.scratch.wsort,
   by rcases s with ⟨c1, sc1⟩; rcases s' with ⟨c2, sc2⟩
      cases c1; cases c2
      dsimp only [AgreesExcept, compactArenaMask] at h
      have hc := congrArg FullState.core h
      cases hc; dsimp only at hg; rw [hg],
   by rcases s with ⟨c1, sc1⟩; rcases s' with ⟨c2, sc2⟩
      cases sc1; cases sc2
      dsimp only [AgreesExcept, compactArenaMask] at h
      have hsc := congrArg FullState.scratch h
      cases hsc; rfl⟩

public section

/-- Canonical WP proof for `full_compact` against `compactSpec` (`FullM6HdrMem`-threaded). -/
theorem full_compact_wp (Γ : Env)
    (hfl : Γ.Has "full_compact_flush" compactFlushSpec)
    (hmk : Γ.Has "full_compact_mark_live" compactMarkLiveSpec)
    (hmp : Γ.Has "full_compact_assign_map" compactAssignMapSpec)
    (hre : Γ.Has "full_compact_record_ext" compactRecordExtSpec)
    (hbn : Γ.Has "full_compact_bins" compactBinsSpec)
    (hdf : Γ.Has "full_wstack_defrag" fullWstackDefragSpec)
    (har : Γ.Has "full_compact_arena" compactArenaSpec)
    (hvr : Γ.Has "full_compact_vars" compactVarsSpec)
    (hvm : Γ.Has "full_compact_vmtf" compactHeurSpec)
    (hhp : Γ.Has "full_compact_heap" compactHeurSpec)
    (hrw : Γ.Has "full_rewatch_arena" fullRewatchArenaSpec) :
    ∀ a m Q X, compactSpec a m Q X → Func.wp Γ full_compact_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  obtain ⟨c, ext, s, F0, R, rfl, hcfg, hext, hlen, hinv, hm, hQ0⟩ :=
    M6HdrCfgContract.elim hs
  let hQ : ∀ r c' ext' s' m',
      FullCfgCompat c c' → FullM6HdrInv c' F0 ext' s' →
      (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.cur_vars ≤ s.core.cur_vars → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 20#64 → F0.Unsat) → (r = 1#64 → s'.core.cur_level = 0) →
      (FullM6HdrMem c' ext' s' ⋆ R) m' → Q (r, ()) m' :=
    fun r c' ext' s' m' hcmp hinv' hr hcv hfu h20 h1 hm' =>
      hQ0 (r, ()) c' ext' s' m' hcmp hinv'.cfgOk hinv'.extOk trivial hinv'.sparse.lengths
        ⟨hinv', hr, hcv, hfu, h20, h1⟩ hm'
  have hdm0 : s.core.dense_mode = 0#64 := hinv.sparse.2.2.2.2
  unfold Func.wp full_compact_body
  refine wp_m6Hdr_focus_frame hm fun hmf => ?_
  c0_hsteps_nogrp; cmp_call hfl
  refine M6HdrContract.intro (w := F0) hinv.cfgOk hinv.extOk hinv.sparse.lengths hinv
    (fullM6HdrMem_unfocus_full hmf) ?_
  rintro ⟨fst, ⟨⟩⟩ ext1 s1 m1 hext1 _ hlen1 ⟨hinv1, hfst, hcv1, hfuel1, h20, h1⟩ hm1
  c0_hsplit
  · have hfst_ne1 : fst ≠ 1#64 := by c0_bound
    c0_hsteps
    rcases hfst with rfl | rfl | rfl
    · exact hQ 0#64 c ext1 s1 m1 (FullCfgCompat.refl c) hinv1 (Or.inl rfl) (by omega) hfuel1
        (fun h => by cases h) (fun h => by cases h) hm1
    · exact absurd rfl hfst_ne1
    · exact hQ 20#64 c ext1 s1 m1 (FullCfgCompat.refl c) hinv1 (Or.inr (Or.inr rfl)) (by omega)
        hfuel1 h20 (fun h => by cases h) hm1
  · have hfst1 : fst = 1#64 := by c0_bound
    obtain ⟨hcl1, hinc1⟩ := h1 hfst1
    have hsp1 := hinv1.sparse
    obtain ⟨F_cur, hspW1⟩ := hsp1.exists_witness
    have hcv1_le := hspW1.1.core_ok.cur_vars_le
    have hmax_lt := c.hmaxv
    have hcv1_lt64 : s1.core.cur_vars < 2 ^ 64 := by unfold dimacsBound at hmax_lt; omega
    refine wp_m6Hdr_focus_frame hm1 fun hm1f => ?_
    c0_hsplit
    · c0_hsteps
      exact hQ 1#64 c ext1 s1 m1 (FullCfgCompat.refl c) hinv1 (Or.inr (Or.inl rfl)) (by omega)
        hfuel1 (fun h => by cases h) (fun _ => hcl1) hm1
    · c0_hsteps_nogrp; cmp_call hmk
      refine FullContract.intro (w := (F0, F_cur)) hspW1.1 hspW1 hm1f ?_
      rintro ⟨⟩ s2 m2 hlen2 ⟨hcore2, _hmod2, hspW2⟩ hm2
      c0_hsteps_nogrp; cmp_call hmp
      refine FullContract.intro (w := ()) hlen2 trivial hm2 ?_
      rintro ⟨ncv, ⟨⟩⟩ s3 m3 hlen3 ⟨hcore3, hmod3, hbij3⟩ hm3
      have hcore3_1 : s3.core = s1.core := Eq.trans hcore3 hcore2
      have hll3 : s3.scratch.last_learned = s2.scratch.last_learned :=
        ScratchModifies.get_of_not_mem hmod3 (f := .last_learned) (by decide)
      have hel3 : s3.scratch.extend_len = s2.scratch.extend_len :=
        ScratchModifies.get_of_not_mem hmod3 (f := .extend_len) (by decide)
      have hspW3 : FullSparseInvW c F0 F_cur s3 :=
        ⟨hlen3, hcore3 ▸ hspW2.2.1,
         ⟨fun v hv => by
            change s3.core.mrk[v]?.getD 0#8 = 0#8
            rw [hcore3]; exact hspW2.2.2.1.1 v hv,
          fun l hl => by
            change s3.core.lit_mark[l]?.getD 0#8 = 0#8
            rw [hcore3]; exact hspW2.2.2.1.2 l hl⟩,
         fun r hr hgr => by
           have hr' : r ∈ fullArenaClauseRefs s2 := by
             unfold fullArenaClauseRefs fullArenaClauseRefsCore at hr ⊢; rw [hcore3] at hr; exact hr
           have hgr' : fullArenaClauseGarb s2 r = false := by
             unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore at hgr ⊢
             rw [← hcore3]; exact hgr
           have hnd' := hspW2.2.2.2.1 r hr' hgr'
           unfold fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore at hnd' ⊢
           rw [hcore3]; exact hnd',
         ⟨fun i hi => by
            rcases hspW2.2.2.2.2.1.1 i hi with hll | hll
            · left; change s3.scratch.last_learned[i]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32
              rw [hll3]; exact hll
            · right; change (s3.scratch.last_learned[i]?.getD 0xFFFFFFFF#32).toNat ∈
                fullArenaClauseRefs s3
              rw [hll3]; unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [hcore3]; exact hll,
          by rw [hel3]; exact hspW2.2.2.2.2.1.2⟩,
         by change s3.core.dense_mode = 0#64; rw [hcore3]; exact hspW2.2.2.2.2.2⟩
      have hbij3' : CompactBijOk s3.core.cur_vars ncv.toNat s3.core.vals
          s3.scratch.work_stk1 s3.scratch.work_stk2 := hcore3 ▸ hbij3
      c0_hsplit
      · c0_hsteps
        exact hQ 1#64 c ext1 s3 _ (FullCfgCompat.refl c)
          ⟨hinv1.cfgOk, hext1, hspW3.toSparse⟩ (Or.inr (Or.inl rfl))
          (by change s3.core.cur_vars ≤ s.core.cur_vars; rw [hcore3_1, hcv1]; exact Nat.le_refl _)
          (by change s3.core.fuel.toNat ≤ s.core.fuel.toNat; rw [hcore3_1]; exact hfuel1)
          (fun h => by cases h) (fun _ => hcore3_1 ▸ hcl1)
          (fullM6HdrMem_unfocus_full hm3)
      · have hold_cv : (BitVec.ofNat 64 s1.core.cur_vars).toNat = s3.core.cur_vars := by
          rw [hcore3_1]; exact bv64_ofNat_toNat hcv1_lt64
        have hncv_le : ncv.toNat ≤ (BitVec.ofNat 64 s1.core.cur_vars).toNat := by
          rw [hold_cv]; exact hbij3'.ncv_le
        have hncv_le_s : ncv.toNat ≤ s.core.cur_vars := by
          rw [hold_cv, hcore3_1, hcv1] at hncv_le; exact hncv_le
        c0_hsteps_nogrp; cmp_call hre
        refine FullContract.intro (w := ()) hlen3 ⟨hold_cv.symm, hncv_le, hspW3.2.2.2.2.1.2⟩
          hm3 ?_
        rintro ⟨ok, ⟨⟩⟩ s4 m4 hlen4 ⟨hcore4, hmod4, helen4, _⟩ hm4
        have hcore4_1 : s4.core = s1.core := Eq.trans hcore4 hcore3_1
        have hll4 : s4.scratch.last_learned = s3.scratch.last_learned :=
          ScratchModifies.get_of_not_mem hmod4 (f := .last_learned) (by decide)
        have hws1_4 : s4.scratch.work_stk1 = s3.scratch.work_stk1 :=
          ScratchModifies.get_of_not_mem hmod4 (f := .work_stk1) (by decide)
        have hws2_4 : s4.scratch.work_stk2 = s3.scratch.work_stk2 :=
          ScratchModifies.get_of_not_mem hmod4 (f := .work_stk2) (by decide)
        have hspW4 : FullSparseInvW c F0 F_cur s4 :=
          ⟨hlen4, hcore4 ▸ hspW3.2.1,
           ⟨fun v hv => by
              change s4.core.mrk[v]?.getD 0#8 = 0#8
              rw [hcore4]; exact hspW3.2.2.1.1 v hv,
            fun l hl => by
              change s4.core.lit_mark[l]?.getD 0#8 = 0#8
              rw [hcore4]; exact hspW3.2.2.1.2 l hl⟩,
           fun r hr hgr => by
             have hr' : r ∈ fullArenaClauseRefs s3 := by
               unfold fullArenaClauseRefs fullArenaClauseRefsCore at hr ⊢
               rw [hcore4] at hr; exact hr
             have hgr' : fullArenaClauseGarb s3 r = false := by
               unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore at hgr ⊢
               rw [← hcore4]; exact hgr
             have hnd' := hspW3.2.2.2.1 r hr' hgr'
             unfold fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore at hnd' ⊢
             rw [hcore4]; exact hnd',
           ⟨fun i hi => by
              rcases hspW3.2.2.2.2.1.1 i hi with hll | hll
              · left; change s4.scratch.last_learned[i]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32
                rw [hll4]; exact hll
              · right; change (s4.scratch.last_learned[i]?.getD 0xFFFFFFFF#32).toNat ∈
                  fullArenaClauseRefs s4
                rw [hll4]; unfold fullArenaClauseRefs fullArenaClauseRefsCore
                rw [hcore4]; exact hll,
            helen4⟩,
           by change s4.core.dense_mode = 0#64; rw [hcore4]; exact hspW3.2.2.2.2.2⟩
        c0_hsplit
        rotate_left
        · c0_hsteps
          exact hQ 1#64 c ext1 s4 _ (FullCfgCompat.refl c)
            ⟨hinv1.cfgOk, hext1, hspW4.toSparse⟩ (Or.inr (Or.inl rfl))
            (by change s4.core.cur_vars ≤ s.core.cur_vars
                rw [hcore4_1, hcv1]; exact Nat.le_refl _)
            (by change s4.core.fuel.toNat ≤ s.core.fuel.toNat; rw [hcore4_1]; exact hfuel1)
            (fun h => by cases h) (fun _ => hcore4_1 ▸ hcl1)
            (fullM6HdrMem_unfocus_full hm4)
        c0_hsteps_nogrp; cmp_call hbn
        refine FullContract.intro (w := (F0, F_cur)) hlen4 ?_ hm4 ?_
        · refine ⟨hspW4, ?_, hncv_le, ?_⟩
          · dsimp only [Arg.val]; rw [hcore4, hold_cv]
          · change CompactBijOk (BitVec.ofNat 64 s1.core.cur_vars).toNat ncv.toNat
              s4.core.vals s4.scratch.work_stk1 s4.scratch.work_stk2
            rw [hold_cv, hcore4, hws1_4, hws2_4]; exact hbij3'
        rintro ⟨⟩ s5 m5 hlen5 ⟨hagr5, hbin5⟩ hm5
        obtain ⟨hsc5, wvec5, wstk5, wu5, nb5, hcore5⟩ := compactBinsMask_elim hagr5
        c0_hsteps_nogrp; cmp_call hdf
        refine ⟨c, s5, m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R, rfl, hlen5, hbin5.layout, hm5,
          fun wvec6 wstk6 wlen6 wsort6 m6 hlen6 hlay6 _ hpres6 hm6 => ?_⟩
        let s6 : FullState :=
          { s5 with
            core := { s5.core with wvec := wvec6, wstk := wstk6, wlen := wlen6, wusable := 0#64 }
            scratch := { s5.scratch with wsort := wsort6 } }
        have hbin6 : CompactUnmapBinsOk ncv.toNat s6.scratch.work_stk2 F_cur s6.core := by
          refine ⟨hlay6, fun l hl1 hl2 => ?_, fun l hl => ?_⟩
          · exact (hpres6 l hl2).1.trans (hbin5.empty_hi l hl1 hl2)
          · have hncv_s5 : ncv.toNat ≤ s5.core.cur_vars := by
              change ncv.toNat ≤ s5.core.cur_vars
              rw [hcore5, hcore4]; exact hbij3'.ncv_le
            obtain ⟨hsz, hsl⟩ := hpres6 l (by omega)
            have hsz' : fullWatchSizeCore s6.core l = fullWatchSizeCore s5.core l := hsz
            rw [hsz']
            have hbin5' : CompactUnmapBinsOk ncv.toNat s6.scratch.work_stk2 F_cur s5.core := by
              change CompactUnmapBinsOk ncv.toNat s5.scratch.work_stk2 F_cur s5.core
              rw [hsc5]; exact hbin5
            exact (hbin5'.slices l hl).relocate hsl
        have hw3 := hspW3.2.1
        have hcore6_eq :
            s6.core.arena = s3.core.arena ∧ s6.core.arena_len = s3.core.arena_len ∧
            s6.core.arena_garbage = s3.core.arena_garbage ∧
            s6.core.first_reducible = s3.core.first_reducible ∧
            s6.core.num_irred = s3.core.num_irred ∧
            s6.core.num_redundant = s3.core.num_redundant ∧
            s6.core.vals = s3.core.vals ∧ s6.core.cur_vars = s3.core.cur_vars ∧
            s6.core.cur_level = s3.core.cur_level ∧ s6.core.dense_mode = s3.core.dense_mode ∧
            s6.core.inconsistent = s3.core.inconsistent ∧
            s6.core.lit_mark = s3.core.lit_mark ∧ s6.core.mrk = s3.core.mrk := by
          dsimp [s6]; rw [hcore5, hcore4]
          exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        have hws1_6 : s6.scratch.work_stk1 = s3.scratch.work_stk1 := by
          dsimp [s6]; rw [hsc5, hws1_4]
        have hws2_6 : s6.scratch.work_stk2 = s3.scratch.work_stk2 := by
          dsimp [s6]; rw [hsc5, hws2_4]
        c0_hsteps_nogrp; cmp_call har
        have hrefs63 : fullArenaClauseRefsCore s6.core = fullArenaClauseRefsCore s3.core := by
          unfold fullArenaClauseRefsCore; rw [hcore6_eq.1, hcore6_eq.2.1]
        have hhdr63 (r : Nat) : fullArenaHdrCore s6.core r = fullArenaHdrCore s3.core r := by
          unfold fullArenaHdrCore; rw [hcore6_eq.1]
        have hsz63 (r : Nat) :
            fullArenaClauseSizeCore s6.core r = fullArenaClauseSizeCore s3.core r := by
          unfold fullArenaClauseSizeCore; rw [hcore6_eq.1]
        have hlits63 (r : Nat) :
            fullArenaClauseLitsCore s6.core r = fullArenaClauseLitsCore s3.core r := by
          unfold fullArenaClauseLitsCore; rw [hcore6_eq.1, hsz63 r]
        have hnext63 (r : Nat) :
            fullArenaNextOff s6.core.arena s6.core.arena_len r =
              fullArenaNextOff s3.core.arena s3.core.arena_len r := by
          rw [hcore6_eq.1, hcore6_eq.2.1]
        have har6_pre :
            CompactArenaPre c F0 F_cur ncv.toNat s6 (BitVec.ofNat 64 s1.core.cur_vars) :=
          ⟨(by rw [hold_cv]; exact hw3.ext_sound),
            ⟨by rw [hcore6_eq.2.1]; exact hw3.arena.len_ok,
             fun r hr => by
               rw [hrefs63] at hr
               rw [hsz63 r, hnext63 r, hcore6_eq.2.1]
               exact hw3.arena.refs_wf r hr,
             fun r hr hsh => by
               rw [hrefs63] at hr; rw [hhdr63 r] at hsh
               rw [hsz63 r, hcore6_eq.1, hcore6_eq.2.1]
               exact hw3.arena.shrk_term r hr hsh,
             fun r hr hns l hl => by
               rw [hrefs63] at hr; unfold fullArenaClauseGarbCore at hns
               rw [hhdr63 r] at hns; rw [hlits63 r] at hl
               rw [hcore6_eq.2.2.2.2.2.2.2.1]
               exact hw3.arena.lits_lt r hr hns l hl,
             fun r hr hns => by
               rw [hrefs63] at hr; unfold fullArenaClauseGarbCore at hns
               rw [hhdr63 r] at hns; rw [hlits63 r]
               exact hw3.arena.entails r hr hns⟩,
            fun r hr hgr => by
              have hr' : r ∈ fullArenaClauseRefs s3 := by
                change r ∈ fullArenaClauseRefsCore s3.core; rw [← hrefs63]; exact hr
              have hgr' : fullArenaClauseGarb s3 r = false := by
                change fullArenaClauseGarbCore s3.core r = false
                unfold fullArenaClauseGarbCore; rw [← hhdr63 r]; exact hgr
              have hnd' := hspW3.2.2.2.1 r hr' hgr'
              change ((fullArenaClauseLitsCore s3.core r).map (· / 2)).Nodup at hnd'
              change ((fullArenaClauseLitsCore s6.core r).map (· / 2)).Nodup
              rw [hlits63 r]; exact hnd',
            hcore6_eq.2.2.2.2.2.2.2.2.2.1.symm ▸ hspW3.2.2.2.2.2,
            hcore6_eq.2.2.2.2.2.2.2.2.1.symm ▸ hcore3_1 ▸ hcl1,
            by rw [hcore6_eq.2.2.2.2.2.2.2.1, hold_cv],
            hncv_le,
            (by rw [hold_cv, hcore6_eq.2.2.2.2.2.2.1, hws1_6, hws2_6]; exact hbij3'),
            (by intro l hl; rw [hold_cv] at hl
                rw [hcore6_eq.2.2.2.2.2.2.1]; exact hw3.vals_domain l hl),
            fun l hl hf => level0_vals_false_entails hw3 (hcore3_1 ▸ hcl1)
              (by rw [hold_cv] at hl; exact hl)
              (by rw [hcore6_eq.2.2.2.2.2.2.1] at hf; exact hf),
            hbin6⟩
        refine FullContract.intro (w := (F0, F_cur, ncv.toNat)) hlen6 har6_pre hm6 ?_
        rintro ⟨ast, ⟨⟩⟩ s7 m7 hlen7 ⟨hagr7, hgarb7, hast, hast2, hast3, hbin7, har7, hll7⟩ hm7
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hcore7, hsc7⟩ :=
          compactArenaMask_elim hagr7 hgarb7
        have hws2_7 : s7.scratch.work_stk2 = s3.scratch.work_stk2 := by
          rw [hsc7]; exact hws2_6
        c0_hsteps_nogrp; cmp_call hvr
        refine FullCfgContract.intro (w := ()) hlen7 ⟨?_, hncv_le, fun nv hnv => ?_⟩ hm7 ?_
        · change s7.core.cur_vars = (BitVec.ofNat 64 s1.core.cur_vars).toNat
          rw [hcore7, hcore6_eq.2.2.2.2.2.2.2.1, hold_cv]
        · obtain ⟨ov, hov, _, _, hinv_ov, _⟩ := hbij3'.inv_ok nv hnv
          rw [hws2_7, hinv_ov, Option.getD_some,
            bv32_ofNat_toNat (by have := hbij3'.old_cv_lt; omega)]
          dsimp only [Arg.val]; rw [hold_cv]; exact hov
        rintro ⟨⟩ c' s8 m8 hcompat8 hlen8
          ⟨hcore_agr8, hft8, _hfd8, htr8, _hcfl8, hvars8, hvals8, hext8, hws1_8, hws2_8⟩ hm8
        dsimp only [Arg.val] at hvars8 hvals8
        have hncv_le8 : ncv.toNat ≤ s8.core.cur_vars := by rw [hvars8.1]; exact Nat.le_refl _
        c0_hsteps_nogrp; rw [← hcompat8.hdr] at hm8 ⊢; cmp_call hvm
        refine FullContract.intro (c := c') (w := ()) hlen8 hncv_le8 hm8 ?_
        rintro ⟨⟩ s9 m9 hlen9 ⟨hcore9, hext9, hws1_9, hws2_9⟩ hm9
        have hncv_le9 : ncv.toNat ≤ s9.core.cur_vars := by rw [hcore9]; exact hncv_le8
        c0_hsteps_nogrp; cmp_call hhp
        refine FullContract.intro (c := c') (w := ()) hlen9 hncv_le9 hm9 ?_
        rintro ⟨⟩ s10 m10 hlen10 ⟨hcore10, hext10, hws1_10, hws2_10⟩ hm10
        dsimp only [CorePres] at hcore9 hcore10
        obtain ⟨har8, hal8, hwv8, hws8, hwl8, hlm8, hmk8, hdm8, hinc8, hfu8⟩ :
            s8.core.arena = s7.core.arena ∧ s8.core.arena_len = s7.core.arena_len ∧
            s8.core.wvec = s7.core.wvec ∧ s8.core.wstk = s7.core.wstk ∧
            s8.core.wlen = s7.core.wlen ∧ s8.core.lit_mark = s7.core.lit_mark ∧
            s8.core.mrk = s7.core.mrk ∧ s8.core.dense_mode = s7.core.dense_mode ∧
            s8.core.inconsistent = s7.core.inconsistent ∧ s8.core.fuel = s7.core.fuel := by
          cases hc7 : s7.core; cases hc8 : s8.core
          dsimp only [AgreesExcept, compactVarsCoreMask] at hcore_agr8
          rw [hc7, hc8] at hcore_agr8; cases hcore_agr8
          exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        have hcore10_fu : s10.core.fuel.toNat ≤ s.core.fuel.toNat := by
          rw [hcore10, hcore9, hfu8, hcore7]; dsimp [s6]; rw [hcore5, hcore4_1]; exact hfuel1
        have hcore10_ar : s10.core.arena = s7.core.arena := by rw [hcore10, hcore9, har8]
        have hcore10_al : s10.core.arena_len = s7.core.arena_len := by rw [hcore10, hcore9, hal8]
        have hcore10_cv : s10.core.cur_vars = ncv.toNat := by rw [hcore10, hcore9, hvars8.1]
        have hcore10_inc : s10.core.inconsistent = 0#64 := by
          rw [hcore10, hcore9, hinc8, hcore7, hcore6_eq.2.2.2.2.2.2.2.2.2.2.1, hcore3_1]
          exact hinc1
        have hcore10_dm : s10.core.dense_mode = 0#64 := by
          rw [hcore10, hcore9, hdm8, hcore7, hcore6_eq.2.2.2.2.2.2.2.2.2.1]
          exact hspW3.2.2.2.2.2
        have hcore10_te : s10.core.trail_end = 0 := by rw [hcore10, hcore9, htr8.1]
        have hcore10_cl : s10.core.cur_level = 0 := by rw [hcore10, hcore9, htr8.2.2.1]
        have har10 : CompactArenaOk ncv.toNat s3.scratch.work_stk2 F_cur s10.core :=
          CompactArenaOk.with_core (by rw [← hws2_6]; exact har7) hcore10_ar hcore10_al
        have hbin10 : CompactUnmapBinsOk ncv.toNat s3.scratch.work_stk2 F_cur s10.core :=
          CompactUnmapBinsOk.with_vars (by rw [← hws2_6]; exact hbin7)
            (by rw [hcore10_cv]; exact Nat.le_refl _)
            (by rw [hcore10_cv, hcore7, hcore6_eq.2.2.2.2.2.2.2.1, ← hold_cv]; exact hncv_le)
            (by rw [hcore10, hcore9, hwv8]) (by rw [hcore10, hcore9, hws8])
            (by rw [hcore10, hcore9, hwl8])
        have hnd10 : FullArenaVarsNodup s10 := fun r hr _ => har10.nodup r hr
        have hmarks10 : FullLitMarksClear c' s10 :=
          FullLitMarksClear.of_compat hcompat8 ⟨fun v hv => by
            change s10.core.mrk[v]?.getD 0#8 = 0#8
            rw [hcore10, hcore9, hmk8, hcore7, hcore6_eq.2.2.2.2.2.2.2.2.2.2.2.2]
            exact hspW3.2.2.1.1 v hv,
          fun l hl => by
            change s10.core.lit_mark[l]?.getD 0#8 = 0#8
            rw [hcore10, hcore9, hlm8, hcore7, hcore6_eq.2.2.2.2.2.2.2.2.2.2.2.1]
            exact hspW3.2.2.1.2 l hl⟩
        have helen7 : s7.scratch.extend_len ≤ c.extend_cap := by
          rw [hsc7]; dsimp [s6]; rw [hsc5]; exact helen4
        have hext10 : FullExtScratchOk c' s10 :=
          FullExtScratchOk.of_compat hcompat8 ⟨hll7, helen7⟩
            ⟨hext10.1.trans (hext9.1.trans hext8.1),
             hext10.2.trans (hext9.2.trans hext8.2)⟩
            (fun r hr => by
              simpa [fullArenaClauseRefs, fullArenaClauseRefsCore, hcore10_ar, hcore10_al] using hr)
        have hvals10 : ∀ l < 2 * s10.core.cur_vars, s10.core.vals[l]?.getD 0#8 = 0#8 := by
          intro l hl
          have hl1 : l < 2 * c'.max_vars := by
            have := hlen10.core_ok.cur_vars_le
            change l < 2 * s10.core.cur_vars at hl
            change s10.core.cur_vars ≤ c'.max_vars at this; omega
          have hl2 : l < 2 * (BitVec.ofNat 64 s1.core.cur_vars).toNat := by
            rw [hold_cv, hcore10_cv] at *; omega
          change s10.core.vals[l]?.getD 0#8 = 0#8
          rw [hcore10, hcore9]; exact hvals8 l hl1 hl2
        have hft10 : (s10.core.frame_trail[0]?.getD 0#32).toNat = 0 := by
          have hft_len : 0 < s7.core.frame_trail.length := by
            have := hlen7.core_ok.frame_trail_len; omega
          change (s10.core.frame_trail[0]?.getD 0#32).toNat = 0
          rw [hcore10, hcore9, hft8, List.getElem?_set_self hft_len, Option.getD_some]; rfl
        have hcfg' : FullM6HdrCfgOk c' := FullM6HdrCfgOk_of_compat hcompat8 hinv1.cfgOk
        c0_hsplit
        · have hast_2 : ast = 2#64 := by c0_bound
          c0_hsteps
          let s11 : FullState := { s10 with core := { s10.core with inconsistent := 1#64 } }
          have har11 : CompactArenaOk ncv.toNat s3.scratch.work_stk2 F_cur s11.core :=
            har10.with_core rfl rfl
          have hbin11 : CompactUnmapBinsOk ncv.toNat s3.scratch.work_stk2 F_cur s11.core :=
            hbin10.with_vars
              (by change ncv.toNat ≤ s10.core.cur_vars; rw [hcore10_cv]; exact Nat.le_refl _)
              (Nat.le_refl _) rfl rfl rfl
          have hw11 := fullWitnessInv_compact_unsat (c := c') (hast2 hast_2) hbin11 har11
            hcore10_cv hcore10_dm hcore10_te hcore10_cl hft10 (hcore10_cv ▸ hvals10)
          have hsp11 : FullSparseInv c' F0 s11 :=
            ⟨⟨{ hlen10 with core_ok := { hlen10.core_ok with
                vals_len := hlen10.core_ok.vals_len } },
              [[]], hw11⟩, hmarks10, hnd10, hext10, hcore10_dm⟩
          exact hQ 20#64 c' ext1 s11 _ hcompat8 ⟨hcfg', hext1, hsp11⟩
            (Or.inr (Or.inr rfl))
            (by change s10.core.cur_vars ≤ _; rw [hcore10_cv]; exact hncv_le_s)
            hcore10_fu (fun _ => hast2 hast_2) (fun h => by cases h)
            (fullM6HdrMem_unfocus_full (by assumption))
        · c0_hsplit
          · c0_hsteps
            let s11 : FullState := { s10 with core := { s10.core with oom := 1#64 } }
            have har11 : CompactArenaOk ncv.toNat s3.scratch.work_stk2 F_cur s11.core :=
              har10.with_core rfl rfl
            have hbin11 : CompactUnmapBinsOk ncv.toNat s3.scratch.work_stk2 F_cur s11.core :=
              hbin10.with_vars
                (by change ncv.toNat ≤ s10.core.cur_vars; rw [hcore10_cv]; exact Nat.le_refl _)
                (Nat.le_refl _) rfl rfl rfl
            have hw11 := fullWitnessInv_compact_build (c := c') hw3.ext_sound
              hbin11 har11 hcore10_cv hcore10_inc hcore10_dm hcore10_te hcore10_cl
              hft10 (hcore10_cv ▸ hvals10)
            have hsp11 : FullSparseInv c' F0 s11 :=
              ⟨⟨{ hlen10 with core_ok := { hlen10.core_ok with
                  vals_len := hlen10.core_ok.vals_len } },
                stateClausesCore s11.core, hw11⟩, hmarks10, hnd10, hext10, hcore10_dm⟩
            exact hQ 0#64 c' ext1 s11 _ hcompat8 ⟨hcfg', hext1, hsp11⟩ (Or.inl rfl)
              (by change s10.core.cur_vars ≤ _; rw [hcore10_cv]; exact hncv_le_s)
              hcore10_fu (fun h => by cases h) (fun h => by cases h)
              (fullM6HdrMem_unfocus_full (by assumption))
          · have hw10 := fullWitnessInv_compact_build (c := c') hw3.ext_sound
              hbin10 har10 hcore10_cv hcore10_inc hcore10_dm hcore10_te hcore10_cl
              hft10 (hcore10_cv ▸ hvals10)
            have hal10_lt : s10.core.arena_len < 2 ^ 64 := by
              have hle : s10.core.arena_len ≤ c'.arena_cap := hlen10.core_ok.arena_len_le
              have := c'.harena; unfold dimacsBound at *; omega
            c0_hsteps_nogrp; cmp_call hrw
            refine ⟨c', F0, stateClausesCore s10.core, s10, m6ExtMem (m6ExtAddr c'.hdr) ext1 ⋆ R,
              rfl, hlen10, hw10, hcore10_dm, bv64_ofNat_toNat hal10_lt, ?_, hm10,
              fun ok arena11 wvec11 wstk11 wlen11 wu11 oom11 ws11 m11
                hlen11 hw11 hnd11 href11 _ _ hm11 => ?_⟩
            · intro r hr
              refine ⟨?_, har10.no_shrk r hr⟩
              have := har10.no_garb r hr
              unfold fullArenaClauseGarb fullArenaClauseGarbCore; simp [this]
            · let s11 : FullState :=
                { s10 with
                  core := { s10.core with arena := arena11, wvec := wvec11, wstk := wstk11,
                                          wlen := wlen11, wusable := wu11, oom := oom11 }
                  scratch := { s10.scratch with wsort := ws11 } }
              have hext11 : FullExtScratchOk c' s11 :=
                FullExtScratchOk.of_pres hext10 ⟨rfl, rfl⟩ fun r hr => by
                  change r ∈ fullArenaClauseRefs s11
                  rw [href11]; exact hr
              have hsp11 : FullSparseInv c' F0 s11 :=
                ⟨⟨hlen11, stateClausesCore s10.core, hw11⟩, hmarks10, hnd11 hnd10, hext11,
                 hcore10_dm⟩
              c0_hsplit
              · c0_hsteps
                exact hQ 1#64 c' ext1 s11 _ hcompat8 ⟨hcfg', hext1, hsp11⟩
                  (Or.inr (Or.inl rfl))
                  (by change s10.core.cur_vars ≤ _; rw [hcore10_cv]; exact hncv_le_s)
                  (by change s11.core.fuel.toNat ≤ _; exact hcore10_fu)
                  (fun h => by cases h) (fun _ => hcore10_cl)
                  (fullM6HdrMem_unfocus_full hm11)
              · c0_hsteps
                let s12 : FullState := { s11 with core := { s11.core with oom := 1#64 } }
                have hw12 : FullWitnessInv c' F0 (stateClausesCore s10.core) s12.core :=
                  { hw11 with
                    arena := { hw11.arena with len_ok := hw11.arena.len_ok }
                    watches := hw11.watches.with_wstk rfl rfl rfl rfl rfl fun _ h => h }
                have hlen12 : s12.LengthsOk c' :=
                  { hlen11 with core_ok := { hlen11.core_ok with
                      vals_len := hlen11.core_ok.vals_len } }
                have hext12 : FullExtScratchOk c' s12 :=
                  FullExtScratchOk.of_pres hext11 ⟨rfl, rfl⟩ fun _ h => h
                have hsp12 : FullSparseInv c' F0 s12 :=
                  ⟨⟨hlen12, stateClausesCore s10.core, hw12⟩, hmarks10, hnd11 hnd10,
                   hext12, hcore10_dm⟩
                exact hQ 0#64 c' ext1 s12 _ hcompat8 ⟨hcfg', hext1, hsp12⟩ (Or.inl rfl)
                  (by change s10.core.cur_vars ≤ _; rw [hcore10_cv]; exact hncv_le_s)
                  (by change s12.core.fuel.toNat ≤ _; exact hcore10_fu)
                  (fun h => by cases h) (fun h => by cases h)
                  (fullM6HdrMem_unfocus_full (by assumption))

end

end LeanQbe.T.Examples.Kissat.Proof.Compact
