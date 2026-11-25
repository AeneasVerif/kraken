/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityVivK6
public import LeanQbe.T.Examples.Kissat.FullFidelityVivK6Proof0a
public import LeanQbe.T.Examples.Kissat.FullM4BvaLemmas1
public import LeanQbe.T.Examples.Kissat.FullSpec
import LeanQbe.T.Examples.Kissat.FullM4BvaLemmas2
import LeanQbe.T.Examples.Kissat.FullAnalyzeLemmas5
import LeanQbe.T.Examples.Kissat.FullPropDecLemmas
import LeanQbe.T.Examples.Kissat.FullBridgeLemmas3
import LeanQbe.T.Examples.Kissat.FullIngestLemmas2
public import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Agrees
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.Logic.ControlComb

/-!
# Kissat Fidelity `full_bva_commit_fid_wp` (`FullFidelityVivK6Proof2`)

UNSAT-only `Func.wp` proof (`public section`, zero expose, zero import-all, `std3`) for
`G1-P2.1b`: `full_bva_commit_fid` (safe 2-literal `u64` copy loop + `u32` tail and `u64` `cnt`
zeroing loops) against exact `FullM4Bva.m4BvaCommitSpec`.
-/

set_option autoImplicit false

local elab "c0_hsteps_np" : tactic => LeanQbe.T.C0HeadStep.headSteps { pruneJnz := false } 10000

local elab "c0_hsteps_nogrp_np" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, pruneJnz := false } 10000

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityVivK6

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full

/-! ## 1. `full_bva_commit_fid` (`FullM4Bva.m4BvaCommitSpec`) -/

section M7BvaProof

open FullBvaHeap FullBvaHeap.FullBvaHeapHelpers FullBvaHeap.FullBvaHeapTactics
open FullBvaHeap.FullBvaHeapScanHelpers FullM4Bva
open scoped FullArenaTactics FullBvaHeapTactics

private theorem nodup_lt_length_le : ∀ {n : Nat} {xs : List Nat},
    xs.Nodup → (∀ x ∈ xs, x < n) → xs.length ≤ n
  | 0, [], _, _ => Nat.zero_le _
  | 0, x :: _, _, hlt => absurd (hlt x (by simp)) (by omega)
  | n + 1, xs, hnd, hlt => by
    by_cases hn : n ∈ xs
    · have hperm := List.perm_cons_erase hn; have hnd' := List.nodup_cons.mp (hnd.perm hperm)
      have hlt' : ∀ y ∈ xs.erase n, y < n := fun y hy => by
        have hmem := List.mem_of_mem_erase hy
        have hne : y ≠ n := fun he => by subst he; exact hnd'.1 hy
        have := hlt y hmem; omega
      have ih := nodup_lt_length_le hnd'.2 hlt'
      have hlen := hperm.length_eq; simp only [List.length_cons] at hlen; omega
    · have hlt' : ∀ y ∈ xs, y < n := fun y hy => by
        have hne : y ≠ n := fun he => by subst he; exact hn hy
        have := hlt y hy; omega
      exact Nat.le_trans (nodup_lt_length_le hnd hlt') (Nat.le_succ _)

private def ArenaMono (k0 k : FullCoreState) : Prop :=
  ∀ r ∈ fullArenaClauseRefsCore k0, r ∈ fullArenaClauseRefsCore k ∧
    fullArenaClauseSizeCore k r = fullArenaClauseSizeCore k0 r ∧
    fullArenaClauseLitsCore k r = fullArenaClauseLitsCore k0 r

private theorem arenaMono_trans {k0 k1 k2 : FullCoreState}
    (h01 : ArenaMono k0 k1) (h12 : ArenaMono k1 k2) : ArenaMono k0 k2 := fun r hr => by
  obtain ⟨hr1, hsz1, hl1⟩ := h01 r hr; obtain ⟨hr2, hsz2, hl2⟩ := h12 r hr1
  exact ⟨hr2, hsz2.trans hsz1, hl2.trans hl1⟩

private abbrev M7BvaStOk (c : FullCfg) (F0 : CNF Nat) (F_next : List (List Nat))
    (s st : FullState) : Prop :=
  FullDenseInvW c F0 F_next st ∧ st.core.cur_vars = s.core.cur_vars + 1 ∧
  st.core.fuel = s.core.fuel ∧ st.scratch.scratch_buf = s.scratch.scratch_buf ∧
  st.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
  st.scratch.tarjan_reach = s.scratch.tarjan_reach ∧ ArenaMono s.core st.core

private abbrev M7BvaPreOk (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s sd : FullState) : Prop :=
  FullDenseInvW c F0 F_cur sd ∧ sd.core.cur_vars = s.core.cur_vars ∧
  sd.core.fuel = s.core.fuel ∧ sd.core.arena = s.core.arena ∧
  sd.core.arena_len = s.core.arena_len ∧ sd.scratch.scratch_buf = s.scratch.scratch_buf ∧
  sd.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
  sd.scratch.tarjan_reach = s.scratch.tarjan_reach

private theorem denseWatchSliceOk_congr {F_cur : List (List Nat)} {k k' : FullCoreState}
    {l off off' n : Nat} (hcv : k'.cur_vars = k.cur_vars)
    (hrefs : fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k)
    (hw : ∀ j < n, k'.wstk[off' + j]? = k.wstk[off + j]?)
    (h : DenseWatchSliceOk F_cur k l off n) : DenseWatchSliceOk F_cur k' l off' n := by
  induction h generalizing off' with
  | empty => exact .empty
  | @bin p rem w0 hp hflag hne hlt hent _ ih =>
    exact .bin (by simpa using (hw 0 (Nat.zero_lt_succ _)).trans hp) hflag hne (by omega) hent
      (ih fun j hj => by simpa [Nat.add_assoc, Nat.add_comm 1 j] using hw (j + 1) (by omega))
  | @occ p rem w0 cref hp hp1 hflag h3 hlt href _ ih =>
    exact .occ (by simpa using (hw 0 (by omega)).trans hp) ((hw 1 (by omega)).trans hp1)
      hflag h3 hlt (by rwa [hrefs])
      (ih fun j hj => by simpa [Nat.add_assoc, Nat.add_comm 2 j] using hw (j + 2) (by omega))

private theorem fullDenseInvW_of_defrag {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {wvec' wstk' wsort' : List (BitVec 32)} {wlen' : Nat}
    (hlen' : let k' := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 }
      ({ s with core := k', scratch := { s.scratch with wsort := wsort' } } :
        FullState).LengthsOk c)
    (hlay' : WatchStackLayout
      { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 })
    (hsl : let k' := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 }
      ∀ l < 2 * s.core.cur_vars, fullWatchSizeCore k' l = fullWatchSizeCore s.core l ∧
      ∀ k < fullWatchSizeCore s.core l,
        wstk'[fullWatchOffCore k' l + k]? = s.core.wstk[fullWatchOffCore s.core l + k]?) :
    let k' := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 }
    FullDenseInvW c F0 F_cur
      { s with core := k', scratch := { s.scratch with wsort := wsort' } } := by
  intro k'; have hdm := hinv.2.2.2.2.2.2; have hdw : DenseWatchesInv F_cur s.core := by
    have h := hinv.2.1.watches; unfold ModeWatchesInv at h; rwa [ite_eq_right hdm] at h
  have hdw' : DenseWatchesInv F_cur k' :=
    DenseWatchesInv.of_slices hlay'.bounds hlay'.pos_off hlay'.disjoint fun l hl => by
      obtain ⟨hsz, hget⟩ := hsl l hl; rw [hsz]
      exact denseWatchSliceOk_congr (k := s.core) (k' := k') rfl rfl (fun j hj => hget j hj)
        (hdw.slices l hl)
  refine ⟨hlen', { hinv.2.1 with
    arena := { hinv.2.1.arena with len_ok := hinv.2.1.arena.len_ok }
    watches := by unfold ModeWatchesInv; rw [ite_eq_right hdm]; exact hdw' },
    hinv.2.2.1, hinv.2.2.2.1, hinv.2.2.2.2.1, hinv.2.2.2.2.2.1, hdm⟩

private theorem fullDenseInvW_of_addBin {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {vals' : List (BitVec 8)} {flags' lvl' rsns' trl' tp' wvec' wstk' wsort' : List (BitVec 32)}
    {ph' : List (BitVec 8)} {te' wlen' : Nat} {unass' unfl' wu' nb' oom' inc' : BitVec 64}
    (hlen' : let k' := { s.core with
      vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
      trail_end := te', unassigned := unass', unflushed := unfl', wvec := wvec', wstk := wstk',
      wlen := wlen', wusable := wu', num_binary := nb', oom := oom', inconsistent := inc' }
      ({ s with core := k', scratch := { s.scratch with phases := ph', wsort := wsort' } } :
        FullState).LengthsOk c)
    (hw' : FullWitnessInv c F0 F_cur { s.core with
      vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
      trail_end := te', unassigned := unass', unflushed := unfl', wvec := wvec', wstk := wstk',
      wlen := wlen', wusable := wu', num_binary := nb', oom := oom', inconsistent := inc' }) :
    let k' := { s.core with
      vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
      trail_end := te', unassigned := unass', unflushed := unfl', wvec := wvec', wstk := wstk',
      wlen := wlen', wusable := wu', num_binary := nb', oom := oom', inconsistent := inc' }
    FullDenseInvW c F0 F_cur
      { s with core := k', scratch := { s.scratch with phases := ph', wsort := wsort' } } :=
  ⟨hlen', hw', hinv.2.2.1, hinv.2.2.2.1, hinv.2.2.2.2.1, hinv.2.2.2.2.2.1, hinv.2.2.2.2.2.2⟩

private theorem fullDenseInvW_of_delBin {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hinv : FullDenseInvW c F0 F_cur s) {wvec' wstk' : List (BitVec 32)}
    {wu' nb' : BitVec 64}
    (hlen' : ({ s with core := { s.core with
      wvec := wvec', wstk := wstk', wusable := wu', num_binary := nb' } } :
      FullState).LengthsOk c)
    (hwat' : ModeWatchesInv F_cur { s.core with
      wvec := wvec', wstk := wstk', wusable := wu', num_binary := nb' }) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with
      wvec := wvec', wstk := wstk', wusable := wu', num_binary := nb' } } :=
  ⟨hlen', { hinv.2.1 with
    arena := { hinv.2.1.arena with len_ok := hinv.2.1.arena.len_ok }, watches := hwat' },
    hinv.2.2.1, hinv.2.2.2.1, hinv.2.2.2.2.1, hinv.2.2.2.2.2.1, hinv.2.2.2.2.2.2⟩

private theorem fullDenseInvW_of_unwatchLarge {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {wvec' wstk' : List (BitVec 32)} {wu' : BitVec 64}
    (hlen' : ({ s with core := { s.core with
      wvec := wvec', wstk := wstk', wusable := wu' } } : FullState).LengthsOk c)
    (hwat' : ModeWatchesInv F_cur { s.core with wvec := wvec', wstk := wstk', wusable := wu' }) :
    FullDenseInvW c F0 F_cur
      { s with core := { s.core with wvec := wvec', wstk := wstk', wusable := wu' } } :=
  fullDenseInvW_of_delBin hinv (nb' := s.core.num_binary) hlen' hwat'

private theorem fullDenseInvW_of_markGarb {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hinv : FullDenseInvW c F0 F_cur s) {cref : Nat}
    (href : cref ∈ fullArenaClauseRefsCore s.core) (ag' : BitVec 64) :
    let ar' := s.core.arena.set cref (fullArenaHdrCore s.core cref ||| 0x00080000#32)
    let s' : FullState := { s with core := { s.core with arena := ar', arena_garbage := ag' } }
    FullDenseInvW c F0 F_cur s' ∧ ArenaMono s.core s'.core := by
  intro ar' s'; have hcl := hinv.1.core_ok; have hwf := hinv.2.1.arena.refs_wf cref href
  have hcref_lt : cref < s.core.arena.length := by
    have := hcl.arena_len_le; have := hcl.arena_len_arr; omega
  have h0 : ar'[cref]? = some (fullArenaHdrCore s.core cref ||| 0x00080000#32) :=
    List.getElem?_set_self hcref_lt
  have hout : ∀ i, i ≠ cref → (i < cref + 3 ∨ cref + 3 + fullArenaClauseSizeCore s.core cref ≤ i) →
      ar'[i]? = s.core.arena[i]? := fun i hne _ => List.getElem?_set_ne (Ne.symm hne)
  have ⟨hclen', hrefs', hw', hother, _⟩ := FullBvaFwdHelpers.fullWitnessInv_markGarb_at_root
    (ag' := ag') hcl hinv.2.1 hinv.2.2.2.2.2.1 href (by simp [ar', hcl.arena_len_arr]) h0 hout
  have hnodup' := FullArenaVarsNodup.of_markGarb hinv.toDense.1 hinv.2.2.2.1 href ag'
  have hext' : FullExtScratchOk c s' := ⟨fun i hi => by
    rcases hinv.2.2.2.2.1.1 i hi with h1 | h2
    · exact Or.inl h1
    · exact Or.inr (by change _ ∈ fullArenaClauseRefsCore s'.core; rw [hrefs']; exact h2),
    hinv.2.2.2.2.1.2⟩
  refine ⟨⟨⟨hclen', hinv.1.scratch_ok⟩, hw', hinv.2.2.1, hnodup', hext',
    hinv.2.2.2.2.2.1, hinv.2.2.2.2.2.2⟩, fun r hr => ⟨by rw [hrefs']; exact hr, ?_, ?_⟩⟩
  · unfold fullArenaClauseSizeCore; dsimp only [s', ar']
    by_cases hrc : r = cref
    · subst hrc; rw [List.getElem?_set_ne (by omega)]
    · have := hinv.2.1.arena.refs_wf r hr
      rcases Nat.lt_or_gt_of_ne hrc with hlt | hgt
      · have := fullArenaScanRefs_disjoint hr href hlt; rw [List.getElem?_set_ne (by omega)]
      · have := fullArenaScanRefs_disjoint href hr hgt; rw [List.getElem?_set_ne (by omega)]
  · by_cases hrc : r = cref
    · subst hrc
      have hsz_eq : fullArenaClauseSizeCore s'.core r = fullArenaClauseSizeCore s.core r := by
        unfold fullArenaClauseSizeCore; dsimp only [s', ar']; rw [List.getElem?_set_ne (by omega)]
      exact fullArenaClauseLitsCore_congr hsz_eq fun j _ => List.getElem?_set_ne (by omega)
    · exact (hother r hr hrc).2

private theorem fullDenseInvW_of_append_clause {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hinv : FullDenseInvW c F0 F_cur s) {sz : Nat}
    (hsz3 : 3 ≤ sz) {ar' wvec' wstk' fl' wsort' : List (BitVec 32)} {wlen' : Nat}
    {wu' ni' : BitVec 64}
    (hlen' : let k' := { s.core with
      arena := ar', arena_len := s.core.arena_len + 3 + sz, wvec := wvec', wstk := wstk',
      wlen := wlen', wusable := wu', flags := fl', num_irred := ni' }
      ({ s with core := k', scratch := { s.scratch with wsort := wsort' } } :
        FullState).LengthsOk c)
    (hhold : ∀ i < s.core.arena_len, ar'[i]? = s.core.arena[i]?)
    (hns : (ar'[s.core.arena_len]?.getD 0#32 &&& 0x00800000#32) = 0#32)
    (hsz_new : (ar'[s.core.arena_len + 2]?.getD 0#32).toNat = sz)
    (hlits_lt : ∀ l ∈ fullArenaClauseLitsCore { s.core with arena := ar' } s.core.arena_len,
      l < 2 * s.core.cur_vars)
    (hlits_nd : ((fullArenaClauseLitsCore { s.core with arena := ar' }
      s.core.arena_len).map (· / 2)).Nodup)
    (hlits_ent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (fullArenaClauseLitsCore { s.core with arena := ar' } s.core.arena_len)))
    (hwat' : ModeWatchesInv F_cur { s.core with
      arena := ar', arena_len := s.core.arena_len + 3 + sz, wvec := wvec', wstk := wstk',
      wlen := wlen', wusable := wu', flags := fl', num_irred := ni' }) :
    let s' : FullState := { s with
      core := { s.core with
        arena := ar', arena_len := s.core.arena_len + 3 + sz, wvec := wvec', wstk := wstk',
        wlen := wlen', wusable := wu', flags := fl', num_irred := ni' },
      scratch := { s.scratch with wsort := wsort' } }
    FullDenseInvW c F0 F_cur s' ∧ ArenaMono s.core s'.core := by
  intro s'; have hw := hinv.2.1; have hcl := hinv.1.core_ok
  have hnxt_hold := hw.arena.arenaNextOff_extend (alen' := s.core.arena_len + 3 + sz)
    (by omega) hhold
  have hrefs :
      fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s.core ++ [s.core.arena_len] :=
    fullArenaClauseRefsCore_append hw.arena hsz3 rfl hhold hns hsz_new
  have hold_garb : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseGarbCore s'.core r = fullArenaClauseGarbCore s.core r := fun r hr => by
    have := (hw.arena.refs_wf r hr).1; unfold fullArenaClauseGarbCore fullArenaHdrCore s'
    simp [hhold r (by omega)]
  have hold_sz : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseSizeCore s'.core r = fullArenaClauseSizeCore s.core r := fun r hr => by
    have := (hw.arena.refs_wf r hr).1; unfold fullArenaClauseSizeCore s'
    simp [hhold (r + 2) (by omega)]
  have hold_lits : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s.core r := fun r hr => by
    have hwf := hw.arena.refs_wf r hr
    exact fullArenaClauseLitsCore_congr (hold_sz r hr) fun j hj => hhold (r + 3 + j) (by omega)
  have harena' : FullArenaClausesInv c F_cur s'.core := by
    refine ⟨Or.inr (by dsimp [s']; omega), ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · have hwf := hw.arena.refs_wf r hr; rw [hnxt_hold r hr, hold_sz r hr]
        refine ⟨by dsimp [s']; omega, hwf.2.1, hwf.2.2.1, by dsimp [s']; omega, ?_⟩
        rcases hwf.2.2.2.2 with he | h3 <;> right <;> dsimp [s'] <;> omega
      · have hnxt_new : fullArenaNextOff s'.core.arena s'.core.arena_len s.core.arena_len =
            s.core.arena_len + 3 + sz := by unfold fullArenaNextOff s'; simp [hsz_new, hns]
        rw [hnxt_new, show fullArenaClauseSizeCore s'.core s.core.arena_len = sz from hsz_new]
        refine ⟨by dsimp [s']; omega, hsz3, by omega, by dsimp [s']; omega, Or.inl (by dsimp [s'])⟩
    · intro r hr hsh; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · have hr3 := (hw.arena.refs_wf r hr).1
        have hsh0 : (fullArenaHdrCore s.core r &&& 0x00800000#32) ≠ 0#32 := by
          unfold fullArenaHdrCore at hsh ⊢; dsimp only [s'] at hsh; rwa [hhold r (by omega)] at hsh
        obtain ⟨t, ht1, ht2, hsent⟩ := hw.arena.shrk_term r hr hsh0
        exact ⟨t, by rw [hold_sz r hr]; exact ht1, by dsimp only [s']; omega,
          by dsimp only [s']; rw [hhold t ht2]; exact hsent⟩
      · unfold fullArenaHdrCore at hsh; dsimp only [s'] at hsh; exact absurd hns hsh
    · intro r hr hng; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · rw [hold_garb r hr] at hng; rw [hold_lits r hr]; exact hw.arena.lits_lt r hr hng
      · exact hlits_lt
    · intro r hr hng; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · rw [hold_garb r hr] at hng; rw [hold_lits r hr]; exact hw.arena.entails r hr hng
      · exact hlits_ent
  have hno_rsn : ∀ idx < s.core.trail_end,
      s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 :=
    fun idx hidx => hw.level0_rsn_none idx hidx (by
      have := hw.lvl_le idx hidx; have := hinv.2.2.2.2.2.1; omega)
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { hw with
      arena := harena', watches := hwat',
      reason_inv := fun idx hidx hne => absurd (hno_rsn idx hidx) hne,
      reason_lit_mem := fun idx hidx hne _ => absurd (hno_rsn idx hidx) hne }
  have hnodup' : FullArenaVarsNodup s' := fun r hr hng => by
    change r ∈ fullArenaClauseRefsCore s'.core at hr
    rw [hrefs, List.mem_append, List.mem_singleton] at hr; rcases hr with hr | rfl
    · change fullArenaClauseGarbCore s'.core r = false at hng; rw [hold_garb r hr] at hng
      change ((fullArenaClauseLitsCore s'.core r).map (· / 2)).Nodup
      rw [hold_lits r hr]; exact hinv.2.2.2.1 r hr hng
    · exact hlits_nd
  have hext' : FullExtScratchOk c s' := ⟨(fun i hi => by
    rcases hinv.2.2.2.2.1.1 i hi with h1 | h2
    · exact Or.inl h1
    · refine Or.inr ?_
      change _ ∈ fullArenaClauseRefsCore s'.core; rw [hrefs]; exact List.mem_append_left _ h2),
    hinv.2.2.2.2.1.2⟩
  exact ⟨⟨hlen', hw', hinv.2.2.1, hnodup', hext', hinv.2.2.2.2.2.1, hinv.2.2.2.2.2.2⟩,
    fun r hr => ⟨by rw [hrefs]; exact List.mem_append_left _ hr, hold_sz r hr, hold_lits r hr⟩⟩

private theorem fullDenseInvW_with_num_irred {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    (ni' : BitVec 64) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with num_irred := ni' } } :=
  ⟨⟨{ hinv.1.core_ok with vals_len := hinv.1.core_ok.vals_len }, hinv.1.scratch_ok⟩,
   { hinv.2.1 with
     arena := { hinv.2.1.arena with len_ok := hinv.2.1.arena.len_ok }
     watches := hinv.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
   hinv.2.2.1, hinv.2.2.2.1, hinv.2.2.2.2.1, hinv.2.2.2.2.2.1, hinv.2.2.2.2.2.2⟩

private theorem fullArenaLitsCore_eq_map {k : FullCoreState} {r sz : Nat}
    (hsz : fullArenaClauseSizeCore k r = sz) (hb : r + 3 + sz ≤ k.arena.length) :
    fullArenaClauseLitsCore k r =
      (List.range sz).map (fun j => (k.arena[r + 3 + j]?.getD 0#32).toNat) := by
  apply List.ext_getElem?; intro j; by_cases hj : j < sz
  · rw [FullBvaFwdHelpers.fullArenaClauseLitsCore_getElem (by omega) (by omega),
      List.getElem?_map, List.getElem?_range hj, Option.map_some,
      List.getElem?_eq_getElem (by omega), Option.getD_some]
  · rw [List.getElem?_eq_none (by
        rw [FullBvaFwdHelpers.fullArenaClauseLitsCore_length (by omega), hsz]; omega),
      List.getElem?_eq_none (by simp; omega)]

private theorem bv32_lit_mask_eq {x : BitVec 32} (h : x.toNat < 2 ^ 31) :
    (x &&& 0x7FFFFFFF#32) = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (0x7FFFFFFF#32).toNat = 2 ^ 31 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt h]

private theorem bv32_shl1_xor1 {x : BitVec 32} (h : x.toNat < 2 ^ 31) :
    ((x <<< (1 : Nat)) ^^^ 1#32).toNat = 2 * x.toNat + 1 := by
  have hev : (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
    rw [bv32_shl1_nat, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_xor, show (1#32).toNat = 1 from rfl, hev]; apply Nat.eq_of_testBit_eq; intro k
  cases k with
  | zero => simp [Nat.testBit_zero]
  | succ j =>
    rw [Nat.testBit_xor, show Nat.testBit 1 (j + 1) = false by rw [Nat.testBit_succ]; simp,
      Bool.xor_false, Nat.testBit_succ, Nat.testBit_succ,
      show (2 * x.toNat + 1) / 2 = (2 * x.toNat) / 2 by omega]

private theorem bv32_shl1_or1 {x : BitVec 32} (h : x.toNat < 2 ^ 31) :
    ((x <<< (1 : Nat)) ||| 1#32).toNat = 2 * x.toNat + 1 := by
  have hev : (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
    rw [bv32_shl1_nat, Nat.mod_eq_of_lt (by omega)]
  rw [FullBvaFwdTactics.bv32_or1_of_even (by rw [hev]; omega), hev]

private theorem fullDenseInvW_set_flags {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {fl' : List (BitVec 32)} (hfl : fl'.length = c.max_vars) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with flags := fl' } } :=
  fullDenseInv_with_core_aux (tc' := s.core.tmp_cnt) (tl' := s.core.tmp_len) (sc' := s.scratch)
    hinv hinv.1.core_ok.repr_len hinv.1.core_ok.min_clr_len_arr hinv.1.core_ok.tmp_len_arr
    hfl hinv.1.core_ok.tmp_len_le hinv.1.scratch_ok rfl rfl

private theorem fullDenseInvW_set_tmp {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {tmp' : List (BitVec 32)} (htmp : tmp'.length = c.max_vars) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with tmp := tmp' } } :=
  fullDenseInv_with_core_aux (tc' := s.core.tmp_cnt) (tl' := s.core.tmp_len) (sc' := s.scratch)
    hinv hinv.1.core_ok.repr_len hinv.1.core_ok.min_clr_len_arr htmp hinv.1.core_ok.flags_len
    hinv.1.core_ok.tmp_len_le hinv.1.scratch_ok rfl rfl

private theorem fullDenseInvW_set_wsort {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {ws' : List (BitVec 32)} (hws : ws'.length = 2 * c.max_vars) :
    FullDenseInvW c F0 F_cur { s with scratch := { s.scratch with wsort := ws' } } :=
  fullDenseInv_with_core_aux (tc' := s.core.tmp_cnt) (tl' := s.core.tmp_len)
    (sc' := { s.scratch with wsort := ws' }) hinv hinv.1.core_ok.repr_len
    hinv.1.core_ok.min_clr_len_arr hinv.1.core_ok.tmp_len_arr hinv.1.core_ok.flags_len
    hinv.1.core_ok.tmp_len_le { hinv.1.scratch_ok with wsort_len := hws } rfl rfl

private theorem wp_jump_eq {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost}
    {L : Cont ts} {args : Tup (Arg Val) ts} {m : Mem 64} :
    wp Γ Q X (.jump L args) m = L (vals args) m := rfl

private theorem is_wp_goal {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {e : Expr Val Cont rs} {m : Mem 64} (h : wp Γ Q X e m) : wp Γ Q X e m := h

local macro "m7_hsteps_to_jump" : tactic =>
  `(tactic| repeat (
    apply is_wp_goal
    first | (rw [wp_jump_eq]; dsimp only [vals, Arg.val]) | c0_hstep))

private def sDummyVal : (t : Ty) → Val t
  | .bits _ => 0 | .bool => true | .float _ => 0 | .pair a b => (sDummyVal a, sDummyVal b)
private def sDummyTup : (ts : List Ty) → Tup Val ts
  | [] => () | t :: ts => (sDummyVal t, sDummyTup ts)
private def sStep {rs : List Ty} : Expr Val Cont rs → Expr Val Cont rs
  | .let_ (ts := ts) _ k => k (sDummyTup ts) | .load t _ k => k (sDummyVal t)
  | .store _ _ k => k | .call (bs := bs) _ _ k => k (sDummyTup bs) | _ => .hlt
private def sSteps {rs : List Ty} : Nat → Expr Val Cont rs → Expr Val Cont rs
  | 0, e => e | n + 1, e => sSteps n (sStep e)
private def sLd64 {rs : List Ty} (v : Val i64) : Expr Val Cont rs → Expr Val Cont rs
  | .load (.bits 64) _ k => k v | _ => .hlt
private def sLd32 {rs : List Ty} (v : Val i32) : Expr Val Cont rs → Expr Val Cont rs
  | .load (.bits 32) _ k => k v | _ => .hlt
private def sLet32 {rs : List Ty} (v : Val i32) : Expr Val Cont rs → Expr Val Cont rs
  | .let_ (ts := [.bits 32]) _ k => k (v, ()) | _ => .hlt
private def sThen {rs : List Ty} : Expr Val Cont rs → Expr Val Cont rs | .jnz _ t _ => t | _ => .hlt
private def sElse {rs : List Ty} : Expr Val Cont rs → Expr Val Cont rs | .jnz _ _ e => e | _ => .hlt
private def sGrp0 {rs : List Ty} (J : Cont []) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[]]) bs _ => (match bs (J, ()) with | .cons f .nil => f ()) | _ => .hlt
private def sGrp1 {rs : List Ty} (J : Cont [i32]) (x : Val i32) :
    Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32]]) bs _ =>
    (match bs (J, ()) with | .cons f .nil => f (x, ())) | _ => .hlt
private def sGrp64_32 {rs : List Ty} (J : Cont [i64, i32]) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 64, .bits 32]]) bs _ =>
    (match bs (J, ()) with | .cons f .nil => f (0#64, 0#32, ())) | _ => .hlt
private def sGrp64_64_32 {rs : List Ty} (J : Cont [i64, i64, i32]) :
    Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 64, .bits 64, .bits 32]]) bs _ =>
    (match bs (J, ()) with | .cons f .nil => f (0#64, 0#64, 0#32, ())) | _ => .hlt
private def sGrp32b {rs : List Ty} (J : Cont [i32, .bool]) (a : Val i32) (b : Val .bool) :
    Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32, .bool]]) bs _ =>
    (match bs (J, ()) with | .cons f .nil => f (a, b, ())) | _ => .hlt

private def m7BvaMidExpr (e : Expr Val Cont [.bool]) : Expr Val Cont [.bool] :=
  e |> sGrp64_32 (fun _ _ => True) |> sStep |> sElse
    |> sGrp64_64_32 (fun _ _ => True) |> sStep |> sElse
    |> sSteps 5 |> sElse |> sSteps 5 |> sElse |> sSteps 6 |> sElse |> sGrp0 (fun _ _ => True)
private def m7BvaHdrExpr (h pAr pScr : Val i64) (best_k : Val i32) : Expr Val Cont [.bool] :=
  full_bva_commit_fid_body Val Cont (h, best_k, ())
    |> sSteps 3 |> sElse |> sStep |> sLd64 pAr |> sStep |> sLd64 pScr
private def m7BvaDelColExpr (h pAr pScr pFl : Val i64) (best_k mi : Val i32) (Jm : Cont [i32]) :
    Expr Val Cont [.bool] :=
  m7BvaHdrExpr h pAr pScr best_k |> sSteps 3 |> sLd64 pFl |> sSteps 14 |> m7BvaMidExpr
    |> sSteps 35 |> sGrp32b (fun _ _ => True) 0#32 true |> sGrp32b (fun _ _ => True) 0#32 true
    |> sThen |> sGrp1 Jm mi |> sStep |> sThen
private def m7BvaPhase2Expr (h pAr pScr pCnt pFl : Val i64) (best_k mn : Val i32) :
    Expr Val Cont [.bool] :=
  m7BvaHdrExpr h pAr pScr best_k |> sStep |> sLd64 pCnt |> sStep |> sLd64 pFl
    |> sSteps 7 |> sLd32 mn |> sSteps 6 |> m7BvaMidExpr |> sSteps 35
    |> sGrp32b (fun _ _ => True) 0#32 true |> sGrp32b (fun _ _ => True) 0#32 true |> sThen
private def m7BvaPostDefragExpr (h pAr pScr pCnt pFl : Val i64) (best_k mn : Val i32) :
    Expr Val Cont [.bool] :=
  m7BvaHdrExpr h pAr pScr best_k |> sStep |> sLd64 pCnt |> sStep |> sLd64 pFl
    |> sSteps 2 |> sLet32 (best_k + 1#32) |> sSteps 4 |> sLd32 mn |> sSteps 6 |> m7BvaMidExpr
private def m7BvaPhase1bExpr (h pAr pScr pCnt pFl pTmp : Val i64) (best_k mn fresh : Val i32)
    (ok1a : Val .bool) : Expr Val Cont [.bool] :=
  m7BvaHdrExpr h pAr pScr best_k |> sStep |> sLd64 pCnt |> sStep |> sLd64 pFl |> sSteps 7
    |> sLd32 mn |> sSteps 6 |> m7BvaMidExpr |> sSteps 32 |> sLet32 fresh |> sStep |> sLd64 pTmp
    |> sGrp32b (fun _ _ => True) 0#32 ok1a
private def bZext (a : Arg Val i32) (k : Val i64 → Expr Val Cont [.bool]) : Expr Val Cont [.bool] :=
  Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (a, ()) } fun p => k p.fst
private def bOp64 (op : OpCode [i64, i64] [i64]) (a b : Arg Val i64)
    (k : Val i64 → Expr Val Cont [.bool]) : Expr Val Cont [.bool] :=
  Expr.let_ { sig := [i64, i64], code := op, args := (a, b, ()) } fun p => k p.fst
private def bOp32 (op : OpCode [i32, i32] [i32]) (a b : Arg Val i32)
    (k : Val i32 → Expr Val Cont [.bool]) : Expr Val Cont [.bool] :=
  Expr.let_ { sig := [i32, i32], code := op, args := (a, b, ()) } fun p => k p.fst
private def bCmp32 (op : CmpOp) (a b : Arg Val i32) (k : Val .bool → Expr Val Cont [.bool]) :
    Expr Val Cont [.bool] :=
  Expr.let_ { sig := [i32, i32], code := OpCode.cmp op i32, args := (a, b, ()) } fun p => k p.fst
private def bPtr32 (base idx : Val i64) (k : Val i64 → Expr Val Cont [.bool]) :
    Expr Val Cont [.bool] :=
  bOp64 (.mul i64) (Arg.var idx) (Arg.imm 4) fun off =>
    bOp64 (.add i64) (Arg.var base) (Arg.var off) k
private def bLd32 (base idx : Val i64) (k : Val i32 → Expr Val Cont [.bool]) :
    Expr Val Cont [.bool] := bPtr32 base idx fun ptr => Expr.load i32 (Arg.var ptr) k

private def m7BvaLargeWatchExpr (h pAr pFl pTmp : Val i64) (tk : Val i32) (ncr : Val i64)
    (J6 : Cont [.bool]) : Expr Val Cont [.bool] :=
  Expr.group (fun _ => Blocks.cons (fun (p : Tup Val [.bool, i32]) =>
    Expr.group (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
      Expr.jump J6 (Arg.var p.fst, ())) Blocks.nil) fun Jni =>
    Expr.jnz (Arg.var p.fst)
      (bOp64 (.add i64) (Arg.var h) (Arg.imm 488) fun p1 => Expr.load i64 (Arg.var p1) fun ld =>
       bOp64 (.add i64) (Arg.var ld) (Arg.imm 1) fun p2 => bOp64 (.add i64) (Arg.var h)
         (Arg.imm 488) fun p3 => Expr.store (Arg.var p2) (Arg.var p3) (Expr.jump Jni.fst ()))
      (Expr.jump Jni.fst ())) Blocks.nil) fun Jw_exit =>
  Expr.group (fun Jw => Blocks.cons (fun (pj : Tup Val [i32]) =>
    bCmp32 .ult (Arg.var pj.fst) (Arg.var tk) fun c => Expr.jnz (Arg.var c)
      (bZext (Arg.var pj.fst) fun j64 => bLd32 pTmp j64 fun lj =>
       bOp32 (.and i32) (Arg.var tk) (Arg.imm 2147483647) fun tkm =>
       Expr.let_ { sig := [i64], code := OpCode.trunc 64 32, args := (Arg.var ncr, ()) } fun n32 =>
       Expr.call "full_watch_push" (as := [i64, i32, i32, i32, i32]) (bs := [.bool])
         (Arg.var h, Arg.var lj, Arg.var tkm, Arg.var n32.fst, Arg.imm 2, ()) fun okw =>
       Expr.jnz (Arg.var okw.fst)
         (bZext (Arg.var pj.fst) fun j64b => bLd32 pTmp j64b fun ljb =>
          bOp32 (.lshr i32) (Arg.var ljb) (Arg.imm 1) fun tv => bZext (Arg.var tv) fun tv64 =>
          bPtr32 pFl tv64 fun pfv => bZext (Arg.var tv) fun tv64b => bLd32 pFl tv64b fun flv =>
          Expr.group (fun _ => Blocks.cons (fun (pf : Tup Val [i32]) =>
            bOp32 (.or i32) (Arg.var flv) (Arg.var pf.fst) fun nfl => Expr.store (Arg.var nfl)
              (Arg.var pfv) (bOp32 (.add i32) (Arg.var pj.fst) (Arg.imm 1) fun j1 =>
              Expr.jump Jw.fst (Arg.var j1, ()))) Blocks.nil) fun Jt =>
          bZext (Arg.var pj.fst) fun j64c => bLd32 pTmp j64c fun ljc =>
          bOp32 (.and i32) (Arg.var ljc) (Arg.imm 1) fun b1 => bCmp32 .ne (Arg.var b1)
            (Arg.imm 0) fun c1 => Expr.jnz (Arg.var c1) (Expr.jump Jt.fst (Arg.imm 64, ()))
            (Expr.jump Jt.fst (Arg.imm 32, ())))
         (Expr.group (fun Juk => Blocks.cons (fun (pu : Tup Val [i32]) =>
            bCmp32 .ult (Arg.var pu.fst) (Arg.var pj.fst) fun cu => Expr.jnz (Arg.var cu)
              (bZext (Arg.var pu.fst) fun u64 => bLd32 pTmp u64 fun lu =>
               Expr.let_ { sig := [i64], code := OpCode.trunc 64 32, args := (Arg.var ncr, ()) }
                 fun n32u => Expr.call "full_unwatch_large" (as := [i64, i32, i32]) (bs := [])
                 (Arg.var h, Arg.var lu, Arg.var n32u.fst, ()) fun _ =>
               bOp32 (.add i32) (Arg.var pu.fst) (Arg.imm 1) fun u1 =>
               Expr.jump Juk.fst (Arg.var u1, ()))
              (bPtr32 pAr ncr fun par1 => bLd32 pAr ncr fun hdrv => bOp32 (.or i32)
                 (Arg.var hdrv) (Arg.imm 524288) fun nhdr => Expr.store (Arg.var nhdr)
                 (Arg.var par1) (bOp64 (.add i64) (Arg.var h) (Arg.imm 472) fun pg1 =>
                  Expr.load i64 (Arg.var pg1) fun ag => bOp64 (.add i64) (Arg.var ag) (Arg.imm 3)
                    fun ag3 => bZext (Arg.var tk) fun tk64 => bOp64 (.add i64) (Arg.var ag3)
                    (Arg.var tk64) fun agn => bOp64 (.add i64) (Arg.var h) (Arg.imm 472) fun pg2 =>
                  Expr.store (Arg.var agn) (Arg.var pg2)
                    (Expr.jump Jw_exit.fst (Arg.imm false, Arg.var pj.fst, ()))))) Blocks.nil)
          fun Juk => Expr.jump Juk.fst (Arg.imm 0, ())))
      (Expr.jump Jw_exit.fst (Arg.var true, Arg.var pj.fst, ()))) Blocks.nil)
  fun Jw => Expr.jump Jw.fst (Arg.imm 0, ())

private def bIdx0_64 (k : Val i64 → Expr Val Cont [.bool]) : Expr Val Cont [.bool] :=
  Expr.let_ { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 0, ()) } fun z0 =>
    k z0.fst

private def fidBvaZeroCntExpr (pCnt zl : Val i64) (eExit : Expr Val Cont [.bool]) :
    Expr Val Cont [.bool] :=
  Expr.group (fun Jz => Blocks.cons (fun (pz : Tup Val [i64]) =>
    bOp64 (.add i64) (Arg.var pz.fst) (Arg.imm 2) fun zi2 =>
    Expr.let_ { sig := [i64, i64], code := OpCode.cmp .ule i64,
                args := (Arg.var zi2, Arg.var zl, ()) } fun cz =>
    Expr.jnz (Arg.var cz.fst)
      (bPtr32 pCnt pz.fst fun zp => bIdx0_64 fun z0 =>
       bOp64 (.mul i64) (Arg.var z0) (Arg.imm 8) fun z08 =>
       bOp64 (.add i64) (Arg.var zp) (Arg.var z08) fun zp0 =>
       Expr.store (t := i64) (Arg.imm 0) (Arg.var zp0)
         (bOp64 (.add i64) (Arg.var pz.fst) (Arg.imm 2) fun zi2b =>
          Expr.jump Jz.fst (Arg.var zi2b, ())))
      eExit) Blocks.nil) fun Jz => Expr.jump Jz.fst (Arg.imm 0, ())

private theorem fid_bv64_add2_toNat {zi : BitVec 64} {ub : Nat}
    (hzi : zi.toNat ≤ ub) (hub : ub + 2 < 2 ^ 64) : (zi + 2#64).toNat = zi.toNat + 2 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

private theorem fid_bv64_ule_add2 {zi zl : BitVec 64} {ub : Nat}
    (hzl : zl.toNat = ub) (hzi : zi.toNat ≤ ub) (hub : ub + 2 < 2 ^ 64)
    (hle : zi + 2#64 ≤ zl) : zi.toNat + 2 ≤ ub := by
  have h1 : (zi + 2#64).toNat ≤ zl.toNat := BitVec.le_def.mp hle
  rw [fid_bv64_add2_toNat hzi hub, hzl] at h1; exact h1

private theorem fid_bv32_add2_toNat {jc : BitVec 32} {tk : Nat}
    (hjc : jc.toNat ≤ tk) (htk : tk + 2 < 2 ^ 32) : (jc + 2#32).toNat = jc.toNat + 2 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

private theorem fid_bv32_ule_add2 {jc tk : BitVec 32}
    (hjc : jc.toNat ≤ tk.toNat) (htk : tk.toNat + 2 < 2 ^ 32)
    (hle : jc + 2#32 ≤ tk) : jc.toNat + 2 ≤ tk.toNat := by
  have h1 : (jc + 2#32).toNat ≤ tk.toNat := BitVec.le_def.mp hle
  rwa [fid_bv32_add2_toNat hjc htk] at h1

private theorem fid_addr_add0_mul4 (base idx : BitVec 64) :
    base + idx * 4#64 + BitVec.ofNat 64 0 * 8#64 = base + BitVec.ofNat 64 (4 * idx.toNat) := by
  have h0 : BitVec.ofNat 64 0 * 8#64 = 0#64 := rfl
  have hm : idx * 4#64 = BitVec.ofNat 64 (4 * idx.toNat) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_mul, Nat.mul_comm]
  rw [h0, BitVec.add_zero, hm]

private theorem fid_tmp_copy_addr (pTmp : BitVec 64) (jb : BitVec 32) :
    pTmp + BitVec.setWidth 64 jb * 4#64 + BitVec.ofNat 64 0 * 8#64 =
      pTmp + BitVec.ofNat 64 (4 * jb.toNat) := by
  rw [fid_addr_add0_mul4, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]

private theorem fid_tmp_tail_addr (pTmp : BitVec 64) (jb : BitVec 32) :
    pTmp + BitVec.setWidth 64 jb * 4#64 = pTmp + BitVec.ofNat 64 (4 * jb.toNat) := by
  have h := fid_tmp_copy_addr pTmp jb
  have h0 : BitVec.ofNat 64 0 * 8#64 = 0#64 := rfl
  rwa [h0, BitVec.add_zero] at h

private theorem fid_arena_copy_addr (pAr : BitVec 64) {ncr0 : Nat} (hncr : ncr0 + 3 < 2 ^ 64)
    (jb : BitVec 32) (_hj : ncr0 + 3 + jb.toNat < 2 ^ 64) :
    pAr + (BitVec.ofNat 64 ncr0 + 3#64) * 4#64 + BitVec.setWidth 64 jb * 4#64 +
        BitVec.ofNat 64 0 * 8#64 =
      pAr + BitVec.ofNat 64 (4 * (ncr0 + 3 + jb.toNat)) := by
  have h0 : BitVec.ofNat 64 0 * 8#64 = 0#64 := rfl
  have hn3 : (BitVec.ofNat 64 ncr0 + 3#64).toNat = ncr0 + 3 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hj64 : (BitVec.setWidth 64 jb).toNat = jb.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
  have hm1 : (BitVec.ofNat 64 ncr0 + 3#64) * 4#64 = BitVec.ofNat 64 (4 * (ncr0 + 3)) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_mul, hn3, Nat.mul_comm]
  have hm2 : BitVec.setWidth 64 jb * 4#64 = BitVec.ofNat 64 (4 * jb.toNat) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_mul, hj64, Nat.mul_comm]
  rw [h0, BitVec.add_zero, hm1, hm2, BitVec.add_assoc]
  congr 1; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, Nat.mul_add]

private theorem fid_arena_tail_addr (pAr : BitVec 64) {ncr0 : Nat} (hncr : ncr0 + 3 < 2 ^ 64)
    (jb : BitVec 32) (hj : ncr0 + 3 + jb.toNat < 2 ^ 64) :
    pAr + (BitVec.ofNat 64 ncr0 + 3#64) * 4#64 + BitVec.setWidth 64 jb * 4#64 =
      pAr + BitVec.ofNat 64 (4 * (ncr0 + 3 + jb.toNat)) := by
  have h := fid_arena_copy_addr pAr hncr jb hj
  have h0 : BitVec.ofNat 64 0 * 8#64 = 0#64 := rfl
  rwa [h0, BitVec.add_zero] at h

private theorem fullMem_wsort_split (c : FullCfg) (s : FullState) (R : Mem 64 → Prop) :
    ∃ Q, ∀ (ws' : List (BitVec 32)) m,
      (FullMem c { s with scratch := { s.scratch with wsort := ws' } } ⋆ R) m ↔
        (array (t := i32) c.pWsort ws' ⋆ Q) m :=
  ⟨dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
    array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆ FullCoreArrays c s.core ⋆
    (FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆
      (array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆
        array (t := i32) c.pWorkStk2 s.scratch.work_stk2 ⋆
        array (t := i32) c.pTarjanMark s.scratch.tarjan_mark ⋆
        array (t := i32) c.pTarjanReach s.scratch.tarjan_reach) ⋆
      FullScrMetaArrs c s.scratch ⋆ FullScrDynArrs c s.scratch) ⋆ c.pad ⋆ R,
   fun ws' m => by
     unfold FullMem FullScratchArrays FullScrWksArrs
     exact ⟨fun h => sep_ac h, fun h => sep_ac h⟩⟩

private theorem fullMem_tmp_split (c : FullCfg) (s : FullState) (R : Mem 64 → Prop) :
    ∃ Q, ∀ (tmp' : List (BitVec 32)) m,
      (FullMem c { s with core := { s.core with tmp := tmp' } } ⋆ R) m ↔
        (array (t := i32) c.pTmp tmp' ⋆ Q) m :=
  ⟨dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
    array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
    (FullCoreByteArrs c s.core ⋆
      (array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
        array (t := i32) c.pReason s.core.rsns ⋆ array (t := i32) c.pTrail s.core.trl ⋆
        array (t := i32) c.pTrailPos s.core.trail_pos ⋆
        array (t := i32) c.pMinClr s.core.min_clr) ⋆
      FullCoreU32B c s.core ⋆ FullCoreDynArrs c s.core) ⋆ FullScratchArrays c s.scratch ⋆ c.pad ⋆ R,
   fun tmp' m => by
     unfold FullMem FullCoreArrays FullCoreU32A
     exact ⟨fun h => sep_ac h, fun h => sep_ac h⟩⟩

private theorem fullMem_arena_split (c : FullCfg) (s : FullState) (R : Mem 64 → Prop) :
    ∃ Q, ∀ (ar' : List (BitVec 32)) m,
      (FullMem c { s with core := { s.core with arena := ar' } } ⋆ R) m ↔
        (array (t := i32) c.pArena ar' ⋆ Q) m :=
  ⟨dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
    array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
    (FullCoreByteArrs c s.core ⋆ FullCoreU32A c s.core ⋆ FullCoreU32B c s.core ⋆
      array (t := i32) c.pWstk s.core.wstk) ⋆ FullScratchArrays c s.scratch ⋆ c.pad ⋆ R,
   fun ar' m => by
     unfold FullMem FullCoreArrays FullCoreDynArrs
     exact ⟨fun h => sep_ac h, fun h => sep_ac h⟩⟩

private theorem store_fullMem_wsort_zero_i64 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {i : Nat} {addr : BitVec 64}
    (haddr : addr = c.pWsort + BitVec.ofNat 64 (4 * i))
    (hi : i + 1 < s.scratch.wsort.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i64 addr ∧
      (FullMem c { s with scratch := { s.scratch with
        wsort := (s.scratch.wsort.set i 0#32).set (i + 1) 0#32 } } ⋆ R)
        (storeMem m i64 addr 0#64) := by
  subst haddr; obtain ⟨Q, hQ⟩ := fullMem_wsort_split c s R
  have hm' : (array (t := i32) c.pWsort s.scratch.wsort ⋆ Q) m := (hQ s.scratch.wsort m).mp hm
  have hs := store_array32_as_i64 (xs := s.scratch.wsort) 0#64 hi hm'
  have h0 : BitVec.setWidth 32 (0#64 : BitVec 64) = 0#32 := rfl
  have h1 : BitVec.setWidth 32 ((0#64 : BitVec 64) >>> 32) = 0#32 := rfl
  rw [h0, h1] at hs; exact ⟨hs.1, (hQ _ _).mpr hs.2⟩

private theorem loadVal_fullMem_tmp_i64_off {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {i : Nat} {addr : BitVec 64}
    (haddr : addr = c.pTmp + BitVec.ofNat 64 (4 * i))
    (hi : i + 1 < s.core.tmp.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i64 addr = some (packU32Pair s.core.tmp[i] s.core.tmp[i + 1]) := by
  subst haddr; obtain ⟨Q, hQ⟩ := fullMem_tmp_split c s R
  exact loadVal_array32_as_i64 hi ((hQ s.core.tmp m).mp hm)

private theorem loadVal_fullMem_tmp_i32_off {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {i : Nat} {addr : BitVec 64}
    (haddr : addr = c.pTmp + BitVec.ofNat 64 (4 * i))
    (hi : i < s.core.tmp.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 addr = some (s.core.tmp[i]'hi) := by
  subst haddr; obtain ⟨Q, hQ⟩ := fullMem_tmp_split c s R
  exact loadVal_array (by decide) hi ((hQ s.core.tmp m).mp hm)

private theorem store_fullMem_arena_i64_off {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {i : Nat} (v : BitVec 64) {addr : BitVec 64}
    (haddr : addr = c.pArena + BitVec.ofNat 64 (4 * i))
    (hi : i + 1 < s.core.arena.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i64 addr ∧
      (FullMem c { s with core := { s.core with
        arena := (s.core.arena.set i (v.setWidth 32)).set (i + 1)
          ((v >>> 32).setWidth 32) } } ⋆ R) (storeMem m i64 addr v) := by
  subst haddr; obtain ⟨Q, hQ⟩ := fullMem_arena_split c s R
  have hm' : (array (t := i32) c.pArena s.core.arena ⋆ Q) m := (hQ s.core.arena m).mp hm
  obtain ⟨hok, hst⟩ := store_array32_as_i64 v hi hm'
  exact ⟨hok, (hQ _ _).mpr hst⟩

private theorem store_fullMem_arena_i32_off {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {i : Nat} (v : BitVec 32) {addr : BitVec 64}
    (haddr : addr = c.pArena + BitVec.ofNat 64 (4 * i))
    (hi : i < s.core.arena.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 addr ∧
      (FullMem c { s with core := { s.core with arena := s.core.arena.set i v } } ⋆ R)
        (storeMem m i32 addr v) := by
  subst haddr; obtain ⟨Q, hQ⟩ := fullMem_arena_split c s R
  have hm' : (array (t := i32) c.pArena s.core.arena ⋆ Q) m := (hQ s.core.arena m).mp hm
  obtain ⟨hok, hst⟩ := c0_store_array32_nat v hm' hi
  exact ⟨hok, (hQ _ _).mpr hst⟩

private theorem fid_bva_zero_cnt_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    {c : FullCfg} {st : FullState} {R : Mem 64 → Prop} {zl : BitVec 64} {n : Nat}
    {eExit : Expr Val Cont [.bool]} {m0 : Mem 64}
    (hn : n ≤ c.max_vars) (hzl : zl.toNat = 2 * n)
    (hws0 : st.scratch.wsort.length = 2 * c.max_vars) (hm0 : (FullMem c st ⋆ R) m0)
    (hExit : ∀ (wsz : List (BitVec 32)) (mzi : Mem 64), wsz.length = 2 * c.max_vars →
      (FullMem c { st with scratch := { st.scratch with wsort := wsz } } ⋆ R) mzi →
      wp Γ Q X eExit mzi) :
    wp Γ Q X (fidBvaZeroCntExpr c.pWsort zl eExit) m0 := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hub : 2 * n + 2 < 2 ^ 64 := by omega
  dsimp only [fidBvaZeroCntExpr, bOp64, bPtr32, bIdx0_64]
  refine wp_loop_inv
    (fun (zi, ()) mzi => ∃ wsz : List (BitVec 32), zi.toNat ≤ 2 * n ∧
      wsz.length = 2 * c.max_vars ∧
      (FullMem c { st with scratch := { st.scratch with wsort := wsz } } ⋆ R) mzi)
    (fun (zi, _) _ => 2 * n - zi.toNat)
    (fun Jz hJz => by
      c0_hsteps
      exact hJz (0#64, ()) m0 ⟨st.scratch.wsort, Nat.zero_le _, hws0, hm0⟩)
    (fun Jz (zi, ()) mzi ⟨wsz, hzi_le, hwsz_l, hmzi⟩ ihz => ?_)
  c0_hsteps_nogrp
  · have hzi2 : zi.toNat + 2 ≤ 2 * n := by
      have h1 : (zi.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 ≤ zl.toNat := by assumption
      rw [show BitVec.toNat (2 : BitVec 64) = 2 from rfl, Nat.mod_eq_of_lt (by omega), hzl] at h1
      exact h1
    have hzi2_n : (zi + 2#64).toNat = zi.toNat + 2 := fid_bv64_add2_toNat hzi_le hub
    have hzi_lt : zi.toNat + 1 < wsz.length := by omega
    let wsz' := (wsz.set zi.toNat 0#32).set (zi.toNat + 1) 0#32
    refine wp_store_sep (P := FullMem c { st with scratch := { st.scratch with wsort := wsz' } })
      (R := R) ?_ ?_
    · exact store_fullMem_wsort_zero_i64 (fid_addr_add0_mul4 c.pWsort zi) hzi_lt hmzi
    · intro m1 hm1
      c0_hsteps
      exact ihz (zi + 2#64, ()) m1 (by dsimp only; rw [hzi2_n]; omega)
        ⟨wsz', by rw [hzi2_n]; exact hzi2, by simp [wsz', hwsz_l], hm1⟩
  · exact hExit wsz mzi hwsz_l hmzi

private def m7BvaLargeTopExpr (h pAr pScr pFl pTmp : Val i64) (best_k mi c_top fresh : Val i32)
    (J4 : Cont [i32, .bool]) (J6 : Cont [.bool]) : Expr Val Cont [.bool] :=
  bZext (Arg.var c_top) fun ct64 => bOp64 (.add i64) (Arg.var ct64) (Arg.imm 2) fun ct2 =>
  bLd32 pAr ct2 fun csz => bZext (Arg.var best_k) fun bk64 => bLd32 pScr bk64 fun flit =>
  Expr.let_ { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 0, ()) } fun z64 =>
  bPtr32 pTmp z64.fst fun ptmp0 => bOp32 (.xor i32) (Arg.var fresh) (Arg.imm 1) fun f1 =>
  Expr.store (Arg.var f1) (Arg.var ptmp0)
    (Expr.group (fun Jf => Blocks.cons (fun (pf : Tup Val [i32, i32]) =>
      bCmp32 .ult (Arg.var pf.snd.fst) (Arg.var csz) fun c => Expr.jnz (Arg.var c)
        (bZext (Arg.var c_top) fun ct64b => bOp64 (.add i64) (Arg.var ct64b) (Arg.imm 3) fun ct3 =>
         bZext (Arg.var pf.snd.fst) fun j64 => bOp64 (.add i64) (Arg.var ct3) (Arg.var j64)
           fun idx => bLd32 pAr idx fun l => Expr.group (fun _ => Blocks.cons
           (fun (ptk : Tup Val [i32]) => bOp32 (.add i32) (Arg.var pf.snd.fst) (Arg.imm 1)
             fun j1 => Expr.jump Jf.fst (Arg.var ptk.fst, Arg.var j1, ())) Blocks.nil) fun Jif =>
         bCmp32 .ne (Arg.var l) (Arg.var flit) fun cne => Expr.jnz (Arg.var cne)
           (bZext (Arg.var pf.fst) fun tk64 => bPtr32 pTmp tk64 fun ptmpt => Expr.store
              (Arg.var l) (Arg.var ptmpt) (bOp32 (.add i32) (Arg.var pf.fst) (Arg.imm 1) fun tk1 =>
              Expr.jump Jif.fst (Arg.var tk1, ()))) (Expr.jump Jif.fst (Arg.var pf.fst, ())))
        (Expr.call "full_alloc_cl" (as := [i64, i32, i32, .bool]) (bs := [i64])
           (Arg.var h, Arg.var pf.fst, Arg.imm 0, Arg.imm false, ()) fun pncr =>
         Expr.let_ { sig := [i64, i64], code := OpCode.cmp .eq i64,
                     args := (Arg.var pncr.fst, Arg.imm 4294967295, ()) } fun ceq =>
         Expr.jnz (Arg.var ceq.fst) (Expr.jump J4 (Arg.var mi, Arg.imm false, ()))
           (bOp64 (.add i64) (Arg.var pncr.fst) (Arg.imm 3) fun n3 =>
            bPtr32 pAr n3 fun dst_cl =>
            Expr.group (fun _ => Blocks.cons (fun (_ : Tup Val [i32]) =>
               m7BvaLargeWatchExpr h pAr pFl pTmp pf.fst pncr.fst J6) Blocks.nil)
             fun Jcp_done =>
             bOp64 (.and i64) (Arg.var pncr.fst) (Arg.imm 1) fun b =>
             Expr.let_ { sig := [i64, i64], code := OpCode.cmp .ne i64,
                         args := (Arg.var b, Arg.imm 0, ()) } fun cb =>
             Expr.jnz (Arg.var cb.fst)
               (Expr.group (fun Jcp => Blocks.cons (fun (pjc : Tup Val [i32]) =>
                  bOp32 (.add i32) (Arg.var pjc.fst) (Arg.imm 2) fun jc2 =>
                  bCmp32 .ule (Arg.var jc2) (Arg.var pf.fst) fun cjc => Expr.jnz (Arg.var cjc)
                    (bZext (Arg.var pjc.fst) fun jc64 => bPtr32 dst_cl jc64 fun dp =>
                     bZext (Arg.var pjc.fst) fun jc64b => bPtr32 pTmp jc64b fun sp =>
                     bIdx0_64 fun i0a => bOp64 (.mul i64) (Arg.var i0a) (Arg.imm 8) fun i0a8 =>
                     bOp64 (.add i64) (Arg.var dp) (Arg.var i0a8) fun dp0 =>
                     bIdx0_64 fun i0b => bOp64 (.mul i64) (Arg.var i0b) (Arg.imm 8) fun i0b8 =>
                     bOp64 (.add i64) (Arg.var sp) (Arg.var i0b8) fun sp0 =>
                     Expr.load i64 (Arg.var sp0) fun v64 =>
                     Expr.store (t := i64) (Arg.var v64) (Arg.var dp0)
                       (bOp32 (.add i32) (Arg.var pjc.fst) (Arg.imm 2) fun jc2n =>
                        Expr.jump Jcp.fst (Arg.var jc2n, ())))
                    (Expr.group (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
                       Expr.jump Jcp_done.fst (Arg.var pjc.fst, ())) Blocks.nil)
                     fun Jtl =>
                     bCmp32 .ult (Arg.var pjc.fst) (Arg.var pf.fst) fun ct => Expr.jnz (Arg.var ct)
                       (bZext (Arg.var pjc.fst) fun jt64a => bPtr32 dst_cl jt64a fun dpt =>
                        bZext (Arg.var pjc.fst) fun jt64b => bLd32 pTmp jt64b fun tv =>
                        Expr.store (t := i32) (Arg.var tv) (Arg.var dpt) (Expr.jump Jtl.fst ()))
                       (Expr.jump Jtl.fst ()))) Blocks.nil)
                fun Jcp => Expr.jump Jcp.fst (Arg.imm 0, ()))
               (Expr.group (fun Jcp => Blocks.cons (fun (pjc : Tup Val [i32]) =>
                  bCmp32 .ult (Arg.var pjc.fst) (Arg.var pf.fst) fun cjc => Expr.jnz (Arg.var cjc)
                    (bZext (Arg.var pjc.fst) fun jc64a => bPtr32 dst_cl jc64a fun dpc =>
                     bZext (Arg.var pjc.fst) fun jc64b => bLd32 pTmp jc64b fun tv =>
                     Expr.store (t := i32) (Arg.var tv) (Arg.var dpc)
                       (bOp32 (.add i32) (Arg.var pjc.fst) (Arg.imm 1) fun j1 =>
                        Expr.jump Jcp.fst (Arg.var j1, ())))
                    (Expr.jump Jcp_done.fst (Arg.var pjc.fst, ()))) Blocks.nil)
                fun Jcp => Expr.jump Jcp.fst (Arg.imm 0, ()))))) Blocks.nil)
     fun Jf => Expr.jump Jf.fst (Arg.imm 1, Arg.imm 0, ()))

private abbrev M7DefragHyp (Γ : Env) :=
  ∀ a m Q X, Full.fullWstackDefragSpec a m Q X → Γ "full_wstack_defrag" [i64] [] a m Q X
private abbrev M7AddBinHyp (Γ : Env) :=
  ∀ a m Q X, Full.fullAddBinSpec a m Q X → Γ "full_add_bin" [i64, i32, i32] [i64] a m Q X
private abbrev M7AllocClHyp (Γ : Env) :=
  ∀ a m Q X, Full.fullAllocClSpec a m Q X → Γ "full_alloc_cl" [i64, i32, i32, .bool] [i64] a m Q X
private abbrev M7WPushHyp (Γ : Env) := ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
  Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X
private abbrev M7DelBinHyp (Γ : Env) :=
  ∀ a m Q X, Full.fullDeleteBinarySpec a m Q X → Γ "full_delete_binary" [i64, i32, i32] [] a m Q X
private abbrev M7UnwatchHyp (Γ : Env) :=
  ∀ a m Q X, Full.fullUnwatchLargeSpec a m Q X → Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X

private theorem m7_bva_del_col_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    (hDelBin : M7DelBinHyp Γ) (hUnwatch : M7UnwatchHyp Γ)
    {c : FullCfg} {F0 : CNF Nat} {F_cur F_next : List (List Nat)} {s st1 : FullState}
    {R : Mem 64 → Prop} {best_k mi : Val i32} {Jm : Cont [i32]} {m1 : Mem 64}
    (hinv : FullDenseInvW c F0 F_cur s) (hbk1 : 1 ≤ best_k.toNat) (hbk32 : best_k.toNat < 32)
    (hmat : M4BvaMatrixInv c F_cur s (best_k.toNat + 1))
    (hmi_lt : mi.toNat < (s.scratch.scratch_buf[32 + best_k.toNat]?.getD 0#32).toNat)
    (hm1 : (FullMem c st1 ⋆ R) m1) (hst1 : M7BvaStOk c F0 F_next s st1)
    (hNext : ∀ st2 m2, M7BvaStOk c F0 F_next s st2 → (FullMem c st2 ⋆ R) m2 → Jm (mi + 1#32, ())
      m2) :
    wp Γ Q X (m7BvaDelColExpr c.hdr c.pArena c.pScratchBuf c.pFlags best_k mi Jm) m1 := by
  have hmx := c.hmaxv; have har_b := c.harena; have hscr_b := c.hscr
  unfold dimacsBound at hmx har_b hscr_b; have hcl := hinv.1.core_ok; have hsc := hinv.1.scratch_ok
  have hcv_le := hcl.cur_vars_le; have hsb_len := hsc.scratch_buf_len
  have hscr16448 := hmat.1; let old_cv := s.core.cur_vars
  dsimp only [m7BvaDelColExpr, m7BvaHdrExpr, m7BvaMidExpr, sSteps, sStep, sLd64, sGrp0, sGrp1,
    sGrp64_32, sGrp64_64_32,
    sGrp32b, sThen, sElse, sDummyTup, sDummyVal, i64, i32, full_bva_commit_fid_body]
  refine wp_join_group
    (fun (_ : Tup Val [i32, i32]) m2 => ∃ st2 : FullState,
      (FullMem c st2 ⋆ R) m2 ∧ M7BvaStOk c F0 F_next s st2)
    (fun _ _ m2 ⟨st2, hm2, hst2⟩ => by c0_hsteps; exact hNext st2 m2 hst2 hm2)
    (fun Jdel hJdel => ?_)
  refine wp_loop_inv
    (fun (idx, sv, ()) msv => ∃ stv : FullState, sv.toNat ≤ best_k.toNat ∧
      idx.toNat < (s.scratch.scratch_buf[32 + sv.toNat]?.getD 0#32).toNat ∧
      M7BvaStOk c F0 F_next s stv ∧ (FullMem c stv ⋆ R) msv)
    (fun (_, sv, _) _ => sv.toNat) (fun Jd hJd => by
      c0_hsteps; exact hJd (mi, best_k, ()) m1 ⟨st1, Nat.le_refl _, hmi_lt, hst1, hm1⟩)
    (fun Jd (idx, sv, ()) msv ⟨stv, hsv_le, hidx_lt, hstv, hmsv⟩ ihd => ?_)
  obtain ⟨hinvv, hcvv, hfuelv, hsbv, htmv, htrv, hmonov⟩ := hstv
  have hclv := hinvv.1.core_ok; have hscv := hinvv.1.scratch_ok
  have hsv_row := hmat.2.2.2 sv.toNat (by omega)
  obtain ⟨hfsv_lt, hqsv_lo, hqsv_hi, hsv_entries⟩ := hsv_row
  obtain ⟨resv, _, _, hcs_ok, _, hpar_ok⟩ := hsv_entries idx.toNat hidx_lt
  have hcs_idx : (64 + sv * 256 + idx).toNat = 64 + sv.toNat * 256 + idx.toNat := by
    change (64#32 + sv * 256#32 + idx).toNat = _; c0_bound
  have hcs_sb : (BitVec.setWidth 64 (64 + sv * 256 + idx)).toNat < stv.scratch.scratch_buf.length
    := by rw [bv64_setWidth_32, hcs_idx, hscv.scratch_buf_len]; omega
  have hsv_sb : (BitVec.setWidth 64 sv).toNat < stv.scratch.scratch_buf.length := by
    rw [bv64_setWidth_32, hscv.scratch_buf_len]; omega
  let cs := s.scratch.scratch_buf[64 + sv.toNat * 256 + idx.toNat]'(by omega)
  have hcs_eq : stv.scratch.scratch_buf[(BitVec.setWidth 64 (64 + sv * 256 + idx)).toNat]'hcs_sb =
    cs := by dsimp only [cs]; simp only [hsbv, bv64_setWidth_32, hcs_idx]
  have hcs_mod_n : (64 + sv.toNat * 256 + idx.toNat) % 2 ^ 32 = 64 + sv.toNat * 256 + idx.toNat :=
    Nat.mod_eq_of_lt (by omega)
  have hcs_mod : stv.scratch.scratch_buf[(BitVec.toNat (64 : BitVec 32) +
      sv.toNat * BitVec.toNat (256 : BitVec 32) + idx.toNat) % 2 ^ 32]'(by
      rw [show BitVec.toNat (64 : BitVec 32) = 64 from rfl,
        show BitVec.toNat (256 : BitVec 32) = 256 from rfl, hcs_mod_n, hscv.scratch_buf_len];
          omega) = cs := by
    dsimp only [cs]; simp only [hsbv, show BitVec.toNat (64 : BitVec 32) = 64 from rfl,
      show BitVec.toNat (256 : BitVec 32) = 256 from rfl, hcs_mod_n]
  have hcs_getD : s.scratch.scratch_buf[64 + sv.toNat * 256 + idx.toNat]?.getD 0#32 = cs := by
    dsimp only [cs]; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  rw [hcs_getD] at hcs_ok; c0_hsteps_nogrp
  · refine wp_join_state0 (α := FullState)
      (fun stc mc => (FullMem c stc ⋆ R) mc ∧ M7BvaStOk c F0 F_next s stc)
      (fun _ stc mc ⟨hmc, hstc⟩ => ?_) (fun Jcs hJcs => ?_)
    · have hscc := hstc.1.1.scratch_ok; c0_hsteps
      · exact hJdel (idx, sv, ()) mc ⟨stc, hmc, hstc⟩
      · have hsv_pos : 0 < sv.toNat := by c0_bound
        have hsv1 : (sv - 1#32).toNat = sv.toNat - 1 := by c0_bound
        have hpar_idx : (8256 + sv * 256 + idx).toNat = 8256 + sv.toNat * 256 + idx.toNat := by
          change (8256#32 + sv * 256#32 + idx).toNat = _; c0_bound
        have hpar_sb : (BitVec.setWidth 64 (8256 + sv * 256 + idx)).toNat <
            stc.scratch.scratch_buf.length := by
          rw [bv64_setWidth_32, hpar_idx, hscc.scratch_buf_len]; omega
        have hpi_lt := (hpar_ok hsv_pos).1; c0_hsteps
        refine ihd (_, sv - 1#32, ()) mc (by dsimp only; rw [hsv1]; omega)
          ⟨stc, by rw [hsv1]; omega, ?_, hstc, hmc⟩
        rw [hsv1]; have h1 : stc.scratch.scratch_buf[(BitVec.setWidth 64
            (8256 + sv * 256 + idx)).toNat]'hpar_sb =
            s.scratch.scratch_buf[8256 + sv.toNat * 256 + idx.toNat]?.getD 0#32 := by
          have heq : stc.scratch.scratch_buf[(BitVec.setWidth 64
              (8256 + sv * 256 + idx)).toNat]? =
              s.scratch.scratch_buf[8256 + sv.toNat * 256 + idx.toNat]? := by
            rw [hstc.2.2.2.1, bv64_setWidth_32, hpar_idx]
          rw [← heq, List.getElem?_eq_getElem hpar_sb, Option.getD_some]
        rw [h1]; exact hpi_lt
    · c0_hsteps
      · have hbin_cs : (cs &&& 0x80000000#32) ≠ 0#32 := by
          simpa only [← hcs_mod] using (by assumption : _)
        unfold M4BvaRowEntryOk at hcs_ok; rw [ite_eq_left hbin_cs] at hcs_ok
        have hq_lt : (cs &&& 0x7FFFFFFF#32).toNat < 2 * old_cv := hcs_ok.1; c0_call hDelBin
        refine ⟨c, stv, R, rfl, hinvv.1, hinvv.2.1.watches.layout, hmsv,
          fun wvec' wstk' wu' nb' md1 hlen_d _ hwat_d hmd1 => ?_⟩
        have hinv_d := fullDenseInvW_of_delBin hinvv hlen_d (hwat_d F_next hinvv.2.1.watches)
        have hq_shr : (BitVec.setWidth 64 ((stv.scratch.scratch_buf[(BitVec.setWidth 64
            (64 + sv * 256 + idx)).toNat]'hcs_sb &&& 0x7FFFFFFF#32) >>> (1 : BitVec 32))).toNat <
            stv.core.flags.length := by
          rw [bv64_setWidth_32, hcs_eq, bv32_lshr1_bv, hclv.flags_len]; omega
        have hq_shr_n : (BitVec.setWidth 64 ((stv.scratch.scratch_buf[(BitVec.setWidth 64
            (64 + sv * 256 + idx)).toNat]'hcs_sb &&& 0x7FFFFFFF#32) >>> (1 : Nat))).toNat <
            stv.core.flags.length := by
          rw [bv64_setWidth_32, hcs_eq, bv32_lshr1_nat, hclv.flags_len]; omega
        c0_hsteps; all_goals
          exact hJcs _ m ⟨hm, fullDenseInvW_set_flags hinv_d (by simp [hlen_d.core_ok.flags_len]),
            hcvv, hfuelv, hsbv, htmv, htrv, hmonov⟩
      · have hbin_cs : (cs &&& 0x80000000#32) = 0#32 := by
          simpa only [← hcs_mod] using (by assumption : _)
        unfold M4BvaRowEntryOk at hcs_ok; rw [ite_eq_right (fun h' => h' hbin_cs)] at hcs_ok
        obtain ⟨hcs_ref0, hcs_ng0, hcs_sz3, hcs_sz256, _, _, _⟩ := hcs_ok
        obtain ⟨hcs_refv, hcs_szv, hcs_litsv⟩ := hmonov cs.toNat hcs_ref0
        have hcs_wfv := hinvv.2.1.arena.refs_wf cs.toNat hcs_refv
        have hcs2_n : (BitVec.setWidth 64 cs + 2).toNat = cs.toNat + 2 := by
          change (BitVec.setWidth 64 cs + 2#64).toNat = _; c0_bound
        have hcs_b2_sb : (BitVec.setWidth 64 (stv.scratch.scratch_buf[(BitVec.setWidth 64
            (64 + sv * 256 + idx)).toNat]'hcs_sb) + 2).toNat < stv.core.arena.length := by
          rw [hcs_eq, hcs2_n]; have := hclv.arena_len_le; have := hclv.arena_len_arr; omega
        have hcsz_eq : (stv.core.arena[cs.toNat + 2]'(by
            have := hclv.arena_len_le; have := hclv.arena_len_arr; omega)).toNat =
            fullArenaClauseSizeCore s.core cs.toNat := by
          rw [← hcs_szv]; unfold fullArenaClauseSizeCore; rw [List.getElem?_eq_getElem (by
            have := hclv.arena_len_le; have := hclv.arena_len_arr; omega), Option.getD_some]
        let csz_bv := stv.core.arena[cs.toNat + 2]'(by
          have := hclv.arena_len_le; have := hclv.arena_len_arr; omega)
        have hcsz_s : csz_bv.toNat = fullArenaClauseSizeCore s.core cs.toNat := hcsz_eq
        c0_hsteps_nogrp; refine wp_loop_inv
          (fun (k, ()) mk => ∃ stk : FullState, k.toNat ≤ csz_bv.toNat ∧
            stk.core.arena = stv.core.arena ∧ stk.core.arena_len = stv.core.arena_len ∧
            M7BvaStOk c F0 F_next s stk ∧ (FullMem c stk ⋆ R) mk)
          (fun (k, _) _ => csz_bv.toNat - k.toNat) (fun Jk hJk => by
            c0_hsteps; exact hJk (0#32, ()) msv
              ⟨stv, Nat.zero_le _, rfl, rfl,
                ⟨hinvv, hcvv, hfuelv, hsbv, htmv, htrv, hmonov⟩, hmsv⟩)
          (fun Jk (k, ()) mk ⟨stk, hk_le, hark, halk, hstk, hmk⟩ ihk => ?_)
        obtain ⟨hinvk, hcvk, hfuelk, hsbk, htmk, htrk, hmonok⟩ := hstk
        have hclk := hinvk.1.core_ok; c0_hsteps
        · have hcs2_mod : (cs.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 = cs.toNat + 2 := by
            rw [show BitVec.toNat (2 : BitVec 64) = 2 from rfl]; omega
          have hk_lt : k.toNat < csz_bv.toNat := by
            dsimp only [csz_bv]
            have h1 : k.toNat < (stv.core.arena[(cs.toNat + BitVec.toNat (2 : BitVec 64)) %
                2 ^ 64]'(by
                  rw [hcs2_mod]; have :=
                    hclv.arena_len_le; have := hclv.arena_len_arr; omega)).toNat :=
              by simpa only [← hcs_mod] using (by assumption : _)
            simpa only [hcs2_mod] using h1
          have hk1 : (k + 1#32).toNat = k.toNat + 1 := by c0_bound
          have hcsk_n : (BitVec.setWidth 64 cs + 3 + BitVec.setWidth 64 k).toNat =
              cs.toNat + 3 + k.toNat := by
            change (BitVec.setWidth 64 cs + 3#64 + BitVec.setWidth 64 k).toNat = _; c0_bound
          have hdl_ar : cs.toNat + 3 + k.toNat < stk.core.arena.length := by
            have := hclv.arena_len_le; have := hclv.arena_len_arr; rw [hark]; omega
          have hdl_ar_sb : (BitVec.setWidth 64 (stv.scratch.scratch_buf[(BitVec.setWidth 64
              (64 + sv * 256 + idx)).toNat]'hcs_sb) + 3 + BitVec.setWidth 64 k).toNat <
              stk.core.arena.length := by rw [hcs_eq, hcsk_n]; exact hdl_ar
          have hdl_mem : (stk.core.arena[cs.toNat + 3 + k.toNat]'hdl_ar).toNat ∈
              fullArenaClauseLitsCore s.core cs.toNat := by
            rw [← hcs_litsv]
            have h1 := FullBvaFwdHelpers.fullArenaClauseLitsCore_getElem (k := stv.core)
              (r := cs.toNat) (j := k.toNat) (by rw [hcs_szv]; omega)
              (by rw [← hark]; exact hdl_ar)
            simpa only [hark] using List.mem_of_getElem? h1
          have hdl_lt : (stk.core.arena[cs.toNat + 3 + k.toNat]'hdl_ar).toNat < 2 * old_cv :=
            hinv.2.1.arena.lits_lt cs.toNat hcs_ref0 hcs_ng0 _ hdl_mem
          c0_hsteps; c0_call hUnwatch
          refine ⟨c, stk, R, rfl, hinvk.1, hinvk.2.1.watches.layout, hmk,
            fun wvec' wstk' wu' mu hlen_u _ hwat_u hmu => ?_⟩
          have hinv_u :=
            fullDenseInvW_of_unwatchLarge hinvk hlen_u (hwat_u F_next hinvk.2.1.watches)
          have hdl_shr : (BitVec.setWidth 64 ((stk.core.arena[(BitVec.setWidth 64
              (stv.scratch.scratch_buf[(BitVec.setWidth 64 (64 + sv * 256 + idx)).toNat]'hcs_sb) +
              3 + BitVec.setWidth 64 k).toNat]'hdl_ar_sb) >>> (1 : BitVec 32))).toNat <
              stk.core.flags.length := by
            rw [bv64_setWidth_32, hclk.flags_len]; simp only [hcs_eq, hcsk_n, bv32_lshr1_bv]; omega
          have hdl_shr_n : (BitVec.setWidth 64 ((stk.core.arena[(BitVec.setWidth 64
              (stv.scratch.scratch_buf[(BitVec.setWidth 64 (64 + sv * 256 + idx)).toNat]'hcs_sb) +
              3 + BitVec.setWidth 64 k).toNat]'hdl_ar_sb) >>> (1 : Nat))).toNat <
              stk.core.flags.length := by
            rw [bv64_setWidth_32, hclk.flags_len]; simp only [hcs_eq, hcsk_n, bv32_lshr1_nat]; omega
          c0_hsteps; all_goals
            refine ihk (k + 1#32, ()) m (by dsimp only; rw [hk1]; omega)
              ⟨_, by rw [hk1]; omega, (by exact hark), (by exact halk), ?_, hm⟩
          all_goals
            exact ⟨fullDenseInvW_set_flags hinv_u (by simp [hlen_u.core_ok.flags_len]),
              hcvk, hfuelk, hsbk, htmk, htrk, hmonok⟩
        · have hcs_refk : cs.toNat ∈ fullArenaClauseRefsCore stk.core :=
            (hmonok cs.toNat hcs_ref0).1
          have hcs_lt_k : cs.toNat < stk.core.arena.length := by
            have := hclv.arena_len_le; have := hclv.arena_len_arr; rw [hark]; omega
          have hcs_lt_sb : (BitVec.setWidth 64 (stv.scratch.scratch_buf[(BitVec.setWidth 64
              (64 + sv * 256 + idx)).toNat]'hcs_sb)).toNat < stk.core.arena.length := by
            rw [hcs_eq, bv64_setWidth_32]; exact hcs_lt_k
          c0_hsteps; have ⟨hinv_g, hmono_g⟩ := fullDenseInvW_of_markGarb hinvk hcs_refk
            (stk.core.arena_garbage + 3#64 + BitVec.setWidth 64
              (stv.core.arena[(BitVec.setWidth 64 cs + 2).toNat]'(by
                rw [hcs2_n]; have := hclv.arena_len_le; have := hclv.arena_len_arr; omega)))
          have hm_g : (FullMem c { stk with
              core := { stk.core with
                arena := stk.core.arena.set cs.toNat
                  (fullArenaHdrCore stk.core cs.toNat ||| 0x00080000#32)
                arena_garbage := stk.core.arena_garbage + 3#64 + BitVec.setWidth 64
                  (stv.core.arena[(BitVec.setWidth 64 cs + 2).toNat]'(by
                    rw [hcs2_n]; have := hclv.arena_len_le; have := hclv.arena_len_arr; omega)) } }
              ⋆ R) m := by
            have hhdr : fullArenaHdrCore stk.core cs.toNat = stk.core.arena[cs.toNat]'hcs_lt_k := by
              unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem hcs_lt_k, Option.getD_some]
            rw [hhdr]; simp only [hcs_eq] at hm; simp only [bv64_setWidth_32] at hm; exact hm
          exact hJcs _ m ⟨hm_g, hinv_g, hcvk, hfuelk, hsbk, htmk, htrk,
            arenaMono_trans hmonok hmono_g⟩
  · cases (by assumption : true = false)

private theorem m7_bva_phase2_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    (hDelBin : M7DelBinHyp Γ) (hUnwatch : M7UnwatchHyp Γ)
    {c : FullCfg} {F0 : CNF Nat} {F_cur F_next : List (List Nat)} {s st0 : FullState}
    {R : Mem 64 → Prop} {best_k mn_bv : Val i32} {m0 : Mem 64} (hinv : FullDenseInvW c F0 F_cur s)
    (hbk1 : 1 ≤ best_k.toNat) (hbk32 : best_k.toNat < 32)
    (hmat : M4BvaMatrixInv c F_cur s (best_k.toNat + 1))
    (hmn_getD : (s.scratch.scratch_buf[32 + best_k.toNat]?.getD 0#32).toNat = mn_bv.toNat)
    (hst0 : M7BvaStOk c F0 F_next s st0) (hm0 : (FullMem c st0 ⋆ R) m0)
    (hQ : ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      FullDenseInv c F0 s' → s.core.cur_vars ≤ s'.core.cur_vars → s'.core.fuel = s.core.fuel →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach → (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    wp Γ Q X (m7BvaPhase2Expr c.hdr c.pArena c.pScratchBuf c.pWsort c.pFlags best_k mn_bv) m0 := by
  have hmx := c.hmaxv; have hscr_b := c.hscr; unfold dimacsBound at hmx hscr_b
  let old_cv := s.core.cur_vars
  have hmn_hi : mn_bv.toNat ≤ 256 := by have := (hmat.2.2.2 best_k.toNat (by omega)).2.2.1; omega
  dsimp only [m7BvaPhase2Expr, m7BvaHdrExpr, m7BvaMidExpr, sSteps, sStep, sLd64, sLd32, sGrp0,
    sGrp64_32, sGrp64_64_32,
    sGrp32b, sThen, sElse, sDummyTup, sDummyVal, i64, i32, full_bva_commit_fid_body]
  refine wp_loop_inv
    (fun (mi, ()) mm => ∃ stm : FullState, mi.toNat ≤ mn_bv.toNat ∧
      M7BvaStOk c F0 F_next s stm ∧ (FullMem c stm ⋆ R) mm)
    (fun (mi, _) _ => mn_bv.toNat - mi.toNat)
    (fun Jm hJm => by c0_hsteps; exact hJm (0#32, ()) m0 ⟨st0, Nat.zero_le _, hst0, hm0⟩)
    (fun Jm (mi, ()) mm ⟨stm, hmi_le, hstm, hmm⟩ ihm => ?_)
  c0_hsteps_nogrp
  · have hmi_lt : mi.toNat < mn_bv.toNat := by c0_bound
    have hmi1 : (mi + 1#32).toNat = mi.toNat + 1 := by c0_bound
    have hdel := m7_bva_del_col_wp (Γ := Γ) (Q := Q) (X := X) hDelBin hUnwatch
      (F_next := F_next) (Jm := Jm) hinv hbk1 hbk32 hmat (by rw [hmn_getD]; exact hmi_lt)
      hmm hstm (fun st2 m2 hst2 hm2 =>
        ihm (mi + 1#32, ()) m2 (by dsimp only; rw [hmi1]; omega)
          ⟨st2, by rw [hmi1]; omega, hst2, hm2⟩)
    dsimp only [m7BvaDelColExpr, m7BvaHdrExpr, m7BvaMidExpr, sSteps, sStep, sLd64, sGrp0, sGrp1,
      sGrp64_32, sGrp64_64_32,
      sGrp32b, sThen, sElse, sDummyTup, sDummyVal, i64, i32, full_bva_commit_fid_body] at hdel
    exact hdel
  · obtain ⟨hinvm, hcvm, hfuelm, _, htmm, htrm, _⟩ := hstm
    have hclm := hinvm.1.core_ok; have hscm := hinvm.1.scratch_ok; have hcv_le := hclm.cur_vars_le
    have h2cv : (BitVec.ofNat 64 stm.core.cur_vars <<< (1 : Nat)).toNat = 2 * (old_cv + 1) := by
      rw [hcvm]; simp only [bv_c0]; omega
    exact fid_bva_zero_cnt_wp (n := old_cv + 1) (by omega) h2cv hscm.wsort_len hmm
      (fun wsz mzi hwsz_l hmzi => by
        c0_hsteps
        have hinv_fin := fullDenseInv_with_core_aux (tc' := stm.core.tmp_cnt)
          (tl' := stm.core.tmp_len)
          (sc' := { stm.scratch with wsort := wsz, bva_cnt := stm.scratch.bva_cnt + 1#64 })
          hinvm hclm.repr_len hclm.min_clr_len_arr hclm.tmp_len_arr hclm.flags_len
          hclm.tmp_len_le { hscm with wsort_len := hwsz_l } rfl rfl
        exact hQ true _ m hinv_fin.toDense (by dsimp only; omega) hfuelm htmm htrm hm)

private theorem m7_bva_large_watch_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    (hWPush : M7WPushHyp Γ) (hUnwatch : M7UnwatchHyp Γ)
    {c : FullCfg} {F0 : CNF Nat} {F_next : List (List Nat)} {s stm : FullState}
    {R : Mem 64 → Prop} {tk : Val i32} {J6 : Cont [.bool]}
    {tmpj arj : List (BitVec 32)} {mjc : Mem 64} (hstm : M7BvaStOk c F0 F_next s stm)
    (htmpj_l : tmpj.length = c.max_vars)
    (htk_ge3 : 3 ≤ tk.toNat) (htk_le : tk.toNat ≤ 256) (htk_le_mv : tk.toNat ≤ c.max_vars)
    (hncr_cap : stm.core.arena_len + 3 + tk.toNat ≤ c.arena_cap)
    (hhold_j : ∀ i < stm.core.arena_len, arj[i]? = stm.core.arena[i]?)
    (hns_cp : (arj[stm.core.arena_len]?.getD 0#32 &&& 0x00800000#32) = 0#32)
    (hsz_cp : (arj[stm.core.arena_len + 2]?.getD 0#32).toNat = tk.toNat)
    (hnew_lt : ∀ l ∈ fullArenaClauseLitsCore { stm.core with arena := arj } stm.core.arena_len,
      l < 2 * stm.core.cur_vars)
    (hnew_nd : ((fullArenaClauseLitsCore { stm.core with arena := arj }
      stm.core.arena_len).map (· / 2)).Nodup)
    (hnew_ent : (cnfOfClauses F_next).EntailsClause
      (cnfClause (fullArenaClauseLitsCore { stm.core with arena := arj } stm.core.arena_len)))
    (htmp_lt : ∀ t (ht : t < tk.toNat),
      (tmpj[t]'(by rw [htmpj_l]; omega)).toNat < 2 * (s.core.cur_vars + 1))
    (hlen_cp : ({ stm with core := { stm.core with
        tmp := tmpj, arena := arj, arena_len := stm.core.arena_len + 3 + tk.toNat } } :
      FullState).LengthsOk c)
    (hrefs_cp : fullArenaClauseRefsCore
        { stm.core with tmp := tmpj, arena := arj, arena_len := stm.core.arena_len + 3 + tk.toNat
          } =
      fullArenaClauseRefsCore stm.core ++ [stm.core.arena_len])
    (hwat_cp : ModeWatchesInv F_next
      { stm.core with tmp := tmpj, arena := arj, arena_len := stm.core.arena_len + 3 + tk.toNat })
    (hmjc : (FullMem c { stm with core := { stm.core with
      tmp := tmpj, arena := arj, arena_len := stm.core.arena_len + 3 + tk.toNat } } ⋆ R) mjc)
    (hDone : ∀ (ok' : Bool) st1 m1, (FullMem c st1 ⋆ R) m1 → M7BvaStOk c F0 F_next s st1 →
      J6 (ok', ()) m1) :
    wp Γ Q X (m7BvaLargeWatchExpr c.hdr c.pArena c.pFlags c.pTmp tk
      (BitVec.ofNat 64 stm.core.arena_len) J6) mjc := by
  obtain ⟨hinvm, hcvm, hfuelm, hsbm, htmm, htrm, hmono⟩ := hstm
  have hmx := c.hmaxv; have har_b := c.harena; unfold dimacsBound at hmx har_b
  have hclm := hinvm.1.core_ok; let old_cv := s.core.cur_vars; let ncr0 := stm.core.arena_len
  let st_tmp : FullState := { stm with core := { stm.core with tmp := tmpj } }
  have hinv_tmp : FullDenseInvW c F0 F_next st_tmp := fullDenseInvW_set_tmp hinvm htmpj_l
  let st_cp : FullState :=
    { st_tmp with core := { st_tmp.core with arena := arj, arena_len := ncr0 + 3 + tk.toNat } }
  have hncr_nat : (BitVec.ofNat 64 ncr0).toNat = ncr0 := by have := hclm.arena_len_le; c0_bound
  have hcv_le := hclm.cur_vars_le
  dsimp only [m7BvaLargeWatchExpr, bZext, bOp64, bOp32, bCmp32, bPtr32, bLd32]
  refine wp_join_group (ts := [.bool, i32])
    (fun (ok', _, ()) mw => ∃ stw : FullState, (FullMem c stw ⋆ R) mw ∧ M7BvaStOk c F0 F_next s stw)
    (fun _ (ok', _, ()) mw ⟨stw, hmw, hstw⟩ => by
      refine wp_join_state0 (α := FullState)
        (fun stf mf => (FullMem c stf ⋆ R) mf ∧ M7BvaStOk c F0 F_next s stf)
        (fun _ stf mf ⟨hmf, hstf⟩ => by m7_hsteps_to_jump; exact hDone ok' stf mf hmf hstf)
        (fun Jni hJni => by
          obtain ⟨hinvw, hcvw, hfuelw, hsbw, htmw, htrw, hmonow⟩ := hstw; c0_hsplit
          · m7_hsteps_to_jump
            exact hJni _ m ⟨hm, fullDenseInvW_with_num_irred hinvw _, hcvw, hfuelw,
              hsbw, htmw, htrw, hmonow⟩
          · m7_hsteps_to_jump
            exact hJni _ mw ⟨hmw, hinvw, hcvw, hfuelw, hsbw, htmw, htrw, hmonow⟩))
    (fun Jw_exit hJw_exit => ?_)
  refine wp_loop_inv
    (fun (jw, ()) mjw => ∃ wvecw wstkw flw wsortw wlenw wuw, jw.toNat ≤ tk.toNat ∧
      let sw : FullState :=
        { st_cp with core := { st_cp.core with wvec := wvecw, wstk := wstkw, wlen := wlenw,
                                               wusable := wuw, flags := flw }
                     scratch := { st_cp.scratch with wsort := wsortw } }
      sw.LengthsOk c ∧ ModeWatchesInv F_next sw.core ∧ (FullMem c sw ⋆ R) mjw)
    (fun (jw, _) _ => tk.toNat - jw.toNat) (fun Jw hJw => by
      m7_hsteps_to_jump; exact hJw (0#32, ()) mjc
        ⟨st_cp.core.wvec, st_cp.core.wstk, st_cp.core.flags,
         st_cp.scratch.wsort, st_cp.core.wlen, st_cp.core.wusable, Nat.zero_le _,
         hlen_cp, hwat_cp, hmjc⟩)
    (fun Jw (jw, ()) mjw ⟨wvecw, wstkw, flw, wsortw, wlenw, wuw, hjw_le, hlenw,
        hwatw, hmjw⟩ ihw => ?_)
  let sw : FullState :=
    { st_cp with core := { st_cp.core with wvec := wvecw, wstk := wstkw, wlen := wlenw,
                                           wusable := wuw, flags := flw }
                 scratch := { st_cp.scratch with wsort := wsortw } }
  c0_hsplit
  · have hjw_lt : jw.toNat < tk.toNat := by c0_bound
    have hjw1 : (jw + 1#32).toNat = jw.toNat + 1 := by c0_bound
    have hjw_tmp : jw.toNat < tmpj.length := by omega
    have hjw_tmp_sw : (BitVec.setWidth 64 jw).toNat < sw.core.tmp.length := by
      rw [bv64_setWidth_32]; exact hjw_tmp
    have htk_mask : (tk &&& (2147483647 : BitVec 32)) = tk := bv32_lit_mask_eq (by omega)
    have htk_ne : (tk &&& (2147483647 : BitVec 32)) ≠ 0xFFFFFFFF#32 := by
      rw [htk_mask]; intro h; have := congrArg BitVec.toNat h
      have : (0xFFFFFFFF#32 : BitVec 32).toNat = 2 ^ 32 - 1 := rfl; omega
    have hncr32_nat : (BitVec.setWidth 32 (BitVec.ofNat 64 ncr0)).toNat = ncr0 := by
      have := hclm.arena_len_le; c0_bound
    have hncr32_ne : BitVec.setWidth 32 (BitVec.ofNat 64 ncr0) ≠ 0xFFFFFFFF#32 := by
      intro h; have := congrArg BitVec.toNat h; rw [hncr32_nat] at this
      have := hclm.arena_len_le; have : (0xFFFFFFFF#32 : BitVec 32).toNat = 2 ^ 32 - 1 := rfl; omega
    c0_hsteps; c0_call hWPush
    refine ⟨c, sw, R, rfl, hlenw, hwatw.layout, (fun h => absurd h (by decide)),
      (fun _ => ⟨htk_ne, hncr32_ne⟩), hmjw,
      fun okw wvec' wstk' wlen' wu' wsort' mw' hlenw' hlayw' hothw hokt hokf hmw' => ?_⟩
    have hwatw' : ModeWatchesInv F_next
        { sw.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' } := by
      refine fullWatchPush_preserves_modeWatchesInv (cnt := 2#32) hwatw hlayw'
        rfl rfl (fun _ hr => hr) (fun h => absurd h (by decide)) ?_ hothw hokt
        (fun hf => (hokf hf).1)
      intro _; have htk_nb : (tk &&& 0x80000000#32) = 0#32 := bv32_bin_flag_zero_of_lt (by omega)
      refine ⟨by rw [htk_mask]; exact htk_nb, fun _ => by rw [htk_mask]; omega,
        by rw [hncr32_nat]; have := hclm.arena_len_le; omega, ?_⟩
      change (BitVec.setWidth 32 (BitVec.ofNat 64 ncr0)).toNat ∈ fullArenaClauseRefsCore st_cp.core
      rw [hncr32_nat, hrefs_cp]; exact List.mem_append_right _ (by dsimp only [ncr0]; simp)
    have htv_shr : (BitVec.setWidth 64 ((tmpj[(BitVec.setWidth 64 jw).toNat]'(by
        rw [bv64_setWidth_32]; exact hjw_tmp)) >>> (1 : BitVec 32))).toNat < flw.length := by
      rw [bv64_setWidth_32, bv32_lshr1_bv, hlenw'.core_ok.flags_len]
      simp only [bv64_setWidth_32]; have := htmp_lt jw.toNat hjw_lt; omega
    have htv_shr_n : (BitVec.setWidth 64 ((tmpj[(BitVec.setWidth 64 jw).toNat]'(by
        rw [bv64_setWidth_32]; exact hjw_tmp)) >>> (1 : Nat))).toNat < flw.length := by
      rw [bv64_setWidth_32, bv32_lshr1_nat, hlenw'.core_ok.flags_len]
      simp only [bv64_setWidth_32]; have := htmp_lt jw.toNat hjw_lt; omega
    c0_hsteps_nogrp
    · c0_hsteps_nogrp
      refine wp_join_group (ts := [i32]) (fun (_ : Tup Val [i32]) mf => mf = mw')
        (fun _ _ mf hmf => by
          subst mf; m7_hsteps_to_jump
          refine ihw (jw + 1#32, ()) m (by dsimp only; rw [hjw1]; omega)
            ⟨wvec', wstk', _, wsort', wlen', wu', by rw [hjw1]; omega, ?_, ?_, hm⟩
          · exact ⟨{ hlenw'.core_ok with flags_len := by simp [hlenw'.core_ok.flags_len] },
              hlenw'.scratch_ok⟩
          · exact hwatw'.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr))
        (fun Jt hJt => by
          c0_hsplit
          · m7_hsteps_to_jump; exact hJt (64#32, ()) mw' rfl
          · m7_hsteps_to_jump; exact hJt (32#32, ()) mw' rfl)
    · let sw_fail : FullState :=
        { sw with core := { sw.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable :=
          wu' }
                  scratch := { sw.scratch with wsort := wsort' } }
      refine wp_loop_inv
        (fun (uk, ()) muk => ∃ wvecu wstku wuu, uk.toNat ≤ jw.toNat ∧ let su : FullState :=
            { sw_fail with core := { sw_fail.core with wvec := wvecu, wstk := wstku, wusable :=
              wuu } }
          su.LengthsOk c ∧ ModeWatchesInv F_next su.core ∧ (FullMem c su ⋆ R) muk)
        (fun (uk, _) _ => jw.toNat - uk.toNat) (fun Juk hJuk => by
          m7_hsteps_to_jump
          exact hJuk (0#32, ()) mw' ⟨wvec', wstk', wu', Nat.zero_le _, hlenw', hwatw', hmw'⟩)
        (fun Juk (uk, ()) muk ⟨wvecu, wstku, wuu, huk_le, hlenu, hwatu, hmuk⟩ ihuk => ?_)
      let su : FullState :=
        { sw_fail with core := { sw_fail.core with wvec := wvecu, wstk := wstku, wusable := wuu } }
      c0_hsplit
      · have huk_lt : uk.toNat < jw.toNat := by c0_bound
        have huk1 : (uk + 1#32).toNat = uk.toNat + 1 := by c0_bound
        have huk_tmp : (BitVec.setWidth 64 uk).toNat < su.core.tmp.length := by
          rw [bv64_setWidth_32, hlenu.core_ok.tmp_len_arr]; omega
        c0_hsteps; c0_call hUnwatch; refine ⟨c, su, R, rfl, hlenu, hwatu.layout, hmuk,
          fun wvecu' wstku' wuu' mu' hlenu' _ hwatu' hmu' => ?_⟩
        m7_hsteps_to_jump; exact ihuk (uk + 1#32, ()) mu' (by dsimp only; rw [huk1]; omega)
          ⟨wvecu', wstku', wuu', by rw [huk1]; omega, hlenu', hwatu' F_next hwatu, hmu'⟩
      · have hncr_ar_u : (BitVec.ofNat 64 ncr0).toNat < su.core.arena.length := by
          rw [hncr_nat, hlenu.core_ok.arena_len_arr]; omega
        m7_hsteps_to_jump; have ⟨hinv_app, hmono_app⟩ := fullDenseInvW_of_append_clause hinv_tmp
          (by omega) hlenu hhold_j hns_cp hsz_cp hnew_lt hnew_nd hnew_ent hwatu
        have hncr_ref : ncr0 ∈ fullArenaClauseRefsCore su.core := by
          change ncr0 ∈ fullArenaClauseRefsCore st_cp.core
          rw [hrefs_cp]; exact List.mem_append_right _ (by dsimp only [ncr0]; simp)
        have ⟨hinv_mg, hmono_mg⟩ := fullDenseInvW_of_markGarb hinv_app hncr_ref
          (su.core.arena_garbage + 3#64 + BitVec.setWidth 64 tk)
        have hm_mg : (FullMem c { su with core := { su.core with
            arena := su.core.arena.set ncr0 (fullArenaHdrCore su.core ncr0 ||| 0x00080000#32)
            arena_garbage := su.core.arena_garbage + 3#64 + BitVec.setWidth 64 tk } } ⋆ R) m := by
          have hhdr : fullArenaHdrCore su.core ncr0 =
              su.core.arena[ncr0]'(by rw [hlenu.core_ok.arena_len_arr]; omega) := by
            unfold fullArenaHdrCore
            rw [List.getElem?_eq_getElem (by rw [hlenu.core_ok.arena_len_arr]; omega),
              Option.getD_some]
          rw [hhdr]; dsimp only [ncr0] at hncr_nat ⊢
          simp only [hncr_nat, show (524288 : BitVec 32) = 0x00080000#32 from rfl,
            show (3 : BitVec 64) = 3#64 from rfl] at hm ⊢
          exact hm
        exact hJw_exit (false, jw, ()) m ⟨_, hm_mg, hinv_mg, hcvm, hfuelm, hsbm, htmm, htrm,
          arenaMono_trans hmono (arenaMono_trans hmono_app hmono_mg)⟩
  · m7_hsteps_to_jump
    have ⟨hinv_app, hmono_app⟩ := fullDenseInvW_of_append_clause hinv_tmp
      (by omega) hlenw hhold_j hns_cp hsz_cp hnew_lt hnew_nd hnew_ent hwatw
    exact hJw_exit (true, jw, ()) mjw ⟨sw, hmjw, hinv_app, hcvm, hfuelm, hsbm, htmm, htrm,
      arenaMono_trans hmono hmono_app⟩

private theorem m7_bva_large_top_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    (hAllocCl : M7AllocClHyp Γ) (hWPush : M7WPushHyp Γ) (hUnwatch : M7UnwatchHyp Γ)
    {c : FullCfg} {F0 : CNF Nat} {F_cur F_next : List (List Nat)} {s stm : FullState}
    {R : Mem 64 → Prop} {best_k mi c_top fresh : Val i32}
    {J4 : Cont [i32, .bool]} {J6 : Cont [.bool]} {mm : Mem 64} {resm : List Nat}
    (hinv : FullDenseInvW c F0 F_cur s)
    (hbk32 : best_k.toNat < 32) (hscr16448 : 16448 ≤ c.scratch_cap)
    (hfresh1 : (fresh ^^^ 1#32).toNat = 2 * s.core.cur_vars + 1)
    (hresm_lt : ∀ x ∈ resm, x < 2 * s.core.cur_vars) (hresm_nd : (resm.map (· / 2)).Nodup)
    (hresm_ent : (cnfOfClauses F_next).EntailsClause (cnfClause ((2 * s.core.cur_vars + 1) ::
      resm)))
    (hct_ref0 : c_top.toNat ∈ fullArenaClauseRefsCore s.core)
    (hct_ng0 : fullArenaClauseGarbCore s.core c_top.toNat = false)
    (hct_sz3 : 3 ≤ fullArenaClauseSizeCore s.core c_top.toNat)
    (hct_sz256 : fullArenaClauseSizeCore s.core c_top.toNat ≤ 256)
    (hfbk_mem : (s.scratch.scratch_buf[best_k.toNat]?.getD 0#32).toNat ∈
      fullArenaClauseLitsCore s.core c_top.toNat)
    (hres_perm_f : resm.Perm ((fullArenaClauseLitsCore s.core c_top.toNat).filter
      (· != (s.scratch.scratch_buf[best_k.toNat]?.getD 0#32).toNat)))
    (hmm : (FullMem c stm ⋆ R) mm) (hstm : M7BvaStOk c F0 F_next s stm)
    (hAbort : ∀ st1 m1, (FullMem c st1 ⋆ R) m1 → M7BvaStOk c F0 F_next s st1 → J4 (mi, false, ())
      m1)
    (hDone : ∀ (ok' : Bool) st1 m1, (FullMem c st1 ⋆ R) m1 → M7BvaStOk c F0 F_next s st1 →
      J6 (ok', ()) m1) :
    wp Γ Q X (m7BvaLargeTopExpr c.hdr c.pArena c.pScratchBuf c.pFlags c.pTmp
      best_k mi c_top fresh J4 J6) mm := by
  obtain ⟨hinvm, hcvm, hfuelm, hsbm, htmm, htrm, hmono⟩ := hstm
  have hmx := c.hmaxv; have har_b := c.harena; have hscr_b := c.hscr
  unfold dimacsBound at hmx har_b hscr_b; have hcl := hinv.1.core_ok; have hsc := hinv.1.scratch_ok
  have hclm := hinvm.1.core_ok; have hscm := hinvm.1.scratch_ok; have hcv_le :=
    hclm.cur_vars_le; have hsb_len := hsc.scratch_buf_len; let old_cv := s.core.cur_vars
  obtain ⟨hct_refm, hct_szm, hct_litsm⟩ := hmono c_top.toNat hct_ref0
  have hct_wfm := hinvm.2.1.arena.refs_wf c_top.toNat hct_refm
  have hct_sz_eq : (stm.core.arena[c_top.toNat + 2]'(by
      have := hclm.arena_len_le; have := hclm.arena_len_arr; omega)).toNat =
      fullArenaClauseSizeCore s.core c_top.toNat := by
    rw [← hct_szm]; unfold fullArenaClauseSizeCore; rw [List.getElem?_eq_getElem (by
      have := hclm.arena_len_le; have := hclm.arena_len_arr; omega), Option.getD_some]
  let csz_bv := stm.core.arena[c_top.toNat + 2]'(by
    have := hclm.arena_len_le; have := hclm.arena_len_arr; omega)
  have hcsz_s : csz_bv.toNat = fullArenaClauseSizeCore s.core c_top.toNat := hct_sz_eq
  let C_lits := fullArenaClauseLitsCore s.core c_top.toNat
  have hC_len : C_lits.length = csz_bv.toNat := by
    rw [hcsz_s]; exact FullBvaFwdHelpers.fullArenaClauseLitsCore_length (by
      have := (hinv.2.1.arena.refs_wf c_top.toNat hct_ref0).2.2.1
      have := (hinv.2.1.arena.refs_wf c_top.toNat hct_ref0).2.2.2.1
      have := hcl.arena_len_le; have := hcl.arena_len_arr; omega)
  have hC_nd_vars : (C_lits.map (· / 2)).Nodup := hinv.2.2.2.1 c_top.toNat hct_ref0 hct_ng0
  have hC_nd : C_lits.Nodup := nodup_of_map_div2 hC_nd_vars
  have hC_len_le_cv : csz_bv.toNat ≤ old_cv := by
    rw [← hC_len, ← List.length_map (· / 2)]; exact nodup_lt_length_le hC_nd_vars fun v hv => by
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hv
      have := hinv.2.1.arena.lits_lt c_top.toNat hct_ref0 hct_ng0 l hl; omega
  let flit := s.scratch.scratch_buf[best_k.toNat]'(by omega)
  have hbk_sb : (BitVec.setWidth 64 best_k).toNat < stm.scratch.scratch_buf.length := by
    rw [bv64_setWidth_32, hscm.scratch_buf_len]; omega
  have hflit_eq : stm.scratch.scratch_buf[(BitVec.setWidth 64 best_k).toNat]'hbk_sb = flit := by
    dsimp only [flit]; simp only [hsbm, bv64_setWidth_32]
  have hfbk_mem' : flit.toNat ∈ C_lits := by
    simpa only [flit, List.getElem?_eq_getElem (by omega : best_k.toNat <
      s.scratch.scratch_buf.length), Option.getD_some] using hfbk_mem
  have hfilt_len : (C_lits.filter (· != flit.toNat)).length + 1 = csz_bv.toNat := by
    rw [← hC_len]; exact filter_ne_nodup_length hC_nd hfbk_mem'
  have hct2_n : (BitVec.setWidth 64 c_top + 2).toNat = c_top.toNat + 2 := by
    change (BitVec.setWidth 64 c_top + 2#64).toNat = _; c0_bound
  have hct2_ar : (BitVec.setWidth 64 c_top + 2).toNat < stm.core.arena.length := by
    rw [hct2_n]; have := hclm.arena_len_le; have := hclm.arena_len_arr; omega
  have htmp0_lt : 0 < stm.core.tmp.length := by rw [hclm.tmp_len_arr]; omega
  dsimp only [m7BvaLargeTopExpr, bZext, bOp64, bOp32, bCmp32, bPtr32, bLd32, bIdx0_64]
  c0_hsteps_nogrp
  refine wp_loop_inv
    (fun (tk, j, ()) mj => ∃ tmpj : List (BitVec 32),
      j.toNat ≤ csz_bv.toNat ∧ tmpj.length = c.max_vars ∧
      tk.toNat = 1 + ((C_lits.take j.toNat).filter (· != flit.toNat)).length ∧
      tmpj[0]? = some (fresh ^^^ 1#32) ∧ (∀ t, 1 ≤ t → t < tk.toNat →
        (tmpj[t]?.getD 0#32).toNat = ((C_lits.take j.toNat).filter (· != flit.toNat))[t - 1]?.getD
          0) ∧
      (FullMem c { stm with core := { stm.core with tmp := tmpj } } ⋆ R) mj)
    (fun (_, j, _) _ => csz_bv.toNat - j.toNat) (fun Jf hJf => by
      dsimp only [wp, vals, Arg.val]
      exact hJf (1#32, 0#32, ()) m ⟨_, Nat.zero_le _, by simp [hclm.tmp_len_arr], rfl,
        by rw [show (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0)).toNat = 0 from rfl,
          List.getElem?_set_self (by rw [hclm.tmp_len_arr]; omega)]; rfl,
        fun _ h1 h2 => by simp only [bv_c0] at h2; omega, hm⟩)
    (fun Jf (tk, j, ()) mj ⟨tmpj, hj_le, htmpj_l, htk_eq, htmp0, htmp_rest, hmj⟩ ihf => ?_)
  c0_hsteps
  · have hj_lt : j.toNat < csz_bv.toNat := by
      have h1 : j.toNat < (stm.core.arena[(BitVec.setWidth 64 c_top + 2).toNat]'hct2_ar).toNat :=
        by assumption
      simpa only [hct2_n] using h1
    have hj1 : (j + 1#32).toNat = j.toNat + 1 := by c0_bound
    have hctj_n : (BitVec.setWidth 64 c_top + 3 + BitVec.setWidth 64 j).toNat =
        c_top.toNat + 3 + j.toNat := by
      change (BitVec.setWidth 64 c_top + 3#64 + BitVec.setWidth 64 j).toNat = _; c0_bound
    have hctj_ar : c_top.toNat + 3 + j.toNat < stm.core.arena.length := by
      have := hclm.arena_len_le; have := hclm.arena_len_arr; omega
    have hCj_eq : C_lits[j.toNat]'(by rw [hC_len]; exact hj_lt) =
        (stm.core.arena[c_top.toNat + 3 + j.toNat]'hctj_ar).toNat := by
      have h1 := FullBvaFwdHelpers.fullArenaClauseLitsCore_getElem (k := stm.core)
        (r := c_top.toNat) (j := j.toNat) (by rw [hct_szm]; omega) hctj_ar
      rw [hct_litsm, List.getElem?_eq_getElem (by rw [hC_len]; exact hj_lt)] at h1
      exact Option.some.inj h1
    have htake_succ := FullBvaFwdHelpers.take_succ_filter_eq (l := C_lits)
      (i := j.toNat) (x := flit.toNat) (by rw [hC_len]; exact hj_lt)
    have hsub_len : ((C_lits.take (j.toNat + 1)).filter (· != flit.toNat)).length ≤
        (C_lits.filter (· != flit.toNat)).length :=
      List.Sublist.length_le (List.Sublist.filter _ (List.take_sublist _ _))
    have hctj_mod : (c_top.toNat + BitVec.toNat (3 : BitVec 64) + j.toNat) % 2 ^ 64 =
        c_top.toNat + 3 + j.toNat := by
      rw [show BitVec.toNat (3 : BitVec 64) = 3 from rfl]; omega
    c0_hsteps_nogrp; refine wp_join_group (ts := [i32])
      (fun (tk', ()) m' => ∃ tmp' : List (BitVec 32), tmp'.length = c.max_vars ∧
        tk'.toNat = 1 + ((C_lits.take (j.toNat + 1)).filter (· != flit.toNat)).length ∧
        tmp'[0]? = some (fresh ^^^ 1#32) ∧
        (∀ t, 1 ≤ t → t < tk'.toNat → (tmp'[t]?.getD 0#32).toNat =
          ((C_lits.take (j.toNat + 1)).filter (· != flit.toNat))[t - 1]?.getD 0) ∧
        (FullMem c { stm with core := { stm.core with tmp := tmp' } } ⋆ R) m')
      (fun _ (tk', ()) m' ⟨tmp', htl', htk', h0', hrest', hm'⟩ => by
        m7_hsteps_to_jump; exact ihf (tk', j + 1#32, ()) m' (by dsimp only; rw [hj1]; omega)
          ⟨tmp', by rw [hj1]; omega, htl', by rw [hj1]; exact htk', h0',
           fun t ht1 ht2 => by rw [hj1]; exact hrest' t ht1 ht2, hm'⟩)
      (fun Jif hJif => ?_)
    c0_hsplit
    · have hne_bv : stm.core.arena[c_top.toNat + 3 + j.toNat]'hctj_ar ≠ flit := by
        have h1 : ¬ stm.core.arena[(c_top.toNat + BitVec.toNat (3 : BitVec 64) + j.toNat) %
            2 ^ 64]'(by rw [hctj_mod]; exact hctj_ar) =
            stm.scratch.scratch_buf[best_k.toNat]'(by rw [hscm.scratch_buf_len]; omega) := by
          assumption
        simpa only [hctj_mod, flit, hsbm] using h1
      have hne_nat : C_lits[j.toNat]'(by rw [hC_len]; exact hj_lt) ≠ flit.toNat := by
        rw [hCj_eq]; intro h; exact hne_bv (BitVec.eq_of_toNat_eq h)
      have htk_succ_eq : ((C_lits.take (j.toNat + 1)).filter (· != flit.toNat)).length =
          ((C_lits.take j.toNat).filter (· != flit.toNat)).length + 1 := by
        rw [htake_succ, ite_eq_left (bne_iff_ne.mpr hne_nat), List.length_append]; rfl
      have htk_lt_tmp : tk.toNat < tmpj.length := by omega
      have htk1 : (tk + 1#32).toNat = tk.toNat + 1 := by c0_bound
      m7_hsteps_to_jump; refine hJif (tk + 1#32, ()) m
        ⟨tmpj.set tk.toNat (stm.core.arena[c_top.toNat + 3 + j.toNat]'hctj_ar),
         by simp [htmpj_l], by rw [htk1, htk_succ_eq]; omega,
         by rw [List.getElem?_set_ne (by omega)]; exact htmp0, fun t ht1 ht2 => ?_, ?_⟩
      · rw [htk1] at ht2; rw [htake_succ, ite_eq_left (bne_iff_ne.mpr hne_nat)]
        by_cases hte : t = tk.toNat
        · subst hte
          rw [List.getElem?_set_self htk_lt_tmp, Option.getD_some,
            List.getElem?_append_right (by omega),
            show tk.toNat - 1 - ((C_lits.take j.toNat).filter (· != flit.toNat)).length = 0 by
              omega]
          simp [hCj_eq]
        · rw [List.getElem?_set_ne (Ne.symm hte), List.getElem?_append_left (by omega)]
          exact htmp_rest t ht1 (by omega)
      · simp only [hctj_n, bv64_setWidth_32] at hm; exact hm
    · have heq_bv : stm.core.arena[c_top.toNat + 3 + j.toNat]'hctj_ar = flit := by
        have h1 : stm.core.arena[(c_top.toNat + BitVec.toNat (3 : BitVec 64) + j.toNat) %
            2 ^ 64]'(by rw [hctj_mod]; exact hctj_ar) =
            stm.scratch.scratch_buf[best_k.toNat]'(by rw [hscm.scratch_buf_len]; omega) := by
          assumption
        simpa only [hctj_mod, flit, hsbm] using h1
      have heq_nat : (C_lits[j.toNat]'(by rw [hC_len]; exact hj_lt) != flit.toNat) = false := by
        rw [hCj_eq, heq_bv]; simp
      have htake_eq : (C_lits.take (j.toNat + 1)).filter (· != flit.toNat) =
          (C_lits.take j.toNat).filter (· != flit.toNat) := by
        rw [htake_succ, heq_nat]; simp
      dsimp only [wp, vals, Arg.val]; exact hJif (tk, ()) mj
        ⟨tmpj, htmpj_l, by rw [htake_eq]; exact htk_eq, htmp0,
         fun t ht1 ht2 => by rw [htake_eq]; exact htmp_rest t ht1 ht2, hmj⟩
  · have hj_eq : j.toNat = csz_bv.toNat := by
      have h1 : ¬ j.toNat < (stm.core.arena[(BitVec.setWidth 64 c_top + 2).toNat]'hct2_ar).toNat :=
        by assumption
      have h2 : ¬ j.toNat < csz_bv.toNat := (by simpa only [hct2_n] using h1); omega
    rw [hj_eq, ← hC_len, List.take_length] at htk_eq htmp_rest
    have htk_csz : tk.toNat = csz_bv.toNat := by omega
    let st_tmp : FullState := { stm with core := { stm.core with tmp := tmpj } }
    have hinv_tmp : FullDenseInvW c F0 F_next st_tmp := fullDenseInvW_set_tmp hinvm htmpj_l
    c0_call hAllocCl; refine ⟨c, st_tmp, R, rfl, hinv_tmp.1, hmj, ?_⟩; split
    · m7_hsteps_to_jump; exact hAbort st_tmp mj hmj ⟨hinv_tmp, hcvm, hfuelm, hsbm, htmm, htrm,
      hmono⟩
    · intro ar1 ma1; dsimp only; intro hlen_a1 hhold_a1 hns_a1 hng_a1 _ hsz_a1 hma1
      have hncr_nat : (BitVec.ofNat 64 stm.core.arena_len).toNat = stm.core.arena_len := by
        have := hclm.arena_len_le; c0_bound
      c0_hsteps_nogrp
      · let ncr0 := stm.core.arena_len
        have hncr_cap : ncr0 + 3 + tk.toNat ≤ c.arena_cap := hlen_a1.core_ok.arena_len_le
        have htk_b : tk.toNat + 2 < 2 ^ 32 := by omega
        let CopyDone (mf : Mem 64) : Prop :=
          ∃ arf : List (BitVec 32), arf.length = c.arena_cap ∧
            (∀ i < ncr0, arf[i]? = stm.core.arena[i]?) ∧ arf[ncr0]? = ar1[ncr0]? ∧
            arf[ncr0 + 2]? = ar1[ncr0 + 2]? ∧ (∀ t < tk.toNat, arf[ncr0 + 3 + t]? = tmpj[t]?) ∧
            (FullMem c { st_tmp with core := { st_tmp.core with
              arena := arf, arena_len := ncr0 + 3 + tk.toNat } } ⋆ R) mf
        refine wp_join_group (ts := [i32]) (fun (_, ()) mf => CopyDone mf)
          (fun _ (_, ()) mf ⟨arf, harj_l, hhold_j, harj0, harj2, hcp_j, hmjc⟩ => by
            let st_cp : FullState :=
              { st_tmp with core := { st_tmp.core with arena := arf, arena_len := ncr0 + 3 +
                tk.toNat } }
            have hlen_cp : st_cp.LengthsOk c :=
              ⟨{ hlen_a1.core_ok with arena_len_arr := harj_l }, hlen_a1.scratch_ok⟩
            have hns_cp : (arf[ncr0]?.getD 0#32 &&& 0x00800000#32) = 0#32 := by
              rw [harj0]; exact hns_a1
            have hsz_cp : (arf[ncr0 + 2]?.getD 0#32).toNat = tk.toNat := by
              rw [harj2]; exact hsz_a1
            have hrefs_cp : fullArenaClauseRefsCore st_cp.core =
                fullArenaClauseRefsCore stm.core ++ [ncr0] :=
              fullArenaClauseRefsCore_append hinvm.2.1.arena (by omega) rfl hhold_j hns_cp hsz_cp
            have hwat_cp : ModeWatchesInv F_next st_cp.core :=
              hinvm.2.1.watches.with_wstk rfl rfl rfl rfl rfl
                (fun r hr => by rw [hrefs_cp]; exact List.mem_append_left _ hr)
            have hnew_lits_eq : fullArenaClauseLitsCore { stm.core with arena := arf } ncr0 =
                (2 * old_cv + 1) :: C_lits.filter (· != flit.toNat) := by
              rw [fullArenaLitsCore_eq_map (sz := tk.toNat)
                (by unfold fullArenaClauseSizeCore; exact hsz_cp) (by dsimp only; omega)]
              apply List.ext_getElem?; intro t; cases t with
              | zero =>
                rw [List.getElem?_map, List.getElem?_range (by omega), Option.map_some,
                  Nat.add_zero, hcp_j 0 (by omega), htmp0, Option.getD_some, hfresh1]; rfl
              | succ t' =>
                by_cases ht : t' + 1 < tk.toNat
                · rw [List.getElem?_map, List.getElem?_range ht, Option.map_some,
                    hcp_j (t' + 1) ht, htmp_rest (t' + 1) (by omega) ht, Nat.add_sub_cancel,
                    List.getElem?_cons_succ,
                    List.getElem?_eq_getElem (by omega : t' < (C_lits.filter (· !=
                      flit.toNat)).length),
                    Option.getD_some]
                · rw [List.getElem?_eq_none (by simp; omega),
                    List.getElem?_eq_none (by simp; omega)]
            have hnew_perm : (fullArenaClauseLitsCore { stm.core with arena := arf }
                ncr0).Perm ((2 * old_cv + 1) :: resm) := by
              rw [hnew_lits_eq]; have hf' : resm.Perm (C_lits.filter (· != flit.toNat)) := by
                simpa only [flit, List.getElem?_eq_getElem (by omega : best_k.toNat <
                  s.scratch.scratch_buf.length), Option.getD_some] using hres_perm_f
              exact List.Perm.cons _ hf'.symm
            have hnew_lt :
                ∀ l ∈ fullArenaClauseLitsCore { stm.core with arena := arf } ncr0,
                l < 2 * stm.core.cur_vars := by
              intro l hl; rw [hcvm]
              rcases List.mem_cons.mp (hnew_perm.subset hl) with rfl | hr
              · omega
              · have := hresm_lt l hr; omega
            have hnew_nd : ((fullArenaClauseLitsCore { stm.core with arena := arf }
                ncr0).map (· / 2)).Nodup := by
              have hp := hnew_perm.map (· / 2)
              refine (List.nodup_cons.mpr ⟨?_, hresm_nd⟩).perm hp.symm
              intro hmem; obtain ⟨x, hx, hdiv⟩ := List.mem_map.mp hmem
              have := hresm_lt x hx; dsimp only [old_cv] at *; omega
            have hnew_ent : (cnfOfClauses F_next).EntailsClause
                (cnfClause (fullArenaClauseLitsCore { stm.core with arena := arf } ncr0)) :=
              clause_entails_of_perm hnew_perm.symm hresm_ent
            have htmp_lt :
                ∀ t (ht : t < tk.toNat), (tmpj[t]'(by omega)).toNat < 2 * (old_cv + 1) := by
              intro t ht; have hmem : (tmpj[t]'(by omega)).toNat ∈
                  fullArenaClauseLitsCore { stm.core with arena := arf } ncr0 := by
                rw [fullArenaLitsCore_eq_map (sz := tk.toNat)
                  (by unfold fullArenaClauseSizeCore; exact hsz_cp) (by dsimp only; omega)]
                refine List.mem_map.mpr ⟨t, List.mem_range.mpr ht, ?_⟩
                rw [hcp_j t ht, List.getElem?_eq_getElem (by omega), Option.getD_some]
              simpa only [hcvm] using hnew_lt _ hmem
            exact m7_bva_large_watch_wp (stm := stm) hWPush hUnwatch
              ⟨hinvm, hcvm, hfuelm, hsbm, htmm, htrm, hmono⟩ htmpj_l (by omega) (by omega)
              (by omega) hncr_cap hhold_j hns_cp hsz_cp hnew_lt hnew_nd hnew_ent
              (fun t ht => htmp_lt t ht) hlen_cp hrefs_cp hwat_cp hmjc hDone)
          (fun Jcp_done hJcp_done => by
            let CopyInv : Tup Val [i32] → Mem 64 → Prop := fun (jc, ()) mjc =>
              ∃ arj : List (BitVec 32), jc.toNat ≤ tk.toNat ∧
                arj.length = c.arena_cap ∧ (∀ i < ncr0, arj[i]? = stm.core.arena[i]?) ∧
                arj[ncr0]? = ar1[ncr0]? ∧ arj[ncr0 + 2]? = ar1[ncr0 + 2]? ∧
                (∀ t < jc.toNat, arj[ncr0 + 3 + t]? = tmpj[t]?) ∧
                (FullMem c { st_tmp with core := { st_tmp.core with
                  arena := arj, arena_len := ncr0 + 3 + tk.toNat } } ⋆ R) mjc
            c0_hsplit
            · -- `(ncr & 1) != 0`: `dst_cl` is 8-byte aligned; run `u64` copy loop + tail
              refine wp_loop_inv CopyInv (fun (jc, _) _ => tk.toNat - jc.toNat)
                (fun Jcp hJcp => by
                  m7_hsteps_to_jump
                  exact hJcp (0#32, ()) ma1 ⟨ar1, Nat.zero_le _, hlen_a1.core_ok.arena_len_arr,
                    hhold_a1, rfl, rfl, fun _ h => by simp only [bv_c0] at h; omega, hma1⟩)
                (fun Jcp (jc, ()) mjc ⟨arj, hjc_le, harj_l, hhold_j, harj0, harj2, hcp_j, hmjc⟩
                    ihcp => ?_)
              c0_hsteps_nogrp
              · have hjc2 : jc.toNat + 2 ≤ tk.toNat := fid_bv32_ule_add2 hjc_le htk_b (by c0_bound)
                have hjc2_n : (jc + 2#32).toNat = jc.toNat + 2 := fid_bv32_add2_toNat hjc_le htk_b
                have hjc_tmp_len : jc.toNat + 1 < st_tmp.core.tmp.length := by
                  dsimp only [st_tmp]; omega
                have hjc_ar_len : (ncr0 + 3 + jc.toNat) + 1 < arj.length := by omega
                have hncr3 : ncr0 + 3 < 2 ^ 64 := by omega
                have hjc_u64 : ncr0 + 3 + jc.toNat < 2 ^ 64 := by omega
                let v64_p : BitVec 64 :=
                  packU32Pair (tmpj[jc.toNat]'(by omega)) (tmpj[jc.toNat + 1]'(by omega))
                let arj' := (arj.set (ncr0 + 3 + jc.toNat) (tmpj[jc.toNat]'(by omega))).set
                  (ncr0 + 3 + jc.toNat + 1) (tmpj[jc.toNat + 1]'(by omega))
                refine wp_load_of (v := v64_p) ?_ ?_
                · exact loadVal_fullMem_tmp_i64_off
                    (s := { st_tmp with core := { st_tmp.core with
                      arena := arj, arena_len := ncr0 + 3 + tk.toNat } })
                    (fid_tmp_copy_addr c.pTmp jc) (by dsimp only [st_tmp]; exact hjc_tmp_len) hmjc
                · refine wp_store_sep
                    (P := FullMem c { st_tmp with core := { st_tmp.core with
                      arena := arj', arena_len := ncr0 + 3 + tk.toNat } }) (R := R) ?_ ?_
                  · have hdp_st := store_fullMem_arena_i64_off
                      (s := { st_tmp with core := { st_tmp.core with
                        arena := arj, arena_len := ncr0 + 3 + tk.toNat } })
                      v64_p (fid_arena_copy_addr c.pArena hncr3 jc hjc_u64)
                      (by dsimp only; exact hjc_ar_len) hmjc
                    dsimp only [v64_p] at hdp_st
                    rw [packU32Pair_lo, packU32Pair_hi] at hdp_st
                    exact hdp_st
                  · intro m1 hm1
                    m7_hsteps_to_jump
                    refine ihcp (jc + 2#32, ()) m1 (by dsimp only; rw [hjc2_n]; omega)
                      ⟨arj', by rw [hjc2_n]; exact hjc2, by simp [arj', harj_l],
                       fun i hi => by
                         dsimp only [arj']
                         rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
                         exact hhold_j i hi,
                       by dsimp only [arj']
                          rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
                          exact harj0,
                       by dsimp only [arj']
                          rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
                          exact harj2,
                       fun t ht => by
                         rw [hjc2_n] at ht; dsimp only [arj']
                         by_cases ht1 : t = jc.toNat + 1
                         · subst ht1
                           rw [← Nat.add_assoc, List.getElem?_set_self (by simp [harj_l]; omega),
                             List.getElem?_eq_getElem (by omega)]
                           try rfl
                         · rw [List.getElem?_set_ne (by omega)]
                           by_cases ht0 : t = jc.toNat
                           · subst ht0
                             rw [List.getElem?_set_self (by omega),
                               List.getElem?_eq_getElem (by omega)]
                             try rfl
                           · rw [List.getElem?_set_ne (by omega)]; exact hcp_j t (by omega),
                       hm1⟩
              · have htk_tail : tk.toNat ≤ jc.toNat + 1 := by
                  have h1 : ¬ (jc.toNat + (2#32 : BitVec 32).toNat) % 2 ^ 32 ≤ tk.toNat := by
                    assumption
                  rw [show (2#32 : BitVec 32).toNat = 2 from rfl, Nat.mod_eq_of_lt (by omega)] at h1
                  omega
                refine wp_join_group (ts := []) (fun () mf => CopyDone mf)
                  (fun _ _ mf hc => by m7_hsteps_to_jump; exact hJcp_done (jc, ()) mf hc)
                  (fun Jtl hJtl => by
                    c0_hsteps_nogrp
                    · have hjc_lt : jc.toNat < tk.toNat := by c0_bound
                      have hjc_tmp : jc.toNat < tmpj.length := by omega
                      have hjc_tmp_st : jc.toNat < st_tmp.core.tmp.length := by
                        dsimp only [st_tmp]; exact hjc_tmp
                      have hncr3 : ncr0 + 3 < 2 ^ 64 := by omega
                      have hjc_u64 : ncr0 + 3 + jc.toNat < 2 ^ 64 := by omega
                      have har_tl : ncr0 + 3 + jc.toNat < arj.length := by omega
                      let tv_j : BitVec 32 := tmpj[jc.toNat]'hjc_tmp
                      let ar_tl := arj.set (ncr0 + 3 + jc.toNat) tv_j
                      refine wp_load_of (v := tv_j) ?_ ?_
                      · exact loadVal_fullMem_tmp_i32_off
                          (s := { st_tmp with core := { st_tmp.core with
                            arena := arj, arena_len := ncr0 + 3 + tk.toNat } })
                          (fid_tmp_tail_addr c.pTmp jc) (by dsimp only [st_tmp]; exact hjc_tmp_st)
                          hmjc
                      · refine wp_store_sep
                          (P := FullMem c { st_tmp with core := { st_tmp.core with
                            arena := ar_tl, arena_len := ncr0 + 3 + tk.toNat } }) (R := R) ?_ ?_
                        · exact store_fullMem_arena_i32_off
                            (s := { st_tmp with core := { st_tmp.core with
                              arena := arj, arena_len := ncr0 + 3 + tk.toNat } })
                            tv_j (fid_arena_tail_addr c.pArena hncr3 jc hjc_u64)
                            (by dsimp only; exact har_tl) hmjc
                        · intro mf hmf
                          m7_hsteps_to_jump
                          refine hJtl () mf ⟨ar_tl, by simp [ar_tl, harj_l],
                            fun i hi => by
                              dsimp only [ar_tl]
                              rw [List.getElem?_set_ne (by omega)]; exact hhold_j i hi,
                            by
                              dsimp only [ar_tl]; rw [List.getElem?_set_ne (by omega)]; exact harj0,
                            by
                              dsimp only [ar_tl]; rw [List.getElem?_set_ne (by omega)]; exact harj2,
                            fun t ht => by
                              dsimp only [ar_tl]
                              by_cases hte : t = jc.toNat
                              · subst hte
                                rw [List.getElem?_set_self (by omega),
                                  List.getElem?_eq_getElem hjc_tmp]
                              · rw [List.getElem?_set_ne (by omega)]; exact hcp_j t (by omega),
                            hmf⟩
                    · have hjc_eq : jc.toNat = tk.toNat := by c0_bound
                      rw [hjc_eq] at hcp_j
                      m7_hsteps_to_jump
                      exact hJtl () mjc ⟨arj, harj_l, hhold_j, harj0, harj2, hcp_j, hmjc⟩)
            · -- `(ncr & 1) == 0`: aligned-safe scalar `u32` copy loop
              refine wp_loop_inv CopyInv (fun (jc, _) _ => tk.toNat - jc.toNat)
                (fun Jcp hJcp => by
                  m7_hsteps_to_jump
                  exact hJcp (0#32, ()) ma1 ⟨ar1, Nat.zero_le _, hlen_a1.core_ok.arena_len_arr,
                    hhold_a1, rfl, rfl, fun _ h => by simp only [bv_c0] at h; omega, hma1⟩)
                (fun Jcp (jc, ()) mjc ⟨arj, hjc_le, harj_l, hhold_j, harj0, harj2, hcp_j, hmjc⟩
                    ihcp => ?_)
              c0_hsteps_nogrp
              · have hjc_lt : jc.toNat < tk.toNat := by c0_bound
                have hjc1_n : (jc + 1#32).toNat = jc.toNat + 1 := by
                  rw [BitVec.toNat_add, show (1#32).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
                have hjc_tmp : jc.toNat < tmpj.length := by omega
                have hjc_tmp_st : jc.toNat < st_tmp.core.tmp.length := by
                  dsimp only [st_tmp]; exact hjc_tmp
                have hncr3 : ncr0 + 3 < 2 ^ 64 := by omega
                have hjc_u64 : ncr0 + 3 + jc.toNat < 2 ^ 64 := by omega
                have har_cp : ncr0 + 3 + jc.toNat < arj.length := by omega
                let tv_j : BitVec 32 := tmpj[jc.toNat]'hjc_tmp
                let ar_cp := arj.set (ncr0 + 3 + jc.toNat) tv_j
                refine wp_load_of (v := tv_j) ?_ ?_
                · exact loadVal_fullMem_tmp_i32_off
                    (s := { st_tmp with core := { st_tmp.core with
                      arena := arj, arena_len := ncr0 + 3 + tk.toNat } })
                    (fid_tmp_tail_addr c.pTmp jc) (by dsimp only [st_tmp]; exact hjc_tmp_st) hmjc
                · refine wp_store_sep
                    (P := FullMem c { st_tmp with core := { st_tmp.core with
                      arena := ar_cp, arena_len := ncr0 + 3 + tk.toNat } }) (R := R) ?_ ?_
                  · exact store_fullMem_arena_i32_off
                      (s := { st_tmp with core := { st_tmp.core with
                        arena := arj, arena_len := ncr0 + 3 + tk.toNat } })
                      tv_j (fid_arena_tail_addr c.pArena hncr3 jc hjc_u64)
                      (by dsimp only; exact har_cp) hmjc
                  · intro m1 hm1
                    m7_hsteps_to_jump
                    refine ihcp (jc + 1#32, ()) m1 (by dsimp only; rw [hjc1_n]; omega)
                      ⟨ar_cp, by rw [hjc1_n]; omega, by simp [ar_cp, harj_l],
                       fun i hi => by
                         dsimp only [ar_cp]
                         rw [List.getElem?_set_ne (by omega)]; exact hhold_j i hi,
                       by dsimp only [ar_cp]; rw [List.getElem?_set_ne (by omega)]; exact harj0,
                       by dsimp only [ar_cp]; rw [List.getElem?_set_ne (by omega)]; exact harj2,
                       fun t ht => by
                         rw [hjc1_n] at ht; dsimp only [ar_cp]
                         by_cases hte : t = jc.toNat
                         · subst hte
                           rw [List.getElem?_set_self (by omega), List.getElem?_eq_getElem hjc_tmp]
                         · rw [List.getElem?_set_ne (by omega)]; exact hcp_j t (by omega),
                       hm1⟩
              · have hjc_eq : jc.toNat = tk.toNat := by c0_bound
                rw [hjc_eq] at hcp_j
                m7_hsteps_to_jump
                exact hJcp_done (jc, ()) mjc
                  ⟨arj, harj_l, hhold_j, harj0, harj2, hcp_j, hmjc⟩)

private theorem m7_bva_phase1b_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    (hAddBin : M7AddBinHyp Γ) (hAllocCl : M7AllocClHyp Γ) (hWPush : M7WPushHyp Γ)
    (hDelBin : M7DelBinHyp Γ) (hUnwatch : M7UnwatchHyp Γ)
    {c : FullCfg} {F0 : CNF Nat} {F_cur F_next : List (List Nat)} {s st1a : FullState}
    {R : Mem 64 → Prop} {best_k mn_bv fresh : Val i32} {ok1a : Val .bool} {m1a : Mem 64}
    (hinv : FullDenseInvW c F0 F_cur s) (hbk1 : 1 ≤ best_k.toNat) (hbk32 : best_k.toNat < 32)
    (hmat : M4BvaMatrixInv c F_cur s (best_k.toNat + 1))
    (hmn_getD : (s.scratch.scratch_buf[32 + best_k.toNat]?.getD 0#32).toNat = mn_bv.toNat)
    (hfresh1 : (fresh ^^^ 1#32).toNat = 2 * s.core.cur_vars + 1) (resAt : Nat → List Nat)
    (hresAt : ∀ idx < mn_bv.toNat,
      (∀ x ∈ resAt idx, x < 2 * s.core.cur_vars) ∧ ((resAt idx).map (· / 2)).Nodup ∧
      M4BvaRowEntryOk F_cur s (s.scratch.scratch_buf[best_k.toNat]?.getD 0#32).toNat
        (s.scratch.scratch_buf[64 + best_k.toNat * 256 + idx]?.getD 0#32) (resAt idx) ∧
      (cnfOfClauses F_next).EntailsClause (cnfClause ((2 * s.core.cur_vars + 1) :: resAt idx)))
    (hst1a : M7BvaStOk c F0 F_next s st1a) (hm1a : (FullMem c st1a ⋆ R) m1a)
    (hQ : ∀ ok s' m', FullDenseInv c F0 s' → s.core.cur_vars ≤ s'.core.cur_vars →
      s'.core.fuel = s.core.fuel → s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach → (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    wp Γ Q X (m7BvaPhase1bExpr c.hdr c.pArena c.pScratchBuf c.pWsort c.pFlags c.pTmp
      best_k mn_bv fresh ok1a) m1a := by
  have hmx := c.hmaxv; have hwcap := c.hwcap; have har_b := c.harena; have hscr_b := c.hscr
  unfold dimacsBound at hmx hwcap har_b hscr_b
  have hcl := hinv.1.core_ok; have hsc := hinv.1.scratch_ok
  have hcv_le := hcl.cur_vars_le; have hsb_len := hsc.scratch_buf_len
  have hscr16448 := hmat.1; let old_cv := s.core.cur_vars
  have hbk_row := hmat.2.2.2 best_k.toNat (by omega)
  obtain ⟨hfbk_lt, hmn_lo, hmn_hi, hbk_entries⟩ := hbk_row
  rw [hmn_getD] at hmn_lo hmn_hi hbk_entries
  dsimp only [m7BvaPhase1bExpr, m7BvaHdrExpr, m7BvaMidExpr, sSteps, sStep, sLet32, sLd64, sLd32,
    sGrp0, sGrp64_32,
    sGrp64_64_32, sGrp32b, sThen, sElse, sDummyTup, sDummyVal, i64, i32, full_bva_commit_fid_body]
  refine wp_join_group (ts := [i32, .bool])
    (fun (_, ok1b, ()) m1b => ∃ st1b : FullState,
      M7BvaStOk c F0 F_next s st1b ∧ (FullMem c st1b ⋆ R) m1b)
    (fun _ (_, ok1b, ()) m1b ⟨st1b, hst1b, hm1b⟩ => ?_) (fun J1b hJ1b => ?_)
  · c0_hsteps_nogrp
    · have hp2 := m7_bva_phase2_wp (Γ := Γ) (Q := Q) (X := X) hDelBin hUnwatch
        (F_next := F_next) (mn_bv := mn_bv) hinv hbk1 hbk32 hmat hmn_getD hst1b hm1b hQ
      dsimp only [m7BvaPhase2Expr, m7BvaHdrExpr, m7BvaMidExpr, sSteps, sStep, sLd64, sLd32,
        sGrp0, sGrp64_32, sGrp64_64_32, sGrp32b, sThen, sElse, sDummyTup, sDummyVal, i64, i32,
        full_bva_commit_fid_body] at hp2
      exact hp2
    · obtain ⟨hinv1b, hcv1b, hfuel1b, hsb1b, htm1b, htr1b, _⟩ := hst1b
      have hcl1b := hinv1b.1.core_ok; have hsc1b := hinv1b.1.scratch_ok
      have hcv1b_le : old_cv + 1 ≤ c.max_vars := by have := hcl1b.cur_vars_le; omega
      have h2cv : (BitVec.ofNat 64 st1b.core.cur_vars <<< (1 : Nat)).toNat = 2 * (old_cv + 1) := by
        rw [hcv1b]; simp only [bv_c0]; omega
      exact fid_bva_zero_cnt_wp (n := old_cv + 1) (by omega) h2cv hsc1b.wsort_len hm1b
        (fun wsz mzi hwsz_l hmzi => by
          c0_hsteps
          exact hQ false _ mzi (fullDenseInvW_set_wsort hinv1b hwsz_l).toDense
            (by dsimp only; omega) hfuel1b htm1b htr1b hmzi)
  · refine wp_loop_inv
      (fun (mi, okm, ()) mm => ∃ stm : FullState, mi.toNat ≤ mn_bv.toNat ∧
        M7BvaStOk c F0 F_next s stm ∧ (FullMem c stm ⋆ R) mm)
      (fun (mi, _, _) _ => mn_bv.toNat - mi.toNat) (fun J1bl hJ1bl => by
        c0_hsteps; exact hJ1bl (0#32, ok1a, ()) m1a ⟨st1a, Nat.zero_le _, hst1a, hm1a⟩)
      (fun J1bl (mi, okm, ()) mm ⟨stm, hmi_le, hstm, hmm⟩ ihm => ?_)
    obtain ⟨hinvm, hcvm, hfuelm, hsbm, htmm, htrm, hmono⟩ := hstm
    have hclm := hinvm.1.core_ok; have hscm := hinvm.1.scratch_ok; c0_hsteps_nogrp
    · have hmi_lt : mi.toNat < mn_bv.toNat := by assumption
      have hokm_t : okm = true := by assumption
      subst hokm_t; have hmi1 : (mi + 1#32).toNat = mi.toNat + 1 := by c0_bound
      have hctop_idx : (64 + best_k * 256 + mi).toNat = 64 + best_k.toNat * 256 + mi.toNat := by
        change (64#32 + best_k * 256#32 + mi).toNat = _; c0_bound
      have hctop_sb : (BitVec.setWidth 64 (64 + best_k * 256 + mi)).toNat <
          stm.scratch.scratch_buf.length := by
        rw [bv64_setWidth_32, hctop_idx, hscm.scratch_buf_len]; omega
      let c_top := s.scratch.scratch_buf[64 + best_k.toNat * 256 + mi.toNat]'(by omega)
      have hctop_eq : stm.scratch.scratch_buf[(BitVec.setWidth 64
          (64 + best_k * 256 + mi)).toNat]'hctop_sb = c_top := by
        dsimp only [c_top]; simp only [hsbm, bv64_setWidth_32, hctop_idx]
      have hctop_mod_n : (64 + best_k.toNat * 256 + mi.toNat) % 2 ^ 32 =
          64 + best_k.toNat * 256 + mi.toNat := Nat.mod_eq_of_lt (by omega)
      have hctop_mod : stm.scratch.scratch_buf[(BitVec.toNat (64 : BitVec 32) +
          best_k.toNat * BitVec.toNat (256 : BitVec 32) + mi.toNat) % 2 ^ 32]'(by
          rw [show BitVec.toNat (64 : BitVec 32) = 64 from rfl,
            show BitVec.toNat (256 : BitVec 32) = 256 from rfl, hctop_mod_n,
            hscm.scratch_buf_len]; omega) = c_top := by
        dsimp only [c_top]; simp only [hsbm, show BitVec.toNat (64 : BitVec 32) = 64 from rfl,
          show BitVec.toNat (256 : BitVec 32) = 256 from rfl, hctop_mod_n]
      obtain ⟨hresm_lt, hresm_nd, hctop_ok0, hresm_ent⟩ := hresAt mi.toNat hmi_lt
      let resm := resAt mi.toNat
      have hctop_getD : s.scratch.scratch_buf[64 + best_k.toNat * 256 + mi.toNat]?.getD 0#32 =
          c_top := by
        dsimp only [c_top]; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      have hctop_ok : M4BvaRowEntryOk F_cur s
          (s.scratch.scratch_buf[best_k.toNat]?.getD 0#32).toNat c_top resm :=
        hctop_getD ▸ hctop_ok0
      c0_hsteps_nogrp; refine wp_join_group (ts := [.bool])
        (fun (_ok', ()) m1 => ∃ st1 : FullState, (FullMem c st1 ⋆ R) m1 ∧ M7BvaStOk c F0 F_next s
          st1)
        (fun _ (ok', ()) m1 ⟨st1, hm1, hst1⟩ => by
          c0_hsteps; exact ihm (mi + 1#32, ok', ()) m1 (by dsimp only; rw [hmi1]; omega)
            ⟨st1, by rw [hmi1]; omega, hst1, hm1⟩)
        (fun Jtop hJtop => ?_)
      c0_hsplit
      · c0_hsteps
        have hbin_ct : (c_top &&& 0x80000000#32) ≠ 0#32 := by
          simpa only [← hctop_mod] using (by assumption : _)
        unfold M4BvaRowEntryOk at hctop_ok; rw [ite_eq_left hbin_ct] at hctop_ok
        obtain ⟨_, hres_q, _⟩ := hctop_ok; c0_call hAddBin
        refine ⟨c, F0, F_next, stm, R, rfl, hinvm.1, hinvm.2.1, hinvm.2.2.2.2.2.1,
          fun _ _ => ?_, hmm,
          fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 hlen1' hw1' _ _ _ hms1' => ?_⟩
        · rw [hctop_eq]; dsimp only [resm] at hres_q; rw [hres_q] at hresm_ent
          simpa only [show (1 : BitVec 32) = 1#32 from rfl, hfresh1,
            show (2147483647 : BitVec 32) = 0x7FFFFFFF#32 from rfl] using hresm_ent
        · have hinv1' := fullDenseInvW_of_addBin hinvm hlen1' hw1'; c0_hsteps
          · exact hJ1b (mi, false, ()) m1 ⟨_, ⟨hinv1', hcvm, hfuelm, hsbm, htmm, htrm, hmono⟩,
            hms1'⟩
          · exact hJ1b (mi, false, ()) m1 ⟨_, ⟨hinv1', hcvm, hfuelm, hsbm, htmm, htrm, hmono⟩,
            hms1'⟩
          · exact hJ1b (mi, false, ()) m1 ⟨_, ⟨hinv1', hcvm, hfuelm, hsbm, htmm, htrm, hmono⟩,
            hms1'⟩
          · exact hJtop (true, ()) m1 ⟨_, hms1', hinv1', hcvm, hfuelm, hsbm, htmm, htrm, hmono⟩
      · have hbin_ct : (c_top &&& 0x80000000#32) = 0#32 := by
          simpa only [← hctop_mod] using (by assumption : _)
        unfold M4BvaRowEntryOk at hctop_ok; rw [ite_eq_right (fun h' => h' hbin_ct)] at hctop_ok
        obtain ⟨hct_ref0, hct_ng0, hct_sz3, hct_sz256, hfbk_mem, hres_perm_f, _⟩ := hctop_ok
        have hlt := m7_bva_large_top_wp (Γ := Γ) (Q := Q) (X := X) hAllocCl hWPush hUnwatch
          (F_next := F_next) (mi := mi) (resm := resm)
          (c_top := stm.scratch.scratch_buf[(BitVec.setWidth 64
            (64 + best_k * 256 + mi)).toNat]'hctop_sb)
          (fresh := fresh) (J4 := J1b) (J6 := Jtop) hinv hbk32 hscr16448 hfresh1 hresm_lt
          hresm_nd hresm_ent (by rwa [hctop_eq]) (by rwa [hctop_eq]) (by rwa [hctop_eq])
          (by rwa [hctop_eq]) (by rwa [hctop_eq]) (by rwa [hctop_eq]) hmm
          ⟨hinvm, hcvm, hfuelm, hsbm, htmm, htrm, hmono⟩
          (fun st1 m1 hm1 hst1 => hJ1b (mi, false, ()) m1 ⟨st1, hst1, hm1⟩)
          (fun ok' st1 m1 hm1 hst1 => hJtop (ok', ()) m1 ⟨st1, hm1, hst1⟩)
        dsimp only [m7BvaLargeTopExpr, m7BvaLargeWatchExpr, bIdx0_64, bLd32, bPtr32, bCmp32,
          bOp32, bOp64, bZext] at hlt
        exact hlt
    · exact hJ1b (mi, okm, ()) mm ⟨stm, ⟨hinvm, hcvm, hfuelm, hsbm, htmm, htrm, hmono⟩, hmm⟩
    · exact hJ1b (mi, okm, ()) mm ⟨stm, ⟨hinvm, hcvm, hfuelm, hsbm, htmm, htrm, hmono⟩, hmm⟩

private theorem m7_bva_post_defrag_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    (hInitFresh : ∀ args m Q X, fullInitFreshVarHeapSpec args m Q X →
      Γ "full_init_fresh_var" [i64, i32] [] args m Q X)
    (hAddBin : M7AddBinHyp Γ) (hAllocCl : M7AllocClHyp Γ) (hWPush : M7WPushHyp Γ)
    (hDelBin : M7DelBinHyp Γ) (hUnwatch : M7UnwatchHyp Γ)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s sd : FullState}
    {R : Mem 64 → Prop} {best_k mn_bv : Val i32} {md : Mem 64}
    (hinv : FullDenseInvW c F0 F_cur s) (hbk1 : 1 ≤ best_k.toNat) (hbk32 : best_k.toNat < 32)
    (hmat : M4BvaMatrixInv c F_cur s (best_k.toNat + 1)) (hcv_lt : s.core.cur_vars < c.max_vars)
    (hmn_getD : (s.scratch.scratch_buf[32 + best_k.toNat]?.getD 0#32).toNat = mn_bv.toNat)
    (hmd : (FullMem c sd ⋆ R) md) (hsd : M7BvaPreOk c F0 F_cur s sd)
    (hQ : ∀ ok s' m', FullDenseInv c F0 s' → s.core.cur_vars ≤ s'.core.cur_vars →
      s'.core.fuel = s.core.fuel → s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach → (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    wp Γ Q X (m7BvaPostDefragExpr c.hdr c.pArena c.pScratchBuf c.pWsort c.pFlags best_k mn_bv)
      md := by
  obtain ⟨hinvd, hcvd, hfueld, hard, hald, hsbd, htmd, htrd⟩ := hsd
  have hmx := c.hmaxv; have hwcap := c.hwcap; have har_b := c.harena; have hscr_b := c.hscr
  unfold dimacsBound at hmx hwcap har_b hscr_b
  have hcl := hinv.1.core_ok; have hsc := hinv.1.scratch_ok
  have hcv_le := hcl.cur_vars_le; have hsb_len := hsc.scratch_buf_len; have hscr16448 := hmat.1
  have hbk_row := hmat.2.2.2 best_k.toNat (by omega)
  obtain ⟨hfbk_lt, hmn_lo, hmn_hi, hbk_entries⟩ := hbk_row
  rw [hmn_getD] at hmn_lo hmn_hi hbk_entries; let dm := best_k.toNat + 1
  have hdm_bv : (best_k + 1#32).toNat = dm := by simp only [bv_c0, dm]; omega
  dsimp only [m7BvaPostDefragExpr, m7BvaHdrExpr, m7BvaMidExpr, sSteps, sStep, sLet32, sLd64,
    sLd32, sGrp0, sGrp64_32,
    sGrp64_64_32, sThen, sElse, sDummyTup, sDummyVal, i64, i32, full_bva_commit_fid_body]
  have hcld := hinvd.1.core_ok; have hscd := hinvd.1.scratch_ok; let old_cv := s.core.cur_vars
  have hfv_nat : (BitVec.setWidth 32 (BitVec.ofNat 64 sd.core.cur_vars)).toNat = old_cv := by
    rw [hcvd]; c0_bound
  have hcv1_nat : (BitVec.ofNat 64 sd.core.cur_vars + 1).toNat = old_cv + 1 := by
    change (BitVec.ofNat 64 sd.core.cur_vars + 1#64).toNat = _; rw [hcvd]; c0_bound
  c0_hsteps
  let sd_inc : FullState := { sd with core := { sd.core with cur_vars := old_cv + 1 } }
  have hmd_inc : (FullMem c sd_inc ⋆ R) m := by dsimp only [sd_inc]; rw [hcv1_nat] at hm; exact hm
  c0_call hInitFresh; refine ⟨c, sd_inc, R, rfl, ⟨{ hcld with
         cur_vars_ge := by have := hcld.cur_vars_ge; dsimp only [sd_inc, old_cv]; omega
         cur_vars_le := by dsimp only [sd_inc, old_cv]; omega
         trail_end_le := by have := hcld.trail_end_le; dsimp only [sd_inc, old_cv]; omega },
     hscd⟩,
    by dsimp only [sd_inc, old_cv]; rw [hfv_nat]; omega, hmd_inc,
    fun vals' mrk' fl' lvl' rsns' wvec' unass' sc' m1 hlen1 hext1 hsb1 hws1 htm1 htr1 hss1
      hv0 hv1 hv_oth hm0 hm_oth hl0 hl_oth hr0 hr_oth hw0 hw_oth hm1 => ?_⟩
  let L : List Nat := (List.range dm).map fun t => (s.scratch.scratch_buf[t]?.getD 0#32).toNat
  let resAt (idx : Nat) : List Nat :=
    if h : idx < mn_bv.toNat then Classical.choose (hbk_entries idx h) else []
  let Qs : List (List Nat) := (List.range mn_bv.toNat).map resAt
  have hL_lt : ∀ f ∈ L, f < 2 * old_cv := by
    intro f hf; obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hf
    rw [List.mem_range] at ht; exact (hmat.2.2.2 t (by omega)).1
  have hQ_lt : ∀ C ∈ Qs, ∀ l ∈ C, l < 2 * old_cv := by
    intro C hC l hl; obtain ⟨idx, hidx, rfl⟩ := List.mem_map.mp hC
    rw [List.mem_range] at hidx; dsimp only [resAt] at hl; rw [dite_eq_left hidx] at hl
    exact (Classical.choose_spec (hbk_entries idx hidx)).1 l hl
  have hprod : ∀ f ∈ L, ∀ C ∈ Qs, (cnfOfClauses F_cur).EntailsClause (cnfClause (f :: C)) := by
    intro f hf C hC; obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hf; rw [List.mem_range] at ht
    obtain ⟨idx, hidx, rfl⟩ := List.mem_map.mp hC; rw [List.mem_range] at hidx
    dsimp only [resAt]; rw [dite_eq_left hidx]
    exact (Classical.choose_spec (hbk_entries idx hidx)).2.2.2.1 t (by omega)
  let F_next := bvaExtendGen old_cv L Qs F_cur
  let s1 : FullState :=
    { sd_inc with core := { sd_inc.core with vals := vals', mrk := mrk', flags := fl', lvl := lvl',
                                             rsns := rsns', wvec := wvec', unassigned := unass' }
                  scratch := sc' }
  have hcore1 : s1.core =
      { sd.core with cur_vars := sd.core.cur_vars + 1, vals := vals', mrk := mrk',
                     flags := fl', lvl := lvl', rsns := rsns', wvec := wvec',
                     unassigned := unass' } := by dsimp only [s1, sd_inc, old_cv]; rw [hcvd]
  have ⟨hw1, hd1⟩ := fullDenseInv_add_fresh_var_gen (s := sd) (s' := s1)
    hinvd.1 hinvd.2.1 hinvd.2.2.1 hinvd.2.2.2.1 hinvd.2.2.2.2.1 hinvd.2.2.2.2.2.1
    hinvd.2.2.2.2.2.2 (by rw [hcvd]; exact hcv_lt)
    (by rw [hcvd]; exact hL_lt) (by rw [hcvd]; exact hQ_lt) hprod hlen1 hcore1
    (by rw [hfv_nat] at hv0; rwa [hcvd]) (by rw [hfv_nat] at hv1; rwa [hcvd])
    (by intro l hl hne; exact hv_oth l hl (by rw [hfv_nat]; dsimp only [old_cv]; rwa [← hcvd]))
    (by rw [hfv_nat] at hm0; rwa [hcvd])
    (by intro v hv hne; exact hm_oth v hv (by rw [hfv_nat]; dsimp only [old_cv]; rwa [← hcvd]))
    (by intro v hv hne; exact hl_oth v hv (by rw [hfv_nat]; dsimp only [old_cv]; rwa [← hcvd]))
    (by intro v hv hne; exact hr_oth v hv (by rw [hfv_nat]; dsimp only [old_cv]; rwa [← hcvd]))
    (by intro k hk; rw [hfv_nat] at hw0; rw [hcvd]; exact hw0 k hk)
    (by intro i hi hne; exact hw_oth i hi (by rw [hfv_nat]; dsimp only [old_cv]; rwa [← hcvd]))
    hext1.1 hext1.2
  have hinv1 : FullDenseInvW c F0 F_next s1 :=
    ⟨hlen1, by rwa [hcvd] at hw1, hd1.2.1, hd1.2.2.1, hd1.2.2.2.1, hd1.2.2.2.2.1, hd1.2.2.2.2.2⟩
  have hpos_ent : ∀ f ∈ L, (cnfOfClauses F_next).EntailsClause (cnfClause [2 * old_cv, f]) :=
    fun _ hf => bvaExtendGen_entails_pos hf
  have hneg_ent : ∀ R ∈ Qs, (cnfOfClauses F_next).EntailsClause (cnfClause ((2 * old_cv + 1) ::
    R)) :=
    fun _ hR => bvaExtendGen_entails_neg hR
  let fv_bv := BitVec.setWidth 32 (BitVec.ofNat 64 sd.core.cur_vars)
  have hfv_repr : 2 * (BitVec.setWidth 64 fv_bv).toNat + 1 < sd.core.repr.length := by
    rw [bv64_setWidth_32, hfv_nat, hcld.repr_len]; omega
  have hfv_sig : (BitVec.setWidth 64 fv_bv).toNat < sc'.sim_sig.length := by
    rw [bv64_setWidth_32, hfv_nat, hlen1.scratch_ok.sim_sig_len]; omega
  have hfv2_ws : (BitVec.setWidth 64 (fv_bv <<< (1 : Nat))).toNat < sc'.wsort.length := by
    rw [bv64_setWidth_32, bv32_shl1_nat, hfv_nat, Nat.mod_eq_of_lt (by omega),
      hlen1.scratch_ok.wsort_len]; omega
  have hfv21_ws : (BitVec.setWidth 64 ((fv_bv <<< (1 : Nat)) ||| 1#32)).toNat < sc'.wsort.length
    := by
    rw [bv64_setWidth_32, bv32_shl1_or1 (by rw [hfv_nat]; omega), hfv_nat,
      hlen1.scratch_ok.wsort_len]; omega
  have hfresh_nat : (fv_bv <<< (1 : Nat)).toNat = 2 * old_cv := by
    rw [bv32_shl1_nat, hfv_nat, Nat.mod_eq_of_lt (by omega)]
  have hfresh_bv : (fv_bv <<< (1 : BitVec 32)).toNat = 2 * old_cv := by
    rw [bv32_shl1_bv, hfv_nat, Nat.mod_eq_of_lt (by omega)]
  have hfresh1_nat : ((fv_bv <<< (1 : Nat)) ^^^ 1#32).toNat = 2 * old_cv + 1 := by
    rw [bv32_shl1_xor1 (by rw [hfv_nat]; omega), hfv_nat]
  have hfresh1_bv : ((fv_bv <<< (1 : BitVec 32)) ^^^ (1 : BitVec 32)).toNat = 2 * old_cv + 1 := by
    have hev : (fv_bv <<< (1 : BitVec 32)) = fv_bv <<< (1 : Nat) := by
      apply BitVec.eq_of_toNat_eq; rw [bv32_shl1_bv, bv32_shl1_nat]
    rw [hev]; exact hfresh1_nat
  c0_hsteps_nogrp
  let st0 : FullState :=
    { core := { sd.core with cur_vars := old_cv + 1, vals := vals', mrk := mrk', flags := fl',
                             lvl := lvl', rsns := rsns', wvec := wvec', unassigned := unass',
                             repr := repr64Set sd.core.repr (BitVec.setWidth 64 fv_bv).toNat 0 }
      scratch := { sc' with
        sim_sig := sc'.sim_sig.set (BitVec.setWidth 64 fv_bv).toNat 0
        wsort := (sc'.wsort.set (BitVec.setWidth 64 (fv_bv <<< (OfNat.ofNat 1 : BitVec 32))).toNat
          0).set (BitVec.setWidth 64 (fv_bv <<< (OfNat.ofNat 1 : BitVec 32) ||| 1#32)).toNat 0 } }
  have hinv0 : FullDenseInvW c F0 F_next st0 :=
    fullDenseInv_with_core_aux (tc' := sd.core.tmp_cnt) (tl' := sd.core.tmp_len)
      hinv1 (by rw [repr64Set_length, hcld.repr_len]) hcld.min_clr_len_arr
      hcld.tmp_len_arr hlen1.core_ok.flags_len hcld.tmp_len_le
      { hlen1.scratch_ok with sim_sig_len := by simp [hlen1.scratch_ok.sim_sig_len]
                              wsort_len := by simp [hlen1.scratch_ok.wsort_len] } rfl rfl
  have hmono0 : ArenaMono s.core st0.core := fun r hr => by
    change r ∈ fullArenaClauseRefsCore { sd.core with arena := sd.core.arena } ∧ _
    have h1 : fullArenaClauseRefsCore { sd.core with arena := sd.core.arena } =
        fullArenaClauseRefsCore s.core := by unfold fullArenaClauseRefsCore; rw [hard, hald]
    refine ⟨by rw [h1]; exact hr, ?_, ?_⟩
    · unfold fullArenaClauseSizeCore; rw [hard]
    · unfold fullArenaClauseLitsCore fullArenaClauseSizeCore; rw [hard]
  refine wp_join_group (ts := [i32, .bool])
    (fun (_, ok1a, ()) m1a => ∃ st1a : FullState,
      M7BvaStOk c F0 F_next s st1a ∧ (FullMem c st1a ⋆ R) m1a)
    (fun _ (_, ok1a, ()) m1a ⟨st1a, hst1a, hm1a⟩ => ?_) (fun J1a hJ1a => ?_)
  · have hp1b := m7_bva_phase1b_wp (Γ := Γ) (Q := Q) (X := X)
      hAddBin hAllocCl hWPush hDelBin hUnwatch (F_next := F_next)
      (fresh := fv_bv <<< (OfNat.ofNat 1 : BitVec 32)) (ok1a := ok1a)
      hinv hbk1 hbk32 hmat hmn_getD hfresh1_bv resAt
      (fun idx hidx => by
        have hspec := Classical.choose_spec (hbk_entries idx hidx)
        have heq : resAt idx = Classical.choose (hbk_entries idx hidx) := by
          dsimp only [resAt]; rw [dite_eq_left hidx]
        rw [heq]; refine ⟨hspec.1, hspec.2.1, hspec.2.2.1, ?_⟩
        have hmem : resAt idx ∈ Qs := List.mem_map.mpr ⟨idx, List.mem_range.mpr hidx, rfl⟩
        have h1 := hneg_ent (resAt idx) hmem; rwa [heq] at h1)
      hst1a hm1a hQ
    dsimp only [m7BvaPhase1bExpr, m7BvaHdrExpr, m7BvaMidExpr, sSteps, sStep, sLet32, sLd64,
      sLd32, sGrp0, sGrp64_32, sGrp64_64_32, sGrp32b, sThen, sElse, sDummyTup, sDummyVal, i64, i32,
      full_bva_commit_fid_body] at hp1b
    exact hp1b
  · refine wp_loop_inv
      (fun (si, ()) msi => ∃ sts : FullState, si.toNat ≤ dm ∧
        M7BvaStOk c F0 F_next s sts ∧ (FullMem c sts ⋆ R) msi)
      (fun (si, _) _ => dm - si.toNat) (fun Js hJs => by
        c0_hsteps; exact hJs (0#32, ()) m ⟨st0, Nat.zero_le _,
          ⟨hinv0, rfl, hfueld, hsb1.trans hsbd, htm1.trans htmd, htr1.trans htrd, hmono0⟩, hm⟩)
      (fun Js (si, ()) msi ⟨sts, hsi_le, hsts, hmsi⟩ ihs => ?_)
    obtain ⟨hinvs, hcvs, hfuels, hsbs, htms, htrs, hmonos⟩ := hsts
    have hcls := hinvs.1.core_ok; have hscs := hinvs.1.scratch_ok; c0_hsteps
    · have hsi_lt : si.toNat < dm := by
        have h1 : si.toNat < (best_k + 1#32).toNat := (by assumption); omega
      have hsi1 : (si + 1#32).toNat = si.toNat + 1 := by simp only [bv_c0]; omega
      have hfs_sb : (BitVec.setWidth 64 si).toNat < sts.scratch.scratch_buf.length := by
        rw [bv64_setWidth_32, hscs.scratch_buf_len]; omega
      have hfs_getD : (sts.scratch.scratch_buf[(BitVec.setWidth 64 si).toNat]'hfs_sb).toNat =
          (s.scratch.scratch_buf[si.toNat]?.getD 0#32).toNat := by
        have h1 : sts.scratch.scratch_buf[(BitVec.setWidth 64 si).toNat]? =
            s.scratch.scratch_buf[si.toNat]? := by rw [hsbs, bv64_setWidth_32]
        rw [← h1, List.getElem?_eq_getElem hfs_sb, Option.getD_some]
      have hfs_lt : (sts.scratch.scratch_buf[(BitVec.setWidth 64 si).toNat]'hfs_sb).toNat <
          2 * old_cv := by
        rw [hfs_getD]; exact hL_lt _ (List.mem_map.mpr ⟨si.toNat, List.mem_range.mpr hsi_lt, rfl⟩)
      c0_hsteps; c0_call hAddBin
      refine ⟨c, F0, F_next, sts, R, rfl, hinvs.1, hinvs.2.1, hinvs.2.2.2.2.2.1,
        fun _ _ => by rw [hfresh_nat, hfs_getD]
                      exact hpos_ent _ (List.mem_map.mpr ⟨si.toNat, List.mem_range.mpr hsi_lt,
                        rfl⟩),
        hmsi, fun _ _ fl_s1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ms1 hlen_s1 hw_s1 _ _ _ hms1 => ?_⟩
      have hinv_s1 := fullDenseInvW_of_addBin hinvs hlen_s1 hw_s1
      have hfs_shr : (BitVec.setWidth 64 ((sts.scratch.scratch_buf[(BitVec.setWidth 64
          si).toNat]'hfs_sb) >>> (1 : BitVec 32))).toNat < fl_s1.length := by
        rw [bv64_setWidth_32, bv32_lshr1_bv, hlen_s1.core_ok.flags_len]; omega
      have hfs_shr_n : (BitVec.setWidth 64 ((sts.scratch.scratch_buf[(BitVec.setWidth 64
          si).toNat]'hfs_sb) >>> (1 : Nat))).toNat < fl_s1.length := by
        rw [bv64_setWidth_32, bv32_lshr1_nat, hlen_s1.core_ok.flags_len]; omega
      c0_hsteps
      · exact hJ1a (si, false, ()) ms1 ⟨_, ⟨hinv_s1, hcvs, hfuels, hsbs, htms, htrs, hmonos⟩, hms1⟩
      · exact hJ1a (si, false, ()) ms1 ⟨_, ⟨hinv_s1, hcvs, hfuels, hsbs, htms, htrs, hmonos⟩, hms1⟩
      · exact hJ1a (si, false, ()) ms1 ⟨_, ⟨hinv_s1, hcvs, hfuels, hsbs, htms, htrs, hmonos⟩, hms1⟩
      · exact ihs (si + 1#32, ()) m (by dsimp only; rw [hsi1]; omega)
          ⟨_, by rw [hsi1]; omega,
           ⟨fullDenseInvW_set_flags hinv_s1 (by simp [hlen_s1.core_ok.flags_len]),
            hcvs, hfuels, hsbs, htms, htrs, hmonos⟩, hm⟩
    · exact hJ1a (si, true, ()) msi ⟨sts, ⟨hinvs, hcvs, hfuels, hsbs, htms, htrs, hmonos⟩, hmsi⟩

/-- `full_bva_commit_fid` (`G1-P2.1b` `u64` copy + `cnt` zeroing loops, `FL_FACT_P = 32u`,
`FL_FACT_N = 64u`) satisfies canonical `FullM4Bva.m4BvaCommitSpec` parametrically in `Γ`. -/
theorem full_bva_commit_fid_wp (Γ : Env)
    (hDefrag : ∀ args m Q X, Full.fullWstackDefragSpec args m Q X →
      Γ "full_wstack_defrag" [i64] [] args m Q X)
    (hInitFresh : ∀ args m Q X, fullInitFreshVarHeapSpec args m Q X →
      Γ "full_init_fresh_var" [i64, i32] [] args m Q X)
    (hAddBin : ∀ args m Q X, Full.fullAddBinSpec args m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] args m Q X)
    (hAllocCl : ∀ args m Q X, Full.fullAllocClSpec args m Q X →
      Γ "full_alloc_cl" [i64, i32, i32, .bool] [i64] args m Q X)
    (hWPush : ∀ args m Q X, Full.fullWatchPushSpec args m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] args m Q X)
    (hDelBin : ∀ args m Q X, Full.fullDeleteBinarySpec args m Q X →
      Γ "full_delete_binary" [i64, i32, i32] [] args m Q X)
    (hUnwatch : ∀ args m Q X, Full.fullUnwatchLargeSpec args m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] args m Q X) :
    ∀ args m Q X, m4BvaCommitSpec args m Q X → Func.wp Γ full_bva_commit_fid_body args m Q X := by
  rintro ⟨h, best_k, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hinv, hbk1, hbk32, hmat, hm, hQ⟩
  have hmx := c.hmaxv; have hwcap := c.hwcap; have har_b := c.harena; have hscr_b := c.hscr
  unfold dimacsBound at hmx hwcap har_b hscr_b
  have hcl := hinv.1.core_ok; have hsc := hinv.1.scratch_ok
  have hcv_le := hcl.cur_vars_le; have hsb_len := hsc.scratch_buf_len; have hwv_len := hcl.wvec_len
  have hscr16448 := hmat.1; have hbk_row := hmat.2.2.2 best_k.toNat (by omega)
  obtain ⟨hfbk_lt, hmn_lo, hmn_hi, hbk_entries⟩ := hbk_row
  have h32bk : ((32 : BitVec 32) + best_k).toNat = 32 + best_k.toNat := by c0_bound
  let mn_bv := s.scratch.scratch_buf[32 + best_k.toNat]'(by omega)
  have hmn_getD : (s.scratch.scratch_buf[32 + best_k.toNat]?.getD 0#32).toNat = mn_bv.toNat := by
    dsimp only [mn_bv]; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  rw [hmn_getD] at hmn_lo hmn_hi hbk_entries
  have hmn_eq : s.scratch.scratch_buf[(BitVec.setWidth 64 (32 + best_k)).toNat]'(by
      rw [bv64_setWidth_32, h32bk]; omega) = mn_bv := by
    dsimp only [mn_bv]; simp only [bv64_setWidth_32, h32bk]
  have h32bk_mod : (BitVec.toNat (32 : BitVec 32) + best_k.toNat) % 2 ^ 32 = 32 + best_k.toNat := by
    rw [show BitVec.toNat (32 : BitVec 32) = 32 from rfl]; omega
  let dm := best_k.toNat + 1
  have hdm_bv : (best_k + 1#32).toNat = dm := by simp only [bv_c0, dm]; omega
  c0_hsteps_nogrp
  · exact hQ false s m hinv.toDense (Nat.le_refl _) rfl rfl rfl hm
  · refine wp_loop_inv (fun (_need_w, si, ()) msi => m = msi ∧ si.toNat ≤ dm)
      (fun (_, si, _) _ => dm - si.toNat)
      (fun Jsi hJsi => by c0_hsteps; exact hJsi (_, 0#32, ()) m ⟨rfl, Nat.zero_le _⟩)
      (fun Jsi (need_w0, si, ()) msi ⟨hmsi, hsi_le⟩ ihsi => ?_)
    rcases hmsi with rfl; c0_hsteps_nogrp
    · have hsi_lt : si.toNat < dm := by
        have h1 : si.toNat < (best_k + 1#32).toNat := (by assumption); omega
      have hsi1 : (si + 1#32).toNat = si.toNat + 1 := by c0_bound
      have hfs_sb : (BitVec.setWidth 64 si).toNat < s.scratch.scratch_buf.length := by
        rw [bv64_setWidth_32, hsb_len]; omega
      have hfs_lt : (s.scratch.scratch_buf[si.toNat]'(by omega)).toNat < 2 * s.core.cur_vars := by
        have h1 := (hmat.2.2.2 si.toNat (by omega)).1
        simpa only [List.getElem?_eq_getElem (by omega : si.toNat < s.scratch.scratch_buf.length),
          Option.getD_some] using h1
      have hfs_wv : ((BitVec.setWidth 64
          (s.scratch.scratch_buf[(BitVec.setWidth 64 si).toNat]'hfs_sb) <<< (1 : Nat)) + 1).toNat <
          s.core.wvec.length := by
        rw [hwv_len]; simp only [bv_c0, show (1 : BitVec 64).toNat = 1 from rfl]; omega
      c0_hsteps; exact ihsi (_, si + 1#32, ()) m (by dsimp only; rw [hsi1]; omega)
        ⟨rfl, by rw [hsi1]; omega⟩
    · refine wp_loop_inv
        (fun (_need_ar, _need_w, mi, ()) mm => m = mm ∧ mi.toNat ≤ mn_bv.toNat)
        (fun (_, _, mi, _) _ => mn_bv.toNat - mi.toNat) (fun Jpre hJpre => by
          c0_hsteps; exact hJpre (16#64, need_w0, 0#32, ()) m ⟨rfl, Nat.zero_le _⟩)
        (fun Jpre (need_ar, need_w, mi, ()) mm ⟨hmm, hmi_le⟩ ihpre => ?_)
      rcases hmm with rfl; c0_hsteps_nogrp
      · have hmi_lt : mi.toNat < mn_bv.toNat := by
          have h1 : mi.toNat < (s.scratch.scratch_buf[(BitVec.toNat (32 : BitVec 32) +
              best_k.toNat) % 2 ^ 32]'(by rw [h32bk_mod]; omega)).toNat := by assumption
          simpa only [mn_bv, h32bk_mod] using h1
        have hmi1 : (mi + 1#32).toNat = mi.toNat + 1 := by c0_bound
        have hctop_idx : (64 + best_k * 256 + mi).toNat = 64 + best_k.toNat * 256 + mi.toNat := by
          change (64#32 + best_k * 256#32 + mi).toNat = _; c0_bound
        have hctop_sb : (BitVec.setWidth 64 (64 + best_k * 256 + mi)).toNat <
            s.scratch.scratch_buf.length := by rw [bv64_setWidth_32, hctop_idx, hsb_len]; omega
        let c_top := s.scratch.scratch_buf[64 + best_k.toNat * 256 + mi.toNat]'(by omega)
        have hctop_eq : s.scratch.scratch_buf[(BitVec.setWidth 64
            (64 + best_k * 256 + mi)).toNat]'hctop_sb = c_top := by
          dsimp only [c_top]; simp only [bv64_setWidth_32, hctop_idx]
        have hctop_mod_n : (64 + best_k.toNat * 256 + mi.toNat) % 2 ^ 32 =
            64 + best_k.toNat * 256 + mi.toNat := Nat.mod_eq_of_lt (by omega)
        have hctop_mod : s.scratch.scratch_buf[(BitVec.toNat (64 : BitVec 32) +
            best_k.toNat * BitVec.toNat (256 : BitVec 32) + mi.toNat) % 2 ^ 32]'(by
            rw [show BitVec.toNat (64 : BitVec 32) = 64 from rfl,
              show BitVec.toNat (256 : BitVec 32) = 256 from rfl, hctop_mod_n, hsb_len]; omega) =
            c_top := by
          dsimp only [c_top]; simp only [show BitVec.toNat (64 : BitVec 32) = 64 from rfl,
            show BitVec.toNat (256 : BitVec 32) = 256 from rfl, hctop_mod_n]
        obtain ⟨_, _, _, hctop_ok, _, _⟩ := hbk_entries mi.toNat hmi_lt
        have hctop_getD : s.scratch.scratch_buf[64 + best_k.toNat * 256 + mi.toNat]?.getD 0#32 =
            c_top := by
              dsimp only [c_top]; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
        rw [hctop_getD] at hctop_ok; c0_hsteps_nogrp
        refine wp_join_state_pure (ts := [i64, i64]) (α := BitVec 64 × BitVec 64)
          (fun p => (p.1, p.2, ())) (fun _ => True) (fun _ ⟨na', nw'⟩ _ => by
            c0_hsteps; exact ihpre (na', nw', mi + 1#32, ()) m (by dsimp only; rw [hmi1]; omega)
              ⟨rfl, by rw [hmi1]; omega⟩)
          (fun Jpn hJpn => ?_)
        c0_hsplit
        · have hbin_ct : (c_top &&& 0x80000000#32) ≠ 0#32 := by
            simpa only [← hctop_mod] using (by assumption : _)
          unfold M4BvaRowEntryOk at hctop_ok; rw [ite_eq_left hbin_ct] at hctop_ok
          have hq_lt : (c_top &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars := hctop_ok.1
          have hq_wv : ((BitVec.setWidth 64 (s.scratch.scratch_buf[(BitVec.setWidth 64
              (64 + best_k * 256 + mi)).toNat]'hctop_sb &&& 0x7FFFFFFF#32) <<< (1 : Nat)) +
              1).toNat < s.core.wvec.length := by
            rw [hctop_eq, hwv_len]; simp only [bv_c0, show (1 : BitVec 64).toNat = 1 from rfl];
              omega
          c0_hsteps; exact hJpn (need_ar, _) trivial
        · have hbin_ct : (c_top &&& 0x80000000#32) = 0#32 := by
            simpa only [← hctop_mod] using (by assumption : _)
          unfold M4BvaRowEntryOk at hctop_ok; rw [ite_eq_right (fun h' => h' hbin_ct)] at hctop_ok
          obtain ⟨hct_ref0, hct_ng0, hct_sz3, hct_sz256, _, _, _⟩ := hctop_ok
          have hct_wf := hinv.2.1.arena.refs_wf c_top.toNat hct_ref0
          have hct2_n : (BitVec.setWidth 64 c_top + 2).toNat = c_top.toNat + 2 := by
            change (BitVec.setWidth 64 c_top + 2#64).toNat = _; c0_bound
          have hct2_ar : (BitVec.setWidth 64 (s.scratch.scratch_buf[(BitVec.setWidth 64
              (64 + best_k * 256 + mi)).toNat]'hctop_sb) + 2).toNat < s.core.arena.length := by
            rw [hctop_eq, hct2_n]; have := hcl.arena_len_le; have := hcl.arena_len_arr; omega
          let csz_bv := s.core.arena[c_top.toNat + 2]'(by
            have := hcl.arena_len_le; have := hcl.arena_len_arr; omega)
          have hcsz_eq : csz_bv.toNat = fullArenaClauseSizeCore s.core c_top.toNat := by
            unfold fullArenaClauseSizeCore; dsimp only [csz_bv]; rw [List.getElem?_eq_getElem (by
              have := hcl.arena_len_le; have := hcl.arena_len_arr; omega), Option.getD_some]
          have hbk_sb : (BitVec.setWidth 64 best_k).toNat < s.scratch.scratch_buf.length := by
            rw [bv64_setWidth_32, hsb_len]; omega
          c0_hsteps_nogrp
          refine wp_loop_inv (fun (_nw, ji, ()) mji => m = mji ∧ ji.toNat ≤ csz_bv.toNat)
            (fun (_, ji, _) _ => csz_bv.toNat - ji.toNat)
            (fun Jj hJj => by c0_hsteps; exact hJj (need_w, 0#32, ()) m ⟨rfl, Nat.zero_le _⟩)
            (fun Jj (nwj, ji, ()) mji ⟨hmji, hji_le⟩ ihj => ?_)
          rcases hmji with rfl; c0_hsteps_nogrp
          · have hct2_mod : (c_top.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 = c_top.toNat +
            2 := by rw [show BitVec.toNat (2 : BitVec 64) = 2 from rfl]; omega
            have hji_lt : ji.toNat < csz_bv.toNat := by
              dsimp only [csz_bv]
              have h1 : ji.toNat < (s.core.arena[(c_top.toNat + BitVec.toNat (2 : BitVec 64)) %
                  2 ^ 64]'(by rw [hct2_mod]; have := hcl.arena_len_le; have := hcl.arena_len_arr
                              omega)).toNat := by simpa only [← hctop_mod] using (by assumption : _)
              simpa only [hct2_mod] using h1
            have hji1 : (ji + 1#32).toNat = ji.toNat + 1 := by c0_bound
            have hctj_n : (BitVec.setWidth 64 c_top + 3 + BitVec.setWidth 64 ji).toNat =
                c_top.toNat + 3 + ji.toNat := by
              change (BitVec.setWidth 64 c_top + 3#64 + BitVec.setWidth 64 ji).toNat = _; c0_bound
            have hctj_ar : c_top.toNat + 3 + ji.toNat < s.core.arena.length := by
              have := hcl.arena_len_le; have := hcl.arena_len_arr; omega
            have hctj_ar_sb : (BitVec.setWidth 64 (s.scratch.scratch_buf[(BitVec.setWidth 64
                (64 + best_k * 256 + mi)).toNat]'hctop_sb) + 3 + BitVec.setWidth 64 ji).toNat <
                s.core.arena.length := by rw [hctop_eq, hctj_n]; exact hctj_ar
            have hlj_lt : (s.core.arena[c_top.toNat + 3 + ji.toNat]'hctj_ar).toNat <
                2 * s.core.cur_vars := by
              have h1 := FullBvaFwdHelpers.fullArenaClauseLitsCore_getElem (k := s.core)
                (r := c_top.toNat) (j := ji.toNat) (by omega) hctj_ar
              exact hinv.2.1.arena.lits_lt c_top.toNat hct_ref0 hct_ng0 _ (List.mem_of_getElem? h1)
            c0_hsteps_nogrp; refine wp_join_state_pure (ts := [i64]) (α := BitVec 64)
              (fun x => (x, ())) (fun _ => True) (fun _ nw' _ => by
                c0_hsteps; exact ihj (nw', ji + 1#32, ()) m (by dsimp only; rw [hji1]; omega)
                  ⟨rfl, by rw [hji1]; omega⟩)
              (fun Jlf hJlf => ?_)
            c0_hsplit
            · have hlj_wv : ((BitVec.setWidth 64 (s.core.arena[(BitVec.setWidth 64
                  (s.scratch.scratch_buf[(BitVec.setWidth 64
                    (64 + best_k * 256 + mi)).toNat]'hctop_sb) +
                  3 + BitVec.setWidth 64 ji).toNat]'hctj_ar_sb) <<< (1 : Nat)) + 1).toNat <
                  s.core.wvec.length := by
                have hlj_eq : s.core.arena[(BitVec.setWidth 64
                  (s.scratch.scratch_buf[(BitVec.setWidth
                    64 (64 + best_k * 256 + mi)).toNat]'hctop_sb) + 3 +
                    BitVec.setWidth 64 ji).toNat]'hctj_ar_sb =
                    s.core.arena[c_top.toNat + 3 + ji.toNat]'hctj_ar := by
                      simp only [hctop_eq, hctj_n]
                rw [hlj_eq, hwv_len]; simp only [bv_c0, show (1 : BitVec 64).toNat = 1 from rfl];
                  omega
              c0_hsteps; exact hJlf _ trivial
            · c0_hsteps; exact hJlf nwj trivial
          · exact hJpn (_, nwj) trivial
      · exact hQ false s m hinv.toDense (Nat.le_refl _) rfl rfl rfl hm
      · exact hQ false s m hinv.toDense (Nat.le_refl _) rfl rfl rfl hm
      · exact hQ false s m hinv.toDense (Nat.le_refl _) rfl rfl rfl hm
      · have hcv_lt : s.core.cur_vars < c.max_vars := by c0_bound
        refine wp_join_state0 (α := FullState) (fun sd md => (FullMem c sd ⋆ R) md ∧ M7BvaPreOk c
          F0 F_cur s sd)
          (fun _ sd md ⟨hmd, hsd⟩ => ?_) (fun Jdef hJdef => ?_)
        · have hpd := m7_bva_post_defrag_wp (Γ := Γ) (Q := Q) (X := X)
            hInitFresh hAddBin hAllocCl hWPush hDelBin hUnwatch
            (mn_bv := s.scratch.scratch_buf[(BitVec.setWidth 64 (32 + best_k)).toNat]'(by
              rw [bv64_setWidth_32, h32bk]; omega))
            hinv hbk1 hbk32 hmat hcv_lt (by rw [hmn_eq]; exact hmn_getD) hmd hsd hQ
          dsimp only [m7BvaPostDefragExpr, m7BvaHdrExpr, m7BvaMidExpr, sSteps, sStep, sLet32,
            sLd64, sLd32, sGrp0,
            sGrp64_32, sGrp64_64_32, sThen, sElse, sDummyTup, sDummyVal, i64, i32,
            full_bva_commit_fid_body] at hpd
          exact hpd
        · refine wp_join_state0 (α := Unit) (fun _ md => md = m)
            (fun _ _ md hmd => by
              subst md; refine wp_join_state0 (α := FullState)
                (fun sd md => (FullMem c sd ⋆ R) md ∧ M7BvaPreOk c F0 F_cur s sd)
                (fun _ sd md ⟨hmd, hinvd, hcvd, hfueld, hard, hald, hsbd, htmd, htrd⟩ => by
                  refine wp_join_state0 (α := Unit) (fun _ mf => mf = md)
                    (fun _ _ mf hmf => by
                      subst mf; c0_hsteps_nogrp
                      have h2cv : (BitVec.ofNat 64 sd.core.cur_vars <<< (1 : Nat)).toNat =
                          2 * s.core.cur_vars := by rw [hcvd]; simp only [bv_c0]; omega
                      exact fid_bva_zero_cnt_wp (n := s.core.cur_vars) (by omega) h2cv
                        hinvd.1.scratch_ok.wsort_len hmd (fun wsz mzi hwsz_l hmzi => by
                          c0_hfast
                          exact hQ false _ mzi (fullDenseInvW_set_wsort hinvd hwsz_l).toDense
                            (by dsimp only; omega) hfueld htmd htrd hmzi))
                    (fun Jfail hJfail => by
                      c0_hsteps
                      · exact hJfail () md rfl
                      · exact hJfail () md rfl
                      · exact hJdef sd md ⟨hmd, hinvd, hcvd, hfueld, hard, hald, hsbd, htmd, htrd⟩))
                (fun Jd1 hJd1 => by
                  c0_hsteps
                  · c0_call hDefrag
                    refine ⟨c, s, R, rfl, hinv.1, hinv.2.1.watches.layout, hm,
                      fun wvec' wstk' wlen' wsort' md hlen' hlay' _ hsl' hmd =>
                        hJd1 _ md ⟨hmd, fullDenseInvW_of_defrag hinv hlen' hlay' hsl',
                          rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
                  · exact hJd1 s m ⟨hm, hinv, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩))
            (fun Jneed hJneed => by
              c0_hsteps
              · exact hJneed () m rfl
              · exact hJneed () m rfl
              · exact hJdef s m ⟨hm, hinv, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

end M7BvaProof

end LeanQbe.T.Examples.Kissat.FullFidelityVivK6
