module

public import LeanQbe.T.Examples.Kissat.FullBvaHeapSpec
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` 3-Hop BVA — Commit Shared Helpers & Sub-Proof Contracts

Shared arena monotonicity, preservation helpers, HOAS sub-expression fragments, and contracts
for `FullBvaHeapLemmas{4a,4b,4}` so commit sub-proofs compile in parallel.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullBvaHeap

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test
open FullBvaHeapTactics FullBvaHeapHelpers FullBvaHeapScanHelpers
open scoped FullArenaTactics FullBvaHeapTactics

section FullBvaHeapCommitHelpers

theorem nodup_lt_length_le : ∀ {n : Nat} {xs : List Nat},
    xs.Nodup → (∀ x ∈ xs, x < n) → xs.length ≤ n
  | 0, [], _, _ => Nat.zero_le _
  | 0, x :: _, _, hlt => absurd (hlt x (by simp)) (by omega)
  | n + 1, xs, hnd, hlt => by
    by_cases hn : n ∈ xs
    · have hperm := List.perm_cons_erase hn
      have hnd' := List.nodup_cons.mp (hnd.perm hperm)
      have hlt' : ∀ y ∈ xs.erase n, y < n := fun y hy => by
        have hmem : y ∈ xs := List.mem_of_mem_erase hy
        have hne : y ≠ n := fun he => by subst he; exact hnd'.1 hy
        have := hlt y hmem; omega
      have ih := nodup_lt_length_le hnd'.2 hlt'
      have hlen := hperm.length_eq; simp only [List.length_cons] at hlen; omega
    · have hlt' : ∀ y ∈ xs, y < n := fun y hy => by
        have hne : y ≠ n := fun he => by subst he; exact hn hy
        have := hlt y hy; omega
      exact Nat.le_trans (nodup_lt_length_le hnd hlt') (Nat.le_succ _)

/-- Monotonicity of existing arena clauses across clause appends and `PH_GARB` marks. -/
@[expose] def ArenaMono (k0 k : FullCoreState) : Prop :=
  ∀ r ∈ fullArenaClauseRefsCore k0,
    r ∈ fullArenaClauseRefsCore k ∧
    fullArenaClauseSizeCore k r = fullArenaClauseSizeCore k0 r ∧
    fullArenaClauseLitsCore k r = fullArenaClauseLitsCore k0 r

theorem arenaMono_refl (k : FullCoreState) : ArenaMono k k :=
  fun _ hr => ⟨hr, rfl, rfl⟩

theorem arenaMono_trans {k0 k1 k2 : FullCoreState}
    (h01 : ArenaMono k0 k1) (h12 : ArenaMono k1 k2) : ArenaMono k0 k2 := fun r hr => by
  obtain ⟨hr1, hsz1, hl1⟩ := h01 r hr
  obtain ⟨hr2, hsz2, hl2⟩ := h12 r hr1
  exact ⟨hr2, hsz2.trans hsz1, hl2.trans hl1⟩

theorem denseWatchSliceOk_congr {F_cur : List (List Nat)} {k k' : FullCoreState}
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

theorem fullDenseInvW_of_defrag {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {wvec' wstk' wsort' : List (BitVec 32)} {wlen' : Nat}
    (hlen' : ({ s with
      core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 }
      scratch := { s.scratch with wsort := wsort' } } : FullState).LengthsOk c)
    (hlay' : WatchStackLayout
      { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 })
    (hsl : ∀ l < 2 * s.core.cur_vars,
      fullWatchSizeCore { s.core with wvec := wvec', wstk := wstk', wlen := wlen',
                                      wusable := 0#64 } l = fullWatchSizeCore s.core l ∧
      ∀ k < fullWatchSizeCore s.core l,
        wstk'[fullWatchOffCore { s.core with wvec := wvec', wstk := wstk', wlen := wlen',
                                             wusable := 0#64 } l + k]? =
        s.core.wstk[fullWatchOffCore s.core l + k]?) :
    FullDenseInvW c F0 F_cur
      { s with
        core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 }
        scratch := { s.scratch with wsort := wsort' } } := by
  have hdm := hinv.2.2.2.2.2.2
  have hdw : DenseWatchesInv F_cur s.core := by
    have h := hinv.2.1.watches; unfold ModeWatchesInv at h; rwa [ite_eq_right hdm] at h
  let k' : FullCoreState :=
    { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 }
  have hdw' : DenseWatchesInv F_cur k' :=
    DenseWatchesInv.of_slices hlay'.bounds hlay'.pos_off hlay'.disjoint fun l hl => by
      obtain ⟨hsz, hget⟩ := hsl l hl
      rw [hsz]
      exact denseWatchSliceOk_congr (k := s.core) (k' := k') rfl rfl (fun j hj => hget j hj)
        (hdw.slices l hl)
  refine ⟨hlen', { hinv.2.1 with
    arena := { hinv.2.1.arena with len_ok := hinv.2.1.arena.len_ok }
    watches := by unfold ModeWatchesInv; rw [ite_eq_right hdm]; exact hdw' },
    hinv.2.2.1, hinv.2.2.2.1, hinv.2.2.2.2.1, hinv.2.2.2.2.2.1, hdm⟩

theorem fullDenseInvW_of_addBin {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {vals' : List (BitVec 8)} {flags' lvl' rsns' trl' tp' wvec' wstk' wsort' : List (BitVec 32)}
    {ph' : List (BitVec 8)} {te' wlen' : Nat} {unass' unfl' wu' nb' oom' inc' : BitVec 64}
    (hlen' : ({ s with
      core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                            trl := trl', trail_pos := tp', trail_end := te', unassigned := unass',
                            unflushed := unfl', wvec := wvec', wstk := wstk', wlen := wlen',
                            wusable := wu', num_binary := nb', oom := oom', inconsistent := inc' }
      scratch := { s.scratch with phases := ph', wsort := wsort' } } : FullState).LengthsOk c)
    (hw' : FullWitnessInv c F0 F_cur
      { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
                    trail_pos := tp', trail_end := te', unassigned := unass', unflushed := unfl',
                    wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu', num_binary := nb',
                    oom := oom', inconsistent := inc' }) :
    FullDenseInvW c F0 F_cur
      { s with
        core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                              trl := trl', trail_pos := tp', trail_end := te', unassigned := unass',
                              unflushed := unfl', wvec := wvec', wstk := wstk', wlen := wlen',
                              wusable := wu', num_binary := nb', oom := oom', inconsistent := inc' }
        scratch := { s.scratch with phases := ph', wsort := wsort' } } :=
  ⟨hlen', hw', hinv.2.2.1, hinv.2.2.2.1, hinv.2.2.2.2.1, hinv.2.2.2.2.2.1, hinv.2.2.2.2.2.2⟩

theorem fullDenseInvW_of_delBin {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {wvec' wstk' : List (BitVec 32)} {wu' nb' : BitVec 64}
    (hlen' : ({ s with core := { s.core with wvec := wvec', wstk := wstk',
                                             wusable := wu', num_binary := nb' } } :
      FullState).LengthsOk c)
    (hwat' : ModeWatchesInv F_cur
      { s.core with wvec := wvec', wstk := wstk', wusable := wu', num_binary := nb' }) :
    FullDenseInvW c F0 F_cur
      { s with core := { s.core with wvec := wvec', wstk := wstk',
                                     wusable := wu', num_binary := nb' } } :=
  ⟨hlen', { hinv.2.1 with
    arena := { hinv.2.1.arena with len_ok := hinv.2.1.arena.len_ok }, watches := hwat' },
   hinv.2.2.1, hinv.2.2.2.1, hinv.2.2.2.2.1, hinv.2.2.2.2.2.1, hinv.2.2.2.2.2.2⟩

theorem fullDenseInvW_of_unwatchLarge {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {wvec' wstk' : List (BitVec 32)} {wu' : BitVec 64}
    (hlen' : ({ s with core := { s.core with wvec := wvec', wstk := wstk',
                                             wusable := wu' } } : FullState).LengthsOk c)
    (hwat' : ModeWatchesInv F_cur
      { s.core with wvec := wvec', wstk := wstk', wusable := wu' }) :
    FullDenseInvW c F0 F_cur
      { s with core := { s.core with wvec := wvec', wstk := wstk', wusable := wu' } } :=
  ⟨hlen', { hinv.2.1 with
    arena := { hinv.2.1.arena with len_ok := hinv.2.1.arena.len_ok }, watches := hwat' },
   hinv.2.2.1, hinv.2.2.2.1, hinv.2.2.2.2.1, hinv.2.2.2.2.2.1, hinv.2.2.2.2.2.2⟩

theorem fullDenseInvW_of_markGarb {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {cref : Nat} (href : cref ∈ fullArenaClauseRefsCore s.core) (ag' : BitVec 64) :
    let ar' := s.core.arena.set cref (fullArenaHdrCore s.core cref ||| 0x00080000#32)
    let s' : FullState := { s with core := { s.core with arena := ar', arena_garbage := ag' } }
    FullDenseInvW c F0 F_cur s' ∧ ArenaMono s.core s'.core := by
  intro ar' s'
  have hcl := hinv.1.core_ok
  have hwf := hinv.2.1.arena.refs_wf cref href
  have hcref_lt : cref < s.core.arena.length := by
    have := hcl.arena_len_le; have := hcl.arena_len_arr; omega
  have h0 : ar'[cref]? = some (fullArenaHdrCore s.core cref ||| 0x00080000#32) :=
    List.getElem?_set_self hcref_lt
  have hout : ∀ i, i ≠ cref → (i < cref + 3 ∨ cref + 3 + fullArenaClauseSizeCore s.core cref ≤ i) →
      ar'[i]? = s.core.arena[i]? := fun i hne _ => List.getElem?_set_ne (Ne.symm hne)
  have ⟨hclen', hrefs', hw', hother, hgarb_cref⟩ :=
    FullBvaFwdHelpers.fullWitnessInv_markGarb_at_root (ag' := ag')
      hcl hinv.2.1 hinv.2.2.2.2.2.1 href (by simp [ar', hcl.arena_len_arr]) h0 hout
  have hnodup' : FullArenaVarsNodup s' :=
    FullArenaVarsNodup.of_markGarb hinv.toDense.1 hinv.2.2.2.1 href ag'
  have hext' : FullExtScratchOk c s' :=
    ⟨fun i hi => by
      rcases hinv.2.2.2.2.1.1 i hi with h1 | h2
      · exact Or.inl h1
      · exact Or.inr (by change _ ∈ fullArenaClauseRefsCore s'.core; rw [hrefs']; exact h2),
     hinv.2.2.2.2.1.2⟩
  refine ⟨⟨⟨hclen', hinv.1.scratch_ok⟩, hw', hinv.2.2.1, hnodup', hext',
    hinv.2.2.2.2.2.1, hinv.2.2.2.2.2.2⟩, fun r hr => ?_⟩
  refine ⟨by rw [hrefs']; exact hr, ?_, ?_⟩
  · unfold fullArenaClauseSizeCore; dsimp only [s', ar']
    by_cases hrc : r = cref
    · subst hrc; rw [List.getElem?_set_ne (by omega)]
    · have hwf_r := hinv.2.1.arena.refs_wf r hr
      rcases Nat.lt_or_gt_of_ne hrc with hlt | hgt
      · have := fullArenaScanRefs_disjoint hr href hlt
        rw [List.getElem?_set_ne (by omega)]
      · have := fullArenaScanRefs_disjoint href hr hgt
        rw [List.getElem?_set_ne (by omega)]
  · by_cases hrc : r = cref
    · subst hrc
      have hsz_eq : fullArenaClauseSizeCore s'.core r = fullArenaClauseSizeCore s.core r := by
        unfold fullArenaClauseSizeCore; dsimp only [s', ar']; rw [List.getElem?_set_ne (by omega)]
      exact fullArenaClauseLitsCore_congr hsz_eq fun j _ =>
        List.getElem?_set_ne (by omega)
    · exact (hother r hr hrc).2

theorem fullDenseInvW_of_append_clause {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {sz : Nat} (hsz3 : 3 ≤ sz)
    {ar' wvec' wstk' fl' wsort' : List (BitVec 32)} {wlen' : Nat} {wu' ni' : BitVec 64}
    (hlen' : ({ s with
      core := { s.core with arena := ar', arena_len := s.core.arena_len + 3 + sz,
                            wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu',
                            flags := fl', num_irred := ni' }
      scratch := { s.scratch with wsort := wsort' } } : FullState).LengthsOk c)
    (hhold : ∀ i < s.core.arena_len, ar'[i]? = s.core.arena[i]?)
    (hns : (ar'[s.core.arena_len]?.getD 0#32 &&& 0x00800000#32) = 0#32)
    (hsz_new : (ar'[s.core.arena_len + 2]?.getD 0#32).toNat = sz)
    (hlits_lt : ∀ l ∈ fullArenaClauseLitsCore { s.core with arena := ar' } s.core.arena_len,
      l < 2 * s.core.cur_vars)
    (hlits_nd : ((fullArenaClauseLitsCore { s.core with arena := ar' }
      s.core.arena_len).map (· / 2)).Nodup)
    (hlits_ent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (fullArenaClauseLitsCore { s.core with arena := ar' } s.core.arena_len)))
    (hwat' : ModeWatchesInv F_cur
      { s.core with arena := ar', arena_len := s.core.arena_len + 3 + sz,
                    wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu',
                    flags := fl', num_irred := ni' }) :
    let s' : FullState :=
      { s with
        core := { s.core with arena := ar', arena_len := s.core.arena_len + 3 + sz,
                              wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu',
                              flags := fl', num_irred := ni' }
        scratch := { s.scratch with wsort := wsort' } }
    FullDenseInvW c F0 F_cur s' ∧ ArenaMono s.core s'.core := by
  intro s'
  have hw := hinv.2.1; have hcl := hinv.1.core_ok
  have hnxt_hold := hw.arena.arenaNextOff_extend (alen' := s.core.arena_len + 3 + sz)
    (by omega) hhold
  have hrefs : fullArenaClauseRefsCore s'.core =
      fullArenaClauseRefsCore s.core ++ [s.core.arena_len] :=
    fullArenaClauseRefsCore_append hw.arena hsz3 rfl hhold hns hsz_new
  have hold_garb : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseGarbCore s'.core r = fullArenaClauseGarbCore s.core r := fun r hr => by
    have := (hw.arena.refs_wf r hr).1
    unfold fullArenaClauseGarbCore fullArenaHdrCore s'; simp [hhold r (by omega)]
  have hold_sz : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseSizeCore s'.core r = fullArenaClauseSizeCore s.core r := fun r hr => by
    have := (hw.arena.refs_wf r hr).1
    unfold fullArenaClauseSizeCore s'; simp [hhold (r + 2) (by omega)]
  have hold_lits : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s.core r := fun r hr => by
    have hwf := hw.arena.refs_wf r hr
    exact fullArenaClauseLitsCore_congr (hold_sz r hr) fun j hj => hhold (r + 3 + j) (by omega)
  have harena' : FullArenaClausesInv c F_cur s'.core := by
    refine ⟨Or.inr (by dsimp [s']; omega), ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · have hwf := hw.arena.refs_wf r hr
        rw [hnxt_hold r hr, hold_sz r hr]
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
          unfold fullArenaHdrCore at hsh ⊢; dsimp only [s'] at hsh
          rwa [hhold r (by omega)] at hsh
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
    fun idx hidx => hw.level0_rsn_none idx hidx
      (by have := hw.lvl_le idx hidx; have := hinv.2.2.2.2.2.1; omega)
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { hw with
      arena := harena', watches := hwat'
      reason_inv := fun idx hidx hne => absurd (hno_rsn idx hidx) hne
      reason_lit_mem := fun idx hidx hne _ => absurd (hno_rsn idx hidx) hne }
  have hnodup' : FullArenaVarsNodup s' := fun r hr hng => by
    change r ∈ fullArenaClauseRefsCore s'.core at hr
    rw [hrefs, List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | rfl
    · change fullArenaClauseGarbCore s'.core r = false at hng
      rw [hold_garb r hr] at hng
      change ((fullArenaClauseLitsCore s'.core r).map (· / 2)).Nodup
      rw [hold_lits r hr]; exact hinv.2.2.2.1 r hr hng
    · exact hlits_nd
  have hext' : FullExtScratchOk c s' :=
    ⟨fun i hi => by
      rcases hinv.2.2.2.2.1.1 i hi with h1 | h2
      · exact Or.inl h1
      · exact Or.inr (by
          change _ ∈ fullArenaClauseRefsCore s'.core
          rw [hrefs]; exact List.mem_append_left _ h2),
     hinv.2.2.2.2.1.2⟩
  exact ⟨⟨hlen', hw', hinv.2.2.1, hnodup', hext', hinv.2.2.2.2.2.1, hinv.2.2.2.2.2.2⟩,
    fun r hr => ⟨by rw [hrefs]; exact List.mem_append_left _ hr, hold_sz r hr, hold_lits r hr⟩⟩

theorem fullArenaLitsCore_eq_map {k : FullCoreState} {r sz : Nat}
    (hsz : fullArenaClauseSizeCore k r = sz) (hb : r + 3 + sz ≤ k.arena.length) :
    fullArenaClauseLitsCore k r =
      (List.range sz).map (fun j => (k.arena[r + 3 + j]?.getD 0#32).toNat) := by
  apply List.ext_getElem?; intro j
  by_cases hj : j < sz
  · rw [FullBvaFwdHelpers.fullArenaClauseLitsCore_getElem (by omega) (by omega),
      List.getElem?_map, List.getElem?_range hj, Option.map_some,
      List.getElem?_eq_getElem (by omega), Option.getD_some]
  · rw [List.getElem?_eq_none (by
        rw [FullBvaFwdHelpers.fullArenaClauseLitsCore_length (by omega), hsz]; omega),
      List.getElem?_eq_none (by simp; omega)]

theorem bv32_lit_mask_eq {x : BitVec 32} (h : x.toNat < 2 ^ 31) :
    (x &&& 0x7FFFFFFF#32) = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (0x7FFFFFFF#32).toNat = 2 ^ 31 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt h]

theorem bv32_shl1_xor1 {x : BitVec 32} (h : x.toNat < 2 ^ 31) :
    ((x <<< (1 : Nat)) ^^^ 1#32).toNat = 2 * x.toNat + 1 := by
  have hev : (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
    rw [bv32_shl1_nat, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_xor, show (1#32).toNat = 1 from rfl, hev]
  apply Nat.eq_of_testBit_eq; intro k
  cases k with
  | zero => simp [Nat.testBit_zero]
  | succ j =>
    rw [Nat.testBit_xor, show Nat.testBit 1 (j + 1) = false by rw [Nat.testBit_succ]; simp,
      Bool.xor_false, Nat.testBit_succ, Nat.testBit_succ,
      show (2 * x.toNat + 1) / 2 = (2 * x.toNat) / 2 by omega]

theorem bv32_shl1_or1 {x : BitVec 32} (h : x.toNat < 2 ^ 31) :
    ((x <<< (1 : Nat)) ||| 1#32).toNat = 2 * x.toNat + 1 := by
  have hev : (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
    rw [bv32_shl1_nat, Nat.mod_eq_of_lt (by omega)]
  rw [FullBvaFwdTactics.bv32_or1_of_even (by rw [hev]; omega), hev]

theorem fullDenseInvW_set_tmp {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {tmp' : List (BitVec 32)} (htmp : tmp'.length = c.max_vars) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with tmp := tmp' } } :=
  fullDenseInv_with_core_aux (tc' := s.core.tmp_cnt) (tl' := s.core.tmp_len) (sc' := s.scratch)
    hinv hinv.1.core_ok.repr_len hinv.1.core_ok.min_clr_len_arr htmp hinv.1.core_ok.flags_len
    hinv.1.core_ok.tmp_len_le hinv.1.scratch_ok rfl rfl

theorem fullDenseInvW_set_wsort {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {ws' : List (BitVec 32)} (hws : ws'.length = 2 * c.max_vars) :
    FullDenseInvW c F0 F_cur { s with scratch := { s.scratch with wsort := ws' } } :=
  fullDenseInv_with_core_aux (tc' := s.core.tmp_cnt) (tl' := s.core.tmp_len)
    (sc' := { s.scratch with wsort := ws' }) hinv hinv.1.core_ok.repr_len
    hinv.1.core_ok.min_clr_len_arr hinv.1.core_ok.tmp_len_arr hinv.1.core_ok.flags_len
    hinv.1.core_ok.tmp_len_le { hinv.1.scratch_ok with wsort_len := hws } rfl rfl

end FullBvaHeapCommitHelpers

/-! ## 2. `full_bva_commit_wp` -/

@[expose] def dummyVal : (t : Ty) → Val t
  | .bits _ => 0
  | .bool => true
  | .float _ => 0
  | .pair a b => (dummyVal a, dummyVal b)

@[expose] def dummyTup : (ts : List Ty) → Tup Val ts
  | [] => ()
  | t :: ts => (dummyVal t, dummyTup ts)

@[expose] def eStep {rs : List Ty} : Expr Val Cont rs → Expr Val Cont rs
  | .let_ (ts := ts) _ k => k (dummyTup ts)
  | .load t _ k => k (dummyVal t)
  | .store _ _ k => k
  | .call (bs := bs) _ _ k => k (dummyTup bs)
  | .jnz _ _ _ => .hlt
  | .jump _ _ => .hlt
  | .ret _ => .hlt
  | .exit _ _ => .hlt
  | .hlt => .hlt
  | .group _ _ => .hlt

@[expose] def eSteps {rs : List Ty} : Nat → Expr Val Cont rs → Expr Val Cont rs
  | 0, e => e
  | n + 1, e => eSteps n (eStep e)

@[expose] def eGrp0_0 {rs : List Ty} (J : Cont []) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[]]) bs _ => (match bs (J, ()) with | .cons f .nil => f ())
  | _ => .hlt

@[expose] def eGrpBody_0 {rs : List Ty} (J : Cont []) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[]]) _ body => body (J, ())
  | _ => .hlt

@[expose] def eGrp0_1 {rs : List Ty} (J : Cont [i32]) (x : Val i32) :
    Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32]]) bs _ => (match bs (J, ()) with | .cons f .nil => f (x, ()))
  | _ => .hlt

@[expose] def commitDelLoopExpr (h pAr pScr pFl : Val i64) (best_k mi : Val i32)
    (Jm : Cont [i32]) : Expr Val Cont [.bool] :=
  full_bva_commit_body Val Cont (h, best_k, ())
    |> eStep |> eLoad64 pAr
    |> eStep |> eLoad64 pScr
    |> eSteps 3 |> eLoad64 pFl
    |> eSteps 20 |> eElse
    |> eSteps 6 |> eElse
    |> eGrp0_0 (fun _ _ => True)
    |> eSteps 35
    |> eGrp0_1 Jm mi
    |> eStep |> eThen
    |> eSteps 7
    |> eGrp0_0 (fun _ _ => True)

@[expose] def commitLargeTopExpr (h pAr pScr pFl pTmp : Val i64) (best_k c_top fresh : Val i32)
    (Jtop : Cont []) : Expr Val Cont [.bool] :=
  full_bva_commit_body Val Cont (h, best_k, ())
    |> eStep |> eLoad64 pAr
    |> eStep |> eLoad64 pScr
    |> eSteps 3 |> eLoad64 pFl
    |> eSteps 20 |> eElse
    |> eSteps 6 |> eElse
    |> eGrp0_0 (fun _ _ => True)
    |> eSteps 32 |> eLet32 fresh |> eStep |> eLoad64 pTmp
    |> eGrp0_1 (fun _ _ => True) 0#32
    |> eStep |> eThen
    |> eSteps 6 |> eLoad32 c_top
    |> eGrpBody_0 Jtop
    |> eSteps 2 |> eElse

@[expose] def commitTailExpr (h pScr pCnt pFl : Val i64) (best_k dm fresh : Val i32) :
    Expr Val Cont [.bool] :=
  full_bva_commit_body Val Cont (h, best_k, ())
    |> eStep |> eLoad64 0#64
    |> eStep |> eLoad64 pScr
    |> eStep |> eLoad64 pCnt
    |> eStep |> eLoad64 pFl
    |> eLet32 dm
    |> eSteps 19 |> eElse
    |> eSteps 6 |> eElse
    |> eGrp0_0 (fun _ _ => True)
    |> eSteps 32 |> eLet32 fresh |> eSteps 2
    |> eGrp0_1 (fun _ _ => True) 0#32
    |> eStep |> eElse


@[expose] def CommitDelLoopWp (Γ : Env) (Q : Post [.bool]) (X : XPost)
    (_hDelBin : ∀ args m Q X, Full.fullDeleteBinarySpec args m Q X →
      Γ "full_delete_binary" [i64, i32, i32] [] args m Q X)
    (_hUnwatch : ∀ args m Q X, Full.fullUnwatchLargeSpec args m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] args m Q X) : Prop :=
  ∀ {c : FullCfg} {F0 : CNF Nat} {F_cur F_next : List (List Nat)} {s st1 : FullState}
    {R : Mem 64 → Prop} {best_k mi : Val i32} {Jm : Cont [i32]} {m1 : Mem 64},
    FullDenseInvW c F0 F_cur s →
    1 ≤ best_k.toNat → best_k.toNat < 16 →
    BvaMatrixInv c F_cur s (best_k.toNat + 1) →
    mi.toNat < (s.scratch.scratch_buf[16 + best_k.toNat]?.getD 0#32).toNat →
    (FullMem c st1 ⋆ R) m1 → FullDenseInvW c F0 F_next st1 →
    st1.core.cur_vars = s.core.cur_vars + 1 →
    st1.core.fuel = s.core.fuel →
    st1.scratch.scratch_buf = s.scratch.scratch_buf →
    st1.scratch.tarjan_mark = s.scratch.tarjan_mark →
    st1.scratch.tarjan_reach = s.scratch.tarjan_reach →
    ArenaMono s.core st1.core →
    (∀ st2 m2,
      FullDenseInvW c F0 F_next st2 →
      st2.core.cur_vars = s.core.cur_vars + 1 → st2.core.fuel = s.core.fuel →
      st2.scratch.scratch_buf = s.scratch.scratch_buf →
      st2.scratch.tarjan_mark = s.scratch.tarjan_mark →
      st2.scratch.tarjan_reach = s.scratch.tarjan_reach →
      ArenaMono s.core st2.core → (FullMem c st2 ⋆ R) m2 →
      Jm (mi + 1#32, ()) m2) →
    wp Γ Q X (commitDelLoopExpr c.hdr c.pArena c.pScratchBuf c.pFlags best_k mi Jm) m1

@[expose] def CommitLargeTopWp (Γ : Env) (Q : Post [.bool]) (X : XPost)
    (_hAllocCl : ∀ args m Q X, Full.fullAllocClSpec args m Q X →
      Γ "full_alloc_cl" [i64, i32, i32, .bool] [i64] args m Q X)
    (_hWPush : ∀ args m Q X, Full.fullWatchPushSpec args m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] args m Q X) : Prop :=
  ∀ {c : FullCfg} {F0 : CNF Nat} {F_cur F_next : List (List Nat)} {s stm : FullState}
    {R : Mem 64 → Prop} {best_k c_top fresh : Val i32} {Jtop : Cont []} {mm : Mem 64}
    {resm : List Nat},
    FullDenseInvW c F0 F_cur s →
    best_k.toNat < 16 → 2304 ≤ c.scratch_cap →
    (fresh ^^^ 1#32).toNat = 2 * s.core.cur_vars + 1 →
    (∀ x ∈ resm, x < 2 * s.core.cur_vars) →
    (resm.map (· / 2)).Nodup →
    (cnfOfClauses F_next).EntailsClause (cnfClause ((2 * s.core.cur_vars + 1) :: resm)) →
    c_top.toNat ∈ fullArenaClauseRefsCore s.core →
    fullArenaClauseGarbCore s.core c_top.toNat = false →
    3 ≤ fullArenaClauseSizeCore s.core c_top.toNat →
    fullArenaClauseSizeCore s.core c_top.toNat ≤ 5 →
    (s.scratch.scratch_buf[best_k.toNat]?.getD 0#32).toNat ∈
      fullArenaClauseLitsCore s.core c_top.toNat →
    resm.Perm ((fullArenaClauseLitsCore s.core c_top.toNat).filter
      (· != (s.scratch.scratch_buf[best_k.toNat]?.getD 0#32).toNat)) →
    (FullMem c stm ⋆ R) mm → FullDenseInvW c F0 F_next stm →
    stm.core.cur_vars = s.core.cur_vars + 1 → stm.core.fuel = s.core.fuel →
    stm.scratch.scratch_buf = s.scratch.scratch_buf →
    stm.scratch.tarjan_mark = s.scratch.tarjan_mark →
    stm.scratch.tarjan_reach = s.scratch.tarjan_reach →
    ArenaMono s.core stm.core →
    (∀ st1 m1,
      (FullMem c st1 ⋆ R) m1 → FullDenseInvW c F0 F_next st1 →
      st1.core.cur_vars = s.core.cur_vars + 1 → st1.core.fuel = s.core.fuel →
      st1.scratch.scratch_buf = s.scratch.scratch_buf →
      st1.scratch.tarjan_mark = s.scratch.tarjan_mark →
      st1.scratch.tarjan_reach = s.scratch.tarjan_reach →
      ArenaMono s.core st1.core → Jtop () m1) →
    wp Γ Q X (commitLargeTopExpr c.hdr c.pArena c.pScratchBuf c.pFlags c.pTmp
      best_k c_top fresh Jtop) mm

@[expose] def CommitTailWp (Γ : Env) (Q : Post [.bool]) (X : XPost)
    (_hAddBin : ∀ args m Q X, Full.fullAddBinSpec args m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] args m Q X) : Prop :=
  ∀ {c : FullCfg} {F0 : CNF Nat} {F_next : List (List Nat)} {s stm : FullState}
    {R : Mem 64 → Prop} {best_k dm_bv fresh : Val i32} {mm : Mem 64},
    best_k.toNat < 16 → 2304 ≤ c.scratch_cap →
    dm_bv.toNat = best_k.toNat + 1 →
    fresh.toNat = 2 * s.core.cur_vars →
    (∀ t < best_k.toNat + 1,
      (s.scratch.scratch_buf[t]?.getD 0#32).toNat < 2 * s.core.cur_vars) →
    (∀ t < best_k.toNat + 1,
      (cnfOfClauses F_next).EntailsClause
        (cnfClause [2 * s.core.cur_vars, (s.scratch.scratch_buf[t]?.getD 0#32).toNat])) →
    FullDenseInvW c F0 F_next stm →
    stm.core.cur_vars = s.core.cur_vars + 1 → stm.core.fuel = s.core.fuel →
    stm.scratch.scratch_buf = s.scratch.scratch_buf →
    stm.scratch.tarjan_mark = s.scratch.tarjan_mark →
    stm.scratch.tarjan_reach = s.scratch.tarjan_reach →
    (FullMem c stm ⋆ R) mm →
    (∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      FullDenseInv c F0 s' → s.core.cur_vars ≤ s'.core.cur_vars →
      s'.core.fuel = s.core.fuel →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') →
    wp Γ Q X (commitTailExpr c.hdr c.pScratchBuf c.pWsort c.pFlags best_k dm_bv fresh) mm

end LeanQbe.T.Examples.Kissat.FullBvaHeap
