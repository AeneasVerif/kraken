/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Dense.Helpers

/-!
# Kissat Large-Clause Watch Attachment WP Proof (`Proof.Dense.WpWatchLarge`)

Parametric `(Γ : Env)` `Func.wp` proof (`public section`, `0` `@[expose]` on
theorems/lemmas/sections, `0` legacy imports, `<= 100` cols) for:
1. `full_watch_large_clauses_fid` (`Spec.fullWatchLargeClausesSpec`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Dense

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Src.Dense
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics

local macro "dr_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

/-! ## 1. Loop Invariant & Pure State Preservation Lemmas -/

private structure WlInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s0 s : FullState) : Prop where
  lengths : s.LengthsOk c
  witness : FullWitnessInv c F0 F_cur s.core
  lm : FullLitMarksClear c s
  nd : FullArenaVarsNodup s
  extOk : FullExtScratchOk c s
  cv : s.core.cur_vars = s0.core.cur_vars
  cl : s.core.cur_level = s0.core.cur_level
  dm : s.core.dense_mode = s0.core.dense_mode
  alen : s.core.arena_len = s0.core.arena_len
  vals : s.core.vals = s0.core.vals
  lvl : s.core.lvl = s0.core.lvl
  flags : s.core.flags = s0.core.flags
  fuel : s.core.fuel = s0.core.fuel
  inc : s.core.inconsistent = s0.core.inconsistent
  dcur : s.core.d_cur = s0.core.d_cur
  dval : s.core.d_val = s0.core.d_val
  probing : s.core.probing = s0.core.probing
  perm : FullArenaPermEq s0.core s.core
  extLen : s.scratch.extend_len = s0.scratch.extend_len
  wvals : s.scratch.walk_vals = s0.scratch.walk_vals
  wbest : s.scratch.walk_best = s0.scratch.walk_best
  ll : s.scratch.last_learned = s0.scratch.last_learned

private theorem wl_arena_next_eq {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {sP : FullState} {p : BitVec 64} (hwP : FullWitnessInv c F0 F_cur sP.core)
    (hlenP : sP.LengthsOk c) (hp_in : p.toNat ∈ fullArenaClauseRefsCore sP.core) :
    let np : BitVec 64 := (BitVec.ofNat 32 (fullArenaNextOff sP.core.arena
      sP.core.arena_len (p.setWidth 32).toNat)).setWidth 64
    p.toNat < np.toNat ∧ np.toNat ≤ sP.core.arena_len ∧
    (np.toNat = sP.core.arena_len ∨ np.toNat ∈ fullArenaClauseRefsCore sP.core) := by
  have har_cap := c.harena; unfold dimacsBound at har_cap
  have hwf := hwP.arena.refs_wf p.toNat hp_in
  have hal := hlenP.core_ok.arena_len_le
  have hp_lt32 : p.toNat < 2 ^ 32 := by omega
  have hp_tr : (p.setWidth 32).toNat = p.toNat := by bv_omega
  have hnb := fullArenaNextOff_bounds (ar := sP.core.arena) (alen := sP.core.arena_len)
    (cref := p.toNat) hwf.1
  have hnxt := fullArenaClauseRefs_next_mem hwP.arena hp_in
  have hlt32 : fullArenaNextOff sP.core.arena sP.core.arena_len p.toNat < 2 ^ 32 := by omega
  have hlt64 : fullArenaNextOff sP.core.arena sP.core.arena_len p.toNat < 2 ^ 64 := by omega
  have hnp : ((BitVec.ofNat 32 (fullArenaNextOff sP.core.arena
      sP.core.arena_len (p.setWidth 32).toNat)).setWidth 64).toNat =
      fullArenaNextOff sP.core.arena sP.core.arena_len p.toNat := by
    rw [hp_tr, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt32]
    exact Nat.mod_eq_of_lt hlt64
  dsimp only; rw [hnp]; exact ⟨hnb.1, hnb.2, hnxt⟩

private theorem wl_swap_ok {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 sP : FullState} (hinvP : WlInv c F0 F_cur s0 sP)
    {p a b : Nat} (hp : p ∈ fullArenaClauseRefsCore sP.core)
    (ha : a < fullArenaClauseSizeCore sP.core p)
    (hb : b < fullArenaClauseSizeCore sP.core p)
    (hpa_lt : p + 3 + a < sP.core.arena.length)
    (hpb_lt : p + 3 + b < sP.core.arena.length) :
    let ar' := (sP.core.arena.set (p + 3 + a) (sP.core.arena[p + 3 + b]'hpb_lt)).set
      (p + 3 + b) (sP.core.arena[p + 3 + a]'hpa_lt)
    let s' : FullState := { sP with core := { sP.core with arena := ar' } }
    WlInv c F0 F_cur s0 s' ∧
    fullArenaClauseSizeCore s'.core p = fullArenaClauseSizeCore sP.core p ∧
    fullArenaClauseGarbCore s'.core p = fullArenaClauseGarbCore sP.core p := by
  intro ar' s'
  have hlenP := hinvP.lengths
  have hwP := hinvP.witness
  have hpwf := hwP.arena.refs_wf p hp
  have har_len : ar'.length = c.arena_cap := by
    dsimp only [ar']; simp [hlenP.core_ok.arena_len_arr]
  have hout : OutsideSliceAgrees (p + 1) (p + 3 + fullArenaClauseSizeCore sP.core p)
      sP.core.arena ar' := by
    intro j hj
    rcases hj with hlt | hge
    · dsimp only [ar']; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    · dsimp only [ar']; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  have h2 : ar'[p + 2]? = sP.core.arena[p + 2]? := by
    dsimp only [ar']; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  have hbd : p + 3 + fullArenaClauseSizeCore sP.core p ≤ sP.core.arena.length := by
    have := hpwf.2.2.1; have := hpwf.2.2.2.1
    have := hlenP.core_ok.arena_len_le; have := hlenP.core_ok.arena_len_arr; omega
  have hperm_raw := swapClauseLits_perm ha hb hbd
  have hsz_eq : fullArenaClauseSizeCore s'.core p = fullArenaClauseSizeCore sP.core p := by
    unfold fullArenaClauseSizeCore; dsimp only [s']; rw [h2]
  have hperm : List.Perm (fullArenaClauseLitsCore s'.core p)
      (fullArenaClauseLitsCore sP.core p) := by
    unfold fullArenaClauseLitsCore; rw [hsz_eq]; exact hperm_raw
  obtain ⟨hrefs, hmeta, hlits_other, hw'⟩ := modifyClauseBody_preserves_witness
    hlenP.core_ok hwP hp har_len hout h2 (fun _ => hperm.mem_iff)
  have hlen' : s'.LengthsOk c :=
    ⟨{ hlenP.core_ok with arena_len_arr := har_len }, hlenP.scratch_ok⟩
  have hnd' : FullArenaVarsNodup s' := fun r hr hng => by
    change r ∈ fullArenaClauseRefsCore s'.core at hr
    dsimp only [s'] at hr hrefs ⊢
    rw [hrefs] at hr
    change fullArenaClauseGarbCore s'.core r = false at hng
    dsimp only [s'] at hng; rw [(hmeta r hr).2.2] at hng
    change ((fullArenaClauseLitsCore s'.core r).map (· / 2)).Nodup
    by_cases hrp : r = p
    · subst r; exact (hperm.map (· / 2)).nodup_iff.mpr (hinvP.nd p hp hng)
    · dsimp only [s']; rw [hlits_other r hr hrp]; exact hinvP.nd r hr hng
  have hll' : FullLastLearnedWf s' :=
    hinvP.extOk.1.of_refs_subset rfl (fun r hr => by
      change r ∈ fullArenaClauseRefsCore s'.core; dsimp only [s']; rw [hrefs]; exact hr)
  have hpe : FullArenaPermEq sP.core s'.core := by
    refine ⟨rfl, ?_, fun r hr => ?_⟩
    · dsimp only [s']; exact hrefs
    · dsimp only [s']
      refine ⟨(hmeta r hr).2.1, (hmeta r hr).2.2, ?_⟩
      by_cases hrp : r = p
      · subst r; exact hperm
      · rw [hlits_other r hr hrp]
  refine ⟨⟨hlen', hw', hinvP.lm, hnd', ⟨hll', hinvP.extOk.2⟩,
    hinvP.cv, hinvP.cl, hinvP.dm, hinvP.alen, hinvP.vals, hinvP.lvl, hinvP.flags,
    hinvP.fuel, hinvP.inc, hinvP.dcur, hinvP.dval, hinvP.probing,
    dense_arenaPermEq_trans hinvP.perm hpe,
    hinvP.extLen, hinvP.wvals, hinvP.wbest, hinvP.ll⟩, hsz_eq, (hmeta p hp).2.2⟩

private theorem wl_swap_mem {c : FullCfg} {sP : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {a a' b b' : Nat} (ha : a = a') (hb : b = b')
    {hal : a < sP.core.arena.length} {hbl : b < sP.core.arena.length}
    {hal' : a' < sP.core.arena.length} {hbl' : b' < sP.core.arena.length}
    (hm : (FullMem c { sP with core := { sP.core with
      arena := (sP.core.arena.set a' (sP.core.arena[b']'hbl')).set
        b' (sP.core.arena[a']'hal') } } ⋆ R) m) :
    (FullMem c { sP with core := { sP.core with
      arena := (sP.core.arena.set a (sP.core.arena[b]'hbl)).set
        b (sP.core.arena[a]'hal) } } ⋆ R) m := by
  subst ha hb; exact hm

private theorem wl_set_hint_ok {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 sP : FullState} (hinvP : WlInv c F0 F_cur s0 sP)
    {p : Nat} (hp : p ∈ fullArenaClauseRefsCore sP.core) :
    let s' : FullState :=
      { sP with core := { sP.core with arena := sP.core.arena.set (p + 1) 2#32 } }
    WlInv c F0 F_cur s0 s' := by
  intro s'
  have hlenP := hinvP.lengths
  have hwP := hinvP.witness
  have hpwf := hwP.arena.refs_wf p hp
  have har_len : s'.core.arena.length = c.arena_cap := by
    dsimp only [s']; simp [hlenP.core_ok.arena_len_arr]
  have hout : OutsideSliceAgrees (p + 1) (p + 3 + fullArenaClauseSizeCore sP.core p)
      sP.core.arena s'.core.arena := fun j hj => by
    dsimp only [s']; rcases hj with _ | _
    · exact List.getElem?_set_ne (by omega)
    · exact List.getElem?_set_ne (by omega)
  have h2 : s'.core.arena[p + 2]? = sP.core.arena[p + 2]? := by
    dsimp only [s']; exact List.getElem?_set_ne (by omega)
  have hbd : p + 3 + fullArenaClauseSizeCore sP.core p ≤ sP.core.arena.length := by
    have := hpwf.2.2.1; have := hpwf.2.2.2.1
    have := hlenP.core_ok.arena_len_le; have := hlenP.core_ok.arena_len_arr; omega
  have hbd' : p + 3 + fullArenaClauseSizeCore s'.core p ≤ s'.core.arena.length := by
    unfold fullArenaClauseSizeCore; dsimp only [s'] at h2 ⊢
    rw [h2, List.length_set]; exact hbd
  have hsz_eq : fullArenaClauseSizeCore s'.core p = fullArenaClauseSizeCore sP.core p := by
    unfold fullArenaClauseSizeCore; dsimp only [s'] at h2 ⊢; rw [h2]
  have hlits_p : fullArenaClauseLitsCore s'.core p = fullArenaClauseLitsCore sP.core p :=
    fullArenaClauseLitsCore_eq_of_hold hbd (by rw [← hsz_eq]; exact hbd') hsz_eq
      fun j _ => by dsimp only [s']; exact List.getElem?_set_ne (by omega)
  obtain ⟨hrefs, hmeta, hlits_other, hw'⟩ := modifyClauseBody_preserves_witness
    hlenP.core_ok hwP hp har_len hout h2 (fun _ => by rw [hlits_p])
  have hlen' : s'.LengthsOk c :=
    ⟨{ hlenP.core_ok with arena_len_arr := har_len }, hlenP.scratch_ok⟩
  have hnd' : FullArenaVarsNodup s' := fun r hr hng => by
    change r ∈ fullArenaClauseRefsCore s'.core at hr
    dsimp only [s'] at hr hrefs ⊢; rw [hrefs] at hr
    change fullArenaClauseGarbCore s'.core r = false at hng
    dsimp only [s'] at hng; rw [(hmeta r hr).2.2] at hng
    change ((fullArenaClauseLitsCore s'.core r).map (· / 2)).Nodup
    by_cases hrp : r = p
    · subst r; dsimp only [s'] at hlits_p ⊢; rw [hlits_p]; exact hinvP.nd p hp hng
    · dsimp only [s']; rw [hlits_other r hr hrp]; exact hinvP.nd r hr hng
  have hll' : FullLastLearnedWf s' :=
    hinvP.extOk.1.of_refs_subset rfl (fun r hr => by
      change r ∈ fullArenaClauseRefsCore s'.core; dsimp only [s']; rw [hrefs]; exact hr)
  have hpe : FullArenaPermEq sP.core s'.core := by
    refine ⟨rfl, ?_, fun r hr => ?_⟩
    · dsimp only [s']; exact hrefs
    · dsimp only [s']
      refine ⟨(hmeta r hr).2.1, (hmeta r hr).2.2, ?_⟩
      by_cases hrp : r = p
      · subst r; dsimp only [s'] at hlits_p ⊢; rw [hlits_p]
      · rw [hlits_other r hr hrp]
  exact ⟨hlen', hw', hinvP.lm, hnd', ⟨hll', hinvP.extOk.2⟩,
    hinvP.cv, hinvP.cl, hinvP.dm, hinvP.alen, hinvP.vals, hinvP.lvl, hinvP.flags,
    hinvP.fuel, hinvP.inc, hinvP.dcur, hinvP.dval, hinvP.probing,
    dense_arenaPermEq_trans hinvP.perm hpe,
    hinvP.extLen, hinvP.wvals, hinvP.wbest, hinvP.ll⟩

private theorem watchSlice_congr {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p p' rem rem' : Nat} (hp : p = p') (hrem : rem = rem')
    (h : WatchSliceOk F_cur k lit p rem) : WatchSliceOk F_cur k lit p' rem' := by
  subst hp hrem; exact h

private theorem watchSlice_relocate_append_large {F_cur : List (List Nat)}
    {k k' : FullCoreState} {lit p p' rem : Nat} {w0 cref : BitVec 32}
    (hvars : k.cur_vars ≤ k'.cur_vars)
    (hrefs : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ j < rem, k'.wstk[p' + j]? = k.wstk[p + j]?)
    (h : WatchSliceOk F_cur k lit p rem)
    (hw0 : k'.wstk[p' + rem]? = some w0) (hcref : k'.wstk[p' + rem + 1]? = some cref)
    (hfl : (w0 &&& 0x80000000#32) = 0#32)
    (hlt : cref.toNat < 0x80000000) (hr : cref.toNat ∈ fullArenaClauseRefsCore k') :
    WatchSliceOk F_cur k' lit p' (rem + 2) := by
  induction h generalizing p' with
  | empty =>
    exact .large (by simpa using hw0) (by simpa using hcref) hfl hlt hr .empty
  | @bin p rem w hp hf hn hltb hent _ ih =>
    refine .bin (by simpa using (hwstk 0 (by omega)).trans hp) hf hn (by omega) hent
      (ih (p' := p' + 1)
        (fun j hj => by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (j + 1) (by omega))
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hw0)
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcref))
  | @large p rem w c hp hc hf hl hcr _ ih =>
    refine .large (by simpa using (hwstk 0 (by omega)).trans hp)
      (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (hwstk 1 (by omega)).trans hc)
      hf hl (hrefs c.toNat hcr)
      (ih (p' := p' + 2)
        (fun j hj => by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (j + 2) (by omega))
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hw0)
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcref))

private theorem watchSlice_relocate {F_cur : List (List Nat)}
    {k k' : FullCoreState} {lit p p' rem : Nat}
    (hvars : k.cur_vars ≤ k'.cur_vars)
    (hrefs : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ j < rem, k'.wstk[p' + j]? = k.wstk[p + j]?)
    (h : WatchSliceOk F_cur k lit p rem) : WatchSliceOk F_cur k' lit p' rem := by
  induction h generalizing p' with
  | empty => exact .empty
  | @bin p rem w hp hf hn hltb hent _ ih =>
    exact .bin (by simpa using (hwstk 0 (by omega)).trans hp) hf hn (by omega) hent
      (ih fun j hj => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (j + 1) (by omega))
  | @large p rem w c hp hc hf hl hcr _ ih =>
    exact .large (by simpa using (hwstk 0 (by omega)).trans hp)
      (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (hwstk 1 (by omega)).trans hc)
      hf hl (hrefs c.toNat hcr)
      (ih fun j hj => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (j + 2) (by omega))

private theorem wl_push_ok {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 sK : FullState} (hinvK : WlInv c F0 F_cur s0 sK)
    (hdm : sK.core.dense_mode = 0#64)
    {lit w0 w1 : BitVec 32} {ok : Bool}
    {wvec' wstk' wsort' : List (BitVec 32)} {wlen' : Nat} {wu' : BitVec 64}
    (hflag : (w0 &&& 0x80000000#32) = 0#32)
    (hlt : w1.toNat < 0x80000000) (href : w1.toNat ∈ fullArenaClauseRefsCore sK.core) :
    let sK' : FullState :=
      { sK with
        core := { sK.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
        scratch := { sK.scratch with wsort := wsort' } }
    sK'.LengthsOk c → WatchStackLayout sK'.core →
    (∀ l < 2 * sK.core.cur_vars, l ≠ lit.toNat →
      fullWatchSize sK' l = fullWatchSize sK l ∧
      ∀ i < fullWatchSize sK l,
        sK'.core.wstk[fullWatchOff sK' l + i]? = sK.core.wstk[fullWatchOff sK l + i]?) →
    (ok = true →
      lit.toNat < 2 * sK.core.cur_vars ∧
      fullWatchSize sK' lit.toNat = fullWatchSize sK lit.toNat + 2 ∧
      (∀ i < fullWatchSize sK lit.toNat,
        sK'.core.wstk[fullWatchOff sK' lit.toNat + i]? =
          sK.core.wstk[fullWatchOff sK lit.toNat + i]?) ∧
      sK'.core.wstk[fullWatchOff sK' lit.toNat + fullWatchSize sK lit.toNat]? = some w0 ∧
      sK'.core.wstk[fullWatchOff sK' lit.toNat + fullWatchSize sK lit.toNat + 1]? = some w1) →
    (ok = false → lit.toNat < 2 * sK.core.cur_vars →
      fullWatchSize sK' lit.toNat = fullWatchSize sK lit.toNat ∧
      ∀ i < fullWatchSize sK lit.toNat,
        sK'.core.wstk[fullWatchOff sK' lit.toNat + i]? =
          sK.core.wstk[fullWatchOff sK lit.toNat + i]?) →
    WlInv c F0 F_cur s0 sK' := by
  intro sK' hlen' hlay' hoth hokT hokF
  have hwatK : WatchesInv F_cur sK.core := by
    simpa [ModeWatchesInv, hdm] using hinvK.witness.watches
  have hslices : ∀ l < 2 * sK'.core.cur_vars,
      WatchSliceOk F_cur sK'.core l (fullWatchOffCore sK'.core l)
        (fullWatchSizeCore sK'.core l) := by
    intro l hl
    by_cases hll : l = lit.toNat
    · subst hll
      cases ok with
      | true =>
        obtain ⟨_, hsz_eq, hpre, hw0, hw1⟩ := hokT rfl
        have h' := watchSlice_relocate_append_large (k := sK.core) (k' := sK'.core)
          (Nat.le_refl _) (fun _ r => r) hpre (hwatK.slices lit.toNat hl) hw0 hw1 hflag hlt href
        exact watchSlice_congr rfl
          (by simpa [fullWatchSizeCore, fullWatchSize] using hsz_eq.symm) h'
      | false =>
        obtain ⟨hsz_eq, hpre⟩ := hokF rfl hl
        have h' := watchSlice_relocate (k := sK.core) (k' := sK'.core)
          (Nat.le_refl _) (fun _ r => r) hpre (hwatK.slices lit.toNat hl)
        exact watchSlice_congr rfl
          (by simpa [fullWatchSizeCore, fullWatchSize] using hsz_eq.symm) h'
    · obtain ⟨hsz_eq, hpre⟩ := hoth l hl hll
      have h' := watchSlice_relocate (k := sK.core) (k' := sK'.core)
        (Nat.le_refl _) (fun _ r => r) hpre (hwatK.slices l hl)
      exact watchSlice_congr rfl
        (by simpa [fullWatchSizeCore, fullWatchSize] using hsz_eq.symm) h'
  have hw' : FullWitnessInv c F0 F_cur sK'.core :=
    { hinvK.witness with
      arena := { hinvK.witness.arena with len_ok := hinvK.witness.arena.len_ok }
      watches := by rw [ModeWatchesInv, ite_eq_left hdm]; exact ⟨hlay', hslices⟩ }
  exact ⟨hlen', hw', hinvK.lm, hinvK.nd, hinvK.extOk, hinvK.cv, hinvK.cl, hinvK.dm, hinvK.alen,
    hinvK.vals, hinvK.lvl, hinvK.flags, hinvK.fuel, hinvK.inc, hinvK.dcur, hinvK.dval,
    hinvK.probing, hinvK.perm, hinvK.extLen, hinvK.wvals, hinvK.wbest, hinvK.ll⟩

private theorem wl_oom_ok {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 sK : FullState} (hinvK : WlInv c F0 F_cur s0 sK) :
    let s' := { sK with core := { sK.core with oom := 1#64 } }
    WlInv c F0 F_cur s0 s' := by
  intro s'
  have hlen' : s'.LengthsOk c :=
    ⟨{ hinvK.lengths.core_ok with vals_len := hinvK.lengths.core_ok.vals_len },
      hinvK.lengths.scratch_ok⟩
  have hw' := fullWitnessInv_with_oom hinvK.witness 1#64
  exact ⟨hlen', hw', hinvK.lm, hinvK.nd, hinvK.extOk, hinvK.cv, hinvK.cl, hinvK.dm, hinvK.alen,
    hinvK.vals, hinvK.lvl, hinvK.flags, hinvK.fuel, hinvK.inc, hinvK.dcur, hinvK.dval,
    hinvK.probing, hinvK.perm, hinvK.extLen, hinvK.wvals, hinvK.wbest, hinvK.ll⟩

private theorem wl_lit_bounds {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {sP : FullState} (hlenP : sP.LengthsOk c) (hwP : FullWitnessInv c F0 F_cur sP.core)
    {p idx : Nat} (hp_in : p ∈ fullArenaClauseRefsCore sP.core)
    (hgarb : fullArenaClauseGarbCore sP.core p = false)
    (hidx_lt : idx < fullArenaClauseSizeCore sP.core p)
    (ha_lt : p + 3 + idx < sP.core.arena.length) :
    let l := (sP.core.arena[p + 3 + idx]'ha_lt).toNat
    l < 2 * sP.core.cur_vars ∧ l < sP.core.vals.length ∧ l / 2 < sP.core.lvl.length := by
  have hpwf := hwP.arena.refs_wf p hp_in
  have hbd : p + 3 + fullArenaClauseSizeCore sP.core p ≤ sP.core.arena.length := by
    have := hpwf.2.2.1; have := hpwf.2.2.2.1
    have := hlenP.core_ok.arena_len_le; have := hlenP.core_ok.arena_len_arr; omega
  have hmem : (sP.core.arena[p + 3 + idx]'ha_lt).toNat ∈ fullArenaClauseLitsCore sP.core p := by
    rw [mem_fullArenaClauseLitsCore_iff hbd]; exact ⟨idx, hidx_lt, rfl⟩
  have hl := hwP.arena.lits_lt p hp_in hgarb _ hmem
  have := hlenP.core_ok.cur_vars_le; have := hlenP.core_ok.vals_len; have := hlenP.core_ok.lvl_len
  omega

private theorem wl_garb_false_of_hdr {sP : FullState} {p : Nat}
    (hp_lt : p < sP.core.arena.length)
    (hng : (sP.core.arena[p]'hp_lt &&& 0x00080000#32) = 0#32) :
    fullArenaClauseGarbCore sP.core p = false := by
  unfold fullArenaClauseGarbCore fullArenaHdrCore
  rw [List.getElem?_eq_getElem hp_lt, Option.getD_some, hng]; decide

private theorem wl_q_close {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sF : FullState} {Q : Post []} {mF : Mem 64} {R : Mem 64 → Prop}
    (hinvF : WlInv c F0 F_cur s sF) (hmF : (FullMem c sF ⋆ R) mF)
    (hQ : ∀ (s' : FullState) (m' : Mem 64),
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      FullLitMarksClear c s' → FullArenaVarsNodup s' → FullExtScratchOk c s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.cur_level = s.core.cur_level →
      s'.core.dense_mode = s.core.dense_mode →
      s'.core.arena_len = s.core.arena_len →
      s'.core.vals = s.core.vals → s'.core.lvl = s.core.lvl → s'.core.flags = s.core.flags →
      s'.core.fuel = s.core.fuel → s'.core.inconsistent = s.core.inconsistent →
      s'.core.d_cur = s.core.d_cur → s'.core.d_val = s.core.d_val →
      s'.core.probing = s.core.probing → FullArenaPermEq s.core s'.core →
      s'.scratch.extend_len = s.scratch.extend_len →
      s'.scratch.walk_vals = s.scratch.walk_vals →
      s'.scratch.walk_best = s.scratch.walk_best →
      s'.scratch.last_learned = s.scratch.last_learned →
      (FullMem c s' ⋆ R) m' → Q () m') :
    Q () mF :=
  hQ sF mF hinvF.lengths hinvF.witness hinvF.lm hinvF.nd hinvF.extOk hinvF.cv hinvF.cl
    hinvF.dm hinvF.alen hinvF.vals hinvF.lvl hinvF.flags hinvF.fuel hinvF.inc hinvF.dcur
    hinvF.dval hinvF.probing hinvF.perm hinvF.extLen hinvF.wvals hinvF.wbest hinvF.ll hmF

private theorem wl_p_offs {p : BitVec 64} (hp : p.toNat + 4 < 2 ^ 31) :
    (p.setWidth 32).toNat = p.toNat ∧
    (p + 1#64).toNat = p.toNat + 1 ∧
    (p + 2#64).toNat = p.toNat + 2 ∧
    (p + 3#64).toNat = p.toNat + 3 ∧
    (p + 4#64).toNat = p.toNat + 4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> bv_omega

private theorem wl_p3_add_eq {p : BitVec 64} {k : BitVec 32}
    (hp : p.toNat + 4 < 2 ^ 31) (hk : k.toNat < 2 ^ 30) :
    (p + 3#64 + k.setWidth 64).toNat = p.toNat + 3 + k.toNat := by
  bv_omega

private theorem wl_u32_add1 {k : BitVec 32} (hk : k.toNat < 2 ^ 30) :
    (k + 1#32).toNat = k.toNat + 1 := by
  bv_omega

private theorem wl_mask_props (l : BitVec 32) :
    (l &&& 0x7FFFFFFF#32 &&& 0x80000000#32) = 0#32 ∧
    (l &&& 0x7FFFFFFF#32) ≠ 0xFFFFFFFF#32 := by
  have hmask : (l &&& 0x7FFFFFFF#32 &&& 0x80000000#32) = 0#32 := by
    rw [BitVec.and_assoc]
    simp [show (0x7FFFFFFF#32 &&& 0x80000000#32) = 0#32 from rfl]
  refine ⟨hmask, fun h => ?_⟩
  rw [h] at hmask; revert hmask; decide

private theorem wl_clause_bd {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {sP : FullState} {p : Nat} (hlenP : sP.LengthsOk c)
    (hwP : FullWitnessInv c F0 F_cur sP.core) (hp : p ∈ fullArenaClauseRefsCore sP.core) :
    3 ≤ fullArenaClauseSizeCore sP.core p ∧
    p + 3 + fullArenaClauseSizeCore sP.core p ≤ sP.core.arena.length := by
  have hwf := hwP.arena.refs_wf p hp
  have := hwf.2.2.1; have := hwf.2.2.2.1
  have := hlenP.core_ok.arena_len_le; have := hlenP.core_ok.arena_len_arr
  exact ⟨hwf.2.1, by omega⟩

private theorem wl_swap_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 sP : FullState} {R : Mem 64 → Prop} {m : Mem 64} {P : Mem 64 → Prop}
    (hK : ∀ s', WlInv c F0 F_cur s0 s' ∧ (FullMem c s' ⋆ R) m → P m)
    (hinvP : WlInv c F0 F_cur s0 sP) {p a a' b b' : Nat}
    (hp : p ∈ fullArenaClauseRefsCore sP.core)
    (ha : a < fullArenaClauseSizeCore sP.core p)
    (hb : b < fullArenaClauseSizeCore sP.core p)
    (haa' : p + 3 + a = a') (hbb' : p + 3 + b = b')
    {hal' : a' < sP.core.arena.length} {hbl' : b' < sP.core.arena.length}
    (hm : (FullMem c { sP with core := { sP.core with
      arena := (sP.core.arena.set a' (sP.core.arena[b']'hbl')).set
        b' (sP.core.arena[a']'hal') } } ⋆ R) m) :
    P m := by
  have hpa : p + 3 + a < sP.core.arena.length := haa' ▸ hal'
  have hpb : p + 3 + b < sP.core.arena.length := hbb' ▸ hbl'
  obtain ⟨hinv', _⟩ := wl_swap_ok hinvP hp ha hb hpa hpb
  exact hK _ ⟨hinv', wl_swap_mem haa' hbb' hm⟩

private def wlAttachWatchesExpr {V : Ty → Type} {C : List Ty → Type}
    (h ar p : V i64) (JN : C []) : Expr V C [] :=
  let op64 (c : OpCode [i64, i64] [i64]) (a b : Arg V i64) := Op.mk c (a, b, ())
  let op32 (c : OpCode [i32, i32] [i32]) (a b : Arg V i32) := Op.mk c (a, b, ())
  .let_ (op64 (.add i64) (.var p) (.imm 1)) fun p1 =>
  .let_ (op64 (.mul i64) (.var p1.fst) (.imm 4)) fun p1o =>
  .let_ (op64 (.add i64) (.var ar) (.var p1o.fst)) fun p1a =>
  .store (t := i32) (.imm 2) (.var p1a.fst)
    (.let_ (op64 (.add i64) (.var p) (.imm 3)) fun p3 =>
     .let_ (op64 (.mul i64) (.var p3.fst) (.imm 4)) fun p3o =>
     .let_ (op64 (.add i64) (.var ar) (.var p3o.fst)) fun p3a =>
     .load i32 (.var p3a.fst) fun l0 =>
     .let_ (op64 (.add i64) (.var p) (.imm 4)) fun p4 =>
     .let_ (op64 (.mul i64) (.var p4.fst) (.imm 4)) fun p4o =>
     .let_ (op64 (.add i64) (.var ar) (.var p4o.fst)) fun p4a =>
     .load i32 (.var p4a.fst) fun l1 =>
     .group (sig := [[]])
       (fun _Js => .cons (fun _ =>
         .let_ (op64 (.add i64) (.var h) (.imm 760)) fun po =>
         .store (t := i64) (.imm 1) (.var po.fst) (.ret ())) .nil)
       fun Js =>
       .let_ (op32 (.and i32) (.var l1) (.imm 2147483647)) fun l1m =>
       .let_ (Op.mk (.trunc 64 32) (.var p, ())) fun p32 =>
       .call (bs := [.bool]) (as := [i64, i32, i32, i32, i32]) (rs := [])
         "full_watch_push_m6"
         (.var h, .var l0, .var l1m.fst, .var p32.fst, .imm 2, ()) fun r1 =>
       .jnz (.var r1.fst)
         (.let_ (op32 (.and i32) (.var l0) (.imm 2147483647)) fun l0m =>
          .let_ (Op.mk (.trunc 64 32) (.var p, ())) fun p32' =>
          .call (bs := [.bool]) (as := [i64, i32, i32, i32, i32]) (rs := [])
            "full_watch_push_m6"
            (.var h, .var l1, .var l0m.fst, .var p32'.fst, .imm 2, ()) fun r2 =>
          .jnz (.var r2.fst) (.jump JN ()) (.jump Js.fst ()))
         (.jump Js.fst ()))

private theorem wl_attach_watches_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s sR : FullState} {R : Mem 64 → Prop} {Q : Post []} {X : XPost}
    {p : BitVec 64} {mR : Mem 64} {JN : Cont []}
    (hWatchPush : Γ.Has "full_watch_push_m6" Proof.Spec.fullWatchPushSpec)
    (hdm : s.core.dense_mode = 0#64) (hp_bd31 : p.toNat + 4 < 2 ^ 31)
    (hp_in_s : p.toNat ∈ fullArenaClauseRefsCore s.core)
    (hinvR : WlInv c F0 F_cur s sR) (hmR : (FullMem c sR ⋆ R) mR)
    (hQ : ∀ sF mF, WlInv c F0 F_cur s sF → (FullMem c sF ⋆ R) mF → Q () mF)
    (hJN : ∀ sN mN, WlInv c F0 F_cur s sN ∧ (FullMem c sN ⋆ R) mN → JN () mN) :
    wp Γ Q X (wlAttachWatchesExpr c.hdr c.pArena p JN) mR := by
  obtain ⟨hp_tr, hp1_eq, _, hp3_eq, hp4_eq⟩ := wl_p_offs hp_bd31
  have hp_inR : p.toNat ∈ fullArenaClauseRefsCore sR.core := by
    rw [hinvR.perm.2.1]; exact hp_in_s
  have ⟨hszR, hbdR⟩ := wl_clause_bd hinvR.lengths hinvR.witness hp_inR
  dsimp only [wlAttachWatchesExpr]
  c0_hsteps_nogrp
  let sH := { sR with core := { sR.core with
    arena := sR.core.arena.set (p + 1#64).toNat 2#32 } }
  have hinvH : WlInv c F0 F_cur s sH := by
    dsimp only [sH]; rw [hp1_eq]; exact wl_set_hint_ok hinvR hp_inR
  have hp_inH : p.toNat ∈ fullArenaClauseRefsCore sH.core := by
    rw [hinvH.perm.2.1]; exact hp_in_s
  have ⟨hszH, hbdH⟩ := wl_clause_bd hinvH.lengths hinvH.witness hp_inH
  have hdmH : sH.core.dense_mode = 0#64 := hinvH.dm.trans hdm
  have hwatH : WatchStackLayout sH.core := by
    have hw := hinvH.witness.watches
    rw [ModeWatchesInv] at hw
    simp only [hdmH, ↓reduceIte] at hw
    exact hw.layout
  have hp_neff : p.setWidth 32 ≠ 0xFFFFFFFF#32 := fun h => by
    have hb : (p.setWidth 32).toNat < 2 ^ 31 := by rw [hp_tr]; omega
    rw [h] at hb; revert hb; decide
  have hmH : (FullMem c sH ⋆ R) m := hm
  c0_hsteps_nogrp
  refine wp_join_group (ts := [])
    (fun _ mOom => ∃ sOom, WlInv c F0 F_cur s sOom ∧ (FullMem c sOom ⋆ R) mOom)
    (fun _ _ mOom ⟨sOom, hinvOom, hmOom⟩ => by
      c0_hsteps_nogrp
      exact hQ _ _ (wl_oom_ok hinvOom) (by assumption))
    ?_
  intro Js hJs
  c0_hsteps_nogrp; dr_call hWatchPush
  let l0 := sH.core.arena[(p + 3#64).toNat]'(by omega)
  let l1 := sH.core.arena[(p + 4#64).toNat]'(by omega)
  obtain ⟨hl1_mask, hl1_neff⟩ := wl_mask_props l1
  refine ⟨c, sH, R, rfl, hinvH.lengths, hwatH, by simp,
    fun _ => ⟨hl1_neff, hp_neff⟩, hmH,
    fun ok1 wvec1 wstk1 wlen1 wu1 wsort1 m1 hlen1 hlay1 hoth1 hokT1 hokF1 hm1 => ?_⟩
  dsimp only [Arg.val] at hokT1 hokF1
  let s1 : FullState :=
    { sH with
      core := { sH.core with wvec := wvec1, wstk := wstk1, wlen := wlen1,
                             wusable := wu1 }
      scratch := { sH.scratch with wsort := wsort1 } }
  have hinv1 := wl_push_ok hinvH hdmH hl1_mask (by rw [hp_tr]; omega)
    (by rw [hp_tr]; exact hp_inH) hlen1 hlay1 hoth1
    (fun ht => let ⟨hl, _, hs, hp, hw0, hw1⟩ := hokT1 ht; ⟨hl, hs, hp, hw0, hw1 rfl⟩)
    (fun hf hl => (hokF1 hf).1 hl)
  c0_hsplit
  · obtain ⟨hl0_mask, hl0_neff⟩ := wl_mask_props l0
    have hwat1 : WatchStackLayout s1.core := hlay1
    have hp_in1 : p.toNat ∈ fullArenaClauseRefsCore s1.core := hp_inH
    c0_hsteps_nogrp; dr_call hWatchPush
    refine ⟨c, s1, R, rfl, hinv1.lengths, hwat1, by simp,
      fun _ => ⟨hl0_neff, hp_neff⟩, hm1,
      fun ok2 wvec2 wstk2 wlen2 wu2 wsort2 m2 hlen2 hlay2 hoth2 hokT2 hokF2 hm2 => ?_⟩
    dsimp only [Arg.val] at hokT2 hokF2
    let s2 : FullState :=
      { s1 with
        core := { s1.core with wvec := wvec2, wstk := wstk2, wlen := wlen2,
                               wusable := wu2 }
        scratch := { s1.scratch with wsort := wsort2 } }
    have hinv2 := wl_push_ok hinv1 hdmH hl0_mask (by rw [hp_tr]; omega)
      (by rw [hp_tr]; exact hp_in1) hlen2 hlay2 hoth2
      (fun ht => let ⟨hl, _, hs, hp, hw0, hw1⟩ := hokT2 ht
        ⟨hl, hs, hp, hw0, hw1 rfl⟩)
      (fun hf hl => (hokF2 hf).1 hl)
    c0_hsplit
    · c0_hsteps_nogrp; exact hJN s2 m2 ⟨hinv2, hm2⟩
    · c0_hsteps_nogrp; exact hJs () m2 ⟨s2, hinv2, hm2⟩
  · c0_hsteps_nogrp; exact hJs () m1 ⟨s1, hinv1, hm1⟩

/-! ## 2. `full_watch_large_clauses_fid` WP Proof -/

/-- `full_watch_large_clauses_fid` WP proof (`Spec.fullWatchLargeClausesSpec`). -/
theorem full_watch_large_clauses_fid_wp (Γ : Env)
    (hArenaNext : Γ.Has "full_arena_next" Proof.Spec.fullArenaNextSpec)
    (hLitRank : Γ.Has "full_lit_rank_m6" Proof.Spec.fullLitRankSpec)
    (hWatchPush : Γ.Has "full_watch_push_m6" Proof.Spec.fullWatchPushSpec) :
    ∀ a m Q X, Spec.fullWatchLargeClausesSpec a m Q X →
      Func.wp Γ full_watch_large_clauses_fid_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hlm, hnd, hext_ok, hdm, hm, hQ⟩
  have har_cap := c.harena; have hmaxv := c.hmaxv; unfold dimacsBound at har_cap hmaxv
  have hinv0 : WlInv c F0 F_cur s s :=
    ⟨hlen, hw, hlm, hnd, hext_ok, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
     rfl, rfl, rfl, ⟨rfl, rfl, fun _ _ => ⟨rfl, rfl, List.Perm.refl _⟩⟩,
     rfl, rfl, rfl, rfl⟩
  unfold Func.wp full_watch_large_clauses_fid_body
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64])
    (fun _ mFin => ∃ sFin : FullState, WlInv c F0 F_cur s sFin ∧ (FullMem c sFin ⋆ R) mFin)
    (fun _ _ mFin ⟨sFin, hinvFin, hmFin⟩ => by
      c0_hsteps_nogrp
      exact wl_q_close hinvFin hmFin hQ)
    (fun JL hJL => ?_)
  c0_hsteps_nogrp
  refine wp_loop_inv
    (fun (p, ()) mP => p.toNat ≤ s.core.arena_len ∧
      (p.toNat = s.core.arena_len ∨ p.toNat ∈ fullArenaClauseRefsCore s.core) ∧
      ∃ sP : FullState, WlInv c F0 F_cur s sP ∧ (FullMem c sP ⋆ R) mP)
    (fun (p, ()) _ => s.core.arena_len - p.toNat)
    (fun JLp hLoop => by
      c0_hsteps_nogrp
      refine hLoop (0#64, ()) m ⟨Nat.zero_le _, ?_, s, hinv0, hm⟩
      by_cases hz : s.core.arena_len = 0
      · exact Or.inl hz.symm
      · exact Or.inr (fullArenaClauseRefs_zero_mem hw.arena (Nat.pos_of_ne_zero hz)))
    (fun JLp ⟨p, ⟨⟩⟩ mP ⟨hp_le, hp_mem, sP, hinvP, hmP⟩ hLoop => ?_)
  have halP := hinvP.lengths.core_ok.arena_len_le
  have haarP := hinvP.lengths.core_ok.arena_len_arr
  have hdmP : sP.core.dense_mode = 0#64 := hinvP.dm.trans hdm
  have halenP : sP.core.arena_len = s.core.arena_len := hinvP.alen
  c0_hsteps_nogrp
  · have hp_lt : p.toNat < sP.core.arena_len := by omega
    have hrefsP : fullArenaClauseRefsCore sP.core = fullArenaClauseRefsCore s.core :=
      hinvP.perm.2.1
    have hp_in : p.toNat ∈ fullArenaClauseRefsCore sP.core := by
      rw [hrefsP]; exact hp_mem.resolve_left (by omega)
    have ⟨hsz3, hp_bd⟩ := wl_clause_bd hinvP.lengths hinvP.witness hp_in
    have hp_bd31 : p.toNat + 4 < 2 ^ 31 := by omega
    obtain ⟨_, _, hp2_eq, hp3_eq, hp4_eq⟩ := wl_p_offs hp_bd31
    have hp2_lt : (p + 2#64).toNat < sP.core.arena.length := by omega
    have hsz_eq : (sP.core.arena[(p + 2#64).toNat]'hp2_lt).toNat =
        fullArenaClauseSizeCore sP.core p.toNat := by
      unfold fullArenaClauseSizeCore
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; simp [hp2_eq]
    c0_hsteps_nogrp; dr_call hArenaNext
    refine ⟨c, sP, R, rfl, hinvP.lengths, hmP, ?_⟩
    obtain ⟨hnp_gt, hnp_le, hnp_mem⟩ := wl_arena_next_eq hinvP.witness hinvP.lengths hp_in
    c0_hsteps_nogrp
    refine wp_join_state0 (α := FullState)
      (fun sN mN => WlInv c F0 F_cur s sN ∧ (FullMem c sN ⋆ R) mN)
      (fun _ sN mN ⟨hinvN, hmN⟩ => by
        c0_hsteps_nogrp
        · exact hJL (p, ()) mN ⟨sN, hinvN, hmN⟩
        · exact hLoop (_, ()) mN (by dsimp only [Arg.val]; omega)
            ⟨by rw [← halenP]; exact hnp_le,
             by rcases hnp_mem with he | hm'
                · exact Or.inl (he.trans halenP)
                · exact Or.inr (hrefsP ▸ hm'),
             sN, hinvN, hmN⟩)
      (fun JN hJN => by
        c0_hsteps_nogrp
        · have hng_hdr : (sP.core.arena[p.toNat]'(by omega) &&& 0x00080000#32) = 0#32 := by
            assumption
          have hgarb := wl_garb_false_of_hdr (by omega) hng_hdr
          refine wp_join_state0 (α := FullState)
            (fun sR mR => WlInv c F0 F_cur s sR ∧ (FullMem c sR ⋆ R) mR)
            (fun _ sR mR ⟨hinvR, hmR⟩ =>
              wl_attach_watches_wp hWatchPush hdm hp_bd31 (hrefsP ▸ hp_in) hinvR hmR
                (fun _ _ hinvF hmF => wl_q_close hinvF hmF hQ) hJN)
            (fun JR hJR => by
              c0_hsplit
              · c0_hsteps_nogrp; exact hJR _ mP ⟨hinvP, hmP⟩
              · have hb0 := wl_lit_bounds hinvP.lengths hinvP.witness hp_in hgarb (idx := 0)
                  (by omega) (by omega)
                c0_hsteps_nogrp; dr_call hLitRank
                refine ⟨sP.core.vals, sP.core.lvl, FullValsLvlRest c sP ⋆ R,
                  by simpa [hp3_eq] using hb0.2.1,
                  by simpa [hp3_eq] using hb0.2.2,
                  focus_full_vals_lvl hmP, fun r0 => ?_⟩
                c0_hsteps_nogrp
                have hsz_lt29 : (sP.core.arena[(p + 2#64).toNat]'hp2_lt).toNat < 2 ^ 30 := by
                  rw [hsz_eq]; omega
                refine wp_loop_inv (ts := [i32, i64, i32])
                  (fun (i0, _, i, _) mL0 => mL0 = mP ∧ 1 ≤ i.toNat ∧
                    i.toNat ≤ (sP.core.arena[(p + 2#64).toNat]'hp2_lt).toNat ∧
                    i0.toNat < (sP.core.arena[(p + 2#64).toNat]'hp2_lt).toNat)
                  (fun (_, _, i, _) _ =>
                    (sP.core.arena[(p + 2#64).toNat]'hp2_lt).toNat - i.toNat)
                  (fun JL0' hLp0 => by
                    c0_hsteps_nogrp
                    exact hLp0 (0#32, r0, 1#32, ()) mP
                      ⟨rfl, by decide,
                       by rw [hsz_eq]; exact Nat.le_trans (by decide) hsz3,
                       by rw [hsz_eq]; exact Nat.lt_of_lt_of_le (by decide) hsz3⟩)
                  (fun JL0' ⟨i0, r0c, i, ⟨⟩⟩ mL0 ⟨hmL0, hi1, hile, hi0_lt⟩ hLp0 => by
                    subst mL0
                    c0_hsplit
                    · have hi_lt : i.toNat < (sP.core.arena[(p + 2#64).toNat]'hp2_lt).toNat :=
                        by assumption
                      have hi_eq := wl_p3_add_eq hp_bd31 (k := i) (by omega)
                      have hb_i := wl_lit_bounds hinvP.lengths hinvP.witness hp_in hgarb
                        (idx := i.toNat) (by rw [← hsz_eq]; exact hi_lt) (by omega)
                      c0_hsteps_nogrp; dr_call hLitRank
                      refine ⟨sP.core.vals, sP.core.lvl, FullValsLvlRest c sP ⋆ R,
                        by simpa [hi_eq] using hb_i.2.1,
                        by simpa [hi_eq] using hb_i.2.2,
                        focus_full_vals_lvl hmP, fun rk => ?_⟩
                      have hi1_n := wl_u32_add1 (k := i) (by omega)
                      c0_hsteps_nogrp
                      refine wp_join_group (ts := [i32, i64])
                        (fun (i0', _) mJ => mJ = mP ∧
                          i0'.toNat < (sP.core.arena[(p + 2#64).toNat]'hp2_lt).toNat)
                        (fun _ ⟨i0', r0', ⟨⟩⟩ mJ ⟨hmJ, hi0'_lt⟩ => by
                          c0_hsteps_nogrp
                          exact hLp0 (i0', r0', i + 1#32, ()) _ (by dsimp only; rw [hi1_n]; omega)
                            ⟨hmJ, by omega, by omega, hi0'_lt⟩)
                        (fun Js1 hJs1 => by
                          c0_hsteps_nogrp
                          · exact hJs1 (i, rk, ()) mP ⟨rfl, hi_lt⟩
                          · exact hJs1 (i0, r0c, ()) mP ⟨rfl, hi0_lt⟩)
                    · c0_hsteps_nogrp
                      refine wp_join_state0 (α := FullState)
                        (fun sS0 mS0 => WlInv c F0 F_cur s sS0 ∧ (FullMem c sS0 ⋆ R) mS0)
                        (fun _ sS0 mS0 ⟨hinvS0, hmS0⟩ => by
                          have hrefsS0 : fullArenaClauseRefsCore sS0.core =
                              fullArenaClauseRefsCore sP.core := hinvS0.perm.2.1.trans hrefsP.symm
                          have hp_inS0 : p.toNat ∈ fullArenaClauseRefsCore sS0.core := by
                            rw [hrefsS0]; exact hp_in
                          have hp_in_s : p.toNat ∈ fullArenaClauseRefsCore s.core := by
                            rw [← hrefsP]; exact hp_in
                          have ⟨hsz3S0, hbdS0⟩ := wl_clause_bd hinvS0.lengths hinvS0.witness hp_inS0
                          have hszS0 : fullArenaClauseSizeCore sS0.core p.toNat =
                              fullArenaClauseSizeCore sP.core p.toNat :=
                            (hinvS0.perm.2.2 p.toNat hp_in_s).1.trans
                              (hinvP.perm.2.2 p.toNat hp_in_s).1.symm
                          have hgarbS0 : fullArenaClauseGarbCore sS0.core p.toNat = false := by
                            have h1 := (hinvS0.perm.2.2 p.toNat hp_in_s).2.1
                            have h2 := (hinvP.perm.2.2 p.toNat hp_in_s).2.1
                            rw [h1, ← h2]; exact hgarb
                          have hb1 := wl_lit_bounds hinvS0.lengths hinvS0.witness hp_inS0 hgarbS0
                            (idx := 1) (by omega) (by omega)
                          c0_hsteps_nogrp; dr_call hLitRank
                          refine ⟨sS0.core.vals, sS0.core.lvl, FullValsLvlRest c sS0 ⋆ R,
                            by simpa [hp4_eq] using hb1.2.1,
                            by simpa [hp4_eq] using hb1.2.2,
                            focus_full_vals_lvl hmS0, fun r1 => ?_⟩
                          c0_hsteps_nogrp
                          refine wp_loop_inv (ts := [i32, i32, i64])
                            (fun (j, i1, _) mL1 => mL1 = mS0 ∧ 2 ≤ j.toNat ∧
                              j.toNat ≤ (sP.core.arena[(p + 2#64).toNat]'hp2_lt).toNat ∧
                              1 ≤ i1.toNat ∧
                              i1.toNat < (sP.core.arena[(p + 2#64).toNat]'hp2_lt).toNat)
                            (fun (j, _, _) _ =>
                              (sP.core.arena[(p + 2#64).toNat]'hp2_lt).toNat - j.toNat)
                            (fun JL1 hLp1 => by
                              c0_hsteps_nogrp
                              exact hLp1 (2#32, 1#32, r1, ()) mS0
                                ⟨rfl, by decide,
                                 by rw [hsz_eq]; exact Nat.le_trans (by decide) hsz3,
                                 by decide,
                                 by rw [hsz_eq]; exact Nat.lt_of_lt_of_le (by decide) hsz3⟩)
                            (fun JL1 ⟨j, i1, r1c, ⟨⟩⟩ mL1
                                ⟨hmL1, hj2, hjle, hi1_ge, hi1_lt⟩ hLp1 => by
                              subst mL1
                              c0_hsplit
                              · have hj_lt :
                                    j.toNat < (sP.core.arena[(p + 2#64).toNat]'hp2_lt).toNat :=
                                  by assumption
                                have hj_eq := wl_p3_add_eq hp_bd31 (k := j) (by omega)
                                have hb_j := wl_lit_bounds hinvS0.lengths hinvS0.witness hp_inS0
                                  hgarbS0 (idx := j.toNat)
                                  (by rw [hszS0, ← hsz_eq]; exact hj_lt) (by omega)
                                c0_hsteps_nogrp; dr_call hLitRank
                                refine ⟨sS0.core.vals, sS0.core.lvl, FullValsLvlRest c sS0 ⋆ R,
                                  by simpa [hj_eq] using hb_j.2.1,
                                  by simpa [hj_eq] using hb_j.2.2,
                                  focus_full_vals_lvl hmS0, fun rk => ?_⟩
                                have hj1 := wl_u32_add1 (k := j) (by omega)
                                c0_hsteps_nogrp
                                refine wp_join_group (ts := [i32, i64])
                                  (fun (i1', _) mJ => mJ = mS0 ∧ 1 ≤ i1'.toNat ∧
                                    i1'.toNat <
                                      (sP.core.arena[(p + 2#64).toNat]'hp2_lt).toNat)
                                  (fun _ ⟨i1', r1', ⟨⟩⟩ mJ ⟨hmJ, hi1'_ge, hi1'_lt⟩ => by
                                    c0_hsteps_nogrp
                                    exact hLp1 (j + 1#32, i1', r1', ()) _
                                      (by dsimp only; rw [hj1]; omega)
                                      ⟨hmJ, by omega, by omega, hi1'_ge, hi1'_lt⟩)
                                  (fun Js2 hJs2 => by
                                    c0_hsteps_nogrp
                                    · exact hJs2 (j, rk, ()) mS0 ⟨rfl, by omega, hj_lt⟩
                                    · exact hJs2 (i1, r1c, ()) mS0 ⟨rfl, hi1_ge, hi1_lt⟩)
                              · c0_hsteps_nogrp
                                refine wp_join_state0 (α := FullState)
                                  (fun sS1 mS1 =>
                                    WlInv c F0 F_cur s sS1 ∧ (FullMem c sS1 ⋆ R) mS1)
                                  (fun _ sS1 mS1 ⟨hinvS1, hmS1⟩ => by
                                    c0_hsteps_nogrp; exact hJR _ mS1 ⟨hinvS1, hmS1⟩)
                                  (fun JsR hJsR => by
                                    c0_hsteps_nogrp
                                    · have hi1_eq := wl_p3_add_eq hp_bd31 (k := i1) (by omega)
                                      have hi1_ar :
                                          (p + 3#64 + i1.setWidth 64).toNat <
                                            sS0.core.arena.length := by
                                        rw [hi1_eq]; omega
                                      have hi1_ar2 :
                                          (p + 3#64 + i1.setWidth 64).toNat <
                                            (sS0.core.arena.set (p + 4#64).toNat
                                              (sS0.core.arena[(p + 3#64 + i1.setWidth 64).toNat]'
                                                hi1_ar)).length := by
                                        simpa only [List.length_set] using hi1_ar
                                      c0_hsteps_nogrp
                                      refine wl_swap_step (P := JsR ()) (fun s' => hJsR s' _) hinvS0
                                        hp_inS0 (a := 1) (b := i1.toNat) (by rw [hszS0]; omega)
                                        (by rw [hszS0, ← hsz_eq]; exact hi1_lt)
                                        (by omega : p.toNat + 3 + 1 = (p + 4#64).toNat)
                                        hi1_eq.symm (hal' := by omega) (hbl' := hi1_ar) ?_
                                      assumption
                                    · exact hJsR _ mS0 ⟨hinvS0, hmS0⟩)))
                        (fun JL0 hJL0 => by
                          c0_hsteps_nogrp
                          · have hi0_eq := wl_p3_add_eq hp_bd31 (k := i0) (by omega)
                            have hi0_ar :
                                (p + 3#64 + i0.setWidth 64).toNat < sP.core.arena.length := by
                              rw [hi0_eq]; omega
                            have hi0_ar2 :
                                (p + 3#64 + i0.setWidth 64).toNat <
                                  (sP.core.arena.set (p + 3#64).toNat
                                    (sP.core.arena[(p + 3#64 + i0.setWidth 64).toNat]'
                                      hi0_ar)).length := by
                              simpa only [List.length_set] using hi0_ar
                            c0_hsteps_nogrp
                            refine wl_swap_step (P := JL0 ()) (fun s' => hJL0 s' _) hinvP hp_in
                              (a := 0) (b := i0.toNat) (by omega)
                              (by rw [← hsz_eq]; exact hi0_lt)
                              (by omega : p.toNat + 3 + 0 = (p + 3#64).toNat)
                              hi0_eq.symm (hal' := by omega) (hbl' := hi0_ar) ?_
                            assumption
                          · exact hJL0 _ _ ⟨hinvP, hmP⟩)))
        · c0_hsteps_nogrp; exact hJN sP mP ⟨hinvP, hmP⟩
        · c0_hsteps_nogrp; exact hJN sP mP ⟨hinvP, hmP⟩)
  · c0_hsteps_nogrp; exact hJL (p, ()) mP ⟨sP, hinvP, hmP⟩

end LeanQbe.T.Examples.Kissat.Proof.Dense
