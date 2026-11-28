/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.BcpFlushHelpers
public import LeanQbe.T.Logic.C0Step
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat BCP Hot-Loop State & Invariant Helpers (`Proof.PropSearch.BcpPropHelpers`)

Canonical non-legacy helper layer for `Proof/PropSearch/Wp*.lean` (`0` legacy imports,
`0` `@[expose]` on theorems/lemmas):
1. `fastPropMem` memory-only projection (`fastPropMem_with_*` & scoped `bv_c0` field equations).
2. `propLitCoreMask`, `fidCoreMask`, `PropLitConfl`, `PropLitInv` (with `FullTrailRsnsPres`),
   and `fid_core_eq_of_agrees` / `fastPropMem_eq_of_eq`.
3. Inline BCP step lemmas (`m7_*` assign, swap, overflow, compact-finish, `fid_pi_rebase`,
   `fid_repl_delay_step`, and `fastProp_findRepl_*`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.PropSearch

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.PropSearch.Spec

/-! ## 1. `fastPropMem` Projection, Field Accessors & `with_*` Equalities -/

/-- Minimal memory-state projection exposing only the `FullCoreState`/`FullScratch` fields
accessed inside hot BCP loops (`prop_lit`, `propagate_ignore*`, `propagate_beyond*`). -/
@[expose] def fastPropMem (s0 sem : FullState) : FullState :=
  { core :=
      { s0.core with
        cur_vars := sem.core.cur_vars
        arena_len := sem.core.arena_len
        wlen := sem.core.wlen
        wusable := sem.core.wusable
        probing := sem.core.probing
        propagated := sem.core.propagated
        cur_level := sem.core.cur_level
        fuel := sem.core.fuel
        confl_ref := sem.core.confl_ref
        confl_type := sem.core.confl_type
        confl_lit0 := sem.core.confl_lit0
        confl_lit1 := sem.core.confl_lit1
        oom := sem.core.oom
        vals := sem.core.vals
        flags := sem.core.flags
        lvl := sem.core.lvl
        rsns := sem.core.rsns
        trl := sem.core.trl
        trail_pos := sem.core.trail_pos
        wvec := sem.core.wvec
        arena := sem.core.arena
        wstk := sem.core.wstk }
    scratch :=
      { s0.scratch with
        delayed_len := sem.scratch.delayed_len
        search_ticks := sem.scratch.search_ticks
        phases := sem.scratch.phases
        wsort := sem.scratch.wsort
        delayed := sem.scratch.delayed } }

theorem fastPropMem_self (s : FullState) : fastPropMem s s = s := by
  cases s with | mk c sc => cases c; cases sc; rfl

namespace BcpPropTactics

@[scoped bv_c0] theorem fastPropMem_vals (s0 sem : FullState) :
    (fastPropMem s0 sem).core.vals = sem.core.vals := rfl
@[scoped bv_c0] theorem fastPropMem_flags (s0 sem : FullState) :
    (fastPropMem s0 sem).core.flags = sem.core.flags := rfl
@[scoped bv_c0] theorem fastPropMem_lvl (s0 sem : FullState) :
    (fastPropMem s0 sem).core.lvl = sem.core.lvl := rfl
@[scoped bv_c0] theorem fastPropMem_rsns (s0 sem : FullState) :
    (fastPropMem s0 sem).core.rsns = sem.core.rsns := rfl
@[scoped bv_c0] theorem fastPropMem_trl (s0 sem : FullState) :
    (fastPropMem s0 sem).core.trl = sem.core.trl := rfl
@[scoped bv_c0] theorem fastPropMem_trail_pos (s0 sem : FullState) :
    (fastPropMem s0 sem).core.trail_pos = sem.core.trail_pos := rfl
@[scoped bv_c0] theorem fastPropMem_wvec (s0 sem : FullState) :
    (fastPropMem s0 sem).core.wvec = sem.core.wvec := rfl
@[scoped bv_c0] theorem fastPropMem_arena (s0 sem : FullState) :
    (fastPropMem s0 sem).core.arena = sem.core.arena := rfl
@[scoped bv_c0] theorem fastPropMem_wstk (s0 sem : FullState) :
    (fastPropMem s0 sem).core.wstk = sem.core.wstk := rfl
@[scoped bv_c0] theorem fastPropMem_phases (s0 sem : FullState) :
    (fastPropMem s0 sem).scratch.phases = sem.scratch.phases := rfl
@[scoped bv_c0] theorem fastPropMem_wsort (s0 sem : FullState) :
    (fastPropMem s0 sem).scratch.wsort = sem.scratch.wsort := rfl
@[scoped bv_c0] theorem fastPropMem_delayed (s0 sem : FullState) :
    (fastPropMem s0 sem).scratch.delayed = sem.scratch.delayed := rfl
@[scoped bv_c0] theorem fastPropMem_cur_vars (s0 sem : FullState) :
    (fastPropMem s0 sem).core.cur_vars = sem.core.cur_vars := rfl
@[scoped bv_c0] theorem fastPropMem_cur_level (s0 sem : FullState) :
    (fastPropMem s0 sem).core.cur_level = sem.core.cur_level := rfl
@[scoped bv_c0] theorem fastPropMem_arena_len (s0 sem : FullState) :
    (fastPropMem s0 sem).core.arena_len = sem.core.arena_len := rfl
@[scoped bv_c0] theorem fastPropMem_oom (s0 sem : FullState) :
    (fastPropMem s0 sem).core.oom = sem.core.oom := rfl
@[scoped bv_c0] theorem fastPropMem_wlen (s0 sem : FullState) :
    (fastPropMem s0 sem).core.wlen = sem.core.wlen := rfl
@[scoped bv_c0] theorem fastPropMem_wusable (s0 sem : FullState) :
    (fastPropMem s0 sem).core.wusable = sem.core.wusable := rfl
@[scoped bv_c0] theorem fastPropMem_probing (s0 sem : FullState) :
    (fastPropMem s0 sem).core.probing = sem.core.probing := rfl
@[scoped bv_c0] theorem fastPropMem_propagated (s0 sem : FullState) :
    (fastPropMem s0 sem).core.propagated = sem.core.propagated := rfl
@[scoped bv_c0] theorem fastPropMem_trail_end (s0 sem : FullState) :
    (fastPropMem s0 sem).core.trail_end = s0.core.trail_end := rfl
@[scoped bv_c0] theorem fastPropMem_unassigned (s0 sem : FullState) :
    (fastPropMem s0 sem).core.unassigned = s0.core.unassigned := rfl
@[scoped bv_c0] theorem fastPropMem_unflushed (s0 sem : FullState) :
    (fastPropMem s0 sem).core.unflushed = s0.core.unflushed := rfl
@[scoped bv_c0] theorem fastPropMem_fuel (s0 sem : FullState) :
    (fastPropMem s0 sem).core.fuel = sem.core.fuel := rfl
@[scoped bv_c0] theorem fastPropMem_confl_type (s0 sem : FullState) :
    (fastPropMem s0 sem).core.confl_type = sem.core.confl_type := rfl
@[scoped bv_c0] theorem fastPropMem_confl_ref (s0 sem : FullState) :
    (fastPropMem s0 sem).core.confl_ref = sem.core.confl_ref := rfl
@[scoped bv_c0] theorem fastPropMem_confl_lit0 (s0 sem : FullState) :
    (fastPropMem s0 sem).core.confl_lit0 = sem.core.confl_lit0 := rfl
@[scoped bv_c0] theorem fastPropMem_confl_lit1 (s0 sem : FullState) :
    (fastPropMem s0 sem).core.confl_lit1 = sem.core.confl_lit1 := rfl
@[scoped bv_c0] theorem fastPropMem_search_ticks (s0 sem : FullState) :
    (fastPropMem s0 sem).scratch.search_ticks = sem.scratch.search_ticks := rfl
@[scoped bv_c0] theorem fastPropMem_delayed_len (s0 sem : FullState) :
    (fastPropMem s0 sem).scratch.delayed_len = sem.scratch.delayed_len := rfl
@[scoped bv_c0] theorem fastPropMem_watchSize (s0 sem : FullState) (l : Nat) :
    fullWatchSizeCore (fastPropMem s0 sem).core l = fullWatchSizeCore sem.core l := rfl
@[scoped bv_c0] theorem fastPropMem_watchOff (s0 sem : FullState) (l : Nat) :
    fullWatchOffCore (fastPropMem s0 sem).core l = fullWatchOffCore sem.core l := rfl

end BcpPropTactics

theorem fastPropMem_with_wstk (s0 sem : FullState) (w' : List (BitVec 32)) :
    { fastPropMem s0 sem with core := { (fastPropMem s0 sem).core with wstk := w' } } =
      fastPropMem s0 { sem with core := { sem.core with wstk := w' } } := rfl

theorem fastPropMem_with_arena (s0 sem : FullState) (a' : List (BitVec 32)) :
    { fastPropMem s0 sem with core := { (fastPropMem s0 sem).core with arena := a' } } =
      fastPropMem s0 { sem with core := { sem.core with arena := a' } } := rfl

theorem fastPropMem_with_vals (s0 sem : FullState) (vs' : List (BitVec 8)) :
    { fastPropMem s0 sem with core := { (fastPropMem s0 sem).core with vals := vs' } } =
      fastPropMem s0 { sem with core := { sem.core with vals := vs' } } := rfl

theorem fastPropMem_with_flags (s0 sem : FullState) (fl' : List (BitVec 32)) :
    { fastPropMem s0 sem with core := { (fastPropMem s0 sem).core with flags := fl' } } =
      fastPropMem s0 { sem with core := { sem.core with flags := fl' } } := rfl

theorem fastPropMem_with_lvl (s0 sem : FullState) (lv' : List (BitVec 32)) :
    { fastPropMem s0 sem with core := { (fastPropMem s0 sem).core with lvl := lv' } } =
      fastPropMem s0 { sem with core := { sem.core with lvl := lv' } } := rfl

theorem fastPropMem_with_rsns (s0 sem : FullState) (rs' : List (BitVec 32)) :
    { fastPropMem s0 sem with core := { (fastPropMem s0 sem).core with rsns := rs' } } =
      fastPropMem s0 { sem with core := { sem.core with rsns := rs' } } := rfl

theorem fastPropMem_with_trl (s0 sem : FullState) (tr' : List (BitVec 32)) :
    { fastPropMem s0 sem with core := { (fastPropMem s0 sem).core with trl := tr' } } =
      fastPropMem s0 { sem with core := { sem.core with trl := tr' } } := rfl

theorem fastPropMem_with_trail_pos (s0 sem : FullState) (tp' : List (BitVec 32)) :
    { fastPropMem s0 sem with core := { (fastPropMem s0 sem).core with trail_pos := tp' } } =
      fastPropMem s0 { sem with core := { sem.core with trail_pos := tp' } } := rfl

theorem fastPropMem_with_phases (s0 sem : FullState) (ph' : List (BitVec 8)) :
    { fastPropMem s0 sem with
      scratch := { (fastPropMem s0 sem).scratch with phases := ph' } } =
      fastPropMem s0 { sem with scratch := { sem.scratch with phases := ph' } } := rfl

theorem fastPropMem_with_oom (s0 sem : FullState) (oom' : BitVec 64) :
    { fastPropMem s0 sem with core := { (fastPropMem s0 sem).core with oom := oom' } } =
      fastPropMem s0 { sem with core := { sem.core with oom := oom' } } := rfl

theorem fastPropMem_with_bin_confl (s0 sem : FullState) (l0 l1 : BitVec 64) :
    { fastPropMem s0 sem with
      core := { (fastPropMem s0 sem).core with
        confl_type := 1#64, confl_lit0 := l0, confl_lit1 := l1, confl_ref := 0xFFFFFFFF#64 } } =
      fastPropMem s0 { sem with
        core := { sem.core with
          confl_type := 1#64, confl_lit0 := l0, confl_lit1 := l1, confl_ref := 0xFFFFFFFF#64 } } :=
  rfl

theorem fastPropMem_with_bin_confl_wstk (s0 sem : FullState)
    (l0 l1 : BitVec 64) (ws' : List (BitVec 32)) :
    { fastPropMem s0 sem with
      core := { (fastPropMem s0 sem).core with
        confl_type := 1#64, confl_lit0 := l0, confl_lit1 := l1,
        confl_ref := 0xFFFFFFFF#64, wstk := ws' } } =
      fastPropMem s0 { sem with
        core := { sem.core with
          confl_type := 1#64, confl_lit0 := l0, confl_lit1 := l1,
          confl_ref := 0xFFFFFFFF#64, wstk := ws' } } := rfl

theorem fastPropMem_with_large_confl_wstk (s0 sem : FullState)
    (cr : BitVec 64) (ws' : List (BitVec 32)) :
    { fastPropMem s0 sem with
      core := { (fastPropMem s0 sem).core with
        confl_type := 2#64, confl_ref := cr, wstk := ws' } } =
      fastPropMem s0 { sem with
        core := { sem.core with confl_type := 2#64, confl_ref := cr, wstk := ws' } } := rfl

theorem fastPropMem_with_large_confl (s0 sem : FullState) (cr : BitVec 64) :
    { fastPropMem s0 sem with
      core := { (fastPropMem s0 sem).core with confl_type := 2#64, confl_ref := cr } } =
      fastPropMem s0 { sem with
        core := { sem.core with confl_type := 2#64, confl_ref := cr } } := rfl

theorem fastPropMem_with_push_rec (s0 st3 : FullState)
    (wv' ws' : List (BitVec 32)) (wl' : Nat) (wu' : BitVec 64) (wso' : List (BitVec 32)) :
    { fastPropMem s0 st3 with
      core := { (fastPropMem s0 st3).core with
        wvec := wv', wstk := ws', wlen := wl', wusable := wu' }
      scratch := { (fastPropMem s0 st3).scratch with wsort := wso' } } =
      fastPropMem s0 { st3 with
        core := { st3.core with wvec := wv', wstk := ws', wlen := wl', wusable := wu' }
        scratch := { st3.scratch with wsort := wso' } } := rfl

theorem fastPropMem_with_oom_revert (s0 st4 : FullState) (ar' ws' : List (BitVec 32)) :
    { fastPropMem s0 st4 with
      core := { (fastPropMem s0 st4).core with arena := ar', wstk := ws', oom := 1#64 } } =
      fastPropMem s0 { st4 with
        core := { st4.core with arena := ar', wstk := ws', oom := 1#64 } } := rfl

theorem fastPropMem_with_vals_ph (s0 sem : FullState)
    (vs' : List (BitVec 8)) (ph' : List (BitVec 8)) :
    FullState.mk
      { (fastPropMem s0 sem).core with vals := vs' }
      { (fastPropMem s0 sem).scratch with phases := ph' } =
      fastPropMem s0 (FullState.mk
        { sem.core with vals := vs' } { sem.scratch with phases := ph' }) := rfl

theorem fastPropMem_lengthsOk {c : FullCfg} {s0 sem mem : FullState}
    (h1 : s0.LengthsOk c) (h2 : sem.LengthsOk c)
    (hcv : s0.core.cur_vars = sem.core.cur_vars)
    (hpr : sem.core.propagated ≤ s0.core.trail_end) (hm : mem = fastPropMem s0 sem) :
    mem.LengthsOk c := by
  subst hm
  refine ⟨⟨h2.core_ok.vals_len, h1.core_ok.lit_mark_len, h1.core_ok.mrk_len,
    h2.core_ok.flags_len, h2.core_ok.lvl_len, h2.core_ok.rsns_len, h2.core_ok.trl_len,
    h2.core_ok.trail_pos_len, h1.core_ok.tmp_len_arr, h1.core_ok.min_clr_len_arr,
    h1.core_ok.frame_trail_len, h1.core_ok.frame_dec_len, h2.core_ok.wvec_len,
    h1.core_ok.repr_len, h1.core_ok.min_stk_len, h2.core_ok.arena_len_arr,
    h2.core_ok.wstk_len_arr, h2.core_ok.cur_vars_ge, h2.core_ok.cur_vars_le,
    h2.core_ok.arena_len_le, h2.core_ok.wlen_le, hcv ▸ h1.core_ok.trail_end_le,
    hpr, h1.core_ok.tmp_len_le, h1.core_ok.min_clr_len_le⟩,
    { h1.scratch_ok with
      phases_len := h2.scratch_ok.phases_len, wsort_len := h2.scratch_ok.wsort_len,
      delayed_len_arr := h2.scratch_ok.delayed_len_arr }⟩

theorem fastPropMem_watchLayout {s0 sem mem : FullState}
    (h : WatchStackLayout sem.core) (hm : mem = fastPropMem s0 sem) :
    WatchStackLayout mem.core := by
  subst hm; exact h.with_wstk rfl rfl rfl rfl

/-! ## 2. Masks, `PropLitConfl`, `PropLitInv` (with `FullTrailRsnsPres`), & Equivalences -/

@[expose] def propLitCoreMask (k : FullCoreState) : FullCoreState :=
  { k with
    vals := [], flags := [], lvl := [], rsns := [], trl := [], trail_pos := [],
    trail_end := 0, unassigned := 0#64, unflushed := 0#64,
    wvec := [], arena := [], wstk := [], wlen := 0, wusable := 0#64,
    confl_type := 0#64, confl_ref := 0#64, confl_lit0 := 0#64, confl_lit1 := 0#64, oom := 0#64 }

@[expose] def fidCoreMask (t : FullCoreState) : FullCoreState :=
  { propLitCoreMask t with propagated := 0, fuel := 0#64 }

theorem fid_core_eq_of_agrees (s sem : FullCoreState) (h : AgreesExcept fidCoreMask s sem) :
    sem = { s with
      vals := sem.vals, flags := sem.flags, lvl := sem.lvl, rsns := sem.rsns, trl := sem.trl,
      trail_pos := sem.trail_pos, trail_end := sem.trail_end, propagated := sem.propagated,
      unassigned := sem.unassigned, unflushed := sem.unflushed, wvec := sem.wvec,
      arena := sem.arena, wstk := sem.wstk, wlen := sem.wlen, wusable := sem.wusable,
      fuel := sem.fuel, confl_type := sem.confl_type, confl_ref := sem.confl_ref,
      confl_lit0 := sem.confl_lit0, confl_lit1 := sem.confl_lit1, oom := sem.oom } := by
  unfold AgreesExcept fidCoreMask propLitCoreMask at h
  cases s; cases sem; simp_all

@[expose] def PropLitConfl (F_cur : List (List Nat)) (ignore_ref : BitVec 64)
    (k : FullCoreState) : Prop :=
  FullConflOkW F_cur k ∧ (k.confl_type = 2#64 → k.confl_ref ≠ ignore_ref)

theorem propLit_confl_toOkW {F_cur : List (List Nat)} {ignore_ref : BitVec 64}
    {k : FullCoreState} (h : PropLitConfl F_cur ignore_ref k) :
    FullConflOkW F_cur k ∧ (k.confl_type = 2#64 → k.confl_ref ≠ ignore_ref) := h

theorem propLit_confl_mono {F_cur : List (List Nat)} {ignore_ref : BitVec 64}
    {k k' : FullCoreState} (h : PropLitConfl F_cur ignore_ref k)
    (hcv : k'.cur_vars = k.cur_vars) (hct : k'.confl_type = k.confl_type)
    (hc0 : k'.confl_lit0 = k.confl_lit0) (hc1 : k'.confl_lit1 = k.confl_lit1)
    (hcr : k'.confl_ref = k.confl_ref)
    (href : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hg : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r)
    (hlits : ∀ r ∈ fullArenaClauseRefsCore k,
      (fullArenaClauseLitsCore k' r).Perm (fullArenaClauseLitsCore k r))
    (hvals : ∀ l < 2 * k.cur_vars, k'.vals[l]?.getD 0#8 = k.vals[l]?.getD 0#8)
    (har_lt : ∀ r ∈ fullArenaClauseRefsCore k, fullArenaClauseGarbCore k r = false →
      ∀ l ∈ fullArenaClauseLitsCore k r, l < 2 * k.cur_vars) :
    PropLitConfl F_cur ignore_ref k' := by
  refine ⟨?_, fun h2 => hcr ▸ h.2 (hct ▸ h2)⟩
  rcases h.1 with ⟨ht, h0, h1, hent, hf0, hf1⟩ | ⟨ht, hrm, hng, hfals⟩
  · left; refine ⟨hct ▸ ht, hcv ▸ hc0 ▸ h0, hcv ▸ hc1 ▸ h1, hc0 ▸ hc1 ▸ hent, ?_, ?_⟩
    · rw [hc0, hvals _ h0]; exact hf0
    · rw [hc1, hvals _ h1]; exact hf1
  · right; refine ⟨hct ▸ ht, hcr ▸ href _ hrm, hcr ▸ (hg _ hrm).trans hng, fun l hl => ?_⟩
    rw [hcr] at hl
    have hl0 := (hlits _ hrm).mem_iff.mp hl
    rw [hvals l (har_lt _ hrm hng l hl0)]; exact hfals l hl0

/-- Inner-loop compaction & propagation invariant for `full_propagate*` carrying `FullTrailExt`,
`FullTrailRsnsPres`, `FullArenaPermEq`, `SplitWatchesInv`, and scratch equality. -/
structure PropLitInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s st : FullState) (not_lit off q p end_v : Nat) : Prop where
  len : st.LengthsOk c
  nw : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st.core)
  sw : SplitWatchesInv F_cur st.core not_lit off q p end_v
  ag : AgreesExcept propLitCoreMask s.core st.core
  tr : FullTrailExt s.core st.core
  rsns_pres : FullTrailRsnsPres s.core st.core
  perm : FullArenaPermEq s.core st.core
  sc_eq : st.scratch = { s.scratch with
    search_ticks := st.scratch.search_ticks, wsort := st.scratch.wsort,
    phases := st.scratch.phases }
  not_f : st.core.vals[not_lit]?.getD 0#8 = 0xFF#8

theorem PropLitInv.end_lt_wcap {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {not_lit off q p end_v : Nat}
    (h : PropLitInv c F0 F_cur s st not_lit off q p end_v) (hnot : not_lit < 2 * st.core.cur_vars) :
    end_v ≤ st.core.wlen ∧ st.core.wlen ≤ c.wcap :=
  SplitWatchesInv.end_lt_wcap h.len.core_ok h.sw hnot

theorem PropLitInv.push_nonskip {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st st' : FullState} {not_lit off q p end_v lit w0 cref : Nat}
    (h : PropLitInv c F0 F_cur s st not_lit off q p end_v)
    (hnot : not_lit < 2 * st.core.cur_vars) (hlit : lit < 2 * st.core.cur_vars)
    (hlit_ne : lit ≠ not_lit) (hlen' : st'.LengthsOk c) (hlay' : WatchStackLayout st'.core)
    (hc_eq : st'.core = { st.core with
      wvec := st'.core.wvec, wstk := st'.core.wstk, wlen := st'.core.wlen,
      wusable := st'.core.wusable })
    (hsc_eq : st'.scratch = { st.scratch with wsort := st'.scratch.wsort })
    (hother : ∀ l < 2 * st.core.cur_vars, l ≠ lit →
      fullWatchSizeCore st'.core l = fullWatchSizeCore st.core l ∧
      ∀ idx < fullWatchSizeCore st.core l,
        st'.core.wstk[fullWatchOffCore st'.core l + idx]? =
          st.core.wstk[fullWatchOffCore st.core l + idx]?)
    (hlit_ok : fullWatchSizeCore st'.core lit = fullWatchSizeCore st.core lit + 2 ∧
      (∀ idx < fullWatchSizeCore st.core lit,
        st'.core.wstk[fullWatchOffCore st'.core lit + idx]? =
          st.core.wstk[fullWatchOffCore st.core lit + idx]?) ∧
      st'.core.wstk[fullWatchOffCore st'.core lit + fullWatchSizeCore st.core lit]? =
        some (BitVec.ofNat 32 w0) ∧
      st'.core.wstk[fullWatchOffCore st'.core lit + fullWatchSizeCore st.core lit + 1]? =
        some (BitVec.ofNat 32 cref))
    (hw0_flag : (BitVec.ofNat 32 w0 &&& 0x80000000#32) = 0#32)
    (hcr_lt : cref < 0x80000000) (hcr_ref : cref ∈ fullArenaClauseRefsCore st'.core) :
    let off' := fullWatchOffCore st'.core not_lit
    PropLitInv c F0 F_cur s st' not_lit off'
      (off' + (q - off)) (off' + (p - off)) (off' + (end_v - off)) := by
  have hnw' := fullWitnessInv_nw_congr hlen'.core_ok.cur_vars_le h.nw
    (by rw [hc_eq]) (by rw [hc_eq]) (by rw [hc_eq]) (by rw [hc_eq])
    (by rw [hc_eq]) (by rw [hc_eq]) (by rw [hc_eq]) (by rw [hc_eq])
    (by rw [hc_eq]) (by rw [hc_eq]) (by rw [hc_eq]) (by rw [hc_eq]) (by rw [hc_eq])
  have hsw' := SplitWatchesInv.push_nonskip (by rw [hc_eq]) (by rw [hc_eq]; exact fun _ hr => hr)
    hlit hlit_ne h.sw hnot hlay' hother hlit_ok hw0_flag hcr_lt hcr_ref
  have hag' : AgreesExcept propLitCoreMask s.core st'.core := by
    have hu := h.ag.update (fun k =>
      { k with
        wvec := st'.core.wvec, wstk := st'.core.wstk,
        wlen := st'.core.wlen, wusable := st'.core.wusable })
    simpa only [← hc_eq] using hu
  have htr' : FullTrailExt s.core st'.core :=
    fullTrailExt_congr h.tr (by rw [hc_eq]) (by rw [hc_eq]) (by rw [hc_eq])
  have hrsns' : FullTrailRsnsPres s.core st'.core :=
    fullTrailRsnsPres_congr h.rsns_pres (by rw [hc_eq])
  have hperm' : FullArenaPermEq s.core st'.core := by
    obtain ⟨hal, hrf, hcl⟩ := h.perm
    exact ⟨by rw [hc_eq]; exact hal, by unfold fullArenaClauseRefsCore; rw [hc_eq]; exact hrf,
      fun r hr => by
        obtain ⟨s1, g1, p1⟩ := hcl r hr
        unfold fullArenaClauseSizeCore fullArenaClauseGarbCore fullArenaClauseLitsCore
          fullArenaHdrCore
        rw [hc_eq]; exact ⟨s1, g1, p1⟩⟩
  have hsc' : st'.scratch = { s.scratch with
      search_ticks := st'.scratch.search_ticks, wsort := st'.scratch.wsort,
      phases := st'.scratch.phases } := by rw [hsc_eq, h.sc_eq]
  have hnf' : st'.core.vals[not_lit]?.getD 0#8 = 0xFF#8 := by rw [hc_eq]; exact h.not_f
  exact ⟨hlen', hnw', hsw', hag', htr', hrsns', hperm', hsc', hnf'⟩

theorem fastProp_nlLvl_const {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {_s st : FullState} {not_lit new_lit : BitVec 32} {alvl : BitVec 32}
    {rsn' : BitVec 32} {flags' : List (BitVec 32)} {unas' unfl' : BitVec 64}
    {ph' : List (BitVec 8)}
    (_hl : st.LengthsOk c) (hnw : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st.core))
    (hnot_lt : not_lit.toNat < 2 * st.core.cur_vars)
    (hnot_f : st.core.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8)
    (hun : st.core.vals[new_lit.toNat]?.getD 0#8 = 0#8) :
    let st2 : FullState :=
      { core :=
          { st.core with
            vals := (st.core.vals.set new_lit.toNat 1#8).set (new_lit.toNat ^^^ 1) 0xFF#8
            flags := flags', lvl := st.core.lvl.set (new_lit.toNat / 2) alvl
            rsns := st.core.rsns.set (new_lit.toNat / 2) rsn'
            trl := st.core.trl.set st.core.trail_end new_lit
            trail_pos := st.core.trail_pos.set (new_lit.toNat / 2)
              (BitVec.ofNat 32 st.core.trail_end)
            trail_end := st.core.trail_end + 1, unassigned := unas', unflushed := unfl' }
        scratch := { st.scratch with phases := ph' } }
    st2.core.lvl[not_lit.toNat / 2]?.getD 0#32 = st.core.lvl[not_lit.toNat / 2]?.getD 0#32 := by
  intro st2
  have hne : new_lit.toNat / 2 ≠ not_lit.toNat / 2 := by
    intro heq
    obtain ⟨m, hm, hm_eq⟩ := (hnw.vals_false_iff not_lit.toNat
      (by dsimp only [withEmptyWatchesCore]; exact hnot_lt)).mp hnot_f
    have hnone := (hnw.vals_zero_iff (by
      dsimp only [withEmptyWatchesCore]
      have := hnw.vals_domain new_lit.toNat
      have : new_lit.toNat / 2 = not_lit.toNat / 2 := heq
      omega)).mp hun m hm
    dsimp only [withEmptyWatchesCore] at hm_eq hnone
    rw [hm_eq, fullInv_var_xor1] at hnone; exact hnone heq.symm
  dsimp only [st2]; rw [List.getElem?_set_ne hne]

theorem fastPropMem_eq_of_eq {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st1 st2 : FullState} {not_lit other : BitVec 32} {off_v q_v p_v end_v : Nat}
    {alvl rsn' : BitVec 32} {flags' : List (BitVec 32)} {ph' : List (BitVec 8)}
    {unas' unfl' : BitVec 64} {nl_lvl0 : BitVec 32}
    (hpi : PropLitInv c F0 F_cur s st1 not_lit.toNat off_v q_v p_v end_v)
    (hsw2 : SplitWatchesInv F_cur st2.core not_lit.toNat off_v q_v p_v end_v)
    (hst2_eq : st2 =
      { core :=
          { st1.core with
            vals := (st1.core.vals.set other.toNat 1#8).set (other.toNat ^^^ 1) 0xFF#8
            flags := flags', lvl := st1.core.lvl.set (other.toNat / 2) alvl
            rsns := st1.core.rsns.set (other.toNat / 2) rsn'
            trl := st1.core.trl.set st1.core.trail_end other
            trail_pos := st1.core.trail_pos.set (other.toNat / 2)
              (BitVec.ofNat 32 st1.core.trail_end)
            trail_end := st1.core.trail_end + 1, unassigned := unas', unflushed := unfl' }
        scratch := { st1.scratch with phases := ph' } })
    (hfl : flags'.length = c.max_vars) (hph : ph'.length = c.max_vars)
    (hnot_lt : not_lit.toNat < 2 * st1.core.cur_vars)
    (hother_lt : other.toNat < 2 * st1.core.cur_vars)
    (hun : st1.core.vals[other.toNat]?.getD 0#8 = 0#8)
    (hnl : st1.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0)
    (hstep : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st2.core) ∧
      FullTrailExt st1.core st2.core ∧ FullTrailRsnsPres st1.core st2.core) :
    PropLitInv c F0 F_cur s st2 not_lit.toNat off_v q_v p_v end_v ∧
    st2.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0 := by
  have hcl := hpi.len.core_ok; have hsc := hpi.len.scratch_ok
  have hte_lt_cv : st1.core.trail_end < st1.core.cur_vars := by
    have := hpi.nw.trail_end_lt_of_unassigned (by dsimp [withEmptyWatchesCore]; exact hother_lt)
      (by dsimp [withEmptyWatchesCore]; exact hun)
    dsimp [withEmptyWatchesCore] at this; exact this
  have hte_lt : st1.core.trail_end < c.max_vars := by have := hcl.cur_vars_le; omega
  have hoth_mv : other.toNat / 2 < c.max_vars := by have := hcl.cur_vars_le; omega
  have hlen2 : st2.LengthsOk c := by
    subst hst2_eq
    refine ⟨{ hcl with
      vals_len := by simp [hcl.vals_len], flags_len := hfl, lvl_len := by simp [hcl.lvl_len],
      rsns_len := by simp [hcl.rsns_len], trl_len := by simp [hcl.trl_len],
      trail_pos_len := by simp [hcl.trail_pos_len],
      trail_end_le := by dsimp only; exact Nat.succ_le_of_lt hte_lt_cv,
      propagated_le := by dsimp only; exact Nat.le_trans hcl.propagated_le (Nat.le_succ _) },
      { hsc with phases_len := hph }⟩
  have hnot_var : other.toNat / 2 ≠ not_lit.toNat / 2 := by
    intro heq
    obtain ⟨m, hm, hm_eq⟩ := (hpi.nw.vals_false_iff not_lit.toNat
      (by dsimp [withEmptyWatchesCore]; exact hnot_lt)).mp hpi.not_f
    have hz := (hpi.nw.vals_zero_iff (by dsimp [withEmptyWatchesCore]; omega)).mp hun m hm
    dsimp [withEmptyWatchesCore] at hm_eq hz
    rw [hm_eq, fullInv_var_xor1] at hz; exact hz heq.symm
  have hnot_ne1 : not_lit.toNat ≠ other.toNat := fun heq => by
    apply hnot_var; rw [heq]
  have hnot_ne2 : not_lit.toNat ≠ other.toNat ^^^ 1 := fun heq => by
    apply hnot_var; rw [heq, fullInv_var_xor1]
  have hnf2 : st2.core.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8 := by
    rw [hst2_eq]; dsimp only
    rw [List.getElem?_set_ne (Ne.symm hnot_ne2), List.getElem?_set_ne (Ne.symm hnot_ne1)]
    exact hpi.not_f
  have hag2 : AgreesExcept propLitCoreMask s.core st2.core := by
    have hu := hpi.ag.update fun k =>
      { k with
        vals := (k.vals.set other.toNat 1#8).set (other.toNat ^^^ 1) 0xFF#8,
        flags := flags', lvl := k.lvl.set (other.toNat / 2) alvl,
        rsns := k.rsns.set (other.toNat / 2) rsn',
        trl := k.trl.set k.trail_end other,
        trail_pos := k.trail_pos.set (other.toNat / 2) (BitVec.ofNat 32 k.trail_end),
        trail_end := k.trail_end + 1, unassigned := unas', unflushed := unfl' }
    rw [hst2_eq]; exact hu
  have hperm2 : FullArenaPermEq s.core st2.core := by
    obtain ⟨hal, hrf, hcl_p⟩ := hpi.perm
    have har : st2.core.arena = st1.core.arena := by rw [hst2_eq]
    have hal2 : st2.core.arena_len = st1.core.arena_len := by rw [hst2_eq]
    refine ⟨hal2.trans hal, ?_, fun r hr => ?_⟩
    · unfold fullArenaClauseRefsCore; rw [har, hal2]; exact hrf
    · obtain ⟨s1, g1, p1⟩ := hcl_p r hr
      have hs : fullArenaClauseSizeCore st2.core r = fullArenaClauseSizeCore st1.core r := by
        unfold fullArenaClauseSizeCore; rw [har]
      have hg : fullArenaClauseGarbCore st2.core r = fullArenaClauseGarbCore st1.core r := by
        unfold fullArenaClauseGarbCore fullArenaHdrCore; rw [har]
      have hl : fullArenaClauseLitsCore st2.core r = fullArenaClauseLitsCore st1.core r := by
        unfold fullArenaClauseLitsCore fullArenaClauseSizeCore; rw [har]
      exact ⟨hs.trans s1, hg.trans g1, hl ▸ p1⟩
  have hsc2 : st2.scratch = { s.scratch with
      search_ticks := st2.scratch.search_ticks, wsort := st2.scratch.wsort,
      phases := st2.scratch.phases } := by
    rw [hst2_eq]; dsimp only; rw [hpi.sc_eq]
  have hnl2 : st2.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0 := by
    rw [hst2_eq]; dsimp only; rw [List.getElem?_set_ne hnot_var]; exact hnl
  exact ⟨⟨hlen2, hstep.1, hsw2, hag2, fullTrailExt_trans hpi.tr hstep.2.1,
    fullTrailRsnsPres_trans hpi.tr hpi.rsns_pres hstep.2.2, hperm2, hsc2, hnf2⟩, hnl2⟩

theorem m7_bin_assign_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s_pi sem : FullState} {not_lit blk alvl nl_lvl0 : BitVec 32}
    {off_v p_v q_v end_v : BitVec 64} {flags' : List (BitVec 32)} {ph' : List (BitVec 8)}
    {unas' unfl' : BitVec 64}
    (hpi : PropLitInv c F0 F_cur s_pi sem not_lit.toNat off_v.toNat (q_v + 1#64).toNat
      (p_v.toNat + 1) end_v.toNat)
    (hfl : flags'.length = c.max_vars) (hph : ph'.length = c.max_vars)
    (hnot_lt : not_lit.toNat < 2 * sem.core.cur_vars)
    (hblk_lt : blk.toNat < 2 * sem.core.cur_vars)
    (hun : sem.core.vals[blk.toNat]?.getD 0#8 = 0#8)
    (halvl : alvl.toNat ≤ sem.core.cur_level)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [not_lit.toNat, blk.toNat]))
    (hnl : sem.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0)
    (hnl_le : (sem.core.lvl[not_lit.toNat / 2]?.getD 0#32).toNat ≤ alvl.toNat)
    (halvl_eq : alvl = 0#32 ↔ (sem.core.lvl[not_lit.toNat / 2]?.getD 0#32) = 0#32) :
    let rsn0 := (not_lit &&& 0x7FFFFFFF#32) ||| 0x80000000#32
    let rsn' := if alvl = 0#32 then 0xFFFFFFFF#32 else rsn0
    let sem2 : FullState :=
      { core :=
          { sem.core with
            vals := (sem.core.vals.set blk.toNat 1#8).set (blk.toNat ^^^ 1) 0xFF#8
            flags := flags', lvl := sem.core.lvl.set (blk.toNat / 2) alvl
            rsns := sem.core.rsns.set (blk.toNat / 2) rsn'
            trl := sem.core.trl.set sem.core.trail_end blk
            trail_pos := sem.core.trail_pos.set (blk.toNat / 2)
              (BitVec.ofNat 32 sem.core.trail_end)
            trail_end := sem.core.trail_end + 1, unassigned := unas', unflushed := unfl' }
        scratch := { sem.scratch with phases := ph' } }
    PropLitInv c F0 F_cur s_pi sem2 not_lit.toNat off_v.toNat (q_v + 1#64).toNat
      (p_v.toNat + 1) end_v.toNat ∧
    sem2.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0 := by
  intro rsn0 rsn' sem2
  have hstep := full_bin_assign_nw_step hpi.len.core_ok hpi.nw halvl hblk_lt hun hnot_lt
    hpi.not_f hent hnl_le halvl_eq flags' unas' unfl'
  have hsw2 : SplitWatchesInv F_cur sem2.core not_lit.toNat off_v.toNat
      (q_v + 1#64).toNat (p_v.toNat + 1) end_v.toNat :=
    SplitWatchesInv.with_nonwatch hpi.sw rfl rfl rfl rfl (fun _ hr => hr)
  exact fastPropMem_eq_of_eq hpi hsw2 rfl hfl hph hnot_lt hblk_lt hun hnl hstep

theorem m7_large_assign_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s_pi sem : FullState} {not_lit other cref alvl nl_lvl0 : BitVec 32}
    {off_v p_v q_v end_v : BitVec 64} {flags' : List (BitVec 32)} {ph' : List (BitVec 8)}
    {unas' unfl' : BitVec 64}
    (hpi : PropLitInv c F0 F_cur s_pi sem not_lit.toNat off_v.toNat (q_v + 2#64).toNat
      (p_v.toNat + 2) end_v.toNat)
    (hfl : flags'.length = c.max_vars) (hph : ph'.length = c.max_vars)
    (hcr_lt : cref.toNat < 0x80000000) (hcref : cref.toNat ∈ fullArenaClauseRefsCore sem.core)
    (hng : fullArenaClauseGarbCore sem.core cref.toNat = false)
    (hnot_lt : not_lit.toNat < 2 * sem.core.cur_vars)
    (hother_lt : other.toNat < 2 * sem.core.cur_vars)
    (hun : sem.core.vals[other.toNat]?.getD 0#8 = 0#8)
    (_hnot_mem : not_lit.toNat ∈ fullArenaClauseLitsCore sem.core cref.toNat)
    (hother_mem : other.toNat ∈ fullArenaClauseLitsCore sem.core cref.toNat)
    (hunit : ∀ l ∈ fullArenaClauseLitsCore sem.core cref.toNat,
      l = other.toNat ∨ sem.core.vals[l]?.getD 0#8 = 0xFF#8)
    (hnl : sem.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0)
    (hmax_ge : ∀ l ∈ fullArenaClauseLitsCore sem.core cref.toNat, l ≠ other.toNat →
      (sem.core.lvl[l / 2]?.getD 0#32).toNat ≤ alvl.toNat)
    (hmax_att : alvl = 0#32 ∨ ∃ l ∈ fullArenaClauseLitsCore sem.core cref.toNat,
      l ≠ other.toNat ∧ alvl = sem.core.lvl[l / 2]?.getD 0#32) :
    let rsn' := if alvl = 0#32 then 0xFFFFFFFF#32 else cref
    let sem2 : FullState :=
      { core :=
          { sem.core with
            vals := (sem.core.vals.set other.toNat 1#8).set (other.toNat ^^^ 1) 0xFF#8
            flags := flags', lvl := sem.core.lvl.set (other.toNat / 2) alvl
            rsns := sem.core.rsns.set (other.toNat / 2) rsn'
            trl := sem.core.trl.set sem.core.trail_end other
            trail_pos := sem.core.trail_pos.set (other.toNat / 2)
              (BitVec.ofNat 32 sem.core.trail_end)
            trail_end := sem.core.trail_end + 1, unassigned := unas', unflushed := unfl' }
        scratch := { sem.scratch with phases := ph' } }
    PropLitInv c F0 F_cur s_pi sem2 not_lit.toNat off_v.toNat (q_v + 2#64).toNat
      (p_v.toNat + 2) end_v.toNat ∧
    sem2.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0 := by
  intro rsn' sem2
  have hstep := full_large_assign_nw_step hpi.len.core_ok hpi.nw hcr_lt hcref hng hother_lt hun
    hnot_lt hpi.not_f hother_mem hunit hmax_ge hmax_att flags' unas' unfl'
  have hsw2 : SplitWatchesInv F_cur sem2.core not_lit.toNat off_v.toNat
      (q_v + 2#64).toNat (p_v.toNat + 2) end_v.toNat :=
    SplitWatchesInv.with_nonwatch hpi.sw rfl rfl rfl rfl (fun _ hr => hr)
  exact fastPropMem_eq_of_eq hpi hsw2 rfl hfl hph hnot_lt hother_lt hun hnl hstep

theorem m7_nonchrono_alvl_facts {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} {cref other not_lit nl_lvl : BitVec 32}
    (hnw : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k))
    (hcref : cref.toNat ∈ fullArenaClauseRefsCore k)
    (hng : fullArenaClauseGarbCore k cref.toNat = false)
    (hnot_f : k.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8)
    (hun : k.vals[other.toNat]?.getD 0#8 = 0#8)
    (hnot_mem : not_lit.toNat ∈ fullArenaClauseLitsCore k cref.toNat)
    (_hunit : ∀ l ∈ fullArenaClauseLitsCore k cref.toNat,
      l = other.toNat ∨ k.vals[l]?.getD 0#8 = 0xFF#8)
    (hnl : k.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl)
    (hge_cl : ∀ l ∈ fullArenaClauseLitsCore k cref.toNat, l ≠ other.toNat →
      (k.lvl[l / 2]?.getD 0#32).toNat ≤ nl_lvl.toNat)
    (hlv_eq : nl_lvl.toNat = k.cur_level) :
    (∀ l ∈ fullArenaClauseLitsCore k cref.toNat, l ≠ other.toNat →
      (k.lvl[l / 2]?.getD 0#32).toNat ≤ nl_lvl.toNat) ∧
    (nl_lvl = 0#32 ∨ ∃ l ∈ fullArenaClauseLitsCore k cref.toNat,
      l ≠ other.toNat ∧ nl_lvl = k.lvl[l / 2]?.getD 0#32) := by
  have _ := (hnw.arena.lits_lt cref.toNat hcref hng)
  have _ := hlv_eq
  refine ⟨hge_cl, Or.inr ⟨not_lit.toNat, hnot_mem,
    (fun heq => by rw [heq, hun] at hnot_f; cases hnot_f), hnl.symm⟩⟩

theorem fastProp_findRepl_ok {st : FullState} {cref r : Nat}
    {hi_lt : cref + 3 + r < st.core.arena.length}
    {hj_lt : (st.core.arena[cref + 3 + r]'hi_lt).toNat < st.core.vals.length}
    (hcv : (st.core.arena[cref + 3 + r]'hi_lt).toNat < 2 * st.core.cur_vars)
    (hsle : (0#32).sle ((st.core.vals[(st.core.arena[cref + 3 + r]'hi_lt).toNat]'hj_lt).signExtend
      32) = true) :
    let cand := (st.core.arena[cref + 3 + r]?.getD 0#32).toNat
    cand < 2 * st.core.cur_vars ∧
    ((st.core.vals[cand]?.getD 0#8).signExtend 32).slt 0#32 = false := by
  dsimp only; rw [List.getElem?_eq_getElem hi_lt, Option.getD_some,
    List.getElem?_eq_getElem hj_lt, Option.getD_some]
  refine ⟨hcv, ?_⟩; rw [bv32_sle0_eq_not_slt0, Bool.not_eq_true'] at hsle; exact hsle

theorem fastProp_findRepl_bad_slt {st : FullState} {cref r : Nat}
    {hi_lt : cref + 3 + r < st.core.arena.length}
    {hj_lt : (st.core.arena[cref + 3 + r]'hi_lt).toNat < st.core.vals.length}
    (h : (0#32).sle ((st.core.vals[(st.core.arena[cref + 3 + r]'hi_lt).toNat]'hj_lt).signExtend
      32) = false) : fullFindReplBad st cref r := by
  unfold fullFindReplBad; refine Or.inr ?_
  rw [List.getElem?_eq_getElem hi_lt, Option.getD_some,
    List.getElem?_eq_getElem hj_lt, Option.getD_some]
  rw [bv32_sle0_eq_not_slt0, Bool.not_eq_false'] at h; exact h

theorem fastProp_findRepl_bad_oob {st : FullState} {cref r nlits : Nat}
    {hi_lt : cref + 3 + r < st.core.arena.length}
    (hnl : nlits = 2 * st.core.cur_vars)
    (h : ¬(st.core.arena[cref + 3 + r]'hi_lt).toNat < nlits) :
    fullFindReplBad st cref r := by
  unfold fullFindReplBad; refine Or.inl ?_
  rw [List.getElem?_eq_getElem hi_lt, Option.getD_some]; omega

theorem m7_setSrch_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s_pi sem1 : FullState} {not_lit l0 l1 cref repl : BitVec 32}
    {ri_n : Nat} {ri32 : BitVec 32} {off_v p_v q_v end_v : BitVec 64}
    (hpi : PropLitInv c F0 F_cur s_pi sem1 not_lit.toNat off_v.toNat q_v.toNat
      (p_v.toNat + 2) end_v.toNat)
    (hcref : cref.toNat ∈ fullArenaClauseRefsCore sem1.core)
    (har3 : sem1.core.arena[cref.toNat + 3]? = some l0)
    (har4 : sem1.core.arena[cref.toNat + 4]? = some l1)
    (har_ri : sem1.core.arena[cref.toNat + 3 + ri_n]? = some repl) :
    let sem2 : FullState :=
      { sem1 with core := { sem1.core with arena := sem1.core.arena.set (cref.toNat + 1) ri32 } }
    PropLitInv c F0 F_cur s_pi sem2 not_lit.toNat off_v.toNat q_v.toNat
      (p_v.toNat + 2) end_v.toNat ∧
    sem2.LengthsOk c ∧ cref.toNat ∈ fullArenaClauseRefsCore sem2.core ∧
    fullArenaClauseSizeCore sem2.core cref.toNat = fullArenaClauseSizeCore sem1.core cref.toNat ∧
    sem2.core.arena[cref.toNat + 3]? = some l0 ∧
    sem2.core.arena[cref.toNat + 4]? = some l1 ∧
    sem2.core.arena[cref.toNat + 3 + ri_n]? = some repl := by
  intro sem2
  have haren := hpi.len.core_ok.arena_len_arr
  have hstep := full_setSrch_preserves_nw hpi.len.core_ok hpi.nw (srch := ri32) hcref
  have hlen2 : sem2.LengthsOk c :=
    ⟨{ hpi.len.core_ok with arena_len_arr := by simp [sem2, haren] }, hpi.len.scratch_ok⟩
  have hnw2 := fullWitnessInv_nw_congr hlen2.core_ok.cur_vars_le hstep.1
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hperm2 := hstep.2
  have hsw2 := SplitWatchesInv.with_nonwatch (k' := sem2.core) hpi.sw rfl rfl rfl rfl
    (fun _ r => hperm2.2.1 ▸ r)
  have hpi2 : PropLitInv c F0 F_cur s_pi sem2 not_lit.toNat off_v.toNat q_v.toNat
      (p_v.toNat + 2) end_v.toNat :=
    { len := hlen2, nw := hnw2, sw := hsw2
      ag := hpi.ag.update (fun k => { k with arena := sem2.core.arena })
      tr := fullTrailExt_congr hpi.tr rfl rfl rfl
      rsns_pres := fullTrailRsnsPres_congr hpi.rsns_pres rfl
      perm := fullArenaPermEq_trans hpi.perm hperm2, sc_eq := hpi.sc_eq, not_f := hpi.not_f }
  refine ⟨hpi2, hlen2, hperm2.2.1.symm ▸ hcref, (hperm2.2.2 _ hcref).1, ?_, ?_, ?_⟩
  · simp only [sem2]; rw [List.getElem?_set_ne (by omega)]; exact har3
  · simp only [sem2]; rw [List.getElem?_set_ne (by omega)]; exact har4
  · simp only [sem2]; rw [List.getElem?_set_ne (by omega)]; exact har_ri

theorem fid_pi_rebase {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 s_pi st : FullState} {not_lit off_v q_v p_v end_v : Nat}
    (hpi : PropLitInv c F0 F_cur s0 st not_lit off_v q_v p_v end_v)
    (hag : AgreesExcept propLitCoreMask s_pi.core st.core)
    (htr : FullTrailExt s_pi.core st.core) (hrsn : FullTrailRsnsPres s_pi.core st.core)
    (hperm : FullArenaPermEq s_pi.core st.core)
    (hsc : st.scratch = { s_pi.scratch with
      search_ticks := st.scratch.search_ticks, wsort := st.scratch.wsort,
      phases := st.scratch.phases }) :
    PropLitInv c F0 F_cur s_pi st not_lit off_v q_v p_v end_v :=
  { hpi with ag := hag, tr := htr, rsns_pres := hrsn, perm := hperm, sc_eq := hsc }

theorem m7_ovf_swap_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s_pi st : FullState} {not_lit repl cref : BitVec 32}
    {ri_n : Nat} {off_v q_v p_v end_v : BitVec 64}
    (hpi : PropLitInv c F0 F_cur s_pi st not_lit.toNat off_v.toNat q_v.toNat p_v.toNat end_v.toNat)
    (hcref : cref.toNat ∈ fullArenaClauseRefsCore st.core)
    (hcsz3 : 3 ≤ fullArenaClauseSizeCore st.core cref.toNat)
    (hfit : cref.toNat + 3 + fullArenaClauseSizeCore st.core cref.toNat ≤ st.core.arena_len)
    (har4 : st.core.arena[cref.toNat + 4]? = some repl)
    (_hri2 : 2 ≤ ri_n) (hri_lt : ri_n < fullArenaClauseSizeCore st.core cref.toNat)
    (har_ri : st.core.arena[cref.toNat + 3 + ri_n]? = some not_lit) :
    let st' : FullState :=
      { st with core := { st.core with
        arena := (st.core.arena.set (cref.toNat + 4) not_lit).set (cref.toNat + 3 + ri_n) repl } }
    PropLitInv c F0 F_cur s_pi st' not_lit.toNat off_v.toNat q_v.toNat p_v.toNat end_v.toNat := by
  intro st'
  have haren := hpi.len.core_ok.arena_len_arr; have halen := hpi.len.core_ok.arena_len_le
  have h1_4 : st.core.arena[cref.toNat + 3 + 1]'(by omega) = repl := by
    rw [List.getElem?_eq_getElem (by omega)] at har4; exact Option.some.inj har4
  have h1_ri : st.core.arena[cref.toNat + 3 + ri_n]'(by omega) = not_lit := by
    rw [List.getElem?_eq_getElem (by omega)] at har_ri; exact Option.some.inj har_ri
  have ⟨hnw', hperm'⟩ := full_swapLits_preserves_nw hpi.len.core_ok hpi.nw hcref (k1 := 1)
    (k2 := ri_n) (by omega) hri_lt
  have hst'_eq : st'.core =
      { st.core with
        arena := (st.core.arena.set (cref.toNat + 3 + 1)
          (st.core.arena[cref.toNat + 3 + ri_n]'(by omega))).set (cref.toNat + 3 + ri_n)
          (st.core.arena[cref.toNat + 3 + 1]'(by omega)) } := by
    simp only [st', h1_4, h1_ri, show cref.toNat + 3 + 1 = cref.toNat + 4 by omega]
  rw [← hst'_eq] at hnw' hperm'
  have hlen' : st'.LengthsOk c :=
    ⟨{ hpi.len.core_ok with arena_len_arr := by simp [st', haren] }, hpi.len.scratch_ok⟩
  exact
    { len := hlen', nw := hnw'
      sw := SplitWatchesInv.with_nonwatch (k' := st'.core) hpi.sw rfl rfl rfl rfl
        (fun _ r => hperm'.2.1 ▸ r)
      ag := hpi.ag.update (fun k => { k with arena := st'.core.arena })
      tr := fullTrailExt_congr hpi.tr rfl rfl rfl
      rsns_pres := fullTrailRsnsPres_congr hpi.rsns_pres rfl
      perm := fullArenaPermEq_trans hpi.perm hperm', sc_eq := hpi.sc_eq, not_f := hpi.not_f }

theorem m7_ovf_ok_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s_pi st2 : FullState} {not_lit w0 cref repl : BitVec 32}
    {off_v p_v q_v end_v wu' : BitVec 64} {wl' : Nat}
    {wv' ws' wso' : List (BitVec 32)}
    (hpi2 : PropLitInv c F0 F_cur s_pi st2 not_lit.toNat off_v.toNat q_v.toNat
      (p_v.toNat + 2) end_v.toNat)
    (hnot_lt : not_lit.toNat < 2 * st2.core.cur_vars)
    (hrepl_lt : repl.toNat < 2 * st2.core.cur_vars)
    (hrepl_ne : repl.toNat ≠ not_lit.toNat) (hflag : (w0 &&& 0x80000000#32) = 0#32)
    (hcr_lt : cref.toNat < 0x80000000) (hcref : cref.toNat ∈ fullArenaClauseRefsCore st2.core)
    (hlen3 : ({ st2 with
      core := { st2.core with wvec := wv', wstk := ws', wlen := wl', wusable := wu' }
      scratch := { st2.scratch with wsort := wso' } } : FullState).LengthsOk c)
    (hlay3 : WatchStackLayout { st2.core with
      wvec := wv', wstk := ws', wlen := wl', wusable := wu' })
    (hother : ∀ l < 2 * st2.core.cur_vars, l ≠ repl.toNat →
      fullWatchSizeCore { st2.core with wvec := wv', wstk := ws', wlen := wl', wusable := wu' } l =
        fullWatchSizeCore st2.core l ∧
      ∀ idx < fullWatchSizeCore st2.core l,
        ws'[fullWatchOffCore { st2.core with
            wvec := wv', wstk := ws', wlen := wl', wusable := wu' } l + idx]? =
          st2.core.wstk[fullWatchOffCore st2.core l + idx]?)
    (hlit_ok : fullWatchSizeCore { st2.core with
        wvec := wv', wstk := ws', wlen := wl', wusable := wu' } repl.toNat =
        fullWatchSizeCore st2.core repl.toNat + 2 ∧
      (∀ idx < fullWatchSizeCore st2.core repl.toNat,
        ws'[fullWatchOffCore { st2.core with
            wvec := wv', wstk := ws', wlen := wl', wusable := wu' } repl.toNat + idx]? =
          st2.core.wstk[fullWatchOffCore st2.core repl.toNat + idx]?) ∧
      ws'[fullWatchOffCore { st2.core with
          wvec := wv', wstk := ws', wlen := wl', wusable := wu' } repl.toNat +
            fullWatchSizeCore st2.core repl.toNat]? = some w0 ∧
      ws'[fullWatchOffCore { st2.core with
          wvec := wv', wstk := ws', wlen := wl', wusable := wu' } repl.toNat +
            fullWatchSizeCore st2.core repl.toNat + 1]? = some cref) :
    let st3 : FullState :=
      { st2 with
        core := { st2.core with wvec := wv', wstk := ws', wlen := wl', wusable := wu' }
        scratch := { st2.scratch with wsort := wso' } }
    let off3 := fullWatchOffCore st3.core not_lit.toNat
    PropLitInv c F0 F_cur s_pi st3 not_lit.toNat off3
      (off3 + (q_v.toNat - off_v.toNat)) (off3 + (p_v.toNat + 2 - off_v.toNat))
      (off3 + (end_v.toNat - off_v.toNat)) :=
  hpi2.push_nonskip (w0 := w0.toNat) (cref := cref.toNat)
    hnot_lt hrepl_lt hrepl_ne hlen3 hlay3 rfl rfl hother
    ⟨hlit_ok.1, hlit_ok.2.1,
      by simpa [bv32_ofNat_toNat_lt w0.isLt] using hlit_ok.2.2.1,
      by simpa [bv32_ofNat_toNat_lt cref.isLt] using hlit_ok.2.2.2⟩
    (by simpa [bv32_ofNat_toNat_lt w0.isLt] using hflag) hcr_lt hcref

theorem m7_swapCl_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st1 : FullState} {not_lit l0 l1 cref : BitVec 32} {off_v p_v q_v end_v : BitVec 64}
    (hpi : PropLitInv c F0 F_cur s st1 not_lit.toNat off_v.toNat q_v.toNat
      (p_v.toNat + 2) end_v.toNat)
    (hcref : cref.toNat ∈ fullArenaClauseRefsCore st1.core)
    (hng : fullArenaClauseGarbCore st1.core cref.toNat = false)
    (hfit : cref.toNat + 3 + fullArenaClauseSizeCore st1.core cref.toNat ≤ st1.core.arena_len)
    (har3 : st1.core.arena[cref.toNat + 3]? = some l0)
    (har4 : st1.core.arena[cref.toNat + 4]? = some l1) :
    let st2 : FullState := { st1 with core := { st1.core with
      arena := (st1.core.arena.set (cref.toNat + 3) l1).set (cref.toNat + 4) l0 } }
    PropLitInv c F0 F_cur s st2 not_lit.toNat off_v.toNat q_v.toNat
      (p_v.toNat + 2) end_v.toNat ∧
    cref.toNat ∈ fullArenaClauseRefsCore st2.core ∧
    fullArenaClauseGarbCore st2.core cref.toNat = false ∧
    fullArenaClauseSizeCore st2.core cref.toNat = fullArenaClauseSizeCore st1.core cref.toNat ∧
    st2.core.arena[cref.toNat + 3]? = some l1 ∧ st2.core.arena[cref.toNat + 4]? = some l0 := by
  intro st2
  have haren := hpi.len.core_ok.arena_len_arr; have halen := hpi.len.core_ok.arena_len_le
  have hsz3 : 3 ≤ fullArenaClauseSizeCore st1.core cref.toNat :=
    (hpi.nw.arena.refs_wf cref.toNat hcref).2.1
  have hl0_g : st1.core.arena[cref.toNat + 3]'(by omega) = l0 := by
    rw [List.getElem?_eq_getElem (by omega)] at har3; exact Option.some.inj har3
  have hl1_g : st1.core.arena[cref.toNat + 4]'(by omega) = l1 := by
    rw [List.getElem?_eq_getElem (by omega)] at har4; exact Option.some.inj har4
  have ⟨hnw2, hperm2⟩ := full_swapCl_preserves_nw hpi.len.core_ok hpi.nw hcref
  have hst2_eq : st2.core = { st1.core with
      arena := (st1.core.arena.set (cref.toNat + 3) (st1.core.arena[cref.toNat + 4]'(by
        have hwf := hpi.nw.arena.refs_wf cref.toNat hcref
        dsimp only [withEmptyWatchesCore] at hwf; omega))).set (cref.toNat + 4)
        (st1.core.arena[cref.toNat + 3]'(by
          have hwf := hpi.nw.arena.refs_wf cref.toNat hcref
          dsimp only [withEmptyWatchesCore] at hwf; omega)) } := by
    simp only [st2, hl0_g, hl1_g]
  rw [← hst2_eq] at hnw2 hperm2
  have hlen2 : st2.LengthsOk c :=
    ⟨{ hpi.len.core_ok with arena_len_arr := by simp [st2, haren] }, hpi.len.scratch_ok⟩
  refine ⟨{ len := hlen2, nw := hnw2
            sw := SplitWatchesInv.with_nonwatch (k' := st2.core) hpi.sw rfl rfl rfl rfl
              (fun _ r => hperm2.2.1 ▸ r)
            ag := hpi.ag.update (fun k => { k with arena := st2.core.arena })
            tr := fullTrailExt_congr hpi.tr rfl rfl rfl
            rsns_pres := fullTrailRsnsPres_congr hpi.rsns_pres rfl
            perm := fullArenaPermEq_trans hpi.perm hperm2, sc_eq := hpi.sc_eq,
            not_f := hpi.not_f },
    hperm2.2.1.symm ▸ hcref, (hperm2.2.2 cref.toNat hcref).2.1.trans hng,
    (hperm2.2.2 cref.toNat hcref).1,
    by simp [st2, List.getElem?_set_ne (by omega : cref.toNat + 4 ≠ cref.toNat + 3),
         List.getElem?_set_self (show cref.toNat + 3 < st1.core.arena.length by omega)],
    by rw [List.getElem?_set_self (by simp; omega)]⟩

theorem m7_compact_finish_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s_pi st : FullState} {not_lit : BitVec 32} {off_v q_v end_v : BitVec 64}
    (hpi : PropLitInv c F0 F_cur s_pi st not_lit.toNat off_v.toNat q_v.toNat
      end_v.toNat end_v.toNat)
    (hdense : s_pi.core.dense_mode = 0#64) (hwc : c.wcap < 2 * dimacsBound)
    (hnot_lt : not_lit.toNat < 2 * st.core.cur_vars)
    (_hq_bnd : q_v.toNat - off_v.toNat < 2 ^ 32) :
    let wvec' := st.core.wvec.set (2 * not_lit.toNat + 1)
      (BitVec.ofNat 32 (q_v.toNat - off_v.toNat))
    let st' : FullState := { st with core := { st.core with wvec := wvec' } }
    st'.LengthsOk c ∧ FullWitnessInv c F0 F_cur st'.core ∧
    FullTrailExt s_pi.core st'.core ∧ FullTrailRsnsPres s_pi.core st'.core ∧
    FullArenaPermEq s_pi.core st'.core ∧ AgreesExcept propLitCoreMask s_pi.core st'.core := by
  intro wvec' st'
  unfold dimacsBound at hwc
  have hcv := hpi.len.core_ok.cur_vars_le
  have hwv := hpi.len.core_ok.wvec_len
  have hdm' : st'.core.dense_mode = 0#64 := by
    have := hpi.ag.get (fun k => k.dense_mode) (fun _ => rfl); exact this.trans hdense
  have hlen' : st'.LengthsOk c :=
    ⟨{ hpi.len.core_ok with wvec_len := by simp [st', wvec', hwv] }, hpi.len.scratch_ok⟩
  have hwat' : WatchesInv F_cur st'.core :=
    SplitWatchesInv.finish_compact hpi.sw (by omega) hpi.len.core_ok hnot_lt
  have hnw' : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st'.core) :=
    fullWitnessInv_nw_congr hlen'.core_ok.cur_vars_le hpi.nw
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  refine ⟨hlen', fullWitnessInv_of_nw hnw' hdm' hwat',
    fullTrailExt_congr hpi.tr rfl rfl rfl,
    fullTrailRsnsPres_congr hpi.rsns_pres rfl,
    ?_, hpi.ag.update (fun k => { k with wvec := wvec' })⟩
  obtain ⟨hal, hrf, hcl⟩ := hpi.perm; exact ⟨hal, hrf, hcl⟩

theorem fid_repl_delay_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s_pi st1 st3 : FullState} {not_lit other cref repl : BitVec 32}
    {ri_n dlen : Nat} {off_v p_v q_v end_v : BitVec 64}
    (hpi : PropLitInv c F0 F_cur s_pi st1 not_lit.toNat off_v.toNat q_v.toNat
      (p_v.toNat + 2) end_v.toNat)
    (hs0_dl : dlen < c.delayed_cap)
    (hst3_len : st3.LengthsOk c)
    (hst3_nw : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st3.core))
    (hst3_sw : SplitWatchesInv F_cur st3.core not_lit.toNat off_v.toNat q_v.toNat
      (p_v.toNat + 2) end_v.toNat)
    (hst3_ag : AgreesExcept propLitCoreMask s_pi.core st3.core)
    (hst3_tr : FullTrailExt s_pi.core st3.core)
    (hst3_rsn : FullTrailRsnsPres s_pi.core st3.core)
    (hst3_perm : FullArenaPermEq s_pi.core st3.core)
    (hst3_sc : st3.scratch = { s_pi.scratch with
      search_ticks := st3.scratch.search_ticks, wsort := st3.scratch.wsort,
      phases := st3.scratch.phases })
    (hst3_notf : st3.core.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8)
    (hdel_ok : DelayedWatchesOk st1.core s_pi.scratch.delayed dlen not_lit.toNat)
    (hrepl_lt : repl.toNat < 2 * st3.core.cur_vars) (hrepl_ne : repl.toNat ≠ not_lit.toNat)
    (hcr_lt : cref.toNat < 0x80000000) (hcr_ref : cref.toNat ∈ fullArenaClauseRefsCore st3.core)
    {w0 : BitVec 32} (hw0_flag : (w0 &&& 0x80000000#32) = 0#32) :
    let del' := ((st3.scratch.delayed.set (3 * dlen) repl).set (3 * dlen + 1) w0).set
      (3 * dlen + 2) cref
    let s_pi' : FullState := { s_pi with scratch := { s_pi.scratch with delayed := del' } }
    let st4 : FullState := { st3 with scratch := { st3.scratch with delayed := del' } }
    PropLitInv c F0 F_cur s_pi' st4 not_lit.toNat off_v.toNat q_v.toNat
      (p_v.toNat + 2) end_v.toNat ∧
    DelayedWatchesOk st4.core st4.scratch.delayed (dlen + 1) not_lit.toNat := by
  intro del' s_pi' st4
  have _ := (other, ri_n)
  have hdl_len : st3.scratch.delayed.length = 3 * c.delayed_cap :=
    hst3_len.scratch_ok.delayed_len_arr
  have hpi3 : PropLitInv c F0 F_cur s_pi st3 not_lit.toNat off_v.toNat q_v.toNat
      (p_v.toNat + 2) end_v.toNat :=
    ⟨hst3_len, hst3_nw, hst3_sw, hst3_ag, hst3_tr, hst3_rsn, hst3_perm, hst3_sc, hst3_notf⟩
  have hdel3 : DelayedWatchesOk st3.core st3.scratch.delayed dlen not_lit.toNat := by
    have hdel_s := delayedWatchesOk_congr hdel_ok
      ((hst3_ag.get (fun k => k.cur_vars) (fun _ => rfl)).trans
        (hpi.ag.get (fun k => k.cur_vars) (fun _ => rfl)).symm)
      (fun r hr => by
        have hr0 : r ∈ fullArenaClauseRefsCore s_pi.core := hpi.perm.2.1 ▸ hr
        exact hst3_perm.2.1.symm ▸ hr0)
    have hds3 : st3.scratch.delayed = s_pi.scratch.delayed := by rw [hst3_sc]
    rwa [← hds3] at hdel_s
  have hdl_ok4 := delayedWatchesOk_push hdel3 (by rw [hdl_len]; omega) hrepl_lt hrepl_ne
    hw0_flag hcr_lt hcr_ref
  have hlen4 : st4.LengthsOk c :=
    ⟨hst3_len.core_ok,
      { hst3_len.scratch_ok with delayed_len_arr := by simp [st4, del', hdl_len] }⟩
  have hag4 : AgreesExcept propLitCoreMask s_pi'.core st4.core := hst3_ag
  have htr4 : FullTrailExt s_pi'.core st4.core := hst3_tr
  have hrsn4 : FullTrailRsnsPres s_pi'.core st4.core := hst3_rsn
  have hperm4 : FullArenaPermEq s_pi'.core st4.core := hst3_perm
  have hsc4 : st4.scratch = { s_pi'.scratch with
      search_ticks := st4.scratch.search_ticks, wsort := st4.scratch.wsort,
      phases := st4.scratch.phases } := by
    rw [show st3.scratch.delayed = s_pi.scratch.delayed by rw [hst3_sc]] at *
    have hsc3' := hst3_sc
    dsimp [st4, s_pi', del']; rw [hst3_sc]
  exact ⟨⟨hlen4, hst3_nw, hst3_sw, hag4, htr4, hrsn4, hperm4, hsc4, hst3_notf⟩, hdl_ok4⟩

theorem fastProp_nonchrono_alvl {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} {cref other not_lit nl_lvl : BitVec 32}
    (hnw : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k))
    (hcref : cref.toNat ∈ fullArenaClauseRefsCore k)
    (hng : fullArenaClauseGarbCore k cref.toNat = false)
    (hnot_f : k.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8)
    (hun : k.vals[other.toNat]?.getD 0#8 = 0#8)
    (hnot_mem : not_lit.toNat ∈ fullArenaClauseLitsCore k cref.toNat)
    (hunit : ∀ l ∈ fullArenaClauseLitsCore k cref.toNat,
      l = other.toNat ∨ k.vals[l]?.getD 0#8 = 0xFF#8)
    (hnl : k.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl)
    (hge_cl : ∀ l ∈ fullArenaClauseLitsCore k cref.toNat, l ≠ other.toNat →
      (k.lvl[l / 2]?.getD 0#32).toNat ≤ nl_lvl.toNat)
    (hlv_eq : nl_lvl.toNat = k.cur_level) :
    (∀ l ∈ fullArenaClauseLitsCore k cref.toNat, l ≠ other.toNat →
      (k.lvl[l / 2]?.getD 0#32).toNat ≤ nl_lvl.toNat) ∧
    (nl_lvl = 0#32 ∨ ∃ l ∈ fullArenaClauseLitsCore k cref.toNat,
      l ≠ other.toNat ∧ nl_lvl = k.lvl[l / 2]?.getD 0#32) :=
  m7_nonchrono_alvl_facts hnw hcref hng hnot_f hun hnot_mem hunit hnl hge_cl hlv_eq

end LeanQbe.T.Examples.Kissat.Proof.PropSearch
