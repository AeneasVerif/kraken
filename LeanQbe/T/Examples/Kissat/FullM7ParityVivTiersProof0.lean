/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM7ParityVivTiers
public import LeanQbe.T.Examples.Kissat.FullM6HdrProof0
public import LeanQbe.T.Examples.Kissat.FullM6OrchAdaptersProof0
public import LeanQbe.T.Examples.Kissat.FullM7BcpHotProof0
import LeanQbe.T.Examples.Kissat.FullM7BcpHotProof1a
import LeanQbe.T.Examples.Kissat.FullM7BcpHotProof1b
import LeanQbe.T.Examples.Kissat.FullM7BcpHotProof1c
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullVivTopLemmas1
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat `M7` Shared Vivification & Focused-Tier WP Proofs (`FullM7ParityVivTiersProof0`)

No blanket expose or local attributes, no unrestricted imports, no heartbeat/depth bumps,
plain `public section`, UNSAT-only contracts (`0` SAT proofs):
1. `m6_hdr_sync_legacy_tiers_wp` (`FullM6Hdr.m6HdrW2aSpec [] []`: focused `M6W_TIER2`)
2. `full_propagate_ignore_hot_wp` (`Full.FullPropDecSpecs.fullPropagateIgnoreSpec`: unconditional
   `search_ticks` recording with phase-saving `rec_ph` preserved)
3. `full_vivify_tier_m6_hdr_wp` (`FullM6OrchAdapters.m6aVivifyTierSpec`: `FullMem`-only
   `h->search_ticks < tick_lim` budget gate, zero synthetic `spent`)
4. `full_vivify_m6_hdr_wp` (`FullM6OrchAdapters.m6aVivifySpec`: `start` save/restore,
   `tier1 >= tier2` merge, saturating cumulative carry-over across tiers `1, 2, 3, 0`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7ParityVivTiers

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FastCore
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullAnalyzeHelpers
open LeanQbe.T.Examples.Kissat.Full.FullVivTopTactics
open LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Full.FullVivTopTactics
open scoped LeanQbe.T.Examples.Kissat.FullM6Hdr.M6HdrTactics
open Kraken.Bedrock2.Test

namespace Tactics

scoped macro "m7p_hsteps" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsteps))

scoped macro "m7p_hsteps_nogrp" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsteps_nogrp))

scoped macro "m7p_hsplit" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsplit))

end Tactics

open scoped LeanQbe.T.Examples.Kissat.FullM7ParityVivTiers.Tactics

/-! ## 1. `m6_hdr_sync_legacy_tiers` (`M6W_TIER2`) -/

private theorem w2a_pres_of_init {ext ext1 ext' : List (BitVec 64)}
    (h1 : FullM6Hdr.M6HdrExtInitOk ext → ext1 = ext) (h2 : FullM6Hdr.M6HdrExtInitOk ext')
    (h3 : FullM6Hdr.M6ExtW2bPres ext1 ext') :
    FullM6Hdr.M6HdrExtInitOk ext → FullM6Hdr.M6HdrExtInitOk ext' ∧
      FullM6Hdr.M6ExtW2bPres ext ext' :=
  fun hi => ⟨h2, (h1 hi) ▸ h3⟩

/-- `m6_hdr_sync_legacy_tiers` satisfies exact `FullM6Hdr.m6HdrW2aSpec [] []` while reading
focused `e[M6W_TIER2]` (`idx = 10`) instead of stable `e[M6W_TIER2 + 1ULL]`. -/
theorem m6_hdr_sync_legacy_tiers_wp (Γ : Env)
    (hEnsure : ∀ a m Q X, FullM6Hdr.m6ExtEnsureInitSpec a m Q X →
      Γ "m6_ext_ensure_init" [i64] [] a m Q X) :
    ∀ a m Q X, FullM6Hdr.m6HdrW2aSpec [] [] a m Q X →
      Func.wp Γ m6_hdr_sync_legacy_tiers_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  obtain ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩ := FullM6Hdr.m6HdrW2aSpec_elim hs
  unfold Func.wp m6_hdr_sync_legacy_tiers_body
  c0_hsteps_nogrp
  c0_call hEnsure
  refine FullM6Hdr.m6ExtEnsureInitSpec_of hcfg hext hlen hm fun ext1 m1 hinit1 hpres1 hm1 => ?_
  have hl1 : ext1.length = 288 := hinit1.toOk.len
  rw [FullM6Hdr.fullM6HdrMem_iff] at hm1
  c0_hsteps
  all_goals
    refine hQ () ext1 _ _ ?_ ?_ ?_ hinit1.toOk
      (w2a_pres_of_init hpres1 hinit1 (FullM6Hdr.M6ExtW2bPres.refl ext1))
      ((FullM6Hdr.fullM6HdrMem_iff ..).mpr (by assumption))
    · rfl
    · exact hlen.with_scratch
        { hlen.scratch_ok with walk_vals_len := hlen.scratch_ok.walk_vals_len }
    · exact FullM6Hdr.M6HdrScratchPres.of_tier _ _

/-! ## 2. `full_propagate_ignore_hot` (Unconditional `search_ticks`) -/

section PropHotSection

open LeanQbe.T.Examples.Kissat.FullM7BcpHot
open LeanQbe.T.Examples.Kissat.Full.FullPropDecSpecs hiding
  fullWatchPushSpec fullPropLitSpec fullPropagateIgnoreSpec fullPropagateSpec
  FullTrailExt FullArenaPermEq

private def m7pCoreMask (t : FullCoreState) : FullCoreState :=
  { t with
    vals := [], flags := [], lvl := [], rsns := [], trl := [], trail_pos := [],
    trail_end := 0, propagated := 0, unassigned := 0#64, unflushed := 0#64,
    wvec := [], arena := [], wstk := [], wlen := 0, wusable := 0#64, fuel := 0#64,
    confl_type := 0#64, confl_ref := 0#64, confl_lit0 := 0#64, confl_lit1 := 0#64,
    oom := 0#64 }

private theorem m7p_agrees_upd_prop_fuel {a b : FullCoreState} {p : Nat} {f : BitVec 64}
    (h : AgreesExcept m7pCoreMask a b) :
    AgreesExcept m7pCoreMask a { b with propagated := p, fuel := f } := by
  unfold AgreesExcept m7pCoreMask at h ⊢; exact h

private abbrev M7pHQ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (ignore_ref : BitVec 64) (R : Mem 64 → Prop) (Q : Post [i64]) : Prop :=
  ∀ (r : BitVec 64) (vals' : List (BitVec 8))
    (flags' lvl' rsns' trl' tp' : List (BitVec 32)) (te' prop' : Nat)
    (unas' unfl' : BitVec 64) (wvec' arena' wstk' : List (BitVec 32)) (wlen' : Nat)
    (wu' fuel' ctype' cref' c0' c1' oom' ticks' : BitVec 64)
    (wsort' : List (BitVec 32)) (phases' : List (BitVec 8)) (m' : Mem 64),
    have s' : FullState :=
      { core :=
          { s.core with
            vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
            trail_pos := tp', trail_end := te', propagated := prop', unassigned := unas',
            unflushed := unfl', wvec := wvec', arena := arena', wstk := wstk',
            wlen := wlen', wusable := wu', fuel := fuel', confl_type := ctype',
            confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
        scratch :=
          { s.scratch with
            search_ticks := ticks', wsort := wsort', phases := phases' } }
    s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
    FullPropDecSpecs.FullTrailExt s.core s'.core →
    FullPropDecSpecs.FullArenaPermEq s.core s'.core →
    fuel'.toNat ≤ s.core.fuel.toNat → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
    (r = 0#64 → prop' = te' ∧ ctype' = s.core.confl_type ∧
      (s.core.oom = 0#64 → oom' = 0#64) ∧
      (s.core.propagated < s.core.trail_end → fuel'.toNat < s.core.fuel.toNat)) →
    (r = 1#64 → fuel'.toNat < s.core.fuel.toNat ∧ oom' = 0#64 ∧
      FullPropDecSpecs.FullConflOkW F_cur s'.core ∧ (ctype' = 2#64 → cref' ≠ ignore_ref) ∧
      (s'.core.cur_level = 0 → F0.Unsat)) →
    (r = 2#64 → oom' ≠ 0#64 ∨ fuel' = 0#64) →
    (s.core.propagated = s.core.trail_end → r = 0#64 ∧ s' = s) →
    (FullMem c s' ⋆ R) m' → Q (r, ()) m'

private def M7pOuterInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s : FullState) (R : Mem 64 → Prop) (rem : Nat)
    (prop_v tend_v unass_v unfl_v _ticks_v : BitVec 64) (m : Mem 64) : Prop :=
  ∃ (sem : FullState) (te_mem : Nat),
    rem = sem.core.fuel.toNat ∧
    sem.LengthsOk c ∧
    FullWitnessInv c F0 F_cur sem.core ∧
    FullPropDecSpecs.FullTrailExt s.core sem.core ∧
    FullPropDecSpecs.FullArenaPermEq s.core sem.core ∧
    AgreesExcept m7pCoreMask s.core sem.core ∧
    sem.core.propagated = prop_v.toNat ∧
    sem.core.trail_end = tend_v.toNat ∧
    sem.core.unassigned = unass_v ∧
    sem.core.unflushed = unfl_v ∧
    sem.core.oom = 0#64 ∧
    sem.core.confl_type = s.core.confl_type ∧
    sem.core.dense_mode = 0#64 ∧
    sem.core.cur_vars = s.core.cur_vars ∧
    sem.core.cur_level = s.core.cur_level ∧
    sem.core.probing = s.core.probing ∧
    sem.core.arena_len = s.core.arena_len ∧
    sem.core.fuel.toNat ≤ s.core.fuel.toNat ∧
    (s.core.propagated < prop_v.toNat → sem.core.fuel.toNat < s.core.fuel.toNat) ∧
    s.core.propagated ≤ prop_v.toNat ∧
    te_mem ≤ sem.core.trail_end ∧
    s.core.propagated ≤ te_mem ∧
    sem.scratch = { s.scratch with
      search_ticks := sem.scratch.search_ticks, wsort := sem.scratch.wsort,
      phases := sem.scratch.phases } ∧
    (FullMem c
      (fastPropMem
        { s with
          core := { s.core with trail_end := te_mem } }
        { sem with
          core := { sem.core with propagated := s.core.propagated } }) ⋆ R) m

private theorem m7p_scratch_trans {s0 s1 s2 : FullState}
    (hbc : s1.scratch = { s0.scratch with
      search_ticks := s1.scratch.search_ticks, wsort := s1.scratch.wsort,
      phases := s1.scratch.phases })
    (hcb : s2.scratch = { s1.scratch with
      search_ticks := s2.scratch.search_ticks, wsort := s2.scratch.wsort,
      phases := s2.scratch.phases }) :
    s2.scratch = { s0.scratch with
      search_ticks := s2.scratch.search_ticks, wsort := s2.scratch.wsort,
      phases := s2.scratch.phases } := by
  rw [hcb, hbc]

private theorem m7p_core_eq_of_agrees (s sem : FullCoreState)
    (h : AgreesExcept m7pCoreMask s sem) :
    { s with
      unassigned := sem.unassigned, wlen := sem.wlen, wusable := sem.wusable,
      unflushed := sem.unflushed, trail_end := sem.trail_end, propagated := sem.propagated,
      fuel := sem.fuel, confl_ref := sem.confl_ref, confl_type := sem.confl_type,
      confl_lit0 := sem.confl_lit0, confl_lit1 := sem.confl_lit1, oom := sem.oom,
      vals := sem.vals, flags := sem.flags, lvl := sem.lvl, rsns := sem.rsns,
      trl := sem.trl, trail_pos := sem.trail_pos, wvec := sem.wvec,
      arena := sem.arena, wstk := sem.wstk } = sem := by
  cases s; cases sem
  unfold AgreesExcept m7pCoreMask at h
  simp only [FullCoreState.mk.injEq, true_and, and_true] at h
  rcases h with
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
     rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rfl

private theorem m7p_exit_hQ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s : FullState) (ignore_ref : BitVec 64) (R : Mem 64 → Prop) (Q : Post [i64])
    (hQ : M7pHQ c F0 F_cur s ignore_ref R Q)
    (r : BitVec 64) (st : FullState) (m' : Mem 64)
    (hag : AgreesExcept m7pCoreMask s.core st.core)
    (hscr : st.scratch = { s.scratch with
      search_ticks := st.scratch.search_ticks, wsort := st.scratch.wsort,
      phases := st.scratch.phases })
    (hlen : st.LengthsOk c) (hw : FullWitnessInv c F0 F_cur st.core)
    (htr : FullPropDecSpecs.FullTrailExt s.core st.core)
    (hperm : FullPropDecSpecs.FullArenaPermEq s.core st.core)
    (hfuel : st.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hr : r = 0#64 ∨ r = 1#64 ∨ r = 2#64)
    (hr0 : r = 0#64 → st.core.propagated = st.core.trail_end ∧
      st.core.confl_type = s.core.confl_type ∧ (s.core.oom = 0#64 → st.core.oom = 0#64) ∧
      (s.core.propagated < s.core.trail_end → st.core.fuel.toNat < s.core.fuel.toNat))
    (hr1 : r = 1#64 → st.core.fuel.toNat < s.core.fuel.toNat ∧ st.core.oom = 0#64 ∧
      FullPropDecSpecs.FullConflOkW F_cur st.core ∧
      (st.core.confl_type = 2#64 → st.core.confl_ref ≠ ignore_ref) ∧
      (st.core.cur_level = 0 → F0.Unsat))
    (hr2 : r = 2#64 → st.core.oom ≠ 0#64 ∨ st.core.fuel = 0#64)
    (hnoop : s.core.propagated = s.core.trail_end → r = 0#64 ∧ st = s)
    (hm : (FullMem c st ⋆ R) m') : Q (r, ()) m' := by
  have hst_eq :
      ({ core := { s.core with
          vals := st.core.vals, flags := st.core.flags, lvl := st.core.lvl,
          rsns := st.core.rsns, trl := st.core.trl, trail_pos := st.core.trail_pos,
          trail_end := st.core.trail_end, propagated := st.core.propagated,
          unassigned := st.core.unassigned, unflushed := st.core.unflushed,
          wvec := st.core.wvec, arena := st.core.arena, wstk := st.core.wstk,
          wlen := st.core.wlen, wusable := st.core.wusable, fuel := st.core.fuel,
          confl_type := st.core.confl_type, confl_ref := st.core.confl_ref,
          confl_lit0 := st.core.confl_lit0, confl_lit1 := st.core.confl_lit1,
          oom := st.core.oom }
         scratch := { s.scratch with
          search_ticks := st.scratch.search_ticks, wsort := st.scratch.wsort,
          phases := st.scratch.phases } } : FullState) = st := by
    cases st; dsimp only; congr 1
    · exact m7p_core_eq_of_agrees s.core _ hag
    · exact hscr.symm
  exact hQ r st.core.vals st.core.flags st.core.lvl st.core.rsns st.core.trl st.core.trail_pos
    st.core.trail_end st.core.propagated st.core.unassigned st.core.unflushed st.core.wvec
    st.core.arena st.core.wstk st.core.wlen st.core.wusable st.core.fuel st.core.confl_type
    st.core.confl_ref st.core.confl_lit0 st.core.confl_lit1 st.core.oom
    st.scratch.search_ticks st.scratch.wsort st.scratch.phases m'
    (hst_eq.symm ▸ hlen) (hst_eq.symm ▸ hw) (hst_eq.symm ▸ htr) (hst_eq.symm ▸ hperm)
    hfuel hr hr0 (hst_eq.symm ▸ hr1) hr2 (fun h => by simpa [hst_eq] using hnoop h)
    (hst_eq.symm ▸ hm)

private theorem m7p_outer_flush_ret {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sem : FullState} {ignore_ref prop_v tend_v unass_v unfl_v ticks' r : BitVec 64}
    {R : Mem 64 → Prop} {Q : Post [i64]} {m : Mem 64}
    (hQ : M7pHQ c F0 F_cur s ignore_ref R Q)
    (hlen_o : sem.LengthsOk c) (hw_o : FullWitnessInv c F0 F_cur sem.core)
    (htr_o : FullPropDecSpecs.FullTrailExt s.core sem.core)
    (hperm_o : FullPropDecSpecs.FullArenaPermEq s.core sem.core)
    (hag_o : AgreesExcept m7pCoreMask s.core sem.core)
    (hsc_o : sem.scratch = { s.scratch with
      search_ticks := sem.scratch.search_ticks, wsort := sem.scratch.wsort,
      phases := sem.scratch.phases })
    (hprop_eq : sem.core.propagated = prop_v.toNat)
    (htend_eq : sem.core.trail_end = tend_v.toNat)
    (hunass_eq : sem.core.unassigned = unass_v)
    (hunfl_eq : sem.core.unflushed = unfl_v)
    (hfuel_le : sem.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hpr_lt : s.core.propagated < s.core.trail_end)
    (hr : r = 0#64 ∨ r = 1#64 ∨ r = 2#64)
    (hr0 : r = 0#64 → prop_v.toNat = tend_v.toNat ∧ sem.core.confl_type = s.core.confl_type ∧
      (s.core.oom = 0#64 → sem.core.oom = 0#64) ∧
      (s.core.propagated < s.core.trail_end → sem.core.fuel.toNat < s.core.fuel.toNat))
    (hr1 : r ≠ 1#64)
    (hr2 : r = 2#64 → sem.core.oom ≠ 0#64 ∨ sem.core.fuel = 0#64)
    (hm : (FullMem c
      { sem with
        core :=
          { sem.core with
            propagated := prop_v.toNat, trail_end := tend_v.toNat
            unassigned := unass_v, unflushed := unfl_v }
        scratch := { sem.scratch with search_ticks := ticks' } } ⋆ R) m) :
    Q (r, ()) m := by
  let sem_fin : FullState :=
    { sem with
      core :=
        { sem.core with
          propagated := prop_v.toNat, trail_end := tend_v.toNat
          unassigned := unass_v, unflushed := unfl_v }
      scratch := { sem.scratch with search_ticks := ticks' } }
  have hfin_core :
      { sem.core with
        propagated := prop_v.toNat, trail_end := tend_v.toNat
        unassigned := unass_v, unflushed := unfl_v } = sem.core := by
    rw [← hprop_eq, ← htend_eq, ← hunass_eq, ← hunfl_eq]
  have hlen_fin : sem_fin.LengthsOk c :=
    ⟨by dsimp only [sem_fin]; rw [hfin_core]; exact hlen_o.core_ok,
     by dsimp only [sem_fin]; exact { hlen_o.scratch_ok with }⟩
  have hw_fin : FullWitnessInv c F0 F_cur sem_fin.core := by
    dsimp only [sem_fin]; rw [hfin_core]; exact hw_o
  have htr_fin : FullPropDecSpecs.FullTrailExt s.core sem_fin.core := by
    dsimp only [sem_fin]; rw [hfin_core]; exact htr_o
  have hperm_fin : FullPropDecSpecs.FullArenaPermEq s.core sem_fin.core := by
    dsimp only [sem_fin]; rw [hfin_core]; exact hperm_o
  have hag_fin : AgreesExcept m7pCoreMask s.core sem_fin.core := by
    dsimp only [sem_fin]; rw [hfin_core]; exact hag_o
  have hsc_fin : sem_fin.scratch = { s.scratch with
      search_ticks := sem_fin.scratch.search_ticks, wsort := sem_fin.scratch.wsort,
      phases := sem_fin.scratch.phases } := by
    dsimp only [sem_fin]; rw [hsc_o]
  exact m7p_exit_hQ c F0 F_cur s ignore_ref R Q hQ r sem_fin m
    hag_fin hsc_fin hlen_fin hw_fin htr_fin hperm_fin
    (by dsimp only [sem_fin]; exact hfuel_le) hr
    (fun h => by dsimp only [sem_fin]; exact hr0 h)
    (fun h => absurd h hr1)
    (fun h => by dsimp only [sem_fin]; exact hr2 h)
    (fun h => absurd h (Nat.ne_of_lt hpr_lt))
    hm

private def m7pPostOvfTicksExpr {Val : Ty → Type} {Cont : List Ty → Type}
    (h_p tk_b brk_c : Val i64) : Expr Val Cont [i64] :=
  .let_ (Op.mk (.add i64) (.var h_p, (.imm 600, ()))) fun p1 =>
  .load i64 (.var p1.1) fun ld =>
  .let_ (Op.mk (.add i64) (.var ld, (.var tk_b, ()))) fun p2 =>
  .let_ (Op.mk (.add i64) (.var h_p, (.imm 600, ()))) fun p3 =>
  .store (.var p2.1) (.var p3.1) (.ret (.var brk_c, ()))

private def m7pPostOvfBrkContExpr {Val : Ty → Type} {Cont : List Ty → Type}
    (J_out : Cont [i64, i64, i64, i64, i64])
    (h_p prop_v te_b un_b uf_b tk_b brk_c : Val i64) : Expr Val Cont [i64] :=
  .let_ (Op.mk (.cmp .ne i64) (.var brk_c, (.imm 0, ()))) fun c0 =>
  .jnz (.var c0.1)
    (.group (sig := [[]])
      (fun Js_brk => .cons (fun _ =>
        .let_ (Op.mk (.add i64) (.var prop_v, (.imm 1, ()))) fun p1 =>
        .let_ (Op.mk (.add i64) (.var h_p, (.imm 152, ()))) fun p2 =>
        .store (.var p1.1) (.var p2.1) (
          .let_ (Op.mk (.add i64) (.var h_p, (.imm 144, ()))) fun p3 =>
          .store (.var te_b) (.var p3.1) (
            .let_ (Op.mk (.add i64) (.var h_p, (.imm 792, ()))) fun p4 =>
            .store (.var un_b) (.var p4.1) (
              .let_ (Op.mk (.add i64) (.var h_p, (.imm 512, ()))) fun p5 =>
              .store (.var uf_b) (.var p5.1)
                (m7pPostOvfTicksExpr h_p tk_b brk_c))))) .nil)
      (fun Js_brk =>
        .let_ (Op.mk (.cmp .eq i64) (.var brk_c, (.imm 2, ()))) fun c2 =>
        .jnz (.var c2.1)
          (.let_ (Op.mk (.add i64) (.var h_p, (.imm 760, ()))) fun p6 =>
           .store (t := i64) (.imm 1) (.var p6.1) (.jump Js_brk.1 ()))
          (.jump Js_brk.1 ())))
    (.let_ (Op.mk (.add i64) (.var prop_v, (.imm 1, ()))) fun p7 =>
     .jump J_out (.var p7.1, (.var te_b, (.var un_b, (.var uf_b, (.var tk_b, ()))))))

private def m7pPostOvfBrkExpr {Val : Ty → Type} {Cont : List Ty → Type}
    (J_out : Cont [i64, i64, i64, i64, i64])
    (h_p prop_v te_b un_b uf_b tk_b brk_b t0_v : Val i64) : Expr Val Cont [i64] :=
  .group (sig := [[i64]])
    (fun Jch => .cons (fun brk_c =>
      m7pPostOvfBrkContExpr J_out h_p prop_v te_b un_b uf_b tk_b brk_c.1) .nil)
    (fun Jch =>
      .let_ (Op.mk (.cmp .ne i64) (.var brk_b, (.imm 2, ()))) fun c1 =>
      .jnz (.var c1.1)
        (.let_ (Op.mk (.cmp .ult i64) (.var t0_v, (.var te_b, ()))) fun c2 =>
         .jnz (.var c2.1)
           (.let_ (Op.mk (.add i64) (.var h_p, (.imm 144, ()))) fun p1 =>
            .store (.var te_b) (.var p1.1)
              (.group (sig := [[i64]])
                (fun Js_1 => .cons (fun r => .jump Jch.1 (.var r.1, ())) .nil)
                (fun Js_1 =>
                  @Expr.call _ _ [i64] "full_prop_chrono_hot" [i64, i64] [.bool]
                    (.var h_p, (.var t0_v, ())) fun ok =>
                  .jnz (.var ok.1)
                    (.jump Js_1.1 (.var brk_b, ()))
                    (.jump Js_1.1 (.imm 2, ())))))
           (.jump Jch.1 (.var brk_b, ())))
        (.jump Jch.1 (.var brk_b, ())))

private def m7pCompactAndPostOvfExpr {Val : Ty → Type} {Cont : List Ty → Type}
    (J_out : Cont [i64, i64, i64, i64, i64])
    (h_p pWstk prop_v te_b un_b uf_b tk_b off_b p_b q_b end_b brk_b t0_v : Val i64)
    (not_lit : Val i32) : Expr Val Cont [i64] :=
  .group (sig := [[i64, i64]])
    (fun Jc => .cons (fun pc_qc =>
      .let_ (Op.mk (.cmp .ult i64) (.var pc_qc.1, (.var end_b, ()))) fun c_lt =>
      .jnz (.var c_lt.1)
        (.let_ (Op.mk (.mul i64) (.var pc_qc.2.1, (.imm 4, ()))) fun oq =>
         .let_ (Op.mk (.add i64) (.var pWstk, (.var oq.1, ()))) fun pq =>
         .let_ (Op.mk (.mul i64) (.var pc_qc.1, (.imm 4, ()))) fun op =>
         .let_ (Op.mk (.add i64) (.var pWstk, (.var op.1, ()))) fun pp =>
         .load i32 (.var pp.1) fun ld =>
         .store (.var ld) (.var pq.1) (
           .let_ (Op.mk (.add i64) (.var pc_qc.2.1, (.imm 1, ()))) fun qc1 =>
           .let_ (Op.mk (.add i64) (.var pc_qc.1, (.imm 1, ()))) fun pc1 =>
           .jump Jc.1 (.var pc1.1, (.var qc1.1, ()))))
        (.let_ (Op.mk (.add i64) (.var h_p, (.imm 104, ()))) fun pwv =>
         .load i64 (.var pwv.1) fun ld_wv =>
         .let_ (Op.mk (.zext 32 64) (.var not_lit, ())) fun nl64 =>
         .let_ (Op.mk (.sext 32 64) (.imm 1, ())) fun sh1 =>
         .let_ (Op.mk (.shl i64) (.var nl64.1, (.var sh1.1, ()))) fun shl =>
         .let_ (Op.mk (.add i64) (.var shl.1, (.imm 1, ()))) fun idx1 =>
         .let_ (Op.mk (.mul i64) (.var idx1.1, (.imm 4, ()))) fun off1 =>
         .let_ (Op.mk (.add i64) (.var ld_wv, (.var off1.1, ()))) fun ptr1 =>
         .let_ (Op.mk (.sub i64) (.var pc_qc.2.1, (.var off_b, ()))) fun dif =>
         .let_ (Op.mk (.trunc 64 32) (.var dif.1, ())) fun sz32 =>
         .store (.var sz32.1) (.var ptr1.1)
           (.group (sig := [[]])
             (fun Jfn => .cons (fun _ =>
               m7pPostOvfBrkExpr J_out h_p prop_v te_b un_b uf_b tk_b brk_b t0_v) .nil)
             (fun Jfn =>
               .let_ (Op.mk (.cmp .ult i64) (.var pc_qc.2.1, (.var end_b, ()))) fun ck =>
               .jnz (.var ck.1)
                 (.let_ (Op.mk (.add i64) (.var h_p, (.imm 464, ()))) fun pwu =>
                  .load i64 (.var pwu.1) fun wu =>
                  .let_ (Op.mk (.sub i64) (.var end_b, (.var pc_qc.2.1, ()))) fun df =>
                  .let_ (Op.mk (.add i64) (.var wu, (.var df.1, ()))) fun wu1 =>
                  .let_ (Op.mk (.add i64) (.var h_p, (.imm 464, ()))) fun pwu2 =>
                  .store (.var wu1.1) (.var pwu2.1)
                    (.group (sig := [[i64]])
                      (fun Jk => .cons (fun k =>
                        .let_ (Op.mk (.cmp .ult i64) (.var k.1, (.var end_b, ()))) fun c_k =>
                        .jnz (.var c_k.1)
                          (.let_ (Op.mk (.mul i64) (.var k.1, (.imm 4, ()))) fun ok =>
                           .let_ (Op.mk (.add i64) (.var pWstk, (.var ok.1, ()))) fun pk =>
                           .store (t := i32) (.imm 0xFFFFFFFF) (.var pk.1) (
                             .let_ (Op.mk (.add i64) (.var k.1, (.imm 1, ()))) fun k1 =>
                             .jump Jk.1 (.var k1.1, ())))
                          (.jump Jfn.1 ())) .nil)
                      (fun Jk => .jump Jk.1 (.var pc_qc.2.1, ()))))
                 (.jump Jfn.1 ()))))) .nil)
    (fun Jc => .jump Jc.1 (.var p_b, (.var q_b, ())))

private theorem m7p_post_ovf_exit_brk2 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s st_c : FullState}
    {ignore_ref te_b un_b uf_b prop_v ticks_fin : BitVec 64}
    {R : Mem 64 → Prop} {Q : Post [i64]} {m : Mem 64}
    (hQ : M7pHQ c F0 F_cur s ignore_ref R Q)
    (hlen_c : st_c.LengthsOk c) (hwf_c : FullWitnessInv c F0 F_cur st_c.core)
    (htr_s_c : FullPropDecSpecs.FullTrailExt s.core st_c.core)
    (hperm_s_c : FullPropDecSpecs.FullArenaPermEq s.core st_c.core)
    (hag_sc : AgreesExcept m7pCoreMask s.core st_c.core)
    (hdm_c : st_c.core.dense_mode = 0#64)
    (hfuel_c : st_c.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hsc_c : st_c.scratch = { s.scratch with
      search_ticks := st_c.scratch.search_ticks,
      wsort := st_c.scratch.wsort, phases := st_c.scratch.phases })
    (hte_c_eq : te_b.toNat = st_c.core.trail_end)
    (hpr_lt : s.core.propagated < s.core.trail_end)
    (hpr_lt_teb : prop_v.toNat + 1 ≤ te_b.toNat)
    (hm : (FullMem c { st_c with
      core := { st_c.core with
        oom := 1#64, propagated := prop_v.toNat + 1,
        trail_end := te_b.toNat, unassigned := un_b, unflushed := uf_b }
      scratch := { st_c.scratch with search_ticks := ticks_fin } } ⋆ R) m) :
    Q (2#64, ()) m := by
  let st_fin2 : FullState :=
    { st_c with
      core :=
        { st_c.core with
          oom := 1#64, propagated := prop_v.toNat + 1
          trail_end := te_b.toNat, unassigned := un_b, unflushed := uf_b }
      scratch := { st_c.scratch with search_ticks := ticks_fin } }
  have hlen_f2 : st_fin2.LengthsOk c :=
    ⟨{ hlen_c.core_ok with
        trail_end_le := by dsimp only [st_fin2]; rw [hte_c_eq]; exact hlen_c.core_ok.trail_end_le
        propagated_le := hpr_lt_teb },
     { hlen_c.scratch_ok with }⟩
  have hwf_f2 : FullWitnessInv c F0 F_cur st_fin2.core := by
    have hnw := fullWitnessInv_nw_congr hlen_f2.core_ok.cur_vars_le
      (fullWitnessInv_to_nw hlen_c.core_ok.cur_vars_le hwf_c)
      rfl rfl rfl rfl hte_c_eq rfl rfl rfl rfl rfl rfl rfl rfl
    have hwat_f2 : WatchesInv F_cur st_fin2.core := by
      have hw_sp : ModeWatchesInv F_cur st_fin2.core :=
        hwf_c.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr)
      simpa only [ModeWatchesInv, st_fin2, hdm_c, ↓reduceIte] using hw_sp
    exact fullWitnessInv_of_nw hnw hdm_c hwat_f2
  exact m7p_exit_hQ c F0 F_cur s ignore_ref R Q hQ 2#64 st_fin2 m
    (hag_sc.update (fun k =>
      { k with
        oom := 1#64, propagated := prop_v.toNat + 1
        trail_end := te_b.toNat, unassigned := un_b, unflushed := uf_b }))
    (by dsimp only [st_fin2]; rw [hsc_c])
    hlen_f2 hwf_f2
    ⟨by simpa [st_fin2, hte_c_eq] using htr_s_c.te_ge,
     by simpa [st_fin2, hte_c_eq] using htr_s_c.trl_pref,
     by simpa [st_fin2, hte_c_eq] using htr_s_c.lvl_pres⟩
    (m7_arenaPermEq_congr rfl rfl rfl rfl hperm_s_c)
    (by simp [st_fin2, hfuel_c])
    (Or.inr (Or.inr rfl))
    (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
    (fun _ => Or.inl (by simp [st_fin2]))
    (fun h => absurd h (Nat.ne_of_lt hpr_lt))
    hm

private theorem m7p_post_ovf_exit_brk1 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s st_c : FullState}
    {ignore_ref te_b un_b uf_b prop_v ticks_fin : BitVec 64}
    {R : Mem 64 → Prop} {Q : Post [i64]} {m : Mem 64}
    (hQ : M7pHQ c F0 F_cur s ignore_ref R Q)
    (hlen_c : st_c.LengthsOk c) (hwf_c : FullWitnessInv c F0 F_cur st_c.core)
    (htr_s_c : FullPropDecSpecs.FullTrailExt s.core st_c.core)
    (hperm_s_c : FullPropDecSpecs.FullArenaPermEq s.core st_c.core)
    (hag_sc : AgreesExcept m7pCoreMask s.core st_c.core)
    (hdm_c : st_c.core.dense_mode = 0#64)
    (hfuel_lt : st_c.core.fuel.toNat < s.core.fuel.toNat)
    (hoom_c : st_c.core.oom = 0#64)
    (hconfl_w : FullPropDecSpecs.FullConflOkW F_cur st_c.core)
    (hc2_ign : st_c.core.confl_type = 2#64 → st_c.core.confl_ref ≠ ignore_ref)
    (hsc_c : st_c.scratch = { s.scratch with
      search_ticks := st_c.scratch.search_ticks,
      wsort := st_c.scratch.wsort, phases := st_c.scratch.phases })
    (hte_c_eq : te_b.toNat = st_c.core.trail_end)
    (hpr_lt : s.core.propagated < s.core.trail_end)
    (hpr_lt_teb : prop_v.toNat + 1 ≤ te_b.toNat)
    (hm : (FullMem c { st_c with
      core := { st_c.core with
        propagated := prop_v.toNat + 1, trail_end := te_b.toNat,
        unassigned := un_b, unflushed := uf_b }
      scratch := { st_c.scratch with search_ticks := ticks_fin } } ⋆ R) m) :
    Q (1#64, ()) m := by
  let st_fin1 : FullState :=
    { st_c with
      core :=
        { st_c.core with
          propagated := prop_v.toNat + 1, trail_end := te_b.toNat
          unassigned := un_b, unflushed := uf_b }
      scratch := { st_c.scratch with search_ticks := ticks_fin } }
  have hlen_f1 : st_fin1.LengthsOk c :=
    ⟨{ hlen_c.core_ok with
        trail_end_le := by dsimp only [st_fin1]; rw [hte_c_eq]; exact hlen_c.core_ok.trail_end_le
        propagated_le := hpr_lt_teb },
     { hlen_c.scratch_ok with }⟩
  have hwf_f1 : FullWitnessInv c F0 F_cur st_fin1.core := by
    have hnw := fullWitnessInv_nw_congr hlen_f1.core_ok.cur_vars_le
      (fullWitnessInv_to_nw hlen_c.core_ok.cur_vars_le hwf_c)
      rfl rfl rfl rfl hte_c_eq rfl rfl rfl rfl rfl rfl rfl rfl
    have hwat_f1 : WatchesInv F_cur st_fin1.core := by
      have hw_sp : ModeWatchesInv F_cur st_fin1.core :=
        hwf_c.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr)
      simpa only [ModeWatchesInv, st_fin1, hdm_c, ↓reduceIte] using hw_sp
    exact fullWitnessInv_of_nw hnw hdm_c hwat_f1
  have hconfl_f1 : FullPropDecSpecs.FullConflOkW F_cur st_fin1.core :=
    m7_fullConflOkW_of_perm
      (m7_arenaPermEq_congr rfl rfl rfl rfl (.refl st_c.core))
      rfl rfl rfl rfl rfl rfl hconfl_w
  exact m7p_exit_hQ c F0 F_cur s ignore_ref R Q hQ 1#64 st_fin1 m
    (hag_sc.update (fun k =>
      { k with
        propagated := prop_v.toNat + 1, trail_end := te_b.toNat
        unassigned := un_b, unflushed := uf_b }))
    (by dsimp only [st_fin1]; rw [hsc_c])
    hlen_f1 hwf_f1
    ⟨by simpa [st_fin1, hte_c_eq] using htr_s_c.te_ge,
     by simpa [st_fin1, hte_c_eq] using htr_s_c.trl_pref,
     by simpa [st_fin1, hte_c_eq] using htr_s_c.lvl_pres⟩
    (m7_arenaPermEq_congr rfl rfl rfl rfl hperm_s_c)
    (by simp [st_fin1]; exact Nat.le_of_lt hfuel_lt)
    (Or.inr (Or.inl rfl))
    (fun h => absurd h (by decide))
    (fun _ => ⟨by simp [st_fin1, hfuel_lt], by simp [st_fin1, hoom_c], hconfl_f1,
      fun h2 => by simpa [st_fin1] using hc2_ign h2,
      fun h0 => FullWitnessInv.level0_unsat_of_conflOkW hwf_f1 h0 hconfl_f1⟩)
    (fun h => absurd h (by decide))
    (fun h => absurd h (Nat.ne_of_lt hpr_lt))
    hm

private theorem m7p_post_ovf_brk_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s sem s_base s_disk sem_b st_fin : FullState}
    {ignore_ref prop_v te_b un_b uf_b tk_b brk_b t0_v : BitVec 64}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {mf : Mem 64}
    {J_out : Cont [i64, i64, i64, i64, i64]}
    (hChrono : ∀ args m Q X, fullPropChronoHotSpec args m Q X →
      Γ "full_prop_chrono_hot" [i64, i64] [.bool] args m Q X)
    (hQ : M7pHQ c F0 F_cur s ignore_ref R Q)
    (hJ_out : ∀ (sem_next : FullState) (te_mc : Nat) (mc0 : Mem 64),
      sem_next.LengthsOk c →
      FullWitnessInv c F0 F_cur sem_next.core →
      FullPropDecSpecs.FullTrailExt s.core sem_next.core →
      FullPropDecSpecs.FullArenaPermEq s.core sem_next.core →
      AgreesExcept m7pCoreMask s.core sem_next.core →
      sem_next.core.propagated = (prop_v + 1#64).toNat →
      sem_next.core.trail_end = te_b.toNat →
      sem_next.core.unassigned = un_b →
      sem_next.core.unflushed = uf_b →
      sem_next.core.oom = 0#64 →
      sem_next.core.confl_type = s.core.confl_type →
      sem_next.core.dense_mode = 0#64 →
      sem_next.core.cur_vars = s.core.cur_vars →
      sem_next.core.cur_level = s.core.cur_level →
      sem_next.core.probing = s.core.probing →
      sem_next.core.arena_len = s.core.arena_len →
      sem_next.core.fuel.toNat < sem.core.fuel.toNat →
      sem_next.core.fuel.toNat < s.core.fuel.toNat →
      sem_next.core.fuel.toNat ≤ s.core.fuel.toNat →
      s.core.propagated ≤ sem_next.core.propagated →
      te_mc ≤ sem_next.core.trail_end →
      s.core.propagated ≤ te_mc →
      sem_next.scratch = { s.scratch with
        search_ticks := sem_next.scratch.search_ticks,
        wsort := sem_next.scratch.wsort, phases := sem_next.scratch.phases } →
      (FullMem c (fastPropMem { s with core := { s.core with trail_end := te_mc } }
        { sem_next with core := { sem_next.core with propagated := s.core.propagated } }) ⋆ R) mc0 →
      wp Γ Q X (Expr.jump J_out (.var (prop_v + 1#64), (.var te_b, (.var un_b, (.var uf_b,
        (.var tk_b, ())))))) mc0)
    (hlen0 : s.LengthsOk c) (hpr_lt : s.core.propagated < s.core.trail_end)
    (hs_base : s_base = { sem with core := { sem.core with
      propagated := s.core.propagated, fuel := sem.core.fuel - 1#64 } })
    (hs_disk : ∃ te_mem, s_disk = { s with core := { s.core with trail_end := te_mem } } ∧
      te_mem ≤ sem.core.trail_end ∧ s.core.propagated ≤ te_mem)
    (htr_o : FullPropDecSpecs.FullTrailExt s.core sem.core)
    (hperm_o : FullPropDecSpecs.FullArenaPermEq s.core sem.core)
    (hag_o : AgreesExcept m7pCoreMask s.core sem.core)
    (hcv_o : sem.core.cur_vars = s.core.cur_vars)
    (hcl_o : sem.core.cur_level = s.core.cur_level)
    (hprob_o : sem.core.probing = s.core.probing)
    (halen_o : sem.core.arena_len = s.core.arena_len)
    (hsc_o : sem.scratch = { s.scratch with
      search_ticks := sem.scratch.search_ticks, wsort := sem.scratch.wsort,
      phases := sem.scratch.phases })
    (hfl_rem_dec : (sem.core.fuel - 1#64).toNat < sem.core.fuel.toNat)
    (hfuel_le : sem.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hp1_prop : (prop_v + 1#64).toNat = prop_v.toNat + 1)
    (hp_lt_o : prop_v.toNat < sem.core.trail_end)
    (hpr_ge : s.core.propagated ≤ prop_v.toNat)
    (_hpi_b_len : sem_b.LengthsOk c)
    (hpi_b_cv : sem_b.core.cur_vars = s_base.core.cur_vars)
    (hpi_b_tr : FullPropDecSpecs.FullTrailExt s_base.core sem_b.core)
    (hpi_b_sc : sem_b.scratch = { s_base.scratch with
      search_ticks := sem_b.scratch.search_ticks,
      wsort := sem_b.scratch.wsort, phases := sem_b.scratch.phases })
    (hdense_b : s_base.core.dense_mode = 0#64)
    (hte_b : te_b.toNat = sem_b.core.trail_end)
    (hun_b : un_b = sem_b.core.unassigned) (huf_b : uf_b = sem_b.core.unflushed)
    (hbr0 : brk_b = 0#64 → sem_b.core.oom = 0#64 ∧ sem_b.core.confl_type = s.core.confl_type)
    (hbr1 : brk_b = 1#64 → PropLitConfl F_cur ignore_ref sem_b.core ∧ sem_b.core.oom = 0#64)
    (hbr_cases : brk_b = 0#64 ∨ brk_b = 1#64 ∨ brk_b = 2#64)
    (hlen_f : st_fin.LengthsOk c) (hwf_f : FullWitnessInv c F0 F_cur st_fin.core)
    (hag_f : AgreesExcept propLitCoreMask s_base.core st_fin.core)
    (htr_f : FullPropDecSpecs.FullTrailExt s_base.core st_fin.core)
    (hperm_f : FullPropDecSpecs.FullArenaPermEq s_base.core st_fin.core)
    (hoom_f : st_fin.core.oom = sem_b.core.oom)
    (hct_f : st_fin.core.confl_type = sem_b.core.confl_type)
    (hcr_f : st_fin.core.confl_ref = sem_b.core.confl_ref)
    (hc0_f : st_fin.core.confl_lit0 = sem_b.core.confl_lit0)
    (hc1_f : st_fin.core.confl_lit1 = sem_b.core.confl_lit1)
    (hcv_f : st_fin.core.cur_vars = sem_b.core.cur_vars)
    (hvals_f : st_fin.core.vals = sem_b.core.vals)
    (hte_f : st_fin.core.trail_end = sem_b.core.trail_end)
    (hun_f : st_fin.core.unassigned = sem_b.core.unassigned)
    (huf_f : st_fin.core.unflushed = sem_b.core.unflushed)
    (halen_f : st_fin.core.arena_len = sem_b.core.arena_len)
    (hcl_f : st_fin.core.cur_level = sem_b.core.cur_level)
    (har_f : st_fin.core.arena = sem_b.core.arena)
    (hscr_f : st_fin.scratch = sem_b.scratch)
    (hmf : (FullMem c (fastPropMem s_disk st_fin) ⋆ R) mf) :
    wp Γ Q X (m7pPostOvfBrkExpr J_out c.hdr prop_v te_b un_b uf_b tk_b brk_b t0_v) mf := by
  obtain ⟨te_mem, rfl, htem_le, hpr_tem⟩ := hs_disk
  have hte_sem_le : sem.core.trail_end ≤ sem_b.core.trail_end := by
    have := hpi_b_tr.te_ge; rw [hs_base] at this; exact this
  have hpr_lt_teb : prop_v.toNat + 1 ≤ te_b.toNat := by
    rw [hte_b]; exact Nat.le_trans hp_lt_o hte_sem_le
  unfold m7pPostOvfBrkExpr m7pPostOvfBrkContExpr m7pPostOvfTicksExpr
  refine wp_join_group (fun (brk_c, ()) mc0 =>
      ∃ st_c : FullState,
        st_c.LengthsOk c ∧
        FullWitnessInv c F0 F_cur st_c.core ∧
        FullPropDecSpecs.FullTrailExt s_base.core st_c.core ∧
        FullPropDecSpecs.FullArenaPermEq s_base.core st_c.core ∧
        AgreesExcept m7pCoreMask s.core st_c.core ∧
        st_c.core.cur_vars = sem_b.core.cur_vars ∧
        st_c.core.vals = sem_b.core.vals ∧
        st_c.core.trail_end = sem_b.core.trail_end ∧
        st_c.core.unassigned = sem_b.core.unassigned ∧
        st_c.core.unflushed = sem_b.core.unflushed ∧
        st_c.core.arena_len = sem_b.core.arena_len ∧
        st_c.core.cur_level = sem_b.core.cur_level ∧
        st_c.core.confl_ref = st_fin.core.confl_ref ∧
        st_c.core.confl_lit0 = st_fin.core.confl_lit0 ∧
        st_c.core.confl_lit1 = st_fin.core.confl_lit1 ∧
        (brk_c = 0#64 → st_c.core.oom = 0#64 ∧ st_c.core.confl_type = s.core.confl_type) ∧
        (brk_c = 1#64 → PropLitConfl F_cur ignore_ref st_c.core ∧ st_c.core.oom = 0#64) ∧
        (brk_c = 2#64 → True) ∧
        (brk_c = 0#64 ∨ brk_c = 1#64 ∨ brk_c = 2#64) ∧
        st_c.core.propagated = s.core.propagated ∧
        st_c.core.fuel = s_base.core.fuel ∧
        st_c.core.probing = s.core.probing ∧
        st_c.core.dense_mode = 0#64 ∧
        st_c.scratch = { s.scratch with
          search_ticks := st_c.scratch.search_ticks,
          wsort := st_c.scratch.wsort, phases := st_c.scratch.phases } ∧
        ∃ te_mc : Nat,
          te_mc ≤ st_c.core.trail_end ∧ s.core.propagated ≤ te_mc ∧
          (FullMem c (fastPropMem { s with core := { s.core with trail_end := te_mc } } st_c) ⋆
            R) mc0) ?_ ?_
  · rintro _ ⟨brk_c, ⟨⟩⟩ mc0 ⟨st_c, hlen_c, hwf_c, htr_c, hperm_c, hag_sc, hcv_c,
        hvals_c, hte_c, hun_c, huf_c, halen_c, hcl_c, _hcr_c, _hc0_c, _hc1_c,
        hc_br0, hc_br1, _hc_br2, hc_cases, hpr_c, hfuel_c, hprob_c, hdm_c,
        hsc_c, te_mc, htemc_le, hpr_temc, hmc0⟩
    let s_dmc : FullState := { s with core := { s.core with trail_end := te_mc } }
    have hsdmc_len : s_dmc.LengthsOk c :=
      ⟨{ hlen0.core_ok with
          trail_end_le := by
            dsimp only [s_dmc]
            rw [← hcv_o, show sem.core.cur_vars = st_c.core.cur_vars from by
              rw [hcv_c, hpi_b_cv, hs_base]]
            exact Nat.le_trans htemc_le hlen_c.core_ok.trail_end_le
          propagated_le := hpr_temc },
       hlen0.scratch_ok⟩
    have hmem_c_len' := fastPropMem_lengthsOk hsdmc_len hlen_c
      (by simpa [s_dmc, hcv_c, hpi_b_cv, hs_base] using hcv_o)
      (by simp [s_dmc, hpr_c]) rfl
    have hte_c_eq : te_b.toNat = st_c.core.trail_end := hte_b.trans hte_c.symm
    have hun_c_eq : un_b = st_c.core.unassigned := hun_b.trans hun_c.symm
    have huf_c_eq : uf_b = st_c.core.unflushed := huf_b.trans huf_c.symm
    have htr_c' : FullPropDecSpecs.FullTrailExt sem.core st_c.core := by
      rw [hs_base] at htr_c; exact ⟨htr_c.te_ge, htr_c.trl_pref, htr_c.lvl_pres⟩
    have htr_s_c : FullPropDecSpecs.FullTrailExt s.core st_c.core := htr_o.trans htr_c'
    have hperm_c' : FullPropDecSpecs.FullArenaPermEq sem.core st_c.core := by
      rw [hs_base] at hperm_c; exact hperm_c
    have hperm_s_c : FullPropDecSpecs.FullArenaPermEq s.core st_c.core := hperm_o.trans hperm_c'
    have hfuel_nx_dec : st_c.core.fuel.toNat < s.core.fuel.toNat := by
      rw [hfuel_c, hs_base]
      exact Nat.lt_of_lt_of_le hfl_rem_dec hfuel_le
    m7p_hsplit
    · have hbrk_ne0 : brk_c ≠ 0#64 := hc
      clear hc
      refine wp_unroll_group fun Js_brk hJs_brk => ?_
      m7p_hsplit
      · subst hc
        m7p_hsteps
        exact m7p_post_ovf_exit_brk2 hQ hlen_c hwf_c htr_s_c hperm_s_c hag_sc hdm_c
          (Nat.le_of_lt hfuel_nx_dec) hsc_c hte_c_eq hpr_lt hpr_lt_teb
          (by simpa only [fastPropMem, s_dmc, hp1_prop, hte_c_eq, hun_c_eq, huf_c_eq,
            BitVec.ofNat_eq_ofNat] using hm)
      · have hbrk1 : brk_c = 1#64 := by
          rcases hc_cases with rfl | rfl | rfl
          · exact absurd rfl hbrk_ne0
          · rfl
          · exact absurd rfl hc
        subst hbrk1
        have ⟨hconfl_c, hoom_c⟩ := hc_br1 rfl
        have hconfl_w : FullPropDecSpecs.FullConflOkW F_cur st_c.core := by
          rcases hconfl_c with hne0 | hok
          · exact absurd hoom_c hne0
          · exact hok.1
        have hc2_ign : st_c.core.confl_type = 2#64 → st_c.core.confl_ref ≠ ignore_ref := by
          rcases hconfl_c with hne0 | hok
          · exact absurd hoom_c hne0
          · exact hok.2
        m7p_hsteps
        exact m7p_post_ovf_exit_brk1 hQ hlen_c hwf_c htr_s_c hperm_s_c hag_sc hdm_c
          hfuel_nx_dec hoom_c hconfl_w hc2_ign hsc_c hte_c_eq hpr_lt hpr_lt_teb
          (by simpa only [fastPropMem, s_dmc, hp1_prop, hte_c_eq, hun_c_eq, huf_c_eq,
            BitVec.ofNat_eq_ofNat] using hm)
    · have ⟨hoom_c0, hct_c0⟩ := hc_br0 hc
      m7p_hsteps
      let sem_next : FullState :=
        { st_c with core := { st_c.core with propagated := prop_v.toNat + 1 } }
      have hlen_next : sem_next.LengthsOk c :=
        ⟨{ hlen_c.core_ok with propagated_le := by rw [← hte_c_eq]; exact hpr_lt_teb },
         { hlen_c.scratch_ok with }⟩
      have hwf_next : FullWitnessInv c F0 F_cur sem_next.core := by
        have hnw := fullWitnessInv_nw_congr hlen_next.core_ok.cur_vars_le
          (fullWitnessInv_to_nw hlen_c.core_ok.cur_vars_le hwf_c)
          rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        have hwat_next : WatchesInv F_cur sem_next.core := by
          have hw_sp : ModeWatchesInv F_cur sem_next.core :=
            hwf_c.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr)
          simpa only [ModeWatchesInv, sem_next, hdm_c, ↓reduceIte] using hw_sp
        exact fullWitnessInv_of_nw hnw hdm_c hwat_next
      have hcl_sb : sem_b.core.cur_level = s.core.cur_level := by
        have h1 : st_fin.core.cur_level = s_base.core.cur_level :=
          hag_f.get FullCoreState.cur_level
        rw [← hcl_f, h1, hs_base]; exact hcl_o
      have halen_sb : sem_b.core.arena_len = s.core.arena_len := by
        have h1 : st_fin.core.arena_len = s_base.core.arena_len :=
          hag_f.get FullCoreState.arena_len
        rw [← halen_f, h1, hs_base]; exact halen_o
      exact hJ_out sem_next te_mc mc0 hlen_next hwf_next
        ⟨by simpa [sem_next] using htr_s_c.te_ge,
         by simpa [sem_next] using htr_s_c.trl_pref,
         by simpa [sem_next] using htr_s_c.lvl_pres⟩
        (m7_arenaPermEq_congr rfl rfl rfl rfl hperm_s_c)
        (hag_sc.update (fun k => { k with propagated := prop_v.toNat + 1 }))
        (by simp [sem_next, hp1_prop]) hte_c_eq.symm hun_c_eq.symm huf_c_eq.symm
        (by simp [sem_next, hoom_c0]) (by simp [sem_next, hct_c0]) hdm_c
        (by rw [hcv_c, hpi_b_cv, hs_base]; exact hcv_o)
        (by rw [hcl_c]; exact hcl_sb)
        hprob_c
        (by rw [halen_c]; exact halen_sb)
        (by dsimp only [sem_next]; rw [hfuel_c, hs_base]; exact hfl_rem_dec)
        hfuel_nx_dec (Nat.le_of_lt hfuel_nx_dec)
        (by simp [sem_next]; omega) htemc_le hpr_temc hsc_c
        (by simpa [sem_next, fastPropMem, hpr_c] using hmc0)
  · intro Jch hJch
    have hag_base : AgreesExcept m7pCoreMask s.core s_base.core := by
      unfold AgreesExcept m7pCoreMask at hag_o ⊢
      rw [hs_base]; exact hag_o
    have hag_s_fin : AgreesExcept m7pCoreMask s.core st_fin.core :=
      hag_base.trans_mono hag_f (fun _ => rfl) (fun _ => rfl)
    m7p_hsplit
    · have hbrk_ne2 : brk_b ≠ 2#64 := hc
      clear hc
      m7p_hsplit
      · have ht0_lt_te : t0_v.toNat < sem_b.core.trail_end := by rw [← hte_b]; exact hc
        have ht0_le_fin : t0_v.toNat ≤ st_fin.core.trail_end := by
          rw [hte_f]; exact Nat.le_of_lt ht0_lt_te
        m7p_hsteps
        let st_c_in : FullState :=
          { st_fin with
            core :=
              { st_fin.core with
                unassigned := s.core.unassigned, unflushed := s.core.unflushed }
            scratch := { st_fin.scratch with search_ticks := s.scratch.search_ticks } }
        have hcin_len : st_c_in.LengthsOk c :=
          ⟨{ hlen_f.core_ok with }, { hlen_f.scratch_ok with }⟩
        have hcin_nw : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st_c_in.core) :=
          fullWitnessInv_nw_congr hcin_len.core_ok.cur_vars_le
            (fullWitnessInv_to_nw hlen_f.core_ok.cur_vars_le hwf_f)
            rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        have hdm_cin : st_c_in.core.dense_mode = 0#64 :=
          (hag_f.get FullCoreState.dense_mode).trans hdense_b
        have hwat_cin : WatchesInv F_cur st_c_in.core := by
          have hw_sp : ModeWatchesInv F_cur st_c_in.core :=
            hwf_f.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr)
          simpa only [ModeWatchesInv, hdm_cin, ↓reduceIte] using hw_sp
        have hcin_wf : FullWitnessInv c F0 F_cur st_c_in.core :=
          fullWitnessInv_of_nw hcin_nw hdm_cin hwat_cin
        have hpr_f : st_fin.core.propagated = s.core.propagated := by
          have := hag_f.get FullCoreState.propagated
          rw [this, hs_base]
        have hm_cin : (FullMem c st_c_in ⋆ R) m := by
          simpa only [st_c_in, fastPropMem, hte_f, hte_b, hpr_f] using hm
        c0_call hChrono
        refine ⟨c, F0, F_cur, st_c_in, R, rfl, hcin_len, hcin_wf,
          hdm_cin, by simpa [st_c_in] using ht0_le_fin, hm_cin,
          fun ok wv' ar' ws' wl' wu' oom' wso' mc' hlen' hwf' hperm' hok_t
            hok_f hmc' => ?_⟩
        let st_c' : FullState :=
          { st_fin with
            core :=
              { st_fin.core with
                wvec := wv', arena := ar', wstk := ws', wlen := wl',
                wusable := wu', oom := oom' }
            scratch := { st_fin.scratch with wsort := wso' } }
        have hlen_c' : st_c'.LengthsOk c :=
          ⟨{ hlen'.core_ok with }, { hlen'.scratch_ok with }⟩
        have hnw_c' : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st_c'.core) :=
          fullWitnessInv_nw_congr hlen_c'.core_ok.cur_vars_le
            (fullWitnessInv_to_nw hlen'.core_ok.cur_vars_le hwf')
            rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        have hdm_c' : st_c'.core.dense_mode = 0#64 := hdm_cin
        have hwat_c' : WatchesInv F_cur st_c'.core := by
          have hw_sp : ModeWatchesInv F_cur st_c'.core :=
            hwf'.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr)
          simpa only [ModeWatchesInv, hdm_c', ↓reduceIte] using hw_sp
        have hwf_c' : FullWitnessInv c F0 F_cur st_c'.core :=
          fullWitnessInv_of_nw hnw_c' hdm_c' hwat_c'
        have hperm_fc : FullPropDecSpecs.FullArenaPermEq st_fin.core st_c'.core :=
          m7_arenaPermEq_congr rfl rfl rfl rfl hperm'
        have hsc_sem_b : sem_b.scratch = { sem.scratch with
            search_ticks := sem_b.scratch.search_ticks, wsort := sem_b.scratch.wsort,
            phases := sem_b.scratch.phases } := by rw [hpi_b_sc, hs_base]
        have hsc_b' : sem_b.scratch = { s.scratch with
            search_ticks := sem_b.scratch.search_ticks, wsort := sem_b.scratch.wsort,
            phases := sem_b.scratch.phases } := m7p_scratch_trans hsc_o hsc_sem_b
        have hsc_c'_b : st_c'.scratch = { sem_b.scratch with
            search_ticks := st_c'.scratch.search_ticks, wsort := st_c'.scratch.wsort,
            phases := st_c'.scratch.phases } := by
          dsimp only [st_c']; rw [hscr_f]
        have hscr_c' : st_c'.scratch = { s.scratch with
            search_ticks := st_c'.scratch.search_ticks, wsort := st_c'.scratch.wsort,
            phases := st_c'.scratch.phases } :=
          m7p_scratch_trans hsc_b' hsc_c'_b
        have hpr_c_le : s.core.propagated ≤ st_c'.core.trail_end := by
          rw [← hpr_f]
          have := hlen'.core_ok.propagated_le
          simpa [st_c', st_c_in] using this
        have hmc'_fin : (FullMem c (fastPropMem { s with core :=
            { s.core with trail_end := st_c'.core.trail_end } } st_c') ⋆ R) mc' := by
          simpa only [fastPropMem, st_c', st_c_in, hpr_f, hte_f] using hmc'
        m7p_hsplit
        · have hoom_eq' : oom' = sem_b.core.oom := (hok_t hc).trans hoom_f
          have hperm_bc' : FullPropDecSpecs.FullArenaPermEq sem_b.core st_c'.core :=
            (m7_arenaPermEq_congr rfl rfl har_f halen_f (.refl sem_b.core)).trans hperm_fc
          have hconfl_pres :
              (brk_b = 1#64 → PropLitConfl F_cur ignore_ref st_c'.core ∧
                st_c'.core.oom = 0#64) := fun h1 => by
            have ⟨hcf, hoo⟩ := hbr1 h1
            have hcf' : FullPropDecSpecs.FullConflOkW F_cur st_c'.core := by
              rcases hcf with hne | hok
              · exact absurd hoo hne
              · exact m7_fullConflOkW_of_perm hperm_bc' hcv_f hvals_f
                  hct_f hcr_f hc0_f hc1_f hok.1
            refine ⟨Or.inr ⟨hcf', fun h2 => ?_⟩, ?_⟩
            · rcases hcf with hne | hok
              · exact absurd hoo hne
              · simpa [st_c', hct_f, hcr_f] using hok.2 (by simpa [st_c', hct_f] using h2)
            · simp [st_c', hoom_eq', hoo]
          subst hc
          m7p_hsteps
          exact hJch (brk_b, ()) mc'
            ⟨st_c', hlen_c', hwf_c', ⟨htr_f.te_ge, htr_f.trl_pref, htr_f.lvl_pres⟩,
              hperm_f.trans hperm_fc,
              hag_s_fin.update (fun k =>
                { k with wvec := wv', arena := ar', wstk := ws', wlen := wl',
                         wusable := wu', oom := oom' }),
              hcv_f, hvals_f, hte_f, hun_f, huf_f, halen_f, hcl_f, rfl, rfl, rfl,
              fun h0 => by
                have ⟨hoo, hct0⟩ := hbr0 h0
                exact ⟨by simp [st_c', hoom_eq', hoo], by simp [st_c', hct_f, hct0]⟩,
              hconfl_pres, fun _ => trivial,
              by rcases hbr_cases with rfl | rfl | rfl <;> simp,
              hpr_f, by simpa [st_c', hs_base] using hag_f.get FullCoreState.fuel,
              by rw [show st_c'.core.probing = st_fin.core.probing from rfl,
                  hag_f.get FullCoreState.probing, hs_base]; exact hprob_o,
              hdm_c', hscr_c', st_c'.core.trail_end, Nat.le_refl _, hpr_c_le, hmc'_fin⟩
        · subst hc
          m7p_hsteps
          exact hJch (2#64, ()) mc'
            ⟨st_c', hlen_c', hwf_c', ⟨htr_f.te_ge, htr_f.trl_pref, htr_f.lvl_pres⟩,
              hperm_f.trans hperm_fc,
              hag_s_fin.update (fun k =>
                { k with wvec := wv', arena := ar', wstk := ws', wlen := wl',
                         wusable := wu', oom := oom' }),
              hcv_f, hvals_f, hte_f, hun_f, huf_f, halen_f, hcl_f, rfl, rfl, rfl,
              fun h => absurd h (by decide), fun h => absurd h (by decide),
              fun _ => trivial, Or.inr (Or.inr rfl),
              hpr_f, by simpa [st_c', hs_base] using hag_f.get FullCoreState.fuel,
              by rw [show st_c'.core.probing = st_fin.core.probing from rfl,
                  hag_f.get FullCoreState.probing, hs_base]; exact hprob_o,
              hdm_c', hscr_c', st_c'.core.trail_end, Nat.le_refl _, hpr_c_le, hmc'_fin⟩
      · have hperm_bf : FullPropDecSpecs.FullArenaPermEq sem_b.core st_fin.core :=
          m7_arenaPermEq_congr rfl rfl har_f halen_f (.refl sem_b.core)
        have hsc_fin' : st_fin.scratch = { s.scratch with
            search_ticks := st_fin.scratch.search_ticks, wsort := st_fin.scratch.wsort,
            phases := st_fin.scratch.phases } := by
          rw [hscr_f]
          exact m7p_scratch_trans hsc_o (by rw [hpi_b_sc, hs_base])
        m7p_hsteps
        exact hJch (brk_b, ()) mf
          ⟨st_fin, hlen_f, hwf_f, htr_f, hperm_f, hag_s_fin, hcv_f, hvals_f,
            hte_f, hun_f, huf_f, halen_f, hcl_f, rfl, rfl, rfl,
            fun h0 => by
              have ⟨hoo, hct0⟩ := hbr0 h0
              exact ⟨by rw [hoom_f, hoo], by rw [hct_f, hct0]⟩,
            fun h1 => by
              have ⟨hcf, hoo⟩ := hbr1 h1
              refine ⟨?_, by rw [hoom_f, hoo]⟩
              rcases hcf with hne | hok
              · exact absurd hoo hne
              · refine Or.inr ⟨m7_fullConflOkW_of_perm hperm_bf hcv_f hvals_f
                    hct_f hcr_f hc0_f hc1_f hok.1, fun h2 => ?_⟩
                rw [hct_f] at h2; simpa [hcr_f] using hok.2 h2,
            fun _ => trivial, hbr_cases,
            by simpa [hs_base] using hag_f.get FullCoreState.propagated,
            hag_f.get FullCoreState.fuel,
            by rw [hag_f.get FullCoreState.probing, hs_base]; exact hprob_o,
            (hag_f.get FullCoreState.dense_mode).trans hdense_b,
            hsc_fin',
            te_mem, Nat.le_trans htem_le (hte_f ▸ hte_sem_le), hpr_tem, hmf⟩
    · have hbr_ne0 : brk_b ≠ 0#64 := by rw [hc]; decide
      have hbr_ne1 : brk_b ≠ 1#64 := by rw [hc]; decide
      subst hc
      have hsc_fin' : st_fin.scratch = { s.scratch with
          search_ticks := st_fin.scratch.search_ticks, wsort := st_fin.scratch.wsort,
          phases := st_fin.scratch.phases } := by
        rw [hscr_f]
        exact m7p_scratch_trans hsc_o (by rw [hpi_b_sc, hs_base])
      exact hJch (2#64, ()) mf
        ⟨st_fin, hlen_f, hwf_f, htr_f, hperm_f, hag_s_fin, hcv_f, hvals_f, hte_f,
          hun_f, huf_f, halen_f, hcl_f, rfl, rfl, rfl,
          fun h => absurd h (by decide), fun h => absurd h (by decide),
          fun _ => trivial, Or.inr (Or.inr rfl),
          by simpa [hs_base] using hag_f.get FullCoreState.propagated,
          hag_f.get FullCoreState.fuel,
          by rw [hag_f.get FullCoreState.probing, hs_base]; exact hprob_o,
          (hag_f.get FullCoreState.dense_mode).trans hdense_b,
          hsc_fin',
          te_mem, Nat.le_trans htem_le (hte_f ▸ hte_sem_le), hpr_tem, hmf⟩

private theorem m7p_compact_post_ovf_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s sem s_base s_disk sem_b : FullState}
    {ignore_ref prop_v te_b un_b uf_b tk_b off_b p_b q_b end_b brk_b t0_v : BitVec 64}
    {not_lit_v : BitVec 32} {not_lit : BitVec 32}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {mb : Mem 64}
    {J_out : Cont [i64, i64, i64, i64, i64]}
    (hChrono : ∀ args m Q X, fullPropChronoHotSpec args m Q X →
      Γ "full_prop_chrono_hot" [i64, i64] [.bool] args m Q X)
    (hQ : M7pHQ c F0 F_cur s ignore_ref R Q)
    (hJ_out : ∀ (sem_next : FullState) (te_mc : Nat) (mc0 : Mem 64),
      sem_next.LengthsOk c →
      FullWitnessInv c F0 F_cur sem_next.core →
      FullPropDecSpecs.FullTrailExt s.core sem_next.core →
      FullPropDecSpecs.FullArenaPermEq s.core sem_next.core →
      AgreesExcept m7pCoreMask s.core sem_next.core →
      sem_next.core.propagated = (prop_v + 1#64).toNat →
      sem_next.core.trail_end = te_b.toNat →
      sem_next.core.unassigned = un_b →
      sem_next.core.unflushed = uf_b →
      sem_next.core.oom = 0#64 →
      sem_next.core.confl_type = s.core.confl_type →
      sem_next.core.dense_mode = 0#64 →
      sem_next.core.cur_vars = s.core.cur_vars →
      sem_next.core.cur_level = s.core.cur_level →
      sem_next.core.probing = s.core.probing →
      sem_next.core.arena_len = s.core.arena_len →
      sem_next.core.fuel.toNat < sem.core.fuel.toNat →
      sem_next.core.fuel.toNat < s.core.fuel.toNat →
      sem_next.core.fuel.toNat ≤ s.core.fuel.toNat →
      s.core.propagated ≤ sem_next.core.propagated →
      te_mc ≤ sem_next.core.trail_end →
      s.core.propagated ≤ te_mc →
      sem_next.scratch = { s.scratch with
        search_ticks := sem_next.scratch.search_ticks,
        wsort := sem_next.scratch.wsort, phases := sem_next.scratch.phases } →
      (FullMem c (fastPropMem { s with core := { s.core with trail_end := te_mc } }
        { sem_next with core := { sem_next.core with propagated := s.core.propagated } }) ⋆ R) mc0 →
      wp Γ Q X (Expr.jump J_out (.var (prop_v + 1#64), (.var te_b, (.var un_b, (.var uf_b,
        (.var tk_b, ())))))) mc0)
    (hwc : c.wcap < 2 * dimacsBound) (_hmaxv : c.max_vars < 2 * dimacsBound)
    (hlen0 : s.LengthsOk c) (hpr_lt : s.core.propagated < s.core.trail_end)
    (hs_base : s_base = { sem with core := { sem.core with
      propagated := s.core.propagated, fuel := sem.core.fuel - 1#64 } })
    (hs_disk : ∃ te_mem, s_disk = { s with core := { s.core with trail_end := te_mem } } ∧
      te_mem ≤ sem.core.trail_end ∧ s.core.propagated ≤ te_mem)
    (htr_o : FullPropDecSpecs.FullTrailExt s.core sem.core)
    (hperm_o : FullPropDecSpecs.FullArenaPermEq s.core sem.core)
    (hag_o : AgreesExcept m7pCoreMask s.core sem.core)
    (hcv_o : sem.core.cur_vars = s.core.cur_vars)
    (hcl_o : sem.core.cur_level = s.core.cur_level)
    (hprob_o : sem.core.probing = s.core.probing)
    (halen_o : sem.core.arena_len = s.core.arena_len)
    (hsc_o : sem.scratch = { s.scratch with
      search_ticks := sem.scratch.search_ticks, wsort := sem.scratch.wsort,
      phases := sem.scratch.phases })
    (hfl_rem_dec : (sem.core.fuel - 1#64).toNat < sem.core.fuel.toNat)
    (hfuel_le : sem.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hp1_prop : (prop_v + 1#64).toNat = prop_v.toNat + 1)
    (hp_lt_o : prop_v.toNat < sem.core.trail_end)
    (hpr_ge : s.core.propagated ≤ prop_v.toNat)
    (hnl_eq : not_lit_v = not_lit)
    (hnot_lt : not_lit.toNat < 2 * sem.core.cur_vars)
    (hdense_b : s_base.core.dense_mode = 0#64)
    (hpi_b : PropLitInv c F0 F_cur s_base sem_b not_lit.toNat off_b.toNat q_b.toNat
      p_b.toNat end_b.toNat)
    (hte_b : te_b.toNat = sem_b.core.trail_end)
    (hun_b : un_b = sem_b.core.unassigned) (huf_b : uf_b = sem_b.core.unflushed)
    (hbr0 : brk_b = 0#64 → sem_b.core.oom = 0#64 ∧ sem_b.core.confl_type = s.core.confl_type)
    (hbr1 : brk_b = 1#64 → PropLitConfl F_cur ignore_ref sem_b.core ∧ sem_b.core.oom = 0#64)
    (hbr_cases : brk_b = 0#64 ∨ brk_b = 1#64 ∨ brk_b = 2#64)
    (hmb : (FullMem c (fastPropMem s_disk sem_b) ⋆ R) mb) :
    wp Γ Q X (m7pCompactAndPostOvfExpr J_out c.hdr c.pWstk prop_v te_b un_b uf_b tk_b off_b p_b q_b
      end_b brk_b t0_v not_lit_v) mb := by
  subst not_lit_v
  obtain ⟨te_mem, hs_disk_eq, htem_le, hpr_tem⟩ := hs_disk
  have hnot_b : not_lit.toNat < 2 * sem_b.core.cur_vars := by
    rw [hpi_b.cur_vars_eq, hs_base]; exact hnot_lt
  have hend_b_le : end_b.toNat ≤ c.wcap := by
    have := hpi_b.end_lt_wcap hnot_b; omega
  have hwc64 : c.wcap + 1 < 2 ^ 64 := Nat.lt_trans (Nat.add_lt_add_right hwc 1) (by decide)
  have hq_ge_b := hpi_b.sw.q_ge
  have hq_le_b := hpi_b.sw.q_le_p
  have hp_le_b := hpi_b.sw.p_le_end
  have hte_sem_le : sem.core.trail_end ≤ sem_b.core.trail_end := by
    have := hpi_b.tr.te_ge; subst hs_base; exact this
  have hsd_len : s_disk.LengthsOk c := by
    subst hs_disk_eq
    exact ⟨{ hlen0.core_ok with
        trail_end_le := Nat.le_trans htem_le
          (Nat.le_trans hte_sem_le (by
            rw [← hcv_o]
            have hcv_b : sem_b.core.cur_vars = sem.core.cur_vars := by
              rw [hpi_b.cur_vars_eq, hs_base]
            rw [← hcv_b]
            exact hpi_b.len.core_ok.trail_end_le))
        propagated_le := hpr_tem }, hlen0.scratch_ok⟩
  have hnot_b_mv : not_lit.toNat < 2 * c.max_vars := by
    have := hpi_b.len.core_ok.cur_vars_le; omega
  have hnl64_1_idx : ((BitVec.setWidth 64 not_lit <<< (1 : Nat)) + (1 : BitVec 64)).toNat =
      2 * not_lit.toNat + 1 := by
    simpa only [BitVec.ofNat_eq_ofNat] using m7_bv64_shl1_add1_nat not_lit
  unfold m7pCompactAndPostOvfExpr
  refine wp_loop_group (fun rem_c (pc_v, qc_v, ()) mc =>
    ∃ wstk_c : List (BitVec 32),
      rem_c = end_b.toNat - pc_v.toNat ∧
      wstk_c.length = c.wcap ∧
      p_b.toNat ≤ pc_v.toNat ∧ pc_v.toNat ≤ end_b.toNat ∧
      qc_v.toNat = q_b.toNat + (pc_v.toNat - p_b.toNat) ∧
      (∀ k, off_b.toNat ≤ k → k < q_b.toNat → wstk_c[k]? = sem_b.core.wstk[k]?) ∧
      (∀ k < pc_v.toNat - p_b.toNat, wstk_c[q_b.toNat + k]? = sem_b.core.wstk[p_b.toNat + k]?) ∧
      (∀ k, pc_v.toNat ≤ k → k < end_b.toNat → wstk_c[k]? = sem_b.core.wstk[k]?) ∧
      (∀ k, (k < off_b.toNat ∨ end_b.toNat ≤ k) → wstk_c[k]? = sem_b.core.wstk[k]?) ∧
      (FullMem c (fastPropMem s_disk { sem_b with core :=
        { sem_b.core with wstk := wstk_c } }) ⋆ R) mc) ?_ ?_
  · rintro Jc rem_c ⟨pc_v, qc_v, ⟨⟩⟩ mc ih_c ⟨wstk_c, rfl, hwc_len, hp_pc, hpc_end,
        hqc_n, hpre_c, hsuf_c, hrem_c, hout_c, hmc⟩
    have hmem_c_len : (fastPropMem s_disk
        { sem_b with core := { sem_b.core with wstk := wstk_c } }).LengthsOk c :=
      fastPropMem_lengthsOk hsd_len
        (sem := { sem_b with core := { sem_b.core with wstk := wstk_c } })
        ⟨{ hpi_b.len.core_ok with wstk_len_arr := hwc_len }, hpi_b.len.scratch_ok⟩
        (by rw [hpi_b.cur_vars_eq, hs_base, hs_disk_eq]; exact hcv_o)
        (by rw [hs_disk_eq]; dsimp only; rw [hpi_b.ag.get FullCoreState.propagated, hs_base])
        rfl
    have hwc_mem : (fastPropMem s_disk
        { sem_b with core := { sem_b.core with wstk := wstk_c } }).core.wstk.length =
        c.wcap := by rw [fastPropMem_wstk]; exact hwc_len
    m7p_hsplit
    · have hpc_lt : pc_v.toNat < end_b.toNat := hc
      have hpc_lt_w : pc_v.toNat < wstk_c.length := by rw [hwc_len]; omega
      have hqc_lt_w : qc_v.toNat < wstk_c.length := by rw [hwc_len]; omega
      have hpc1_n : (pc_v + 1#64).toNat = pc_v.toNat + 1 := m7_bv64_add1_toNat (by omega)
      have hqc1_n : (qc_v + 1#64).toNat = qc_v.toNat + 1 := m7_bv64_add1_toNat (by omega)
      let v_p := wstk_c[pc_v.toNat]'hpc_lt_w
      let wstk_c' := wstk_c.set qc_v.toNat v_p
      have hstep := propLit_loop2_step hq_ge_b hq_le_b hp_pc hpc_lt hpc_lt_w
        (by rw [← hqc_n]; exact hqc_lt_w) hpre_c hsuf_c hrem_c hout_c
      rw [← hqc_n] at hstep
      m7p_hsteps
      exact ih_c _ (pc_v + 1#64, qc_v + 1#64, ()) m (by rw [hpc1_n]; omega)
        ⟨wstk_c', rfl, by simp [wstk_c', hwc_len], by rw [hpc1_n]; omega,
          by rw [hpc1_n]; omega, by rw [hqc1_n, hpc1_n]; omega,
          hstep.1, fun k hk => by rw [hpc1_n] at hk; exact hstep.2.1 k hk,
          fun k hk1 hk2 => by rw [hpc1_n] at hk1; exact hstep.2.2.1 k hk1 hk2,
          hstep.2.2.2, by
            simpa only [wstk_c', v_p, fastPropMem_with_wstk, fastPropMem_wstk] using hm⟩
    · have hpc_eq : pc_v = end_b := BitVec.eq_of_toNat_eq (by omega)
      rw [hpc_eq] at hqc_n hsuf_c
      m7p_hsteps_nogrp
      refine wp_store_sep (FullArenaTactics.c0_store_full_wvec
        (BitVec.setWidth 32 (qc_v - off_b)) ?_ hmc) ?_
      next =>
        dsimp only
        erw [hnl64_1_idx]
        rw [fastPropMem_wvec, hpi_b.len.core_ok.wvec_len]
        change 2 * not_lit.toNat + 1 < 4 * c.max_vars; omega
      intro m hm
      dsimp only at hm
      erw [hnl64_1_idx] at hm
      rw [fastPropMem_wvec] at hm
      replace hm : (FullMem c (fastPropMem s_disk
          { sem_b with core :=
            { sem_b.core with
              wstk := wstk_c
              wvec := sem_b.core.wvec.set (2 * not_lit.toNat + 1)
                ((qc_v - off_b).setWidth 32) } }) ⋆ R) m := by
        simpa only [fastPropMem] using hm
      refine wp_join_group (ts := []) (fun () mf =>
          ∃ st_fin : FullState,
            st_fin.LengthsOk c ∧
            FullWitnessInv c F0 F_cur st_fin.core ∧
            AgreesExcept propLitCoreMask s_base.core st_fin.core ∧
            FullPropDecSpecs.FullTrailExt s_base.core st_fin.core ∧
            FullPropDecSpecs.FullArenaPermEq s_base.core st_fin.core ∧
            st_fin.core.oom = sem_b.core.oom ∧
            st_fin.core.confl_type = sem_b.core.confl_type ∧
            st_fin.core.confl_ref = sem_b.core.confl_ref ∧
            st_fin.core.confl_lit0 = sem_b.core.confl_lit0 ∧
            st_fin.core.confl_lit1 = sem_b.core.confl_lit1 ∧
            st_fin.core.cur_vars = sem_b.core.cur_vars ∧
            st_fin.core.vals = sem_b.core.vals ∧
            st_fin.core.trail_end = sem_b.core.trail_end ∧
            st_fin.core.unassigned = sem_b.core.unassigned ∧
            st_fin.core.unflushed = sem_b.core.unflushed ∧
            st_fin.core.arena_len = sem_b.core.arena_len ∧
            st_fin.core.cur_level = sem_b.core.cur_level ∧
            st_fin.core.arena = sem_b.core.arena ∧
            st_fin.scratch = sem_b.scratch ∧
            (FullMem c (fastPropMem s_disk st_fin) ⋆ R) mf) ?_ ?_
      · rintro _ ⟨⟩ mf ⟨st_fin, hlen_f, hwf_f, hag_f, htr_f, hperm_f, hoom_f, hct_f,
            hcr_f, hc0_f, hc1_f, hcv_f, hvals_f, hte_f, hun_f, huf_f, halen_f, hcl_f,
            har_f, hscr_f, hmf⟩
        exact m7p_post_ovf_brk_wp hChrono hQ hJ_out hlen0 hpr_lt hs_base
          ⟨te_mem, hs_disk_eq, htem_le, hpr_tem⟩ htr_o hperm_o hag_o hcv_o hcl_o hprob_o
          halen_o hsc_o hfl_rem_dec hfuel_le hp1_prop hp_lt_o hpr_ge hpi_b.len hpi_b.cur_vars_eq
          hpi_b.tr hpi_b.sc_eq hdense_b hte_b hun_b
          huf_b hbr0 hbr1 hbr_cases hlen_f hwf_f hag_f htr_f hperm_f hoom_f hct_f hcr_f hc0_f
          hc1_f hcv_f hvals_f hte_f hun_f huf_f halen_f hcl_f har_f hscr_f hmf
      · intro Jfn hJfn
        have hqc_v_eq : qc_v.toNat = q_b.toNat + (end_b.toNat - p_b.toNat) := hqc_n
        have hqc_le_end : qc_v.toNat ≤ end_b.toNat := by omega
        have hidx1_lt : ((not_lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat <
            sem_b.core.wvec.length := by
          rw [hpi_b.len.core_ok.wvec_len, m7_bv64_shl1_add1_nat]; omega
        let wvec_f := sem_b.core.wvec.set (2 * not_lit.toNat + 1)
          ((qc_v - off_b).setWidth 32)
        let wu_f := sem_b.core.wusable + (end_b - qc_v)
        m7p_hsplit
        · m7p_hsteps
          refine wp_loop_group (fun rem_k (k_v, ()) mk =>
            ∃ wstk_k : List (BitVec 32),
              rem_k = end_b.toNat - k_v.toNat ∧
              wstk_k.length = c.wcap ∧
              qc_v.toNat ≤ k_v.toNat ∧ k_v.toNat ≤ end_b.toNat ∧
              (∀ i, (i < qc_v.toNat ∨ end_b.toNat ≤ i) → wstk_k[i]? = wstk_c[i]?) ∧
              (FullMem c (fastPropMem s_disk { sem_b with core :=
                { sem_b.core with
                  wstk := wstk_k, wvec := wvec_f, wusable := wu_f } }) ⋆ R) mk) ?_ ?_
          · rintro Jk rem_k ⟨k_v, ⟨⟩⟩ mk ih_k ⟨wstk_k, rfl, hwk_len, hq_k, hk_end,
                hk_keep, hmk⟩
            have hmem_k_len : (fastPropMem s_disk { sem_b with core :=
                { sem_b.core with
                  wstk := wstk_k, wvec := wvec_f, wusable := wu_f } }).LengthsOk c :=
              fastPropMem_lengthsOk hsd_len
                (sem := { sem_b with core :=
                  { sem_b.core with wstk := wstk_k, wvec := wvec_f, wusable := wu_f } })
                ⟨{ hpi_b.len.core_ok with
                    wvec_len := by simp [wvec_f, hpi_b.len.core_ok.wvec_len]
                    wstk_len_arr := hwk_len },
                 hpi_b.len.scratch_ok⟩
                (by rw [hpi_b.cur_vars_eq, hs_base, hs_disk_eq]; exact hcv_o)
                (by rw [hs_disk_eq]; dsimp only
                    rw [hpi_b.ag.get FullCoreState.propagated, hs_base])
                rfl
            have hwk_mem : (fastPropMem s_disk { sem_b with core :=
                { sem_b.core with
                  wstk := wstk_k, wvec := wvec_f, wusable := wu_f } }).core.wstk.length =
                c.wcap := by rw [fastPropMem_wstk]; exact hwk_len
            m7p_hsplit
            · have hk_lt : k_v.toNat < end_b.toNat := hc
              have hk_lt_w : k_v.toNat < wstk_k.length := by rw [hwk_len]; omega
              have hk1_n : (k_v + 1#64).toNat = k_v.toNat + 1 := m7_bv64_add1_toNat (by omega)
              have hk_dec : end_b.toNat - (k_v + 1#64).toNat < end_b.toNat - k_v.toNat := by
                omega
              have hq_k1 : qc_v.toNat ≤ (k_v + 1#64).toNat := by omega
              have hk1_end : (k_v + 1#64).toNat ≤ end_b.toNat := by omega
              refine wp_store_sep
                (FullArenaTactics.c0_store_full_wstk 0xFFFFFFFF#32
                  (by rw [hwk_mem]; exact Nat.lt_of_lt_of_eq hk_lt_w hwk_len) hmk) ?_
              intro m hm
              clear hmk hwk_mem
              m7p_hsteps
              dsimp only [Arg.val] at hm
              exact ih_k (end_b.toNat - (k_v + 1#64).toNat) (k_v + 1#64, ()) m hk_dec
                ⟨wstk_k.set k_v.toNat 0xFFFFFFFF#32, rfl,
                  by rw [List.length_set, hwk_len], hq_k1, hk1_end,
                  propLit_loop3_step hq_k hk_lt hk_keep,
                  by simpa only [fastPropMem_with_wstk, fastPropMem_wstk] using hm⟩
            · m7p_hsteps
              have hfin := m7_compact_finish_step hpi_b hdense_b hnot_b hwk_len
                hqc_v_eq hpre_c hsuf_c hout_c hk_keep
              let st_fin_k : FullState :=
                { sem_b with core :=
                  { sem_b.core with wstk := wstk_k, wvec := wvec_f, wusable := wu_f } }
              exact hJfn () mk ⟨st_fin_k, hfin.1, hfin.2.1, hfin.2.2.1, hfin.2.2.2.1,
                hfin.2.2.2.2.1, hfin.2.2.2.2.2.1, hfin.2.2.2.2.2.2.1,
                hfin.2.2.2.2.2.2.2.1, hfin.2.2.2.2.2.2.2.2.1,
                hfin.2.2.2.2.2.2.2.2.2.1, hfin.2.2.2.2.2.2.2.2.2.2.1,
                hfin.2.2.2.2.2.2.2.2.2.2.2.1, hfin.2.2.2.2.2.2.2.2.2.2.2.2.1,
                hfin.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
                hfin.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
                hfin.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
                hfin.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
                rfl, rfl, hmk⟩
          · intro Jk hJk
            exact hJk _ (qc_v, ()) m
              ⟨wstk_c, rfl, hwc_len, Nat.le_refl _, hqc_le_end,
                fun _ _ => rfl,
                by simpa only [wvec_f, wu_f, fastPropMem_wusable, fastPropMem] using hm⟩
        · have hqc_eq_end : qc_v = end_b := BitVec.eq_of_toNat_eq (by omega)
          have hsub0 : end_b - qc_v = 0#64 := by rw [hqc_eq_end]; simp
          have hfin := m7_compact_finish_step hpi_b hdense_b hnot_b hwc_len
            hqc_v_eq hpre_c hsuf_c hout_c (fun _ _ => rfl)
          have hwu0 : sem_b.core.wusable + (end_b - qc_v) = sem_b.core.wusable := by
            rw [hsub0]; simp
          let st_fin_0 : FullState :=
            { sem_b with core :=
              { sem_b.core with
                wstk := wstk_c, wvec := wvec_f,
                wusable := sem_b.core.wusable + (end_b - qc_v) } }
          exact hJfn () m ⟨st_fin_0, hfin.1, hfin.2.1, hfin.2.2.1, hfin.2.2.2.1,
            hfin.2.2.2.2.1, hfin.2.2.2.2.2.1, hfin.2.2.2.2.2.2.1,
            hfin.2.2.2.2.2.2.2.1, hfin.2.2.2.2.2.2.2.2.1,
            hfin.2.2.2.2.2.2.2.2.2.1, hfin.2.2.2.2.2.2.2.2.2.2.1,
            hfin.2.2.2.2.2.2.2.2.2.2.2.1, hfin.2.2.2.2.2.2.2.2.2.2.2.2.1,
            hfin.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
            hfin.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
            hfin.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
            hfin.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
            rfl, rfl, by simpa only [st_fin_0, wvec_f, hwu0] using hm⟩
  · intro Jc hJc
    exact hJc _ (p_b, q_b, ()) mb
      ⟨sem_b.core.wstk, rfl, hpi_b.len.core_ok.wstk_len_arr, Nat.le_refl _,
        hp_le_b, by simp, fun _ _ _ => rfl, fun _ hk => absurd hk (by omega),
        fun _ _ _ => rfl, fun _ _ => rfl, hmb⟩

private def m7pPostLpOvfExpr (c : FullCfg) (not_lit_v : Val i32) (off_o end_o : Val i64)
    (Bo Lo : Cont [i64, i64, i64, i64, i64, i64, i64, i64, i64, Ty.bool])
    (te_p un_p uf_p tk_p p_p q_p brk_p : Val i64) (ovf_p : Val Ty.bool)
    (ovf_rw_p ovf_oth_p ovf_cr_p : Val i32) (ovf_ri_p : Val i64) : Expr Val Cont [i64] :=
  Expr.group (sig := [[i64, i64, i64, i64, i64]])
    (fun _Js0 => Blocks.cons
      (fun p1 => Expr.jump Lo
        (Arg.var te_p, Arg.var un_p, Arg.var uf_p, Arg.var tk_p, Arg.var p1.fst,
          Arg.var p1.snd.fst, Arg.var p1.snd.snd.fst, Arg.var p1.snd.snd.snd.fst,
          Arg.var p1.snd.snd.snd.snd.fst, Arg.var ovf_p, ()))
      Blocks.nil)
    (fun Js0 =>
      Expr.jnz (Arg.var ovf_p)
        (Expr.call (as := [i64, i32, i32, i32]) (bs := [.bool]) "full_prop_lit_ovf_hot"
          (Arg.var c.hdr, Arg.var ovf_rw_p, Arg.var ovf_oth_p, Arg.var ovf_cr_p, ()) fun pok =>
        Expr.let_ ⟨OpCode.add i64, (Arg.var c.hdr, Arg.imm 104, ())⟩ fun wvp =>
        Expr.load i64 (Arg.var wvp.fst) fun wv =>
        Expr.let_ ⟨OpCode.zext 32 64, (Arg.var not_lit_v, ())⟩ fun nl64 =>
        Expr.let_ ⟨OpCode.sext 32 64, (Arg.imm (t := i32) 1, ())⟩ fun s1 =>
        Expr.let_ ⟨OpCode.shl i64, (Arg.var nl64.fst, Arg.var s1.fst, ())⟩ fun idx =>
        Expr.let_ ⟨OpCode.mul i64, (Arg.var idx.fst, Arg.imm 4, ())⟩ fun boff =>
        Expr.let_ ⟨OpCode.add i64, (Arg.var wv, Arg.var boff.fst, ())⟩ fun addr =>
        Expr.load i32 (Arg.var addr.fst) fun noff32 =>
        Expr.let_ ⟨OpCode.zext 32 64, (Arg.var noff32, ())⟩ fun noff =>
        Expr.group (sig := [[i64, i64, i64, i64]])
          (fun _Jn => Blocks.cons
            (fun pn =>
              Expr.jnz (Arg.var pok.fst)
                (Expr.let_ ⟨OpCode.zext 32 64, (Arg.var ovf_cr_p, ())⟩ fun cr64 =>
                Expr.let_ ⟨OpCode.add i64, (Arg.var cr64.fst, Arg.imm 3, ())⟩ fun obase =>
                Expr.let_ ⟨OpCode.mul i64, (Arg.var obase.fst, Arg.imm 4, ())⟩ fun b3 =>
                Expr.let_ ⟨OpCode.add i64, (Arg.var c.pArena, Arg.var b3.fst, ())⟩ fun a3 =>
                Expr.store (Arg.var ovf_oth_p) (Arg.var a3.fst) $
                Expr.let_ ⟨OpCode.add i64, (Arg.var obase.fst, Arg.imm 1, ())⟩ fun ob1 =>
                Expr.let_ ⟨OpCode.mul i64, (Arg.var ob1.fst, Arg.imm 4, ())⟩ fun b4 =>
                Expr.let_ ⟨OpCode.add i64, (Arg.var c.pArena, Arg.var b4.fst, ())⟩ fun a4 =>
                Expr.store (Arg.var ovf_rw_p) (Arg.var a4.fst) $
                Expr.let_ ⟨OpCode.add i64, (Arg.var obase.fst, Arg.var ovf_ri_p, ())⟩ fun obri =>
                Expr.let_ ⟨OpCode.mul i64, (Arg.var obri.fst, Arg.imm 4, ())⟩ fun bri =>
                Expr.let_ ⟨OpCode.add i64, (Arg.var c.pArena, Arg.var bri.fst, ())⟩ fun ari =>
                Expr.store (Arg.var not_lit_v) (Arg.var ari.fst) $
                Expr.jump Js0.fst
                  (Arg.var pn.fst, Arg.var pn.snd.fst, Arg.var pn.snd.snd.fst,
                    Arg.var pn.snd.snd.snd.fst, Arg.var brk_p, ()))
                (Expr.let_ ⟨OpCode.mul i64, (Arg.var pn.snd.snd.fst, Arg.imm 4, ())⟩ fun bq =>
                Expr.let_ ⟨OpCode.add i64, (Arg.var c.pWstk, Arg.var bq.fst, ())⟩ fun aq =>
                Expr.store (Arg.var ovf_oth_p) (Arg.var aq.fst) $
                Expr.let_ ⟨OpCode.add i64, (Arg.var pn.snd.snd.fst, Arg.imm 1, ())⟩ fun q1 =>
                Expr.let_ ⟨OpCode.mul i64, (Arg.var q1.fst, Arg.imm 4, ())⟩ fun bq1 =>
                Expr.let_ ⟨OpCode.add i64, (Arg.var c.pWstk, Arg.var bq1.fst, ())⟩ fun aq1 =>
                Expr.store (Arg.var ovf_cr_p) (Arg.var aq1.fst) $
                Expr.let_ ⟨OpCode.add i64, (Arg.var pn.snd.snd.fst, Arg.imm 2, ())⟩ fun q2 =>
                Expr.jump Bo
                  (Arg.var te_p, Arg.var un_p, Arg.var uf_p, Arg.var tk_p,
                    Arg.var pn.fst, Arg.var pn.snd.fst, Arg.var q2.fst,
                    Arg.var pn.snd.snd.snd.fst, Arg.imm 2, Arg.var ovf_p, ())))
            Blocks.nil)
          (fun Jn =>
            Expr.let_ ⟨OpCode.cmp CmpOp.ne i64, (Arg.var noff.fst, Arg.var off_o, ())⟩ fun ne =>
            Expr.jnz (Arg.var ne.fst)
              (Expr.let_ ⟨OpCode.sub i64, (Arg.var q_p, Arg.var off_o, ())⟩ fun qoff =>
              Expr.let_ ⟨OpCode.add i64, (Arg.var noff.fst, Arg.var qoff.fst, ())⟩ fun qn =>
              Expr.let_ ⟨OpCode.sub i64, (Arg.var p_p, Arg.var off_o, ())⟩ fun poff =>
              Expr.let_ ⟨OpCode.add i64, (Arg.var noff.fst, Arg.var poff.fst, ())⟩ fun pn =>
              Expr.let_ ⟨OpCode.sub i64, (Arg.var end_o, Arg.var off_o, ())⟩ fun eoff =>
              Expr.let_ ⟨OpCode.add i64, (Arg.var noff.fst, Arg.var eoff.fst, ())⟩ fun en =>
              Expr.jump Jn.fst
                (Arg.var noff.fst, Arg.var pn.fst, Arg.var qn.fst, Arg.var en.fst, ()))
              (Expr.jump Jn.fst
                (Arg.var off_o, Arg.var p_p, Arg.var q_p, Arg.var end_o, ()))))
        (Expr.jump Js0.fst
          (Arg.var off_o, Arg.var p_p, Arg.var q_p, Arg.var end_o, Arg.var brk_p, ())))

private theorem m7p_post_lp_ovf_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s_base s_disk sem_o sem_p : FullState}
    {ignore_ref t0_v off_o p_o end_o te_p un_p uf_p tk_p p_p q_p brk_p : BitVec 64}
    {ovf_p : Bool} {not_lit not_lit_v ovf_rw_p ovf_oth_p ovf_cr_p : BitVec 32}
    {ovf_ri_p : BitVec 64}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {mbp : Mem 64}
    {Bo Lo : Cont [i64, i64, i64, i64, i64, i64, i64, i64, i64, Ty.bool]}
    (hOvf : ∀ args m Q X, fullPropLitOvfHotSpec args m Q X →
      Γ "full_prop_lit_ovf_hot" [i64, i32, i32, i32] [.bool] args m Q X)
    (hBo : ∀ xs m,
      (match xs with
        | (te_b, un_b, uf_b, _tk_b, off_b, p_b, q_b, end_b, brk_b, _ovf_b, ()) =>
          ∃ sem_b : FullState,
            PropLitInv c F0 F_cur s_base sem_b not_lit.toNat off_b.toNat q_b.toNat
              p_b.toNat end_b.toNat ∧
            te_b.toNat = sem_b.core.trail_end ∧ un_b = sem_b.core.unassigned ∧
            uf_b = sem_b.core.unflushed ∧
            (t0_v = 0xFFFFFFFFFFFFFFFF#64 ∨ t0_v.toNat ≤ sem_b.core.trail_end) ∧
            (brk_b = 0#64 →
              sem_b.core.oom = 0#64 ∧ sem_b.core.confl_type = s.core.confl_type ∧
              p_b = end_b) ∧
            (brk_b = 1#64 → PropLitConfl F_cur ignore_ref sem_b.core ∧
              sem_b.core.oom = 0#64) ∧
            (brk_b = 0#64 ∨ brk_b = 1#64 ∨ brk_b = 2#64) ∧
            (FullMem c (fastPropMem s_disk sem_b) ⋆ R) m) → Bo xs m)
    (ih_o : ∀ rem' xs m,
      rem' < (end_o.toNat - p_o.toNat) + 1 →
      (match xs with
        | (te_o', un_o', uf_o', _tk_o', off_o', p_o', q_o', end_o', brk_o', ovf_o', ()) =>
          ∃ sem_o' : FullState,
            rem' = (end_o'.toNat - p_o'.toNat) + (if ovf_o' then 1 else 0) ∧
            PropLitInv c F0 F_cur s_base sem_o' not_lit.toNat off_o'.toNat q_o'.toNat
              p_o'.toNat end_o'.toNat ∧
            te_o'.toNat = sem_o'.core.trail_end ∧ un_o' = sem_o'.core.unassigned ∧
            uf_o' = sem_o'.core.unflushed ∧
            (t0_v = 0xFFFFFFFFFFFFFFFF#64 ∨ t0_v.toNat ≤ sem_o'.core.trail_end) ∧
            (ovf_o' = true → brk_o' = 0#64 ∧ sem_o'.core.oom = 0#64 ∧
              sem_o'.core.confl_type = s.core.confl_type) ∧
            (ovf_o' = false →
              (brk_o' = 0#64 →
                sem_o'.core.oom = 0#64 ∧ sem_o'.core.confl_type = s.core.confl_type ∧
                p_o' = end_o') ∧
              (brk_o' = 1#64 → PropLitConfl F_cur ignore_ref sem_o'.core ∧
                sem_o'.core.oom = 0#64) ∧
              (brk_o' = 0#64 ∨ brk_o' = 1#64)) ∧
            (FullMem c (fastPropMem s_disk sem_o') ⋆ R) m) → Lo xs m)
    (har : c.arena_cap < 2 * 2 ^ 28) (hwc : c.wcap < 2 * 2 ^ 28)
    (hsd_len : s_disk.LengthsOk c) (hsd_cv : s_disk.core.cur_vars = sem_p.core.cur_vars)
    (hsd_pr : s_disk.core.propagated = sem_p.core.propagated)
    (hnot_lt : not_lit.toNat < 2 * sem_p.core.cur_vars)
    (hnl64_idx : (not_lit.setWidth 64 <<< (1 : Nat)).toNat = 2 * not_lit.toNat)
    (hct_o2 : sem_o.core.confl_type = s.core.confl_type)
    (ht0_p : t0_v = 0xFFFFFFFFFFFFFFFF#64 ∨ t0_v.toNat ≤ sem_p.core.trail_end)
    (hnl_eq : not_lit_v = not_lit)
    (hpi_p : PropLitInv c F0 F_cur s_base sem_p not_lit.toNat off_o.toNat
      q_p.toNat p_p.toNat end_o.toNat)
    (_hpo_le_pp : p_o.toNat ≤ p_p.toNat)
    (hte_p : te_p.toNat = sem_p.core.trail_end) (hun_p : un_p = sem_p.core.unassigned)
    (huf_p : uf_p = sem_p.core.unflushed) (hoom_p : sem_p.core.oom = 0#64)
    (hnoov : ovf_p = false →
      (brk_p = 0#64 → p_p = end_o ∧ sem_p.core.confl_type = sem_o.core.confl_type) ∧
      (brk_p = 1#64 → PropLitConfl F_cur ignore_ref sem_p.core) ∧
      (brk_p = 0#64 ∨ brk_p = 1#64))
    (hov_yes : ovf_p = true →
      brk_p = 0#64 ∧ sem_p.core.confl_type = sem_o.core.confl_type ∧
      2 ≤ p_p.toNat - off_o.toNat ∧ q_p.toNat + 2 ≤ p_p.toNat ∧
      end_o.toNat - p_p.toNat < end_o.toNat - p_o.toNat ∧
      ovf_cr_p.toNat < 0x80000000 ∧
      ovf_cr_p.toNat ∈ fullArenaClauseRefsCore sem_p.core ∧
      ovf_cr_p.toNat + 3 + fullArenaClauseSizeCore sem_p.core ovf_cr_p.toNat ≤
        sem_p.core.arena_len ∧
      ovf_oth_p.toNat < 2 * sem_p.core.cur_vars ∧
      ovf_rw_p.toNat < 2 * sem_p.core.cur_vars ∧
      ovf_rw_p.toNat ≠ not_lit.toNat ∧
      2 ≤ ovf_ri_p.toNat ∧
      ovf_ri_p.toNat < fullArenaClauseSizeCore sem_p.core ovf_cr_p.toNat ∧
      sem_p.core.arena[ovf_cr_p.toNat + 3]? = some ovf_oth_p ∧
      sem_p.core.arena[ovf_cr_p.toNat + 4]? = some not_lit ∧
      sem_p.core.arena[ovf_cr_p.toNat + 3 + ovf_ri_p.toNat]? = some ovf_rw_p)
    (hmbp : (FullMem c (fastPropMem s_disk sem_p) ⋆ R) mbp) :
    wp Γ Q X (m7pPostLpOvfExpr c not_lit_v off_o end_o Bo Lo
      te_p un_p uf_p tk_p p_p q_p brk_p ovf_p ovf_rw_p ovf_oth_p ovf_cr_p ovf_ri_p) mbp := by
  have hmaxv := c.hmaxv
  unfold dimacsBound at hmaxv
  rw [hnl_eq]
  unfold m7pPostLpOvfExpr
  m7p_hsteps
  m7p_hsplit
  · have hovf_true : ovf_p = true := hc
    have hov_y := hov_yes hovf_true
    subst hovf_true
    obtain ⟨rfl, hct_p, hp_off2, hq_pp2, hrem_dec, hcr_lt, hcr_ref, hcr_fit,
      hoth_lt, hovf_lt, hovf_ne, hri2, hri_lt, har3, har4, har_ri⟩ := hov_y
    have hlen_mp : (fastPropMem s_disk sem_p).LengthsOk c :=
      fastPropMem_lengthsOk hsd_len hpi_p.len hsd_cv.symm hsd_pr.symm rfl
    have hlay_mp : WatchStackLayout (fastPropMem s_disk sem_p).core :=
      fastPropMem_watchLayout hpi_p.sw.layout rfl
    c0_call hOvf
    refine ⟨c, fastPropMem s_disk sem_p, R, rfl, hlen_mp, hlay_mp,
      fun h => absurd h (by decide),
      fun _ => ⟨by
          intro h; rw [h] at hoth_lt
          have h42 : (4294967295#32 : BitVec 32).toNat = 4294967295 := rfl
          rw [h42] at hoth_lt
          have := hpi_p.len.core_ok.cur_vars_le; omega,
        by intro h; rw [h] at hcr_lt; revert hcr_lt; decide⟩,
      hmbp,
      fun pok wv' ws' wl' wu' wsrt' mo' hlen' hlay' hoth_pr hnew_pr hfail_pr hmo' => ?_⟩
    let st4 : FullState :=
      { sem_p with
        core := { sem_p.core with wvec := wv', wstk := ws', wlen := wl', wusable := wu' }
        scratch := { sem_p.scratch with wsort := wsrt' } }
    have hlen4 : st4.LengthsOk c := by
      simp only [fastPropMem_def] at hlen'
      have hso := hlen'.scratch_ok
      have hscr4 : st4.scratch.LengthsOk c :=
        ⟨hso.1, hso.2, hso.3, hso.4, hso.5, hso.6, hso.7, hso.8,
         hso.9, hso.10, hso.11, hso.12, hso.13, hso.14, hso.15, hso.16,
         hso.17, hso.18, hso.19, hso.20, hso.21, hso.22, hso.23, hso.24⟩
      exact ⟨{ hlen'.core_ok with
          trail_end_le := hpi_p.len.core_ok.trail_end_le
          propagated_le := hpi_p.len.core_ok.propagated_le }, hscr4⟩
    have hcv4 : st4.core.cur_vars = sem_p.core.cur_vars := rfl
    have hlay4 : WatchStackLayout st4.core := by
      simp only [fastPropMem_def] at hlay'
      exact { bounds := hlay'.bounds, pos_off := hlay'.pos_off,
              disjoint := hlay'.disjoint, no_sentinel := hlay'.no_sentinel }
    have hperm24 : FullPropDecSpecs.FullArenaPermEq sem_p.core st4.core :=
      ⟨rfl, fun r _ => ⟨rfl, rfl, .refl _⟩⟩
    have hnw4 : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st4.core) :=
      fullWitnessInv_nw_congr hlen4.core_ok.cur_vars_le hpi_p.nw rfl rfl rfl
        rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    have hag4 : AgreesExcept propLitCoreMask s_base.core st4.core :=
      hpi_p.ag.update (fun k =>
        { k with wvec := wv', wstk := ws', wlen := wl', wusable := wu' })
    have htr4 : FullPropDecSpecs.FullTrailExt s_base.core st4.core :=
      ⟨hpi_p.tr.te_ge, hpi_p.tr.trl_pref, hpi_p.tr.lvl_pres⟩
    have hsc4 : st4.scratch = { s_base.scratch with
        search_ticks := st4.scratch.search_ticks,
        wsort := st4.scratch.wsort, phases := st4.scratch.phases } := by
      dsimp only [st4]; rw [hpi_p.sc_eq]
    have hoth_mask : (ovf_oth_p &&& 0x7FFFFFFF#32) = ovf_oth_p :=
      m7_bv32_mask7f_eq (by
        have := hpi_p.cur_vars_eq; have := hpi_p.len.core_ok.cur_vars_le; omega)
    have hp_ge2 : 2 ≤ p_p.toNat := by omega
    have hp_sub2 : (p_p - 2#64).toNat = p_p.toNat - 2 := m7_bv64_sub_toNat hp_ge2
    have hq_le_prev : q_p.toNat ≤ (p_p - 2#64).toNat := by rw [hp_sub2]; omega
    have hp2_back :
        (p_p - 2#64 + 1#64 + 1#64).toNat = (p_p - 2#64).toNat + 2 := by
      have := hpi_p.len.core_ok.wlen_le
      have := hpi_p.end_lt_wcap hnot_lt
      have := hpi_p.sw.p_le_end
      rw [BitVec.toNat_add, BitVec.toNat_add, hp_sub2]
      have h1 : p_p.toNat - 2 + 1 < 2 ^ 64 := by omega
      rw [show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt h1,
        Nat.mod_eq_of_lt (by omega)]
    have hq_le_p' : q_p.toNat ≤ p_p.toNat := hpi_p.sw.q_le_p
    have hnot_f4 : st4.core.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8 := hpi_p.not_f
    have hmem4 : (FullMem c (fastPropMem s_disk st4) ⋆ R) mo' := by
      simpa only [st4, fastPropMem_def] using hmo'
    have hwvc4 := hlen4.core_ok.wvec_len
    have hoff4_lt_wv : 2 * not_lit.toNat < st4.core.wvec.length := by
      rw [hwvc4]; have := hlen4.core_ok.cur_vars_le; omega
    have hoff4_lt_m : (not_lit.setWidth 64 <<< (1 : Nat)).toNat <
        (fastPropMem s_disk st4).core.wvec.length := by
      rw [fastPropMem_wvec, hnl64_idx]; exact hoff4_lt_wv
    have h2n_lt64 : 2 * not_lit.toNat < 2 ^ 64 := by
      have := hlen4.core_ok.cur_vars_le; omega
    have hoff4_mod : 2 * not_lit.toNat % 2 ^ 64 = 2 * not_lit.toNat :=
      Nat.mod_eq_of_lt h2n_lt64
    have hmem_wvec_get : ∀ {i : Nat} (hi : i = 2 * not_lit.toNat)
        (pf : i < (fastPropMem s_disk st4).core.wvec.length),
        ((fastPropMem s_disk st4).core.wvec[i]'pf).setWidth 64 =
        (st4.core.wvec[2 * not_lit.toNat]'hoff4_lt_wv).setWidth 64 := by
      intro i hi pf
      have hg : (fastPropMem s_disk st4).core.wvec[i]? =
          st4.core.wvec[2 * not_lit.toNat]? := by rw [fastPropMem_wvec, hi]
      rw [List.getElem?_eq_getElem pf, List.getElem?_eq_getElem hoff4_lt_wv,
        Option.some.injEq] at hg
      exact congrArg (BitVec.setWidth 64) hg
    m7p_hsteps_nogrp
    refine wp_join_group (fun ((off_n, p_n, q_n, end_n, ()) :
        Tup Val [i64, i64, i64, i64]) mj =>
        mj = mo' ∧
        off_n = (st4.core.wvec[2 * not_lit.toNat]'hoff4_lt_wv).setWidth 64 ∧
        q_n = off_n + (q_p - off_o) ∧
        p_n = off_n + (p_p - off_o) ∧
        end_n = off_n + (end_o - off_o)) ?_ ?_
    · rintro _ ⟨off_n, p_n, q_n, end_n, ⟨⟩⟩ mj ⟨rfl, hoff_n_def, hqn_d, hpn_d, hen_d⟩
      have hpi_p_sh : PropLitInv c F0 F_cur s_base sem_p not_lit.toNat
          off_o.toNat q_p.toNat ((p_p - 2#64).toNat + 2) end_o.toNat := by
        simpa only [show (p_p - 2#64).toNat + 2 = p_p.toNat from by rw [hp_sub2]; omega]
          using hpi_p
      have hpn_d' : p_n = off_n + ((p_p - 2#64) + 1#64 + 1#64 - off_o) := by
        rw [hpn_d, show (p_p - 2#64) + 1#64 + 1#64 = p_p from by
          apply BitVec.eq_of_toNat_eq; rw [hp2_back, hp_sub2]; omega]
      have hoff_n_eq : off_n = BitVec.setWidth 64
          (st4.core.wvec[2 * not_lit.toNat]?.getD 0#32) := by
        rw [hoff_n_def, List.getElem?_eq_getElem hoff4_lt_wv, Option.getD_some]
      clear hoff_n_def hpn_d
      subst hqn_d hen_d hpn_d' hoff_n_eq
      m7p_hsplit
      · have hpok_t : pok = true := hc
        have hok := m7_ovf_ok_step hpi_p_sh hlen4 hcv4 hnot_lt hlay4 hperm24 hnw4
          hag4 htr4 hsc4 hnot_f4 rfl hcr_fit rfl har3 har4 hri2 hri_lt har_ri
          hovf_lt hovf_ne hcr_lt hcr_ref hp2_back hq_le_prev hoth_mask
          (fun l hl hne => by
            have h := hoth_pr l (by simpa only [fastPropMem_def] using hl) hne
            simp only [fastPropMem_def, fullWatchSize, fullWatchSizeCore,
              fullWatchOff, fullWatchOffCore] at h
            simpa only [st4, fullWatchSizeCore, fullWatchOffCore] using h)
          (by
            have h := (hnew_pr hpok_t).2.2
            simp only [fastPropMem_def, fullWatchSize, fullWatchSizeCore,
              fullWatchOff, fullWatchOffCore] at h
            simpa only [st4, fullWatchSizeCore, fullWatchOffCore,
              hoth_mask] using ⟨h.1, h.2.1, h.2.2.1, h.2.2.2 rfl⟩)
        have hcr_u64 : ovf_cr_p.toNat + 3 +
            fullArenaClauseSizeCore sem_p.core ovf_cr_p.toNat < 2 ^ 64 := by
          have := hpi_p.len.core_ok.arena_len_le
          exact Nat.lt_of_le_of_lt (Nat.le_trans hcr_fit this) (Nat.lt_trans har (by decide))
        have har_m4 : (fastPropMem s_disk st4).core.arena.length = sem_p.core.arena.length :=
          congrArg List.length (fastPropMem_arena s_disk st4)
        have h3_idx : (BitVec.setWidth 64 ovf_cr_p + 3).toNat = ovf_cr_p.toNat + 3 := by
          rw [BitVec.toNat_add, bv_c0_zext32_64, show (3 : BitVec 64).toNat = 3 from rfl,
            Nat.mod_eq_of_lt (by omega)]
        have h31_idx : (BitVec.setWidth 64 ovf_cr_p + 3 + 1).toNat = ovf_cr_p.toNat + 4 := by
          rw [BitVec.toNat_add, h3_idx, show (1 : BitVec 64).toNat = 1 from rfl,
            Nat.mod_eq_of_lt (by omega)]
        have hri_idx : (BitVec.setWidth 64 ovf_cr_p + 3 + ovf_ri_p).toNat =
            ovf_cr_p.toNat + 3 + ovf_ri_p.toNat := by
          rw [BitVec.toNat_add, h3_idx, Nat.mod_eq_of_lt (by omega)]
        have har3_m : (BitVec.setWidth 64 ovf_cr_p + 3).toNat <
            (fastPropMem s_disk st4).core.arena.length := by
          rw [h3_idx, har_m4]; exact (List.getElem?_eq_some_iff.mp har3).1
        have har31_m : (BitVec.setWidth 64 ovf_cr_p + 3 + 1).toNat <
            (fastPropMem s_disk st4).core.arena.length := by
          rw [h31_idx, har_m4]; exact (List.getElem?_eq_some_iff.mp har4).1
        have har_ri_m : (BitVec.setWidth 64 ovf_cr_p + 3 + ovf_ri_p).toNat <
            (fastPropMem s_disk st4).core.arena.length := by
          rw [hri_idx, har_m4]; exact (List.getElem?_eq_some_iff.mp har_ri).1
        m7p_hsteps
        exact ih_o _ (te_p, un_p, uf_p, tk_p, _, _, _, _, 0#64, true, ()) _
          (by
            simp only [↓reduceIte]
            rw [hok.2.2.2.2.1, show (p_p - 2#64).toNat + 2 = p_p.toNat from by
              rw [hp_sub2]; exact Nat.sub_add_cancel hp_ge2]
            exact Nat.add_lt_add_right hrem_dec 1)
          ⟨_, rfl, hok.2.2.2.2.2, hte_p, hun_p, huf_p, ht0_p,
            fun _ => ⟨rfl, hoom_p, hct_p.trans hct_o2⟩,
            fun h => absurd h (by decide),
            by
              simpa only [fastPropMem_arena, fastPropMem_with_arena,
                h3_idx, h31_idx, hri_idx] using hm⟩
      · have hpok_f : pok = false := hc
        have hfail := m7_ovf_fail_step hpi_p_sh hlen4 hcv4 hnot_lt
          hlay4 hperm24 hnw4 hag4 htr4 hsc4 hnot_f4 hovf_lt hovf_ne hcr_lt
          hcr_ref hp2_back hq_le_prev hoth_mask
          (fun l hl hne => by
            have h := hoth_pr l (by simpa only [fastPropMem_def] using hl) hne
            simp only [fastPropMem_def, fullWatchSize, fullWatchSizeCore,
              fullWatchOff, fullWatchOffCore] at h
            simpa only [st4, fullWatchSizeCore, fullWatchOffCore] using h)
          (by
            have h := (hfail_pr hpok_f).1
              (by simpa only [fastPropMem_def, hpi_p.cur_vars_eq] using hovf_lt)
            simp only [fastPropMem_def, fullWatchSize, fullWatchSizeCore,
              fullWatchOff, fullWatchOffCore] at h
            simpa only [st4, fullWatchSizeCore, fullWatchOffCore] using h)
        have hq_wlen :
            (BitVec.setWidth 64 (st4.core.wvec[2 * not_lit.toNat]?.getD 0#32) +
              (q_p - off_o)).toNat < (fastPropMem s_disk st4).core.wstk.length := by
          rw [fastPropMem_wstk]; exact hfail.1
        have hq1_wlen :
            (BitVec.setWidth 64 (st4.core.wvec[2 * not_lit.toNat]?.getD 0#32) +
              (q_p - off_o) + 1).toNat < (fastPropMem s_disk st4).core.wstk.length := by
          rw [fastPropMem_wstk, show (1 : BitVec 64) = 1#64 from rfl, hfail.2.2.1]
          exact hfail.2.1
        ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsteps!)
        refine hBo _ _ ⟨_, hfail.2.2.2.2.2.2.2, hte_p, hun_p, huf_p, ht0_p,
          fun h => absurd h (by decide), fun h => absurd h (by decide), Or.inr (Or.inr rfl),
          by
            simpa only [fastPropMem_wstk, fastPropMem_with_wstk,
              show (1 : BitVec 64) = 1#64 from rfl, hfail.2.2.1] using hm⟩
    · intro Jn hJn
      m7p_hsplit
      · m7p_hsteps
        have hnoff := hmem_wvec_get hnl64_idx hoff4_lt_m
        exact hJn _ mo' ⟨rfl, hnoff, rfl, rfl, rfl⟩
      · m7p_hsteps
        have hnoff_eq := hmem_wvec_get hoff4_mod
          (by rw [hoff4_mod, fastPropMem_wvec]; exact hoff4_lt_wv)
        have hoff_eq : off_o = (st4.core.wvec[2 * not_lit.toNat]'hoff4_lt_wv).setWidth 64 :=
          hc.symm.trans hnoff_eq
        have had_sub : ∀ {x : BitVec 64}, off_o.toNat ≤ x.toNat →
            x.toNat < 2 ^ 64 → x = off_o + (x - off_o) := by
          intro x hle hlt
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_add, m7_bv64_sub_toNat hle, Nat.mod_eq_of_lt (by omega)]
          omega
        have hend_lt : end_o.toNat < 2 ^ 64 :=
          Nat.lt_of_le_of_lt
            (Nat.le_trans (hpi_p.end_lt_wcap hnot_lt).1 (hpi_p.end_lt_wcap hnot_lt).2)
            (Nat.lt_trans hwc (by decide))
        have hq_ge := hpi_p.sw.q_ge
        have hq_le := hpi_p.sw.q_le_p
        have hp_le := hpi_p.sw.p_le_end
        exact hJn _ mo' ⟨rfl, hoff_eq,
          had_sub hq_ge (by omega),
          had_sub (Nat.le_trans hq_ge hq_le) (by omega),
          had_sub (Nat.le_trans hq_ge (Nat.le_trans hq_le hp_le)) hend_lt⟩
  · have hovf_false : ovf_p = false := hc
    subst hovf_false
    have ⟨hbrk0_fn, hbrk1_fn, hbrk_disj⟩ := hnoov rfl
    m7p_hsteps
    exact ih_o _ (te_p, un_p, uf_p, tk_p, off_o, p_p, q_p, end_o, brk_p, false, ()) mbp
      (by simp only [Bool.false_eq_true, ↓reduceIte]; have := _hpo_le_pp; omega)
      ⟨sem_p, rfl, hpi_p, hte_p, hun_p, huf_p, ht0_p,
        fun h => absurd h (by decide),
        fun _ => ⟨fun h0 => ⟨hoom_p, (hbrk0_fn h0).2.trans hct_o2, (hbrk0_fn h0).1⟩,
          fun h1 => ⟨hbrk1_fn h1, hoom_p⟩, by rcases hbrk_disj with rfl | rfl <;> simp⟩,
        hmbp⟩

/-- `full_propagate_ignore_hot` satisfies exact `Full.FullPropDecSpecs.fullPropagateIgnoreSpec`
while unconditionally accumulating `h->search_ticks += ticks` regardless of `h->probing`. -/
theorem full_propagate_ignore_hot_wp (Γ : Env)
    (hOvf : ∀ args m Q X, fullPropLitOvfHotSpec args m Q X →
      Γ "full_prop_lit_ovf_hot" [i64, i32, i32, i32] [.bool] args m Q X)
    (hChrono : ∀ args m Q X, fullPropChronoHotSpec args m Q X →
      Γ "full_prop_chrono_hot" [i64, i64] [.bool] args m Q X) :
    ∀ args m Q X, FullPropDecSpecs.fullPropagateIgnoreSpec args m Q X →
      Func.wp Γ full_propagate_ignore_hot_body args m Q X := by
  rintro ⟨h, ignore_ref, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen0, hw0, hdense0, hm0, hQ⟩
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have har := c.harena; unfold dimacsBound at har
  have hwc := c.hwcap; unfold dimacsBound at hwc
  have hcv0 := hlen0.core_ok.cur_vars_le
  have hcv_lt64 : s.core.cur_vars < 2 ^ 64 :=
    Nat.lt_of_le_of_lt hcv0 (Nat.lt_trans hmaxv (by decide))
  have h2cv_lt64 : 2 * s.core.cur_vars < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_left 2 hcv0)
      (Nat.lt_trans (Nat.mul_lt_mul_of_pos_left hmaxv (by decide)) (by decide))
  have h2cv_lt31 : 2 * s.core.cur_vars < 2 ^ 31 :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_left 2 hcv0)
      (Nat.lt_trans (Nat.mul_lt_mul_of_pos_left hmaxv (by decide)) (by decide))
  have hte0_lt64 : s.core.trail_end < 2 ^ 64 :=
    Nat.lt_of_le_of_lt hlen0.core_ok.trail_end_le hcv_lt64
  have hpr0_lt64 : s.core.propagated < 2 ^ 64 :=
    Nat.lt_of_le_of_lt hlen0.core_ok.propagated_le hte0_lt64
  have hclv_lt32 : s.core.cur_level < 2 ^ 32 := by
    have := hw0.cur_level_le; have := hlen0.core_ok.trail_end_le; omega
  have hclv_lt64 : s.core.cur_level < 2 ^ 64 := Nat.lt_trans hclv_lt32 (by decide)
  have hal0_lt64 : s.core.arena_len < 2 ^ 64 :=
    Nat.lt_of_le_of_lt hlen0.core_ok.arena_len_le (Nat.lt_trans har (by decide))
  unfold Func.wp full_propagate_ignore_hot_body
  m7p_hsplit
  · have hge : s.core.trail_end ≤ s.core.propagated := by
      have hh : s.core.trail_end % 2 ^ 64 ≤ s.core.propagated % 2 ^ 64 := hc
      rwa [Nat.mod_eq_of_lt hte0_lt64, Nat.mod_eq_of_lt hpr0_lt64] at hh
    have hpe : s.core.propagated = s.core.trail_end :=
      Nat.le_antisymm hlen0.core_ok.propagated_le hge
    exact hQ 0#64 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      hlen0 hw0 (.refl _) (.refl _) (Nat.le_refl _) (Or.inl rfl)
      (fun _ => ⟨hpe, rfl, fun h => h,
        fun hlt => absurd hlt (Nat.not_lt_of_ge (Nat.le_of_eq hpe.symm))⟩)
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun _ => ⟨rfl, rfl⟩) hm0
  · have hpr_lt : s.core.propagated < s.core.trail_end := by
      have hh : ¬ s.core.trail_end % 2 ^ 64 ≤ s.core.propagated % 2 ^ 64 := hc
      rwa [Nat.mod_eq_of_lt hte0_lt64, Nat.mod_eq_of_lt hpr0_lt64, Nat.not_le] at hh
    m7p_hsplit
    · exact hQ 2#64 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        hlen0 hw0 (.refl _) (.refl _) (Nat.le_refl _) (Or.inr (Or.inr rfl))
        (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
        (fun _ => Or.inl hc) (fun h => absurd h (Nat.ne_of_lt hpr_lt)) hm0
    · have hoom0 : s.core.oom = 0#64 := hc
      m7p_hsteps_nogrp
      refine wp_loop_group (fun rem (prop_v, tend_v, unass_v, unfl_v, ticks_v, ()) ml =>
        M7pOuterInv c F0 F_cur s R rem prop_v tend_v unass_v unfl_v ticks_v ml) ?_ ?_
      · rintro J rem ⟨prop_v, tend_v, unass_v, unfl_v, ticks_v, ⟨⟩⟩ ml ih
          ⟨sem, te_mem, rfl, hlen_o, hw_o, htr_o, hperm_o, hag_o, hprop_eq, htend_eq,
           hunass_eq, hunfl_eq, hoom_o, hct_o, hdm_o, hcv_o, hcl_o, hprob_o, halen_o,
           hfuel_le, hfuel_lt, hpr_ge, htem_le, hpr_tem, hsc_o, hml⟩
        let s_disk : FullState := { s with core := { s.core with trail_end := te_mem } }
        let sem_d : FullState :=
          { sem with core := { sem.core with propagated := s.core.propagated } }
        have hsd_len : s_disk.LengthsOk c :=
          ⟨{ hlen0.core_ok with
              trail_end_le := Nat.le_trans htem_le (hcv_o ▸ hlen_o.core_ok.trail_end_le)
              propagated_le := hpr_tem },
           hlen0.scratch_ok⟩
        have hsemd_len : sem_d.LengthsOk c :=
          ⟨{ hlen_o.core_ok with
              propagated_le := Nat.le_trans hpr_ge (hprop_eq ▸ hlen_o.core_ok.propagated_le) },
           hlen_o.scratch_ok⟩
        have hmem_len : (fastPropMem s_disk sem_d).LengthsOk c :=
          fastPropMem_lengthsOk hsd_len hsemd_len (by simp [s_disk, sem_d, hcv_o]) rfl rfl
        have hte_lt64 : sem.core.trail_end < 2 ^ 64 :=
          Nat.lt_of_le_of_lt hlen_o.core_ok.trail_end_le (hcv_o ▸ hcv_lt64)
        have hpr_o_lt64 : sem.core.propagated < 2 ^ 64 :=
          Nat.lt_of_le_of_lt hlen_o.core_ok.propagated_le hte_lt64
        m7p_hsplit
        · have hp_lt_o : prop_v.toNat < tend_v.toNat := hc
          have hp_lt_sem : sem.core.propagated < sem.core.trail_end := by
            rw [hprop_eq, htend_eq]; exact hp_lt_o
          m7p_hsplit
          · have hfl0 : sem.core.fuel = 0#64 := by
              simpa [s_disk, sem_d, m7_fastPropMem_fuel] using hc
            clear ih
            m7p_hsteps
            exact m7p_outer_flush_ret (ticks' := s.scratch.search_ticks + ticks_v)
              hQ hlen_o hw_o htr_o hperm_o hag_o hsc_o
              hprop_eq htend_eq hunass_eq hunfl_eq hfuel_le hpr_lt
              (Or.inr (Or.inr rfl)) (fun h => absurd h (by decide)) (by decide)
              (fun _ => Or.inr hfl0)
              (by
                simpa only [fastPropMem, s_disk, sem_d, hprop_eq, htend_eq,
                  hunass_eq, hunfl_eq] using hm)
          · have hfl_ne : sem.core.fuel ≠ 0#64 := by
              simpa [s_disk, sem_d, m7_fastPropMem_fuel] using hc
            have hfl_pos : 0 < sem.core.fuel.toNat := by
              by_cases h0 : sem.core.fuel.toNat = 0
              · exact absurd (BitVec.eq_of_toNat_eq h0) hfl_ne
              · omega
            have hfl_dec : (sem.core.fuel - 1#64).toNat = sem.core.fuel.toNat - 1 :=
              m7_bv64_sub_toNat (by simp; omega)
            have hfl_rem_dec : (sem.core.fuel - 1#64).toNat < sem.core.fuel.toNat := by omega
            have hp_lt_trl : prop_v.toNat < (fastPropMem s_disk sem_d).core.trl.length := by
              rw [fastPropMem_trl, hlen_o.core_ok.trl_len]
              have := hlen_o.core_ok.trail_end_le; have := hcv_o; omega
            let lit := (fastPropMem s_disk sem_d).core.trl[prop_v.toNat]'hp_lt_trl
            have hlit_eq : lit = sem.core.trl[sem.core.propagated]'(by
                rw [hlen_o.core_ok.trl_len]; have := hlen_o.core_ok.trail_end_le
                have := hcv_o; omega) := by
              simp only [lit, fc_getElem_trl]
              exact (fc_getElem_eq_of_idx hprop_eq _ _).symm
            have hlit_lt : lit.toNat < 2 * sem.core.cur_vars := by
              have := hw_o.trail_lits_lt sem.core.propagated hp_lt_sem
              have hlt_trl : sem.core.propagated < sem.core.trl.length := by
                rw [hlen_o.core_ok.trl_len]; have := hlen_o.core_ok.trail_end_le
                have := hcv_o; omega
              rwa [List.getElem?_eq_getElem hlt_trl, Option.getD_some, ← hlit_eq] at this
            let not_lit := lit ^^^ 1#32
            have hnot_lt : not_lit.toNat < 2 * sem.core.cur_vars := by
              dsimp only [not_lit]; rw [BitVec.toNat_xor]
              simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
              rw [fc_nat_xor_one]; split <;> omega
            have hnot_f0 : sem.core.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8 := by
              have hlt_trl : sem.core.propagated < sem.core.trl.length := by
                rw [hlen_o.core_ok.trl_len]; have := hlen_o.core_ok.trail_end_le
                have := hcv_o; omega
              refine (hw_o.vals_false_iff not_lit.toNat hnot_lt).mpr
                ⟨sem.core.propagated, hp_lt_sem, ?_⟩
              rw [List.getElem?_eq_getElem hlt_trl, Option.getD_some, ← hlit_eq]
              dsimp only [not_lit]; rw [BitVec.toNat_xor]
              simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
              rcases Nat.mod_two_eq_zero_or_one lit.toNat with h | h
              · have h2 : (lit.toNat + 1) % 2 = 1 := by omega
                simp only [fc_nat_xor_one, h, ↓reduceIte, h2, Nat.one_ne_zero]; omega
              · have h2 : (lit.toNat - 1) % 2 = 0 := by omega
                simp only [fc_nat_xor_one, h, Nat.one_ne_zero, ↓reduceIte, h2]; omega
            have hnl64_idx : (not_lit.setWidth 64 <<< (1 : Nat)).toNat = 2 * not_lit.toNat :=
              m7_bv64_shl1_u32_nat not_lit
            have hnl64_1_idx : ((not_lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat =
                2 * not_lit.toNat + 1 := m7_bv64_shl1_add1_nat not_lit
            have hwv_o_len := hlen_o.core_ok.wvec_len
            have hp1_prop : (prop_v + 1#64).toNat = prop_v.toNat + 1 :=
              m7_bv64_add1_toNat (by have := hte_lt64; omega)
            have hnl64_lt_wv0 : (not_lit.setWidth 64 <<< (1 : Nat)).toNat <
                sem.core.wvec.length := by
              rw [hwv_o_len, hnl64_idx]; have := hlen_o.core_ok.cur_vars_le; omega
            have hnl64_1_lt_wv0 : ((not_lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat <
                sem.core.wvec.length := by
              rw [hwv_o_len, hnl64_1_idx]; have := hlen_o.core_ok.cur_vars_le; omega
            have hnl64_lt_wv : (not_lit.setWidth 64 <<< (1 : Nat)).toNat <
                (fastPropMem s_disk sem_d).core.wvec.length := by
              rw [fastPropMem_wvec]; exact hnl64_lt_wv0
            have hnl64_1_lt_wv : ((not_lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat <
                (fastPropMem s_disk sem_d).core.wvec.length := by
              rw [fastPropMem_wvec]; exact hnl64_1_lt_wv0
            have h_wvec_len_mem : (fastPropMem s_disk sem_d).core.wvec.length =
                4 * c.max_vars := by
              rw [fastPropMem_wvec, hwv_o_len]
            have hp_sem_lt_trl : prop_v.toNat < sem.core.trl.length := by
              rw [hlen_o.core_ok.trl_len]
              have := hlen_o.core_ok.trail_end_le; have := hcv_o; omega
            have hsz_hc_idx :
                ((not_lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat =
                  (2 * ((sem.core.trl[prop_v.toNat]'hp_sem_lt_trl).toNat ^^^ 1) + 1) %
                    2 ^ 64 := by
              have hlit_trl : sem.core.trl[prop_v.toNat]'hp_sem_lt_trl = lit := by
                simp only [lit, fc_getElem_trl, sem_d]
              have hnot_toNat : not_lit.toNat = lit.toNat ^^^ 1 := by
                dsimp only [not_lit]; rw [BitVec.toNat_xor]
                simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
              rw [hnl64_1_idx, hlit_trl, ← hnot_toNat,
                Nat.mod_eq_of_lt (by have := hlen_o.core_ok.cur_vars_le; omega)]
            m7p_hsplit
            · have hsz0 : (sem.core.wvec[((not_lit.setWidth 64 <<< (1 : Nat)) +
                  1#64).toNat]'hnl64_1_lt_wv0).setWidth 64 = 0#64 := by
                have hc' := hc
                simp only [fastPropMem_wvec, fastPropMem_trl] at hc'
                rw [fc_getElem_eq_of_idx hsz_hc_idx hnl64_1_lt_wv0
                  (by rw [← hsz_hc_idx]; exact hnl64_1_lt_wv0)]
                exact hc'
              m7p_hsteps
              let sem_n : FullState :=
                { sem with
                  core :=
                    { sem.core with
                      propagated := prop_v.toNat + 1
                      fuel := sem.core.fuel - 1#64 } }
              have hlen_n : sem_n.LengthsOk c :=
                ⟨{ hlen_o.core_ok with propagated_le := by rw [htend_eq]; exact hp_lt_o },
                 hlen_o.scratch_ok⟩
              have hwat_n : WatchesInv F_cur sem_n.core := by
                have hw_sp : ModeWatchesInv F_cur sem_n.core :=
                  hw_o.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr)
                have hdm_n : sem_n.core.dense_mode = 0#64 := hdm_o
                simpa only [ModeWatchesInv, hdm_n, ↓reduceIte] using hw_sp
              have hw_n : FullWitnessInv c F0 F_cur sem_n.core :=
                fullWitnessInv_of_nw
                  (fullWitnessInv_nw_congr hlen_n.core_ok.cur_vars_le
                    (fullWitnessInv_to_nw hlen_o.core_ok.cur_vars_le hw_o) rfl rfl rfl rfl rfl rfl
                    rfl rfl rfl rfl rfl rfl rfl)
                  (show sem_n.core.dense_mode = 0#64 from hdm_o) hwat_n
              exact ih (sem_n.core.fuel.toNat) (prop_v + 1#64, tend_v, unass_v, unfl_v,
                  ticks_v, ()) m hfl_rem_dec
                ⟨sem_n, te_mem, rfl, hlen_n, hw_n,
                  ⟨htr_o.te_ge, htr_o.trl_pref, htr_o.lvl_pres⟩,
                  hperm_o, m7p_agrees_upd_prop_fuel hag_o, by simp [sem_n, hp1_prop], htend_eq,
                  hunass_eq, hunfl_eq, hoom_o,
                  hct_o, hdm_o, hcv_o, hcl_o, hprob_o, halen_o,
                  Nat.le_trans (Nat.le_of_lt hfl_rem_dec) hfuel_le,
                  fun _ => Nat.lt_of_lt_of_le hfl_rem_dec hfuel_le,
                  by rw [hp1_prop]; omega, htem_le, hpr_tem, hsc_o, by
                    simpa [sem_n, sem_d, fastPropMem] using hm⟩
            · have hsz_ne : (sem.core.wvec[((not_lit.setWidth 64 <<< (1 : Nat)) +
                  1#64).toNat]'hnl64_1_lt_wv0).setWidth 64 ≠ 0#64 := by
                have hc' := hc
                simp only [fastPropMem_wvec, fastPropMem_trl] at hc'
                rw [fc_getElem_eq_of_idx hsz_hc_idx hnl64_1_lt_wv0
                  (by rw [← hsz_hc_idx]; exact hnl64_1_lt_wv0)]
                exact hc'
              let s_base : FullState :=
                { sem with core := { sem.core with
                  propagated := s.core.propagated, fuel := sem.core.fuel - 1#64 } }
              have hbase_len : s_base.LengthsOk c :=
                ⟨{ hlen_o.core_ok with
                    propagated_le :=
                      Nat.le_trans hpr_ge (hprop_eq ▸ hlen_o.core_ok.propagated_le) },
                 hlen_o.scratch_ok⟩
              have hbase_nw : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c s_base.core) :=
                fullWitnessInv_nw_congr hbase_len.core_ok.cur_vars_le
                  (fullWitnessInv_to_nw hlen_o.core_ok.cur_vars_le hw_o) rfl rfl rfl rfl rfl rfl
                  rfl rfl rfl rfl rfl rfl rfl
              have hwat_base : WatchesInv F_cur s_base.core := by
                have hw_sp : ModeWatchesInv F_cur s_base.core :=
                  hw_o.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr)
                have hdm_b : s_base.core.dense_mode = 0#64 := hdm_o
                simpa only [ModeWatchesInv, hdm_b, ↓reduceIte] using hw_sp
              have hoff0_nat : ((sem.core.wvec[(not_lit.setWidth 64 <<< (1 : Nat)).toNat]'
                  hnl64_lt_wv0).setWidth 64).toNat =
                  fullWatchOffCore s_base.core not_lit.toNat := by
                unfold fullWatchOffCore
                rw [bv_c0_zext32_64]
                exact congrArg BitVec.toNat (fc_getElem_eq_getD_of_idx hnl64_idx _)
              have hsz0_nat : ((sem.core.wvec[((not_lit.setWidth 64 <<< (1 : Nat)) +
                  1#64).toNat]'hnl64_1_lt_wv0).setWidth 64).toNat =
                  fullWatchSizeCore s_base.core not_lit.toNat := by
                unfold fullWatchSizeCore
                rw [bv_c0_zext32_64]
                exact congrArg BitVec.toNat (fc_getElem_eq_getD_of_idx hnl64_1_idx _)
              have hsz0_pos : 0 < fullWatchSizeCore s_base.core not_lit.toNat := by
                rw [← hsz0_nat]
                by_cases h0 : ((sem.core.wvec[((not_lit.setWidth 64 <<< (1 : Nat)) +
                    1#64).toNat]'hnl64_1_lt_wv0).setWidth 64).toNat = 0
                · exact absurd (BitVec.eq_of_toNat_eq h0) hsz_ne
                · omega
              have hpi0 : PropLitInv c F0 F_cur s_base s_base not_lit.toNat
                  (fullWatchOffCore s_base.core not_lit.toNat)
                  (fullWatchOffCore s_base.core not_lit.toNat)
                  (fullWatchOffCore s_base.core not_lit.toNat)
                  (fullWatchOffCore s_base.core not_lit.toNat +
                    fullWatchSizeCore s_base.core not_lit.toNat) :=
                { len := hbase_len, nw := hbase_nw
                  sw := SplitWatchesInv.init (hcv_o ▸ hnot_lt) hwat_base hsz0_pos
                  ag := .refl _ _, tr := .refl _, perm := .refl _, sc_eq := rfl
                  not_f := by simpa [s_base] using hnot_f0 }
              m7p_hsteps_nogrp
              have hm_base : (FullMem c (fastPropMem s_disk s_base) ⋆ R) m := by
                simpa only [fastPropMem, s_base, s_disk, sem_d,
                  BitVec.ofNat_eq_ofNat] using hm
              clear hm
              refine wp_join_group (fun (t0_v, ()) mt =>
                  (FullMem c (fastPropMem s_disk s_base) ⋆ R) mt ∧
                  (t0_v = 0xFFFFFFFFFFFFFFFF#64 ∨ t0_v.toNat ≤ sem.core.trail_end))
                ?_ ?_
              · rintro _ ⟨t0_v, ⟨⟩⟩ mt ⟨hm_t, ht0_bound⟩
                have hend0_lt64 : fullWatchOffCore s_base.core not_lit.toNat +
                    fullWatchSizeCore s_base.core not_lit.toNat < 2 ^ 64 := by
                  have := hpi0.end_lt_wcap hnot_lt
                  exact Nat.lt_of_le_of_lt (Nat.le_trans this.1 this.2)
                    (Nat.lt_trans hwc (by decide))
                m7p_hsteps_nogrp
                refine wp_loop_break_group
                  (fun (te_b, un_b, uf_b, tk_b, off_b, p_b, q_b, end_b, brk_b, _ovf_b, ()) mb =>
                    ∃ sem_b : FullState,
                      PropLitInv c F0 F_cur s_base sem_b not_lit.toNat off_b.toNat q_b.toNat
                        p_b.toNat end_b.toNat ∧
                      te_b.toNat = sem_b.core.trail_end ∧ un_b = sem_b.core.unassigned ∧
                      uf_b = sem_b.core.unflushed ∧
                      (t0_v = 0xFFFFFFFFFFFFFFFF#64 ∨ t0_v.toNat ≤ sem_b.core.trail_end) ∧
                      (brk_b = 0#64 →
                        sem_b.core.oom = 0#64 ∧ sem_b.core.confl_type = s.core.confl_type ∧
                        p_b = end_b) ∧
                      (brk_b = 1#64 → PropLitConfl F_cur ignore_ref sem_b.core ∧
                        sem_b.core.oom = 0#64) ∧
                      (brk_b = 0#64 ∨ brk_b = 1#64 ∨ brk_b = 2#64) ∧
                      (FullMem c (fastPropMem s_disk sem_b) ⋆ R) mb)
                  (fun rem_o (te_o, un_o, uf_o, tk_o, off_o, p_o, q_o, end_o, brk_o, ovf_o, ())
                      mo =>
                    ∃ sem_o : FullState,
                      rem_o = (end_o.toNat - p_o.toNat) + (if ovf_o then 1 else 0) ∧
                      PropLitInv c F0 F_cur s_base sem_o not_lit.toNat off_o.toNat q_o.toNat
                        p_o.toNat end_o.toNat ∧
                      te_o.toNat = sem_o.core.trail_end ∧ un_o = sem_o.core.unassigned ∧
                      uf_o = sem_o.core.unflushed ∧
                      (t0_v = 0xFFFFFFFFFFFFFFFF#64 ∨ t0_v.toNat ≤ sem_o.core.trail_end) ∧
                      (ovf_o = true → brk_o = 0#64 ∧ sem_o.core.oom = 0#64 ∧
                        sem_o.core.confl_type = s.core.confl_type) ∧
                      (ovf_o = false →
                        (brk_o = 0#64 →
                          sem_o.core.oom = 0#64 ∧ sem_o.core.confl_type = s.core.confl_type ∧
                          p_o = end_o) ∧
                        (brk_o = 1#64 → PropLitConfl F_cur ignore_ref sem_o.core ∧
                          sem_o.core.oom = 0#64) ∧
                        (brk_o = 0#64 ∨ brk_o = 1#64)) ∧
                      (FullMem c (fastPropMem s_disk sem_o) ⋆ R) mo)
                  ?_ ?_ ?_
                · rintro _ ⟨te_b, un_b, uf_b, tk_b, off_b, p_b, q_b, end_b, brk_b, ovf_b, ⟨⟩⟩ mb
                    ⟨sem_b, hpi_b, hte_b, hun_b, huf_b, _ht0_b, hbr0, hbr1, hbr_cases, hmb⟩
                  exact m7p_compact_post_ovf_wp hChrono hQ
                    (fun sem_next te_mc mc0 hlen_n hw_n htr_n hperm_n hag_n hpr_n hte_n hun_n
                      huf_n hoom_n hct_n hdm_n hcv_n hcl_n hprob_n halen_n hfl_sem_lt hfl_s_lt
                      hfl_le hpr_ge_n htemc_le hpr_temc hsc_n hm_mc =>
                      ih sem_next.core.fuel.toNat
                        (prop_v + 1#64, te_b, un_b, uf_b, tk_b, ()) mc0 hfl_sem_lt
                        ⟨sem_next, te_mc, rfl, hlen_n, hw_n, htr_n, hperm_n, hag_n, hpr_n,
                          hte_n, hun_n, huf_n, hoom_n, hct_n, hdm_n, hcv_n, hcl_n, hprob_n,
                          halen_n, hfl_le, fun _ => hfl_s_lt, (hpr_n ▸ hpr_ge_n), htemc_le,
                          hpr_temc, hsc_n, hm_mc⟩)
                    hwc hmaxv hlen0 hpr_lt rfl ⟨te_mem, rfl, htem_le, hpr_tem⟩
                    htr_o hperm_o hag_o hcv_o hcl_o hprob_o halen_o hsc_o hfl_rem_dec hfuel_le
                    hp1_prop (htend_eq ▸ hp_lt_o) hpr_ge rfl hnot_lt hdm_o hpi_b hte_b hun_b
                    huf_b (fun h => let x := hbr0 h; ⟨x.1, x.2.1⟩) hbr1 hbr_cases hmb
                · rintro Bo Lo rem_o
                      ⟨te_o, un_o, uf_o, tk_o, off_o, p_o, q_o, end_o, brk_o, ovf_o, ⟨⟩⟩
                    mo hBo ih_o ⟨sem_o, rfl, hpi_o, hte_o, hun_o, huf_o, ht0_o, hov_t, hov_f, hmo⟩
                  m7p_hsplit
                  · have hov_t_eq : ovf_o = true := hc
                    have ⟨hbr0_o, hoom_o2, hct_o2⟩ := hov_t hov_t_eq
                    clear hov_t hov_f hc
                    m7p_hsteps_nogrp
                    refine wp_join_group
                      (fun (te_p, un_p, uf_p, tk_p, p_p, q_p, brk_p, ovf_p,
                          ovf_rw_p, ovf_oth_p, ovf_cr_p, ovf_ri_p, ()) mbp =>
                        ∃ sem_p : FullState,
                          PropLitInv c F0 F_cur s_base sem_p not_lit.toNat off_o.toNat
                            q_p.toNat p_p.toNat end_o.toNat ∧
                          p_o.toNat ≤ p_p.toNat ∧ sem_o.core.trail_end ≤ sem_p.core.trail_end ∧
                          te_p.toNat = sem_p.core.trail_end ∧ un_p = sem_p.core.unassigned ∧
                          uf_p = sem_p.core.unflushed ∧ sem_p.core.oom = 0#64 ∧
                          (ovf_p = false →
                            (brk_p = 0#64 → p_p = end_o ∧
                              sem_p.core.confl_type = sem_o.core.confl_type) ∧
                            (brk_p = 1#64 → PropLitConfl F_cur ignore_ref sem_p.core) ∧
                            (brk_p = 0#64 ∨ brk_p = 1#64)) ∧
                          (ovf_p = true →
                            brk_p = 0#64 ∧ sem_p.core.confl_type = sem_o.core.confl_type ∧
                            2 ≤ p_p.toNat - off_o.toNat ∧ q_p.toNat + 2 ≤ p_p.toNat ∧
                            end_o.toNat - p_p.toNat < end_o.toNat - p_o.toNat ∧
                            ovf_cr_p.toNat < 0x80000000 ∧
                            ovf_cr_p.toNat ∈ fullArenaClauseRefsCore sem_p.core ∧
                            ovf_cr_p.toNat + 3 +
                              fullArenaClauseSizeCore sem_p.core ovf_cr_p.toNat ≤
                              sem_p.core.arena_len ∧
                            ovf_oth_p.toNat < 2 * sem_p.core.cur_vars ∧
                            ovf_rw_p.toNat < 2 * sem_p.core.cur_vars ∧
                            ovf_rw_p.toNat ≠ not_lit.toNat ∧
                            2 ≤ ovf_ri_p.toNat ∧
                            ovf_ri_p.toNat < fullArenaClauseSizeCore sem_p.core ovf_cr_p.toNat ∧
                            sem_p.core.arena[ovf_cr_p.toNat + 3]? = some ovf_oth_p ∧
                            sem_p.core.arena[ovf_cr_p.toNat + 4]? = some not_lit ∧
                            sem_p.core.arena[ovf_cr_p.toNat + 3 + ovf_ri_p.toNat]? =
                              some ovf_rw_p) ∧
                          (FullMem c (fastPropMem s_disk sem_p) ⋆ R) mbp) ?_ ?_
                    · rintro _ ⟨te_p, un_p, uf_p, tk_p, p_p, q_p, brk_p, ovf_p,
                          ovf_rw_p, ovf_oth_p, ovf_cr_p, ovf_ri_p, ⟨⟩⟩ mbp
                        ⟨sem_p, hpi_p, _hpo_le_pp, hte_ge_p, hte_p, hun_p, huf_p, hoom_p, hnoov,
                          hov_yes, hmbp⟩
                      have ht0_p :
                          t0_v = 0xFFFFFFFFFFFFFFFF#64 ∨ t0_v.toNat ≤ sem_p.core.trail_end :=
                        ht0_o.imp_right (fun h => Nat.le_trans h hte_ge_p)
                      dsimp only [Blocks.get]
                      change wp Γ _ _ (m7pPostLpOvfExpr c _ off_o end_o Bo Lo
                        te_p un_p uf_p tk_p p_p q_p brk_p ovf_p
                        ovf_rw_p ovf_oth_p ovf_cr_p ovf_ri_p) mbp
                      exact m7p_post_lp_ovf_wp hOvf hBo
                        (fun n' xs m hlt => ih_o n' xs m
                          (by simpa only [hov_t_eq, ↓reduceIte] using hlt))
                        har hwc hsd_len
                        (by dsimp only [s_disk, s_base]; rw [hpi_p.cur_vars_eq, hcv_o])
                        (by simp [s_disk, s_base, hpi_p.ag.get FullCoreState.propagated])
                        (hpi_p.cur_vars_eq.symm ▸ hnot_lt)
                        hnl64_idx hct_o2 ht0_p
                        (by
                          simp only [not_lit, lit, fastPropMem_trl, fc_getElem_trl,
                            sem_d, BitVec.ofNat_eq_ofNat])
                        hpi_p _hpo_le_pp hte_p hun_p huf_p hoom_p hnoov hov_yes hmbp
                    · intro J_ovf hJ_ovf
                      have hnot_o : not_lit.toNat < 2 * sem_o.core.cur_vars :=
                        hpi_o.cur_vars_eq.symm ▸ hnot_lt
                      have hcl32_o : sem_o.core.cur_level < 2 ^ 32 := by
                        rw [hpi_o.ag.get FullCoreState.cur_level]
                        change sem.core.cur_level < 2 ^ 32
                        rw [hcl_o]; exact hclv_lt32
                      refine m7_lp_loop_wp c.hmaxv c.harena c.hwcap hpi_o hnot_o
                        (by
                          rw [hpi_o.cur_vars_eq]; dsimp only [s_base]; rw [hcv_o]
                          simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
                          rw [Nat.mod_eq_of_lt hcv_lt64,
                            show (OfNat.ofNat 1 : Nat) = 1 from rfl,
                            Nat.shiftLeft_eq, Nat.pow_one,
                            Nat.mul_comm s.core.cur_vars 2, Nat.mod_eq_of_lt h2cv_lt64])
                        (by
                          apply BitVec.eq_of_toNat_eq
                          rw [hpi_o.ag.get FullCoreState.cur_level]; dsimp only [s_base]
                          rw [hcl_o]
                          simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
                            Nat.mod_eq_of_lt hclv_lt32, Nat.mod_eq_of_lt hclv_lt64])
                        hcl32_o hte_o hun_o huf_o hoom_o2 hbr0_o hmo ?_
                      intro sem' te' un' uf' tk' p' q' brk' ovf' ovf_rw' ovf_oth' ovf_cr'
                        ovf_ri' m' hpi' hp' hte_ge' hte' hun' huf' hoom' hno' hyes' hm'
                      m7p_hsteps
                      exact hJ_ovf _ m' ⟨sem', hpi', hp', hte_ge', hte', hun', huf', hoom',
                        hno', hyes', hm'⟩
                  · have hov_f_eq : ovf_o = false := by revert hc; cases ovf_o <;> simp
                    have ⟨h0, h1, hcs⟩ := hov_f hov_f_eq
                    exact hBo _ mo ⟨sem_o, hpi_o, hte_o, hun_o, huf_o, ht0_o, h0, h1,
                      hcs.elim Or.inl (fun h => Or.inr (Or.inl h)), hmo⟩
                · intro Bo Lo hBo hLo
                  m7p_hsteps
                  have hsz_trl : ∀ (trl : List (BitVec 32)) (htrl : trl = sem.core.trl) pf1 pf2,
                      (sem.core.wvec[((BitVec.setWidth 64
                          (trl[prop_v.toNat]'pf1 ^^^ (1 : BitVec 32))
                        <<< (1 : Nat)) + (1 : BitVec 64)).toNat]'pf2).setWidth 64 =
                      BitVec.ofNat 64 (fullWatchSizeCore s_base.core not_lit.toNat) := by
                    intro trl htrl pf1 pf2
                    have h1 : trl[prop_v.toNat]'pf1 = lit := by
                      subst htrl
                      exact (fc_getElem_eq_of_idx rfl pf1 hp_sem_lt_trl).trans
                        (by simp only [lit, fc_getElem_trl, sem_d])
                    have hidx := m7_shl1_add1_eq_of_trl rfl pf1 pf1 h1
                    have hget : (sem.core.wvec[((BitVec.setWidth 64
                        (trl[prop_v.toNat]'pf1 ^^^ (1 : BitVec 32)) <<< (1 : Nat)) +
                        (1 : BitVec 64)).toNat]'pf2).setWidth 64 =
                        (sem.core.wvec[((not_lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat]'
                          hnl64_1_lt_wv0).setWidth 64 := by
                      congr 1; exact fc_getElem_eq_of_idx (hidx.trans hnl64_1_idx.symm) pf2
                        hnl64_1_lt_wv0
                    rw [hget]; apply BitVec.eq_of_toNat_eq
                    rw [hsz0_nat, m7_bv64_ofNat_toNat_lt (by
                      have := hpi0.end_lt_wcap hnot_lt; omega)]
                  have hoff_trl : ∀ (trl : List (BitVec 32)) (htrl : trl = sem.core.trl) pf1 pf2,
                      (sem.core.wvec[(BitVec.setWidth 64 (trl[prop_v.toNat]'pf1 ^^^ (1 : BitVec 32))
                        <<< (1 : Nat)).toNat]'pf2).setWidth 64 =
                      BitVec.ofNat 64 (fullWatchOffCore s_base.core not_lit.toNat) := by
                    intro trl htrl pf1 pf2
                    have h1 : trl[prop_v.toNat]'pf1 = lit := by
                      subst htrl
                      exact (fc_getElem_eq_of_idx rfl pf1 hp_sem_lt_trl).trans
                        (by simp only [lit, fc_getElem_trl, sem_d])
                    have hidx := m7_shl1_eq_of_trl rfl pf1 pf1 h1
                    have hget : (sem.core.wvec[(BitVec.setWidth 64
                        (trl[prop_v.toNat]'pf1 ^^^ (1 : BitVec 32)) <<< (1 : Nat)).toNat]'
                        pf2).setWidth 64 =
                        (sem.core.wvec[(not_lit.setWidth 64 <<< (1 : Nat)).toNat]'
                          hnl64_lt_wv0).setWidth 64 := by
                      congr 1; exact fc_getElem_eq_of_idx (hidx.trans hnl64_idx.symm) pf2
                        hnl64_lt_wv0
                    rw [hget]; apply BitVec.eq_of_toNat_eq
                    rw [hoff0_nat, m7_bv64_ofNat_toNat_lt (by
                      have := hpi0.end_lt_wcap hnot_lt; omega)]
                  have hoff0_lt64 : fullWatchOffCore s_base.core not_lit.toNat < 2 ^ 64 :=
                    Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hend0_lt64
                  have hsz0_lt64 : fullWatchSizeCore s_base.core not_lit.toNat < 2 ^ 64 :=
                    Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hend0_lt64
                  have hof0_eq := m7_bv64_ofNat_toNat_lt hoff0_lt64
                  have hsz0_eq := m7_bv64_ofNat_toNat_lt hsz0_lt64
                  have hadd0_eq : (BitVec.ofNat 64 (fullWatchOffCore s_base.core not_lit.toNat) +
                      BitVec.ofNat 64 (fullWatchSizeCore s_base.core not_lit.toNat)).toNat =
                      fullWatchOffCore s_base.core not_lit.toNat +
                      fullWatchSizeCore s_base.core not_lit.toNat := by
                    rw [BitVec.toNat_add, hof0_eq, hsz0_eq, Nat.mod_eq_of_lt hend0_lt64]
                  simp only [fastPropMem_wvec]
                  refine hLo (fullWatchSizeCore s_base.core not_lit.toNat + 1) _ mt ?_
                  refine ⟨s_base, ?_, ?_, htend_eq.symm, hunass_eq.symm, hunfl_eq.symm,
                    ht0_bound, fun _ => ⟨rfl, hoom_o, hct_o⟩,
                    fun h => absurd h (by decide), hm_t⟩
                  · dsimp only [fastPropMem]
                    erw [hoff_trl sem.core.trl rfl _ _, hsz_trl sem.core.trl rfl _ _]
                    rw [hadd0_eq, hof0_eq]
                    simp only [↓reduceIte]
                    exact congrArg (· + 1)
                      (Nat.add_sub_cancel_left (fullWatchOffCore s_base.core not_lit.toNat)
                        (fullWatchSizeCore s_base.core not_lit.toNat)).symm
                  · dsimp only [fastPropMem]
                    erw [hoff_trl sem.core.trl rfl _ _, hsz_trl sem.core.trl rfl _ _]
                    rw [hof0_eq, hadd0_eq]
                    exact hpi0
              · intro Jt0 hJt0
                m7p_hsplit
                · have hlit_div :
                      (((FullState.mk (fastPropMem s_disk sem_d).core
                        (fastPropMem s_disk sem_d).scratch).core.trl[prop_v.toNat]'hp_lt_trl >>>
                        (1 : Nat)).setWidth 64).toNat = lit.toNat / 2 := by
                    change ((lit >>> (1 : Nat)).setWidth 64).toNat = lit.toNat / 2
                    rw [bv_c0_zext32_64, bv32_lshr_1]
                  have hlvl_l : (fastPropMem s_disk s_base).core.lvl.length = c.max_vars := by
                    rw [fastPropMem_lvl]; exact hbase_len.core_ok.lvl_len
                  ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _));
                    c0_hfast)
                  · exact hJt0 (tend_v, ()) m ⟨hm_base, Or.inr (htend_eq ▸ Nat.le_refl _)⟩
                  · exact hJt0 (0xFFFFFFFFFFFFFFFF#64, ()) m ⟨hm_base, Or.inl rfl⟩
                  · have hc' : ¬ lit.toNat < 2 * sem.core.cur_vars := by
                      have hc0 := hc
                      simp only [fastPropMem_trl] at hc0
                      rw [Nat.mod_eq_of_lt hcv_lt64, Nat.mod_eq_of_lt h2cv_lt64, ← hcv_o] at hc0
                      have hlt_eq : sem.core.trl[prop_v.toNat]'hp_sem_lt_trl = lit := by
                        simp only [lit, fc_getElem_trl, sem_d]
                      simpa only [hlt_eq] using hc0
                    exact absurd hlit_lt hc'
                · m7p_hsteps; exact hJt0 (0xFFFFFFFFFFFFFFFF#64, ()) m ⟨hm_base, Or.inl rfl⟩
        · have hpe_o : sem.core.propagated = sem.core.trail_end := by
            have hh : tend_v.toNat ≤ prop_v.toNat := Nat.le_of_not_lt hc
            rw [← htend_eq, ← hprop_eq] at hh
            exact Nat.le_antisymm hlen_o.core_ok.propagated_le hh
          have hprop_gt : s.core.propagated < prop_v.toNat := by
            rw [← hprop_eq, hpe_o]
            exact Nat.lt_of_lt_of_le hpr_lt htr_o.te_ge
          have hfuel_dec := hfuel_lt hprop_gt
          clear ih
          m7p_hsteps
          exact m7p_outer_flush_ret (ticks' := s.scratch.search_ticks + ticks_v)
            hQ hlen_o hw_o htr_o hperm_o hag_o hsc_o
            hprop_eq htend_eq hunass_eq hunfl_eq hfuel_le hpr_lt
            (Or.inl rfl)
            (fun _ => ⟨hprop_eq ▸ htend_eq ▸ hpe_o, hct_o, fun _ => hoom_o,
              fun _ => hfuel_dec⟩)
            (by decide) (fun h => absurd h (by decide))
            (by
              simpa only [fastPropMem, s_disk, sem_d, hprop_eq, htend_eq,
                hunass_eq, hunfl_eq] using hm)
      · intro J hJ
        exact hJ s.core.fuel.toNat (BitVec.ofNat 64 s.core.propagated,
            BitVec.ofNat 64 s.core.trail_end, s.core.unassigned, s.core.unflushed, 0#64, ()) m
          ⟨s, s.core.trail_end, rfl, hlen0, hw0, .refl _, .refl _, .refl _ _,
            (m7_bv64_ofNat_toNat_lt hpr0_lt64).symm, (m7_bv64_ofNat_toNat_lt hte0_lt64).symm,
            rfl, rfl, hoom0, rfl, hdense0, rfl, rfl, rfl, rfl, Nat.le_refl _,
            fun hlt => absurd (m7_bv64_ofNat_toNat_lt hpr0_lt64 ▸ hlt) (Nat.lt_irrefl _),
            by rw [m7_bv64_ofNat_toNat_lt hpr0_lt64]; exact Nat.le_refl _,
            Nat.le_refl _, hlen0.core_ok.propagated_le,
            rfl, by simpa only [fastPropMem_self] using hm0⟩

end PropHotSection

/-! ## 3. `full_vivify_tier_m6_hdr` & `full_vivify_m6_hdr` (`FullMem`-Only `search_ticks`) -/

section VivifySection

private theorem sparse_with_tr {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) {tr' : List (BitVec 32)} (htr : tr'.length = 2 * c.max_vars) :
    FullSparseInv c F0 { s with scratch := { s.scratch with tarjan_reach := tr' } } :=
  ⟨⟨⟨h.1.lengths.core_ok, { h.1.lengths.scratch_ok with tarjan_reach_len := htr }⟩, h.1.witness⟩,
    h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

private theorem sparse_with_rr {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) {rr' : List (BitVec 32)} (hrr : rr'.length = c.red_cap) :
    FullSparseInv c F0 { s with scratch := { s.scratch with red_refs := rr' } } :=
  ⟨⟨⟨h.1.lengths.core_ok, { h.1.lengths.scratch_ok with red_refs_len := hrr }⟩, h.1.witness⟩,
    h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

private theorem sparseInvW_of_prop_canon {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    {vals' : List (BitVec 8)} {flags' lvl' rsns' trl' tp' : List (BitVec 32)}
    {te' prop' : Nat} {unass' unfl' : BitVec 64} {wvec' arena' wstk' : List (BitVec 32)}
    {wlen' : Nat} {wu' fuel' ctype' cref' c0' c1' oom' ticks' : BitVec 64}
    {wsort' : List (BitVec 32)} {phases' : List (BitVec 8)} {delayed' : List (BitVec 32)}
    (hlen' : ({ s with
      core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                            trl := trl', trail_pos := tp', trail_end := te', propagated := prop',
                            unassigned := unass', unflushed := unfl', wvec := wvec',
                            arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
                            fuel := fuel', confl_type := ctype', confl_ref := cref',
                            confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
      scratch := { s.scratch with search_ticks := ticks', wsort := wsort', phases := phases',
                                  delayed := delayed' } } :
      FullState).LengthsOk c)
    (hw' : FullWitnessInv c F0 F_cur
      { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
                    trail_pos := tp', trail_end := te', propagated := prop',
                    unassigned := unass', unflushed := unfl', wvec := wvec', arena := arena',
                    wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
                    confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
                    confl_lit1 := c1', oom := oom' })
    (hperm : FullArenaPermEq s.core
      { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
                    trail_pos := tp', trail_end := te', propagated := prop',
                    unassigned := unass', unflushed := unfl', wvec := wvec', arena := arena',
                    wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
                    confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
                    confl_lit1 := c1', oom := oom' }) :
    FullSparseInvW c F0 F_cur
      { s with
        core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                              trl := trl', trail_pos := tp', trail_end := te', propagated := prop',
                              unassigned := unass', unflushed := unfl', wvec := wvec',
                              arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
                              fuel := fuel', confl_type := ctype', confl_ref := cref',
                              confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
        scratch := { s.scratch with
          search_ticks := ticks', wsort := wsort', phases := phases', delayed := delayed' } } := by
  let s' : FullState :=
    { s with
      core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                            trl := trl', trail_pos := tp', trail_end := te', propagated := prop',
                            unassigned := unass', unflushed := unfl', wvec := wvec',
                            arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
                            fuel := fuel', confl_type := ctype', confl_ref := cref',
                            confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
      scratch := { s.scratch with search_ticks := ticks', wsort := wsort', phases := phases',
                                  delayed := delayed' } }
  have hnd' : FullArenaVarsNodup s' := fun ref href hng => by
    have href0 : ref ∈ fullArenaClauseRefsCore s.core := hperm.2.1 ▸ href
    obtain ⟨_, hgb, hp⟩ := hperm.2.2 ref href0
    exact (hp.map (· / 2)).nodup_iff.mpr (hsp.2.2.2.1 ref href0 (hgb.symm.trans hng))
  have hrefs : ∀ ref ∈ fullArenaClauseRefs s, ref ∈ fullArenaClauseRefs s' := fun ref hr => by
    change ref ∈ fullArenaClauseRefsCore s'.core; rw [hperm.2.1]; exact hr
  exact FullVivTop.fullSparseInvW_of_prop_state hsp hlen' hw' hnd'
    ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hrefs

private theorem fullSparseInv_of_core_eq_m6 {c : FullCfg} {F0 : CNF Nat}
    {s s' : FullState} (h : FullSparseInv c F0 s)
    (hlen' : s'.LengthsOk c) (hcore : s'.core = s.core)
    (hpres : FullM6Hdr.M6HdrScratchPres s s') : FullSparseInv c F0 s' := by
  obtain ⟨hcore_inv, hmc, hvn, hsc, hdm⟩ := h
  refine ⟨⟨hlen', ?_⟩, ?_, ?_, ?_, ?_⟩
  · obtain ⟨F_cur, hw⟩ := hcore_inv.2
    exact ⟨F_cur, by rw [hcore]; exact hw⟩
  · unfold FullLitMarksClear FullMrkZero; rw [hcore]; exact hmc
  · unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseGarb fullArenaClauseLits
    rw [hcore]; exact hvn
  · exact FullExtScratchOk.of_pres hsc hpres.extPres fun r hr => by
      unfold fullArenaClauseRefs; rwa [hcore]
  · rw [hcore]; exact hdm

private theorem fullSparseInv_with_ticks {c : FullCfg} {F0 : CNF Nat}
    {s : FullState} (h : FullSparseInv c F0 s) (st : BitVec 64) :
    FullSparseInv c F0 { s with scratch := { s.scratch with search_ticks := st } } :=
  fullSparseInv_of_core_eq_m6 h (h.1.lengths.with_scratch { h.1.lengths.scratch_ok with }) rfl
    (FullM6Hdr.M6HdrScratchPres.of_ticks st)

/-- `full_vivify_tier_m6_hdr` satisfies exact `FullM6OrchAdapters.m6aVivifyTierSpec` over `FullMem`
using direct `h->search_ticks < tick_lim` gating without synthetic `spent`. -/
theorem full_vivify_tier_m6_hdr_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hCollect : ∀ a m Q X, FullM6VivBackbone.fullVivCollectM6Spec a m Q X →
      Γ "full_viv_collect_m6" [i64, i64] [i64] a m Q X)
    (hCount : ∀ a m Q X, FullM6VivBackbone.fullVivCountM6Spec a m Q X →
      Γ "full_viv_count_m6" [i64, i64] [] a m Q X)
    (hKeys : ∀ a m Q X, FullM6VivBackbone.fullVivKeysM6Spec a m Q X →
      Γ "full_viv_keys_m6" [i64, i64] [] a m Q X)
    (hSortSched : ∀ a m Q X, FullM6VivBackbone.fullVivSortSchedM6Spec a m Q X →
      Γ "full_viv_sort_sched_m6" [i64, i64] [] a m Q X)
    (hVivClause : ∀ a m Q X, FullM6VivBackbone.fullVivClauseM6Spec a m Q X →
      Γ "full_viv_clause_m6" [i64, i32] [i64] a m Q X)
    (hProp : ∀ a m Q X, FullM6BcpS15.fullBcpS15Spec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hClearTier : ∀ a m Q X, FullM6VivBackbone.fullVivClearTierM6Spec a m Q X →
      Γ "full_viv_clear_tier_m6" [i64, i64] [] a m Q X) :
    ∀ a m Q X, FullM6OrchAdapters.m6aVivifyTierSpec a m Q X →
      Func.wp Γ full_vivify_tier_m6_hdr_body a m Q X := by
  rintro ⟨h, tier_mode, budget0, tick_lim, ⟨⟩⟩ m0 Q X hs
  obtain ⟨c, F0, s, R, rfl, hsp0, hm0, hQ⟩ := FullM6OrchAdapters.m6aVivifyTierSpec_elim hs
  have har_cap := c.harena; have hmx := c.hmaxv; have hrc := c.hred
  unfold LratBytes.dimacsBound at har_cap hmx hrc
  have hmaxv : c.max_vars < 2 * 2 ^ 28 := hmx
  unfold Func.wp full_vivify_tier_m6_hdr_body; fvt_to_group
  · fvt_steps
    exact hQ 1#64 s m0 hsp0 (fun h => h) (fun h => h) (fun hb => absurd (by c0_bound) hb)
      (Nat.le_refl _) (Or.inl rfl) (fun h => by cases h) hm0
  refine wp_join_group (ts := [])
    (fun () m1 => ∃ s1 : FullState, FullSparseInv c F0 s1 ∧ s1.core.cur_level = 0 ∧
      s1.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s1 ⋆ R) m1) ?_ ?_
  · rintro _ ⟨⟩ m ⟨s1, hsp1, hcl1, hfl1, hm⟩
    fvt_steps
    let s2 : FullState := { s1 with core := { s1.core with probing := 1#64 } }
    have hsp2 : FullSparseInv c F0 s2 := FullVivTop.FullSparseInv.with_probing hsp1 1#64
    have hm2 : (FullMem c s2 ⋆ R) m := hm
    have hfl2 : s2.core.fuel.toNat ≤ s.core.fuel.toNat := hfl1
    clear_value s2
    clear hsp1 hcl1 hfl1
    c0_call hCollect
    refine ⟨c, F0, s2, R, rfl, hsp2, hm2, fun bn rr3 m3 h3bn hrr3 hok3 hm3 => ?_⟩
    let s3 : FullState := { s2 with scratch := { s2.scratch with red_refs := rr3 } }
    have hsp3 : FullSparseInv c F0 s3 := sparse_with_rr hsp2 hrr3
    c0_call hCount
    refine ⟨c, F0, s3, R, rfl, hsp3, h3bn, hok3, hm3, fun tr3 m3c htr3 hm3c => ?_⟩
    let s3c : FullState := { s3 with scratch := { s3.scratch with tarjan_reach := tr3 } }
    have hsp3c : FullSparseInv c F0 s3c := sparse_with_tr hsp3 htr3
    c0_call hKeys
    refine ⟨c, F0, s3c, R, rfl, hsp3c, h3bn, hok3, hm3c, fun rr4 m4 hrr4 hok4 hm4 => ?_⟩
    let s4 : FullState := { s3c with scratch := { s3c.scratch with red_refs := rr4 } }
    have hsp4 : FullSparseInv c F0 s4 := sparse_with_rr hsp3c hrr4
    c0_call hSortSched
    refine ⟨c, F0, s4, R, rfl, hsp4, h3bn, hok4, hm4,
      fun rr5 m5 hrr5_len hok5 hm5 => ?_⟩
    let s5 : FullState := { s4 with scratch := { s4.scratch with red_refs := rr5 } }
    have hsp5 : FullSparseInv c F0 s5 := sparse_with_rr hsp4 hrr5_len
    have hfl5 : s5.core.fuel.toNat ≤ s.core.fuel.toNat := hfl2
    have hrefs5 : fullArenaClauseRefs s5 = fullArenaClauseRefs s2 := rfl
    have hrr5 : s5.scratch.red_refs = rr5 := rfl
    have hok5' : ∀ k < bn.toNat, (rr5[3 * k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s2 := hok5
    have hm5' : (FullMem c s5 ⋆ R) m5 := hm5
    clear_value s5 s4 s3c s3
    clear s4 s3c s3 hsp4 hsp3c hsp3 tr3 rr3 rr4 htr3 hrr3 hrr4 hok3 hok4 hok5
      hm3 hm3c hm4 hm5 hsp2 hm2 hfl2 hCollect hCount hKeys hSortSched
    c0_hsteps_nogrp
    refine wp_loop_break_group (brkTs := [i64, i64, i64]) (lpTs := [i64, i64])
      (fun (_budget_b, res_b, bi_b, ()) mb => ∃ sb : FullState,
        FullSparseInv c F0 sb ∧ sb.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        (res_b = 1#64 ∨ res_b = 20#64) ∧ (res_b = 20#64 → F0.Unsat) ∧
        (FullMem c sb ⋆ R) mb)
      (fun rem (budget, bi, ()) mvi => ∃ svi : FullState,
        bi.toNat ≤ bn.toNat ∧ rem = bn.toNat - bi.toNat ∧
        FullSparseInv c F0 svi ∧ svi.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        fullArenaClauseRefs svi = fullArenaClauseRefs s2 ∧
        svi.scratch.red_refs = rr5 ∧ (FullMem c svi ⋆ R) mvi)
      ?_ ?_ ?_
    · rintro _ ⟨_, res_b, bi_b, ⟨⟩⟩ mb ⟨sb, hspb, hflb, hresb, h20b, hmb⟩
      refine wp_join_group (ts := [])
        (fun () m_bt => ∃ sbt : FullState,
          FullSparseInv c F0 sbt ∧ sbt.core.cur_level = 0 ∧
          sbt.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c sbt ⋆ R) m_bt) ?_ ?_
      · rintro _ ⟨⟩ m_bt ⟨sbt, hspbt, hclbt, hflbt, hm_bt⟩
        refine wp_join_group (ts := [])
          (fun () m_w => ∃ sw : FullState,
            FullSparseInv c F0 sw ∧ sw.core.cur_level = 0 ∧
            sw.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c sw ⋆ R) m_w) ?_ ?_
        · rintro _ ⟨⟩ m_w ⟨sw, hspw, hclw, hflw, hm_w⟩
          fvt_steps
          let sf : FullState := { sw with core := { sw.core with probing := 0#64 } }
          have hspf : FullSparseInv c F0 sf := FullVivTop.FullSparseInv.with_probing hspw 0#64
          exact hQ res_b sf _ hspf (fun _ => hclw) (fun _ => rfl)
            (fun _ => ⟨hclw, rfl⟩) hflw hresb h20b hm
        · intro Jw hJw
          fvt_steps
          · c0_call hClearTier
            refine ⟨c, F0, sbt, R, rfl, hspbt, hclbt, hm_bt,
              fun sw m_w hspw hclw hflw hm_w =>
                hJw () m_w ⟨sw, hspw, hclw, by rw [hflw]; exact hflbt, hm_w⟩⟩
          · exact hJw () m_bt ⟨sbt, hspbt, hclbt, hflbt, hm_bt⟩
          · exact hJw () m_bt ⟨sbt, hspbt, hclbt, hflbt, hm_bt⟩
          · exact hJw () m_bt ⟨sbt, hspbt, hclbt, hflbt, hm_bt⟩
      · intro Jbt hJbt
        obtain ⟨F_curb, hswb⟩ := hspb.exists_witness
        have hclb_lt : sb.core.cur_level < 2 ^ 64 := by
          have := hswb.2.1.cur_level_le; have := hspb.1.lengths.core_ok.trail_end_le
          have := hspb.1.lengths.core_ok.cur_vars_le; omega
        fvt_steps
        · c0_call hBacktrack
          refine ⟨c, sb, R, rfl, hspb.1.lengths, hclb_lt,
            (by intro _
                have := hswb.2.1.cur_level_le; have := hspb.1.lengths.core_ok.trail_end_le
                have := hspb.1.lengths.core_ok.cur_vars_le; omega),
            hswb.2.1.trail_lits_lt, hmb,
            fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m_bt
              hlen_bt _ _ hcl_bt hpres_bt _ _ _ hw_bt _ hm_bt => ?_⟩
          have hsp_bt : FullSparseInv c F0 _ :=
            FullVivTop.FullSparseInv.of_backtrack hspb (Nat.zero_le _) hlen_bt hpres_bt
              (by simpa using hw_bt F0)
          exact hJbt () m_bt ⟨_, hsp_bt, by rw [hcl_bt]; simp, hflb, hm_bt⟩
        · have hclb0 : sb.core.cur_level = 0 := by
            have h0 : (BitVec.ofNat 64 sb.core.cur_level).toNat = 0 := by rw [hc]; rfl
            rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hclb_lt] at h0
          exact hJbt () mb ⟨sb, hspb, hclb0, hflb, hmb⟩
    · intro B L rem ⟨budget, bi, ⟨⟩⟩ mvi hB hL
        ⟨svi, hbi_le, hrem, hspv, hflv, hrefsv, hrrv, hmvi⟩
      subst hrem
      fvt_steps
      · have hbi_lt : bi.toNat < bn.toNat := by c0_bound
        have hbi3_nat : (bi * 3).toNat = 3 * bi.toNat := by bv_omega
        have hbi3_lt : (bi * 3).toNat < svi.scratch.red_refs.length := by
          rw [hrrv, hrr5_len]; omega
        let cr := svi.scratch.red_refs[(bi * 3).toNat]'hbi3_lt
        have hcr_ref : cr.toNat ∈ fullArenaClauseRefs svi := by
          rw [hrefsv]
          have h := hok5' bi.toNat hbi_lt
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h
          have heq : cr = rr5[3 * bi.toNat]'(by omega) := Option.some.inj (by
            rw [← List.getElem?_eq_getElem hbi3_lt, hrrv, hbi3_nat,
              List.getElem?_eq_getElem (by omega)])
          rwa [heq]
        obtain ⟨F_curv, hswv⟩ := hspv.exists_witness
        have hbi1 : (bi + 1#64).toNat = bi.toNat + 1 := by bv_omega
        fvt_steps
        c0_call hVivClause
        refine ⟨c, F0, F_curv, svi, R, rfl, hswv, hcr_ref, hmvi,
          fun vc s_vc m_vc hsw_vc hfl_vc _ hrefs_vc hrr_vc hvc h20_vc hm_vc => ?_⟩
        have hrefs_vc2 : fullArenaClauseRefs s_vc = fullArenaClauseRefs s2 :=
          hrefs_vc.trans hrefsv
        have hrr_vc5 : s_vc.scratch.red_refs = rr5 := hrr_vc.trans hrrv
        have hfl_vc' : s_vc.core.fuel.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfl_vc hflv
        fvt_steps
        · exact hB (budget - 1#64, 20#64, bi, ()) m_vc
            ⟨s_vc, hsw_vc.toSparse, hfl_vc', Or.inr rfl, fun _ => h20_vc (by c0_bound), hm_vc⟩
        · exact hB (budget - 1#64, 1#64, bi, ()) m_vc
            ⟨s_vc, hsw_vc.toSparse, hfl_vc', Or.inl rfl, (fun h => by cases h), hm_vc⟩
        · have hcl_vc_lt : s_vc.core.cur_level < 2 ^ 64 := by
            have := hsw_vc.2.1.cur_level_le; have := hsw_vc.1.core_ok.trail_end_le
            have := hsw_vc.1.core_ok.cur_vars_le; omega
          have hcl_vc0 : s_vc.core.cur_level = 0 := by
            have h0 : (BitVec.ofNat 64 s_vc.core.cur_level).toNat = 0 := by
              have hc0 : BitVec.ofNat 64 s_vc.core.cur_level = 0#64 := by c0_bound
              rw [hc0]; rfl
            rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcl_vc_lt] at h0
          c0_call hProp
          refine ⟨c, F0, F_curv, s_vc, R, rfl, hsw_vc.1, hsw_vc.2.1, hsw_vc.2.2.2.2.2, hm_vc,
            fun pr vals_p flags_p lvl_p rsns_p trl_p tp_p te_p prop_p unass_p unfl_p
              wvec_p arena_p wstk_p wlen_p wu_p fuel_p ctype_p cref_p c0_p c1_p oom_p
              ticks_p wsort_p phases_p delayed_p m_p hlen_p hw_p _ hperm_p _ hfl_p _ _ hpr1 _ _
              hm_p => ?_⟩
          let s_p : FullState :=
            { s_vc with
              core := { s_vc.core with
                vals := vals_p, flags := flags_p, lvl := lvl_p, rsns := rsns_p,
                trl := trl_p, trail_pos := tp_p, trail_end := te_p, propagated := prop_p,
                unassigned := unass_p, unflushed := unfl_p, wvec := wvec_p,
                arena := arena_p, wstk := wstk_p, wlen := wlen_p, wusable := wu_p,
                fuel := fuel_p, confl_type := ctype_p, confl_ref := cref_p,
                confl_lit0 := c0_p, confl_lit1 := c1_p, oom := oom_p }
              scratch := { s_vc.scratch with
                search_ticks := ticks_p, wsort := wsort_p, phases := phases_p,
                delayed := delayed_p } }
          have hsw_p : FullSparseInvW c F0 F_curv s_p :=
            sparseInvW_of_prop_canon hsw_vc hlen_p hw_p hperm_p
          have hrefs_p : fullArenaClauseRefs s_p = fullArenaClauseRefs s_vc := hperm_p.2.1
          have hfl_p' : s_p.core.fuel.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfl_p hfl_vc'
          fvt_steps
          · have hpr_eq1 : pr = 1#64 := by c0_bound
            have hunsat : F0.Unsat :=
              FullVivTopSpecs.level0_unsat_of_conflict_okW hw_p hcl_vc0 (hpr1 hpr_eq1).2.2
            exact hB (budget - 1#64, 20#64, bi, ()) m_p
              ⟨s_p, hsw_p.toSparse, hfl_p', Or.inr rfl, fun _ => hunsat, hm_p⟩
          · exact hL (bn.toNat - (bi + 1#64).toNat) (budget - 1#64, bi + 1#64, ()) m_p
              (by rw [hbi1]; omega)
              ⟨s_p, by rw [hbi1]; omega, rfl, hsw_p.toSparse, hfl_p',
                hrefs_p.trans hrefs_vc2, hrr_vc5, hm_p⟩
        · exact hL (bn.toNat - (bi + 1#64).toNat) (budget - 1#64, bi + 1#64, ()) m_vc
            (by rw [hbi1]; omega)
            ⟨s_vc, by rw [hbi1]; omega, rfl, hsw_vc.toSparse, hfl_vc', hrefs_vc2, hrr_vc5, hm_vc⟩
      · exact hB (budget, 1#64, bi, ()) mvi
          ⟨svi, hspv, hflv, Or.inl rfl, (fun h => by cases h), hmvi⟩
      · exact hB (budget, 1#64, bi, ()) mvi
          ⟨svi, hspv, hflv, Or.inl rfl, (fun h => by cases h), hmvi⟩
      · exact hB (budget, 1#64, bi, ()) mvi
          ⟨svi, hspv, hflv, Or.inl rfl, (fun h => by cases h), hmvi⟩
      · exact hB (budget, 1#64, bi, ()) mvi
          ⟨svi, hspv, hflv, Or.inl rfl, (fun h => by cases h), hmvi⟩
      · exact hB (budget, 1#64, bi, ()) mvi
          ⟨svi, hspv, hflv, Or.inl rfl, (fun h => by cases h), hmvi⟩
    · intro B L _ hL; fvt_steps
      exact hL bn.toNat (budget0, 0#64, ()) m5
        ⟨s5, Nat.zero_le _, by simp, hsp5, hfl5, hrefs5, hrr5, hm5'⟩
  · intro Jc hJc
    obtain ⟨F_cur0, hsw0⟩ := hsp0.exists_witness
    have hcl0_lt : s.core.cur_level < 2 ^ 64 := by
      have := hsw0.2.1.cur_level_le; have := hsp0.1.lengths.core_ok.trail_end_le
      have := hsp0.1.lengths.core_ok.cur_vars_le; omega
    fvt_steps
    · c0_call hBacktrack
      refine ⟨c, s, R, rfl, hsp0.1.lengths, hcl0_lt,
        (by intro _
            have := hsw0.2.1.cur_level_le; have := hsp0.1.lengths.core_ok.trail_end_le
            have := hsp0.1.lengths.core_ok.cur_vars_le; omega),
        hsw0.2.1.trail_lits_lt, hm0,
        fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m1
          hlen1 _ _ hcl1 hpres1 _ _ _ hw_bt _ hm1 => ?_⟩
      have hsp1 : FullSparseInv c F0 _ :=
        FullVivTop.FullSparseInv.of_backtrack hsp0 (Nat.zero_le _) hlen1 hpres1
          (by simpa using hw_bt F0)
      exact hJc () m1 ⟨_, hsp1, by rw [hcl1]; simp, Nat.le_refl _, hm1⟩
    · have hcl0 : s.core.cur_level = 0 := by
        have h0 : (BitVec.ofNat 64 s.core.cur_level).toNat = 0 := by rw [hc]; rfl
        rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcl0_lt] at h0
      exact hJc () m0 ⟨s, hsp0, hcl0, Nat.le_refl _, hm0⟩

/-- `full_vivify_m6_hdr` satisfies exact `FullM6OrchAdapters.m6aVivifySpec` with saved/restored
`start = h->search_ticks`, `tier1 >= tier2` merge, and saturating carry-over across tiers
`1, 2, 3, 0`. -/
theorem full_vivify_m6_hdr_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hSync : ∀ a m Q X, FullM6Hdr.m6HdrW2aSpec [] [] a m Q X →
      Γ "m6_hdr_sync_legacy_tiers" [i64] [] a m Q X)
    (hGetWm : ∀ a m Q X, FullM6Hdr.m6HdrW2aSpec [i64] [i64] a m Q X →
      Γ "m6_hdr_get_watermark" [i64, i64] [i64] a m Q X)
    (hVivTier : ∀ a m Q X, FullM6OrchAdapters.m6aVivifyTierSpec a m Q X →
      Γ "full_vivify_tier_m6_hdr" [i64, i64, i64, i64] [i64] a m Q X) :
    ∀ a m Q X, FullM6OrchAdapters.m6aVivifySpec a m Q X →
      Func.wp Γ full_vivify_m6_hdr_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  obtain ⟨c, F0, ext, s, R, rfl, hcfg, hext, hsp, hm, hQ⟩ :=
    FullM6OrchAdapters.m6aVivifySpec_elim hs
  have har_cap := c.harena; have hmx := c.hmaxv; have hrc := c.hred
  unfold LratBytes.dimacsBound at har_cap hmx hrc
  have hmaxv : c.max_vars < 2 * 2 ^ 28 := hmx
  have hspw0 := hsp
  obtain ⟨F_cur, hw0⟩ := hspw0.1.witness
  have hco0 := hspw0.1.lengths.core_ok
  have hclv_lt : s.core.cur_level < 2 ^ 64 := by
    have := hw0.cur_level_le; have := hco0.trail_end_le; have := hco0.cur_vars_le; omega
  have hmax_vars_pos : 0 < s.core.cur_level → 0 < c.max_vars := by
    intro _; have := hw0.cur_level_le; have := hco0.trail_end_le
    have := hco0.cur_vars_le; omega
  rw [FullM6Hdr.fullM6HdrMem_iff] at hm
  unfold Func.wp full_vivify_m6_hdr_body; fvt_to_group
  refine wp_join_group (ts := [])
    (fun () m1 => ∃ s1, FullSparseInv c F0 s1 ∧ s1.core.cur_level = 0 ∧
      s1.core.fuel.toNat ≤ s.core.fuel.toNat ∧
      (FullMem c s1 ⋆ (array64 (c.hdr - 2304) ext ⋆ R)) m1)
    (fun _ () m1 ⟨s1, hsp1, hcl01, hfu1, hm1⟩ => ?_) (fun _ hJ => ?_)
  · clear hm
    c0_call hSync
    refine FullM6Hdr.m6HdrW2aSpec_of rfl hcfg hext hsp1.1.lengths
      ((FullM6Hdr.fullM6HdrMem_iff ..).mpr hm1)
      fun () ext2 s2 m2 hcore2 hlen2 hsc2 hext2 hw2 hm2 => ?_
    have hsp2 : FullSparseInv c F0 s2 := fullSparseInv_of_core_eq_m6 hsp1 hlen2 hcore2 hsc2
    have hcl02 : s2.core.cur_level = 0 := by rw [hcore2]; exact hcl01
    rw [FullM6Hdr.fullM6HdrMem_iff] at hm2
    c0_hsteps_nogrp
    c0_call hGetWm
    refine FullM6Hdr.m6HdrW2aSpec_of rfl hcfg hext2 hsp2.1.lengths
      ((FullM6Hdr.fullM6HdrMem_iff ..).mpr hm2)
      fun ⟨last_p, ⟨⟩⟩ ext3 s3 m3 hcore3 hlen3 hsc3 hext3 hw3 hm3 => ?_
    have hsp3 : FullSparseInv c F0 s3 := fullSparseInv_of_core_eq_m6 hsp2 hlen3 hcore3 hsc3
    have hcl03 : s3.core.cur_level = 0 := by rw [hcore3]; exact hcl02
    have hpres3 : FullM6Hdr.M6HdrExtInitOk ext →
        FullM6Hdr.M6HdrExtInitOk ext3 ∧ FullM6Hdr.M6ExtW2bPres ext ext3 := fun hi =>
      ⟨(hw3 (hw2 hi).1).1, (hw2 hi).2.trans (hw3 (hw2 hi).1).2⟩
    have hfl3_le : s3.core.fuel.toNat ≤ s.core.fuel.toNat := by
      rw [hcore3, hcore2]; exact hfu1
    rw [FullM6Hdr.fullM6HdrMem_iff] at hm3
    have hbud : (0xFFFFFFFF#64 : BitVec 64) ≠ 0#64 := by decide
    let start := s2.scratch.search_ticks
    fvt_to_group
    refine wp_join_group (ts := [i64]) (fun _ md => md = m3) ?_
      (fun Jd hJd => by fvt_steps <;> exact hJd _ m3 rfl)
    rintro _ ⟨delta, ⟨⟩⟩ md hmd; rw [hmd]; fvt_to_group
    refine wp_join_group (ts := [i64]) (fun _ me => me = m3) ?_
      (fun Je hJe => by fvt_steps <;> exact hJe _ m3 rfl)
    rintro _ ⟨eff_ref, ⟨⟩⟩ me hme; rw [hme]; fvt_to_group
    · -- `num_redundant == 0`: single tier-0 pass + restore `h->search_ticks = start`
      refine wp_join_group (ts := [i64]) (fun _ ml0 => ml0 = m3) ?_
        (fun Jl0 hJl0 => by fvt_steps <;> exact hJl0 _ m3 rfl)
      rintro _ ⟨lim0, ⟨⟩⟩ ml0 hml0; rw [hml0]
      c0_call hVivTier
      refine FullM6OrchAdapters.m6aVivifyTierSpec_of hsp3 hm3
        fun r2 s4 m4 hsp4 _ _ hnz2 hfl4 hr2 hu2 hm4 => ?_
      obtain ⟨hcl4, hpr4⟩ := hnz2 hbud
      fvt_steps
      let s4' : FullState := { s4 with scratch := { s4.scratch with search_ticks := start } }
      have hsp4' : FullSparseInv c F0 s4' := fullSparseInv_with_ticks hsp4 start
      exact hQ r2 ext3 s4' _ ⟨hext3, hpres3⟩ hsp4' ⟨hcl4, hpr4⟩
        (Nat.le_trans hfl4 hfl3_le) hr2 hu2 ((FullM6Hdr.fullM6HdrMem_iff ..).mpr hm)
    · -- `num_redundant != 0`: merge `tier1 >= tier2` and thread carry-over `1 -> 2 -> 3 -> 0`
      refine wp_join_group (ts := [i64, i64]) (fun _ mw => mw = m3) ?_
        (fun Jw hJw => by fvt_steps <;> exact hJw _ m3 rfl)
      rintro _ ⟨w1, w2, ⟨⟩⟩ mw hmw; rw [hmw]; fvt_to_group
      refine wp_join_group (ts := [i64]) (fun _ ml1 => ml1 = m3) ?_
        (fun Jl1 hJl1 => by fvt_steps <;> exact hJl1 _ m3 rfl)
      rintro _ ⟨lim1, ⟨⟩⟩ ml1 hml1; rw [hml1]
      c0_call hVivTier
      refine FullM6OrchAdapters.m6aVivifyTierSpec_of hsp3 hm3
        fun res1 s4 m4 hsp4 _ _ hnz4 hfl4 hr1 hu1 hm4 => ?_
      obtain ⟨hcl4, hpr4⟩ := hnz4 hbud
      let TierInv : Tup Val [i64, i64] → Mem 64 → Prop := fun (r, _lim, ()) mk =>
        ∃ sk : FullState,
          FullSparseInv c F0 sk ∧ sk.core.cur_level = 0 ∧ sk.core.probing = 0#64 ∧
          sk.core.fuel.toNat ≤ s.core.fuel.toNat ∧
          (r = 1#64 ∨ r = 20#64) ∧ (r = 20#64 → F0.Unsat) ∧
          (FullMem c sk ⋆ (array64 (c.hdr - 2304) ext3 ⋆ R)) mk
      fvt_to_group
      refine wp_join_group (ts := [i64, i64]) TierInv ?_ ?_
      · -- Tier 2 continuation -> Tier 3 join
        rintro _ ⟨res2, lim2, ⟨⟩⟩ m_t2 ⟨s_t2, hsp_t2, hcl_t2, hpr_t2, hfl_t2, hr_t2, hu_t2, hm_t2⟩
        fvt_to_group
        refine wp_join_group (ts := [i64, i64]) TierInv ?_ ?_
        · -- Tier 3 continuation -> Tier 0 join
          rintro _ ⟨res3, lim3, ⟨⟩⟩ m_t3
            ⟨s_t3, hsp_t3, hcl_t3, hpr_t3, hfl_t3, hr_t3, hu_t3, hm_t3⟩
          fvt_to_group
          refine wp_join_group (ts := [i64, i64]) TierInv ?_ ?_
          · -- Final return: restore `h->search_ticks = start` and return `res`
            rintro _ ⟨res0, _lim0, ⟨⟩⟩ m_t0
              ⟨s_t0, hsp_t0, hcl_t0, hpr_t0, hfl_t0, hr_t0, hu_t0, hm_t0⟩
            fvt_steps
            let s_fin : FullState :=
              { s_t0 with scratch := { s_t0.scratch with search_ticks := start } }
            have hsp_fin : FullSparseInv c F0 s_fin := fullSparseInv_with_ticks hsp_t0 start
            exact hQ res0 ext3 s_fin _ ⟨hext3, hpres3⟩ hsp_fin ⟨hcl_t0, hpr_t0⟩
              hfl_t0 hr_t0 hu_t0 ((FullM6Hdr.fullM6HdrMem_iff ..).mpr hm)
          · -- Tier 0 branch (`res3 != 20ULL`)
            intro J0 hJ0
            fvt_to_group
            · refine wp_join_group (ts := [i64]) (fun _ ml0 => ml0 = m_t3) ?_
                (fun Jl0 hJl0 => by fvt_steps <;> exact hJl0 _ m_t3 rfl)
              rintro _ ⟨lim0', ⟨⟩⟩ ml0 hml0; rw [hml0]
              c0_call hVivTier
              refine FullM6OrchAdapters.m6aVivifyTierSpec_of hsp_t3 hm_t3
                fun res0 s_t0 m_t0 hsp_t0 _ _ hnz0 hfl0 hr0 hu0 hm_t0 => ?_
              obtain ⟨hcl0, hpr0⟩ := hnz0 hbud
              exact hJ0 (res0, lim0', ()) m_t0
                ⟨s_t0, hsp_t0, hcl0, hpr0, Nat.le_trans hfl0 hfl_t3, hr0, hu0, hm_t0⟩
            · exact hJ0 (res3, lim3, ()) m_t3
                ⟨s_t3, hsp_t3, hcl_t3, hpr_t3, hfl_t3, hr_t3, hu_t3, hm_t3⟩
        · -- Tier 3 branch (`res2 != 20ULL`)
          intro J3 hJ3
          fvt_to_group
          · refine wp_join_group (ts := [i64]) (fun _ ml3 => ml3 = m_t2) ?_
              (fun Jl3 hJl3 => by fvt_steps <;> exact hJl3 _ m_t2 rfl)
            rintro _ ⟨lim3', ⟨⟩⟩ ml3 hml3; rw [hml3]
            c0_call hVivTier
            refine FullM6OrchAdapters.m6aVivifyTierSpec_of hsp_t2 hm_t2
              fun res3 s_t3 m_t3 hsp_t3 _ _ hnz3 hfl3 hr3 hu3 hm_t3 => ?_
            obtain ⟨hcl3, hpr3⟩ := hnz3 hbud
            exact hJ3 (res3, lim3', ()) m_t3
              ⟨s_t3, hsp_t3, hcl3, hpr3, Nat.le_trans hfl3 hfl_t2, hr3, hu3, hm_t3⟩
          · exact hJ3 (res2, lim2, ()) m_t2
              ⟨s_t2, hsp_t2, hcl_t2, hpr_t2, hfl_t2, hr_t2, hu_t2, hm_t2⟩
      · -- Tier 2 branch (`res1 != 20ULL && w2 > 0ULL`)
        intro J2 hJ2
        fvt_to_group
        · refine wp_join_group (ts := [i64]) (fun _ ml2 => ml2 = m4) ?_
            (fun Jl2 hJl2 => by fvt_steps <;> exact hJl2 _ m4 rfl)
          rintro _ ⟨lim2', ⟨⟩⟩ ml2 hml2; rw [hml2]
          c0_call hVivTier
          refine FullM6OrchAdapters.m6aVivifyTierSpec_of hsp4 hm4
            fun res2 s_t2 m_t2 hsp_t2 _ _ hnz2 hfl2 hr2 hu2 hm_t2 => ?_
          obtain ⟨hcl2, hpr2⟩ := hnz2 hbud
          exact hJ2 (res2, lim2', ()) m_t2
            ⟨s_t2, hsp_t2, hcl2, hpr2, Nat.le_trans hfl2 (Nat.le_trans hfl4 hfl3_le),
              hr2, hu2, hm_t2⟩
        all_goals
          exact hJ2 (res1, lim1, ()) m4
            ⟨s4, hsp4, hcl4, hpr4, Nat.le_trans hfl4 hfl3_le, hr1, hu1, hm4⟩
  · fvt_steps
    · c0_call hBacktrack
      refine ⟨c, s, array64 (c.hdr - 2304) ext ⋆ R, rfl, hsp.1.lengths, hclv_lt, hmax_vars_pos,
        hw0.trail_lits_lt, hm, fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m1
          hlen1 _ _ hcl1 hpres1 _ _ _ hw_bt _ hm1 => ?_⟩
      have hsp1 : FullSparseInv c F0 _ :=
        FullVivTop.FullSparseInv.of_backtrack hsp (Nat.zero_le _) hlen1 hpres1
          (by simpa using hw_bt F0)
      exact hJ () m1 ⟨_, hsp1, by rw [hcl1]; simp, Nat.le_refl _, hm1⟩
    · have hcl0 : s.core.cur_level = 0 := by
        have h0 : (BitVec.ofNat 64 s.core.cur_level).toNat = 0 := by rw [hc]; rfl
        rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hclv_lt] at h0
      exact hJ () m ⟨s, hsp, hcl0, Nat.le_refl _, hm⟩

end VivifySection

end LeanQbe.T.Examples.Kissat.FullM7ParityVivTiers
