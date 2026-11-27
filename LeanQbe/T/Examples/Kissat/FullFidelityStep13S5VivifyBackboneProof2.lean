/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S5VivifyBackboneProof0a
public import LeanQbe.T.Examples.Kissat.FullFidelityVivK6Proof0b
public import LeanQbe.T.Examples.Kissat.FullM6VivBackboneProof3b
public import LeanQbe.T.Examples.Kissat.FullM6HdrProof0
import LeanQbe.T.Examples.Kissat.FullVivTopLemmas1
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 13 Shard S5-B — Vivify Tier & Top-Level (`Proof2`)

Proves UNSAT-sound `Func.wp` (`XPost := False`, `0` `@[expose]` on theorems/lemmas, `<= 100`
cols, every theorem `<= 420` lines) for:
1. `full_vivify_tier_m6_hdr_s5_wp` (`step13VivifyTierSpec`)
2. `full_vivify_m6_hdr_s5_wp` (`step13VivifySpec`)
-/

set_option autoImplicit false

local macro "s13_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S5

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open FullVivTopTactics FullM6Hdr FullM6VivBackbone FullFidelityVivK6
open scoped FullArenaTactics FullVivTopTactics FullM6Hdr.M6HdrTactics

@[expose] public section

/-- Read-only `FullState`-preserving spec for unchanged `m6_hdr_get_watermark(h, kind)`
needed where `full_vivify_tier_m6_hdr` calls it inside the `red_refs` loop guard. -/
def step13HdrGetWatermarkSpec : Spec [i64, i64] [i64] :=
  fun (h, _kind, ()) m Q _ =>
    ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
      (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ r ext' m',
        M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
        (FullM6HdrMem c ext' s ⋆ R) m' → Q (r, ()) m'

end

public section

/-! ## 1. Pure & Framing Helpers (`VivifyTierS5`) -/

section VivifyTierHelpers

private theorem s13_sparse_with_rr {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) {rr' : List (BitVec 32)} (hrr : rr'.length = c.red_cap) :
    FullSparseInv c F0 { s with scratch := { s.scratch with red_refs := rr' } } :=
  ⟨⟨⟨h.1.lengths.core_ok, { h.1.lengths.scratch_ok with red_refs_len := hrr }⟩, h.1.witness⟩,
    h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

private theorem s13_sparse_with_tr {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) {tr' : List (BitVec 32)} (htr : tr'.length = 2 * c.max_vars) :
    FullSparseInv c F0 { s with scratch := { s.scratch with tarjan_reach := tr' } } :=
  ⟨⟨⟨h.1.lengths.core_ok, { h.1.lengths.scratch_ok with tarjan_reach_len := htr }⟩, h.1.witness⟩,
    h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

private theorem s13_sparse_with_rr_scr {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) {rr' scr' : List (BitVec 32)} (hrr : rr'.length = c.red_cap)
    (hscr : scr'.length = c.scratch_cap) :
    FullSparseInv c F0
      { s with scratch := { s.scratch with red_refs := rr', scratch_buf := scr' } } :=
  ⟨⟨⟨h.1.lengths.core_ok,
      { h.1.lengths.scratch_ok with red_refs_len := hrr, scratch_buf_len := hscr }⟩,
    h.1.witness⟩, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

private theorem s13_sparse_with_res_sz {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) (rsz : BitVec 64) :
    FullSparseInv c F0 { s with scratch := { s.scratch with res_sz := rsz } } :=
  ⟨⟨⟨h.1.lengths.core_ok, { h.1.lengths.scratch_ok with }⟩, h.1.witness⟩,
    h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

private theorem s13_sparse_with_tier1 {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) (t1 : BitVec 64) :
    FullSparseInv c F0 { s with scratch := { s.scratch with tier1 := t1 } } :=
  ⟨⟨⟨h.1.lengths.core_ok, { h.1.lengths.scratch_ok with }⟩, h.1.witness⟩,
    h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

private theorem s13_sparse_with_tier2 {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) (t2 : BitVec 64) :
    FullSparseInv c F0 { s with scratch := { s.scratch with tier2 := t2 } } :=
  ⟨⟨⟨h.1.lengths.core_ok, { h.1.lengths.scratch_ok with }⟩, h.1.witness⟩,
    h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

private theorem s13_sparseInvW_of_prop_canon {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
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
      scratch := { s.scratch with search_ticks := ticks', wsort := wsort',
                                  phases := phases', delayed := delayed' } } :
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
        scratch := { s.scratch with search_ticks := ticks', wsort := wsort',
                                    phases := phases', delayed := delayed' } } := by
  let s' : FullState :=
    { s with
      core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                            trl := trl', trail_pos := tp', trail_end := te', propagated := prop',
                            unassigned := unass', unflushed := unfl', wvec := wvec',
                            arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
                            fuel := fuel', confl_type := ctype', confl_ref := cref',
                            confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
      scratch := { s.scratch with search_ticks := ticks', wsort := wsort',
                                  phases := phases', delayed := delayed' } }
  have hnd' : Full.FullArenaVarsNodup s' := fun ref href hng => by
    have href0 : ref ∈ fullArenaClauseRefsCore s.core := hperm.2.1 ▸ href
    obtain ⟨_, hgb, hp⟩ := hperm.2.2 ref href0
    exact (hp.map (· / 2)).nodup_iff.mpr (hsp.2.2.2.1 ref href0 (hgb.symm.trans hng))
  have hrefs : ∀ ref ∈ fullArenaClauseRefs s, ref ∈ fullArenaClauseRefs s' := fun ref hr => by
    change ref ∈ fullArenaClauseRefsCore s'.core; rw [hperm.2.1]; exact hr
  exact FullVivTop.fullSparseInvW_of_prop_state hsp hlen' hw' hnd'
    ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hrefs

private theorem s13_ext_pres_trans {ext0 ext1 ext2 : List (BitVec 64)}
    (h1 : M6HdrExtInitOk ext0 → M6HdrExtInitOk ext1 ∧ M6ExtW2bPres ext0 ext1)
    (h2 : M6HdrExtInitOk ext1 → M6HdrExtInitOk ext2 ∧ M6ExtW2bPres ext1 ext2) :
    M6HdrExtInitOk ext0 → M6HdrExtInitOk ext2 ∧ M6ExtW2bPres ext0 ext2 := fun hi =>
  ⟨(h2 (h1 hi).1).1, (h1 hi).2.trans (h2 (h1 hi).1).2⟩

private theorem s13_sparse_of_core_eq {c : FullCfg} {F0 : CNF Nat} {s s' : FullState}
    (hsp : FullSparseInv c F0 s) (hlen' : s'.LengthsOk c) (hc : s'.core = s.core)
    (hsc' : M6HdrScratchPres s s') : FullSparseInv c F0 s' := by
  obtain ⟨hcore_inv, hmc, hvn, hsc, hdm⟩ := hsp
  refine ⟨⟨hlen', ?_⟩, ?_, ?_, ?_, ?_⟩
  · obtain ⟨F_cur, hw⟩ := hcore_inv.2
    exact ⟨F_cur, by rw [hc]; exact hw⟩
  · unfold FullLitMarksClear FullMrkZero; rw [hc]; exact hmc
  · unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseGarb fullArenaClauseLits
    rw [hc]; exact hvn
  · exact FullExtScratchOk.of_pres hsc hsc'.extPres fun r hr => by
      unfold fullArenaClauseRefs; rwa [hc]
  · rw [hc]; exact hdm

private theorem s13_red_ref_mem {svi s2 : FullState} {rr5 : List (BitVec 32)}
    {bn bi : BitVec 64} (hrrv : svi.scratch.red_refs = rr5)
    (hrefsv : fullArenaClauseRefs svi = fullArenaClauseRefs s2)
    (hok5' : ∀ k < bn.toNat, (rr5[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s2)
    (hidx_rr : (bn - 1#64 - bi).toNat < svi.scratch.red_refs.length)
    (hidx_nat : (bn - 1#64 - bi).toNat = bn.toNat - 1 - bi.toNat)
    (hbi_lt : bi.toNat < bn.toNat) (hrr5_len : bn.toNat - 1 - bi.toNat < rr5.length) :
    (svi.scratch.red_refs[(bn - 1#64 - bi).toNat]'hidx_rr).toNat ∈
      fullArenaClauseRefs svi := by
  rw [hrefsv]
  have h := hok5' (bn.toNat - 1 - bi.toNat) (by omega)
  rw [List.getElem?_eq_getElem hrr5_len, Option.getD_some] at h
  suffices heq : svi.scratch.red_refs[(bn - 1#64 - bi).toNat]'hidx_rr =
      rr5[bn.toNat - 1 - bi.toNat]'hrr5_len by rwa [heq]
  subst hrrv; congr 1

private abbrev s13TierPropSt (s_vc : FullState) (vals_p : List (BitVec 8))
    (flags_p lvl_p rsns_p trl_p tp_p : List (BitVec 32)) (te_p prop_p : Nat)
    (unass_p unfl_p : BitVec 64) (wvec_p arena_p wstk_p : List (BitVec 32)) (wlen_p : Nat)
    (wu_p fuel_p ctype_p cref_p c0_p c1_p oom_p ticks_p : BitVec 64)
    (wsort_p : List (BitVec 32)) (phases_p : List (BitVec 8)) (delayed_p : List (BitVec 32)) :
    FullState :=
  { s_vc with
    core := { s_vc.core with
      vals := vals_p, flags := flags_p, lvl := lvl_p, rsns := rsns_p, trl := trl_p,
      trail_pos := tp_p, trail_end := te_p, propagated := prop_p, unassigned := unass_p,
      unflushed := unfl_p, wvec := wvec_p, arena := arena_p, wstk := wstk_p, wlen := wlen_p,
      wusable := wu_p, fuel := fuel_p, confl_type := ctype_p, confl_ref := cref_p,
      confl_lit0 := c0_p, confl_lit1 := c1_p, oom := oom_p }
    scratch := { s_vc.scratch with
      search_ticks := ticks_p, wsort := wsort_p, phases := phases_p, delayed := delayed_p } }

private abbrev S13TierSortJoin (c : FullCfg) (F0 : CNF Nat) (ext0 : List (BitVec 64))
    (s s2 : FullState) (bn : BitVec 64) (R : Mem 64 → Prop) : Tup Val [] → Mem 64 → Prop :=
  fun () ms => ∃ (s5 : FullState) (rr5 : List (BitVec 32)),
    FullSparseInv c F0 s5 ∧ s5.core.fuel.toNat ≤ s.core.fuel.toNat ∧
    fullArenaClauseRefs s5 = fullArenaClauseRefs s2 ∧ s5.scratch.red_refs = rr5 ∧
    rr5.length = c.red_cap ∧
    (∀ k < bn.toNat, (rr5[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s2) ∧
    (FullM6HdrMem c ext0 s5 ⋆ R) ms

private abbrev S13TierBrkInv (c : FullCfg) (F0 : CNF Nat) (ext0 : List (BitVec 64))
    (s : FullState) (R : Mem 64 → Prop) : Tup Val [i64, i64, i64] → Mem 64 → Prop :=
  fun (_budget_b, res_b, _bi_b, ()) mb =>
    ∃ (extb : List (BitVec 64)) (sb : FullState),
      M6HdrExtOk extb ∧ (M6HdrExtInitOk ext0 → M6HdrExtInitOk extb ∧ M6ExtW2bPres ext0 extb) ∧
      FullSparseInv c F0 sb ∧ sb.core.fuel.toNat ≤ s.core.fuel.toNat ∧
      (res_b = 1#64 ∨ res_b = 20#64) ∧ (res_b = 20#64 → F0.Unsat) ∧
      (FullM6HdrMem c extb sb ⋆ R) mb

private abbrev S13TierLpInv (c : FullCfg) (F0 : CNF Nat) (ext0 : List (BitVec 64))
    (s s2 : FullState) (bn : BitVec 64) (rr5 : List (BitVec 32)) (R : Mem 64 → Prop) :
    Nat → Tup Val [i64, i64] → Mem 64 → Prop :=
  fun rem (_budget, bi, ()) mvi =>
    ∃ (extv : List (BitVec 64)) (svi : FullState),
      M6HdrExtOk extv ∧ (M6HdrExtInitOk ext0 → M6HdrExtInitOk extv ∧ M6ExtW2bPres ext0 extv) ∧
      bi.toNat ≤ bn.toNat ∧ rem = bn.toNat - bi.toNat ∧ FullSparseInv c F0 svi ∧
      svi.core.fuel.toNat ≤ s.core.fuel.toNat ∧ fullArenaClauseRefs svi = fullArenaClauseRefs s2 ∧
      svi.scratch.red_refs = rr5 ∧ (FullM6HdrMem c extv svi ⋆ R) mvi

end VivifyTierHelpers

/-! ## 2. `full_vivify_tier_m6_hdr_s5_wp` (`step13VivifyTierSpec`) -/

section VivifyTierS5

private theorem s13_tier_prop_sparse {c : FullCfg} {F0 : CNF Nat} {F_curv : List (List Nat)}
    {s_vc : FullState} {vals_p : List (BitVec 8)}
    {flags_p lvl_p rsns_p trl_p tp_p : List (BitVec 32)}
    {te_p prop_p : Nat} {unass_p unfl_p : BitVec 64} {wvec_p arena_p wstk_p : List (BitVec 32)}
    {wlen_p : Nat} {wu_p fuel_p ctype_p cref_p c0_p c1_p oom_p : BitVec 64} {sc_p : FullScratch}
    (hsw_vc : FullSparseInvW c F0 F_curv s_vc)
    (hlen_p : ({ s_vc with
      core := { s_vc.core with
        vals := vals_p, flags := flags_p, lvl := lvl_p, rsns := rsns_p, trl := trl_p,
        trail_pos := tp_p, trail_end := te_p, propagated := prop_p, unassigned := unass_p,
        unflushed := unfl_p, wvec := wvec_p, arena := arena_p, wstk := wstk_p, wlen := wlen_p,
        wusable := wu_p, fuel := fuel_p, confl_type := ctype_p, confl_ref := cref_p,
        confl_lit0 := c0_p, confl_lit1 := c1_p, oom := oom_p }
      scratch := sc_p } : FullState).LengthsOk c)
    (hw_p : FullWitnessInv c F0 F_curv { s_vc.core with
      vals := vals_p, flags := flags_p, lvl := lvl_p, rsns := rsns_p, trl := trl_p,
      trail_pos := tp_p, trail_end := te_p, propagated := prop_p, unassigned := unass_p,
      unflushed := unfl_p, wvec := wvec_p, arena := arena_p, wstk := wstk_p, wlen := wlen_p,
      wusable := wu_p, fuel := fuel_p, confl_type := ctype_p, confl_ref := cref_p,
      confl_lit0 := c0_p, confl_lit1 := c1_p, oom := oom_p })
    (hperm_p : FullArenaPermEq s_vc.core { s_vc.core with
      vals := vals_p, flags := flags_p, lvl := lvl_p, rsns := rsns_p, trl := trl_p,
      trail_pos := tp_p, trail_end := te_p, propagated := prop_p, unassigned := unass_p,
      unflushed := unfl_p, wvec := wvec_p, arena := arena_p, wstk := wstk_p, wlen := wlen_p,
      wusable := wu_p, fuel := fuel_p, confl_type := ctype_p, confl_ref := cref_p,
      confl_lit0 := c0_p, confl_lit1 := c1_p, oom := oom_p })
    (hpr_sc_p : Full.FullProbeScratchPres { s_vc with scratch := { s_vc.scratch with
      search_ticks := sc_p.search_ticks, wsort := sc_p.wsort,
      phases := sc_p.phases, delayed := sc_p.delayed } } { s_vc with
      core := { s_vc.core with
        vals := vals_p, flags := flags_p, lvl := lvl_p, rsns := rsns_p, trl := trl_p,
        trail_pos := tp_p, trail_end := te_p, propagated := prop_p, unassigned := unass_p,
        unflushed := unfl_p, wvec := wvec_p, arena := arena_p, wstk := wstk_p, wlen := wlen_p,
        wusable := wu_p, fuel := fuel_p, confl_type := ctype_p, confl_ref := cref_p,
        confl_lit0 := c0_p, confl_lit1 := c1_p, oom := oom_p }
      scratch := sc_p }) :
    FullSparseInvW c F0 F_curv { s_vc with
      core := { s_vc.core with
        vals := vals_p, flags := flags_p, lvl := lvl_p, rsns := rsns_p, trl := trl_p,
        trail_pos := tp_p, trail_end := te_p, propagated := prop_p, unassigned := unass_p,
        unflushed := unfl_p, wvec := wvec_p, arena := arena_p, wstk := wstk_p, wlen := wlen_p,
        wusable := wu_p, fuel := fuel_p, confl_type := ctype_p, confl_ref := cref_p,
        confl_lit0 := c0_p, confl_lit1 := c1_p, oom := oom_p }
      scratch := sc_p } := by
  let s_p : FullState := { s_vc with
    core := { s_vc.core with
      vals := vals_p, flags := flags_p, lvl := lvl_p, rsns := rsns_p, trl := trl_p,
      trail_pos := tp_p, trail_end := te_p, propagated := prop_p, unassigned := unass_p,
      unflushed := unfl_p, wvec := wvec_p, arena := arena_p, wstk := wstk_p, wlen := wlen_p,
      wusable := wu_p, fuel := fuel_p, confl_type := ctype_p, confl_ref := cref_p,
      confl_lit0 := c0_p, confl_lit1 := c1_p, oom := oom_p }
    scratch := sc_p }
  have hnd_p : Full.FullArenaVarsNodup s_p := fun ref href hng => by
    have href0 : ref ∈ fullArenaClauseRefsCore s_vc.core := hperm_p.2.1 ▸ href
    obtain ⟨_, hgb, hp⟩ := hperm_p.2.2 ref href0
    exact (hp.map (· / 2)).nodup_iff.mpr (hsw_vc.2.2.2.1 ref href0 (hgb.symm.trans hng))
  have hrefs_p : ∀ ref ∈ fullArenaClauseRefs s_vc, ref ∈ fullArenaClauseRefs s_p := fun ref hr => by
    change ref ∈ fullArenaClauseRefsCore s_p.core; rw [hperm_p.2.1]; exact hr
  exact FullVivTop.fullSparseInvW_of_prop_state hsw_vc hlen_p hw_p hnd_p hpr_sc_p hrefs_p

private theorem s13_tier_cur_level_lt64 {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hsp : FullSparseInv c F0 s) : s.core.cur_level < 2 ^ 64 := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  obtain ⟨_, hw⟩ := hsp.exists_witness
  have := hw.2.1.cur_level_le; have := hsp.1.lengths.core_ok.trail_end_le
  have := hsp.1.lengths.core_ok.cur_vars_le; omega

private theorem s13_tier_cur_level_zero {cl : Nat} (hcl_lt : cl < 2 ^ 64)
    (hc0 : BitVec.ofNat 64 cl = 0#64) : cl = 0 := by
  have h0 : (BitVec.ofNat 64 cl).toNat = 0 := by rw [hc0]; rfl
  rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcl_lt] at h0

theorem full_vivify_tier_m6_hdr_s5_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hCollect : ∀ a m Q X, fullVivCollectFidSpec a m Q X →
      Γ "full_viv_collect_fid" [i64, i64] [i64] a m Q X)
    (hArenaNext : ∀ a m Q X, Full.fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hSort : ∀ a m Q X, fullVivSortFidSpec a m Q X →
      Γ "full_viv_sort_fid" [i64, i64] [] a m Q X)
    (hGetWm : ∀ a m Q X, step13HdrGetWatermarkSpec a m Q X →
      Γ "m6_hdr_get_watermark" [i64, i64] [i64] a m Q X)
    (hVivClause : ∀ a m Q X, FullM6VivBackbone.fullVivClauseM6Spec a m Q X →
      Γ "full_viv_clause_m6" [i64, i32] [i64] a m Q X)
    (hProp : ∀ a m Q X, s5bBcpM6Spec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hClearTier : ∀ a m Q X, FullM6VivBackbone.fullVivClearTierM6Spec a m Q X →
      Γ "full_viv_clear_tier_m6" [i64, i64] [] a m Q X) :
    ∀ a m Q X, step13VivifyTierSpec a m Q X →
      Func.wp Γ FullFidelityStep13S5VivifyBackbone.full_vivify_tier_m6_hdr_body a m Q X := by
  rintro ⟨h, tier_mode, budget0, tick_lim, ⟨⟩⟩ m0 Q X
    ⟨c, F0, ext0, s, R, rfl, hcfg, hext0, hsp0, hm0, hQ⟩
  have har_cap := c.harena; have hmx := c.hmaxv; have hrc := c.hred
  unfold dimacsBound at har_cap hmx hrc
  unfold Func.wp FullFidelityStep13S5VivifyBackbone.full_vivify_tier_m6_hdr_body
  dsimp only; fvt_to_group
  · fvt_steps
    exact hQ 1#64 ext0 s m0 ⟨hext0, fun hi => ⟨hi, M6ExtW2bPres.refl ext0⟩⟩
      hsp0 (fun h => h) rfl (fun hb => absurd (by c0_bound) hb)
      (Nat.le_refl _) (Or.inl rfl) (fun h => by cases h) hm0
  refine wp_join_group (ts := [])
    (fun () m1 => ∃ s1 : FullState, FullSparseInv c F0 s1 ∧ s1.core.cur_level = 0 ∧
      s1.core.probing = s.core.probing ∧ s1.core.fuel.toNat ≤ s.core.fuel.toNat ∧
      (FullM6HdrMem c ext0 s1 ⋆ R) m1) ?_ ?_
  · rintro _ ⟨⟩ m ⟨s1, hsp1, hcl1, hpr1, hfl1, hm⟩
    rw [fullM6HdrMem_iff] at hm
    fvt_steps
    let s2 : FullState := { s1 with core := { s1.core with probing := 1#64 } }
    have hsp2 : FullSparseInv c F0 s2 := FullVivTop.FullSparseInv.with_probing hsp1 1#64
    have hm2 : (FullMem c s2 ⋆ (array64 (c.hdr - 2304) ext0 ⋆ R)) m := hm
    have hfl2 : s2.core.fuel.toNat ≤ s.core.fuel.toNat := hfl1
    clear hm; clear hsp1 hcl1 hfl1
    s13_call hCollect
    refine fullVivCollectFidSpec_intro rfl hsp2
      (fullM6HdrMem_focus_full ((fullM6HdrMem_iff ..).mpr hm2))
      (fun bn rr3 m3 hbn_le hrr3 hok3 hm3 => ?_)
    let s3 : FullState := { s2 with scratch := { s2.scratch with red_refs := rr3 } }
    have hsp3 : FullSparseInv c F0 s3 := s13_sparse_with_rr hsp2 hrr3
    have hcv3_le := hsp3.1.lengths.core_ok.cur_vars_le
    have har3_le := hsp3.1.lengths.core_ok.arena_len_le
    have har3_len := hsp3.1.lengths.core_ok.arena_len_arr
    have htr3_len := hsp3.1.lengths.scratch_ok.tarjan_reach_len
    have hnlits3 : (BitVec.ofNat 64 s3.core.cur_vars <<< BitVec.signExtend 64 1#32).toNat =
        2 * s3.core.cur_vars := by
      change (BitVec.ofNat 64 s3.core.cur_vars <<< (1 : Nat)).toNat = 2 * s3.core.cur_vars
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.shiftLeft_eq, Nat.pow_one, Nat.mod_eq_of_lt (by omega)]
      omega
    obtain ⟨F_cur3, hsw3⟩ := hsp3.exists_witness
    fvt_steps
    -- Inline count zero loop: `while (l_vc < nlits_vc)`
    refine wp_loop_inv (ts := [i64])
      (fun (l_vc, ()) ml => ∃ trl : List (BitVec 32),
        l_vc.toNat ≤ 2 * s3.core.cur_vars ∧ trl.length = 2 * c.max_vars ∧
        (FullMem c { s3 with scratch := { s3.scratch with tarjan_reach := trl } } ⋆
          (m6ExtMem (m6ExtAddr c.hdr) ext0 ⋆ R)) ml)
      (fun (l_vc, ()) _ => 2 * s3.core.cur_vars - l_vc.toNat)
      (fun Jl hJl => by
        fvt_steps; exact hJl (0#64, ()) m3 ⟨s3.scratch.tarjan_reach, Nat.zero_le _, htr3_len, hm3⟩)
      (fun Jl ⟨l_vc, ⟨⟩⟩ ml ⟨trl, hl_le, htrl_len, hml⟩ ihl => ?_)
    c0_hsplit
    · have hl_lt : l_vc.toNat < 2 * s3.core.cur_vars := by
        have hc' : l_vc.toNat <
            (BitVec.ofNat 64 s3.core.cur_vars <<< BitVec.signExtend 64 1#32).toNat := by c0_bound
        rwa [hnlits3] at hc'
      have hl1 : (l_vc + 1#64).toNat = l_vc.toNat + 1 := by bv_omega
      fvt_steps
      exact ihl (l_vc + 1#64, ()) _ (by dsimp only; rw [hl1]; omega)
        ⟨_, by rw [hl1]; omega, by simp [htrl_len], hm⟩
    · -- Inline count arena scan loop: `while (p_vc < h->arena_len)`
      refine wp_loop_inv (ts := [i64])
        (fun (p_vc, ()) mp => ∃ trp : List (BitVec 32),
          p_vc.toNat ≤ s3.core.arena_len ∧
          (p_vc.toNat = s3.core.arena_len ∨ p_vc.toNat ∈ fullArenaClauseRefs s3) ∧
          trp.length = 2 * c.max_vars ∧
          (FullMem c { s3 with scratch := { s3.scratch with tarjan_reach := trp } } ⋆
            (m6ExtMem (m6ExtAddr c.hdr) ext0 ⋆ R)) mp)
        (fun (p_vc, ()) _ => s3.core.arena_len - p_vc.toNat)
        (fun Jp hJp => by
          fvt_steps
          refine hJp (0#64, ()) ml ⟨trl, Nat.zero_le _, ?_, htrl_len, hml⟩
          by_cases hz : s3.core.arena_len = 0
          · exact Or.inl hz.symm
          · exact Or.inr (FullVivifyHelpers.fullArenaClauseRefs_zero_mem hsw3.2.1.arena
              (by omega)))
        (fun Jp ⟨p_vc, ⟨⟩⟩ mp ⟨trp, hp_le, hp_mem, htrp_len, hmp⟩ ihp => ?_)
      c0_hsplit
      · have hp_lt : p_vc.toNat < s3.core.arena_len := by
          have hc' : p_vc.toNat < (BitVec.ofNat 64 s3.core.arena_len).toNat := by c0_bound
          rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hc'
        have hp_ref : p_vc.toNat ∈ fullArenaClauseRefs s3 := by
          rcases hp_mem with heq | hmem
          · omega
          · exact hmem
        have hwf_p := hsw3.2.1.arena.refs_wf p_vc.toNat hp_ref
        have hp2_nat : (p_vc + 2#64).toNat = p_vc.toNat + 2 := by bv_omega
        have hp2_lt : (p_vc + 2#64).toNat < s3.core.arena.length := by omega
        let hdr_vc := s3.core.arena[p_vc.toNat]'(by omega)
        let sz_vc := s3.core.arena[(p_vc + 2#64).toNat]'hp2_lt
        have hsz_eq : sz_vc.toNat = fullArenaClauseSizeCore s3.core p_vc.toNat := by
          dsimp only [sz_vc]; unfold fullArenaClauseSizeCore
          simp only [hp2_nat, List.getElem?_eq_getElem (by omega : p_vc.toNat + 2 <
            s3.core.arena.length), Option.getD_some]
        have hsz_bd : p_vc.toNat + 3 + sz_vc.toNat ≤ s3.core.arena_len := by
          rw [hsz_eq]; exact Nat.le_trans hwf_p.2.2.1 hwf_p.2.2.2.1
        have hp32_nat : (p_vc.truncate 32).toNat = p_vc.toNat := by
          rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
        let s3p : FullState := { s3 with scratch := { s3.scratch with tarjan_reach := trp } }
        have hlen3p : s3p.LengthsOk c :=
          ⟨hsp3.1.lengths.core_ok, { hsp3.1.lengths.scratch_ok with tarjan_reach_len := htrp_len }⟩
        c0_hsteps_nogrp; s13_call hArenaNext
        refine ⟨c, s3p, m6ExtMem (m6ExtAddr c.hdr) ext0 ⋆ R, rfl, hlen3p, hmp, ?_⟩
        have hnxt_bnd := fullArenaNextOff_bounds (ar := s3.core.arena) (alen := s3.core.arena_len)
          (cref := p_vc.toNat) (by omega)
        have hnxt_mem : fullArenaNextOff s3.core.arena s3.core.arena_len p_vc.toNat =
            s3.core.arena_len ∨
            fullArenaNextOff s3.core.arena s3.core.arena_len p_vc.toNat ∈ fullArenaClauseRefs s3 :=
          FullVivifyHelpers.fullArenaClauseRefs_next_mem_or_end hsw3.2.1.arena hp_ref
        let np32 := BitVec.ofNat 32 (fullArenaNextOff s3.core.arena s3.core.arena_len p_vc.toNat)
        have hnp32_eq : np32 = BitVec.ofNat 32
            (fullArenaNextOff s3p.core.arena s3p.core.arena_len (p_vc.truncate 32).toNat) := by
          dsimp only [np32, s3p]; rw [hp32_nat]
        have hnp_nat : (np32.setWidth 64).toNat =
            fullArenaNextOff s3.core.arena s3.core.arena_len p_vc.toNat := by
          dsimp only [np32]
          rw [bv32_setWidth64_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        fvt_to_group
        refine wp_join_group (ts := [])
          (fun () mj => ∃ trj : List (BitVec 32), trj.length = 2 * c.max_vars ∧
            (FullMem c { s3 with scratch := { s3.scratch with tarjan_reach := trj } } ⋆
              (m6ExtMem (m6ExtAddr c.hdr) ext0 ⋆ R)) mj)
          (fun _ () mj ⟨trj, htrj_len, hmj⟩ => by
            fvt_steps
            rw [← hnp32_eq]
            exact ihp (np32.setWidth 64, ()) mj (by dsimp only; rw [hnp_nat]; omega)
              ⟨trj, by rw [hnp_nat]; omega, by rw [hnp_nat]; exact hnxt_mem, htrj_len, hmj⟩)
          (fun Jif hJif => by
            fvt_steps
            · -- `(hdr_vc & PH_GARB) == 0 && sz_vc >= 3`: inner `k_vc` loop
              refine wp_loop_inv (ts := [i32])
                (fun (k_vc, ()) mk => ∃ trk : List (BitVec 32),
                  k_vc.toNat ≤ sz_vc.toNat ∧ trk.length = 2 * c.max_vars ∧
                  (FullMem c { s3 with scratch := { s3.scratch with tarjan_reach := trk } } ⋆
                    (m6ExtMem (m6ExtAddr c.hdr) ext0 ⋆ R)) mk)
                (fun (k_vc, ()) _ => sz_vc.toNat - k_vc.toNat)
                (fun Jk hJk => by fvt_steps; exact hJk (0#32, ()) mp ⟨trp, Nat.zero_le _,
                  htrp_len, hmp⟩)
                (fun Jk ⟨k_vc, ⟨⟩⟩ mk ⟨trk, hk_le, htrk_len, hmk⟩ ihk => ?_)
              c0_hsplit
              · have hk_lt : k_vc.toNat < sz_vc.toNat := by c0_bound
                have hk1 : (k_vc + 1#32).toNat = k_vc.toNat + 1 := by bv_omega
                have hk_idx : (p_vc + 3#64 + k_vc.setWidth 64).toNat =
                    p_vc.toNat + 3 + k_vc.toNat := by bv_omega
                have hk_ar : (p_vc + 3#64 + k_vc.setWidth 64).toNat < s3.core.arena.length := by
                  omega
                let lit_vc := s3.core.arena[(p_vc + 3#64 + k_vc.setWidth 64).toNat]'hk_ar
                have hk_idx_eq : (p_vc + 3#64 + k_vc.setWidth 64).toNat =
                    (p_vc.toNat + 3 + k_vc.toNat) % 2 ^ 64 := by
                  simp [BitVec.toNat_add, Nat.add_assoc]
                fvt_to_group
                refine wp_join_group (ts := [])
                  (fun () m1 => ∃ tr1 : List (BitVec 32), tr1.length = 2 * c.max_vars ∧
                    (FullMem c { s3 with scratch := { s3.scratch with tarjan_reach := tr1 } } ⋆
                      (m6ExtMem (m6ExtAddr c.hdr) ext0 ⋆ R)) m1)
                  (fun _ () m1 ⟨tr1, htr1, hm1⟩ => by
                    fvt_steps
                    exact ihk (k_vc + 1#32, ()) m1 (by dsimp only; rw [hk1]; omega)
                      ⟨tr1, by rw [hk1]; omega, htr1, hm1⟩)
                  (fun Jif2 hJif2 => by
                    c0_hsplit
                    · have hcv2_lt : s2.core.cur_vars < 2 ^ 64 := by
                        change s3.core.cur_vars < 2 ^ 64; omega
                      have hlit_lt : lit_vc.toNat < 2 * s3.core.cur_vars := by
                        have hsum_lt : p_vc.toNat + 3 + k_vc.toNat < 2 ^ 64 := by omega
                        have h2 : (s3.core.arena[(p_vc.toNat + 3 + k_vc.toNat) % 2 ^ 64]'(by
                            rw [Nat.mod_eq_of_lt hsum_lt]; omega)).toNat <
                            2 * s3.core.cur_vars := by
                          have h1 := hc
                          have hcv_lt : s2.core.cur_vars < 2 ^ 64 := by
                            change s3.core.cur_vars < 2 ^ 64; omega
                          have hcv2_lt' : 2 * s2.core.cur_vars < 2 ^ 64 := by
                            change 2 * s3.core.cur_vars < 2 ^ 64; omega
                          rwa [Nat.mod_eq_of_lt hcv_lt, Nat.mod_eq_of_lt hcv2_lt'] at h1
                        simpa [lit_vc, hk_idx_eq] using h2
                      have hlit_tr : (BitVec.setWidth 64
                          (s3.core.arena[(p_vc + 3#64 + k_vc.setWidth 64).toNat]'hk_ar)).toNat <
                          trk.length := by
                        rw [bv32_setWidth64_toNat, htrk_len]; change lit_vc.toNat < 2 * c.max_vars
                        omega
                      c0_hsplit
                      · c0_hsteps; refine hJif2 () _ ⟨_, ?_, by assumption⟩
                        rw [List.length_set]; exact htrk_len
                      · exact hJif2 () mk ⟨trk, htrk_len, hmk⟩
                    · exact hJif2 () mk ⟨trk, htrk_len, hmk⟩)
              all_goals exact hJif () mk ⟨trk, htrk_len, hmk⟩
            · exact hJif () mp ⟨trp, htrp_len, hmp⟩
            · exact hJif () mp ⟨trp, htrp_len, hmp⟩)
      · -- Exit arena scan loop: optional `full_viv_sort_fid(h, bn)`
        let s3b : FullState := { s3 with scratch := { s3.scratch with tarjan_reach := trp } }
        have hsp3b : FullSparseInv c F0 s3b := s13_sparse_with_tr hsp3 htrp_len
        have hok3b : ∀ k < bn.toNat, (s3b.scratch.red_refs[k]?.getD 0#32).toNat ∈
            fullArenaClauseRefs s3b := hok3
        let SortJoin := S13TierSortJoin c F0 ext0 s s2 bn R
        c0_hsteps_nogrp
        refine wp_join_group (ts := [.bool]) (fun _ md => mp = md) ?_
          (fun _ hJd => by
            have hten : (10#64 : BitVec 64) ≠ 0#64 := by decide
            c0_hsplit
            · c0_hsteps; exact hJd _ mp rfl
            · c0_hsteps_nogrp
              c0_hsplit
              · c0_hsteps; exact hJd _ mp rfl
              · c0_hsteps; exact hJd _ mp rfl)
        rintro _ ⟨do_sort, ⟨⟩⟩ md hmd; rw [← hmd]; c0_hsteps_nogrp
        refine wp_join_group (ts := []) SortJoin ?_ ?_
        · rintro _ ⟨⟩ m5 ⟨s5, rr5, hsp5, hfl5, hrefs5, hrr5, hrr5_len, hok5', hm5'⟩
          c0_hsteps_nogrp
          refine wp_loop_break_group (brkTs := [i64, i64, i64]) (lpTs := [i64, i64])
            (S13TierBrkInv c F0 ext0 s R) (S13TierLpInv c F0 ext0 s s2 bn rr5 R) ?_ ?_ ?_
          · rintro _ ⟨_, res_b, bi_b, ⟨⟩⟩ mb ⟨extb, sb, hextb, hpb, hspb, hflb, hresb, h20b, hmb⟩
            refine wp_join_group (ts := [])
              (fun () m_bt => ∃ sbt : FullState,
                FullSparseInv c F0 sbt ∧ sbt.core.cur_level = 0 ∧
                sbt.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c extb sbt ⋆ R) m_bt) ?_ ?_
            · rintro _ ⟨⟩ m_bt ⟨sbt, hspbt, hclbt, hflbt, hm_bt⟩
              refine wp_join_group (ts := [])
                (fun () m_w => ∃ sw : FullState,
                  FullSparseInv c F0 sw ∧ sw.core.cur_level = 0 ∧
                  sw.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullM6HdrMem c extb sw ⋆ R) m_w) ?_ ?_
              · rintro _ ⟨⟩ m_w ⟨sw, hspw, hclw, hflw, hm_w⟩
                rw [fullM6HdrMem_iff] at hm_w
                fvt_steps
                let sf1 : FullState := { sw with scratch := { sw.scratch with res_sz := bi_b } }
                let sf : FullState :=
                  { sf1 with core := { sf1.core with probing := s1.core.probing } }
                exact hQ res_b extb sf _ ⟨hextb, hpb⟩
                  (FullVivTop.FullSparseInv.with_probing (s13_sparse_with_res_sz hspw bi_b)
                    s1.core.probing) (fun _ => hclw) hpr1 (fun _ => hclw) hflw hresb h20b
                  ((fullM6HdrMem_iff ..).mpr (by assumption))
              · intro Jw hJw; rw [fullM6HdrMem_iff] at hm_bt
                c0_hsplit
                · c0_hsplit
                  · c0_hsplit
                    · s13_call hClearTier
                      refine ⟨c, F0, sbt, m6ExtMem (m6ExtAddr c.hdr) extb ⋆ R, rfl, hspbt, hclbt,
                        fullM6HdrMem_focus_full ((fullM6HdrMem_iff ..).mpr hm_bt),
                        fun sw m_w hspw hclw hflw hm_w =>
                          hJw () m_w ⟨sw, hspw, hclw, by rw [hflw]; exact hflbt,
                            fullM6HdrMem_unfocus_full hm_w⟩⟩
                    all_goals (c0_hsteps; exact hJw () m_bt ⟨sbt, hspbt, hclbt, hflbt,
                      (fullM6HdrMem_iff ..).mpr hm_bt⟩)
                  all_goals (c0_hsteps; exact hJw () m_bt ⟨sbt, hspbt, hclbt, hflbt,
                    (fullM6HdrMem_iff ..).mpr hm_bt⟩)
                all_goals (c0_hsteps; exact hJw () m_bt ⟨sbt, hspbt, hclbt, hflbt,
                  (fullM6HdrMem_iff ..).mpr hm_bt⟩)
            · intro Jbt hJbt; obtain ⟨F_curb, hswb⟩ := hspb.exists_witness
              have hclb_lt : sb.core.cur_level < 2 ^ 64 := by
                have := hswb.2.1.cur_level_le; have := hspb.1.lengths.core_ok.trail_end_le
                have := hspb.1.lengths.core_ok.cur_vars_le; omega
              rw [fullM6HdrMem_iff] at hmb; c0_hsplit
              · s13_call hBacktrack
                refine ⟨c, sb, m6ExtMem (m6ExtAddr c.hdr) extb ⋆ R, rfl, hspb.1.lengths, hclb_lt,
                  (by intro _; have := hswb.2.1.cur_level_le
                      have := hspb.1.lengths.core_ok.trail_end_le
                      have := hspb.1.lengths.core_ok.cur_vars_le; omega),
                  hswb.2.1.trail_lits_lt, fullM6HdrMem_focus_full ((fullM6HdrMem_iff ..).mpr hmb),
                  fun _ _ _ _ _ _ _ _ _ _ m_bt hlen_bt _ _ hcl_bt hpres_bt _ _ _ hw_bt _ hm_bt =>
                    hJbt () m_bt ⟨_, FullVivTop.FullSparseInv.of_backtrack hspb (Nat.zero_le _)
                      hlen_bt hpres_bt (by simpa using hw_bt F0), by rw [hcl_bt]; simp,
                      hflb, fullM6HdrMem_unfocus_full hm_bt⟩⟩
              · exact hJbt () mb ⟨sb, hspb, s13_tier_cur_level_zero hclb_lt hc, hflb,
                  (fullM6HdrMem_iff ..).mpr hmb⟩
          · intro B L rem ⟨budget, bi, ⟨⟩⟩ mvi hB hL
              ⟨extv, svi, hextv, hpv, hbi_le, hrem, hspv, hflv, hrefsv, hrrv, hmvi⟩
            subst hrem
            have hrrv_len : svi.scratch.red_refs.length = c.red_cap := by rw [hrrv, hrr5_len]
            rw [fullM6HdrMem_iff] at hmvi
            fvt_to_group
            · have hbi_lt : bi.toNat < bn.toNat := by c0_bound
              have hbi1 : (bi + 1#64).toNat = bi.toNat + 1 := by bv_omega
              s13_call hGetWm
              refine ⟨c, extv, svi, R, rfl, hcfg, hextv, hspv.1.lengths,
                (fullM6HdrMem_iff ..).mpr hmvi, fun wm ext_w mw hext_w hpw mw_mem => ?_⟩
              have hpw' := s13_ext_pres_trans hpv hpw
              rw [fullM6HdrMem_iff] at mw_mem
              c0_hsplit
              · have hidx_nat : (bn - 1#64 - bi).toNat = bn.toNat - 1 - bi.toNat := by bv_omega
                have hidx_rr : (bn - 1#64 - bi).toNat < svi.scratch.red_refs.length := by
                  rw [hidx_nat, hrrv_len]; omega
                have hcr_ref := s13_red_ref_mem hrrv hrefsv hok5' hidx_rr hidx_nat hbi_lt
                  (by omega)
                obtain ⟨F_curv, hswv⟩ := hspv.exists_witness
                c0_hsteps_nogrp
                s13_call hVivClause
                refine ⟨c, F0, F_curv, svi, m6ExtMem (m6ExtAddr c.hdr) ext_w ⋆ R, rfl, hswv,
                  hcr_ref, fullM6HdrMem_focus_full ((fullM6HdrMem_iff ..).mpr mw_mem),
                  fun vc s_vc m_vc hsw_vc hfl_vc _ hrefs_vc hrr_vc hvc h20_vc hm_vc => ?_⟩
                have hm_vc' := fullM6HdrMem_unfocus_full hm_vc
                have hrefs_vc2 : fullArenaClauseRefs s_vc = fullArenaClauseRefs s2 :=
                  hrefs_vc.trans hrefsv
                have hrr_vc5 : s_vc.scratch.red_refs = rr5 := hrr_vc.trans hrrv
                have hfl_vc' : s_vc.core.fuel.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfl_vc hflv
                c0_hsplit
                · exact hB (budget - 1#64, 20#64, bi, ()) m_vc
                    ⟨ext_w, s_vc, hext_w, hpw', hsw_vc.toSparse, hfl_vc', Or.inr rfl,
                     fun _ => h20_vc (by c0_bound), hm_vc'⟩
                · c0_hsplit
                  · exact hB (budget - 1#64, 1#64, bi, ()) m_vc
                      ⟨ext_w, s_vc, hext_w, hpw', hsw_vc.toSparse, hfl_vc', Or.inl rfl,
                       (fun h => by cases h), hm_vc'⟩
                  · c0_hsteps_nogrp
                    refine wp_join_group (ts := [])
                      (fun () m_j => ∃ (ext_j : List (BitVec 64)) (F_curj : List (List Nat))
                        (sj : FullState), M6HdrExtOk ext_j ∧
                        (M6HdrExtInitOk ext0 → M6HdrExtInitOk ext_j ∧ M6ExtW2bPres ext0 ext_j) ∧
                        FullSparseInvW c F0 F_curj sj ∧ sj.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                        fullArenaClauseRefs sj = fullArenaClauseRefs s2 ∧
                        sj.scratch.red_refs = rr5 ∧ (FullM6HdrMem c ext_j sj ⋆ R) m_j)
                      (fun _ ⟨⟩ m_j ⟨ext_j, _, sj, hext_j, hpj, hsw_j, hfl_j, hrefs_j, hrr_j,
                          hm_j⟩ => by
                        c0_hsteps
                        exact hL (bn.toNat - (bi + 1#64).toNat) (budget - 1#64, bi + 1#64, ()) m_j
                          (by rw [hbi1]; omega)
                          ⟨ext_j, sj, hext_j, hpj, by rw [hbi1]; omega, rfl, hsw_j.toSparse,
                           hfl_j, hrefs_j, hrr_j, hm_j⟩)
                      (fun Jc hJc => by
                        c0_hsplit
                        · have hcl_vc0 : s_vc.core.cur_level = 0 :=
                            s13_tier_cur_level_zero (s13_tier_cur_level_lt64 hsw_vc.toSparse)
                              (by c0_bound)
                          s13_call hProp
                          refine ⟨c, F0, F_curv, ext_w, s_vc, R, rfl, hcfg, hext_w,
                            hsw_vc.1, hsw_vc.2.1, hsw_vc.2.2.2.2.2, hm_vc',
                            fun pr ext_p vals_p flags_p lvl_p rsns_p trl_p tp_p te_p prop_p
                              unass_p unfl_p wvec_p arena_p wstk_p wlen_p wu_p fuel_p ctype_p
                              cref_p c0_p c1_p oom_p sc_p m_p hext_p hp_ext hlen_p hw_p _ hperm_p
                              hpr_sc_p hrr_p _ _ _ hfl_p _ _ hpr1 _ _ hm_p => ?_⟩
                          let s_p : FullState :=
                            { s_vc with
                              core := { s_vc.core with
                                vals := vals_p, flags := flags_p, lvl := lvl_p, rsns := rsns_p,
                                trl := trl_p, trail_pos := tp_p, trail_end := te_p,
                                propagated := prop_p, unassigned := unass_p, unflushed := unfl_p,
                                wvec := wvec_p, arena := arena_p, wstk := wstk_p, wlen := wlen_p,
                                wusable := wu_p, fuel := fuel_p, confl_type := ctype_p,
                                confl_ref := cref_p, confl_lit0 := c0_p, confl_lit1 := c1_p,
                                oom := oom_p }
                              scratch := sc_p }
                          have hsw_p := s13_tier_prop_sparse hsw_vc hlen_p hw_p hperm_p hpr_sc_p
                          have hfl_p' : s_p.core.fuel.toNat ≤ s.core.fuel.toNat :=
                            Nat.le_trans hfl_p hfl_vc'
                          have hext_wp := s13_ext_pres_trans hpw' hp_ext
                          c0_hsplit
                          · have hpr_eq1 : pr = 1#64 := by c0_bound
                            exact hB (budget - 1#64, 20#64, bi, ()) m_p
                              ⟨ext_p, s_p, hext_p, hext_wp, hsw_p.toSparse, hfl_p', Or.inr rfl,
                               fun _ => FullVivTopSpecs.level0_unsat_of_conflict_okW hw_p hcl_vc0
                                 (hpr1 hpr_eq1).2.2, hm_p⟩
                          · exact hJc () m_p ⟨ext_p, F_curv, s_p, hext_p, hext_wp, hsw_p, hfl_p',
                              hperm_p.2.1.trans hrefs_vc2, hrr_p.trans hrr_vc5, hm_p⟩
                        · exact hJc () m_vc ⟨ext_w, F_curv, s_vc, hext_w, hpw', hsw_vc, hfl_vc',
                            hrefs_vc2, hrr_vc5, hm_vc'⟩)
              · exact hB (budget, 1#64, bi, ()) mw
                  ⟨ext_w, svi, hext_w, hpw', hspv, hflv, Or.inl rfl, (fun h => by cases h),
                    (fullM6HdrMem_iff ..).mpr mw_mem⟩
            all_goals exact hB (budget, 1#64, bi, ()) mvi ⟨extv, svi, hextv, hpv, hspv, hflv,
              Or.inl rfl, (fun h => by cases h), (fullM6HdrMem_iff ..).mpr hmvi⟩
          · intro B L _ hL; fvt_steps
            exact hL bn.toNat (budget0, 0#64, ()) m5
              ⟨ext0, s5, hext0, (fun hi => ⟨hi, M6ExtW2bPres.refl ext0⟩),
               Nat.zero_le _, rfl, hsp5, hfl5, hrefs5, hrr5, hm5'⟩
        · intro Js hJs
          c0_hsplit
          · s13_call hSort
            refine fullVivSortFidSpec_intro rfl hsp3b hbn_le hok3b hmp
              (fun rr5 scr5 m5 hrr5_len hscr5 hok5 hm5 => ?_)
            let s5 : FullState :=
              { s3b with scratch := { s3b.scratch with red_refs := rr5, scratch_buf := scr5 } }
            have hsp5 : FullSparseInv c F0 s5 := s13_sparse_with_rr_scr hsp3b hrr5_len hscr5
            exact hJs () m5 ⟨s5, rr5, hsp5, hfl2, rfl, rfl, hrr5_len, hok5,
              fullM6HdrMem_unfocus_full hm5⟩
          · c0_hsteps
            exact hJs () mp ⟨s3b, rr3, hsp3b, hfl2, rfl, rfl, hrr3, hok3b,
              fullM6HdrMem_unfocus_full hmp⟩
  · intro Jc hJc; obtain ⟨F_cur0, hsw0⟩ := hsp0.exists_witness
    have hcl0_lt : s.core.cur_level < 2 ^ 64 := s13_tier_cur_level_lt64 hsp0
    have hm0' := hm0; rw [fullM6HdrMem_iff] at hm0; c0_hsteps_nogrp; c0_hsplit
    · s13_call hBacktrack
      refine ⟨c, s, m6ExtMem (m6ExtAddr c.hdr) ext0 ⋆ R, rfl, hsp0.1.lengths, hcl0_lt,
        (by intro _; have := hsw0.2.1.cur_level_le; have := hsp0.1.lengths.core_ok.trail_end_le
            have := hsp0.1.lengths.core_ok.cur_vars_le; omega),
        hsw0.2.1.trail_lits_lt, fullM6HdrMem_focus_full hm0',
        fun _ _ _ _ _ _ _ _ _ _ m1 hlen1 _ _ hcl1 hpres1 _ _ _ hw_bt _ hm1 =>
          hJc () m1 ⟨_, FullVivTop.FullSparseInv.of_backtrack hsp0 (Nat.zero_le _) hlen1
            hpres1 (by simpa using hw_bt F0), by rw [hcl1]; simp, rfl, Nat.le_refl _,
            fullM6HdrMem_unfocus_full hm1⟩⟩
    · exact hJc () m0 ⟨s, hsp0, s13_tier_cur_level_zero hcl0_lt hc, rfl, Nat.le_refl _, hm0'⟩

end VivifyTierS5

/-! ## 3. `full_vivify_m6_hdr_s5_wp` (`step13VivifySpec`) -/

section VivifyTopS5

theorem full_vivify_m6_hdr_s5_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hGetT1 : ∀ a m Q X, m6HdrW2aSpec [.bool] [i64] a m Q X →
      Γ "m6_hdr_get_tier1" [i64, .bool] [i64] a m Q X)
    (hGetT2 : ∀ a m Q X, m6HdrW2aSpec [.bool] [i64] a m Q X →
      Γ "m6_hdr_get_tier2" [i64, .bool] [i64] a m Q X)
    (hDelaying : ∀ a m Q X, m6HdrW2aSpec [i64] [.bool] a m Q X →
      Γ "m6_hdr_delaying" [i64, i64] [.bool] a m Q X)
    (hGetWm : ∀ a m Q X, step13HdrGetWatermarkSpec a m Q X →
      Γ "m6_hdr_get_watermark" [i64, i64] [i64] a m Q X)
    (hVivTier : ∀ a m Q X, step13VivifyTierSpec a m Q X →
      Γ "full_vivify_tier_m6_hdr" [i64, i64, i64, i64] [i64] a m Q X)
    (hBump : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_bump_delay" [i64, i64] [] a m Q X)
    (hReduce : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_reduce_delay" [i64, i64] [] a m Q X)
    (hSync : ∀ a m Q X, m6HdrW2aSpec [] [] a m Q X →
      Γ "m6_hdr_sync_legacy_tiers" [i64] [] a m Q X) :
    ∀ a m Q X, step13VivifySpec a m Q X →
      Func.wp Γ FullFidelityStep13S5VivifyBackbone.full_vivify_m6_hdr_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, ext, s, R, rfl, hcfg, hext, hsp, hm, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  obtain ⟨F_cur, hw0⟩ := hsp.1.witness
  have hco0 := hsp.1.lengths.core_ok
  have hclv_lt : s.core.cur_level < 2 ^ 64 := by
    have := hw0.cur_level_le; have := hco0.trail_end_le; have := hco0.cur_vars_le; omega
  have hm_orig := hm
  rw [fullM6HdrMem_iff] at hm
  unfold Func.wp FullFidelityStep13S5VivifyBackbone.full_vivify_m6_hdr_body
  c0_hsteps_nogrp
  refine wp_join_group (ts := [])
    (fun () m1 => ∃ s1, FullSparseInv c F0 s1 ∧ s1.core.cur_level = 0 ∧
      s1.core.probing = s.core.probing ∧ s1.core.fuel.toNat ≤ s.core.fuel.toNat ∧
      (FullM6HdrMem c ext s1 ⋆ R) m1) ?_ ?_
  · rintro _ ⟨⟩ m1 ⟨s1, hsp1, hcl01, hpr01, hfl1, hm1⟩
    s13_call hGetT1
    refine m6HdrW2aSpec_of rfl hcfg hext hsp1.1.lengths hm1
      fun ⟨t1, ⟨⟩⟩ ext1 s1a m1a hcore1 hlen1 hsc1 hext1 hw1 hm1a => ?_
    have hsp1a := s13_sparse_of_core_eq hsp1 hlen1 hcore1 hsc1
    rw [fullM6HdrMem_iff] at hm1a; c0_hsteps_nogrp
    let s1b : FullState := { s1a with scratch := { s1a.scratch with tier1 := t1 } }
    have hsp1b := s13_sparse_with_tier1 hsp1a t1
    have hcl1b : s1b.core.cur_level = 0 := by dsimp only [s1b]; rw [hcore1]; exact hcl01
    have hpr1b : s1b.core.probing = s.core.probing := by dsimp only [s1b]; rw [hcore1]; exact hpr01
    have hfl1b : s1b.core.fuel.toNat ≤ s.core.fuel.toNat := by
      dsimp only [s1b]; rw [hcore1]; exact hfl1
    s13_call hGetT2
    refine m6HdrW2aSpec_of rfl hcfg hext1 hsp1b.1.lengths ((fullM6HdrMem_iff ..).mpr hm)
      fun ⟨t2, ⟨⟩⟩ ext2 s2a m2a hcore2 hlen2 hsc2 hext2 hw2 hm2a => ?_
    have hsp2a := s13_sparse_of_core_eq hsp1b hlen2 hcore2 hsc2
    have hpres2 := s13_ext_pres_trans hw1 hw2
    rw [fullM6HdrMem_iff] at hm2a; c0_hsteps_nogrp
    let s2 : FullState := { s2a with scratch := { s2a.scratch with tier2 := t2 } }
    have hsp2 := s13_sparse_with_tier2 hsp2a t2
    have hcl2 : s2.core.cur_level = 0 := by dsimp only [s2]; rw [hcore2]; exact hcl1b
    have hpr2 : s2.core.probing = s.core.probing := by dsimp only [s2]; rw [hcore2]; exact hpr1b
    have hfl2 : s2.core.fuel.toNat ≤ s.core.fuel.toNat := by
      dsimp only [s2]; rw [hcore2]; exact hfl1b
    refine wp_join_group (ts := [i64])
      (fun (w0, ()) mw => ∃ ext3 s3, M6HdrExtOk ext3 ∧
        (M6HdrExtInitOk ext → M6HdrExtInitOk ext3 ∧ M6ExtW2bPres ext ext3) ∧
        FullSparseInv c F0 s3 ∧ s3.core.cur_level = 0 ∧ s3.core.probing = s.core.probing ∧
        s3.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        (FullMem c s3 ⋆ (array64 (c.hdr - 2304) ext3 ⋆ R)) mw)
      (fun _ ⟨w0, ⟨⟩⟩ m3 ⟨ext3, s3, hext3, hpres3, hsp3, hcl3, hpr3, hfl3, hm3⟩ => ?_)
      (fun _ hJw => by
        s13_call hDelaying
        refine m6HdrW2aSpec_of rfl hcfg hext2 hsp2.1.lengths ((fullM6HdrMem_iff ..).mpr hm)
          fun ⟨_del, ⟨⟩⟩ ext3 s3 m3 hcore3 hlen3 hsc3 hext3 hw3 hm3 => ?_
        have hsp3 := s13_sparse_of_core_eq hsp2 hlen3 hcore3 hsc3
        have hcl3 : s3.core.cur_level = 0 := by rw [hcore3]; exact hcl2
        have hpr3 : s3.core.probing = s.core.probing := by rw [hcore3]; exact hpr2
        have hfl3 : s3.core.fuel.toNat ≤ s.core.fuel.toNat := by rw [hcore3]; exact hfl2
        have hpres3 := s13_ext_pres_trans hpres2 hw3
        rw [fullM6HdrMem_iff] at hm3
        c0_hsplit
        · c0_hsteps; exact hJw (0#64, ()) m3 ⟨ext3, s3, hext3, hpres3, hsp3, hcl3, hpr3, hfl3, hm3⟩
        · c0_hsteps; exact hJw (3#64, ()) m3 ⟨ext3, s3, hext3, hpres3, hsp3, hcl3, hpr3, hfl3, hm3⟩)
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64])
      (fun (w1, ()) mw => (w1 = 0#64 ∨ w1 = 3#64) ∧ mw = m3) ?_
      (fun _ hJw => by
        c0_hsplit
        · c0_hsteps; exact hJw (0#64, ()) m3 ⟨Or.inl rfl, rfl⟩
        · c0_hsteps; exact hJw (3#64, ()) m3 ⟨Or.inr rfl, rfl⟩)
    rintro _ ⟨w1, ⟨⟩⟩ mw ⟨hw1_v, hmw⟩; rw [hmw]; c0_hsteps_nogrp
    refine wp_join_group (ts := [i64])
      (fun (w2, ()) mw => (w2 = 0#64 ∨ w2 = 3#64) ∧ mw = m3) ?_
      (fun _ hJw => by
        c0_hsplit
        · c0_hsteps; exact hJw (0#64, ()) m3 ⟨Or.inl rfl, rfl⟩
        · c0_hsteps; exact hJw (3#64, ()) m3 ⟨Or.inr rfl, rfl⟩)
    rintro _ ⟨w2, ⟨⟩⟩ mw ⟨hw2_v, hmw⟩; rw [hmw]; c0_hsteps_nogrp
    refine wp_join_group (ts := [i64])
      (fun (w3, ()) mw => (w3 = 0#64 ∨ w3 = 1#64) ∧ mw = m3) ?_
      (fun _ hJw => by
        c0_hsplit
        · c0_hsteps; exact hJw (0#64, ()) m3 ⟨Or.inl rfl, rfl⟩
        · c0_hsteps; exact hJw (1#64, ()) m3 ⟨Or.inr rfl, rfl⟩)
    rintro _ ⟨w3, ⟨⟩⟩ mw ⟨hw3_v, hmw⟩; rw [hmw]; c0_hsteps_nogrp
    c0_hsplit
    · -- `sum == 0`: return `1`
      c0_hsteps
      exact hQ 1#64 ext3 s3 m3 ⟨hext3, hpres3⟩ hsp3 ⟨hcl3, hpr3⟩ hfl3 (Or.inl rfl)
        (fun h => by cases h) ((fullM6HdrMem_iff ..).mpr hm3)
    · -- `sum ≠ 0`
      have hsum_nz : w0 + w1 + w2 + w3 ≠ 0#64 := by c0_bound
      have hten_nz : (10#64 : BitVec 64) ≠ 0#64 := by decide
      c0_hsteps_nogrp
      s13_call hGetWm
      refine ⟨c, ext3, s3, R, rfl, hcfg, hext3, hsp3.1.lengths,
        ((fullM6HdrMem_iff ..).mpr hm3), fun last_p ext4 m4 hext4 hw4 hm4 => ?_⟩
      have hpres4 := s13_ext_pres_trans hpres3 hw4
      rw [fullM6HdrMem_iff] at hm4
      c0_hsteps_nogrp
      refine wp_join_group (ts := [i64]) (fun _ md => md = m4) ?_
        (fun _ hJd => by c0_hsteps <;> exact hJd _ m4 rfl)
      rintro _ ⟨delta, ⟨⟩⟩ md hmd; rw [hmd]; c0_hsteps_nogrp
      refine wp_join_group (ts := [i64]) (fun _ me => me = m4) ?_
        (fun _ hJe => by c0_hsteps <;> exact hJe _ m4 rfl)
      rintro _ ⟨eff_ref, ⟨⟩⟩ me hme; rw [hme]; c0_hsteps_nogrp
      refine wp_join_group (ts := [i64, i64]) (fun _ mw12 => mw12 = m4) ?_
        (fun _ hJw12 => by c0_hsteps <;> exact hJw12 _ m4 rfl)
      rintro _ ⟨w1', w2', ⟨⟩⟩ mw12 hmw12; rw [hmw12]; c0_hsteps_nogrp
      s13_call hGetWm
      refine ⟨c, ext4, s3, R, rfl, hcfg, hext4, hsp3.1.lengths,
        ((fullM6HdrMem_iff ..).mpr hm4), fun lim0 ext5 m5 hext5 hw5 hm5 => ?_⟩
      have hpres5 := s13_ext_pres_trans hpres4 hw5
      have hbud : (0xFFFFFFFF#64 : BitVec 64) ≠ 0#64 := by decide
      let TierPost (res : Val i64) (ext_n : List (BitVec 64)) (sn : FullState) (mn : Mem 64) :
          Prop :=
        M6HdrExtOk ext_n ∧ (M6HdrExtInitOk ext → M6HdrExtInitOk ext_n ∧ M6ExtW2bPres ext ext_n) ∧
        FullSparseInv c F0 sn ∧ sn.core.cur_level = 0 ∧ sn.core.probing = s.core.probing ∧
        sn.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (res = 1#64 ∨ res = 20#64) ∧
        (res = 20#64 → F0.Unsat) ∧ (FullM6HdrMem c ext_n sn ⋆ R) mn
      rw [fullM6HdrMem_iff] at hm5
      c0_hsteps_nogrp
      -- After tier 1
      refine wp_join_group (ts := [i64, i64])
        (fun (res1, _lim1, ()) mt1 => ∃ ext_t1 st1, TierPost res1 ext_t1 st1 mt1) ?_ ?_
      · rintro _ ⟨res1, lim1, ⟨⟩⟩ mt1 ⟨ext_t1, st1, hpt1⟩
        c0_hsteps_nogrp
        refine wp_join_group (ts := [i64, i64])
          (fun (res2, _lim2, ()) mt2 => ∃ ext_t2 st2, TierPost res2 ext_t2 st2 mt2) ?_ ?_
        · rintro _ ⟨res2, lim2, ⟨⟩⟩ mt2 ⟨ext_t2, st2, hpt2⟩
          c0_hsteps_nogrp
          refine wp_join_group (ts := [i64, i64])
            (fun (res3, _lim3, ()) mt3 => ∃ ext_t3 st3, TierPost res3 ext_t3 st3 mt3) ?_ ?_
          · rintro _ ⟨res3, lim3, ⟨⟩⟩ mt3 ⟨ext_t3, st3, hpt3⟩
            c0_hsteps_nogrp
            refine wp_join_group (ts := [i64, i64])
              (fun (res0, _lim0, ()) mt0 => ∃ ext_t0 st0, TierPost res0 ext_t0 st0 mt0) ?_ ?_
            · rintro _ ⟨res0, _lim0, ⟨⟩⟩ mt0 ⟨ext_t0, st0, hext_t0, hpt_t0, hsp_t0, hcl_t0, hpr_t0,
                hfl_t0, hres_t0, h20_t0, hm_t0⟩
              s13_call hSync
              refine m6HdrW2aSpec_of rfl hcfg hext_t0 hsp_t0.1.lengths hm_t0
                fun () ext_f sf mf hcore_f hlen_f hsc_f hext_f hw_f hm_f => ?_
              have hspf := s13_sparse_of_core_eq hsp_t0 hlen_f hcore_f hsc_f
              exact hQ res0 ext_f sf mf ⟨hext_f, s13_ext_pres_trans hpt_t0 hw_f⟩ hspf
                ⟨by rw [hcore_f]; exact hcl_t0, by rw [hcore_f]; exact hpr_t0⟩
                (by rw [hcore_f]; exact hfl_t0) hres_t0 h20_t0 hm_f
            · intro J0 hJ0
              obtain ⟨hext_t3, hpt_t3, hsp_t3, hcl_t3, hpr_t3, hfl_t3, hres_t3, h20_t3, hm_t3⟩ :=
                hpt3
              rw [fullM6HdrMem_iff] at hm_t3
              c0_hsplit
              · c0_hsplit
                · c0_hsteps_nogrp
                  refine wp_join_group (ts := [i64]) (fun _ ml => ml = mt3) ?_
                    (fun _ hJl => by c0_hsplit <;> (c0_hsteps; exact hJl _ mt3 rfl))
                  rintro _ ⟨_lim4, ⟨⟩⟩ ml hml; rw [hml]; c0_hsteps_nogrp
                  s13_call hVivTier
                  refine ⟨c, F0, ext_t3, st3, R, rfl, hcfg, hext_t3, hsp_t3,
                    (fullM6HdrMem_iff ..).mpr hm_t3,
                    fun r4 ext4 s4 m4 ⟨hext4, hp4⟩ hsp4 _ hpr4 hcl4 hfl4 hr4 h20_4 hm4 => ?_⟩
                  have hp4' := s13_ext_pres_trans hpt_t3 hp4
                  rw [fullM6HdrMem_iff] at hm4
                  c0_hsteps_nogrp
                  refine wp_join_group (ts := [])
                    (fun () m_end => ∃ ext4b s4b, M6HdrExtOk ext4b ∧
                      (M6HdrExtInitOk ext → M6HdrExtInitOk ext4b ∧ M6ExtW2bPres ext ext4b) ∧
                      FullSparseInv c F0 s4b ∧ s4b.core.cur_level = 0 ∧
                      s4b.core.probing = s.core.probing ∧
                      s4b.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                      (FullM6HdrMem c ext4b s4b ⋆ R) m_end)
                    (fun _ () m_end ⟨ext4b, s4b, hext4b, hpt4b, hsp4b, hcl4b, hpr4b, hfl4b,
                        hm4b⟩ =>
                      hJ0 (r4, _, ()) m_end ⟨ext4b, s4b, hext4b, hpt4b, hsp4b, hcl4b, hpr4b,
                        hfl4b, hr4, h20_4, hm4b⟩)
                    (fun J_if hJ_if => by
                      c0_hsplit
                      · c0_hsteps_nogrp
                        refine wp_join_group (ts := [i64]) (fun _ md => md = m4) ?_
                          (fun _ hJd => by c0_hsplit <;> (c0_hsteps; exact hJd _ m4 rfl))
                        rintro _ ⟨_du, ⟨⟩⟩ md hmd; rw [hmd]; c0_hsteps_nogrp
                        refine wp_join_group (ts := [])
                          (fun () mb => ∃ ext4b s4b, M6HdrExtOk ext4b ∧
                            (M6HdrExtInitOk ext → M6HdrExtInitOk ext4b ∧
                              M6ExtW2bPres ext ext4b) ∧
                            FullSparseInv c F0 s4b ∧ s4b.core.cur_level = 0 ∧
                            s4b.core.probing = s.core.probing ∧
                            s4b.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                            (FullM6HdrMem c ext4b s4b ⋆ R) mb)
                          (fun _ () mb hmb_post => hJ_if () mb hmb_post)
                          (fun Ja hJa => by
                            refine wp_join_group (ts := []) (fun () mc => mc = m4)
                              (fun _ () mc hmc => by
                                subst hmc
                                s13_call hBump
                                refine m6HdrW2aSpec_of rfl hcfg hext4 hsp4.1.lengths
                                  ((fullM6HdrMem_iff ..).mpr hm4)
                                  fun () ext4b s4b m4b hcore4b hlen4b hsc4b hext4b hw4b hm4b => ?_
                                exact hJa () m4b ⟨ext4b, s4b, hext4b, s13_ext_pres_trans hp4' hw4b,
                                  s13_sparse_of_core_eq hsp4 hlen4b hcore4b hsc4b,
                                  by rw [hcore4b]; exact hcl4 hbud,
                                  by rw [hcore4b]; exact hpr4.trans hpr_t3,
                                  by rw [hcore4b]; exact Nat.le_trans hfl4 hfl_t3, hm4b⟩)
                              (fun Jb hJb => by
                                c0_hsplit
                                · exact hJb () m4 rfl
                                · c0_hsteps_nogrp
                                  c0_hsplit
                                  · exact hJb () m4 rfl
                                  · s13_call hReduce
                                    refine m6HdrW2aSpec_of rfl hcfg hext4 hsp4.1.lengths
                                      ((fullM6HdrMem_iff ..).mpr hm4)
                                      fun () ext4b s4b m4b hcore4b hlen4b hsc4b hext4b hw4b hm4b =>
                                        hJa () m4b ⟨ext4b, s4b, hext4b,
                                          s13_ext_pres_trans hp4' hw4b,
                                          s13_sparse_of_core_eq hsp4 hlen4b hcore4b hsc4b,
                                          by rw [hcore4b]; exact hcl4 hbud,
                                          by rw [hcore4b]; exact hpr4.trans hpr_t3,
                                          by rw [hcore4b]; exact Nat.le_trans hfl4 hfl_t3, hm4b⟩))
                      · exact hJ_if () m4 ⟨ext4, s4, hext4, hp4', hsp4, hcl4 hbud,
                          hpr4.trans hpr_t3, Nat.le_trans hfl4 hfl_t3,
                          ((fullM6HdrMem_iff ..).mpr hm4)⟩)
                · exact hJ0 (res3, _, ()) mt3 ⟨ext_t3, st3, hext_t3, hpt_t3, hsp_t3, hcl_t3, hpr_t3,
                    hfl_t3, hres_t3, h20_t3, (fullM6HdrMem_iff ..).mpr hm_t3⟩
              · exact hJ0 (res3, _, ()) mt3 ⟨ext_t3, st3, hext_t3, hpt_t3, hsp_t3, hcl_t3, hpr_t3,
                  hfl_t3, hres_t3, h20_t3, (fullM6HdrMem_iff ..).mpr hm_t3⟩
          · intro J3 hJ3
            obtain ⟨hext_t2, hpt_t2, hsp_t2, hcl_t2, hpr_t2, hfl_t2, hres_t2, h20_t2, hm_t2⟩ :=
              hpt2
            c0_hsplit
            · c0_hsplit
              · c0_hsteps_nogrp
                refine wp_join_group (ts := [i64]) (fun _ ml => ml = mt2) ?_
                  (fun _ hJl => by c0_hsplit <;> (c0_hsteps; exact hJl _ mt2 rfl))
                rintro _ ⟨_lim3, ⟨⟩⟩ ml hml; rw [hml]; c0_hsteps_nogrp
                s13_call hVivTier
                refine ⟨c, F0, ext_t2, st2, R, rfl, hcfg, hext_t2, hsp_t2, hm_t2,
                  fun r3 ext3' s3' m3' ⟨hext3', hp3'⟩ hsp3' _ hpr3' hcl3'
                    hfl3' hr3' h20_3' hm3' => ?_⟩
                exact hJ3 (r3, _, ()) m3' ⟨ext3', s3', hext3', s13_ext_pres_trans hpt_t2 hp3',
                  hsp3', hcl3' hbud, hpr3'.trans hpr_t2, Nat.le_trans hfl3' hfl_t2,
                  hr3', h20_3', hm3'⟩
              · exact hJ3 (res2, lim2, ()) mt2 ⟨ext_t2, st2, hext_t2, hpt_t2, hsp_t2, hcl_t2,
                  hpr_t2, hfl_t2, hres_t2, h20_t2, hm_t2⟩
            · exact hJ3 (res2, lim2, ()) mt2 ⟨ext_t2, st2, hext_t2, hpt_t2, hsp_t2, hcl_t2,
                hpr_t2, hfl_t2, hres_t2, h20_t2, hm_t2⟩
        · intro J2 hJ2
          obtain ⟨hext_t1, hpt_t1, hsp_t1, hcl_t1, hpr_t1, hfl_t1, hres_t1, h20_t1, hm_t1⟩ :=
            hpt1
          c0_hsplit
          · c0_hsplit
            · c0_hsteps_nogrp
              refine wp_join_group (ts := [i64]) (fun _ ml => ml = mt1) ?_
                (fun _ hJl => by c0_hsplit <;> (c0_hsteps; exact hJl _ mt1 rfl))
              rintro _ ⟨_lim2, ⟨⟩⟩ ml hml; rw [hml]; c0_hsteps_nogrp
              s13_call hVivTier
              refine ⟨c, F0, ext_t1, st1, R, rfl, hcfg, hext_t1, hsp_t1, hm_t1,
                fun r2 ext2' s2' m2' ⟨hext2', hp2'⟩ hsp2' _ hpr2' hcl2'
                  hfl2' hr2' h20_2' hm2' => ?_⟩
              exact hJ2 (r2, _, ()) m2' ⟨ext2', s2', hext2', s13_ext_pres_trans hpt_t1 hp2',
                hsp2', hcl2' hbud, hpr2'.trans hpr_t1, Nat.le_trans hfl2' hfl_t1,
                hr2', h20_2', hm2'⟩
            · exact hJ2 (res1, lim1, ()) mt1 ⟨ext_t1, st1, hext_t1, hpt_t1, hsp_t1, hcl_t1,
                hpr_t1, hfl_t1, hres_t1, h20_t1, hm_t1⟩
          · exact hJ2 (res1, lim1, ()) mt1 ⟨ext_t1, st1, hext_t1, hpt_t1, hsp_t1, hcl_t1,
              hpr_t1, hfl_t1, hres_t1, h20_t1, hm_t1⟩
      · intro J1 hJ1
        c0_hsplit
        · c0_hsteps_nogrp
          refine wp_join_group (ts := [i64]) (fun _ ml => ml = m5) ?_
            (fun _ hJl => by c0_hsplit <;> (c0_hsteps; exact hJl _ m5 rfl))
          rintro _ ⟨_lim1, ⟨⟩⟩ ml hml; rw [hml]; c0_hsteps_nogrp
          s13_call hVivTier
          refine ⟨c, F0, ext5, s3, R, rfl, hcfg, hext5, hsp3,
            ((fullM6HdrMem_iff ..).mpr hm5),
            fun r1 ext1' s1' m1' ⟨hext1', hp1'⟩ hsp1' _ hpr1' hcl1' hfl1' hr1' h20_1' hm1' => ?_⟩
          exact hJ1 (r1, _, ()) m1' ⟨ext1', s1', hext1', s13_ext_pres_trans hpres5 hp1',
            hsp1', hcl1' hbud, hpr1'.trans hpr3, Nat.le_trans hfl1' hfl3, hr1', h20_1', hm1'⟩
        · exact hJ1 (1#64, lim0, ()) _ ⟨ext5, s3, hext5, hpres5, hsp3, hcl3, hpr3, hfl3,
            Or.inl rfl, (fun h => by cases h), ((fullM6HdrMem_iff ..).mpr hm5)⟩
  · intro Jb hJb
    fvt_steps
    · s13_call hBacktrack
      refine ⟨c, s, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hsp.1.lengths, hclv_lt,
        (by intro _; have := hw0.cur_level_le; have := hco0.trail_end_le
            have := hco0.cur_vars_le; omega),
        hw0.trail_lits_lt, fullM6HdrMem_focus_full hm_orig,
        fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m1
          hlen1 _ _ hcl1 hpres1 _ _ _ hw_bt _ hm1 => ?_⟩
      have hsp1 : FullSparseInv c F0 _ :=
        FullVivTop.FullSparseInv.of_backtrack hsp (Nat.zero_le _) hlen1 hpres1
          (by simpa using hw_bt F0)
      exact hJb () m1 ⟨_, hsp1, by rw [hcl1]; simp, rfl, Nat.le_refl _,
        fullM6HdrMem_unfocus_full hm1⟩
    · have hcl0 : s.core.cur_level = 0 := by
        have h0 : (BitVec.ofNat 64 s.core.cur_level).toNat = 0 := by rw [hc]; rfl
        rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hclv_lt] at h0
      exact hJb () m ⟨s, hsp, hcl0, rfl, Nat.le_refl _, hm_orig⟩

end VivifyTopS5

end

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S5
