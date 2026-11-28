/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Vivify.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Vivify.Tactics
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts3
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts4
public import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv1

/-!
# Arena, Witness, & Watch Preservation Invariants (`Proof.Vivify.InvArena`)

Provides canonical (`0` legacy `Full*` imports) preservation lemmas for `FullSparseInvW` /
`FullSparseInv` across backtrack, canonical propagation (`propIgnoreM6Spec` / `propagateM6Spec`),
header flag/glue updates, `PH_GARB`, in-place clause shrinking under `NonActiveReason`,
large watch push, resolution soundness (`VivDeduceSubWitness`), and arena next-ref iteration.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Vivify

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Vivify.Spec
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Vivify.VivTactics
open Kraken.Bedrock2.Test

public section

/-! ## 1. Shared Predicates & Field Updaters -/

/-- `ShrkPad` compatibility predicate for in-place clause shrinking. -/
@[expose] def M6ShrkPad (ar_p ar0 : List (BitVec 32)) (cref old_sz nsz : Nat) : Prop :=
  if (ar0[cref]?.getD 0#32 &&& 0x00800000#32) = 0#32 then
    (∀ k, cref + 3 + nsz ≤ k → k < cref + 3 + old_sz - 1 → ar_p[k]? = ar0[k]?) ∧
    ar_p[cref + 3 + old_sz - 1]? = some 0xFFFFFFFF#32
  else
    ∀ k, cref + 3 + nsz ≤ k → k < cref + 3 + old_sz → ar_p[k]? = ar0[k]?

/-- Level-0 metadata preservation predicate across simplify / commit / watch-push steps. -/
@[expose] def VivMetaEq (s s' : FullState) : Prop :=
  s'.core.arena_len = s.core.arena_len ∧ s'.core.cur_vars = s.core.cur_vars ∧
  s'.core.cur_level = 0 ∧ s'.core.probing = s.core.probing ∧ s'.core.fuel = s.core.fuel

/-- Arena reference & next-offset equality across non-reallocating arena mutations. -/
@[expose] def VivArenaEq (s s' : FullState) : Prop :=
  fullArenaClauseRefs s' = fullArenaClauseRefs s ∧ ∀ q ∈ fullArenaClauseRefs s,
    fullArenaNextOff s'.core.arena s.core.arena_len q =
      fullArenaNextOff s.core.arena s.core.arena_len q

theorem viv_conflictOkW_to_viv {F_cur : List (List Nat)} {s : FullState}
    (h : FullConflictOkW F_cur s) : FullVivConflictOk F_cur s := by
  rcases h with ⟨ht, h0, h1, hf0, hf1, hent⟩ | h2
  · exact Or.inl ⟨ht, h0, h1, hent, hf0, hf1⟩
  · exact Or.inr h2

theorem viv_fullMem_eq {c : FullCfg} {s1 s2 : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (h : s1 = s2) (hm : (FullMem c s1 ⋆ R) m) : (FullMem c s2 ⋆ R) m := h ▸ hm

theorem viv_m6HdrMem_eq {c : FullCfg} {ext : List (BitVec 64)} {s1 s2 : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (h : s1 = s2)
    (hm : (FullM6HdrMem c ext s1 ⋆ R) m) : (FullM6HdrMem c ext s2 ⋆ R) m := h ▸ hm

theorem viv_sparseW_to_sparse {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullSparseInvW c F0 F_cur s) : FullSparseInv c F0 s :=
  h.toSparse

theorem viv_watchLayout_of_sparse {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s) : WatchStackLayout s.core := by
  have hmw := hsp.2.1.watches; unfold ModeWatchesInv at hmw
  rw [ite_eq_left hsp.2.2.2.2.2] at hmw; exact hmw.layout

theorem viv_with_scratch {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) {sc' : FullScratch} (hlen : sc'.LengthsOk c)
    (hpres : FullExtScratchPres s { s with scratch := sc' }) :
    FullSparseInv c F0 { s with scratch := sc' } := by
  obtain ⟨F_cur, hsw⟩ := h.exists_witness
  exact FullSparseInvW.toSparse
    ⟨⟨hsw.1.core_ok, hlen⟩, hsw.2.1, hsw.2.2.1, hsw.2.2.2.1,
     h.2.2.2.1.of_pres hpres (fun _ hr => hr), hsw.2.2.2.2.2⟩

theorem viv_with_oomW {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    (h : FullSparseInvW c F0 F_cur s) (v : BitVec 64) :
    FullSparseInvW c F0 F_cur { s with core := { s.core with oom := v } } :=
  ⟨⟨{ h.1.core_ok with vals_len := h.1.core_ok.vals_len }, h.1.scratch_ok⟩,
   { h.2.1 with
     arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
     watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
   h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem viv_with_probing {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) (pr : BitVec 64) :
    FullSparseInv c F0 { s with core := { s.core with probing := pr } } := by
  obtain ⟨F_cur, hsw⟩ := h.exists_witness
  exact ⟨⟨⟨{ hsw.1.core_ok with vals_len := hsw.1.core_ok.vals_len }, hsw.1.scratch_ok⟩,
    F_cur,
    { hsw.2.1 with
      arena := { hsw.2.1.arena with len_ok := hsw.2.1.arena.len_ok }
      watches := hsw.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }⟩,
    hsw.2.2.1, hsw.2.2.2.1, hsw.2.2.2.2.1, hsw.2.2.2.2.2⟩

theorem viv_with_confl {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    (h : FullSparseInvW c F0 F_cur s) (ct cr : BitVec 64) :
    FullSparseInvW c F0 F_cur
      { s with core := { s.core with confl_type := ct, confl_ref := cr } } :=
  ⟨⟨{ h.1.core_ok with vals_len := h.1.core_ok.vals_len }, h.1.scratch_ok⟩,
   { h.2.1 with
     arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
     watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
   h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem viv_with_tmp {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    (h : FullSparseInvW c F0 F_cur s) {tmp' : List (BitVec 32)}
    (ht : tmp'.length = c.max_vars) :
    FullSparseInvW c F0 F_cur { s with core := { s.core with tmp := tmp' } } :=
  ⟨⟨{ h.1.core_ok with tmp_len_arr := ht }, h.1.scratch_ok⟩,
   { h.2.1 with
     arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
     watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
   h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem viv_with_flags {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    (h : FullSparseInvW c F0 F_cur s) {fl' : List (BitVec 32)} (hfl : fl'.length = c.max_vars) :
    FullSparseInvW c F0 F_cur { s with core := { s.core with flags := fl' } } :=
  ⟨⟨{ h.1.core_ok with flags_len := hfl }, h.1.scratch_ok⟩,
   { h.2.1 with
     arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
     watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
   h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem viv_with_ant_res {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    (hsp : FullSparseInvW c F0 F_cur s) (asz rsz : BitVec 64) :
    FullSparseInvW c F0 F_cur
      { s with scratch := { s.scratch with ant_sz := asz, res_sz := rsz } } :=
  ⟨⟨hsp.1.core_ok, { hsp.1.scratch_ok with }⟩,
   hsp.2.1, hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩

theorem viv_with_ws2 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    (hsp : FullSparseInvW c F0 F_cur s) {ws2' : List (BitVec 32)}
    (hlen : ws2'.length = 2 * c.max_vars) :
    FullSparseInvW c F0 F_cur { s with scratch := { s.scratch with work_stk2 := ws2' } } :=
  ⟨⟨hsp.1.core_ok, { hsp.1.scratch_ok with work_stk2_len := hlen }⟩,
   hsp.2.1, hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩

theorem viv_with_mrk_rsz {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    (hsp : FullSparseInv c F0 s) (hw : FullWitnessInv c F0 F_cur s.core)
    {mrk' : List (BitVec 8)} {ws1' ws2' : List (BitVec 32)} {rsz' : BitVec 64}
    (hmrk : mrk'.length = c.max_vars) (hmrk_clr : ∀ v < c.max_vars, mrk'[v]?.getD 0#8 = 0#8)
    (hws1 : ws1'.length = 2 * c.max_vars) (hws2 : ws2'.length = 2 * c.max_vars) :
    let s' : FullState :=
      { s with
        core := { s.core with mrk := mrk' }
        scratch := { s.scratch with work_stk1 := ws1', work_stk2 := ws2', res_sz := rsz' } }
    FullSparseInv c F0 s' ∧ FullWitnessInv c F0 F_cur s'.core := by
  intro s'
  let hw' : FullWitnessInv c F0 F_cur s'.core :=
    { hw with
      arena := { hw.arena with len_ok := hw.arena.len_ok }
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }
  have hlen' : s'.LengthsOk c :=
    ⟨{ hsp.1.lengths.core_ok with mrk_len := hmrk },
     { hsp.1.lengths.scratch_ok with work_stk1_len := hws1, work_stk2_len := hws2 }⟩
  exact ⟨⟨⟨hlen', F_cur, hw'⟩, ⟨hmrk_clr, hsp.2.1.2⟩, hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2⟩,
    hw'⟩

theorem viv_sparse_with_rr {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) {rr' : List (BitVec 32)} (hrr : rr'.length = c.red_cap) :
    FullSparseInv c F0 { s with scratch := { s.scratch with red_refs := rr' } } :=
  ⟨⟨⟨h.1.lengths.core_ok, { h.1.lengths.scratch_ok with red_refs_len := hrr }⟩, h.1.witness⟩,
   h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem viv_sparse_with_tr {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) {tr' : List (BitVec 32)} (htr : tr'.length = 2 * c.max_vars) :
    FullSparseInv c F0 { s with scratch := { s.scratch with tarjan_reach := tr' } } :=
  ⟨⟨⟨h.1.lengths.core_ok, { h.1.lengths.scratch_ok with tarjan_reach_len := htr }⟩, h.1.witness⟩,
   h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem viv_sparse_with_rr_scr {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) {rr' scr' : List (BitVec 32)} (hrr : rr'.length = c.red_cap)
    (hscr : scr'.length = c.scratch_cap) :
    FullSparseInv c F0
      { s with scratch := { s.scratch with red_refs := rr', scratch_buf := scr' } } :=
  ⟨⟨⟨h.1.lengths.core_ok,
      { h.1.lengths.scratch_ok with red_refs_len := hrr, scratch_buf_len := hscr }⟩,
    h.1.witness⟩, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem viv_sparse_with_res_sz {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) (rsz : BitVec 64) :
    FullSparseInv c F0 { s with scratch := { s.scratch with res_sz := rsz } } :=
  ⟨⟨⟨h.1.lengths.core_ok, { h.1.lengths.scratch_ok with }⟩, h.1.witness⟩,
   h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem viv_sparse_with_tier1 {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) (t1 : BitVec 64) :
    FullSparseInv c F0 { s with scratch := { s.scratch with tier1 := t1 } } :=
  ⟨⟨⟨h.1.lengths.core_ok, { h.1.lengths.scratch_ok with }⟩, h.1.witness⟩,
   h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem viv_sparse_with_tier2 {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) (t2 : BitVec 64) :
    FullSparseInv c F0 { s with scratch := { s.scratch with tier2 := t2 } } :=
  ⟨⟨⟨h.1.lengths.core_ok, { h.1.lengths.scratch_ok with }⟩, h.1.witness⟩,
   h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem viv_sparse_of_core_eq {c : FullCfg} {F0 : CNF Nat} {s s' : FullState}
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

theorem viv_sparse_of_backtrack {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) {target_lvl : Nat}
    {lvl' rsns' trl' tp' : List (BitVec 32)} {vals8' : List (BitVec 8)}
    {te' prop' cl' : Nat} {unass' : BitVec 64} {sc' : FullScratch}
    (htle : target_lvl ≤ s.core.cur_level)
    (hlen' : ({ s with
      core := { s.core with vals := vals8', lvl := lvl', rsns := rsns', trl := trl',
                            trail_pos := tp', trail_end := te', propagated := prop',
                            cur_level := cl', unassigned := unass' }
      scratch := sc' } : FullState).LengthsOk c)
    (hpres : FullProbeScratchPres s { s with scratch := sc' })
    (hw_bt : ∀ F_cur, FullWitnessInv c F0 F_cur s.core → target_lvl ≤ s.core.cur_level →
      FullWitnessInv c F0 F_cur
        { s.core with vals := vals8', lvl := lvl', rsns := rsns', trl := trl',
                      trail_pos := tp', trail_end := te', propagated := prop',
                      cur_level := cl', unassigned := unass' }) :
    FullSparseInv c F0
      { s with
        core := { s.core with vals := vals8', lvl := lvl', rsns := rsns', trl := trl',
                              trail_pos := tp', trail_end := te', propagated := prop',
                              cur_level := cl', unassigned := unass' }
        scratch := sc' } := by
  obtain ⟨F_cur, hw⟩ := h.1.witness
  have hw' := hw_bt F_cur hw htle
  refine ⟨⟨hlen', F_cur, hw'⟩, h.2.1, h.2.2.1,
    ⟨fun i hi => by dsimp only [FullLastLearnedWf]; rw [hpres.1.1]; exact h.2.2.2.1.1 i hi,
     by rw [hpres.1.2]; exact h.2.2.2.1.2⟩, h.2.2.2.2⟩

theorem viv_sparseW_of_backtrack {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullSparseInvW c F0 F_cur s) {target_lvl : Nat}
    {vals8' : List (BitVec 8)} {lvl' rsns' trl' tp' : List (BitVec 32)}
    {te' prop' cl' : Nat} {unass' : BitVec 64} {sc' : FullScratch}
    (_htle : target_lvl ≤ s.core.cur_level)
    (hlen' : ({ s with
      core := { s.core with vals := vals8', lvl := lvl', rsns := rsns', trl := trl',
                            trail_pos := tp', trail_end := te', propagated := prop',
                            cur_level := cl', unassigned := unass' }
      scratch := sc' } : FullState).LengthsOk c)
    (hpres : FullProbeScratchPres s { s with scratch := sc' })
    (hw' : FullWitnessInv c F0 F_cur
      { s.core with vals := vals8', lvl := lvl', rsns := rsns', trl := trl',
                    trail_pos := tp', trail_end := te', propagated := prop',
                    cur_level := cl', unassigned := unass' }) :
    FullSparseInvW c F0 F_cur
      { s with
        core := { s.core with vals := vals8', lvl := lvl', rsns := rsns', trl := trl',
                              trail_pos := tp', trail_end := te', propagated := prop',
                              cur_level := cl', unassigned := unass' }
        scratch := sc' } :=
  ⟨hlen', hw', h.2.2.1, h.2.2.2.1,
   ⟨fun i hi => by dsimp only [FullLastLearnedWf]; rw [hpres.1.1]; exact h.2.2.2.2.1.1 i hi,
    by rw [hpres.1.2]; exact h.2.2.2.2.1.2⟩, h.2.2.2.2.2⟩

theorem viv_sparseInvW_of_prop_canon {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s_vc : FullState} {vals_p : List (BitVec 8)}
    {flags_p lvl_p rsns_p trl_p tp_p : List (BitVec 32)}
    {te_p prop_p : Nat} {unass_p unfl_p : BitVec 64} {wvec_p arena_p wstk_p : List (BitVec 32)}
    {wlen_p : Nat} {wu_p fuel_p ctype_p cref_p c0_p c1_p oom_p : BitVec 64} {sc_p : FullScratch}
    (hsw_vc : FullSparseInvW c F0 F_cur s_vc)
    (hlen_p : ({ s_vc with
      core := { s_vc.core with
        vals := vals_p, flags := flags_p, lvl := lvl_p, rsns := rsns_p, trl := trl_p,
        trail_pos := tp_p, trail_end := te_p, propagated := prop_p, unassigned := unass_p,
        unflushed := unfl_p, wvec := wvec_p, arena := arena_p, wstk := wstk_p, wlen := wlen_p,
        wusable := wu_p, fuel := fuel_p, confl_type := ctype_p, confl_ref := cref_p,
        confl_lit0 := c0_p, confl_lit1 := c1_p, oom := oom_p }
      scratch := sc_p } : FullState).LengthsOk c)
    (hw_p : FullWitnessInv c F0 F_cur { s_vc.core with
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
    (hpr_sc_p : FullProbeScratchPres { s_vc with scratch := { s_vc.scratch with
      search_ticks := sc_p.search_ticks, wsort := sc_p.wsort,
      phases := sc_p.phases, delayed := sc_p.delayed } } { s_vc with
      core := { s_vc.core with
        vals := vals_p, flags := flags_p, lvl := lvl_p, rsns := rsns_p, trl := trl_p,
        trail_pos := tp_p, trail_end := te_p, propagated := prop_p, unassigned := unass_p,
        unflushed := unfl_p, wvec := wvec_p, arena := arena_p, wstk := wstk_p, wlen := wlen_p,
        wusable := wu_p, fuel := fuel_p, confl_type := ctype_p, confl_ref := cref_p,
        confl_lit0 := c0_p, confl_lit1 := c1_p, oom := oom_p }
      scratch := sc_p }) :
    FullSparseInvW c F0 F_cur { s_vc with
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
  have hnd_p : FullArenaVarsNodup s_p := fun ref href hng => by
    have href0 : ref ∈ fullArenaClauseRefsCore s_vc.core := hperm_p.2.1 ▸ href
    obtain ⟨_, hgb, hp⟩ := hperm_p.2.2 ref href0
    exact (hp.map (· / 2)).nodup_iff.mpr (hsw_vc.2.2.2.1 ref href0 (hgb.symm.trans hng))
  have hrefs_p : ∀ ref ∈ fullArenaClauseRefs s_vc, ref ∈ fullArenaClauseRefs s_p := fun ref hr =>
    by change ref ∈ fullArenaClauseRefsCore s_p.core; rw [hperm_p.2.1]; exact hr
  refine ⟨hlen_p, hw_p, hsw_vc.2.2.1, hnd_p,
    ⟨fun i hi => by
       dsimp only [FullLastLearnedWf]; rw [hpr_sc_p.1.1]
       rcases hsw_vc.2.2.2.2.1.1 i hi with hff | hmem
       · exact Or.inl hff
       · exact Or.inr (hrefs_p _ hmem),
     by rw [hpr_sc_p.1.2]; exact hsw_vc.2.2.2.2.1.2⟩,
    hsw_vc.2.2.2.2.2⟩

/-! ## 2. Nodup & Arena Block Helpers -/

theorem viv_nodup_map_inj_on {α β : Type} {f : α → β} :
    ∀ l : List α, l.Nodup → (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) → (l.map f).Nodup
  | [], _, _ => .nil
  | a :: l, hnd, hinj => by
    have ⟨han, hndl⟩ := List.nodup_cons.mp hnd
    refine List.nodup_cons.mpr ⟨fun hm => ?_,
      viv_nodup_map_inj_on l hndl fun x hx y hy => hinj x (by simp [hx]) y (by simp [hy])⟩
    obtain ⟨b, hb, hfb⟩ := List.mem_map.mp hm
    exact han ((hinj b (by simp [hb]) a (by simp) hfb) ▸ hb)

theorem viv_nodup_lt_length_le :
    ∀ (l : List Nat) (n : Nat), l.Nodup → (∀ x ∈ l, x < n) → l.length ≤ n
  | [], _, _, _ => Nat.zero_le _
  | a :: _, 0, _, h => absurd (h a (by simp)) (by omega)
  | a :: l, n + 1, hnd, h => by
    have ha := h a (by simp)
    have ⟨han, hndl⟩ := List.nodup_cons.mp hnd
    by_cases htop : a = n
    · have hl := viv_nodup_lt_length_le l n hndl fun x hx => by
        have := h x (by simp [hx]); have : x ≠ a := fun e => han (e ▸ hx); omega
      simp [hl]
    · let l' := l.map fun x => if x = n then a else x
      have hnd' : l'.Nodup := by
        refine viv_nodup_map_inj_on l hndl fun x hx y hy heq => ?_
        by_cases hxn : x = n <;> by_cases hyn : y = n <;> simp only [hxn, hyn, ↓reduceIte] at heq
        · rw [hxn, hyn]
        · exact absurd (heq ▸ hy) han
        · exact absurd (heq.symm ▸ hx) han
        · exact heq
      have hlt' : ∀ y ∈ l', y < n := by
        intro y hy; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
        by_cases hxn : x = n
        · simp only [hxn, ↓reduceIte]; omega
        · simp only [hxn, ↓reduceIte]; have := h x (by simp [hx]); omega
      have hl' := viv_nodup_lt_length_le l' n hnd' hlt'
      simp only [l', List.length_map] at hl'
      simp only [List.length_cons]; omega

theorem viv_queue_missing_lt {n m x : Nat} {xs : List (BitVec 32)}
    (hm : m ≤ xs.length) (hlt : ∀ i < m, (xs[i]?.getD 0#32).toNat < n)
    (hnd : ((xs.take m).map BitVec.toNat).Nodup) (hx : x < n)
    (hmiss : ∀ i < m, (xs[i]?.getD 0#32).toNat ≠ x) : m < n := by
  refine inj_lt_of_missing (fun i => (xs[i]?.getD 0#32).toNat) (fun i j hi hj heq => ?_) hlt
    hx hmiss
  have hlen : ((xs.take m).map BitVec.toNat).length = m := by
    rw [List.length_map, List.length_take]; omega
  have hpw := List.pairwise_iff_getElem.mp hnd
  rw [← hlen] at hi hj
  by_cases hne : i = j
  · exact hne
  · rcases Nat.lt_or_gt_of_ne hne with hlt_ij | hgt_ij
    · exact absurd (by
        simp only [List.getElem_map, List.getElem_take]
        rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at heq
        exact heq) (hpw i j hi hj hlt_ij)
    · exact absurd (by
        simp only [List.getElem_map, List.getElem_take]
        rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at heq
        exact heq.symm) (hpw j i hj hi hgt_ij)

theorem viv_nodup_of_strict_subseq {orig sub : List Nat} (hnd : (orig.map (· / 2)).Nodup)
    (idxs : List Nat) (hlen : idxs.length = sub.length) (hp : idxs.Pairwise (· < ·))
    (hbd : ∀ q ∈ idxs, q < orig.length)
    (heq : ∀ (t : Nat) (ht : t < sub.length), sub[t] = orig[idxs[t]?.getD 0]'(by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact hbd _ (by simp))) :
    (sub.map (· / 2)).Nodup := by
  unfold List.Nodup at hnd ⊢; rw [List.pairwise_iff_getElem] at hnd ⊢
  intro i j hi hj hij heqv; simp only [List.length_map, List.getElem_map] at hi hj heqv
  rw [heq i hi, heq j hj] at heqv
  have hid : ∀ t (ht : t < idxs.length), idxs[t]?.getD 0 = idxs[t]'ht := fun t ht => by
    rw [List.getElem?_eq_getElem ht, Option.getD_some]
  exact hnd (idxs[i]'(by omega)) (idxs[j]'(by omega)) (by simp [hbd]) (by simp [hbd])
    (List.pairwise_iff_getElem.mp hp i j (by omega) (by omega) hij)
    (by simpa [List.getElem_map, hid i (by omega), hid j (by omega)] using heqv)

theorem fullArenaClauseLitsCore_length {k : FullCoreState} {r : Nat}
    (hbd : r + 3 + fullArenaClauseSizeCore k r ≤ k.arena.length) :
    (fullArenaClauseLitsCore k r).length = fullArenaClauseSizeCore k r := by
  unfold fullArenaClauseLitsCore; simp [List.length_map, List.length_take, List.length_drop]; omega

theorem fullArenaClauseLitsCore_getElem {k : FullCoreState} {r t : Nat}
    (hbd : r + 3 + fullArenaClauseSizeCore k r ≤ k.arena.length)
    (ht : t < fullArenaClauseSizeCore k r) :
    (fullArenaClauseLitsCore k r)[t]'(by rw [fullArenaClauseLitsCore_length hbd]; exact ht) =
      (k.arena[r + 3 + t]'(by omega)).toNat := by
  unfold fullArenaClauseLitsCore; simp [List.getElem_map, List.getElem_take, List.getElem_drop]

theorem fullArenaClauseLitsCore_eq_map_take {k : FullCoreState} {r nsz : Nat}
    {out : List (BitVec 32)} (hsz : fullArenaClauseSizeCore k r = nsz)
    (hbd : r + 3 + nsz ≤ k.arena.length) (hout_len : nsz ≤ out.length)
    (hget : ∀ j < nsz, k.arena[r + 3 + j]? = out[j]?) :
    fullArenaClauseLitsCore k r = (out.take nsz).map BitVec.toNat := by
  have hbd' : r + 3 + fullArenaClauseSizeCore k r ≤ k.arena.length := hsz ▸ hbd
  refine List.ext_getElem
    (by rw [fullArenaClauseLitsCore_length hbd', hsz, List.length_map, List.length_take]; omega)
    fun t ht1 _ => ?_
  rw [fullArenaClauseLitsCore_length hbd', hsz] at ht1
  rw [fullArenaClauseLitsCore_getElem hbd' (by omega), List.getElem_map, List.getElem_take]
  have hg := hget t ht1; rw [List.getElem?_eq_getElem (by omega),
    List.getElem?_eq_getElem (by omega)] at hg; exact congrArg BitVec.toNat (Option.some.inj hg)

theorem fullArenaClauseSize_le_maxVars {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState}
    (hsp : FullSparseInv c F0 s) (hw : FullWitnessInv c F0 F_cur s.core)
    {cref : Nat} (href : cref ∈ fullArenaClauseRefs s) (hng : fullArenaClauseGarb s cref = false) :
    fullArenaClauseSize s cref ≤ c.max_vars := by
  have hcl := hsp.1.lengths.core_ok
  have hwf := hw.arena.refs_wf cref href
  have hbd : cref + 3 + fullArenaClauseSizeCore s.core cref ≤ s.core.arena.length := by
    have := hcl.arena_len_arr; have := hcl.arena_len_le; omega
  have hlen : (fullArenaClauseLits s cref).length = fullArenaClauseSize s cref := by
    unfold fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSize
    simp [List.length_map, List.length_take, List.length_drop]; omega
  have hnd := hsp.2.2.1 cref href hng
  have hlt : ∀ x ∈ (fullArenaClauseLits s cref).map (· / 2), x < c.max_vars := by
    intro x hx; obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
    have := hw.arena.lits_lt cref href hng l hl; have := hcl.cur_vars_le; omega
  have hl := viv_nodup_lt_length_le _ _ hnd hlt
  rwa [List.length_map, hlen] at hl

/-! ## 3. Arena Header, Shrink, & `PH_GARB` Preservation -/

theorem fullWitnessInv_set_hdr_non_gs {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hlen : k.LengthsOk c) (hw : FullWitnessInv c F0 F_cur k)
    {cref : Nat} (href : cref ∈ fullArenaClauseRefsCore k) (v : BitVec 32)
    (h19 : (v &&& 0x00080000#32) = (fullArenaHdrCore k cref &&& 0x00080000#32))
    (h23 : (v &&& 0x00800000#32) = (fullArenaHdrCore k cref &&& 0x00800000#32)) :
    let k' : FullCoreState := { k with arena := k.arena.set cref v }
    k'.LengthsOk c ∧ fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k ∧
    FullWitnessInv c F0 F_cur k' ∧
    (∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r ∧
      fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r ∧
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r) := by
  intro k'
  have hcref_wf := hw.arena.refs_wf cref href
  have har_len : cref < k.arena.length := by
    have := hlen.arena_len_le; have := hlen.arena_len_arr; omega
  have ha_cref : k'.arena[cref]? = some v := List.getElem?_set_self har_len
  have hne_out : ∀ r ∈ fullArenaClauseRefsCore k, r ≠ cref →
      (r + 3 + fullArenaClauseSizeCore k r ≤ cref ∧
        fullArenaNextOff k.arena k.arena_len r ≤ cref) ∨
      (cref + 3 ≤ fullArenaNextOff k.arena k.arena_len cref ∧
        fullArenaNextOff k.arena k.arena_len cref ≤ r) := fun r hr hne => by
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl ⟨by have := fullArenaScanRefs_disjoint hr href hlt
                       have := (hw.arena.refs_wf r hr).2.2.1; omega,
        fullArenaScanRefs_disjoint hr href hlt⟩
    · exact Or.inr ⟨by omega, fullArenaScanRefs_disjoint href hr hgt⟩
  have hnxt : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaNextOff k'.arena k.arena_len r = fullArenaNextOff k.arena k.arena_len r := by
    intro r hr; by_cases hrc : r = cref
    · subst r
      have h2eq : k'.arena[cref + 2]? = k.arena[cref + 2]? := List.getElem?_set_ne (by omega)
      have h1 : ¬ (cref + 3 > k.arena_len) := by omega
      have h2 : ¬ (cref + 3 + (k.arena[cref + 2]?.getD 0#32).toNat > k.arena_len) := by
        unfold fullArenaClauseSizeCore at hcref_wf; omega
      unfold fullArenaNextOff
      simp only [h1, ↓reduceIte, h2eq, h2, ha_cref, Option.getD_some]
      rw [h23, show fullArenaHdrCore k cref = k.arena[cref]?.getD 0#32 from rfl]
      split
      · exact fullArenaSkipShrk_congr fun i hi _ => List.getElem?_set_ne (by omega)
      · rfl
    · refine fullArenaNextOff_congr_block (List.getElem?_set_ne (Ne.symm hrc)) ?_ ?_
      · rcases hne_out r hr hrc with ⟨_, _⟩ | ⟨_, _⟩
        · have := (hw.arena.refs_wf r hr).2.1; exact List.getElem?_set_ne (by omega)
        · exact List.getElem?_set_ne (by omega)
      · intro i _ _
        rcases hne_out r hr hrc with ⟨_, _⟩ | ⟨_, _⟩
        · exact List.getElem?_set_ne (by omega)
        · have := (hw.arena.refs_wf r hr).2.2.1; exact List.getElem?_set_ne (by omega)
  have hrefs : fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k :=
    fullArenaClauseRefsCore_congr rfl hnxt
  have hsz_eq : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r := fun r hr => by
    unfold fullArenaClauseSizeCore; dsimp only [k']
    by_cases hrc : r = cref
    · subst r; rw [List.getElem?_set_ne (by omega)]
    · rcases hne_out r hr hrc with ⟨_, _⟩ | ⟨_, _⟩
      · have := (hw.arena.refs_wf r hr).2.1; rw [List.getElem?_set_ne (by omega)]
      · rw [List.getElem?_set_ne (by omega)]
  have hgarb_eq : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r := fun r hr => by
    unfold fullArenaClauseGarbCore fullArenaHdrCore; dsimp only [k']
    by_cases hrc : r = cref
    · subst r; rw [List.getElem?_set_self har_len, Option.getD_some, h19]; rfl
    · rw [List.getElem?_set_ne (Ne.symm hrc)]
  have hlits_eq : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r := fun r hr => by
    have _ := hw.arena.refs_wf r hr
    have hk_bd : r + 3 + fullArenaClauseSizeCore k r ≤ k.arena.length := by
      have := hlen.arena_len_le; have := hlen.arena_len_arr; omega
    refine fullArenaClauseLitsCore_eq_of_hold hk_bd (by simpa [k'] using hk_bd) (hsz_eq r hr) ?_
    intro j _; dsimp only [k']; apply List.getElem?_set_ne
    by_cases hrc : r = cref
    · subst r; omega
    · rcases hne_out r hr hrc with ⟨h1, _⟩ | ⟨_, h2⟩ <;> omega
  have harena' : FullArenaClausesInv c F_cur k' := by
    refine ⟨hw.arena.len_ok, ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs] at hr; dsimp only [k'] at hnxt ⊢
      rw [hnxt r hr, hsz_eq r hr]; exact hw.arena.refs_wf r hr
    · intro r hr hsh; rw [hrefs] at hr
      have hsh0 : (fullArenaHdrCore k r &&& 0x00800000#32) ≠ 0#32 := by
        by_cases hrc : r = cref
        · subst r; unfold fullArenaHdrCore at hsh h23 ⊢; simpa [ha_cref, h23] using hsh
        · unfold fullArenaHdrCore at hsh ⊢
          simpa [k', List.getElem?_set_ne (Ne.symm hrc)] using hsh
      obtain ⟨t, ht1, ht2, hsent⟩ := hw.arena.shrk_term r hr hsh0
      have hget_r : k.arena[r]? = some (fullArenaHdrCore k r) := by
        have _ := (hw.arena.refs_wf r hr).1
        have : r < k.arena.length := by
          have := hlen.arena_len_le; have := hlen.arena_len_arr; omega
        unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem this, Option.getD_some]
      obtain ⟨t0, ht0_lo, _, _, ht0_sent⟩ :=
        fullArenaNextOff_hits_sentinel (hw.arena.refs_wf r hr).1
          (by rw [hget_r, Option.getD_some]; exact hsh0) ht1 ht2 hsent
      have ht0_ne : t0 ≠ cref := by
        by_cases hrc : r = cref
        · subst r; have := (hw.arena.refs_wf cref hr).2.1; omega
        · rcases hne_out r hr hrc with ⟨_, _⟩ | ⟨_, _⟩
          · omega
          · have := (hw.arena.refs_wf r hr).2.1; omega
      have hnxt_le : fullArenaNextOff k.arena k.arena_len r ≤ k.arena_len :=
        (hw.arena.refs_wf r hr).2.2.2.1
      refine ⟨t0, by rw [hsz_eq r hr]; exact ht0_lo, by dsimp only [k']; omega, ?_⟩
      dsimp only [k']; rw [List.getElem?_set_ne ht0_ne.symm]; exact ht0_sent
    · intro r hr hng l hl; rw [hrefs] at hr
      rw [hgarb_eq r hr] at hng; rw [hlits_eq r hr] at hl
      exact hw.arena.lits_lt r hr hng l hl
    · intro r hr hng; rw [hrefs] at hr
      rw [hgarb_eq r hr] at hng; rw [hlits_eq r hr]
      exact hw.arena.entails r hr hng
  refine ⟨{ hlen with arena_len_arr := by simp [k', hlen.arena_len_arr] }, hrefs,
    { hw with
      arena := harena'
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hrefs ▸ hr)
      reason_inv := fun idx hidx hne => by
        have hrs := hw.reason_inv idx hidx hne
        dsimp only [k'] at hrs ⊢
        by_cases hbin : (k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD
            0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32
        · rw [ite_eq_left hbin] at hrs ⊢; exact hrs
        · rw [ite_eq_right hbin] at hrs ⊢
          let r := (k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat
          exact ⟨hrefs ▸ hrs.1, (hgarb_eq r hrs.1).trans hrs.2.1,
            fun q hq => hrs.2.2 q ((hlits_eq r hrs.1) ▸ hq)⟩
      reason_lit_mem := fun idx hidx hne hlg => by
        have hrs := hw.reason_inv idx hidx hne
        have hbf : ¬ (k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD
            0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 := fun h => absurd hlg h
        rw [ite_eq_right hbf] at hrs
        dsimp only [k']
        rw [hlits_eq _ hrs.1]
        exact hw.reason_lit_mem idx hidx hne hlg },
    fun r hr => ⟨hgarb_eq r hr, hsz_eq r hr, hlits_eq r hr⟩⟩

theorem fullSparseInvW_set_hdr_non_gs {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    {cref : Nat} (href : cref ∈ fullArenaClauseRefs s) (v : BitVec 32)
    (ni' nr' : BitVec 64)
    (h19 : (v &&& 0x00080000#32) = (fullArenaHdr s cref &&& 0x00080000#32))
    (h23 : (v &&& 0x00800000#32) = (fullArenaHdr s cref &&& 0x00800000#32)) :
    let s' : FullState :=
      { s with core :=
        { s.core with arena := s.core.arena.set cref v,
                      num_irred := ni', num_redundant := nr' } }
    FullSparseInvW c F0 F_cur s' ∧ fullArenaClauseRefs s' = fullArenaClauseRefs s ∧
    (∀ r ∈ fullArenaClauseRefs s,
      fullArenaClauseGarb s' r = fullArenaClauseGarb s r ∧
      fullArenaClauseSize s' r = fullArenaClauseSize s r ∧
      fullArenaClauseLits s' r = fullArenaClauseLits s r) := by
  intro s'
  obtain ⟨hlen_c, hrefs, hw', hall⟩ :=
    fullWitnessInv_set_hdr_non_gs hsp.1.core_ok hsp.2.1 href v h19 h23
  have hlen' : s'.LengthsOk c := ⟨{ hlen_c with }, hsp.1.scratch_ok⟩
  have hw_s' : FullWitnessInv c F0 F_cur s'.core :=
    { hw' with
      arena := { hw'.arena with len_ok := hw'.arena.len_ok }
      watches := hw'.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }
  have hrefs' : fullArenaClauseRefs s' = fullArenaClauseRefs s := hrefs
  have hnd' : FullArenaVarsNodup s' := fun r hr hng => by
    have hr0 : r ∈ fullArenaClauseRefs s := hrefs' ▸ hr
    obtain ⟨hg, _, hl⟩ := hall r hr0
    have hl' : fullArenaClauseLits s' r = fullArenaClauseLits s r := hl
    have hg' : fullArenaClauseGarb s' r = fullArenaClauseGarb s r := hg
    rw [hl']; exact hsp.2.2.2.1 r hr0 (hg'.symm.trans hng)
  have hext' : FullExtScratchOk c s' :=
    ⟨fun i hi => (hsp.2.2.2.2.1.1 i hi).imp id (fun h => hrefs' ▸ h), hsp.2.2.2.2.1.2⟩
  exact ⟨⟨hlen', hw_s', hsp.2.2.1, hnd', hext', hsp.2.2.2.2.2⟩, hrefs', hall⟩

theorem fullArena_setHdr_preserves_sparseW {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s) {cref : Nat}
    (href : cref ∈ fullArenaClauseRefs s) {hdr' : BitVec 32}
    (hgarb : (hdr' &&& 0x00080000#32) = (fullArenaHdr s cref &&& 0x00080000#32))
    (hshrk : (hdr' &&& 0x00800000#32) = (fullArenaHdr s cref &&& 0x00800000#32)) :
    let s' : FullState := { s with core := { s.core with arena := s.core.arena.set cref hdr' } }
    FullSparseInvW c F0 F_cur s' ∧ fullArenaClauseRefs s' = fullArenaClauseRefs s ∧
    (∀ r ∈ fullArenaClauseRefs s,
      fullArenaClauseSize s' r = fullArenaClauseSize s r ∧
      fullArenaClauseGarb s' r = fullArenaClauseGarb s r ∧
      fullArenaClauseLits s' r = fullArenaClauseLits s r) := by
  obtain ⟨hsp', hrefs', hall⟩ :=
    fullSparseInvW_set_hdr_non_gs hsp href hdr' s.core.num_irred s.core.num_redundant hgarb hshrk
  exact ⟨hsp', hrefs', fun r hr =>
    let ⟨hg, hsz, hl⟩ := hall r hr
    ⟨hsz, hg, hl⟩⟩

private theorem fullArenaSkipShrk_step_range_m6 {ar : List (BitVec 32)} {alen : Nat} :
    ∀ {p q : Nat}, p ≤ q → q ≤ alen →
      (∀ k, p ≤ k → k < q → ar[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32) →
      fullArenaSkipShrk ar alen p (alen - p) = fullArenaSkipShrk ar alen q (alen - q) := by
  suffices h : ∀ d p q, p + d = q → q ≤ alen →
      (∀ k, p ≤ k → k < q → ar[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32) →
      fullArenaSkipShrk ar alen p (alen - p) = fullArenaSkipShrk ar alen q (alen - q) from
    fun {p q} hle hqa hne => h (q - p) p q (by omega) hqa hne
  intro d; induction d with
  | zero => intro p q hpq _ _; rw [show p = q by omega]
  | succ d ih =>
    intro p q hpq hqa hne
    have hpa : p < alen := by omega
    have hf : alen - p = (alen - (p + 1)) + 1 := by omega
    have hnep : ar[p]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := hne p (Nat.le_refl p) (by omega)
    have hstep1 : ∀ f, fullArenaSkipShrk ar alen p (f + 1) =
        fullArenaSkipShrk ar alen (p + 1) f := fun f => by simp [fullArenaSkipShrk, hpa, hnep]
    rw [hf, hstep1]
    exact ih (p + 1) q (by omega) hqa fun k hk1 hk2 => hne k (by omega) hk2

theorem inPlaceShrink_hnonact_preserves_fullWitness {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState}
    (hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    {cref nsz : Nat} (href : cref ∈ fullArenaClauseRefs s)
    (hnonact : NonActiveReason s.core cref)
    (hng : fullArenaClauseGarb s cref = false)
    (hnsz3 : 3 ≤ nsz) (hnsz_lt : nsz < fullArenaClauseSize s cref)
    {arena' : List (BitVec 32)} {ni' nr' : BitVec 64} {sc' : FullScratch}
    (hal' : arena'.length = c.arena_cap) (hsc' : sc'.LengthsOk c)
    (hout : ∀ k, (k < cref ∨ cref + 3 + fullArenaClauseSize s cref ≤ k) →
      arena'[k]? = s.core.arena[k]?)
    (hnhdr_garb : (arena'[cref]?.getD 0#32 &&& 0x00080000#32) = 0#32)
    (hnhdr_shrk : (arena'[cref]?.getD 0#32 &&& 0x00800000#32) ≠ 0#32)
    (hnsz_eq : (arena'[cref + 2]?.getD 0#32).toNat = nsz)
    (hpad_old : M6ShrkPad arena' s.core.arena cref (fullArenaClauseSize s cref) nsz)
    (hlits_lt : ∀ j < nsz, (arena'[cref + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (fullArenaClauseLitsCore { s.core with arena := arena' } cref))) :
    let s' : FullState :=
      { s with
        core := { s.core with arena := arena', num_irred := ni', num_redundant := nr' }
        scratch := sc' }
    s'.LengthsOk c ∧ FullWitnessInv c F0 F_cur s'.core ∧
    fullArenaClauseRefs s' = fullArenaClauseRefs s ∧
    fullArenaClauseGarb s' cref = false ∧ fullArenaClauseSize s' cref = nsz ∧
    (∀ r ∈ fullArenaClauseRefs s,
      fullArenaNextOff s'.core.arena s.core.arena_len r =
        fullArenaNextOff s.core.arena s.core.arena_len r) := by
  intro s'
  dsimp only [fullArenaClauseRefs, fullArenaClauseSize, fullArenaClauseGarb,
    fullArenaClauseLits, fullArenaHdr, M6ShrkPad] at *
  have hcl := hlen.core_ok
  have hcref_wf := hw.arena.refs_wf cref href
  have hold_bd : cref + 3 + fullArenaClauseSizeCore s.core cref ≤ s.core.arena.length := by
    have := hcl.arena_len_arr; have := hcl.arena_len_le; omega
  have hold_ne_ff : ∀ k, cref + 3 ≤ k → k < cref + 3 + fullArenaClauseSizeCore s.core cref →
      s.core.arena[k]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
    intro k hk1 hk2
    let j := k - (cref + 3)
    have hj : j < fullArenaClauseSizeCore s.core cref := by omega
    have hmem : (s.core.arena[cref + 3 + j]'(by omega)).toNat ∈
        fullArenaClauseLitsCore s.core cref :=
      (mem_fullArenaClauseLitsCore_iff hold_bd).mpr ⟨j, hj, rfl⟩
    have hlt := hw.arena.lits_lt cref href hng _ hmem
    have hcv := hcl.cur_vars_le; have hmax := c.hmaxv; unfold dimacsBound at hmax
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    intro heq
    have h1 : (s.core.arena[cref + 3 + j]'(by omega)).toNat = 0xFFFFFFFF := by
      have hidx_eq : cref + 3 + j = k := by omega
      simp only [hidx_eq, heq]; rfl
    omega
  have hnxt_cref : fullArenaNextOff arena' s.core.arena_len cref =
      fullArenaNextOff s.core.arena s.core.arena_len cref := by
    have h1 : ¬ (cref + 3 > s.core.arena_len) := by omega
    have h2 : ¬ (cref + 3 + (s.core.arena[cref + 2]?.getD 0#32).toNat > s.core.arena_len) := by
      unfold fullArenaClauseSizeCore at hcref_wf; omega
    have h2n : ¬ (cref + 3 + nsz > s.core.arena_len) := by omega
    unfold fullArenaNextOff
    simp only [h1, h2, hnhdr_shrk, hnsz_eq, h2n, ↓reduceIte, ne_eq, not_false_eq_true]
    by_cases hsh0 : (s.core.arena[cref]?.getD 0#32 &&& 0x00800000#32) = 0#32
    · rw [ite_eq_left hsh0] at hpad_old
      obtain ⟨hkeep, hterm⟩ := hpad_old
      have hsh0' : ¬ ((s.core.arena[cref]?.getD 0#32 &&& 0x00800000#32) ≠ 0#32) := by
        simpa using hsh0
      rw [ite_eq_right hsh0']
      have hstep := fullArenaSkipShrk_step_range_m6 (ar := arena') (alen := s.core.arena_len)
        (p := cref + 3 + nsz) (q := cref + 3 + fullArenaClauseSizeCore s.core cref - 1)
        (by omega) (by omega) fun k hk1 hk2 => by
          rw [hkeep k hk1 hk2]; exact hold_ne_ff k (by omega) (by omega)
      rw [hstep]
      have hfl : s.core.arena_len - (cref + 3 + fullArenaClauseSizeCore s.core cref - 1) =
          (s.core.arena_len - (cref + 3 + fullArenaClauseSizeCore s.core cref)) + 1 := by omega
      have hlt_a : cref + 3 + fullArenaClauseSizeCore s.core cref - 1 < s.core.arena_len := by
        omega
      rw [hfl]; unfold fullArenaSkipShrk
      simp only [hlt_a, hterm, Option.getD_some, ↓reduceIte, ne_eq, not_true_eq_false]
      have hsz_def : fullArenaClauseSizeCore s.core cref =
          (s.core.arena[cref + 2]?.getD 0#32).toNat := rfl
      omega
    · rw [ite_eq_right hsh0] at hpad_old
      rw [ite_eq_left hsh0]
      have hstep := fullArenaSkipShrk_step_range_m6 (ar := arena') (alen := s.core.arena_len)
        (p := cref + 3 + nsz) (q := cref + 3 + fullArenaClauseSizeCore s.core cref)
        (by omega) (by omega) fun k hk1 hk2 => by
          rw [hpad_old k hk1 hk2]; exact hold_ne_ff k (by omega) hk2
      rw [hstep]
      exact fullArenaSkipShrk_congr fun k hk1 _ => hout k (Or.inr hk1)
  have hne_out : ∀ r ∈ fullArenaClauseRefsCore s.core, r ≠ cref →
      (r + 3 + fullArenaClauseSizeCore s.core r ≤ cref ∧
        fullArenaNextOff s.core.arena s.core.arena_len r ≤ cref) ∨
      (cref + 3 + fullArenaClauseSizeCore s.core cref ≤ r) := fun r hr hne => by
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl ⟨by have := fullArenaScanRefs_disjoint hr href hlt
                       have := (hw.arena.refs_wf r hr).2.2.1; omega,
        fullArenaScanRefs_disjoint hr href hlt⟩
    · exact Or.inr (by have := fullArenaScanRefs_disjoint href hr hgt; omega)
  have hnxt : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaNextOff arena' s.core.arena_len r =
        fullArenaNextOff s.core.arena s.core.arena_len r := by
    intro r hr; by_cases hrc : r = cref
    · subst r; exact hnxt_cref
    · rcases hne_out r hr hrc with ⟨_, hle⟩ | hge
      · refine fullArenaNextOff_congr_block (hout r (Or.inl (by omega)))
          (hout (r + 2) (Or.inl (by have := (hw.arena.refs_wf r hr).2.1; omega)))
          fun k _ hk2 => hout k (Or.inl (by omega))
      · refine fullArenaNextOff_congr_block (hout r (Or.inr hge))
          (hout (r + 2) (Or.inr (by omega)))
          fun k hk1 _ => hout k (Or.inr (by omega))
  have hrefs : fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s.core :=
    fullArenaClauseRefsCore_congr rfl hnxt
  have hoth_eq : ∀ r ∈ fullArenaClauseRefsCore s.core, r ≠ cref →
      fullArenaClauseGarbCore s'.core r = fullArenaClauseGarbCore s.core r ∧
      fullArenaClauseSizeCore s'.core r = fullArenaClauseSizeCore s.core r ∧
      fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s.core r := by
    intro r hr hne
    have hr_wf := hw.arena.refs_wf r hr
    have hr_bd : r + 3 + fullArenaClauseSizeCore s.core r ≤ s.core.arena.length := by
      have := hcl.arena_len_arr; have := hcl.arena_len_le; omega
    have hout_r : ∀ p, r ≤ p → p < r + 3 + fullArenaClauseSizeCore s.core r →
        arena'[p]? = s.core.arena[p]? := fun p _ _ => by
      rcases hne_out r hr hne with ⟨hlt, _⟩ | hge
      · exact hout p (Or.inl (by omega))
      · exact hout p (Or.inr (by omega))
    have hgb : fullArenaClauseGarbCore s'.core r = fullArenaClauseGarbCore s.core r := by
      unfold fullArenaClauseGarbCore fullArenaHdrCore; dsimp only [s']
      rw [hout_r r (by omega) (by omega)]
    have hsz : fullArenaClauseSizeCore s'.core r = fullArenaClauseSizeCore s.core r := by
      unfold fullArenaClauseSizeCore; dsimp only [s']
      rw [hout_r (r + 2) (by omega) (by omega)]
    have hlits := fullArenaClauseLitsCore_eq_of_hold hr_bd
      (by rw [hal', ← hcl.arena_len_arr]; exact hr_bd) hsz
      fun j hj => hout_r (r + 3 + j) (by omega) (by omega)
    exact ⟨hgb, hsz, hlits⟩
  have hgarb_c : fullArenaClauseGarbCore s'.core cref = false := by
    unfold fullArenaClauseGarbCore fullArenaHdrCore; dsimp only [s']; simp [hnhdr_garb]
  have hsz_c : fullArenaClauseSizeCore s'.core cref = nsz := hnsz_eq
  have harena' : FullArenaClausesInv c F_cur s'.core := by
    refine ⟨hw.arena.len_ok, ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs] at hr; dsimp only [s'] at hnxt ⊢
      rw [hnxt r hr]
      by_cases hrc : r = cref
      · subst r; rw [hsz_c]; exact ⟨hcref_wf.1, hnsz3, by omega, hcref_wf.2.2.2.1, hcref_wf.2.2.2.2⟩
      · rw [(hoth_eq r hr hrc).2.1]; exact hw.arena.refs_wf r hr
    · intro r hr hsh; rw [hrefs] at hr
      by_cases hrc : r = cref
      · subst r
        by_cases hsh0 : (s.core.arena[cref]?.getD 0#32 &&& 0x00800000#32) = 0#32
        · rw [ite_eq_left hsh0] at hpad_old
          have := hcref_wf.2.2.1; have := hcref_wf.2.2.2.1
          exact ⟨cref + 3 + fullArenaClauseSizeCore s.core cref - 1,
            by rw [hsz_c]; omega, by dsimp only [s']; omega, hpad_old.2⟩
        · have hsh0' : (fullArenaHdrCore s.core cref &&& 0x00800000#32) ≠ 0#32 := hsh0
          obtain ⟨t, ht1, ht2, hsent⟩ := hw.arena.shrk_term cref hr hsh0'
          refine ⟨t, by rw [hsz_c]; omega, ht2, ?_⟩
          dsimp only [s']; rw [hout t (Or.inr ht1)]; exact hsent
      · have hr_wf := hw.arena.refs_wf r hr
        have hsh0 : (fullArenaHdrCore s.core r &&& 0x00800000#32) ≠ 0#32 := by
          unfold fullArenaHdrCore at hsh ⊢; dsimp only [s'] at hsh
          rcases hne_out r hr hrc with ⟨_, _⟩ | hge
          · rwa [hout r (Or.inl (by omega))] at hsh
          · rwa [hout r (Or.inr hge)] at hsh
        obtain ⟨t, ht1, ht2, hsent⟩ := hw.arena.shrk_term r hr hsh0
        have hget_r : s.core.arena[r]? = some (fullArenaHdrCore s.core r) := by
          have : r < s.core.arena.length := by
            have := hcl.arena_len_le; have := hcl.arena_len_arr; omega
          unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem this, Option.getD_some]
        obtain ⟨t0, ht0_lo, _, ht0_nxt, ht0_sent⟩ :=
          fullArenaNextOff_hits_sentinel hr_wf.1
            (by rw [hget_r, Option.getD_some]; exact hsh0) ht1 ht2 hsent
        have hr_nxt_le := hr_wf.2.2.2.1
        refine ⟨t0, by rw [(hoth_eq r hr hrc).2.1]; exact ht0_lo, by dsimp only [s']; omega, ?_⟩
        dsimp only [s']
        rcases hne_out r hr hrc with ⟨_, _⟩ | hge
        · rw [hout t0 (Or.inl (by omega))]; exact ht0_sent
        · rw [hout t0 (Or.inr (by omega))]; exact ht0_sent
    · intro r hr hngr l hl; rw [hrefs] at hr
      by_cases hrc : r = cref
      · subst r
        have hbd' : cref + 3 + fullArenaClauseSizeCore s'.core cref ≤ s'.core.arena.length := by
          rw [hsz_c]; dsimp only [s']; rw [hal']; have := hcl.arena_len_le
          have := hcref_wf.2.2.1; have := hcref_wf.2.2.2.1; omega
        obtain ⟨j, hj, hjl⟩ := (mem_fullArenaClauseLitsCore_iff hbd').mp hl
        rw [hsz_c] at hj
        have hlt := hlits_lt j hj
        have hjl_bd : cref + 3 + j < arena'.length := by
          rw [hsz_c] at hbd'; dsimp only [s'] at hbd'; omega
        rw [List.getElem?_eq_getElem hjl_bd, Option.getD_some] at hlt
        exact hjl ▸ hlt
      · obtain ⟨hg, _, hli⟩ := hoth_eq r hr hrc
        exact hw.arena.lits_lt r hr (hg ▸ hngr) l (hli ▸ hl)
    · intro r hr hngr; rw [hrefs] at hr
      by_cases hrc : r = cref
      · subst r; exact hent
      · obtain ⟨hg, _, hli⟩ := hoth_eq r hr hrc
        rw [hli]; exact hw.arena.entails r hr (hg ▸ hngr)
  have hlen' : s'.LengthsOk c := ⟨{ hcl with arena_len_arr := by simp [s', hal'] }, hsc'⟩
  refine ⟨hlen', { hw with
    arena := harena'
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hrefs ▸ hr)
    reason_inv := fun idx hidx hne => by
      have hrs := hw.reason_inv idx hidx hne
      dsimp only [s'] at hrs ⊢
      by_cases hbin : (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32
      · rw [ite_eq_left hbin] at hrs ⊢; exact hrs
      · have hlg' : (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
            0xFFFFFFFF#32 &&& 0x80000000#32) = 0#32 :=
          Classical.byContradiction fun hn => hbin hn
        rw [ite_eq_right hbin] at hrs ⊢
        let r := (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat
        have hne_c := hnonact idx hidx hne hlg'
        obtain ⟨hg, _, hl⟩ := hoth_eq r hrs.1 hne_c
        exact ⟨hrefs ▸ hrs.1, hg.trans hrs.2.1, fun q hq => hrs.2.2 q (hl ▸ hq)⟩
    reason_lit_mem := fun idx hidx hne hlg => by
      have hrs := hw.reason_inv idx hidx hne
      have hbf : ¬ (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 := fun h => absurd hlg h
      rw [ite_eq_right hbf] at hrs
      have hne_c := hnonact idx hidx hne hlg
      dsimp only [s']
      rw [(hoth_eq _ hrs.1 hne_c).2.2]
      exact hw.reason_lit_mem idx hidx hne hlg },
    hrefs, hgarb_c, hsz_c, hnxt⟩

theorem fullSparseInvW_of_inPlaceShrink_hnonact {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    {cref nsz : Nat} (href : cref ∈ fullArenaClauseRefs s)
    (hnonact : NonActiveReason s.core cref) (hng : fullArenaClauseGarb s cref = false)
    (hnsz3 : 3 ≤ nsz) (hnsz_lt : nsz < fullArenaClauseSize s cref)
    {arena' : List (BitVec 32)} {ni' nr' : BitVec 64} (hal' : arena'.length = c.arena_cap)
    (hout : ∀ k, (k < cref ∨ cref + 3 + fullArenaClauseSize s cref ≤ k) →
      arena'[k]? = s.core.arena[k]?)
    (hnhdr_garb : (arena'[cref]?.getD 0#32 &&& 0x00080000#32) = 0#32)
    (hnhdr_shrk : (arena'[cref]?.getD 0#32 &&& 0x00800000#32) ≠ 0#32)
    (hnsz_eq : (arena'[cref + 2]?.getD 0#32).toNat = nsz)
    (hpad_old : M6ShrkPad arena' s.core.arena cref (fullArenaClauseSize s cref) nsz)
    (hlits_lt : ∀ j < nsz, (arena'[cref + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hnd_cref : ((fullArenaClauseLitsCore { s.core with arena := arena' } cref).map (· / 2)).Nodup)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (fullArenaClauseLitsCore { s.core with arena := arena' } cref))) :
    let s' : FullState :=
      { s with core := { s.core with arena := arena', num_irred := ni', num_redundant := nr' } }
    FullSparseInvW c F0 F_cur s' ∧ fullArenaClauseRefs s' = fullArenaClauseRefs s ∧
    fullArenaClauseGarb s' cref = false ∧ fullArenaClauseSize s' cref = nsz := by
  intro s'
  have hw := hsp.2.1; have hcl := hsp.1.core_ok
  obtain ⟨hlen', hw', hrefs', hgb', hsz', _⟩ :=
    inPlaceShrink_hnonact_preserves_fullWitness hsp.1 hw href hnonact hng hnsz3 hnsz_lt hal'
      hsp.1.scratch_ok hout hnhdr_garb hnhdr_shrk hnsz_eq hpad_old hlits_lt hent
  have hnd' : FullArenaVarsNodup s' := fun r hr hngr => by
    rw [hrefs'] at hr
    dsimp only [fullArenaClauseRefs, fullArenaClauseGarb, fullArenaClauseLits] at hr hngr ⊢
    by_cases hrc : r = cref
    · subst r; exact hnd_cref
    · have hr_wf := hw.arena.refs_wf r hr
      have hdisj := (Nat.lt_or_gt_of_ne hrc).elim
        (fun h => Or.inl (hw.arena.disjoint hr href h))
        (fun h => Or.inr (hw.arena.disjoint href hr h))
      have hbd1 : r + 3 + fullArenaClauseSizeCore s.core r ≤ s.core.arena.length := by
        have := hr_wf.2.2.1; have := hr_wf.2.2.2.1
        have := hcl.arena_len_arr; have := hcl.arena_len_le; omega
      have hout' : ∀ p, r ≤ p → p < r + 3 + fullArenaClauseSizeCore s.core r →
          arena'[p]? = s.core.arena[p]? := fun p _ _ => by
        dsimp only [fullArenaClauseSize] at hout
        exact hdisj.elim
          (fun h1 => hout p (Or.inl (by omega)))
          (fun h2 => hout p (Or.inr (by omega)))
      have hszr : fullArenaClauseSizeCore s'.core r = fullArenaClauseSizeCore s.core r := by
        unfold fullArenaClauseSizeCore; dsimp only [s']; rw [hout' (r + 2) (by omega) (by omega)]
      have hgbr : fullArenaClauseGarbCore s'.core r = fullArenaClauseGarbCore s.core r := by
        unfold fullArenaClauseGarbCore fullArenaHdrCore; dsimp only [s']
        rw [hout' r (by omega) (by omega)]
      have hlitsr := fullArenaClauseLitsCore_eq_of_hold hbd1
        (by rw [hal', ← hcl.arena_len_arr]; exact hbd1)
        hszr fun j hj => hout' (r + 3 + j) (by omega) (by omega)
      rw [hgbr] at hngr; rw [hlitsr]; exact hsp.2.2.2.1 r hr hngr
  have hext' : FullExtScratchOk c s' :=
    ⟨fun i hi => by dsimp only [s']; rw [hrefs']; exact hsp.2.2.2.2.1.1 i hi, hsp.2.2.2.2.1.2⟩
  exact ⟨⟨hlen', hw', hsp.2.2.1, hnd', hext', hsp.2.2.2.2.2⟩, hrefs', hgb', hsz'⟩

theorem nonActiveReason_of_level0 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hl0 : k.cur_level = 0)
    (cref : Nat) : NonActiveReason k cref := fun idx hidx hne _ => by
  have hlv : (k.lvl[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
    have := hw.lvl_le idx hidx; omega
  exact absurd (hw.level0_rsn_none idx hidx hlv) hne

theorem simplify_shrk_sparseInv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s2 : FullState} (hsp2 : FullSparseInvW c F0 F_cur s2)
    (hl0 : s2.core.cur_level = 0) {cref nsz : Nat} (href : cref ∈ fullArenaClauseRefs s2)
    (hng : fullArenaClauseGarb s2 cref = false) (hnsz3 : 3 ≤ nsz)
    (hnsz_lt : nsz < fullArenaClauseSize s2 cref) {ar3 ar_f : List (BitVec 32)} {idxs : List Nat}
    (harf_len : ar_f.length = c.arena_cap) (hid_len : idxs.length = nsz)
    (hid_pw : idxs.Pairwise (· < ·)) (hid_lt : ∀ q ∈ idxs, q < fullArenaClauseSize s2 cref)
    (hsub3 : ∀ t < nsz, ar3[cref + 3 + t]? = s2.core.arena[cref + 3 + idxs[t]?.getD 0]?)
    (hnew_lt : ∀ t < nsz, (ar3[cref + 3 + t]?.getD 0#32).toNat < 2 * s2.core.cur_vars)
    (hent_new : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((List.range nsz).map fun t => (ar3[cref + 3 + t]?.getD 0#32).toNat)))
    (hout_f : ∀ k, (k < cref ∨ cref + 3 + fullArenaClauseSize s2 cref ≤ k) →
      ar_f[k]? = s2.core.arena[k]?)
    (hng_f : (ar_f[cref]?.getD 0#32 &&& 0x00080000#32) = 0#32)
    (hsh_f : (ar_f[cref]?.getD 0#32 &&& 0x00800000#32) ≠ 0#32)
    (hsz_f : (ar_f[cref + 2]?.getD 0#32).toNat = nsz)
    (hpay_f : ∀ t < nsz, ar_f[cref + 3 + t]? = ar3[cref + 3 + t]?)
    (hpad_f : M6ShrkPad ar_f s2.core.arena cref (fullArenaClauseSize s2 cref) nsz) :
    let s_f : FullState := { s2 with core := { s2.core with arena := ar_f } }
    FullSparseInvW c F0 F_cur s_f ∧ fullArenaClauseGarb s_f cref = false ∧
    fullArenaClauseRefs s_f = fullArenaClauseRefs s2 := by
  have hw2 := hsp2.2.1; have hcl := hsp2.1.core_ok; have hcref_wf := hw2.arena.refs_wf cref href
  have har_len := hcl.arena_len_arr; have halen_le := hcl.arena_len_le
  have hbd0 : cref + 3 + fullArenaClauseSizeCore s2.core cref ≤ s2.core.arena.length := by
    have _ := hcref_wf.2.2.1; have _ := hcref_wf.2.2.2.1; omega
  have hsz_core_f : fullArenaClauseSizeCore { s2.core with arena := ar_f } cref = nsz := hsz_f
  have hbd_f : cref + 3 + fullArenaClauseSizeCore { s2.core with arena := ar_f } cref ≤
      ar_f.length := by
    have hsz_eq0 : fullArenaClauseSizeCore s2.core cref = fullArenaClauseSize s2 cref := rfl
    rw [hsz_core_f]; omega
  have hnd_f : ((fullArenaClauseLitsCore { s2.core with arena := ar_f } cref).map
      (· / 2)).Nodup := by
    refine viv_nodup_of_strict_subseq (hsp2.2.2.2.1 cref href hng) idxs
      (by rw [fullArenaClauseLitsCore_length hbd_f, hsz_core_f]; exact hid_len) hid_pw
      (fun q hq => by rw [fullArenaClauseLitsCore_length hbd0]; exact hid_lt q hq) fun t ht => ?_
    rw [fullArenaClauseLitsCore_length hbd_f, hsz_core_f] at ht
    have hq_lt : idxs[t]?.getD 0 < fullArenaClauseSizeCore s2.core cref := by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact hid_lt _ (by simp)
    rw [fullArenaClauseLitsCore_getElem hbd_f (by omega),
      fullArenaClauseLitsCore_getElem hbd0 hq_lt]
    have heq_t := (hpay_f t ht).trans (hsub3 t ht)
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at heq_t
    exact congrArg BitVec.toNat (Option.some.inj heq_t)
  have hent_f : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (fullArenaClauseLitsCore { s2.core with arena := ar_f } cref)) := by
    have heq_l : fullArenaClauseLitsCore { s2.core with arena := ar_f } cref =
        (List.range nsz).map fun t => (ar3[cref + 3 + t]?.getD 0#32).toNat := by
      refine List.ext_getElem (by rw [fullArenaClauseLitsCore_length hbd_f, hsz_core_f,
          List.length_map, List.length_range]) fun t ht1 _ => ?_
      rw [fullArenaClauseLitsCore_length hbd_f, hsz_core_f] at ht1
      rw [fullArenaClauseLitsCore_getElem hbd_f (by omega), List.getElem_map, List.getElem_range,
        ← hpay_f t ht1, List.getElem?_eq_getElem (by omega), Option.getD_some]
    rwa [heq_l]
  obtain ⟨hsp_f, hrefs_f, hgb_f, _⟩ := fullSparseInvW_of_inPlaceShrink_hnonact hsp2 href
    (nonActiveReason_of_level0 hw2 hl0 cref) hng hnsz3 hnsz_lt harf_len hout_f hng_f
    hsh_f hsz_f hpad_f (fun j hj => by rw [hpay_f j hj]; exact hnew_lt j hj) hnd_f hent_f
  exact ⟨hsp_f, hgb_f, hrefs_f⟩

theorem markGarb_hnonact_preserves_fullSparseW {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    {cref : Nat} (href : cref ∈ fullArenaClauseRefs s) (hnonact : NonActiveReason s.core cref)
    (ag' ni' nr' vc' : BitVec 64) :
    let s' : FullState :=
      { s with
        core := { s.core with
          arena := s.core.arena.set cref (fullArenaHdr s cref ||| 0x00080000#32)
          arena_garbage := ag', num_irred := ni', num_redundant := nr' }
        scratch := { s.scratch with viv_cnt := vc' } }
    FullSparseInvW c F0 F_cur s' ∧ fullArenaClauseRefs s' = fullArenaClauseRefs s := by
  intro s'
  have hw := hsp.2.1; have hcl := hsp.1.core_ok
  have hmg := hw.arena.markGarb hcl href ag'
  have hrefs : fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s.core := hmg.1
  have hdisj_lits : ∀ {r : Nat}, r ∈ fullArenaClauseRefsCore s.core → r ≠ cref →
      fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s.core r := fun {r} hr hne => by
    have hdisj : r + 3 + fullArenaClauseSizeCore s.core r ≤ cref ∨ cref + 3 ≤ r := by
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · exact Or.inl (hw.arena.disjoint hr href hlt)
      · exact Or.inr (by have := hw.arena.disjoint href hr hgt; omega)
    have hbd : r + 3 + fullArenaClauseSizeCore s.core r ≤ s.core.arena.length := by
      have := (hw.arena.refs_wf r hr).2.2.1; have := (hw.arena.refs_wf r hr).2.2.2.1
      have := hcl.arena_len_le; have := hcl.arena_len_arr; omega
    exact (fullArenaClauseLitsCore_set_outside hbd hdisj).2
  have hlen' : s'.LengthsOk c :=
    ⟨{ hcl with arena_len_arr := by simp [s', hcl.arena_len_arr] }, { hsp.1.scratch_ok with }⟩
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { hw with
      arena := { hmg.2 with len_ok := hmg.2.len_ok }
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hrefs ▸ hr)
      reason_inv := fun idx hidx hne => by
        have hrs := hw.reason_inv idx hidx hne
        dsimp only [s'] at hrs ⊢
        by_cases hbin : (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
            0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32
        · rw [ite_eq_left hbin] at hrs ⊢; exact hrs
        · have hlg' : (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
              0xFFFFFFFF#32 &&& 0x80000000#32) = 0#32 :=
            Classical.byContradiction fun hn => hbin hn
          rw [ite_eq_right hbin] at hrs ⊢
          let r := (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat
          have hne_c := hnonact idx hidx hne hlg'
          have hgb : fullArenaClauseGarbCore s'.core r = false := by
            unfold fullArenaClauseGarbCore fullArenaHdrCore; dsimp only [s']
            rw [List.getElem?_set_ne hne_c.symm]; exact hrs.2.1
          have hl := hdisj_lits hrs.1 hne_c
          exact ⟨hrefs ▸ hrs.1, hgb, fun q hq => hrs.2.2 q (hl ▸ hq)⟩
      reason_lit_mem := fun idx hidx hne hlg => by
        have hrs := hw.reason_inv idx hidx hne
        have hbf : ¬ (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
            0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 := fun h => absurd hlg h
        rw [ite_eq_right hbf] at hrs
        dsimp only [s']
        exact hdisj_lits hrs.1 (hnonact idx hidx hne hlg) ▸ hw.reason_lit_mem idx hidx hne hlg }
  have hrefs' : fullArenaClauseRefs s' = fullArenaClauseRefs s := hrefs
  have hnd' : FullArenaVarsNodup s' := fun r hr hngr => by
    rw [hrefs'] at hr
    by_cases hrc : r = cref
    · subst r
      exfalso
      have hgb : fullArenaClauseGarb s' cref = true := by
        unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore; dsimp only [s']
        have hlt : cref < s.core.arena.length := by
          have := (hw.arena.refs_wf cref href).1; have := hcl.arena_len_le
          have := hcl.arena_len_arr; omega
        rw [List.getElem?_set_self hlt, Option.getD_some, BitVec.and_or_distrib_right,
          show (0x00080000#32 &&& 0x00080000#32) = 0x00080000#32 from rfl]
        have hne : (fullArenaHdr s cref &&& 0x00080000#32) ||| 0x00080000#32 ≠ 0#32 := by
          intro hz
          have := congrArg (· &&& 0x00080000#32) hz
          rw [BitVec.and_or_distrib_right,
            show (0x00080000#32 &&& 0x00080000#32) = 0x00080000#32 from rfl,
            BitVec.zero_and] at this
          have hbit := congrArg (fun x : BitVec 32 => x[19]) this
          simp at hbit
        simp [hne]
      rw [hgb] at hngr; cases hngr
    · have hgb0 : fullArenaClauseGarb s r = false := by
        unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore at hngr ⊢
        dsimp only [s'] at hngr; rwa [List.getElem?_set_ne (Ne.symm hrc)] at hngr
      rw [show fullArenaClauseLits s' r = fullArenaClauseLits s r from hdisj_lits hr hrc]
      exact hsp.2.2.2.1 r hr hgb0
  have hext' : FullExtScratchOk c s' :=
    ⟨fun i hi => (hsp.2.2.2.2.1.1 i hi).imp id (fun h => hrefs' ▸ h), hsp.2.2.2.2.1.2⟩
  exact ⟨⟨hlen', hw', hsp.2.2.1, hnd', hext', hsp.2.2.2.2.2⟩, hrefs'⟩

/-! ## 4. Watch-Push, Arena Helpers, & Trail/Resolution Lemmas -/

theorem viv_watchSlice_relocate {F_cur : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat}
    (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ i < rem, k'.wstk[p' + i]? = k.wstk[p + i]?)
    (h : WatchSliceOk F_cur k lit p rem) : WatchSliceOk F_cur k' lit p' rem := by
  induction h generalizing p' with
  | empty => exact .empty
  | @bin p rem w0 hp hflag hne hlt hent _ ih =>
    refine .bin (by simpa using (hwstk 0 (by omega)).trans hp) hflag hne (by omega) hent
      (ih (p' := p' + 1) fun i hi => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (i + 1) (by omega))
  | @large p rem w0 cref hp hp1 hflag hlt href _ ih =>
    refine .large (by simpa using (hwstk 0 (by omega)).trans hp)
      (by simpa using (hwstk 1 (by omega)).trans hp1) hflag hlt (hsub _ href)
      (ih (p' := p' + 2) fun i hi => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (i + 2) (by omega))

theorem viv_watchSlice_append_large {F_cur : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat} {w0 cref : BitVec 32}
    (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ i < rem, k'.wstk[p' + i]? = k.wstk[p + i]?)
    (h : WatchSliceOk F_cur k lit p rem)
    (hw0 : k'.wstk[p' + rem]? = some w0) (hw1 : k'.wstk[p' + rem + 1]? = some cref)
    (hflag : (w0 &&& 0x80000000#32) = 0#32) (hlt : cref.toNat < 0x80000000)
    (href : cref.toNat ∈ fullArenaClauseRefsCore k') :
    WatchSliceOk F_cur k' lit p' (rem + 2) := by
  induction h generalizing p' with
  | empty => exact .large (by simpa using hw0) (by simpa using hw1) hflag hlt href .empty
  | @bin p rem w hp hf hne hl he _ ih =>
    refine .bin (by simpa using (hwstk 0 (by omega)).trans hp) hf hne (by omega) he ?_
    exact ih (p' := p' + 1)
      (fun i hi => by simpa [show p' + 1 + i = p' + (i + 1) by omega,
        show p + 1 + i = p + (i + 1) by omega] using hwstk (i + 1) (by omega))
      (by simpa [show p' + 1 + rem = p' + (rem + 1) by omega] using hw0)
      (by simpa [show p' + 1 + rem + 1 = p' + (rem + 1) + 1 by omega] using hw1)
  | @large p rem w cr hp hp1 hf hl hr _ ih =>
    refine .large (by simpa using (hwstk 0 (by omega)).trans hp)
      (by simpa using (hwstk 1 (by omega)).trans hp1) hf hl (hsub _ hr) ?_
    exact ih (p' := p' + 2)
      (fun i hi => by simpa [show p' + 2 + i = p' + (i + 2) by omega,
        show p + 2 + i = p + (i + 2) by omega] using hwstk (i + 2) (by omega))
      (by simpa [show p' + 2 + rem = p' + (rem + 2) by omega] using hw0)
      (by simpa [show p' + 2 + rem + 1 = p' + (rem + 2) + 1 by omega] using hw1)

theorem fullWatchPush_large_preserves_sparseInvW {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState}
    (hsp : FullSparseInvW c F0 F_cur s) {lit w0 cref : BitVec 32} {ok : Bool}
    {wvec' wstk' wsort' : List (BitVec 32)} {wlen' : Nat} {wusable' : BitVec 64}
    (hflag : (w0 &&& 0x80000000#32) = 0#32) (hlt : cref.toNat < 0x80000000)
    (href : cref.toNat ∈ fullArenaClauseRefs s) :
    let s' : FullState :=
      { s with
        core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable' }
        scratch := { s.scratch with wsort := wsort' } }
    s'.LengthsOk c → WatchStackLayout s'.core →
    (∀ l < 2 * s.core.cur_vars, l ≠ lit.toNat →
      fullWatchSize s' l = fullWatchSize s l ∧
      ∀ k < fullWatchSize s l,
        s'.core.wstk[fullWatchOff s' l + k]? = s.core.wstk[fullWatchOff s l + k]?) →
    (ok = true →
      lit.toNat < 2 * s.core.cur_vars ∧
      fullWatchSize s' lit.toNat = fullWatchSize s lit.toNat + 2 ∧
      (∀ k < fullWatchSize s lit.toNat,
        s'.core.wstk[fullWatchOff s' lit.toNat + k]? =
          s.core.wstk[fullWatchOff s lit.toNat + k]?) ∧
      s'.core.wstk[fullWatchOff s' lit.toNat + fullWatchSize s lit.toNat]? = some w0 ∧
      s'.core.wstk[fullWatchOff s' lit.toNat + fullWatchSize s lit.toNat + 1]? = some cref) →
    (ok = false → lit.toNat < 2 * s.core.cur_vars →
      fullWatchSize s' lit.toNat = fullWatchSize s lit.toNat ∧
      ∀ k < fullWatchSize s lit.toNat,
        s'.core.wstk[fullWatchOff s' lit.toNat + k]? =
          s.core.wstk[fullWatchOff s lit.toNat + k]?) →
    FullSparseInvW c F0 F_cur s' := by
  intro s' hlen' hlay hother hok_t hok_f
  obtain ⟨_, hw, hmc, hnd, hext, hdm⟩ := hsp
  have hwat0 : WatchesInv F_cur s.core := by
    have := hw.watches; unfold ModeWatchesInv at this; simpa [hdm] using this
  have hwat' : ModeWatchesInv F_cur s'.core := by
    unfold ModeWatchesInv; rw [show s'.core.dense_mode = 0#64 from hdm]; simp only [↓reduceIte]
    refine ⟨hlay, fun l hl => ?_⟩
    by_cases hle : l = lit.toNat
    · subst hle
      cases ok with
      | false =>
        obtain ⟨hsz, hpre⟩ := hok_f rfl hl
        rw [show fullWatchSizeCore s'.core lit.toNat = fullWatchSizeCore s.core lit.toNat from hsz]
        exact viv_watchSlice_relocate (k := s.core) (k' := s'.core)
          (Nat.le_refl _) (fun _ r => r) hpre (hwat0.slices _ hl)
      | true =>
        obtain ⟨_, hsz, hpre, hw0, hw1⟩ := hok_t rfl
        rw [show fullWatchSizeCore s'.core lit.toNat =
          fullWatchSizeCore s.core lit.toNat + 2 from hsz]
        exact viv_watchSlice_append_large (k := s.core) (k' := s'.core)
          (Nat.le_refl _) (fun _ r => r) hpre (hwat0.slices _ hl) hw0 hw1 hflag hlt href
    · obtain ⟨hsz, hpre⟩ := hother l hl hle
      rw [show fullWatchSizeCore s'.core l = fullWatchSizeCore s.core l from hsz]
      exact viv_watchSlice_relocate (k := s.core) (k' := s'.core)
        (Nat.le_refl _) (fun _ r => r) hpre (hwat0.slices l hl)
  have harena' : FullArenaClausesInv c F_cur s'.core :=
    ⟨hw.arena.len_ok, hw.arena.refs_wf, hw.arena.shrk_term, hw.arena.lits_lt, hw.arena.entails⟩
  exact ⟨hlen', { hw with arena := harena', watches := hwat' }, hmc, hnd, hext, hdm⟩

theorem ar_set_sz_props {ar0 ar_orig : List (BitVec 32)} {cref old_sz nsz : Nat}
    {nsz_bv : BitVec 32} {p2 p1 : Nat} (hlen : ar0.length = ar_orig.length) (hnsz3 : 3 ≤ nsz)
    (hlt : nsz < old_sz) (hbd : cref + 3 + old_sz ≤ ar0.length) (hnsz_eq : nsz_bv.toNat = nsz)
    (hp2 : p2 = cref + 2) (hp1 : p1 = cref + 1)
    (hout : ∀ p, (p < cref + 3 ∨ cref + 3 + nsz ≤ p) → ar0[p]? = ar_orig[p]?) :
    let ar_sz := (ar0.set p2 nsz_bv).set p1 2#32
    ar_sz.length = ar_orig.length ∧ (∀ k, (k < cref ∨ cref + 3 + old_sz ≤ k) →
      ar_sz[k]? = ar_orig[k]?) ∧ (ar_sz[cref + 2]?.getD 0#32).toNat = nsz ∧
    (∀ t < nsz, ar_sz[cref + 3 + t]? = ar0[cref + 3 + t]?) ∧
    (∀ k, cref + 3 + nsz ≤ k → k < cref + 3 + old_sz → ar_sz[k]? = ar_orig[k]?) ∧
    ar_sz[cref]? = ar_orig[cref]? := by
  intro ar_sz; subst hp2 hp1
  refine ⟨by simp [ar_sz, hlen], fun k hk => ?_, ?_, fun t ht => ?_, fun k hk1 _ => ?_, ?_⟩ <;>
    dsimp only [ar_sz]
  · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact hout k (by omega)
  · rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega), Option.getD_some,
      hnsz_eq]
  · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact hout k (Or.inr hk1)
  rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  exact hout cref (Or.inl (by omega))

theorem ar_set_shrk_facts {ar_sz ar_orig : List (BitVec 32)}
    {cref old_sz nsz cap term : Nat} {nhdr : BitVec 32} (har_len : ar_sz.length = cap)
    (hsz_le : cref + 3 + old_sz ≤ cap) (hterm : term = cref + 3 + old_sz - 1)
    (hnz_lt : nsz < old_sz) (hnsz3 : 3 ≤ nsz) (hng : (nhdr &&& 0x00080000#32) = 0#32)
    (hsh0 : (nhdr &&& 0x00800000#32) = 0#32)
    (hsh_orig : (ar_orig[cref]?.getD 0#32 &&& 0x00800000#32) = (nhdr &&& 0x00800000#32))
    (hout : ∀ k, (k < cref ∨ cref + 3 + old_sz ≤ k) → ar_sz[k]? = ar_orig[k]?)
    (hsz : (ar_sz[cref + 2]?.getD 0#32).toNat = nsz)
    (hpad : ∀ k, cref + 3 + nsz ≤ k → k < cref + 3 + old_sz → ar_sz[k]? = ar_orig[k]?) :
    let ar1 := ar_sz.set cref (nhdr ||| 0x00800000#32); let ar2 := ar1.set term 0xFFFFFFFF#32
    ar2.length = cap ∧ (∀ k, (k < cref ∨ cref + 3 + old_sz ≤ k) → ar2[k]? = ar_orig[k]?) ∧
    (ar2[cref]?.getD 0#32 &&& 0x00080000#32) = 0#32 ∧
    (ar2[cref]?.getD 0#32 &&& 0x00800000#32) ≠ 0#32 ∧ (ar2[cref + 2]?.getD 0#32).toNat = nsz ∧
    M6ShrkPad ar2 ar_orig cref old_sz nsz := by
  intro ar1 ar2; subst hterm
  refine ⟨by simp [ar2, ar1, har_len], fun k hk => by
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact hout k hk,
    by rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp [har_len]; omega),
        Option.getD_some, bv32_or_shrk_garb, hng],
    by rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp [har_len]; omega),
        Option.getD_some]; exact bv32_or_shrk_ne0 nhdr,
    by rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact hsz, ?_⟩
  unfold M6ShrkPad; rw [ite_eq_left (by rw [hsh_orig, hsh0])]
  exact ⟨fun k hk1 hk2 => by rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
                             exact hpad k hk1 (by omega),
    List.getElem?_set_self (by simp [ar1, har_len]; omega)⟩

theorem entails_filter_level0 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (_hl0 : k.cur_level = 0)
    {c1 c2 : List Nat} (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause c1))
    (hsub : ∀ l ∈ c1, l ∈ c2 ∨ (l < 2 * k.cur_vars ∧ k.vals[l]?.getD 0#8 = 0xFF#8)) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause c2) := by
  refine entails_of_mem_or_false hent fun l hl => ?_
  rcases hsub l hl with hin | ⟨hlt, hff⟩
  · exact Or.inl hin
  · right
    obtain ⟨i, hi, hieq⟩ := (hw.vals_false_iff l hlt).mp hff
    have hli : (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
      have := hw.lvl_le i hi; omega
    have hs := hw.level0_sound i hi hli
    rwa [hieq] at hs

theorem inst_resolve_entails {F : CNF Nat} {out rest : List Nat} {lit : Nat}
    (hout : F.EntailsClause (cnfClause out))
    (hfull : F.EntailsClause (cnfClause (rest ++ [lit])))
    (hsub : ∀ x ∈ out, x = lit ^^^ 1 ∨ x ∈ rest) :
    F.EntailsClause (cnfClause rest) := by
  rw [CNF.entails_clause_def] at hout hfull ⊢
  intro α hα
  obtain ⟨x, hx_mem, hx_sat⟩ := (clause_sat_cnfClause_iff α _).mp (hout α hα)
  rcases hsub x hx_mem with hx_eq | hx_rest
  · obtain ⟨y, hy_mem, hy_sat⟩ := (clause_sat_cnfClause_iff α _).mp (hfull α hα)
    rw [List.mem_append, List.mem_singleton] at hy_mem
    rcases hy_mem with hy_rest | hy_eq
    · exact (clause_sat_cnfClause_iff α _).mpr ⟨y, hy_rest, hy_sat⟩
    · exfalso
      rw [hx_eq] at hx_sat; rw [hy_eq] at hy_sat
      have hx_neg : (cnfClause [lit ^^^ 1]).Sat α := (sat_cnfClause_singleton α _).mpr hx_sat
      have hy_pos : (cnfClause [lit]).Sat α := (sat_cnfClause_singleton α _).mpr hy_sat
      exact ((sat_cnfClause_litNeg_iff α lit).mp hx_neg) hy_pos
  · exact (clause_sat_cnfClause_iff α _).mpr ⟨x, hx_rest, hx_sat⟩

theorem viv_inst_sub_witness_entails {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core) {sz : Nat}
    (hsz : 1 ≤ sz) (hsz_tmp : sz ≤ s.core.tmp.length)
    (hsub : VivDeduceSubWitness F_cur s sz)
    (hlit_val : s.core.vals[(s.core.tmp[sz - 1]'(by omega)).toNat]?.getD 0#8 = 1#8)
    (hlit_rsn : s.core.rsns[(s.core.tmp[sz - 1]'(by omega)).toNat / 2]?.getD 0xFFFFFFFF#32 =
      0xFFFFFFFF#32) :
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((s.core.tmp.take (sz - 1)).map BitVec.toNat)) := by
  obtain ⟨sub, hent, hmem⟩ := hsub
  refine entails_of_mem_or_false hent fun l hl => ?_
  obtain ⟨hl_lt, hcase⟩ := hmem l hl
  rcases hcase with ⟨⟨k, hk, hkeq⟩, hnot⟩ | ⟨hff, hlvl0⟩
  · left
    have hkne : k ≠ sz - 1 := by
      intro hk_eq; subst hk_eq
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hkeq
      simp only [hkeq] at hlit_val hlit_rsn
      rcases hnot with hv | hr
      · exact hv hlit_val
      · exact hr hlit_rsn
    rw [List.mem_map]
    refine ⟨s.core.tmp[k]'(by omega), ?_, ?_⟩
    · rw [List.mem_iff_getElem]
      exact ⟨k, by simp [List.length_take]; omega, by simp [List.getElem_take]⟩
    · rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at hkeq
  · right
    obtain ⟨i, hi, hieq⟩ := (hw.vals_false_iff l hl_lt).mp hff
    have hli : (s.core.lvl[(s.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
      rw [hieq, show (l ^^^ 1) / 2 = l / 2 from litVar_litNeg l]; exact hlvl0
    have hs := hw.level0_sound i hi hli
    rwa [hieq] at hs

theorem falsified_preserved_of_trailExt {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k k' : FullCoreState} (hw : FullWitnessInv c F0 F_cur k)
    (hw' : FullWitnessInv c F0 F_cur k') (hcv : k'.cur_vars = k.cur_vars)
    (hte : k.trail_end ≤ k'.trail_end) (htrl : ∀ i < k.trail_end, k'.trl[i]? = k.trl[i]?)
    {l : Nat} (hl : l < 2 * k.cur_vars) (hff : k.vals[l]?.getD 0#8 = 0xFF#8) :
    k'.vals[l]?.getD 0#8 = 0xFF#8 := by
  obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff l hl).mp hff
  exact (hw'.vals_false_iff l (hcv ▸ hl)).mpr ⟨i, by omega, by rwa [htrl i hi]⟩

theorem vals_xor1_eq_zero {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) {l : Nat}
    (hl : l < 2 * k.cur_vars) (hun : k.vals[l]?.getD 0#8 = 0#8) :
    k.vals[l ^^^ 1]?.getD 0#8 = 0#8 := by
  have hl1 : l ^^^ 1 < 2 * k.cur_vars := litNeg_lt_two_mul hl
  rcases hw.vals_domain (l ^^^ 1) hl1 with h0 | h1 | hff
  · exact h0
  · obtain ⟨i, hi, heq⟩ := (hw.vals_true_iff (l ^^^ 1) hl1).mp h1
    have hff := (hw.vals_false_iff l hl).mpr ⟨i, hi, heq⟩
    rw [hun] at hff; cases hff
  · obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff (l ^^^ 1) hl1).mp hff
    rw [show l ^^^ 1 ^^^ 1 = l from litNeg_litNeg l] at heq
    have ht := (hw.vals_true_iff l hl).mpr ⟨i, hi, heq⟩
    rw [hun] at ht; cases ht

theorem vivCopy_perm_lits {tmp tmp' ar : List (BitVec 32)} {cref sz : Nat}
    (htmp_len : tmp.length ≥ sz) (har_len : cref + 3 + sz ≤ ar.length)
    (hcp : ∀ k < sz, tmp[k]? = ar[cref + 3 + k]?)
    (hperm : (tmp'.take sz).Perm (tmp.take sz))
    (_hsz' : tmp'.length ≥ sz) :
    ((tmp'.take sz).map BitVec.toNat).Perm (((ar.drop (cref + 3)).take sz).map BitVec.toNat) := by
  refine List.Perm.map BitVec.toNat (hperm.trans ?_)
  refine List.Perm.of_eq (List.ext_getElem (by simp; omega) fun i hi _ => ?_)
  simp only [List.length_take] at hi
  rw [List.getElem_take, List.getElem_take, List.getElem_drop]
  have hget := hcp i (by omega)
  rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at hget
  exact Option.some.inj hget

theorem fullArenaClauseRefs_zero_mem {c : FullCfg} {F_cur : List (List Nat)} {k : FullCoreState}
    (ha : FullArenaClausesInv c F_cur k) (hpos : 0 < k.arena_len) :
    0 ∈ fullArenaClauseRefsCore k := by
  rcases ha.len_ok with hz | h3
  · omega
  · unfold fullArenaClauseRefsCore
    have hf : ∃ f, k.arena_len = f + 1 := ⟨k.arena_len - 1, by omega⟩
    obtain ⟨f, hf⟩ := hf
    rw [hf]; unfold fullArenaScanRefs; simp [show 0 + 3 ≤ f + 1 by omega]

theorem fullArenaScanRefs_next_mem_or_end {ar : List (BitVec 32)} {alen : Nat} :
    ∀ {fuel pos r : Nat}, alen - pos ≤ fuel →
      (∀ q ∈ fullArenaScanRefs ar alen pos fuel,
        fullArenaNextOff ar alen q = alen ∨ fullArenaNextOff ar alen q + 3 ≤ alen) →
      r ∈ fullArenaScanRefs ar alen pos fuel →
      fullArenaNextOff ar alen r = alen ∨
        fullArenaNextOff ar alen r ∈ fullArenaScanRefs ar alen pos fuel
  | 0, _, _, _, _, h => by simp [fullArenaScanRefs] at h
  | fuel + 1, pos, r, hfl, hwf, h => by
    unfold fullArenaScanRefs at h hwf ⊢; split at h
    · rename_i hle
      simp only [hle, ↓reduceIte] at hwf ⊢
      simp only [List.mem_cons] at h
      have _ := fullArenaNextOff_bounds (ar := ar) (alen := alen) (cref := pos) hle
      rcases h with rfl | hrest
      · rcases hwf r List.mem_cons_self with hend | h3
        · exact Or.inl hend
        · right; right
          cases fuel with
          | zero => omega
          | succ f' =>
            unfold fullArenaScanRefs; simp only [h3, ↓reduceIte]; exact List.mem_cons_self
      · rcases fullArenaScanRefs_next_mem_or_end (by omega)
            (fun q hq => hwf q (List.mem_cons_of_mem _ hq)) hrest with hend | hmem
        · exact Or.inl hend
        · exact Or.inr (List.mem_cons_of_mem _ hmem)
    · simp at h

theorem fullArenaClauseRefs_next_mem_or_end {c : FullCfg} {F_cur : List (List Nat)}
    {k : FullCoreState} (ha : FullArenaClausesInv c F_cur k)
    {r : Nat} (hr : r ∈ fullArenaClauseRefsCore k) :
    fullArenaNextOff k.arena k.arena_len r = k.arena_len ∨
      fullArenaNextOff k.arena k.arena_len r ∈ fullArenaClauseRefsCore k :=
  fullArenaScanRefs_next_mem_or_end (by omega) (fun q hq => (ha.refs_wf q hq).2.2.2.2) hr

end

end LeanQbe.T.Examples.Kissat.Proof.Vivify
