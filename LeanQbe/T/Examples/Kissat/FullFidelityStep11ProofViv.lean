/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep11
public import LeanQbe.T.Examples.Kissat.FullSpec3
public import LeanQbe.T.Examples.Kissat.FullM6BcpS15Proof1
public import LeanQbe.T.Examples.Kissat.FullM6OrchAdaptersProof0
public import LeanQbe.T.Examples.Kissat.FullFidelityVivK6Proof0b
public import LeanQbe.T.Examples.Kissat.FullM6VivBackboneProof3b
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas
import LeanQbe.T.Examples.Kissat.FullVivTopLemmas1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 11 PR 1: `full_vivify_tier_m6_hdr` Proof (`FullFidelityStep11ProofViv`)

UNSAT-only `Func.wp` proof (`public section`, `0` `@[expose]` on theorems/lemmas, `0` `import all`,
`std3`, `XPost`-polymorphic) for `fidStep11VivifyTierM6HdrFn` (`S11-1` LIFO unsorted scan
`rr[do_sort ? bi : (bn - 1ULL - bi)]`, `vivify.c:1303`) parameterized on the relaxed
`fid11VivCollectSpec` (allowing arena-header `PH_VIV` updates in `S11-8` while preserving
`FullSparseInv` and `fullArenaClauseRefs`, strictly generalizing `fullVivCollectFidSpec`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep11

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open LeanQbe.T.Examples.Kissat.FullFidelityStep7
open LeanQbe.T.Examples.Kissat.FullFidelityVivK6
open LeanQbe.T.Examples.Kissat.FullM6BcpS15
open LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
open LeanQbe.T.Examples.Kissat.FullM6VivBackbone
open FullVivTopTactics
open Kraken.Bedrock2.Test

/-! ## 1. Relaxed `fid11VivCollectSpec` (Shared PR 1 / PR 3 `S11-8` Contract) -/

/-- Relaxed `full_viv_collect_fid(h, tier_mode)` specification permitting arena-header-only
mutations (e.g., setting `PH_VIV` when `prioritized == 0` per `S11-8`, `vivify.c:297-301`) while
preserving `FullSparseInv`, `fullArenaClauseRefs`, and all non-arena `core` fields. -/
def fid11VivCollectSpec : Spec [i64, i64] [i64] := fun (h, _tier_mode, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ bn arena' rr' m',
      let s' : FullState :=
        { core := { s.core with arena := arena' }
          scratch := { s.scratch with red_refs := rr' } }
      bn.toNat ≤ c.red_cap → rr'.length = c.red_cap →
      FullSparseInv c F0 s' → fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (∀ k < bn.toNat, (rr'[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s') →
      (FullMem c s' ⋆ R) m' → Q (bn, ()) m'

theorem fid11VivCollectSpec_monoX {xs : Tup Val [i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X X' : XPost} (h : fid11VivCollectSpec xs m Q X) :
    fid11VivCollectSpec xs m Q X' := by
  rcases xs with ⟨_, _, ⟨⟩⟩; exact h

theorem fid11VivCollectSpec_elim {h tier_mode : BitVec 64} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (hsp0 : fid11VivCollectSpec (h, tier_mode, ()) m Q X) :
    ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
      ∀ bn arena' rr' m',
        let s' : FullState :=
          { core := { s.core with arena := arena' }
            scratch := { s.scratch with red_refs := rr' } }
        bn.toNat ≤ c.red_cap → rr'.length = c.red_cap →
        FullSparseInv c F0 s' → fullArenaClauseRefs s' = fullArenaClauseRefs s →
        (∀ k < bn.toNat, (rr'[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s') →
        (FullMem c s' ⋆ R) m' → Q (bn, ()) m' :=
  hsp0

section VivStep11Helpers

private theorem s11_sparse_with_rr {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) {rr' : List (BitVec 32)} (hrr : rr'.length = c.red_cap) :
    FullSparseInv c F0 { s with scratch := { s.scratch with red_refs := rr' } } := by
  obtain ⟨⟨hl, F_cur, hw⟩, hlm, hnd, hext, hdm⟩ := h
  exact ⟨⟨⟨hl.core_ok, { hl.scratch_ok with red_refs_len := hrr }⟩, F_cur, hw⟩, hlm, hnd,
    FullExtScratchOk.of_pres hext ⟨rfl, rfl⟩ (fun _ hr => hr), hdm⟩

private theorem s11_sparse_with_tr {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) {tr' : List (BitVec 32)} (htr : tr'.length = 2 * c.max_vars) :
    FullSparseInv c F0 { s with scratch := { s.scratch with tarjan_reach := tr' } } := by
  obtain ⟨⟨hl, F_cur, hw⟩, hlm, hnd, hext, hdm⟩ := h
  exact ⟨⟨⟨hl.core_ok, { hl.scratch_ok with tarjan_reach_len := htr }⟩, F_cur, hw⟩, hlm, hnd,
    FullExtScratchOk.of_pres hext ⟨rfl, rfl⟩ (fun _ hr => hr), hdm⟩

private theorem s11_sparse_with_rr_scr {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) {rr' : List (BitVec 32)} {scr' : List (BitVec 32)}
    (hrr : rr'.length = c.red_cap) (hscr : scr'.length = c.scratch_cap) :
    FullSparseInv c F0
      { s with scratch := { s.scratch with red_refs := rr', scratch_buf := scr' } } := by
  obtain ⟨⟨hl, F_cur, hw⟩, hlm, hnd, hext, hdm⟩ := h
  exact ⟨⟨⟨hl.core_ok,
    { hl.scratch_ok with red_refs_len := hrr, scratch_buf_len := hscr }⟩, F_cur, hw⟩,
    hlm, hnd, FullExtScratchOk.of_pres hext ⟨rfl, rfl⟩ (fun _ hr => hr), hdm⟩

private theorem s11_sparse_with_res_sz {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) (rsz : BitVec 64) :
    FullSparseInv c F0 { s with scratch := { s.scratch with res_sz := rsz } } := by
  obtain ⟨⟨hl, F_cur, hw⟩, hlm, hnd, hext, hdm⟩ := h
  exact ⟨⟨⟨hl.core_ok, { hl.scratch_ok with }⟩, F_cur, hw⟩, hlm, hnd,
    FullExtScratchOk.of_pres hext ⟨rfl, rfl⟩ (fun _ hr => hr), hdm⟩

private theorem s11_sparseInvW_of_prop_canon {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    {vals' : List (BitVec 8)} {flags' lvl' rsns' trl' tp' : List (BitVec 32)}
    {te' prop' : Nat} {unass' unfl' : BitVec 64}
    {wvec' arena' wstk' : List (BitVec 32)}
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

end VivStep11Helpers

/-- Strict `FullFidelityVivK6.fullVivCollectFidSpec` implies relaxed `fid11VivCollectSpec`. -/
theorem fid11VivCollectSpec_of_strict {xs : Tup Val [i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (h : fid11VivCollectSpec xs m Q X) :
    fullVivCollectFidSpec xs m Q X := by
  rcases xs with ⟨h0, tm, ⟨⟩⟩
  obtain ⟨c, F0, s, R, rfl, hsp, hm, hQ⟩ := h
  exact fullVivCollectFidSpec_intro rfl hsp hm fun bn rr' m' hbn hrr hok hm' =>
    hQ bn s.core.arena rr' m' hbn hrr (s11_sparse_with_rr hsp hrr) rfl hok hm'

/-! ## 2. `full_vivify_tier_m6_hdr_step11_wp` (`FullM6OrchAdapters.m6aVivifyTierSpec`) -/

/-- Parametric `Func.wp` proof for `fidStep11VivifyTierM6HdrFn` (`full_vivify_tier_m6_hdr`,
`S11-1` LIFO unsorted scan `rr[do_sort ? bi : (bn - 1ULL - bi)]`) against
`FullM6OrchAdapters.m6aVivifyTierSpec`, accepting relaxed `fid11VivCollectSpec` for `S11-8`. -/
theorem full_vivify_tier_m6_hdr_step11_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hCollect : ∀ a m Q X, fid11VivCollectSpec a m Q X →
      Γ "full_viv_collect_fid" [i64, i64] [i64] a m Q X)
    (hCount : ∀ a m Q X, fullVivCountFidSpec a m Q X →
      Γ "full_viv_count_fid" [i64, i64] [] a m Q X)
    (hSort : ∀ a m Q X, fullVivSortFidSpec a m Q X →
      Γ "full_viv_sort_fid" [i64, i64] [] a m Q X)
    (hVivClause : ∀ a m Q X, FullM6VivBackbone.fullVivClauseM6Spec a m Q X →
      Γ "full_viv_clause_m6" [i64, i32] [i64] a m Q X)
    (hProp : ∀ a m Q X, FullM6BcpS15.fullBcpS15Spec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hClearTier : ∀ a m Q X, FullM6VivBackbone.fullVivClearTierM6Spec a m Q X →
      Γ "full_viv_clear_tier_m6" [i64, i64] [] a m Q X) :
    ∀ a m Q X, FullM6OrchAdapters.m6aVivifyTierSpec a m Q X →
      Func.wp Γ fidStep11VivifyTierM6HdrFn.body a m Q X := by
  rintro ⟨h, tier_mode, budget0, tick_lim, ⟨⟩⟩ m0 Q X hs
  obtain ⟨c, F0, s, R, rfl, hsp0, hm0, hQ⟩ := FullM6OrchAdapters.m6aVivifyTierSpec_elim hs
  have har_cap := c.harena; have hmx := c.hmaxv; have hrc := c.hred
  unfold LratBytes.dimacsBound at har_cap hmx hrc
  have hmaxv : c.max_vars < 2 * 2 ^ 28 := hmx
  unfold Func.wp fidStep11VivifyTierM6HdrFn fidStep7VivifyTierM6HdrFn
    FullFidelityStep7.full_vivify_tier_m6_hdr_body
  dsimp only; fvt_to_group
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
    refine ⟨c, F0, s2, R, rfl, hsp2, hm2,
      fun bn arena3 rr3 m3 hbn_le hrr3 hsp3 hrefs3 hok3 hm3 => ?_⟩
    let s3 : FullState :=
      { core := { s2.core with arena := arena3 }
        scratch := { s2.scratch with red_refs := rr3 } }
    have hok3_2 : ∀ k < bn.toNat, (rr3[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s2 :=
      fun k hk => hrefs3 ▸ hok3 k hk
    let SortJoin : Tup Val [] → Mem 64 → Prop := fun () ms =>
      ∃ (s5 : FullState) (rr5 : List (BitVec 32)),
        FullSparseInv c F0 s5 ∧ s5.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        fullArenaClauseRefs s5 = fullArenaClauseRefs s2 ∧
        s5.scratch.red_refs = rr5 ∧ rr5.length = c.red_cap ∧
        (∀ k < bn.toNat, (rr5[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s2) ∧
        (FullMem c s5 ⋆ R) ms
    fvt_to_group
    refine wp_join_group (ts := [.bool]) (fun _ md => m3 = md) ?_
      (fun Jd hJd => by fvt_steps <;> exact hJd _ m3 rfl)
    rintro _ ⟨do_sort, ⟨⟩⟩ _ rfl
    fvt_to_group
    refine wp_join_group (ts := []) SortJoin ?_ ?_
    · rintro _ ⟨⟩ m5 ⟨s5, rr5, hsp5, hfl5, hrefs5, hrr5, hrr5_len, hok5', hm5'⟩
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
            let sf1 : FullState := { sw with scratch := { sw.scratch with res_sz := bi_b } }
            let sf : FullState := { sf1 with core := { sf1.core with probing := 0#64 } }
            have hspf : FullSparseInv c F0 sf :=
              FullVivTop.FullSparseInv.with_probing (s11_sparse_with_res_sz hspw bi_b) 0#64
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
        fvt_to_group
        · have hbi_lt : bi.toNat < bn.toNat := by c0_bound
          have hbi1 : (bi + 1#64).toNat = bi.toNat + 1 := by bv_omega
          refine wp_join_group (ts := [i64])
            (fun (idx, ()) mi => mvi = mi ∧ idx.toNat < bn.toNat) ?_
            (fun Ji hJi => by
              fvt_steps
              · exact hJi (bi, ()) mvi ⟨rfl, hbi_lt⟩
              · exact hJi (bn - 1#64 - bi, ()) mvi ⟨rfl, by bv_omega⟩)
          rintro _ ⟨idx, ⟨⟩⟩ _ ⟨rfl, hidx_lt⟩
          have hidx_rr : idx.toNat < svi.scratch.red_refs.length := by rw [hrrv, hrr5_len]; omega
          let cr := svi.scratch.red_refs[idx.toNat]'hidx_rr
          have hcr_ref : cr.toNat ∈ fullArenaClauseRefs svi := by
            rw [hrefsv]
            have h := hok5' idx.toNat hidx_lt
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h
            have heq : cr = rr5[idx.toNat]'(by omega) := Option.some.inj (by
              rw [← List.getElem?_eq_getElem hidx_rr, hrrv, List.getElem?_eq_getElem (by omega)])
            rwa [heq]
          obtain ⟨F_curv, hswv⟩ := hspv.exists_witness
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
              s11_sparseInvW_of_prop_canon hsw_vc hlen_p hw_p hperm_p
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
    · intro Js hJs
      fvt_steps
      · c0_call hCount
        refine fullVivCountFidSpec_intro rfl hsp3 hbn_le hok3 hm3
          (fun tr3 m3c htr3 hm3c => ?_)
        let s3c : FullState := { s3 with scratch := { s3.scratch with tarjan_reach := tr3 } }
        have hsp3c : FullSparseInv c F0 s3c := s11_sparse_with_tr hsp3 htr3
        c0_call hSort
        refine fullVivSortFidSpec_intro rfl hsp3c hbn_le hok3 hm3c
          (fun rr4 scr4 m4 hrr4 hscr4 hok4 hm4 => ?_)
        let s4 : FullState :=
          { s3c with scratch := { s3c.scratch with red_refs := rr4, scratch_buf := scr4 } }
        have hsp4 : FullSparseInv c F0 s4 := s11_sparse_with_rr_scr hsp3c hrr4 hscr4
        exact hJs () m4 ⟨s4, rr4, hsp4, hfl2, hrefs3, rfl, hrr4,
          fun k hk => hrefs3 ▸ hok4 k hk, hm4⟩
      · exact hJs () m3 ⟨s3, rr3, hsp3, hfl2, hrefs3, rfl, hrr3, hok3_2, hm3⟩
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

end LeanQbe.T.Examples.Kissat.FullFidelityStep11

end
