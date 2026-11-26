/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep10
public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Examples.Kissat.FullM6BcpS15Proof1
public import LeanQbe.T.Examples.Kissat.FullM6OrchAdaptersProof0
public import LeanQbe.T.Examples.Kissat.FullFidelityVivK6Proof0b
public import LeanQbe.T.Examples.Kissat.FullM6VivBackboneProof3b
public import LeanQbe.T.Examples.Kissat.FullFidelityBveProof0
public import LeanQbe.T.Examples.Kissat.FullM6SweepProofSpec
public import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofBve0
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas
import LeanQbe.T.Examples.Kissat.FullVivTopLemmas1
import LeanQbe.T.Examples.Kissat.FullFidelityBveTactics
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 10 Proofs — Vivification, Rebuild & BVE (`FullFidelityStep10ProofMisc`)

UNSAT-only parametric `(Γ : Env)` `Func.wp` proofs (`public section`, `0` `@[expose]` on
theorems/lemmas, `0` `import all`, `std3`, `XPost`-polymorphic) for 3 Step-10 fixes:
1. `full_vivify_tier_m6_hdr_step10_wp` (`FullM6OrchAdapters.m6aVivifyTierSpec`): forward `rr[bi]`
   scan on both sorted and unsorted paths (`[P1]` unsorted vivification priority inversion).
2. `full_rebuild_watches_nosort_fid_step10_wp` (`Full.fullRebuildWatchesSpec`): clears
   `h->unflushed = 0ULL` when `full_arena_sweep(h) == 0ULL` before `full_propagate(h)`.
3. `full_bve_def_k6_fid_step10_wp` (`FullM8CoreParity.m8BveGatesSpec`): clears
   `scr[4130] = scr[4131] = 0u` whenever 1-sided `full_bve_certify_unit_fid` returns `false`
   (`[P1]` uncertified 1-sided core gate flag leak).
-/

set_option autoImplicit false

local macro "s10_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep10

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullFidelityVivK6
open LeanQbe.T.Examples.Kissat.FullFidelityBve
open LeanQbe.T.Examples.Kissat.FullM4Sweep
open LeanQbe.T.Examples.Kissat.FullM6BcpS15
open LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
open LeanQbe.T.Examples.Kissat.FullM6Sweep
open LeanQbe.T.Examples.Kissat.FullM6VivBackbone
open LeanQbe.T.Examples.Kissat.FullM8CoreParity
open FullVivTopTactics
open Kraken.Bedrock2.Test
open scoped FullArenaTactics FullVivTopTactics

/-! ## 1. `full_vivify_tier_m6_hdr_step10_wp` (`m6aVivifyTierSpec`) -/

section VivifyStep10

private theorem s10_sparse_with_rr {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) {rr' : List (BitVec 32)} (hrr : rr'.length = c.red_cap) :
    FullSparseInv c F0 { s with scratch := { s.scratch with red_refs := rr' } } :=
  ⟨⟨⟨h.1.lengths.core_ok, { h.1.lengths.scratch_ok with red_refs_len := hrr }⟩, h.1.witness⟩,
    h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

private theorem s10_sparse_with_tr {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) {tr' : List (BitVec 32)} (htr : tr'.length = 2 * c.max_vars) :
    FullSparseInv c F0 { s with scratch := { s.scratch with tarjan_reach := tr' } } :=
  ⟨⟨⟨h.1.lengths.core_ok, { h.1.lengths.scratch_ok with tarjan_reach_len := htr }⟩, h.1.witness⟩,
    h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

private theorem s10_sparse_with_rr_scr {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) {rr' scr' : List (BitVec 32)} (hrr : rr'.length = c.red_cap)
    (hscr : scr'.length = c.scratch_cap) :
    FullSparseInv c F0
      { s with scratch := { s.scratch with red_refs := rr', scratch_buf := scr' } } :=
  ⟨⟨⟨h.1.lengths.core_ok,
      { h.1.lengths.scratch_ok with red_refs_len := hrr, scratch_buf_len := hscr }⟩,
    h.1.witness⟩, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

private theorem s10_sparse_with_res_sz {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) (rsz : BitVec 64) :
    FullSparseInv c F0 { s with scratch := { s.scratch with res_sz := rsz } } :=
  ⟨⟨⟨h.1.lengths.core_ok, { h.1.lengths.scratch_ok with }⟩, h.1.witness⟩,
    h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

private theorem s10_sparseInvW_of_prop_canon {c : FullCfg} {F0 : CNF Nat}
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

end VivifyStep10

/-- Parametric `Func.wp` proof for `fidStep10VivifyTierM6HdrFn` (`full_vivify_tier_m6_hdr`,
forward `rr[bi]` scan for both sorted and unsorted paths) against `m6aVivifyTierSpec`. -/
theorem full_vivify_tier_m6_hdr_step10_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hCollect : ∀ a m Q X, fullVivCollectFidSpec a m Q X →
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
      Func.wp Γ fidStep10VivifyTierM6HdrFn.body a m Q X := by
  rintro ⟨h, tier_mode, budget0, tick_lim, ⟨⟩⟩ m0 Q X hs
  obtain ⟨c, F0, s, R, rfl, hsp0, hm0, hQ⟩ := FullM6OrchAdapters.m6aVivifyTierSpec_elim hs
  have har_cap := c.harena; have hmx := c.hmaxv; have hrc := c.hred
  unfold LratBytes.dimacsBound at har_cap hmx hrc
  have hmaxv : c.max_vars < 2 * 2 ^ 28 := hmx
  unfold Func.wp fidStep10VivifyTierM6HdrFn full_vivify_tier_m6_hdr_body; dsimp only; fvt_to_group
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
    refine fullVivCollectFidSpec_intro rfl hsp2 hm2
      (fun bn rr3 m3 hbn_le hrr3 hok3 hm3 => ?_)
    let s3 : FullState := { s2 with scratch := { s2.scratch with red_refs := rr3 } }
    have hsp3 : FullSparseInv c F0 s3 := s10_sparse_with_rr hsp2 hrr3
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
              FullVivTop.FullSparseInv.with_probing (s10_sparse_with_res_sz hspw bi_b) 0#64
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
        have hrrv_len : svi.scratch.red_refs.length = c.red_cap := by rw [hrrv, hrr5_len]
        fvt_to_group
        · have hbi_lt : bi.toNat < bn.toNat := by c0_bound
          have hbi1 : (bi + 1#64).toNat = bi.toNat + 1 := by bv_omega
          have hbi_rr : bi.toNat < svi.scratch.red_refs.length := by omega
          let cr := svi.scratch.red_refs[bi.toNat]'hbi_rr
          have hcr_ref : cr.toNat ∈ fullArenaClauseRefs svi := by
            rw [hrefsv]
            have h := hok5' bi.toNat hbi_lt
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h
            have heq : cr = rr5[bi.toNat]'(by omega) := Option.some.inj (by
              rw [← List.getElem?_eq_getElem hbi_rr, hrrv, List.getElem?_eq_getElem (by omega)])
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
              s10_sparseInvW_of_prop_canon hsw_vc hlen_p hw_p hperm_p
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
        have hsp3c : FullSparseInv c F0 s3c := s10_sparse_with_tr hsp3 htr3
        c0_call hSort
        refine fullVivSortFidSpec_intro rfl hsp3c hbn_le hok3 hm3c
          (fun rr4 scr4 m4 hrr4 hscr4 hok4 hm4 => ?_)
        let s4 : FullState :=
          { s3c with scratch := { s3c.scratch with red_refs := rr4, scratch_buf := scr4 } }
        have hsp4 : FullSparseInv c F0 s4 := s10_sparse_with_rr_scr hsp3c hrr4 hscr4
        exact hJs () m4 ⟨s4, rr4, hsp4, hfl2, rfl, rfl, hrr4, hok4, hm4⟩
      · exact hJs () m3 ⟨s3, rr3, hsp3, hfl2, rfl, rfl, hrr3, hok3, hm3⟩
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

/-! ## 2. `full_rebuild_watches_nosort_fid_step10_wp` (`Full.fullRebuildWatchesSpec`) -/

section RebuildStep10

private def S10RebuildOk (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s s' : FullState) : Prop :=
  FullSparseInvW c F0 F_cur s' ∧ s'.core.cur_level = 0 ∧
  s'.core.fuel.toNat ≤ s.core.fuel.toNat

private theorem s10RebuildOk_sweep {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} (hst : S10RebuildOk c F0 F_cur s st)
    {vals' : List (BitVec 8)}
    {flags' lvl' rsns' trl' tp' wvec' wstk' arena' : List (BitVec 32)}
    {te' alen' wlen' : Nat} {unass' unfl' wu' fred' ni' nr' nb' oom' : BitVec 64}
    {sc' : FullScratch} :
    let sA : FullState :=
      { st with
        core := { st.core with
          vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
          trail_pos := tp', trail_end := te', unassigned := unass', unflushed := unfl',
          wvec := wvec', wstk := wstk', arena := arena', arena_len := alen', wlen := wlen',
          wusable := wu', arena_garbage := 0#64, first_reducible := fred', num_irred := ni',
          num_redundant := nr', num_binary := nb', oom := oom' }
        scratch := sc' }
    sA.LengthsOk c → FullWitnessInv c F0 F_cur sA.core → Full.FullArenaVarsNodup sA →
    FullLastLearnedWf sA → sc'.extend_len = st.scratch.extend_len →
    S10RebuildOk c F0 F_cur s sA := by
  intro sA hlenA hwA hndA hllA hextA
  exact ⟨⟨hlenA, hwA, hst.1.2.2.1, hndA, ⟨hllA, hextA ▸ hst.1.2.2.2.2.1.2⟩, hst.1.2.2.2.2.2⟩,
    hst.2.1, hst.2.2⟩

private theorem s10RebuildOk_unflushed {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sA : FullState} (hA : S10RebuildOk c F0 F_cur s sA) (u' : BitVec 64) :
    S10RebuildOk c F0 F_cur s { sA with core := { sA.core with unflushed := u' } } := by
  refine ⟨⟨⟨{ hA.1.1.core_ok with }, hA.1.1.scratch_ok⟩, ?_, hA.1.2.2.1, hA.1.2.2.2.1,
    hA.1.2.2.2.2.1, hA.1.2.2.2.2.2⟩, hA.2.1, hA.2.2⟩
  exact { hA.1.2.1 with
    arena := { hA.1.2.1.arena with len_ok := hA.1.2.1.arena.len_ok }
    watches := hA.1.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }

private theorem s10RebuildOk_bcp {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sA : FullState} (hA : S10RebuildOk c F0 F_cur s sA)
    {valsB : List (BitVec 8)}
    {flagsB lvlB rsnsB trlB tpB wvecB arenaB wstkB : List (BitVec 32)}
    {teB propB wlenB : Nat} {unassB unflB wuB fuelB ctypeB crefB c0B c1B oomB ticksB : BitVec 64}
    {wsortB delayedB : List (BitVec 32)} {phasesB : List (BitVec 8)} :
    let sB : FullState :=
      { sA with
        core := { sA.core with
          vals := valsB, flags := flagsB, lvl := lvlB, rsns := rsnsB, trl := trlB,
          trail_pos := tpB, trail_end := teB, propagated := propB, unassigned := unassB,
          unflushed := unflB, wvec := wvecB, arena := arenaB, wstk := wstkB, wlen := wlenB,
          wusable := wuB, fuel := fuelB, confl_type := ctypeB, confl_ref := crefB,
          confl_lit0 := c0B, confl_lit1 := c1B, oom := oomB }
        scratch := { sA.scratch with
          search_ticks := ticksB, wsort := wsortB, phases := phasesB, delayed := delayedB } }
    sB.LengthsOk c → FullWitnessInv c F0 F_cur sB.core →
    FullArenaPermEq sA.core sB.core → fuelB.toNat ≤ sA.core.fuel.toNat →
    S10RebuildOk c F0 F_cur s sB := by
  intro sB hlenB hwB hpermB hfuelB
  have hndB : Full.FullArenaVarsNodup sB := fun ref href hng => by
    have href0 : ref ∈ fullArenaClauseRefs sA := by
      change ref ∈ fullArenaClauseRefsCore sB.core at href
      change ref ∈ fullArenaClauseRefsCore sA.core; rwa [← hpermB.2.1]
    have hp := hpermB.2.2 ref href0
    have hgb : fullArenaClauseGarb sA ref = false := by
      change fullArenaClauseGarbCore sA.core ref = false
      change fullArenaClauseGarbCore sB.core ref = false at hng; rwa [← hp.2.1]
    exact (hp.2.2.map (· / 2)).nodup_iff.mpr (hA.1.2.2.2.1 ref href0 hgb)
  have hllB : FullLastLearnedWf sB :=
    hA.1.2.2.2.2.1.1.of_refs_subset rfl fun ref href => by
      change ref ∈ fullArenaClauseRefsCore sA.core at href
      change ref ∈ fullArenaClauseRefsCore sB.core; rwa [hpermB.2.1]
  exact ⟨⟨hlenB, hwB, hA.1.2.2.1, hndB, ⟨hllB, hA.1.2.2.2.2.1.2⟩, hA.1.2.2.2.2.2⟩,
    hA.2.1, Nat.le_trans hfuelB hA.2.2⟩

end RebuildStep10

/-- Parametric `Func.wp` proof for `fidStep10RebuildWatchesNosortFn`
(`full_rebuild_watches_nosort_fid`, clearing `h->unflushed = 0ULL` when `sr == 0ULL`) against
`Full.fullRebuildWatchesSpec`. -/
theorem full_rebuild_watches_nosort_fid_step10_wp (Γ : Env)
    (hSweep : ∀ a m Q X, Full.fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hProp : ∀ a m Q X, FullM6BcpS15.fullBcpS15Spec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X) :
    ∀ a m Q X, Full.fullRebuildWatchesSpec a m Q X →
      Func.wp Γ fidStep10RebuildWatchesNosortFn.body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m0 Q X ⟨c, F0, s, R, rfl, hdn, hm0, hQ⟩
  obtain ⟨F_cur, hdw⟩ := hdn.exists_witness
  let s0 : FullState := { s with core := { s.core with dense_mode := 0#64 } }
  have hsp0 : FullSparseInvW c F0 F_cur s0 := hdw.toSparse_clear_dense
  have hok0 : S10RebuildOk c F0 F_cur s s0 := ⟨hsp0, hdw.2.2.2.2.2.1, Nat.le_refl _⟩
  unfold Func.wp fidStep10RebuildWatchesNosortFn; dsimp only
  unfold full_rebuild_watches_nosort_fid_body
  c0_hsteps_nogrp
  refine wp_join_group (ts := [])
    (fun () m1 => ∃ st : FullState, S10RebuildOk c F0 F_cur s st ∧ (FullMem c st ⋆ R) m1)
    (fun _ () m1 ⟨st, hok, hm1⟩ => by
      c0_hsteps_nogrp
      exact hQ 1#64 _ m1 hok.1.toSparse hok.2.1 hok.2.2 (Or.inr (Or.inl rfl))
        (fun h => by cases h) hm1)
    ?_
  intro Jbrk hJbrk
  c0_hsteps_nogrp
  refine wp_loop_group (ts := [])
    (fun rem () ml => ∃ st : FullState, rem = c.max_vars - st.core.trail_end ∧
      S10RebuildOk c F0 F_cur s st ∧ (FullMem c st ⋆ R) ml) ?_ ?_
  · rintro L rem ⟨⟩ ml ih ⟨st, rfl, hok_st, hm_st⟩
    dsimp only [Blocks.get]
    refine wp_jnz_of (fun _ => ?_) (fun hc => by cases hc)
    c0_hsteps_nogrp
    s10_call hSweep
    refine ⟨c, F0, F_cur, st, R, rfl, hok_st.1.1, hok_st.1.2.1, hok_st.1.2.2.2.1,
      hok_st.1.2.2.2.2.2, fun hpos => by have := hok_st.2.1; omega, hm_st,
      fun sr vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' arena' alen'
        wlen' wu' fred' ni' nr' nb' oom' sc' mA hlenA hsr_dom hextA _ hllA hwA hndA
        _ _ hsr1 hsr2 _ hmA => ?_⟩
    let sA : FullState :=
      { st with
        core := { st.core with
          vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
          trail_pos := tp', trail_end := te', unassigned := unass', unflushed := unfl',
          wvec := wvec', wstk := wstk', arena := arena', arena_len := alen', wlen := wlen',
          wusable := wu', arena_garbage := 0#64, first_reducible := fred', num_irred := ni',
          num_redundant := nr', num_binary := nb', oom := oom' }
        scratch := sc' }
    have hokA : S10RebuildOk c F0 F_cur s sA :=
      s10RebuildOk_sweep hok_st hlenA hwA hndA hllA hextA
    c0_hsteps_nogrp
    · exact hQ 20#64 sA mA hokA.1.toSparse hokA.2.1 hokA.2.2 (Or.inr (Or.inr rfl))
        (fun _ => (hsr2 hc).2) hmA
    · exact hQ 0#64 sA mA hokA.1.toSparse hokA.2.1 hokA.2.2 (Or.inl rfl)
        (fun h => by cases h) hmA
    · refine wp_join_group (ts := [])
        (fun () mA' => ∃ sA' : FullState,
          S10RebuildOk c F0 F_cur s sA' ∧ sA'.core.trail_end = te' ∧ (FullMem c sA' ⋆ R) mA')
        ?_ ?_
      · rintro _ ⟨⟩ mA' ⟨sA', hokA', hteA', hmA'⟩
        c0_hsteps_nogrp
        s10_call hProp
        refine ⟨c, F0, F_cur, sA', R, rfl, hokA'.1.1, hokA'.1.2.1, hokA'.1.2.2.2.2.2, hmA',
          fun pr valsB flagsB lvlB rsnsB trlB tpB teB propB unassB unflB wvecB arenaB wstkB
            wlenB wuB fuelB ctypeB crefB c0B c1B oomB ticksB wsortB phasesB delayedB mB
            hlenB hwB htrB hpermB _ hfuelB _ _ hpr1 _ _ hmB => ?_⟩
        let sB : FullState :=
          { sA' with
            core := { sA'.core with
              vals := valsB, flags := flagsB, lvl := lvlB, rsns := rsnsB, trl := trlB,
              trail_pos := tpB, trail_end := teB, propagated := propB, unassigned := unassB,
              unflushed := unflB, wvec := wvecB, arena := arenaB, wstk := wstkB, wlen := wlenB,
              wusable := wuB, fuel := fuelB, confl_type := ctypeB, confl_ref := crefB,
              confl_lit0 := c0B, confl_lit1 := c1B, oom := oomB }
            scratch := { sA'.scratch with
              search_ticks := ticksB, wsort := wsortB, phases := phasesB, delayed := delayedB } }
        have hokB : S10RebuildOk c F0 F_cur s sB :=
          s10RebuildOk_bcp hokA' hlenB hwB hpermB hfuelB
        c0_hsteps_nogrp
        · have hunsat : F0.Unsat :=
            FullVivTopSpecs.level0_unsat_of_conflict_okW hwB hokA'.2.1 (hpr1 hc).2.2
          exact hQ 20#64 sB mB hokB.1.toSparse hokB.2.1 hokB.2.2 (Or.inr (Or.inr rfl))
            (fun _ => hunsat) hmB
        · exact hJbrk () mB ⟨sB, hokB, hmB⟩
        · have hsr_eq1 : sr = 1#64 := by
            rcases hsr_dom with rfl | rfl | rfl | rfl <;> first | rfl | contradiction
          obtain ⟨_, hte_lt⟩ := hsr1 hsr_eq1
          have hte_bd : sB.core.trail_end ≤ c.max_vars :=
            Nat.le_trans hlenB.core_ok.trail_end_le hlenB.core_ok.cur_vars_le
          have hte_le : sA'.core.trail_end ≤ sB.core.trail_end := htrB.1
          rw [hteA'] at hte_le
          exact ih (c.max_vars - sB.core.trail_end) () mB (by omega) ⟨sB, rfl, hokB, hmB⟩
      · intro Junfl hJunfl
        c0_hsteps_nogrp
        · exact hJunfl () _
            ⟨{ sA with core := { sA.core with unflushed := 0#64 } },
              s10RebuildOk_unflushed hokA 0#64, rfl, by assumption⟩
        · exact hJunfl () mA ⟨sA, hokA, rfl, hmA⟩
  · intro L hL; c0_hsteps_nogrp
    exact hL (c.max_vars - s0.core.trail_end) () _ ⟨s0, rfl, hok0, by assumption⟩

/-! ## 3. `full_bve_def_k6_fid_step10_wp` (`m8BveGatesSpec`) -/

section BveStep10

private theorem s10_zext64_toNat (x : BitVec 32) :
    (BitVec.zeroExtend 64 x).toNat = x.toNat := by
  rw [show BitVec.zeroExtend 64 x = BitVec.setWidth 64 x from rfl, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (by have := x.isLt; omega)

end BveStep10

/-- Parametric `Func.wp` proof for `fidStep10BveDefK6Fn` (`full_bve_def_k6_fid`, clearing
`scr[4130]` and `scr[4131]` when 1-sided unit certification returns `false`) against
`FullM8CoreParity.m8BveGatesSpec`. -/
theorem full_bve_def_k6_fid_step10_wp (Γ : Env)
    (hMv : ∀ a m Q X, fidBveK6MvSpec a m Q X → Γ "full_bve_k6_mv_fid" [i64] [i64] a m Q X)
    (hExtSolve : ∀ a m Q X, fidK6ExtractSolveSpec a m Q X →
      Γ "full_k6_extract_and_solve_fid" [i64, i32, i32, i32, .bool, i32] [.bool] a m Q X)
    (hCertUnit : ∀ a m Q X, fidBveCertifyUnitSpec a m Q X →
      Γ "full_bve_certify_unit_fid" [i64, i32, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, m8BveGatesSpec a m Q X → Func.wp Γ fidStep10BveDefK6Fn.body a m Q X := by
  rintro ⟨h, v, np, nn, ⟨⟩⟩ m Q X hspec
  rcases m8BveGatesSpec_elim hspec with
    ⟨c, F0, F_cur, s, R, rfl, hinv, htmk, hcap, hv, hnp, hnn, henp, henn, hm, hQ⟩
  unfold fidStep10BveDefK6Fn full_bve_def_k6_fid_body Func.wp; dsimp only; c0_hsteps
  s10_call hMv; refine fidBveK6MvSpec_intro ?_; c0_hsteps
  · exact hQ s m hinv htmk rfl rfl rfl (Nat.le_refl _) (fun _ _ => rfl) (fun _ _ => rfl) hm
  · exact hQ s m hinv htmk rfl rfl rfl (Nat.le_refl _) (fun _ _ => rfl) (fun _ _ => rfl) hm
  · exact hQ s m hinv htmk rfl rfl rfl (Nat.le_refl _) (fun _ _ => rfl) (fun _ _ => rfl) hm
  · exact hQ s m hinv htmk rfl rfl rfl (Nat.le_refl _) (fun _ _ => rfl) (fun _ _ => rfl) hm
  · s10_call hExtSolve
    refine fidK6ExtractSolveSpec_intro rfl hinv htmk hcap hv hnp hnn henp henn hm ?_
    intro _ s1 m1 hinv1 htmk1 hcv1 har1 hal1 hfl1 hpres1 _ hm1
    have henp1 : ∀ idx < np.toNat,
        FullBveEntryOkW F_cur s1 (2 * v.toNat) (s1.scratch.scratch_buf[idx]?.getD 0#32) :=
      fun idx hidx => by
        rw [hpres1 idx (by omega)]; exact m8_bveEntry_congr_core (henp idx hidx) hcv1 har1 hal1
    have henn1 : ∀ idx < nn.toNat, FullBveEntryOkW F_cur s1 (2 * v.toNat + 1)
          (s1.scratch.scratch_buf[2001 + idx]?.getD 0#32) := fun idx hidx => by
      rw [hpres1 (2001 + idx) (by omega)]
      exact m8_bveEntry_congr_core (henn idx hidx) hcv1 har1 hal1
    c0_hsteps
    · s10_call hExtSolve
      refine fidK6ExtractSolveSpec_intro rfl hinv1 htmk1 hcap (by rw [hcv1]; exact hv)
        hnp hnn henp1 henn1 hm1 ?_
      intro _ s2 m2 hinv2 htmk2 hcv2 har2 hal2 hfl2 hpres2 _ hm2
      let scr2 := s2.scratch.scratch_buf
      have hlen2 : scr2.length = c.scratch_cap := hinv2.1.scratch_ok.scratch_buf_len
      have hpres02 : ∀ idx < 4002, scr2[idx]? = s.scratch.scratch_buf[idx]? := fun idx hidx => by
        rw [show scr2[idx]? = s1.scratch.scratch_buf[idx]? from hpres2 idx hidx]
        exact hpres1 idx hidx
      have henp2 : ∀ idx < np.toNat,
          FullBveEntryOkW F_cur s2 (2 * v.toNat) (scr2[idx]?.getD 0#32) := fun idx hidx => by
        rw [hpres02 idx (by omega)]
        exact m8_bveEntry_congr_core (henp idx hidx) (hcv2.trans hcv1) (har2.trans har1)
          (hal2.trans hal1)
      have henn2 : ∀ idx < nn.toNat,
          FullBveEntryOkW F_cur s2 (2 * v.toNat + 1) (scr2[2001 + idx]?.getD 0#32) :=
        fun idx hidx => by
          rw [hpres02 (2001 + idx) (by omega)]
          exact m8_bveEntry_congr_core (henn idx hidx) (hcv2.trans hcv1) (har2.trans har1)
            (hal2.trans hal1)
      c0_hsteps_nogrp
      · refine wp_while_state (fun st : Bool × Bool × BitVec 32 => (st.1, st.2.1, st.2.2, ()))
          (fun st => 64 - st.2.2.toNat) (fun _ m' => m' = m2)
          (fun J hJ => by c0_hsteps; exact hJ (false, false, 0#32) m2 rfl)
          (fun J (hp, hn, k) m' hm_eq ih => ?_)
        rw [hm_eq]; c0_hsteps_nogrp
        · refine wp_join_state1 (fun b : Bool => b) (fun _ m' => m' = m2)
            (fun J1 b m' hm_eq => by
              rw [hm_eq]; c0_hsteps_nogrp
              refine wp_join_state1 (fun b2 : Bool => b2) (fun _ m' => m' = m2)
                (fun J2 b2 m' hm_eq => by
                  rw [hm_eq]; c0_hsteps; have hk : k.toNat < 64 := by c0_bound
                  exact ih (b, b2, k + 1#32) m2 (by simp [BitVec.toNat_add]; omega) rfl)
                (fun J2 hJ2 => by
                  have hk : k.toNat < 64 := by c0_bound
                  have h4066 : (4066#32 + k).toNat = 4066 + k.toNat := by
                    simp [BitVec.toNat_add]; omega
                  have hlt : (BitVec.zeroExtend 64 (4066#32 + k)).toNat < scr2.length := by
                    rw [s10_zext64_toNat, h4066]; omega
                  c0_hsteps
                  · exact hJ2 true m2 rfl
                  · exact hJ2 hn m2 rfl))
            (fun J1 hJ1 => by
              have hk : k.toNat < 64 := by c0_bound
              have h4002 : (4002#32 + k).toNat = 4002 + k.toNat := by
                simp [BitVec.toNat_add]; omega
              have hlt : (BitVec.zeroExtend 64 (4002#32 + k)).toNat < scr2.length := by
                rw [s10_zext64_toNat, h4002]; omega
              c0_hsteps
              · exact hJ1 true m2 rfl
              · exact hJ1 hp m2 rfl)
        · have hret2 : Q () m2 := hQ s2 m2 hinv2 htmk2 (hcv2.trans hcv1) (har2.trans har1)
            (hal2.trans hal1) (Nat.le_trans hfl2 hfl1) (fun idx hidx => hpres02 idx (by omega))
            (fun idx hidx => hpres02 (2001 + idx) (by omega)) hm2
          have hpostCert : ∀ {s3 : FullState} {m3 : Mem 64}, FullDenseInvW c F0 F_cur s3 →
              TmkZero s3 → s3.core.cur_vars = s2.core.cur_vars → s3.core.arena = s2.core.arena →
              s3.core.arena_len = s2.core.arena_len → s3.core.fuel.toNat ≤ s2.core.fuel.toNat →
              (∀ i < 4192, s3.scratch.scratch_buf[i]? = s2.scratch.scratch_buf[i]?) →
              (Full.FullMem c s3 ⋆ R) m3 → Q () m3 := fun hi3 ht3 hcv3 har3 hal3 hfl3 hp3 hm3 =>
            hQ _ _ hi3 ht3 (hcv3.trans (hcv2.trans hcv1)) (har3.trans (har2.trans har1))
              (hal3.trans (hal2.trans hal1)) (Nat.le_trans hfl3 (Nat.le_trans hfl2 hfl1))
              (fun idx hidx => by rw [hp3 idx (by omega)]; exact hpres02 idx (by omega))
              (fun idx hidx => by
                rw [hp3 (2001 + idx) (by omega)]; exact hpres02 (2001 + idx) (by omega)) hm3
          have hpostCertClear : ∀ {s3 : FullState} {m3 : Mem 64},
              FullDenseInvW c F0 F_cur s3 → TmkZero s3 →
              s3.core.cur_vars = s2.core.cur_vars → s3.core.arena = s2.core.arena →
              s3.core.arena_len = s2.core.arena_len → s3.core.fuel.toNat ≤ s2.core.fuel.toNat →
              (∀ i < 4192, s3.scratch.scratch_buf[i]? = s2.scratch.scratch_buf[i]?) →
              (Full.FullMem c { s3 with scratch := { s3.scratch with
                scratch_buf := (s3.scratch.scratch_buf.set (BitVec.zeroExtend 64 4130#32).toNat
                  0#32).set (BitVec.zeroExtend 64 4131#32).toNat 0#32 } } ⋆ R) m3 →
              Q () m3 := fun {s3 m3} hi3 ht3 hcv3 har3 hal3 hfl3 hp3 hm3 => by
            let scr3 := s3.scratch.scratch_buf
            let scr4 := (scr3.set (BitVec.zeroExtend 64 4130#32).toNat 0#32).set
              (BitVec.zeroExtend 64 4131#32).toNat 0#32
            have hscr4_eq : scr4 = (scr3.set 4130 0#32).set 4131 0#32 := by simp [scr4]
            have hlen4 : scr4.length = c.scratch_cap := by
              rw [hscr4_eq]; simp [scr3, hi3.1.scratch_ok.scratch_buf_len]
            have hi4 : FullDenseInvW c F0 F_cur
                { s3 with scratch := { s3.scratch with scratch_buf := scr4 } } :=
              m8_fullDenseInvW_def hi3 hi3.1.core_ok.tmp_len_arr
                hi3.1.scratch_ok.wsort_len hi3.1.scratch_ok.tarjan_mark_len hlen4
            have hp04 : ∀ idx < 4002, scr4[idx]? = s.scratch.scratch_buf[idx]? := fun idx hi => by
              rw [hscr4_eq, List.getElem?_set_ne (by omega : 4131 ≠ idx),
                List.getElem?_set_ne (by omega : 4130 ≠ idx), hp3 idx (by omega)]
              exact hpres02 idx hi
            exact hQ _ _ hi4 ht3 (hcv3.trans (hcv2.trans hcv1)) (har3.trans (har2.trans har1))
              (hal3.trans (hal2.trans hal1)) (Nat.le_trans hfl3 (Nat.le_trans hfl2 hfl1))
              (fun idx hidx => hp04 idx (by omega))
              (fun idx hidx => hp04 (2001 + idx) (by omega)) hm3
          have hb_lt : 2 * v.toNat + 1 < 2 ^ 32 := by
            have h1 := hinv2.1.core_ok.cur_vars_le; have h2 := c.hmaxv
            unfold LeanQbe.T.Examples.LratBytes.dimacsBound at h2; omega
          c0_hsteps_nogrp
          refine wp_join0 (fun m' => Q () m') (fun J m' hQm => by c0_hsteps; exact hQm)
            (fun Jret hJret => by
              c0_hsteps_nogrp
              refine wp_join0 (fun m' => Q () m' ∧ (hp = true → m' = m2))
                (fun J1 m' ⟨hQm, hmeq⟩ => by
                  c0_hsteps
                  · exact hJret m' hQm
                  · have hme : m' = m2 := hmeq (by c0_bound); subst hme
                    s10_call hCertUnit; dsimp only [vals, Arg.val]
                    refine fidBveCertifyUnitSpec_intro rfl hinv2 htmk2 hcap ?_ hnp (by simp; omega)
                      (Or.inl rfl) (fun i hi => by
                        simp only [show (0 : BitVec 32).toNat = 0 from rfl, Nat.zero_add]
                        rw [show (v <<< OfNat.ofNat 1 : BitVec 32) = (v <<< 1) from rfl,
                          m8_bv32_shl1_toNat (by omega)]
                        exact henp2 i hi) hm2 ?_
                    · rw [show (v <<< OfNat.ofNat 1 : BitVec 32) = (v <<< 1) from rfl,
                        m8_bv32_shl1_toNat (by omega)]; omega
                    · intro _ s3 m3 hi3 ht3 hcv3 har3 hal3 hfl3 hp3 hm3
                      have hlen3 : s3.scratch.scratch_buf.length = c.scratch_cap :=
                        hi3.1.scratch_ok.scratch_buf_len
                      have hlt4130 : (BitVec.zeroExtend 64 4130#32).toNat <
                          s3.scratch.scratch_buf.length := by
                        rw [show (BitVec.zeroExtend 64 4130#32).toNat = 4130 from rfl]; omega
                      have hlt4131 : (BitVec.zeroExtend 64 4131#32).toNat <
                          s3.scratch.scratch_buf.length := by
                        rw [show (BitVec.zeroExtend 64 4131#32).toNat = 4131 from rfl]; omega
                      c0_hsteps
                      · exact hJret m3 (hpostCert hi3 ht3 hcv3 har3 hal3 hfl3 hp3 hm3)
                      · exact hJret _ (hpostCertClear hi3 ht3 hcv3 har3 hal3 hfl3 hp3
                          (by assumption))
                  · exact hJret m' hQm)
                (fun Jpos hJpos => by
                  c0_hsteps
                  · exact hJpos m2 ⟨hret2, fun _ => rfl⟩
                  · s10_call hCertUnit; dsimp only [vals, Arg.val]
                    refine fidBveCertifyUnitSpec_intro rfl hinv2 htmk2 hcap ?_ hnn (by simp; omega)
                      (Or.inr rfl) (fun i hi => by
                        simp only [show (2001 : BitVec 32).toNat = 2001 from rfl]
                        rw [show (v <<< OfNat.ofNat 1 ||| 1 : BitVec 32) = ((v <<< 1) ||| 1#32)
                          from rfl, m8_bv32_shl1_or1_toNat hb_lt]
                        exact henn2 i hi) hm2 ?_
                    · rw [show (v <<< OfNat.ofNat 1 ||| 1 : BitVec 32) = ((v <<< 1) ||| 1#32)
                        from rfl, m8_bv32_shl1_or1_toNat hb_lt]; omega
                    · intro _ s3 m3 hi3 ht3 hcv3 har3 hal3 hfl3 hp3 hm3
                      have hlen3 : s3.scratch.scratch_buf.length = c.scratch_cap :=
                        hi3.1.scratch_ok.scratch_buf_len
                      have hlt4130 : (BitVec.zeroExtend 64 4130#32).toNat <
                          s3.scratch.scratch_buf.length := by
                        rw [show (BitVec.zeroExtend 64 4130#32).toNat = 4130 from rfl]; omega
                      have hlt4131 : (BitVec.zeroExtend 64 4131#32).toNat <
                          s3.scratch.scratch_buf.length := by
                        rw [show (BitVec.zeroExtend 64 4131#32).toNat = 4131 from rfl]; omega
                      c0_hsteps
                      · exact hJret m3 (hpostCert hi3 ht3 hcv3 har3 hal3 hfl3 hp3 hm3)
                      · exact hJret _ (hpostCertClear hi3 ht3 hcv3 har3 hal3 hfl3 hp3
                          (by assumption))
                  · exact hJpos m2 ⟨hret2, fun _ => rfl⟩))
      · have hlt4130 : (BitVec.zeroExtend 64 4130#32).toNat < scr2.length := by
          rw [show (BitVec.zeroExtend 64 4130#32).toNat = 4130 from rfl]; omega
        have hlt4131 : (BitVec.zeroExtend 64 4131#32).toNat < scr2.length := by
          rw [show (BitVec.zeroExtend 64 4131#32).toNat = 4131 from rfl]; omega
        c0_hsteps
        let scr3 := (scr2.set (BitVec.zeroExtend 64 4130#32).toNat 0#32).set
          (BitVec.zeroExtend 64 4131#32).toNat 0#32
        have hscr3_eq : scr3 = (scr2.set 4130 0#32).set 4131 0#32 := by simp [scr3]
        have hlen3 : scr3.length = c.scratch_cap := by simp [hscr3_eq, hlen2]
        have hinv3 : FullDenseInvW c F0 F_cur
            { s2 with scratch := { s2.scratch with scratch_buf := scr3 } } :=
          m8_fullDenseInvW_def hinv2 hinv2.1.core_ok.tmp_len_arr
            hinv2.1.scratch_ok.wsort_len hinv2.1.scratch_ok.tarjan_mark_len hlen3
        have hpres03 : ∀ idx < 4002, scr3[idx]? = s.scratch.scratch_buf[idx]? := fun idx hidx => by
          rw [hscr3_eq, List.getElem?_set_ne (by omega : 4131 ≠ idx),
            List.getElem?_set_ne (by omega : 4130 ≠ idx)]
          exact hpres02 idx hidx
        exact hQ _ _ hinv3 htmk2 (hcv2.trans hcv1) (har2.trans har1) (hal2.trans hal1)
          (Nat.le_trans hfl2 hfl1) (fun idx hidx => hpres03 idx (by omega))
          (fun idx hidx => hpres03 (2001 + idx) (by omega)) (by assumption)
    · exact hQ s1 m1 hinv1 htmk1 hcv1 har1 hal1 hfl1 (fun idx hidx => hpres1 idx (by omega))
        (fun idx hidx => hpres1 (2001 + idx) (by omega)) hm1

end LeanQbe.T.Examples.Kissat.FullFidelityStep10

end
