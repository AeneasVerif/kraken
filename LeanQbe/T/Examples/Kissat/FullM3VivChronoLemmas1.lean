module

public import LeanQbe.T.Examples.Kissat.FullM3VivChrono
public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Examples.Kissat.FullBridgeLemmas3
public import LeanQbe.T.Examples.Kissat.FullVivTopLemmas1
public import LeanQbe.T.Examples.Kissat.FullFastBveBudgetsLemmas1
public import LeanQbe.T.Examples.Kissat.FullFastSchedLemmas
public import LeanQbe.T.Logic.C0HeadStep
public import LeanQbe.T.Logic.ControlComb
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat M3a `Func.wp` Proofs — Part 1 (`full_tick_rel`, `full_vivify`, `full_probe_tail`)

Proves `Func.wp` UNSAT soundness (`XPost := False`, `0` SAT proofs) for `3` of the `5` M3a
functions in `FullM3VivChrono`:
1. `full_tick_rel` against `Full.fullTickRelSpec` (`h->stable != 0` guard).
2. `full_vivify` against `FullFastBveBudgets.fullVivifyFastSpec` (persistent `PH_VIV` cursor with
   per-tier wrap-around clear only when reaching `h->arena_len`).
3. `full_probe_tail` against `FullFastSched.schedProbeTailSpec` (ticks-gated `full_transitive`,
   `full_probe_run`, and Tier-1/2/3/0 `full_vivify`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM3VivChrono

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullFastSched
open Kraken.Bedrock2.Test

/-! ## 1. `m3_tick_rel_wp` (`h->stable == 0` guard) -/

section TickRelProof

open FullBridgeHelpers
open scoped FullArenaTactics FullHeurWalkTactics

theorem m3_tick_rel_wp (Γ : Env) :
    ∀ a m Q X, fullTickRelSpec a m Q X → Func.wp Γ full_tick_rel_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  dsimp only [fullSafetySlice] at hm hlen
  c0_to_group
  · exact hQ () s m rfl hlen (probePres_refl s) hm
  · exact hQ () s m rfl hlen (probePres_refl s) hm
  · exact hQ () s m rfl hlen (probePres_refl s) hm
  · refine wp_join_group
      (fun _ m1 => ∃ s1 : FullState, PreservesCoreSlice FullState.core s s1 ∧
        s1.LengthsOk c ∧ FullProbeScratchPres s s1 ∧ (FullMem c s1 ⋆ R) m1)
      (fun _ _ m1 ⟨s1, hcore1, hlen1, hpres1, hm1⟩ => ?_) ?_
    · c0_to_group
      · exact hQ () s1 m1 hcore1 hlen1 hpres1 hm1
      · refine wp_join_group (fun _ m2 => m1 = m2) (fun _ _ m2 hm2 => ?_) ?_
        · rcases hm2 with rfl; c0_to_group
          refine wp_join_group (fun _ m3 => m1 = m3) (fun _ _ m3 hm3 => ?_) ?_
          · rcases hm3 with rfl; c0_to_group
            refine wp_join_group (fun _ m4 => m1 = m4) (fun _ _ m4 hm4 => ?_) ?_
            · rcases hm4 with rfl; c0_steps
              all_goals
                refine hQ () _ m ?_ ?_ ?_ hm
                · exact hcore1
                · exact hlen_upd_scalar hlen1 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
                    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
                · exact hpres1
            · intro Jm hJm; c0_steps; all_goals exact hJm _ _ rfl
          · intro Jm hJm; c0_steps; all_goals exact hJm _ _ rfl
        · intro Jm hJm; c0_steps; all_goals exact hJm _ _ rfl
    · intro Jm hJm; c0_steps
      · refine hJm _ _ ⟨_, ?_, ?_, ?_, hm⟩
        · exact rfl
        · exact hlen_upd_scalar hlen rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
            rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        · exact probePres_refl s
      · exact hJm _ _ ⟨s, rfl, hlen, probePres_refl s, hm⟩

end TickRelProof

/-! ## 2. `m3_vivify_wp` (persistent `PH_VIV` cursor + Tier-3 wrap-around clear) -/

section VivifyProof

open FullVivTopTactics FullVivTop
open scoped FullArenaTactics FullVivTopTactics

local macro "fvt_peel_tier" mp:ident hmp:ident : tactic => `(tactic| (
  intro Jtk hJtk
  fvt_to_group
  · exact hJtk _ $mp $hmp
  · refine wp_join_group (ts := [.bool]) (fun _ m1 => m1 = $mp)
      (fun _ x m1 hm => by c0_hsteps; rw [hm]; exact hJtk x $mp $hmp)
      (fun J1 hJ1 => ?_)
    fvt_to_group
    · c0_hsteps <;> exact hJ1 _ $mp rfl
    · refine wp_join_group (ts := [.bool]) (fun _ m2 => m2 = $mp)
        (fun _ x m2 hm => by c0_hsteps; rw [hm]; exact hJ1 x $mp rfl)
        (fun J2' hJ2' => by c0_hsteps <;> exact hJ2' _ $mp rfl)))

private theorem m3_viv_otfs_to_canon {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (h : FullVivTopSpecs.FullOtfsWitnessInv c F0 F_cur k) :
    FullOtfsWitnessInv c F0 F_cur k :=
  ⟨h.ext_sound, h.inconsistent_sound, h.arena, h.watches, h.cur_level_le, h.trail_lits_lt,
    h.trail_vars_nodup, h.vals_domain, h.vals_true_iff, h.vals_false_iff, h.lvl_le, h.dec_earliest,
    h.levels_inhabited, h.level0_sound, h.trail_pos_inv, h.level0_rsn_none, h.frame_trail_lt,
    h.frame_trail_mono, h.frame_trail_before_lt, h.frame_dec_lt, h.reason_inv_below,
    h.reason_lit_mem_below⟩

private theorem m3_viv_backtrack_adapter {Γ : Env}
    (hBt : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X) :
    ∀ a m Q X, FullVivTopSpecs.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X := by
  rintro ⟨h, tgt, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hcl64, htgt, htrl, hm, hQ⟩
  exact hBt _ m Q X ⟨c, s, R, rfl, hlen, hcl64, htgt, htrl, hm,
    fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m'
      hlen' hte hprop hcl hps _ htrl' _ hw_w hw_o hm' =>
      hQ vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m' hlen' hte hprop hcl hps htrl' hw_w
        (fun F0 Fc ho => hw_o F0 Fc (m3_viv_otfs_to_canon ho)) hm'⟩

private theorem m3_viv_prop_adapter {Γ : Env}
    (hProp : ∀ a m Q X, Full.fullPropagateSpec a m Q X → Γ "full_propagate" [i64] [i64] a m Q X) :
    ∀ a m Q X, FullVivTopSpecs.fullPropagateSpec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hnd, hdm, hm, hQ⟩
  refine hProp _ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm, hm, ?_⟩
  dsimp only
  intro r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
    fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' m'
    hlen' hw' htr hperm hfu hr hr0 hr1 hr2 hnp hm'
  let s' : FullState :=
    { s with
      core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                            trl := trl', trail_pos := tp', trail_end := te', propagated := prop',
                            unassigned := unass', unflushed := unfl', wvec := wvec',
                            arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
                            fuel := fuel', confl_type := ctype', confl_ref := cref',
                            confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
      scratch := { s.scratch with search_ticks := ticks', wsort := wsort', phases := phases' } }
  have hnd' : FullVivTopSpecs.FullArenaVarsNodup s' := by
    intro ref href hng
    have href0 : ref ∈ fullArenaClauseRefsCore s.core := hperm.2.1 ▸ href
    obtain ⟨_, hgb, hp⟩ := hperm.2.2 ref href0
    exact (hp.map (· / 2)).nodup_iff.mpr (hnd ref href0 (hgb.symm.trans hng))
  have hps' : FullVivTopSpecs.FullProbeScratchPres s s' :=
    ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact hQ r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
    fuel' ctype' cref' c0' c1' oom' s'.scratch m' hlen' hw' hnd' hps' htr.1 hfu
    (fun ref href => by change ref ∈ fullArenaClauseRefsCore _; rw [hperm.2.1]; exact href)
    htr.2.1 hr hr0 hr1 hr2 hnp hm'

theorem m3_vivify_wp (Γ : Env)
    (hBacktrack : ∀ args m Q X, Full.fullBacktrackSpec args m Q X →
      Γ "full_backtrack" [i64, i64] [] args m Q X)
    (hNext : ∀ args m Q X, Full.fullArenaNextSpec args m Q X →
      Γ "full_arena_next" [i64, i32] [i32] args m Q X)
    (hVivClause : ∀ args m Q X, Full.fullVivClauseSpec args m Q X →
      Γ "full_viv_clause" [i64, i32] [i64] args m Q X)
    (hProp : ∀ args m Q X, Full.fullPropagateSpec args m Q X →
      Γ "full_propagate" [i64] [i64] args m Q X) :
    ∀ args m Q X, fullVivifyFastSpec args m Q X →
      Func.wp Γ full_vivify_body args m Q X := by
  let hBt := m3_viv_backtrack_adapter hBacktrack
  let hPr := m3_viv_prop_adapter hProp
  rintro ⟨h, tier_mode, budget0, ⟨⟩⟩ m0 Q X ⟨c, F0, s, R, rfl, hsp0, hm0, hQ⟩
  have har_cap := c.harena; have hmx := c.hmaxv; unfold dimacsBound at har_cap hmx
  unfold Func.wp full_vivify_body; fvt_to_group
  -- Early guard: `if (budget == 0ULL) { return 1ULL; }`
  · fvt_steps
    exact hQ 1#64 s m0 hsp0 id id (fun hnz => absurd (by c0_bound) hnz)
      (Nat.le_refl _) (Or.inl rfl) (fun h => by cases h) hm0
  have hbud_ne : budget0 ≠ 0#64 := by c0_bound
  refine wp_join_group (ts := [])
    (fun () m1 => ∃ s1 : FullState, FullSparseInv c F0 s1 ∧ s1.core.cur_level = 0 ∧
      s1.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s1 ⋆ R) m1) ?_ ?_
  · rintro _ ⟨⟩ m1 ⟨s1, hsp1, hcl1, hfl1, hm1⟩
    fvt_to_group
    let s2 : FullState := { s1 with core := { s1.core with probing := 1#64 } }
    have hsp2 : FullSparseInv c F0 s2 := FullSparseInv.with_probing hsp1 1#64
    refine wp_loop_break_group (brkTs := [i64, i64, i64]) (lpTs := [i64, i64])
      (fun (_budget_b, _p_b, res_b, ()) mb => ∃ sb : FullState,
        FullSparseInv c F0 sb ∧ sb.core.cur_level = 0 ∧
        sb.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        (res_b = 1#64 ∨ res_b = 20#64) ∧ (res_b = 20#64 → F0.Unsat) ∧
        (FullMem c sb ⋆ R) mb)
      (fun rem (budget, p, ()) mp => ∃ sp : FullState,
        sp.core.arena_len ≤ c.arena_cap ∧ p.toNat ≤ sp.core.arena_len ∧
        rem = sp.core.arena_len - p.toNat ∧
        FullSparseInv c F0 sp ∧ sp.core.cur_level = 0 ∧
        sp.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        (p.toNat = sp.core.arena_len ∨ p.toNat ∈ fullArenaClauseRefs sp) ∧
        (FullMem c sp ⋆ R) mp) ?_ ?_ ?_
    · rintro _ ⟨_, _, res_b, ⟨⟩⟩ mb ⟨sb, hspb, hclb, hflb, hresb, h20b, hmb⟩
      fvt_steps
      · have hres1 : res_b = 1#64 := by c0_bound
        refine wp_loop_inv (ts := [i64])
          (fun (p2, ()) mp2 => ∃ sp2 : FullState,
            sp2.core.arena_len ≤ c.arena_cap ∧ p2.toNat ≤ sp2.core.arena_len ∧
            FullSparseInv c F0 sp2 ∧ sp2.core.cur_level = 0 ∧
            sp2.core.fuel.toNat ≤ s.core.fuel.toNat ∧
            (p2.toNat = sp2.core.arena_len ∨ p2.toNat ∈ fullArenaClauseRefs sp2) ∧
            (FullMem c sp2 ⋆ R) mp2)
          (fun (p2, ()) _ => c.arena_cap - p2.toNat) ?_ ?_
        · intro J2 hJ2; fvt_steps
          obtain ⟨F_curb, hswb⟩ := hspb.exists_witness
          have halb : sb.core.arena_len ≤ c.arena_cap := hspb.1.lengths.core_ok.arena_len_le
          have h0_mem : 0 = sb.core.arena_len ∨ 0 ∈ fullArenaClauseRefs sb := by
            rcases Nat.eq_zero_or_pos sb.core.arena_len with h0 | hpos
            · exact Or.inl h0.symm
            · exact Or.inr (fullArenaClauseRefs_zero_mem hswb.2.1.arena hpos)
          exact hJ2 (0#64, ()) mb ⟨sb, halb, Nat.zero_le _, hspb, hclb, hflb, h0_mem, hmb⟩
        · intro J2 (p2, ⟨⟩) mp2 ⟨sp2, hal2, hp2_le, hsp2, hcl2, hfl2, hp2_mem, hmp2⟩ ih2
          fvt_steps
          · have hp2_lt : p2.toNat < sp2.core.arena_len := by c0_bound
            have hp2_ref : p2.toNat ∈ fullArenaClauseRefs sp2 :=
              hp2_mem.resolve_left (by omega)
            obtain ⟨F_cur2, hsw2⟩ := hsp2.exists_witness
            have hcl_ok := hsp2.1.lengths.core_ok
            have hp2_lt_ar : p2.toNat < sp2.core.arena.length := by
              have := hcl_ok.arena_len_arr; omega
            have hp2_32 : (p2.setWidth 32).toNat = p2.toNat := by bv_omega
            let hdr2 := sp2.core.arena[p2.toNat]'hp2_lt_ar
            have hhdr2 : fullArenaHdr sp2 p2.toNat = hdr2 := by
              unfold fullArenaHdr fullArenaHdrCore
              rw [List.getElem?_eq_getElem hp2_lt_ar, Option.getD_some]
            fvt_to_group
            refine wp_join_group (ts := [])
              (fun () mp3 => ∃ sp3 : FullState,
                sp3.core.arena_len = sp2.core.arena_len ∧
                sp3.core.arena_len ≤ c.arena_cap ∧
                FullSparseInv c F0 sp3 ∧ sp3.core.cur_level = 0 ∧
                sp3.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                p2.toNat ∈ fullArenaClauseRefs sp3 ∧
                (FullMem c sp3 ⋆ R) mp3) ?_ ?_
            · rintro _ ⟨⟩ mp3 ⟨sp3, hal3_eq, hal3, hsp3, hcl3, hfl3, hp2_ref3, hmp3⟩
              fvt_steps
              c0_call hNext
              refine ⟨c, sp3, R, rfl, hsp3.1.lengths, hmp3, ?_⟩
              obtain ⟨F_cur3, hsw3⟩ := hsp3.exists_witness
              have hwf3 := hsw3.2.1.arena.refs_wf p2.toNat hp2_ref3
              let np2_nat := fullArenaNextOff sp3.core.arena sp3.core.arena_len p2.toNat
              have hnb : p2.toNat < np2_nat ∧ np2_nat ≤ sp3.core.arena_len := by
                dsimp only [np2_nat]
                simpa using fullArenaNextOff_bounds hwf3.1
              have hnp2_mem :
                  np2_nat = sp3.core.arena_len ∨ np2_nat ∈ fullArenaClauseRefs sp3 := by
                dsimp only [np2_nat]
                exact fullArenaClauseRefs_next_mem_or_end hsw3.2.1.arena hp2_ref3
              have hnp2_bv : ((BitVec.ofNat 32 np2_nat).setWidth 64).toNat = np2_nat := by
                rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
                  Nat.mod_eq_of_lt (by omega)]
              have hrem2 : c.arena_cap - ((BitVec.ofNat 32 np2_nat).setWidth 64).toNat <
                  c.arena_cap - p2.toNat := by rw [hnp2_bv]; omega
              simp only [hp2_32]
              exact ih2 ((BitVec.ofNat 32 np2_nat).setWidth 64, ()) _ hrem2
                ⟨sp3, hal3, by rw [hnp2_bv]; exact hnb.2, hsp3, hcl3, hfl3,
                  by rw [hnp2_bv]; exact hnp2_mem, hmp3⟩
            · intro Jn2 hJn2
              fvt_to_group
              · refine wp_join_group (ts := [.bool])
                  (fun (_take, ()) mn => (FullMem c sp2 ⋆ R) mn) ?_ ?_
                · rintro _ ⟨take, ⟨⟩⟩ mn hmn
                  dsimp only at hmn
                  fvt_steps
                  · let hdr2' := hdr2 &&& ~~~0x00100000#32
                    obtain ⟨hsw_cl, hrefs_cl, _⟩ := fullArena_setHdr_preserves_sparseW hsw2 hp2_ref
                      (hdr' := hdr2') (by rw [hhdr2]; exact bv32_clr_viv_garb hdr2)
                      (by rw [hhdr2]; exact bv32_clr_viv_shrk hdr2)
                    let s_cl : FullState :=
                      { sp2 with
                        core := { sp2.core with arena := sp2.core.arena.set p2.toNat hdr2' } }
                    have hp2_ref_cl : p2.toNat ∈ fullArenaClauseRefs s_cl := by
                      rw [hrefs_cl]; exact hp2_ref
                    exact hJn2 () _ ⟨s_cl, rfl, hal2, hsw_cl.toSparse, hcl2, hfl2, hp2_ref_cl,
                      by assumption⟩
                  · exact hJn2 () mn ⟨sp2, rfl, hal2, hsp2, hcl2, hfl2, hp2_ref, hmn⟩
                · fvt_peel_tier mp2 hmp2
              · exact hJn2 () mp2 ⟨sp2, rfl, hal2, hsp2, hcl2, hfl2, hp2_ref, hmp2⟩
          · subst hres1
            let sf : FullState := { sp2 with core := { sp2.core with probing := 0#64 } }
            have hspf : FullSparseInv c F0 sf := FullSparseInv.with_probing hsp2 0#64
            exact hQ 1#64 sf m hspf (fun _ => hcl2) (fun _ => rfl) (fun _ => ⟨hcl2, rfl⟩)
              hfl2 (Or.inl rfl) (fun h => by cases h) hm
      · let sf : FullState := { sb with core := { sb.core with probing := 0#64 } }
        have hspf : FullSparseInv c F0 sf := FullSparseInv.with_probing hspb 0#64
        exact hQ res_b sf m hspf (fun _ => hclb) (fun _ => rfl) (fun _ => ⟨hclb, rfl⟩)
          hflb hresb h20b hm
      · let sf : FullState := { sb with core := { sb.core with probing := 0#64 } }
        have hspf : FullSparseInv c F0 sf := FullSparseInv.with_probing hspb 0#64
        exact hQ res_b sf m hspf (fun _ => hclb) (fun _ => rfl) (fun _ => ⟨hclb, rfl⟩)
          hflb hresb h20b hm
    · intro B L rem (budget, p, ⟨⟩) mp hB hL
        ⟨sp, halp, hp_le, hrem, hspp, hclp, hflp, hp_mem, hmp⟩
      subst hrem; clear hm
      fvt_steps
      · have hp_lt : p.toNat < sp.core.arena_len := by c0_bound
        have hp_ref : p.toNat ∈ fullArenaClauseRefs sp := hp_mem.resolve_left (by omega)
        obtain ⟨F_curp, hswp⟩ := hspp.exists_witness
        have hwfp := hswp.2.1.arena.refs_wf p.toNat hp_ref
        have hcl_ok := hspp.1.lengths.core_ok
        have hp_lt_ar : p.toNat < sp.core.arena.length := by have := hcl_ok.arena_len_arr; omega
        have hp_32 : (p.setWidth 32).toNat = p.toNat := by bv_omega
        fvt_steps
        c0_call hNext
        refine ⟨c, sp, R, rfl, hspp.1.lengths, hmp, ?_⟩
        let np_nat := fullArenaNextOff sp.core.arena sp.core.arena_len (p.setWidth 32).toNat
        have hnb : p.toNat < np_nat ∧ np_nat ≤ sp.core.arena_len := by
          dsimp only [np_nat]; rw [hp_32]; exact fullArenaNextOff_bounds hwfp.1
        have hnp_mem : np_nat = sp.core.arena_len ∨ np_nat ∈ fullArenaClauseRefs sp := by
          dsimp only [np_nat]; rw [hp_32]
          exact fullArenaClauseRefs_next_mem_or_end hswp.2.1.arena hp_ref
        have hnp_bv : ((BitVec.ofNat 32 np_nat).setWidth 64).toNat = np_nat := by
          rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
            Nat.mod_eq_of_lt (by omega)]
        dsimp only; fvt_to_group
        refine wp_join_group (ts := [i64, i64])
          (fun (budget', _res', ()) mn => ∃ sn : FullState,
            sn.core.arena_len = sp.core.arena_len ∧
            sn.core.arena_len ≤ c.arena_cap ∧ np_nat ≤ sn.core.arena_len ∧
            FullSparseInv c F0 sn ∧ sn.core.cur_level = 0 ∧
            sn.core.fuel.toNat ≤ s.core.fuel.toNat ∧
            (np_nat = sn.core.arena_len ∨ np_nat ∈ fullArenaClauseRefs sn) ∧
            (FullMem c sn ⋆ R) mn) ?_ ?_
        · rintro _ ⟨budget', _, ⟨⟩⟩ mn
            ⟨sn, haln_eq, haln, hnp_le, hspn, hcln, hfln, hnp_memn, hmn⟩
          fvt_steps
          have hrem1 : sn.core.arena_len - ((BitVec.ofNat 32 np_nat).setWidth 64).toNat <
              sp.core.arena_len - p.toNat := by rw [hnp_bv, haln_eq]; omega
          exact hL _ (budget', (BitVec.ofNat 32 np_nat).setWidth 64, ()) mn hrem1
            ⟨sn, haln, by rw [hnp_bv]; exact hnp_le, rfl, hspn, hcln, hfln,
              by rw [hnp_bv]; exact hnp_memn, hmn⟩
        · intro Jn hJn; fvt_to_group
          · have hgarb_z : (sp.core.arena[p.toNat]'hp_lt_ar &&& 0x00180000#32) = 0#32 := by
              c0_bound
            have hngp : fullArenaClauseGarb sp p.toNat = false := by
              unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
              rw [List.getElem?_eq_getElem hp_lt_ar, Option.getD_some,
                bv32_garb_zero_of_and_viv hgarb_z]; rfl
            refine wp_join_group (ts := [.bool])
              (fun (_take, ()) mn => (FullMem c sp ⋆ R) mn) ?_ ?_
            · rintro _ ⟨take, ⟨⟩⟩ mn hmn
              fvt_steps
              · c0_call hVivClause
                refine ⟨c, F0, F_curp, sp, R, rfl, hswp, hclp, by simpa [hp_32] using hp_ref,
                  by simpa [hp_32] using hngp, hmn,
                  fun vc s_vc m_vc hsw_vc hcl_vc hfl_vc hal_vc hrefs_vc hvc h20_vc hm_vc => ?_⟩
                fvt_steps
                · exact hB (budget - 1#64, p, 20#64, ()) m_vc
                    ⟨s_vc, hsw_vc.toSparse, hcl_vc, Nat.le_trans hfl_vc hflp,
                      Or.inr rfl, fun _ => h20_vc (by c0_bound), hm_vc⟩
                · c0_call hPr
                  refine ⟨c, F0, F_curp, s_vc, R, rfl, hsw_vc.1, hsw_vc.2.1, hsw_vc.2.2.2.1,
                    hsw_vc.2.2.2.2.2, hm_vc,
                    fun pr vals_p flags_p lvl_p rsns_p trl_p tp_p te_p prop_p unass_p unfl_p
                      wvec_p arena_p wstk_p wlen_p wu_p fuel_p ctype_p cref_p c0_p c1_p oom_p sc_p
                      m_p hlen_p hw_p hnd_p hpres_p _ hfl_p hrefs_p _ hpr_disj
                      _ hpr1 _ _ hm_p => ?_⟩
                  let s_p : FullState :=
                    { s_vc with
                      core := { s_vc.core with
                        vals := vals_p, flags := flags_p, lvl := lvl_p, rsns := rsns_p,
                        trl := trl_p, trail_pos := tp_p, trail_end := te_p, propagated := prop_p,
                        unassigned := unass_p, unflushed := unfl_p, wvec := wvec_p,
                        arena := arena_p, wstk := wstk_p, wlen := wlen_p, wusable := wu_p,
                        fuel := fuel_p, confl_type := ctype_p, confl_ref := cref_p,
                        confl_lit0 := c0_p, confl_lit1 := c1_p, oom := oom_p }
                      scratch := sc_p }
                  have hsw_p : FullSparseInvW c F0 F_curp s_p :=
                    fullSparseInvW_of_prop_state hsw_vc hlen_p hw_p hnd_p hpres_p hrefs_p
                  have hcl_p : s_p.core.cur_level = 0 := hcl_vc
                  have hfl_p' : s_p.core.fuel.toNat ≤ s.core.fuel.toNat :=
                    Nat.le_trans hfl_p (Nat.le_trans hfl_vc hflp)
                  have hal_p : s_p.core.arena_len = sp.core.arena_len := hal_vc
                  fvt_steps
                  · have hpr_eq1 : pr = 1#64 := by c0_bound
                    have hunsat : F0.Unsat :=
                      level0_unsat_of_conflict_okW hw_p hcl_p (hpr1 hpr_eq1).2.2
                    exact hB (budget - 1#64, p, 20#64, ()) m_p
                      ⟨s_p, hsw_p.toSparse, hcl_p, hfl_p', Or.inr rfl, fun _ => hunsat, hm_p⟩
                  · have hnp_mem_p : np_nat = s_p.core.arena_len ∨
                        np_nat ∈ fullArenaClauseRefs s_p := by
                      rw [hal_p]
                      rcases hnp_mem with h | h
                      · exact Or.inl h
                      · exact Or.inr (hrefs_p _ (hrefs_vc ▸ h))
                    exact hJn (budget - 1#64, 1#64, ()) m_p
                      ⟨s_p, hal_p, by rw [hal_p]; exact halp, by rw [hal_p]; exact hnb.2,
                        hsw_p.toSparse, hcl_p, hfl_p', hnp_mem_p, hm_p⟩
              · exact hJn (budget, 1#64, ()) _
                  ⟨sp, rfl, halp, hnb.2, hspp, hclp, hflp, hnp_mem, hmn⟩
            · fvt_peel_tier mp hmp
          · exact hJn (budget, 1#64, ()) _ ⟨sp, rfl, halp, hnb.2, hspp, hclp, hflp, hnp_mem, hmp⟩
      · exact hB (budget, p, 1#64, ()) mp
          ⟨sp, hspp, hclp, hflp, Or.inl rfl, (fun h => by cases h), hmp⟩
      · exact hB (budget, p, 1#64, ()) mp
          ⟨sp, hspp, hclp, hflp, Or.inl rfl, (fun h => by cases h), hmp⟩
      · exact hB (budget, p, 1#64, ()) mp
          ⟨sp, hspp, hclp, hflp, Or.inl rfl, (fun h => by cases h), hmp⟩
      · exact hB (budget, p, 1#64, ()) mp
          ⟨sp, hspp, hclp, hflp, Or.inl rfl, (fun h => by cases h), hmp⟩
    · intro B L hB hL; fvt_steps
      obtain ⟨F_cur2, hsw2⟩ := hsp2.exists_witness
      have hal2 : s2.core.arena_len ≤ c.arena_cap := hsp2.1.lengths.core_ok.arena_len_le
      have h0_mem : 0 = s2.core.arena_len ∨ 0 ∈ fullArenaClauseRefs s2 := by
        rcases Nat.eq_zero_or_pos s2.core.arena_len with h0 | hpos
        · exact Or.inl h0.symm
        · exact Or.inr (fullArenaClauseRefs_zero_mem hsw2.2.1.arena hpos)
      exact hL s2.core.arena_len (budget0, 0#64, ()) _
        ⟨s2, hal2, Nat.zero_le _, by simp, hsp2, hcl1, hfl1, h0_mem, hm⟩
  · intro Jc hJc
    obtain ⟨F_cur0, hsw0⟩ := hsp0.exists_witness
    have hcl0_lt : s.core.cur_level < 2 ^ 64 := by
      have := hsw0.2.1.cur_level_le; have := hsp0.1.lengths.core_ok.trail_end_le
      have := hsp0.1.lengths.core_ok.cur_vars_le; omega
    fvt_steps
    · c0_call hBt
      refine ⟨c, s, R, rfl, hsp0.1.lengths, hcl0_lt,
        fun h => by
          have h0n : (0 : BitVec 64).toNat = 0 := rfl; rw [h0n] at h
          have := hsw0.2.1.cur_level_le; have := hsp0.1.lengths.core_ok.trail_end_le
          have := hsp0.1.lengths.core_ok.cur_vars_le; omega,
        hsw0.2.1.trail_lits_lt, hm0,
        fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m1
          hlen1 _ _ hcl1 hpres1 _ hw_bt _ hm1 => ?_⟩
      have hsp1 : FullSparseInv c F0 _ :=
        FullSparseInv.of_backtrack hsp0 (Nat.zero_le _) hlen1 hpres1 (by simpa using hw_bt F0)
      exact hJc () m1 ⟨_, hsp1, by rw [hcl1]; simp, Nat.le_refl _, hm1⟩
    · have hcl0 : s.core.cur_level = 0 := by
        have h0 : (BitVec.ofNat 64 s.core.cur_level).toNat = 0 := by rw [hc]; rfl
        rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcl0_lt] at h0
      exact hJc () m0 ⟨s, hsp0, hcl0, Nat.le_refl _, hm0⟩

end VivifyProof

/-! ## 3. `m3_probe_tail_wp` (Tier-1/2/3/0 vivification + M2 budgets) -/

section ProbeTailProof

open scoped FullArenaTactics

theorem m3_probe_tail_wp (Γ : Env)
    (hTrans : ∀ a m Q X, fullTransitiveFastSpec a m Q X →
      Γ "full_transitive" [i64, i64] [i64] a m Q X)
    (hMin : ∀ a m Q X, schedMinU64Spec a m Q X →
      Γ "full_min_u64" [i64, i64] [i64] a m Q X)
    (hPRun : ∀ a m Q X, fullProbeRunFastSpec a m Q X →
      Γ "full_probe_run" [i64, i64] [i64] a m Q X)
    (hViv : ∀ a m Q X, fullVivifyFastSpec a m Q X →
      Γ "full_vivify" [i64, i64, i64] [i64] a m Q X) :
    ∀ a m Q X, schedProbeTailSpec a m Q X → Func.wp Γ full_probe_tail_body a m Q X := by
  rintro ⟨h, dticks, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hcl0, hm, hQ⟩
  unfold Func.wp full_probe_tail_body
  c0_hsteps_nogrp
  -- Join after optional `full_transitive`
  refine wp_join_state0 (α := FullState)
    (fun s1 m1 => FullSparseInv c F0 s1 ∧ s1.core.cur_level = 0 ∧
      s1.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s1 ⋆ R) m1)
    (fun _ s1 m1 ⟨hinv1, hcl1, hfu1, hm1⟩ => by
      c0_hsteps; c0_call hMin; intro pbud _
      c0_hsteps_nogrp
      -- Join after optional `full_probe_run`
      refine wp_join_state0 (α := FullState)
        (fun s2 m2 => FullSparseInv c F0 s2 ∧ s2.core.cur_level = 0 ∧
          s2.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s2 ⋆ R) m2)
        (fun _ s2 m2 ⟨hinv2, hcl2, hfu2, hm2⟩ => by
          c0_hsteps; c0_call hMin; intro v1 _
          c0_hsteps; c0_call hMin; intro v0 _
          c0_hsteps; c0_call hViv; refine ⟨c, F0, s2, R, rfl, hinv2, hm2, ?_⟩
          intro r3 s3 m3 hinv3 hcl3 _ _ hfu3 _ hu3 hm3; c0_hsteps
          · exact hQ 20#64 s3 m3 hinv3 (hcl3 hcl2) (by omega) (Or.inr rfl) (fun _ => hu3 hc) hm3
          c0_call hViv; refine ⟨c, F0, s3, R, rfl, hinv3, hm3, ?_⟩
          intro r4 s4 m4 hinv4 hcl4 _ _ hfu4 _ hu4 hm4; c0_hsteps
          · exact hQ 20#64 s4 m4 hinv4 (hcl4 (hcl3 hcl2)) (by omega) (Or.inr rfl)
              (fun _ => hu4 hc) hm4
          c0_call hViv; refine ⟨c, F0, s4, R, rfl, hinv4, hm4, ?_⟩
          intro r5 s5 m5 hinv5 hcl5 _ _ hfu5 _ hu5 hm5; c0_hsteps
          · exact hQ 20#64 s5 m5 hinv5 (hcl5 (hcl4 (hcl3 hcl2))) (by omega) (Or.inr rfl)
              (fun _ => hu5 hc) hm5
          c0_call hViv; refine ⟨c, F0, s5, R, rfl, hinv5, hm5, ?_⟩
          intro r6 s6 m6 hinv6 hcl6 _ _ hfu6 _ hu6 hm6; c0_hsteps
          · exact hQ 20#64 s6 m6 hinv6 (hcl6 (hcl5 (hcl4 (hcl3 hcl2)))) (by omega) (Or.inr rfl)
              (fun _ => hu6 hc) hm6
          exact hQ 1#64 s6 m6 hinv6 (hcl6 (hcl5 (hcl4 (hcl3 hcl2)))) (by omega) (Or.inl rfl)
            (fun h => by cases h) hm6)
        (fun J2 hJ2 => by
          c0_hsplit
          · c0_hsteps; c0_call hPRun; refine ⟨c, F0, s1, R, rfl, hinv1, hm1, ?_⟩
            intro rp s2 m2 hinv2 hcl2 _ _ hfu2 _ hup2 hm2; c0_hsteps
            · exact hQ 20#64 s2 m2 hinv2 (hcl2 hcl1) (by omega) (Or.inr rfl)
                (fun _ => hup2 hc) hm2
            exact hJ2 s2 m2 ⟨hinv2, hcl2 hcl1, by omega, hm2⟩
          · c0_hsteps; exact hJ2 s1 m1 ⟨hinv1, hcl1, hfu1, hm1⟩))
    (fun J1 hJ1 => by
      c0_hsplit
      · c0_hsteps; c0_call hTrans; refine ⟨c, F0, s, R, rfl, hinv, hm, ?_⟩
        intro rt s1 m1 hinv1 hcl1 _ _ hfu1 _ hut1 hm1; c0_hsteps
        · exact hQ 20#64 s1 m1 hinv1 (hcl1 hcl0) hfu1 (Or.inr rfl) (fun _ => hut1 hc) hm1
        exact hJ1 s1 m1 ⟨hinv1, hcl1 hcl0, hfu1, hm1⟩
      · c0_hsteps; exact hJ1 s m ⟨hinv, hcl0, Nat.le_refl _, hm⟩)

end ProbeTailProof

end LeanQbe.T.Examples.Kissat.FullM3VivChrono
