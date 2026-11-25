/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityBcpProof2c

/-!
# Kissat Fidelity Delayed-Watch BCP Proofs — Part 2a (Inner Watch Loop)

Plain `public section` (`0` `@[expose]`, `0` `import all`). Proves `fid_lp_loop_wp`, the WP of
the inner `while (p < end)` watch loop `fidLpLoopExpr` of `full_propagate_ignore_fid`, threading the
delayed-watch buffer (`di = 3 * dlen`, `DelayedWatchesOk`) alongside `PropLitInv`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityBcp

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.FastCore
open LeanQbe.T.Examples.Kissat.FullM5Otfs
open LeanQbe.T.Examples.Kissat.FullM6BcpS15
open LeanQbe.T.Examples.Kissat.FullM7BcpHot
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullAnalyzeHelpers
open LeanQbe.T.Examples.Kissat.Full.FullPropDecSpecs hiding
  fullWatchPushSpec fullPropLitSpec fullPropagateIgnoreSpec fullPropagateSpec
  FullTrailExt FullArenaPermEq
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics

attribute [local irreducible] fastPropMem

local macro "fid_hsteps" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsteps))

local macro "fid_hsteps_nogrp" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsteps_nogrp))

local macro "fid_hsplit" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsplit))

/-! ## 1. Inner Watch Loop (`fidLpLoopExpr`) -/

/-- WP of the inner `while (p < end)` watch loop of `full_propagate_ignore_fid`: every exit (end of
slice, conflict, or full delayed buffer) reaches `J_ovf` with `PropLitInv` over the current delayed
buffer, `di = 3 * dlen`, and `DelayedWatchesOk` relative to the loop-entry base state. -/
theorem fid_lp_loop_wp {Γ : Env} {rs : List Ty} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s_orig s_disk sem0 : FullState}
    {cur_lvl32 not_lit nl_lvl : BitVec 32}
    {two_cv te0 un0 uf0 tk0 p0 q0 di0 dlim end0 off0 brk0 ignore_ref : BitVec 64}
    {rec_ph : Bool} {dlen0 : Nat}
    {R : Mem 64 → Prop} {m0 : Mem 64} {Q : Post rs} {X : XPost}
    {J_ovf : Cont [i64, i64, i64, i64, i64, i64, i64, i64, Ty.bool, i32, i32, i32, i64]}
    (hmaxv : c.max_vars < 2 * dimacsBound) (har : c.arena_cap < 2 * dimacsBound)
    (hwc : c.wcap < 2 * dimacsBound)
    (hpi0 : PropLitInv c F0 F_cur
      { s_orig with scratch := { s_orig.scratch with delayed := sem0.scratch.delayed } } sem0
      not_lit.toNat off0.toNat q0.toNat p0.toNat end0.toNat)
    (hnot_lt : not_lit.toNat < 2 * sem0.core.cur_vars)
    (htwo_cv : two_cv.toNat = 2 * sem0.core.cur_vars)
    (hcur_lvl : cur_lvl32 = BitVec.ofNat 32 sem0.core.cur_level)
    (hcl32 : sem0.core.cur_level < 2 ^ 32)
    (hte0 : te0.toNat = sem0.core.trail_end) (hun0 : un0 = sem0.core.unassigned)
    (huf0 : uf0 = sem0.core.unflushed) (hoom0 : sem0.core.oom = 0#64)
    (hbrk0 : brk0 = 0#64)
    (hnl : ∀ k : FullCoreState, FullPropDecSpecs.FullTrailExt s_orig.core k →
      k.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl)
    (hdi0 : di0.toNat = 3 * dlen0) (hdlen0 : dlen0 ≤ c.delayed_cap)
    (hdlim : dlim.toNat = 3 * c.delayed_cap)
    (hdok0 : DelayedWatchesOk s_orig.core sem0.scratch.delayed dlen0 not_lit.toNat)
    (hd00 : c.delayed_cap = 0 → sem0.scratch.delayed = s_orig.scratch.delayed)
    (hm0 : (FullMem c (fastPropMem s_disk sem0) ⋆ R) m0)
    (hJ_ovf : ∀ {sem' : FullState} {te' un' uf' tk' p' q' di' brk' : BitVec 64} {ovf' : Bool}
        {ovf_rw' ovf_oth' ovf_cr' : BitVec 32} {ovf_ri' : BitVec 64} {dlen' : Nat} {m' : Mem 64},
      PropLitInv c F0 F_cur
        { s_orig with scratch := { s_orig.scratch with delayed := sem'.scratch.delayed } } sem'
        not_lit.toNat off0.toNat q'.toNat p'.toNat end0.toNat →
      di'.toNat = 3 * dlen' → dlen' ≤ c.delayed_cap →
      DelayedWatchesOk s_orig.core sem'.scratch.delayed dlen' not_lit.toNat →
      (c.delayed_cap = 0 → sem'.scratch.delayed = s_orig.scratch.delayed) →
      p0.toNat ≤ p'.toNat → sem0.core.trail_end ≤ sem'.core.trail_end →
      te'.toNat = sem'.core.trail_end → un' = sem'.core.unassigned → uf' = sem'.core.unflushed →
      sem'.core.oom = 0#64 →
      (ovf' = false →
        (brk' = 0#64 → p' = end0 ∧ sem'.core.confl_type = sem0.core.confl_type) ∧
        (brk' = 1#64 → PropLitConfl F_cur ignore_ref sem'.core) ∧
        (brk' = 0#64 ∨ brk' = 1#64)) →
      (ovf' = true → brk' = 0#64 ∧ sem'.core.confl_type = sem0.core.confl_type ∧
        2 ≤ p'.toNat - off0.toNat ∧ q'.toNat + 2 ≤ p'.toNat ∧
        end0.toNat - p'.toNat < end0.toNat - p0.toNat ∧
        ovf_cr'.toNat < 0x80000000 ∧ ovf_cr'.toNat ∈ fullArenaClauseRefsCore sem'.core ∧
        ovf_cr'.toNat + 3 + fullArenaClauseSizeCore sem'.core ovf_cr'.toNat ≤
          sem'.core.arena_len ∧
        ovf_oth'.toNat < 2 * sem'.core.cur_vars ∧ ovf_rw'.toNat < 2 * sem'.core.cur_vars ∧
        ovf_rw'.toNat ≠ not_lit.toNat ∧ 2 ≤ ovf_ri'.toNat ∧
        ovf_ri'.toNat < fullArenaClauseSizeCore sem'.core ovf_cr'.toNat ∧
        sem'.core.arena[ovf_cr'.toNat + 3]? = some ovf_oth' ∧
        sem'.core.arena[ovf_cr'.toNat + 4]? = some not_lit ∧
        sem'.core.arena[ovf_cr'.toNat + 3 + ovf_ri'.toNat]? = some ovf_rw') →
      (FullMem c (fastPropMem s_disk sem') ⋆ R) m' →
      wp Γ Q X (.jump J_ovf (.var te', (.var un', (.var uf', (.var tk', (.var p', (.var q',
        (.var di', (.var brk', (.var ovf', (.var ovf_rw', (.var ovf_oth', (.var ovf_cr',
        (.var ovf_ri', ())))))))))))))) m') :
    wp Γ Q X (fidLpLoopExpr c.hdr ignore_ref c.pVals c.pWstk c.pArena c.pLevel c.pReason c.pTrail
      c.pTrailPos c.pFlags c.pPhases c.pDelayed dlim two_cv cur_lvl32 not_lit nl_lvl rec_ph end0
      brk0 te0 un0 uf0 tk0 p0 q0 di0 J_ovf) m0 := by
  subst hbrk0
  unfold fidLpLoopExpr
  refine wp_loop_group (fun rem (te_p, un_p, uf_p, tk_p, p_p, q_p, di_p, ()) mlp =>
      ∃ (sem_p : FullState) (dlen_p : Nat),
        rem = end0.toNat - p_p.toNat ∧ p0.toNat ≤ p_p.toNat ∧
        sem0.core.trail_end ≤ sem_p.core.trail_end ∧
        PropLitInv c F0 F_cur
          { s_orig with scratch := { s_orig.scratch with delayed := sem_p.scratch.delayed } }
          sem_p not_lit.toNat off0.toNat q_p.toNat p_p.toNat end0.toNat ∧
        di_p.toNat = 3 * dlen_p ∧ dlen_p ≤ c.delayed_cap ∧
        DelayedWatchesOk s_orig.core sem_p.scratch.delayed dlen_p not_lit.toNat ∧
        (c.delayed_cap = 0 → sem_p.scratch.delayed = s_orig.scratch.delayed) ∧
        te_p.toNat = sem_p.core.trail_end ∧ un_p = sem_p.core.unassigned ∧
        uf_p = sem_p.core.unflushed ∧ sem_p.core.oom = 0#64 ∧
        sem_p.core.confl_type = sem0.core.confl_type ∧
        (FullMem c (fastPropMem s_disk sem_p) ⋆ R) mlp) ?_ ?_
  · rintro J_lp rem ⟨te_p, un_p, uf_p, tk_p, p_p, q_p, di_p, ⟨⟩⟩ mlp ih
      ⟨sem_p, dlen_p, rfl, hp_ge, hte_ge, hpi_p, hdi_p, hdl_p, hdok_p, hd0_p, hte_p, hun_p,
        huf_p, hoom_p, hct_p, hmlp⟩
    have hcv_p0 : sem_p.core.cur_vars = sem0.core.cur_vars :=
      hpi_p.cur_vars_eq.trans hpi0.cur_vars_eq.symm
    have hnot_p : not_lit.toNat < 2 * sem_p.core.cur_vars := hcv_p0 ▸ hnot_lt
    have htwo_p : two_cv.toNat = 2 * sem_p.core.cur_vars := by rw [htwo_cv, hcv_p0]
    have hcl_p : sem_p.core.cur_level = sem0.core.cur_level :=
      (hpi_p.ag.get FullCoreState.cur_level).trans (hpi0.ag.get FullCoreState.cur_level).symm
    have hcur_p : cur_lvl32 = BitVec.ofNat 32 sem_p.core.cur_level := by rw [hcl_p, hcur_lvl]
    have hcl32_p : sem_p.core.cur_level < 2 ^ 32 := hcl_p ▸ hcl32
    have hnl_p : sem_p.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl := hnl _ hpi_p.tr
    fid_hsplit
    · have hp_lt : p_p.toNat < end0.toNat := hc
      have ⟨hend_le, hwlen_le⟩ := hpi_p.end_lt_wcap hnot_p
      have hp_ws : p_p.toNat < (fastPropMem s_disk sem_p).core.wstk.length := by
        rw [fastPropMem_wstk, hpi_p.len.core_ok.wstk_len_arr]
        exact lt_of_lt_of_le hp_lt (le_trans hend_le hwlen_le)
      have hw0_raw_lt : p_p.toNat < sem_p.core.wstk.length := by
        rw [hpi_p.len.core_ok.wstk_len_arr]
        exact lt_of_lt_of_le hp_lt (le_trans hend_le hwlen_le)
      let w0 := (fastPropMem s_disk sem_p).core.wstk[p_p.toNat]'hp_ws
      have hw0_get : sem_p.core.wstk[p_p.toNat]? = some w0 := by
        simpa only [w0, fc_getElem_wstk] using List.getElem?_eq_getElem hw0_raw_lt
      fid_hsteps_nogrp
      dsimp only at *
      fid_hsplit
      · refine fid_lp_bin_wp (ignore_ref := ignore_ref) hmaxv hwc hpi_p hnot_p hp_lt hw0_get hc
          hte_p hun_p huf_p hoom_p hnl_p hmlp ?_ ?_
        · intro sem' p' q' brk' m' hpi' hp' hte' hoom' hun' huf' hbrk' hcf' hm'
          have hd' : sem'.scratch.delayed = sem_p.scratch.delayed := by
            rw [fid_pi_delayed_eq hpi']
          exact hJ_ovf (fid_pi_rebase hpi') hdi_p hdl_p (hd' ▸ hdok_p)
            (fun h0 => hd'.trans (hd0_p h0)) (le_trans hp_ge hp')
            (by rw [← hte', hte_p]; exact hte_ge) hte'
            (hun_p.trans hun'.symm) (huf_p.trans huf'.symm) hoom'
            (fun _ => ⟨fun h => absurd h (by rw [hbrk']; decide), fun _ => hcf', Or.inr hbrk'⟩)
            (fun h => absurd h (by decide)) hm'
        · intro sem' te' un' uf' tk' p' q' m' hpi' hp_inc hp'_end hte_inc hte' hun' huf'
            hoom' hct' hm'
          have hd' : sem'.scratch.delayed = sem_p.scratch.delayed := by
            rw [fid_pi_delayed_eq hpi']
          exact ih (end0.toNat - p'.toNat) (te', un', uf', tk', p', q', di_p, ()) m'
            (by omega)
            ⟨sem', dlen_p, rfl, le_trans hp_ge (le_of_lt hp_inc), le_trans hte_ge hte_inc,
              fid_pi_rebase hpi', hdi_p, hdl_p, hd' ▸ hdok_p, fun h0 => hd'.trans (hd0_p h0),
              hte', hun', huf', hoom'.trans hoom_p, hct'.trans hct_p, hm'⟩
      · have hflag : (w0 &&& 0x80000000#32) = 0#32 := by
          simpa only [w0, BitVec.ofNat_eq_ofNat,
            show (2147483648#32 : BitVec 32) = 0x80000000#32 from rfl] using hc
        refine fid_lp_large_step_wp (s_orig := s_orig) hmaxv har hwc rfl hpi_p hnot_p htwo_p
          hcur_p hcl32_p hp_lt hw0_get hflag hte_p hun_p huf_p hoom_p hnl_p hdi_p hdl_p hdlim
          hdok_p hmlp ?_ ?_
        · intro sem' tk' p' q' brk' ovf' ovf_rw' ovf_oth' ovf_cr' ovf_ri' m' hpi' hte' hoom'
            hun' huf' hno hov hm'
          have hd' : sem'.scratch.delayed = sem_p.scratch.delayed := by
            rw [fid_pi_delayed_eq hpi']
          refine hJ_ovf (fid_pi_rebase hpi') hdi_p hdl_p (hd' ▸ hdok_p)
            (fun h0 => hd'.trans (hd0_p h0)) ?_ (by rw [← hte', hte_p]; exact hte_ge) hte'
            (hun_p.trans hun'.symm) (huf_p.trans huf'.symm) hoom' ?_ ?_ hm'
          · cases ovf'
            · exact le_trans hp_ge (hno rfl).1
            · exact le_trans hp_ge (le_of_lt (hov rfl).2.2.1)
          · intro hf; obtain ⟨hp', rfl, hcf⟩ := hno hf
            exact ⟨fun h => absurd h (by decide), fun _ => hcf, Or.inr rfl⟩
          · intro ht
            obtain ⟨rfl, hct', hp_inc, hp'_end, hp_off, hq_le', hcr_lt, hcr_ref, hcr_fit,
              hoth_lt, hrw_lt, hrw_ne, hri2, hri_lt, har3, har4, har_ri⟩ := hov ht
            dsimp only at hp_inc hp'_end
            exact ⟨rfl, hct'.trans hct_p, hp_off, hq_le', by omega, hcr_lt, hcr_ref, hcr_fit,
              hoth_lt, hrw_lt, hrw_ne, hri2, hri_lt, har3, har4, har_ri⟩
        · intro sem' te' un' uf' tk' p' q' di' dlen' m' hpi' hdi' hdl' hdok' hd0' hp_inc hp'_end
            hte_inc hte' hun' huf' hoom' hct' hm'
          dsimp only at hp_inc hp'_end
          exact ih (end0.toNat - p'.toNat) (te', un', uf', tk', p', q', di', ()) m'
            (by omega)
            ⟨sem', dlen', rfl, le_trans hp_ge (le_of_lt hp_inc), le_trans hte_ge hte_inc, hpi',
              hdi', hdl', hdok', fun h0 => (hd0' h0).trans (hd0_p h0), hte', hun', huf',
              hoom'.trans hoom_p, hct'.trans hct_p, hm'⟩
    · have hp_end : p_p = end0 :=
        BitVec.eq_of_toNat_eq (le_antisymm hpi_p.sw.p_le_end (Nat.le_of_not_lt hc))
      fid_hsteps
      exact hJ_ovf hpi_p hdi_p hdl_p hdok_p hd0_p hp_ge hte_ge hte_p hun_p huf_p hoom_p
        (fun _ => ⟨fun _ => ⟨hp_end, hct_p⟩, fun h => absurd h (by decide), Or.inl rfl⟩)
        (fun h => absurd h (by decide)) hmlp
  · intro J_lp hJ_lp
    fid_hsteps
    exact hJ_lp _ (te0, un0, uf0, tk0, p0, q0, di0, ()) m0
      ⟨sem0, dlen0, rfl, Nat.le_refl _, Nat.le_refl _, hpi0, hdi0, hdlen0, hdok0, hd00, hte0,
        hun0, huf0, hoom0, rfl, hm0⟩

end LeanQbe.T.Examples.Kissat.FullFidelityBcp
