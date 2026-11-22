module

public import LeanQbe.T.Examples.Kissat.FullBvaHeapSpec
import LeanQbe.T.Logic.ControlComb
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` 3-Hop BVA & Heap Factoring Proofs — Part 1 (`FreshVar, 3-Hop, FHeap`)

Proves parametric `(Γ : Env)` `Func.wp` contracts for:
- `full_init_fresh_var` (`full_init_fresh_var_heap_wp` + canonical `full_init_fresh_var_wp`)
- `full_bva_hop1`, `full_bva_hop2`, `full_bva_hop3`
- `full_fheap_up`, `full_fheap_down`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullBvaHeap

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test
open FullBvaHeapTactics FullBvaHeapHelpers
open scoped FullArenaTactics FullBvaHeapTactics

/-! ## 4. `full_init_fresh_var_heap_wp` & Canonical `full_init_fresh_var_wp` -/

private theorem initFreshVar_post {c : FullCfg} {s s' : FullState} {fv : BitVec 32}
    {R : Mem 64 → Prop} {Q : Post []} {m' : Mem 64}
    (hfv_lt : fv.toNat < s.core.cur_vars) (hclen : s.core.LengthsOk c) (hlen' : s'.LengthsOk c)
    (hcv_le : s.core.cur_vars ≤ c.max_vars)
    (hcore : s'.core =
      { s.core with
        wvec := (((s.core.wvec.set (4 * fv.toNat) 0#32).set (4 * fv.toNat + 1) 0#32).set
          (4 * fv.toNat + 2) 0#32).set (4 * fv.toNat + 3) 0#32
        vals := (s.core.vals.set (2 * fv.toNat) 0#8).set (2 * fv.toNat + 1) 0#8
        mrk := s.core.mrk.set fv.toNat 0#8, lvl := s.core.lvl.set fv.toNat 0#32
        rsns := s.core.rsns.set fv.toNat 0xFFFFFFFF#32, flags := s.core.flags.set fv.toNat 1145#32
        unassigned := s.core.unassigned + 1#64 })
    (hext_pres : FullExtScratchPres s s')
    (hsb : s'.scratch.scratch_buf = s.scratch.scratch_buf)
    (hws : s'.scratch.wsort = s.scratch.wsort)
    (htm : s'.scratch.tarjan_mark = s.scratch.tarjan_mark)
    (htr : s'.scratch.tarjan_reach = s.scratch.tarjan_reach)
    (hss : s'.scratch.sim_sig = s.scratch.sim_sig)
    (hm' : (FullMem c s' ⋆ R) m')
    (hQ : ∀ vals' mrk' flags' lvl' rsns' wvec' unass' sc' m',
      let s1 : FullState :=
        { s with
          core := { s.core with vals := vals', mrk := mrk', flags := flags', lvl := lvl',
                                rsns := rsns', wvec := wvec', unassigned := unass' }
          scratch := sc' }
      s1.LengthsOk c → FullExtScratchPres s s1 →
      sc'.scratch_buf = s.scratch.scratch_buf → sc'.wsort = s.scratch.wsort →
      sc'.tarjan_mark = s.scratch.tarjan_mark → sc'.tarjan_reach = s.scratch.tarjan_reach →
      sc'.sim_sig = s.scratch.sim_sig →
      vals'[2 * fv.toNat]?.getD 1#8 = 0#8 → vals'[2 * fv.toNat + 1]?.getD 1#8 = 0#8 →
      (∀ l < 2 * c.max_vars, l / 2 ≠ fv.toNat → vals'[l]? = s.core.vals[l]?) →
      mrk'[fv.toNat]?.getD 1#8 = 0#8 →
      (∀ v < c.max_vars, v ≠ fv.toNat → mrk'[v]? = s.core.mrk[v]?) →
      lvl'[fv.toNat]?.getD 1#32 = 0#32 →
      (∀ v < c.max_vars, v ≠ fv.toNat → lvl'[v]? = s.core.lvl[v]?) →
      rsns'[fv.toNat]?.getD 0#32 = 0xFFFFFFFF#32 →
      (∀ v < c.max_vars, v ≠ fv.toNat → rsns'[v]? = s.core.rsns[v]?) →
      (∀ k < 4, wvec'[4 * fv.toNat + k]?.getD 1#32 = 0#32) →
      (∀ i < 4 * c.max_vars, i / 4 ≠ fv.toNat → wvec'[i]? = s.core.wvec[i]?) →
      (FullMem c s1 ⋆ R) m' → Q () m') : Q () m' := by
  have hs'_eq : s' = { s with core := s'.core, scratch := s'.scratch } := by cases s'; rfl
  let vals' := (s.core.vals.set (2 * fv.toNat) 0#8).set (2 * fv.toNat + 1) 0#8
  let mrk' := s.core.mrk.set fv.toNat 0#8
  let flags' := s.core.flags.set fv.toNat 1145#32
  let lvl' := s.core.lvl.set fv.toNat 0#32
  let rsns' := s.core.rsns.set fv.toNat 0xFFFFFFFF#32
  let wvec' := (((s.core.wvec.set (4 * fv.toNat) 0#32).set (4 * fv.toNat + 1) 0#32).set
    (4 * fv.toNat + 2) 0#32).set (4 * fv.toNat + 3) 0#32
  let unass' := s.core.unassigned + 1#64
  refine hQ vals' mrk' flags' lvl' rsns' wvec' unass' s'.scratch m'
    (by rw [← hcore, ← hs'_eq]; exact hlen')
    hext_pres hsb hws htm htr hss ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (by rw [← hcore, ← hs'_eq]; exact hm')
  · dsimp only [vals']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by rw [hclen.vals_len]; omega)]
    rfl
  · dsimp only [vals']
    rw [List.getElem?_set_self (by simp [hclen.vals_len]; omega)]; rfl
  · intro l _ _
    dsimp only [vals']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  · dsimp only [mrk']; rw [List.getElem?_set_self (by rw [hclen.mrk_len]; omega)]; rfl
  · intro v _ hv; exact List.getElem?_set_ne (Ne.symm hv)
  · dsimp only [lvl']; rw [List.getElem?_set_self (by rw [hclen.lvl_len]; omega)]; rfl
  · intro v _ hv; exact List.getElem?_set_ne (Ne.symm hv)
  · dsimp only [rsns']; rw [List.getElem?_set_self (by rw [hclen.rsns_len]; omega)]; rfl
  · intro v _ hv; exact List.getElem?_set_ne (Ne.symm hv)
  · intro k hk; dsimp only [wvec']
    rcases k with _ | _ | _ | _ | k
    · rw [show 4 * fv.toNat + 0 = 4 * fv.toNat from rfl, List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_self (by simp [hclen.wvec_len]; omega)]; rfl
    · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_self (by simp [hclen.wvec_len]; omega)]; rfl
    · rw [List.getElem?_set_ne (by omega),
        List.getElem?_set_self (by simp [hclen.wvec_len]; omega)]; rfl
    · rw [List.getElem?_set_self (by simp [hclen.wvec_len]; omega)]; rfl
    · omega
  · intro i _ hi; dsimp only [wvec']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]

theorem full_init_fresh_var_heap_wp (Γ : Env) :
    ∀ args m Q X, fullInitFreshVarHeapSpec args m Q X →
      Func.wp Γ full_init_fresh_var_body args m Q X := by
  rintro ⟨h, fv, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hslen, hfv_lt, hm, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hclen := hslen.core_ok; have hsc := hslen.scratch_ok; have hcv_le := hclen.cur_vars_le
  have hwv_len := hclen.wvec_len; have hvals_len := hclen.vals_len; have hmrk_len := hclen.mrk_len
  have hlvl_len := hclen.lvl_len; have hrsns_len := hclen.rsns_len; have hfl_len := hclen.flags_len
  have hpos_len := hsc.pos_len; have hph_len := hsc.phases_len; have hqp_len := hsc.q_prev_len
  have hqn_len := hsc.q_next_len; have hqs_len := hsc.q_stamp_len; have hsc_len := hsc.score_len
  have hfv64 : (BitVec.setWidth 64 fv).toNat = fv.toNat := by c0_bound
  have hwb0 : (BitVec.setWidth 64 fv <<< (2 : Nat)).toNat = 4 * fv.toNat := by c0_bound
  have hwb1 : ((BitVec.setWidth 64 fv <<< (2 : Nat)) + 1).toNat = 4 * fv.toNat + 1 := by
    change ((BitVec.setWidth 64 fv <<< (2 : Nat)) + 1#64).toNat = _; c0_bound
  have hwb2 : ((BitVec.setWidth 64 fv <<< (2 : Nat)) + 2).toNat = 4 * fv.toNat + 2 := by
    change ((BitVec.setWidth 64 fv <<< (2 : Nat)) + 2#64).toNat = _; c0_bound
  have hwb3 : ((BitVec.setWidth 64 fv <<< (2 : Nat)) + 3).toNat = 4 * fv.toNat + 3 := by
    change ((BitVec.setWidth 64 fv <<< (2 : Nat)) + 3#64).toNat = _; c0_bound
  have hv2 : (BitVec.setWidth 64 fv <<< (1 : Nat)).toNat = 2 * fv.toNat := by c0_bound
  have hv2p1 : ((BitVec.setWidth 64 fv <<< (1 : Nat)) ||| 1).toNat = 2 * fv.toNat + 1 := by
    change ((BitVec.setWidth 64 fv <<< (1 : Nat)) ||| 1#64).toNat = _
    rw [FullBvaFwdTactics.bv64_or1_of_even (by rw [hv2]; omega), hv2]
  have hv2p1_lt : ((BitVec.setWidth 64 fv <<< (1 : Nat)) ||| 1).toNat < s.core.vals.length := by
    rw [hv2p1, hvals_len]; omega
  have hfl_or : (((((1 : BitVec 32) ||| 8) ||| 16) ||| 1024) ||| 32) ||| 64 = 1145#32 := by decide
  unfold Func.wp full_init_fresh_var_body; dsimp only
  open scoped FullBvaFwdTactics in bf_fast_nogrp
  refine wp_join_state0 (α := FullState)
    (fun sm mm =>
      (FullMem c sm ⋆ R) mm ∧ sm.LengthsOk c ∧
      sm.core =
        { s.core with
          wvec := (((s.core.wvec.set (4 * fv.toNat) 0#32).set (4 * fv.toNat + 1) 0#32).set
            (4 * fv.toNat + 2) 0#32).set (4 * fv.toNat + 3) 0#32
          vals := (s.core.vals.set (2 * fv.toNat) 0#8).set (2 * fv.toNat + 1) 0#8
          mrk := s.core.mrk.set fv.toNat 0#8, lvl := s.core.lvl.set fv.toNat 0#32
          rsns := s.core.rsns.set fv.toNat 0xFFFFFFFF#32
          flags := s.core.flags.set fv.toNat 1145#32 } ∧
      FullExtScratchPres s sm ∧ sm.scratch.scratch_buf = s.scratch.scratch_buf ∧
      sm.scratch.wsort = s.scratch.wsort ∧ sm.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
      sm.scratch.tarjan_reach = s.scratch.tarjan_reach ∧
      sm.scratch.sim_sig = s.scratch.sim_sig)
    (fun _ sm mm ⟨hmm, hlenm, hcorem, hextm, hsbm, hwsm, htmm, htrm, hssm⟩ => ?_)
    (fun Jm hJm => ?_)
  · clear hm
    have hqsm_len := hlenm.scratch_ok.q_stamp_len
    open scoped FullBvaFwdTactics in bf_fast
    refine initFreshVar_post hfv_lt hclen ?_ hcv_le ?_ ?_ ?_ ?_ ?_ ?_ ?_ hm hQ
    · exact ⟨{ hlenm.core_ok with }, { hlenm.scratch_ok with q_stamp_len := by simp [hqsm_len] }⟩
    · dsimp only; rw [hcorem]; rfl
    · exact ⟨hextm.1, hextm.2⟩
    · exact hsbm
    · exact hwsm
    · exact htmm
    · exact htrm
    · exact hssm
  · open scoped FullBvaFwdTactics in bf_fast
    all_goals
      refine hJm _ _ ⟨hm, ?_, ?_, ⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩
      · exact ⟨
          { hclen with
            wvec_len := by simp [hwv_len], vals_len := by simp [hvals_len],
            mrk_len := by simp [hmrk_len], lvl_len := by simp [hlvl_len],
            rsns_len := by simp [hrsns_len], flags_len := by simp [hfl_len] },
          { hsc with
            phases_len := by simp [hph_len], pos_len := by simp [hpos_len],
            score_len := by simp [hsc_len], q_prev_len := by simp [hqp_len],
            q_next_len := by simp [hqn_len] }⟩
      · dsimp only; rw [hfv64, hwb0, hwb1, hwb2, hwb3, hv2, hv2p1, hfl_or]; rfl

/-- Canonical `Full.fullInitFreshVarSpec` corollary (zero callee hypotheses required). -/
theorem full_init_fresh_var_wp (Γ : Env) :
    ∀ args m Q X, Full.fullInitFreshVarSpec args m Q X →
      Func.wp Γ full_init_fresh_var_body args m Q X := by
  rintro ⟨h, fv, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hslen, hfv_lt, hm, hQ⟩
  exact full_init_fresh_var_heap_wp Γ _ m Q X ⟨c, s, R, rfl, hslen, hfv_lt, hm,
    fun vals' mrk' flags' lvl' rsns' wvec' unass' sc' m' hlen' hext' hsb _ _ _ _
      hv0 hv1 hv_oth hm0 hm_oth hl0 hl_oth hr0 hr_oth hw0 hw_oth hm' =>
      hQ vals' mrk' flags' lvl' rsns' wvec' unass' sc' m' hlen' hext' hsb
        hv0 hv1 hv_oth hm0 hm_oth hl0 hl_oth hr0 hr_oth hw0 hw_oth hm'⟩

/-! ## 5. 3-Hop Structural Overlap Scorer (`full_bva_hop1`, `full_bva_hop2`, `full_bva_hop3`) -/

private theorem hop_wvec_bounds {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hinv : FullDenseInvNoLm c F0 F_cur s) {sl : Nat}
    (hsl : sl < 2 * s.core.cur_vars) :
    fullWatchOffCore s.core sl + fullWatchSizeCore s.core sl ≤ s.core.wlen ∧
    DenseWatchSliceOk F_cur s.core sl (fullWatchOffCore s.core sl)
      (fullWatchSizeCore s.core sl) := by
  have hdw : DenseWatchesInv F_cur s.core := by
    have h := hinv.2.1.watches; unfold ModeWatchesInv at h
    rwa [ite_eq_right hinv.2.2.2.2.2] at h
  exact ⟨hdw.layout.bounds sl hsl, hdw.slices sl hsl⟩

theorem full_bva_hop1_wp (Γ : Env) :
    ∀ args m Q X, fullBvaHop1Spec args m Q X → Func.wp Γ full_bva_hop1_body args m Q X := by
  rintro ⟨h, src_lit, dst_idx, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hinv, hsrc_lt, htc_le, hmclr_ok, hm, hQ⟩
  have hmx := c.hmaxv; have hwcap := c.hwcap; have har_b := c.harena
  unfold dimacsBound at hmx hwcap har_b
  have hcl := hinv.1.core_ok; have hsc := hinv.1.scratch_ok
  have hcv_le := hcl.cur_vars_le; have hrepr_len := hcl.repr_len
  have hwv_len := hcl.wvec_len; have hws_len := hcl.wstk_len_arr; have har_len := hcl.arena_len_arr
  have hwlen_le := hcl.wlen_le; have hal_le := hcl.arena_len_le
  have hmclr_len := hcl.min_clr_len_arr
  have hsidx_lt : (src_lit >>> 1).toNat < s.core.cur_vars := by
    rw [bv32_lshr1_nat]; omega
  c0_hsteps_nogrp
  · exact hQ _ s.core.repr s.core.min_clr s.core.tmp_cnt s.scratch.ant_sz m
      hinv htc_le hmclr_ok (Nat.le_refl _) hm
  · refine wp_join_state1 (t := i64) (α := BitVec 64) (fun r => r) (fun _ ml => m = ml)
      (fun _ res0 ml hml => ?_) (fun J0 hJ0 => ?_)
    · rcases hml with rfl
      c0_hsteps_nogrp
      refine wp_loop_inv
        (fun (res, sgn, ()) ml => ∃ ant : BitVec 64,
          sgn.toNat ≤ 2 ∧ ant.toNat ≤ s.scratch.ant_sz.toNat ∧
          (FullMem c { s with scratch := { s.scratch with ant_sz := ant } } ⋆ R) ml)
        (fun (_, sgn, _) _ => 2 - sgn.toNat)
        (fun Js hJs => by
          c0_hsteps; exact hJs (res0, 0#32, ()) m ⟨s.scratch.ant_sz, by decide, Nat.le_refl _, hm⟩)
        (fun Js (res, sgn, ()) ml ⟨ant, hsgn_le, hant_le, hml⟩ ihs => ?_)
      c0_hsteps_nogrp
      refine wp_join_state0 (α := BitVec 64)
        (fun antF mf => antF.toNat ≤ s.scratch.ant_sz.toNat ∧
          (FullMem c { s with scratch := { s.scratch with ant_sz := antF } } ⋆ R) mf)
        (fun _ antF mf ⟨hantF, hmf⟩ => ?_)
        (fun Jend hJend => ?_)
      · c0_hsteps_nogrp
        refine wp_join_state1 (t := i64) (α := BitVec 64) (fun r => r) (fun _ ml => mf = ml)
          (fun _ resC ml hml => ?_) (fun Jc hJc => ?_)
        · rcases hml with rfl
          c0_hsteps
          · have htc1 : s.core.tmp_cnt + 1 ≤ s.core.cur_vars := by c0_bound
            have hinv' : FullDenseInvNoLm c F0 F_cur
                { core := { s.core with
                    repr := repr64Set s.core.repr (src_lit >>> 1).toNat (resC + 1)
                    min_clr := s.core.min_clr.set s.core.tmp_cnt (src_lit >>> 1)
                    tmp_cnt := s.core.tmp_cnt + 1 }
                  scratch := { s.scratch with ant_sz := antF } } :=
              fullDenseInvNoLm_with_core_aux hinv (by rw [repr64Set_length, hrepr_len])
                (by simp [hmclr_len]) hcl.tmp_len_arr hcl.flags_len hcl.tmp_len_le
                { hsc with } rfl rfl
            have hm' : (FullMem c
                { core := { s.core with
                    repr := repr64Set s.core.repr (src_lit >>> 1).toNat (resC + 1)
                    min_clr := s.core.min_clr.set s.core.tmp_cnt (src_lit >>> 1)
                    tmp_cnt := s.core.tmp_cnt + 1 }
                  scratch := { s.scratch with ant_sz := antF } } ⋆ R) m := by
              have h1 : (BitVec.ofNat 64 s.core.tmp_cnt + 1).toNat = s.core.tmp_cnt + 1 := by
                change (BitVec.ofNat 64 s.core.tmp_cnt + 1#64).toNat = _; c0_bound
              have h2 : (BitVec.ofNat 64 s.core.tmp_cnt).toNat = s.core.tmp_cnt := by c0_bound
              have h3 : (BitVec.setWidth 64 (src_lit >>> 1)).toNat = (src_lit >>> 1).toNat := by
                c0_bound
              rw [h1, h2, h3] at hm; exact hm
            exact hQ _ _ _ (s.core.tmp_cnt + 1) antF m hinv' htc1 (fun i hi => by
              by_cases hie : i = s.core.tmp_cnt
              · subst hie; rw [List.getElem?_set_self (by omega), Option.getD_some]; omega
              · rw [List.getElem?_set_ne (Ne.symm hie)]; exact hmclr_ok i (by omega)) hantF hm'
          · have hinv' : FullDenseInvNoLm c F0 F_cur
                { core := { s.core with
                    repr := repr64Set s.core.repr (src_lit >>> 1).toNat (resC + 1) }
                  scratch := { s.scratch with ant_sz := antF } } :=
              fullDenseInvNoLm_with_core_aux hinv (by rw [repr64Set_length, hrepr_len])
                hmclr_len hcl.tmp_len_arr hcl.flags_len hcl.tmp_len_le { hsc with } rfl rfl
            have hm' : (FullMem c
                { core := { s.core with
                    repr := repr64Set s.core.repr (src_lit >>> 1).toNat (resC + 1) }
                  scratch := { s.scratch with ant_sz := antF } } ⋆ R) m := by
              have h3 : (BitVec.setWidth 64 (src_lit >>> 1)).toNat = (src_lit >>> 1).toNat := by
                c0_bound
              rw [h3] at hm; exact hm
            exact hQ _ _ _ s.core.tmp_cnt antF m hinv' htc_le hmclr_ok hantF hm'
        · c0_hsteps
          · exact hJc 0x3FFFFFFFFFFFFFFF#64 mf rfl
          · exact hJc res mf rfl
      · c0_hsteps
        · have hsgn_lt : sgn.toNat < 2 := by c0_bound
          have hsl_nat : (((src_lit >>> (1 : Nat)) <<< (1 : Nat)) ||| sgn).toNat =
              2 * (src_lit >>> (1 : Nat)).toNat + sgn.toNat := by
            have hs01 : sgn.toNat = 0 ∨ sgn.toNat = 1 := by omega
            rcases hs01 with h0 | h1
            · have hs0 : sgn = 0#32 := BitVec.eq_of_toNat_eq h0; subst hs0
              rw [BitVec.or_zero]; c0_bound
            · have hs1 : sgn = 1#32 := BitVec.eq_of_toNat_eq h1; subst hs1
              rw [FullBvaFwdTactics.bv32_or1_of_even (by c0_bound)]; c0_bound
          have hsl_lt : (((src_lit >>> (1 : Nat)) <<< (1 : Nat)) ||| sgn).toNat <
              2 * s.core.cur_vars := by omega
          obtain ⟨hbd_sl, hslice_sl⟩ := hop_wvec_bounds hinv hsl_lt
          let sl : BitVec 32 := ((src_lit >>> (1 : Nat)) <<< (1 : Nat)) ||| sgn
          have hsl_lt_sl : sl.toNat < 2 * s.core.cur_vars := hsl_lt
          have hwv_sl0 : (BitVec.setWidth 64 sl <<< (1 : Nat)).toNat < s.core.wvec.length := by
            c0_bound
          have hwv_sl1 : ((BitVec.setWidth 64 sl <<< (1 : Nat)) + 1).toNat <
              s.core.wvec.length := by
            change ((BitVec.setWidth 64 sl <<< (1 : Nat)) + 1#64).toNat < _; c0_bound
          have hoff_eq : (s.core.wvec[2 * sl.toNat]'(by omega)).toNat =
              fullWatchOffCore s.core sl.toNat := by
            unfold fullWatchOffCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          have hsz_eq : (s.core.wvec[2 * sl.toNat + 1]'(by omega)).toNat =
              fullWatchSizeCore s.core sl.toNat := by
            unfold fullWatchSizeCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          let off0 := fullWatchOffCore s.core sl.toNat
          let sz0 := fullWatchSizeCore s.core sl.toNat
          have hoff_sz_le : off0 + sz0 ≤ s.core.wlen := hbd_sl
          have h2sl0 : (BitVec.setWidth 64 sl <<< (1 : Nat)).toNat = 2 * sl.toNat := by c0_bound
          have h2sl1 : ((BitVec.setWidth 64 sl <<< (1 : Nat)) + 1).toNat = 2 * sl.toNat + 1 := by
            change ((BitVec.setWidth 64 sl <<< (1 : Nat)) + 1#64).toNat = _; c0_bound
          have hoff_c0 : (BitVec.setWidth 64
              (s.core.wvec[(BitVec.setWidth 64 sl <<< (1 : Nat)).toNat]'hwv_sl0)).toNat = off0 := by
            rw [bv64_setWidth_32]; simp only [h2sl0]; exact hoff_eq
          have hmod0 : 2 * sl.toNat % 2 ^ 64 = 2 * sl.toNat := Nat.mod_eq_of_lt (by omega)
          have hmod1 : (2 * sl.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = 2 * sl.toNat + 1 :=
            by c0_bound
          have hend_mod : ((s.core.wvec[2 * sl.toNat % 2 ^ 64]'(by rw [hmod0]; omega)).toNat +
              (s.core.wvec[(2 * sl.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                rw [hmod1]; omega)).toNat) % 2 ^ 64 = off0 + sz0 := by
            simp only [hmod0, hmod1, hoff_eq, hsz_eq]; exact Nat.mod_eq_of_lt (by omega)
          c0_hsteps_nogrp
          refine wp_loop_inv
            (fun (res1, p, ()) mlp => ∃ antp : BitVec 64,
              off0 ≤ p.toNat ∧ p.toNat ≤ off0 + sz0 ∧ antp.toNat ≤ ant.toNat ∧
              DenseWatchSliceOk F_cur s.core sl.toNat p.toNat (off0 + sz0 - p.toNat) ∧
              (FullMem c { s with scratch := { s.scratch with ant_sz := antp } } ⋆ R) mlp)
            (fun (_, p, _) _ => off0 + sz0 - p.toNat)
            (fun Jp hJp => by
              c0_hfast
              exact hJp (res, _, ()) ml ⟨ant, by rw [hoff_c0]; exact Nat.le_refl _,
                by rw [hoff_c0]; omega, Nat.le_refl _,
                by rw [hoff_c0, Nat.add_sub_cancel_left]; exact hslice_sl, hml⟩)
            (fun Jp (res1, p, ()) mlp ⟨antp, hp_ge, hp_le, hantp_le, hrem, hmlp⟩ ihp => ?_)
          c0_hfast
          · have hp_lt : p.toNat < off0 + sz0 := by rw [← hend_mod]; assumption
            have hp_ws : p.toNat < s.core.wstk.length := by omega
            have hant1 : (antp - 1#64).toNat ≤ ant.toNat := by simp only [bv_c0]; omega
            have hp1_n : (p + 1).toNat = p.toNat + 1 := by
              change (p + 1#64).toNat = _; simp only [bv_c0]; omega
            have hp1_mod : (p.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = p.toNat + 1 := by
              rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]; omega
            c0_hfast
            · have ⟨_, _, hrem_next⟩ := FullBvaFwdHelpers.bva_slice_bin_info hrem (by omega) hp_ws
                (by assumption)
              exact ihp (_, p + 1, ()) m (by dsimp only; rw [hp1_n]; omega)
                ⟨antp - 1#64, by rw [hp1_n]; omega, by rw [hp1_n]; omega, hant1,
                 by rw [hp1_n, show off0 + sz0 - (p.toNat + 1) = off0 + sz0 - p.toNat - 1 by omega]
                    exact hrem_next, hm⟩
            · have ⟨_, _, hrem_next⟩ := FullBvaFwdHelpers.bva_slice_bin_info hrem (by omega) hp_ws
                (by assumption)
              exact ihp (_, p + 1, ()) m (by dsimp only; rw [hp1_n]; omega)
                ⟨antp - 1#64, by rw [hp1_n]; omega, by rw [hp1_n]; omega, hant1,
                 by rw [hp1_n, show off0 + sz0 - (p.toNat + 1) = off0 + sz0 - p.toNat - 1 by omega]
                    exact hrem_next, hm⟩
            · have hm_flat : (FullMem c
                  { s with scratch := { s.scratch with ant_sz := antp - 1#64 } } ⋆ R) m := hm
              clear hm
              have ⟨h2le, hrem_next⟩ := FullBvaFwdHelpers.bva_slice_occ_info hrem (by omega) hp_ws
                (by assumption)
              have hp1_ws : p.toNat + 1 < s.core.wstk.length := by omega
              have ⟨_, hcr_ref, _⟩ := FullBvaFwdHelpers.fwd_slice_occ_info hrem (by omega) hp_ws
                hp1_ws (by assumption)
              have hcr_wf := hinv.2.1.arena.refs_wf _ hcr_ref
              have hp2_n : (p + 1 + 1).toNat = p.toNat + 2 := by
                change (p + 1#64 + 1#64).toNat = _; simp only [bv_c0]; omega
              let cr := s.core.wstk[p.toNat + 1]'hp1_ws
              have hcr_al : cr.toNat + 3 + fullArenaClauseSizeCore s.core cr.toNat ≤
                  s.core.arena_len := by
                have h1 := hcr_wf.2.2.1; have h2 := hcr_wf.2.2.2.1; dsimp only [cr]; omega
              have hcr_eq : s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws) = cr := by
                dsimp only [cr]; simp only [hp1_n]
              have hcr0_eq : (BitVec.setWidth 64
                  (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws))).toNat = cr.toNat := by
                rw [bv64_setWidth_32, hcr_eq]
              have hcr_b0 : (BitVec.setWidth 64
                  (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws))).toNat <
                  s.core.arena.length := by rw [hcr0_eq]; omega
              have hcr2_eq : (BitVec.setWidth 64
                  (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws)) + 2).toNat =
                  cr.toNat + 2 := by
                change (BitVec.setWidth 64 _ + 2#64).toNat = _
                rw [hcr_eq]; simp only [bv_c0]; omega
              have hcr_b2 : (BitVec.setWidth 64
                  (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws)) + 2).toNat <
                  s.core.arena.length := by rw [hcr2_eq]; omega
              have hsz_cr : (s.core.arena[cr.toNat + 2]'(by omega)).toNat =
                  fullArenaClauseSizeCore s.core cr.toNat := by
                unfold fullArenaClauseSizeCore
                rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
              have hcr_sz_le : cr.toNat + 3 + (s.core.arena[cr.toNat + 2]'(by omega)).toNat ≤
                  s.core.arena.length := by rw [hsz_cr]; omega
              c0_hfast
              · clear hQ ihs hJend
                refine wp_loop_inv
                  (fun (resk, k, ()) mk =>
                    k.toNat ≤ (s.core.arena[cr.toNat + 2]'(by omega)).toNat ∧ mk = m)
                  (fun (_, k, _) _ => (s.core.arena[cr.toNat + 2]'(by omega)).toNat - k.toNat)
                  (fun Jk hJk => by c0_hfast; exact hJk (res1, 0#32, ()) m ⟨Nat.zero_le _, rfl⟩)
                  (fun Jk (resk, k, ()) mk ⟨hk_le, hmk⟩ ihk => ?_)
                subst hmk; c0_hsplit
                · have hk_lt : k.toNat < (s.core.arena[cr.toNat + 2]'(by omega)).toNat := by
                    have h1 : k.toNat < (s.core.arena[(BitVec.setWidth 64
                        (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws)) +
                        2).toNat]'hcr_b2).toNat := by assumption
                    simpa only [hcr2_eq] using h1
                  have hcrk_b : (BitVec.setWidth 64
                      (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws)) + 3 +
                      BitVec.setWidth 64 k).toNat < s.core.arena.length := by
                    change (BitVec.setWidth 64 _ + 3#64 + BitVec.setWidth 64 k).toNat < _
                    rw [hcr_eq]; simp only [bv_c0]; omega
                  have hk1 : (k + 1#32).toNat = k.toNat + 1 := by simp only [bv_c0]; omega
                  c0_hfast
                  all_goals
                    exact ihk (_, k + 1#32, ()) mk (by dsimp only; rw [hk1]; omega)
                      ⟨by rw [hk1]; omega, rfl⟩
                · c0_hfast
                  exact ihp (resk, p + 1 + 1, ()) mk (by dsimp only; rw [hp2_n]; omega)
                    ⟨antp - 1#64, by rw [hp2_n]; omega, by rw [hp2_n]; omega, hant1,
                     by rw [hp2_n, show off0 + sz0 - (p.toNat + 2) = off0 + sz0 - p.toNat - 2
                          by omega]; exact hrem_next, hm_flat⟩
              · exact ihp (res1, p + 1 + 1, ()) m (by dsimp only; rw [hp2_n]; omega)
                  ⟨antp - 1#64, by rw [hp2_n]; omega, by rw [hp2_n]; omega, hant1,
                   by rw [hp2_n, show off0 + sz0 - (p.toNat + 2) = off0 + sz0 - p.toNat - 2
                        by omega]; exact hrem_next, hm_flat⟩
            · exfalso
              have ⟨h2le, _⟩ := FullBvaFwdHelpers.bva_slice_occ_info hrem (by omega) hp_ws
                (by assumption)
              have hge : ¬ (p.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 <
                  ((s.core.wvec[2 * sl.toNat % 2 ^ 64]'(by rw [hmod0]; omega)).toNat +
                   (s.core.wvec[(2 * sl.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                     rw [hmod1]; omega)).toNat) % 2 ^ 64 := by assumption
              rw [hend_mod, hp1_mod] at hge; omega
          all_goals
            exact ihs (res1, sgn + 1#32, ()) mlp (by simp only [bv_c0]; omega)
              ⟨antp, by simp only [bv_c0]; omega, Nat.le_trans hantp_le hant_le, hmlp⟩
        · exact hJend ant ml ⟨hant_le, hml⟩
        · exact hJend ant ml ⟨hant_le, hml⟩
    · c0_hsteps
      · exact hJ0 1#64 m rfl
      · exact hJ0 0#64 m rfl

theorem full_bva_hop2_wp (Γ : Env)
    (hHop1 : ∀ args m Q X, fullBvaHop1Spec args m Q X →
      Γ "full_bva_hop1" [i64, i32, i32] [i64] args m Q X) :
    ∀ args m Q X, fullBvaHop2Spec args m Q X → Func.wp Γ full_bva_hop2_body args m Q X := by
  rintro ⟨h, src_lit, dst_idx, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hinv, hsrc_lt, htc_le, htl_le, hmclr_ok, hshrk_ok, hm, hQ⟩
  have hmx := c.hmaxv; have hwcap := c.hwcap; have har_b := c.harena
  unfold dimacsBound at hmx hwcap har_b
  have hcl := hinv.1.core_ok; have hsc := hinv.1.scratch_ok
  have hcv_le := hcl.cur_vars_le; have hsig_len := hsc.sim_sig_len
  have hshrk_len := hsc.shrink_stk_len
  have hwv_len := hcl.wvec_len; have hws_len := hcl.wstk_len_arr; have har_len := hcl.arena_len_arr
  have hwlen_le := hcl.wlen_le; have hal_le := hcl.arena_len_le
  have hsidx_lt : (src_lit >>> 1).toNat < s.core.cur_vars := by rw [bv32_lshr1_nat]; omega
  c0_hsteps_nogrp
  · exact hQ _ s.core.repr s.core.min_clr s.core.tmp_cnt s.core.tmp_len s.scratch.ant_sz
      s.scratch.sim_sig s.scratch.shrink_stk m hinv htc_le htl_le hmclr_ok hshrk_ok
      (Nat.le_refl _) hm
  · refine wp_join_state1 (t := i64) (α := BitVec 64) (fun r => r) (fun _ ml => m = ml)
      (fun _ res0 ml hml => ?_) (fun J0 hJ0 => ?_)
    · rcases hml with rfl
      c0_hsteps_nogrp
      let mkSt (rp mc : List (BitVec 32)) (tc : Nat) (ant : BitVec 64) : FullState :=
        { core := { s.core with repr := rp, min_clr := mc, tmp_cnt := tc }
          scratch := { s.scratch with ant_sz := ant } }
      refine wp_loop_inv
        (fun (res, sgn, ()) ml => ∃ rp mc tc ant,
          sgn.toNat ≤ 2 ∧ tc ≤ s.core.cur_vars ∧ ant.toNat ≤ s.scratch.ant_sz.toNat ∧
          FullDenseInvNoLm c F0 F_cur (mkSt rp mc tc ant) ∧
          (∀ i < tc, (mc[i]?.getD 0#32).toNat < c.max_vars) ∧
          (FullMem c (mkSt rp mc tc ant) ⋆ R) ml)
        (fun (_, sgn, _) _ => 2 - sgn.toNat)
        (fun Js hJs => by
          c0_hsteps; exact hJs (res0, 0#32, ()) m
            ⟨s.core.repr, s.core.min_clr, s.core.tmp_cnt, s.scratch.ant_sz, by decide, htc_le,
             Nat.le_refl _, hinv, hmclr_ok, hm⟩)
        (fun Js (res, sgn, ()) ml
            ⟨rp, mc, tc, ant, hsgn_le, htc, hant, hinv_s, hmc_ok, hml⟩ ihs => ?_)
      c0_hsteps_nogrp
      refine wp_join_state0
        (α := List (BitVec 32) × List (BitVec 32) × Nat × BitVec 64)
        (fun ⟨rpF, mcF, tcF, antF⟩ mf =>
          tcF ≤ s.core.cur_vars ∧ antF.toNat ≤ s.scratch.ant_sz.toNat ∧
          FullDenseInvNoLm c F0 F_cur (mkSt rpF mcF tcF antF) ∧
          (∀ i < tcF, (mcF[i]?.getD 0#32).toNat < c.max_vars) ∧
          (FullMem c (mkSt rpF mcF tcF antF) ⋆ R) mf)
        (fun _ ⟨rpF, mcF, tcF, antF⟩ mf ⟨htcF, hantF, hinvF, hmcF, hmf⟩ => ?_)
        (fun Jend hJend => ?_)
      · dsimp only [mkSt] at hmf hinvF
        c0_hsteps_nogrp
        refine wp_join_state1 (t := i64) (α := BitVec 64) (fun r => r) (fun _ ml => mf = ml)
          (fun _ resC ml hml => ?_) (fun Jc hJc => ?_)
        · rcases hml with rfl
          c0_hsteps
          · have htl1 : s.core.tmp_len + 1 ≤ s.core.cur_vars := by c0_bound
            let sc1 : FullScratch :=
              { s.scratch with
                ant_sz := antF
                sim_sig := s.scratch.sim_sig.set (src_lit >>> 1).toNat (resC + 1)
                shrink_stk := s.scratch.shrink_stk.set s.core.tmp_len (src_lit >>> 1) }
            have hinv' := fullDenseInvNoLm_with_core_aux (tc' := tcF) (tl' := s.core.tmp_len + 1)
              (sc' := sc1) hinvF hinvF.1.core_ok.repr_len hinvF.1.core_ok.min_clr_len_arr
              hcl.tmp_len_arr hcl.flags_len (by omega)
              { hsc with sim_sig_len := by simp [sc1, hsig_len],
                         shrink_stk_len := by simp [sc1, hshrk_len] }
              rfl rfl
            have hm' : (FullMem c
                { core := { s.core with repr := rpF, min_clr := mcF, tmp_cnt := tcF,
                                        tmp_len := s.core.tmp_len + 1 }
                  scratch := sc1 } ⋆ R) m := by
              have h1 : (BitVec.ofNat 64 s.core.tmp_len + 1).toNat = s.core.tmp_len + 1 := by
                change (BitVec.ofNat 64 s.core.tmp_len + 1#64).toNat = _; c0_bound
              have h2 : (BitVec.ofNat 64 s.core.tmp_len).toNat = s.core.tmp_len := by c0_bound
              have h3 : (BitVec.setWidth 64 (src_lit >>> 1)).toNat = (src_lit >>> 1).toNat := by
                c0_bound
              dsimp only [sc1]; rw [h1, h2, h3] at hm; exact hm
            exact hQ _ rpF mcF tcF (s.core.tmp_len + 1) antF _ _ m
              (by dsimp only [sc1] at hinv'; exact hinv') htcF htl1 hmcF
              (fun i hi => by
                by_cases hie : i = s.core.tmp_len
                · subst hie; rw [List.getElem?_set_self (by omega), Option.getD_some]; omega
                · rw [List.getElem?_set_ne (Ne.symm hie)]; exact hshrk_ok i (by omega)) hantF hm'
          · let sc2 : FullScratch :=
              { s.scratch with
                ant_sz := antF
                sim_sig := s.scratch.sim_sig.set (src_lit >>> 1).toNat (resC + 1) }
            have hinv' := fullDenseInvNoLm_with_core_aux (tc' := tcF) (tl' := s.core.tmp_len)
              (sc' := sc2) hinvF hinvF.1.core_ok.repr_len hinvF.1.core_ok.min_clr_len_arr
              hcl.tmp_len_arr hcl.flags_len hcl.tmp_len_le
              { hsc with sim_sig_len := by simp [sc2, hsig_len] } rfl rfl
            have hm' : (FullMem c
                { core := { s.core with repr := rpF, min_clr := mcF, tmp_cnt := tcF }
                  scratch := sc2 } ⋆ R) m := by
              have h3 : (BitVec.setWidth 64 (src_lit >>> 1)).toNat = (src_lit >>> 1).toNat := by
                c0_bound
              dsimp only [sc2]; rw [h3] at hm; exact hm
            exact hQ _ rpF mcF tcF s.core.tmp_len antF _ s.scratch.shrink_stk m
              (by dsimp only [sc2] at hinv'; exact hinv') htcF htl_le hmcF hshrk_ok hantF hm'
        · c0_hsteps
          · exact hJc 0x3FFFFFFFFFFFFFFF#64 mf rfl
          · exact hJc res mf rfl
      · dsimp only [mkSt] at hml
        c0_hsteps
        · have hsgn_lt : sgn.toNat < 2 := by c0_bound
          have hsl_nat : (((src_lit >>> (1 : Nat)) <<< (1 : Nat)) ||| sgn).toNat =
              2 * (src_lit >>> (1 : Nat)).toNat + sgn.toNat := by
            have hs01 : sgn.toNat = 0 ∨ sgn.toNat = 1 := by omega
            rcases hs01 with h0 | h1
            · have hs0 : sgn = 0#32 := BitVec.eq_of_toNat_eq h0; subst hs0
              rw [BitVec.or_zero]; c0_bound
            · have hs1 : sgn = 1#32 := BitVec.eq_of_toNat_eq h1; subst hs1
              rw [FullBvaFwdTactics.bv32_or1_of_even (by c0_bound)]; c0_bound
          have hsl_lt : (((src_lit >>> (1 : Nat)) <<< (1 : Nat)) ||| sgn).toNat <
              2 * s.core.cur_vars := by omega
          obtain ⟨hbd_sl, hslice_sl⟩ := hop_wvec_bounds hinv hsl_lt
          let sl : BitVec 32 := ((src_lit >>> (1 : Nat)) <<< (1 : Nat)) ||| sgn
          have hsl_lt_sl : sl.toNat < 2 * s.core.cur_vars := hsl_lt
          have hwv_sl0 : (BitVec.setWidth 64 sl <<< (1 : Nat)).toNat < s.core.wvec.length := by
            c0_bound
          have hwv_sl1 : ((BitVec.setWidth 64 sl <<< (1 : Nat)) + 1).toNat <
              s.core.wvec.length := by
            change ((BitVec.setWidth 64 sl <<< (1 : Nat)) + 1#64).toNat < _; c0_bound
          have hoff_eq : (s.core.wvec[2 * sl.toNat]'(by omega)).toNat =
              fullWatchOffCore s.core sl.toNat := by
            unfold fullWatchOffCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          have hsz_eq : (s.core.wvec[2 * sl.toNat + 1]'(by omega)).toNat =
              fullWatchSizeCore s.core sl.toNat := by
            unfold fullWatchSizeCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          let off0 := fullWatchOffCore s.core sl.toNat
          let sz0 := fullWatchSizeCore s.core sl.toNat
          have hoff_sz_le : off0 + sz0 ≤ s.core.wlen := hbd_sl
          have h2sl0 : (BitVec.setWidth 64 sl <<< (1 : Nat)).toNat = 2 * sl.toNat := by c0_bound
          have h2sl1 : ((BitVec.setWidth 64 sl <<< (1 : Nat)) + 1).toNat = 2 * sl.toNat + 1 := by
            change ((BitVec.setWidth 64 sl <<< (1 : Nat)) + 1#64).toNat = _; c0_bound
          have hoff_c0 : (BitVec.setWidth 64
              (s.core.wvec[(BitVec.setWidth 64 sl <<< (1 : Nat)).toNat]'hwv_sl0)).toNat = off0 := by
            rw [bv64_setWidth_32]; simp only [h2sl0]; exact hoff_eq
          have hmod0 : 2 * sl.toNat % 2 ^ 64 = 2 * sl.toNat := Nat.mod_eq_of_lt (by omega)
          have hmod1 : (2 * sl.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = 2 * sl.toNat + 1 :=
            by c0_bound
          have hend_mod : ((s.core.wvec[2 * sl.toNat % 2 ^ 64]'(by rw [hmod0]; omega)).toNat +
              (s.core.wvec[(2 * sl.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                rw [hmod1]; omega)).toNat) % 2 ^ 64 = off0 + sz0 := by
            simp only [hmod0, hmod1, hoff_eq, hsz_eq]; exact Nat.mod_eq_of_lt (by omega)
          c0_hsteps_nogrp
          refine wp_loop_inv
            (fun (res1, p, ()) mlp => ∃ rpp mcp tcp antp,
              off0 ≤ p.toNat ∧ p.toNat ≤ off0 + sz0 ∧ tcp ≤ s.core.cur_vars ∧
              antp.toNat ≤ ant.toNat ∧ FullDenseInvNoLm c F0 F_cur (mkSt rpp mcp tcp antp) ∧
              (∀ i < tcp, (mcp[i]?.getD 0#32).toNat < c.max_vars) ∧
              DenseWatchSliceOk F_cur s.core sl.toNat p.toNat (off0 + sz0 - p.toNat) ∧
              (FullMem c (mkSt rpp mcp tcp antp) ⋆ R) mlp)
            (fun (_, p, _) _ => off0 + sz0 - p.toNat)
            (fun Jp hJp => by
              c0_hfast
              exact hJp (res, _, ()) ml ⟨rp, mc, tc, ant, by rw [hoff_c0]; exact Nat.le_refl _,
                by rw [hoff_c0]; omega, htc, Nat.le_refl _, hinv_s, hmc_ok,
                by rw [hoff_c0, Nat.add_sub_cancel_left]; exact hslice_sl, hml⟩)
            (fun Jp (res1, p, ()) mlp ⟨rpp, mcp, tcp, antp, hp_ge, hp_le, htcp, hantp, hinvp,
                hmcp_ok, hrem, hmlp⟩ ihp => ?_)
          dsimp only [mkSt] at hmlp
          c0_hfast
          · have hp_lt : p.toNat < off0 + sz0 := by rw [← hend_mod]; assumption
            have hp_ws : p.toNat < s.core.wstk.length := by omega
            have hant1 : (antp - 1#64).toNat ≤ ant.toNat := by simp only [bv_c0]; omega
            have hp1_n : (p + 1).toNat = p.toNat + 1 := by
              change (p + 1#64).toNat = _; simp only [bv_c0]; omega
            have hp1_mod : (p.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = p.toNat + 1 := by
              rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]; omega
            have hinvp1 : FullDenseInvNoLm c F0 F_cur (mkSt rpp mcp tcp (antp - 1#64)) :=
              fullDenseInvNoLm_with_core_aux (tc' := tcp) (tl' := s.core.tmp_len) hinvp
                hinvp.1.core_ok.repr_len hinvp.1.core_ok.min_clr_len_arr hcl.tmp_len_arr
                hcl.flags_len hcl.tmp_len_le { hsc with } rfl rfl
            c0_hfast
            · have ⟨hot_lt, _, hrem_next⟩ :=
                FullBvaFwdHelpers.bva_slice_bin_info hrem (by omega) hp_ws (by assumption)
              c0_call hHop1
              refine ⟨c, F0, F_cur, mkSt rpp mcp tcp (antp - 1#64), R, rfl, hinvp1, hot_lt, htcp,
                hmcp_ok, hm, fun r1 rp1 mc1 tc1 ant1 m1 hinv1 htc1 hmc1 hant1' hm1 => ?_⟩
              c0_hfast
              exact ihp (res1 + r1, p + 1, ()) m1 (by dsimp only; rw [hp1_n]; omega)
                ⟨rp1, mc1, tc1, ant1, by rw [hp1_n]; omega, by rw [hp1_n]; omega, htc1,
                 Nat.le_trans hant1' hant1, hinv1, hmc1,
                 by rw [hp1_n, show off0 + sz0 - (p.toNat + 1) = off0 + sz0 - p.toNat - 1 by omega]
                    exact hrem_next, hm1⟩
            · have hm_flat : (FullMem c
                  { core := { s.core with repr := rpp, min_clr := mcp, tmp_cnt := tcp },
                    scratch := { s.scratch with ant_sz := antp - 1#64 } } ⋆ R) m := hm
              clear hm
              have ⟨h2le, hrem_next⟩ := FullBvaFwdHelpers.bva_slice_occ_info hrem (by omega) hp_ws
                (by assumption)
              have hp1_ws : p.toNat + 1 < s.core.wstk.length := by omega
              have ⟨_, hcr_ref, _⟩ := FullBvaFwdHelpers.fwd_slice_occ_info hrem (by omega) hp_ws
                hp1_ws (by assumption)
              have hcr_wf := hinv.2.1.arena.refs_wf _ hcr_ref
              have hp2_n : (p + 1 + 1).toNat = p.toNat + 2 := by
                change (p + 1#64 + 1#64).toNat = _; simp only [bv_c0]; omega
              let cr := s.core.wstk[p.toNat + 1]'hp1_ws
              have hcr_al : cr.toNat + 3 + fullArenaClauseSizeCore s.core cr.toNat ≤
                  s.core.arena_len := by
                have h1 := hcr_wf.2.2.1; have h2 := hcr_wf.2.2.2.1; dsimp only [cr]; omega
              have hcr_eq : s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws) = cr := by
                dsimp only [cr]; simp only [hp1_n]
              have hcr0_eq : (BitVec.setWidth 64
                  (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws))).toNat = cr.toNat := by
                rw [bv64_setWidth_32, hcr_eq]
              have hcr_b0 : (BitVec.setWidth 64
                  (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws))).toNat <
                  s.core.arena.length := by rw [hcr0_eq]; omega
              have hcr2_eq : (BitVec.setWidth 64
                  (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws)) + 2).toNat =
                  cr.toNat + 2 := by
                change (BitVec.setWidth 64 _ + 2#64).toNat = _
                rw [hcr_eq]; simp only [bv_c0]; omega
              have hcr_b2 : (BitVec.setWidth 64
                  (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws)) + 2).toNat <
                  s.core.arena.length := by rw [hcr2_eq]; omega
              have hsz_cr : (s.core.arena[cr.toNat + 2]'(by omega)).toNat =
                  fullArenaClauseSizeCore s.core cr.toNat := by
                unfold fullArenaClauseSizeCore
                rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
              have hcr_sz_le : cr.toNat + 3 + (s.core.arena[cr.toNat + 2]'(by omega)).toNat ≤
                  s.core.arena.length := by rw [hsz_cr]; omega
              c0_hfast
              · have hng_cr : fullArenaClauseGarbCore s.core cr.toNat = false := by
                  unfold fullArenaClauseGarbCore fullArenaHdrCore
                  rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                  have h1 : s.core.arena[(BitVec.setWidth 64
                      (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws))).toNat]'hcr_b0 &&&
                      (524288#32 ||| 4194304#32) = 0#32 := by assumption
                  exact FullBvaFwdHelpers.garb_false_of_and_garb_red_eq_zero (by
                    simpa only [hcr0_eq] using h1)
                clear hQ ihs hJend
                refine wp_loop_inv
                  (fun (resk, k, ()) mk => ∃ rpk mck tck antk,
                    k.toNat ≤ (s.core.arena[cr.toNat + 2]'(by omega)).toNat ∧
                    tck ≤ s.core.cur_vars ∧ antk.toNat ≤ ant.toNat ∧
                    FullDenseInvNoLm c F0 F_cur (mkSt rpk mck tck antk) ∧
                    (∀ i < tck, (mck[i]?.getD 0#32).toNat < c.max_vars) ∧
                    (FullMem c (mkSt rpk mck tck antk) ⋆ R) mk)
                  (fun (_, k, _) _ => (s.core.arena[cr.toNat + 2]'(by omega)).toNat - k.toNat)
                  (fun Jk hJk => by
                    c0_hfast; exact hJk (res1, 0#32, ()) m
                      ⟨rpp, mcp, tcp, antp - 1#64, Nat.zero_le _, htcp, hant1, hinvp1, hmcp_ok,
                       hm_flat⟩)
                  (fun Jk (resk, k, ()) mk ⟨rpk, mck, tck, antk, hk_le, htck, hantk, hinvk,
                      hmck_ok, hmk⟩ ihk => ?_)
                dsimp only [mkSt] at hmk
                c0_hsplit
                · have hk_lt : k.toNat < (s.core.arena[cr.toNat + 2]'(by omega)).toNat := by
                    have h1 : k.toNat < (s.core.arena[(BitVec.setWidth 64
                        (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws)) +
                        2).toNat]'hcr_b2).toNat := by assumption
                    simpa only [hcr2_eq] using h1
                  have hk1 : (k + 1#32).toNat = k.toNat + 1 := by simp only [bv_c0]; omega
                  c0_hsplit
                  · have hcrk_b : (BitVec.setWidth 64
                        (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws)) + 3 +
                        BitVec.setWidth 64 k).toNat < s.core.arena.length := by
                      change (BitVec.setWidth 64 _ + 3#64 + BitVec.setWidth 64 k).toNat < _
                      rw [hcr_eq]; simp only [bv_c0]; omega
                    have hol_mem : (s.core.arena[cr.toNat + 3 + k.toNat]'(by omega)).toNat ∈
                        fullArenaClauseLitsCore s.core cr.toNat :=
                      List.mem_of_getElem? (FullBvaFwdHelpers.fullArenaClauseLitsCore_getElem
                        (by rw [← hsz_cr]; exact hk_lt) (by omega))
                    have hol_lt := hinv.2.1.arena.lits_lt cr.toNat hcr_ref hng_cr _ hol_mem
                    have hcrk_eq : (BitVec.setWidth 64 cr + 3 + BitVec.setWidth 64 k).toNat =
                        cr.toNat + 3 + k.toNat := by
                      change (BitVec.setWidth 64 cr + 3#64 + BitVec.setWidth 64 k).toNat = _
                      simp only [bv_c0]; omega
                    c0_hfast
                    · c0_call hHop1
                      refine ⟨c, F0, F_cur, mkSt rpk mck tck antk, R, rfl, hinvk, ?_, htck, hmck_ok,
                        hmk, fun r1 rp1 mc1 tc1 ant1 m1 hinv1 htc1 hmc1 hant1' hm1 => ?_⟩
                      · simpa only [hcr_eq, hcrk_eq] using hol_lt
                      · c0_hfast
                        exact ihk (resk + r1, k + 1#32, ()) m1 (by dsimp only; rw [hk1]; omega)
                          ⟨rp1, mc1, tc1, ant1, by rw [hk1]; omega, htc1,
                           Nat.le_trans hant1' hantk, hinv1, hmc1, hm1⟩
                    · exact ihk (resk, k + 1#32, ()) mk (by dsimp only; rw [hk1]; omega)
                        ⟨rpk, mck, tck, antk, by rw [hk1]; omega, htck, hantk, hinvk, hmck_ok, hmk⟩
                  · c0_hfast
                    exact ihp (resk, p + 1 + 1, ()) mk (by dsimp only; rw [hp2_n]; omega)
                      ⟨rpk, mck, tck, antk, by rw [hp2_n]; omega, by rw [hp2_n]; omega, htck, hantk,
                       hinvk, hmck_ok,
                       by rw [hp2_n, show off0 + sz0 - (p.toNat + 2) = off0 + sz0 - p.toNat - 2
                            by omega]; exact hrem_next, hmk⟩
                · c0_hfast
                  exact ihp (resk, p + 1 + 1, ()) mk (by dsimp only; rw [hp2_n]; omega)
                    ⟨rpk, mck, tck, antk, by rw [hp2_n]; omega, by rw [hp2_n]; omega, htck, hantk,
                     hinvk, hmck_ok,
                     by rw [hp2_n, show off0 + sz0 - (p.toNat + 2) = off0 + sz0 - p.toNat - 2
                          by omega]; exact hrem_next, hmk⟩
              · exact ihp (res1, p + 1 + 1, ()) m (by dsimp only; rw [hp2_n]; omega)
                  ⟨rpp, mcp, tcp, antp - 1#64, by rw [hp2_n]; omega, by rw [hp2_n]; omega, htcp,
                   hant1, hinvp1, hmcp_ok,
                   by rw [hp2_n, show off0 + sz0 - (p.toNat + 2) = off0 + sz0 - p.toNat - 2
                        by omega]; exact hrem_next, hm_flat⟩
            · exfalso
              have ⟨h2le, _⟩ := FullBvaFwdHelpers.bva_slice_occ_info hrem (by omega) hp_ws
                (by assumption)
              have hge : ¬ (p.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 <
                  ((s.core.wvec[2 * sl.toNat % 2 ^ 64]'(by rw [hmod0]; omega)).toNat +
                   (s.core.wvec[(2 * sl.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                     rw [hmod1]; omega)).toNat) % 2 ^ 64 := by assumption
              rw [hend_mod, hp1_mod] at hge; omega
          all_goals
            exact ihs (res1, sgn + 1#32, ()) mlp (by simp only [bv_c0]; omega)
              ⟨rpp, mcp, tcp, antp, by simp only [bv_c0]; omega, htcp, Nat.le_trans hantp hant,
               hinvp, hmcp_ok, hmlp⟩
        · exact hJend ⟨rp, mc, tc, ant⟩ ml ⟨htc, hant, hinv_s, hmc_ok, hml⟩
        · exact hJend ⟨rp, mc, tc, ant⟩ ml ⟨htc, hant, hinv_s, hmc_ok, hml⟩
    · c0_hsteps
      · exact hJ0 1#64 m rfl
      · exact hJ0 0#64 m rfl

theorem full_bva_hop3_wp (Γ : Env)
    (hHop2 : ∀ args m Q X, fullBvaHop2Spec args m Q X →
      Γ "full_bva_hop2" [i64, i32, i32] [i64] args m Q X) :
    ∀ args m Q X, fullBvaHop3Spec args m Q X → Func.wp Γ full_bva_hop3_body args m Q X := by
  rintro ⟨h, src_lit, dst_idx, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hinv, hsrc_lt, hm, hQ⟩
  have hmx := c.hmaxv; have hwcap := c.hwcap; have har_b := c.harena
  unfold dimacsBound at hmx hwcap har_b
  have hcl := hinv.1.core_ok; have hsc := hinv.1.scratch_ok
  have hcv_le := hcl.cur_vars_le; have hwv_len := hcl.wvec_len
  have hws_len := hcl.wstk_len_arr; have har_len := hcl.arena_len_arr
  have hwlen_le := hcl.wlen_le; have hal_le := hcl.arena_len_le
  have hsidx_lt : (src_lit >>> 1).toNat < s.core.cur_vars := by rw [bv32_lshr1_nat]; omega
  c0_hsteps_nogrp
  refine wp_join_state1 (t := i64) (α := BitVec 64) (fun r => r) (fun _ ml => ml = m)
    (fun _ res0 ml hml => ?_) (fun J0 hJ0 => ?_)
  · subst hml
    let mkSt (rp mc : List (BitVec 32)) (tc tl : Nat) (ant : BitVec 64) (sig : List (BitVec 64))
        (shrk : List (BitVec 32)) : FullState :=
      { core := { s.core with repr := rp, min_clr := mc, tmp_cnt := tc, tmp_len := tl }
        scratch := { s.scratch with ant_sz := ant, sim_sig := sig, shrink_stk := shrk } }
    c0_hsteps
    have hinv0 : FullDenseInvNoLm c F0 F_cur (mkSt s.core.repr s.core.min_clr 0 0 256#64
        s.scratch.sim_sig s.scratch.shrink_stk) :=
      fullDenseInvNoLm_with_core_aux hinv hcl.repr_len hcl.min_clr_len_arr hcl.tmp_len_arr
        hcl.flags_len (Nat.zero_le _) { hsc with } rfl rfl
    refine wp_loop_inv
      (fun (res, sgn, ()) ml => ∃ rp mc tc tl ant sig shrk,
        sgn.toNat ≤ 2 ∧ tc ≤ s.core.cur_vars ∧ tl ≤ s.core.cur_vars ∧
        FullDenseInvNoLm c F0 F_cur (mkSt rp mc tc tl ant sig shrk) ∧
        (∀ i < tc, (mc[i]?.getD 0#32).toNat < c.max_vars) ∧
        (∀ i < tl, (shrk[i]?.getD 0#32).toNat < c.max_vars) ∧
        (FullMem c (mkSt rp mc tc tl ant sig shrk) ⋆ R) ml)
      (fun (_, sgn, _) _ => 2 - sgn.toNat)
      (fun Js hJs => by
        c0_hsteps; exact hJs (res0, 0#32, ()) m
          ⟨s.core.repr, s.core.min_clr, 0, 0, 256#64, s.scratch.sim_sig, s.scratch.shrink_stk,
           by decide, Nat.zero_le _, Nat.zero_le _, hinv0,
           fun _ h => by omega, fun _ h => by omega, hm⟩)
      (fun Js (res, sgn, ()) ml ⟨rp, mc, tc, tl, ant, sig, shrk, hsgn_le, htc, htl, hinv_s,
          hmc_ok, hshrk_ok, hml⟩ ihs => ?_)
    c0_hsteps_nogrp
    refine wp_join_state0
      (α := List (BitVec 32) × List (BitVec 32) × Nat × Nat × BitVec 64 ×
        List (BitVec 64) × List (BitVec 32))
      (fun ⟨rpF, mcF, tcF, tlF, antF, sigF, shrkF⟩ mf =>
        tcF ≤ s.core.cur_vars ∧ tlF ≤ s.core.cur_vars ∧
        FullDenseInvNoLm c F0 F_cur (mkSt rpF mcF tcF tlF antF sigF shrkF) ∧
        (∀ i < tcF, (mcF[i]?.getD 0#32).toNat < c.max_vars) ∧
        (∀ i < tlF, (shrkF[i]?.getD 0#32).toNat < c.max_vars) ∧
        (FullMem c (mkSt rpF mcF tcF tlF antF sigF shrkF) ⋆ R) mf)
      (fun _ ⟨rpF, mcF, tcF, tlF, antF, sigF, shrkF⟩ mf
          ⟨htcF, htlF, hinvF, hmcF, hshrkF, hmf⟩ => ?_)
      (fun Jend hJend => ?_)
    · -- Cleanup loops: zero `s1[st1[0..tcF)]` then `s2[st2[0..tlF)]`, reset `tmp_cnt=0, tmp_len=0`
      have hmcF_len : mcF.length = c.max_vars := hinvF.1.core_ok.min_clr_len_arr
      have hshrkF_len : shrkF.length = c.max_vars := hinvF.1.scratch_ok.shrink_stk_len
      c0_hsteps
      refine wp_loop_inv
        (fun (i, ()) mi => ∃ rpi, i.toNat ≤ tcF ∧ rpi.length = 2 * c.max_vars ∧
          (FullMem c (mkSt rpi mcF tcF tlF antF sigF shrkF) ⋆ R) mi)
        (fun (i, ()) _ => tcF - i.toNat)
        (fun J1 hJ1 => by
          c0_hsteps; exact hJ1 (0#64, ()) mf ⟨rpF, Nat.zero_le _, hinvF.1.core_ok.repr_len, hmf⟩)
        (fun J1 (i, ()) mi ⟨rpi, hi_le, hrpi_len, hmi⟩ ih1 => ?_)
      dsimp only [mkSt] at hmi
      c0_hsteps
      · have hi_lt : i.toNat < tcF := by c0_bound
        have hidx_lt : (mcF[i.toNat]'(by omega)).toNat < c.max_vars := by
          have := hmcF i.toNat hi_lt
          rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
        c0_hsteps
        exact ih1 (i + 1#64, ()) m (by c0_bound)
          ⟨_, by c0_bound, by rw [repr64Set_length, hrpi_len], hm⟩
      · refine wp_loop_inv
          (fun (i, ()) mi2 => ∃ sigi, i.toNat ≤ tlF ∧ sigi.length = c.max_vars ∧
            (FullMem c (mkSt rpi mcF tcF tlF antF sigi shrkF) ⋆ R) mi2)
          (fun (i, ()) _ => tlF - i.toNat)
          (fun J2 hJ2 => by
            c0_hsteps; exact hJ2 (0#64, ()) mi ⟨sigF, Nat.zero_le _, hinvF.1.scratch_ok.sim_sig_len,
              hmi⟩)
          (fun J2 (i, ()) mi2 ⟨sigi, hi2_le, hsigi_len, hmi2⟩ ih2 => ?_)
        dsimp only [mkSt] at hmi2
        c0_hsteps
        · have hi2_lt : i.toNat < tlF := by c0_bound
          have hidx_lt : (shrkF[i.toNat]'(by omega)).toNat < c.max_vars := by
            have := hshrkF i.toNat hi2_lt
            rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
          c0_hsteps
          exact ih2 (i + 1#64, ()) m (by c0_bound) ⟨_, by c0_bound, by simp [hsigi_len], hm⟩
        · have hsc_fin : ({ s.scratch with
              ant_sz := antF, sim_sig := sigi, shrink_stk := shrkF } : FullScratch).LengthsOk c :=
            { hsc with sim_sig_len := hsigi_len, shrink_stk_len := hshrkF_len }
          dsimp only [mkSt] at hinvF
          have hinv_fin := fullDenseInvNoLm_with_core_aux (tc' := 0) (tl' := 0) hinvF hrpi_len
            hmcF_len hcl.tmp_len_arr hcl.flags_len (Nat.zero_le _) hsc_fin rfl rfl
          exact hQ res rpi mcF antF sigi shrkF m hinv_fin hm
    · dsimp only [mkSt] at hml
      c0_hsteps
      · have hsgn_lt : sgn.toNat < 2 := by c0_bound
        have hsl_nat : (((src_lit >>> (1 : Nat)) <<< (1 : Nat)) ||| sgn).toNat =
            2 * (src_lit >>> (1 : Nat)).toNat + sgn.toNat := by
          have hs01 : sgn.toNat = 0 ∨ sgn.toNat = 1 := by omega
          rcases hs01 with h0 | h1
          · have hs0 : sgn = 0#32 := BitVec.eq_of_toNat_eq h0; subst hs0
            rw [BitVec.or_zero]; c0_bound
          · have hs1 : sgn = 1#32 := BitVec.eq_of_toNat_eq h1; subst hs1
            rw [FullBvaFwdTactics.bv32_or1_of_even (by c0_bound)]; c0_bound
        have hsl_lt : (((src_lit >>> (1 : Nat)) <<< (1 : Nat)) ||| sgn).toNat <
            2 * s.core.cur_vars := by omega
        obtain ⟨hbd_sl, hslice_sl⟩ := hop_wvec_bounds hinv hsl_lt
        let sl : BitVec 32 := ((src_lit >>> (1 : Nat)) <<< (1 : Nat)) ||| sgn
        have hsl_lt_sl : sl.toNat < 2 * s.core.cur_vars := hsl_lt
        have hwv_sl0 : (BitVec.setWidth 64 sl <<< (1 : Nat)).toNat < s.core.wvec.length := by
          c0_bound
        have hwv_sl1 : ((BitVec.setWidth 64 sl <<< (1 : Nat)) + 1).toNat < s.core.wvec.length := by
          change ((BitVec.setWidth 64 sl <<< (1 : Nat)) + 1#64).toNat < _; c0_bound
        have hoff_eq : (s.core.wvec[2 * sl.toNat]'(by omega)).toNat =
            fullWatchOffCore s.core sl.toNat := by
          unfold fullWatchOffCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
        have hsz_eq : (s.core.wvec[2 * sl.toNat + 1]'(by omega)).toNat =
            fullWatchSizeCore s.core sl.toNat := by
          unfold fullWatchSizeCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
        let off0 := fullWatchOffCore s.core sl.toNat
        let sz0 := fullWatchSizeCore s.core sl.toNat
        have hoff_sz_le : off0 + sz0 ≤ s.core.wlen := hbd_sl
        have h2sl0 : (BitVec.setWidth 64 sl <<< (1 : Nat)).toNat = 2 * sl.toNat := by c0_bound
        have h2sl1 : ((BitVec.setWidth 64 sl <<< (1 : Nat)) + 1).toNat = 2 * sl.toNat + 1 := by
          change ((BitVec.setWidth 64 sl <<< (1 : Nat)) + 1#64).toNat = _; c0_bound
        have hoff_c0 : (BitVec.setWidth 64
            (s.core.wvec[(BitVec.setWidth 64 sl <<< (1 : Nat)).toNat]'hwv_sl0)).toNat = off0 := by
          rw [bv64_setWidth_32]; simp only [h2sl0]; exact hoff_eq
        have hmod0 : 2 * sl.toNat % 2 ^ 64 = 2 * sl.toNat := Nat.mod_eq_of_lt (by omega)
        have hmod1 : (2 * sl.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = 2 * sl.toNat + 1 :=
          by c0_bound
        have hend_mod : ((s.core.wvec[2 * sl.toNat % 2 ^ 64]'(by rw [hmod0]; omega)).toNat +
            (s.core.wvec[(2 * sl.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
              rw [hmod1]; omega)).toNat) % 2 ^ 64 = off0 + sz0 := by
          simp only [hmod0, hmod1, hoff_eq, hsz_eq]; exact Nat.mod_eq_of_lt (by omega)
        c0_hsteps_nogrp
        refine wp_loop_inv
          (fun (res1, p, ()) mlp => ∃ rpp mcp tcp tlp antp sigp shrkp,
            off0 ≤ p.toNat ∧ p.toNat ≤ off0 + sz0 ∧ tcp ≤ s.core.cur_vars ∧
            tlp ≤ s.core.cur_vars ∧
            FullDenseInvNoLm c F0 F_cur (mkSt rpp mcp tcp tlp antp sigp shrkp) ∧
            (∀ i < tcp, (mcp[i]?.getD 0#32).toNat < c.max_vars) ∧
            (∀ i < tlp, (shrkp[i]?.getD 0#32).toNat < c.max_vars) ∧
            DenseWatchSliceOk F_cur s.core sl.toNat p.toNat (off0 + sz0 - p.toNat) ∧
            (FullMem c (mkSt rpp mcp tcp tlp antp sigp shrkp) ⋆ R) mlp)
          (fun (_, p, _) _ => off0 + sz0 - p.toNat)
          (fun Jp hJp => by
            c0_hfast
            exact hJp (res, _, ()) ml ⟨rp, mc, tc, tl, ant, sig, shrk,
              by rw [hoff_c0]; exact Nat.le_refl _, by rw [hoff_c0]; omega, htc, htl, hinv_s,
              hmc_ok, hshrk_ok, by rw [hoff_c0, Nat.add_sub_cancel_left]; exact hslice_sl, hml⟩)
          (fun Jp (res1, p, ()) mlp ⟨rpp, mcp, tcp, tlp, antp, sigp, shrkp, hp_ge, hp_le, htcp,
              htlp, hinvp, hmcp_ok, hshrkp_ok, hrem, hmlp⟩ ihp => ?_)
        dsimp only [mkSt] at hmlp
        c0_hfast
        · have hp_lt : p.toNat < off0 + sz0 := by rw [← hend_mod]; assumption
          have hp_ws : p.toNat < s.core.wstk.length := by omega
          have hp1_n : (p + 1).toNat = p.toNat + 1 := by
            change (p + 1#64).toNat = _; simp only [bv_c0]; omega
          have hp1_mod : (p.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = p.toNat + 1 := by
            rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]; omega
          have hinvp1 : FullDenseInvNoLm c F0 F_cur
              (mkSt rpp mcp tcp tlp (antp - 1#64) sigp shrkp) :=
            fullDenseInvNoLm_with_core_aux (tc' := tcp) (tl' := tlp) hinvp
              hinvp.1.core_ok.repr_len hinvp.1.core_ok.min_clr_len_arr hcl.tmp_len_arr
              hcl.flags_len hinvp.1.core_ok.tmp_len_le { hinvp.1.scratch_ok with } rfl rfl
          c0_hfast
          · have ⟨hot_lt, _, hrem_next⟩ := FullBvaFwdHelpers.bva_slice_bin_info hrem (by omega)
              hp_ws (by assumption)
            c0_call hHop2
            refine ⟨c, F0, F_cur, mkSt rpp mcp tcp tlp (antp - 1#64) sigp shrkp, R, rfl, hinvp1,
              hot_lt, htcp, htlp, hmcp_ok, hshrkp_ok, hm,
              fun r1 rp1 mc1 tc1 tl1 ant1 sig1 shrk1 m1 hinv1 htc1 htl1 hmc1 hshrk1 _ hm1 => ?_⟩
            c0_hfast
            exact ihp (res1 + r1, p + 1, ()) m1 (by dsimp only; rw [hp1_n]; omega)
              ⟨rp1, mc1, tc1, tl1, ant1, sig1, shrk1, by rw [hp1_n]; omega, by rw [hp1_n]; omega,
               htc1, htl1, hinv1, hmc1, hshrk1,
               by rw [hp1_n, show off0 + sz0 - (p.toNat + 1) = off0 + sz0 - p.toNat - 1 by omega]
                  exact hrem_next, hm1⟩
          · have hm_flat : (FullMem c
                { core := { s.core with repr := rpp, min_clr := mcp,
                                        tmp_cnt := tcp, tmp_len := tlp }
                  scratch := { s.scratch with ant_sz := antp - 1#64, sim_sig := sigp,
                                              shrink_stk := shrkp } } ⋆ R) m := hm
            clear hm
            have ⟨h2le, hrem_next⟩ := FullBvaFwdHelpers.bva_slice_occ_info hrem (by omega) hp_ws
              (by assumption)
            have hp1_ws : p.toNat + 1 < s.core.wstk.length := by omega
            have ⟨_, hcr_ref, _⟩ := FullBvaFwdHelpers.fwd_slice_occ_info hrem (by omega) hp_ws
              hp1_ws (by assumption)
            have hcr_wf := hinv.2.1.arena.refs_wf _ hcr_ref
            have hp2_n : (p + 1 + 1).toNat = p.toNat + 2 := by
              change (p + 1#64 + 1#64).toNat = _; simp only [bv_c0]; omega
            let cr := s.core.wstk[p.toNat + 1]'hp1_ws
            have hcr_al : cr.toNat + 3 + fullArenaClauseSizeCore s.core cr.toNat ≤
                s.core.arena_len := by
              have h1 := hcr_wf.2.2.1; have h2 := hcr_wf.2.2.2.1; dsimp only [cr]; omega
            have hcr_eq : s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws) = cr := by
              dsimp only [cr]; simp only [hp1_n]
            have hcr0_eq : (BitVec.setWidth 64
                (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws))).toNat = cr.toNat := by
              rw [bv64_setWidth_32, hcr_eq]
            have hcr_b0 : (BitVec.setWidth 64
                (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws))).toNat <
                s.core.arena.length := by rw [hcr0_eq]; omega
            have hcr2_eq : (BitVec.setWidth 64
                (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws)) + 2).toNat =
                cr.toNat + 2 := by
              change (BitVec.setWidth 64 _ + 2#64).toNat = _; rw [hcr_eq]; simp only [bv_c0]; omega
            have hcr_b2 : (BitVec.setWidth 64
                (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws)) + 2).toNat <
                s.core.arena.length := by rw [hcr2_eq]; omega
            have hsz_cr : (s.core.arena[cr.toNat + 2]'(by omega)).toNat =
                fullArenaClauseSizeCore s.core cr.toNat := by
              unfold fullArenaClauseSizeCore
              rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
            have hcr_sz_le : cr.toNat + 3 + (s.core.arena[cr.toNat + 2]'(by omega)).toNat ≤
                s.core.arena.length := by rw [hsz_cr]; omega
            c0_hfast
            · have hng_cr : fullArenaClauseGarbCore s.core cr.toNat = false := by
                unfold fullArenaClauseGarbCore fullArenaHdrCore
                rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                have h1 : s.core.arena[(BitVec.setWidth 64
                    (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws))).toNat]'hcr_b0 &&&
                    (524288#32 ||| 4194304#32) = 0#32 := by assumption
                exact FullBvaFwdHelpers.garb_false_of_and_garb_red_eq_zero (by
                  simpa only [hcr0_eq] using h1)
              clear hQ ihs hJend
              refine wp_loop_inv
                (fun (resk, k, ()) mk => ∃ rpk mck tck tlk antk sigk shrkk,
                  k.toNat ≤ (s.core.arena[cr.toNat + 2]'(by omega)).toNat ∧
                  tck ≤ s.core.cur_vars ∧ tlk ≤ s.core.cur_vars ∧
                  FullDenseInvNoLm c F0 F_cur (mkSt rpk mck tck tlk antk sigk shrkk) ∧
                  (∀ i < tck, (mck[i]?.getD 0#32).toNat < c.max_vars) ∧
                  (∀ i < tlk, (shrkk[i]?.getD 0#32).toNat < c.max_vars) ∧
                  (FullMem c (mkSt rpk mck tck tlk antk sigk shrkk) ⋆ R) mk)
                (fun (_, k, _) _ => (s.core.arena[cr.toNat + 2]'(by omega)).toNat - k.toNat)
                (fun Jk hJk => by
                  c0_hfast; exact hJk (res1, 0#32, ()) m
                    ⟨rpp, mcp, tcp, tlp, antp - 1#64, sigp, shrkp, Nat.zero_le _, htcp, htlp,
                     hinvp1, hmcp_ok, hshrkp_ok, hm_flat⟩)
                (fun Jk (resk, k, ()) mk ⟨rpk, mck, tck, tlk, antk, sigk, shrkk, hk_le, htck, htlk,
                    hinvk, hmck_ok, hshrkk_ok, hmk⟩ ihk => ?_)
              dsimp only [mkSt] at hmk
              c0_hsplit
              · have hk_lt : k.toNat < (s.core.arena[cr.toNat + 2]'(by omega)).toNat := by
                  have h1 : k.toNat < (s.core.arena[(BitVec.setWidth 64
                      (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws)) +
                      2).toNat]'hcr_b2).toNat := by assumption
                  simpa only [hcr2_eq] using h1
                have hk1 : (k + 1#32).toNat = k.toNat + 1 := by simp only [bv_c0]; omega
                c0_hsplit
                · have hcrk_b : (BitVec.setWidth 64
                      (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws)) + 3 +
                      BitVec.setWidth 64 k).toNat < s.core.arena.length := by
                    change (BitVec.setWidth 64 _ + 3#64 + BitVec.setWidth 64 k).toNat < _
                    rw [hcr_eq]; simp only [bv_c0]; omega
                  have hol_mem : (s.core.arena[cr.toNat + 3 + k.toNat]'(by omega)).toNat ∈
                      fullArenaClauseLitsCore s.core cr.toNat :=
                    List.mem_of_getElem? (FullBvaFwdHelpers.fullArenaClauseLitsCore_getElem
                      (by rw [← hsz_cr]; exact hk_lt) (by omega))
                  have hol_lt := hinv.2.1.arena.lits_lt cr.toNat hcr_ref hng_cr _ hol_mem
                  have hcrk_eq : (BitVec.setWidth 64 cr + 3 + BitVec.setWidth 64 k).toNat =
                      cr.toNat + 3 + k.toNat := by
                    change (BitVec.setWidth 64 cr + 3#64 + BitVec.setWidth 64 k).toNat = _
                    simp only [bv_c0]; omega
                  c0_hfast
                  · c0_call hHop2
                    refine ⟨c, F0, F_cur, mkSt rpk mck tck tlk antk sigk shrkk, R, rfl, hinvk, ?_,
                      htck, htlk, hmck_ok, hshrkk_ok, hmk,
                      fun r1 rp1 mc1 tc1 tl1 ant1 sig1 shrk1 m1 hinv1 htc1 htl1 hmc1 hshrk1 _
                          hm1 => ?_⟩
                    · simpa only [hcr_eq, hcrk_eq] using hol_lt
                    · c0_hfast
                      exact ihk (resk + r1, k + 1#32, ()) m1 (by dsimp only; rw [hk1]; omega)
                        ⟨rp1, mc1, tc1, tl1, ant1, sig1, shrk1, by rw [hk1]; omega, htc1, htl1,
                         hinv1, hmc1, hshrk1, hm1⟩
                  · exact ihk (resk, k + 1#32, ()) mk (by dsimp only; rw [hk1]; omega)
                      ⟨rpk, mck, tck, tlk, antk, sigk, shrkk, by rw [hk1]; omega, htck, htlk,
                       hinvk, hmck_ok, hshrkk_ok, hmk⟩
                · c0_hfast
                  exact ihp (resk, p + 1 + 1, ()) mk (by dsimp only; rw [hp2_n]; omega)
                    ⟨rpk, mck, tck, tlk, antk, sigk, shrkk, by rw [hp2_n]; omega,
                     by rw [hp2_n]; omega, htck, htlk, hinvk, hmck_ok, hshrkk_ok,
                     by rw [hp2_n, show off0 + sz0 - (p.toNat + 2) = off0 + sz0 - p.toNat - 2
                          by omega]; exact hrem_next, hmk⟩
              · c0_hfast
                exact ihp (resk, p + 1 + 1, ()) mk (by dsimp only; rw [hp2_n]; omega)
                  ⟨rpk, mck, tck, tlk, antk, sigk, shrkk, by rw [hp2_n]; omega,
                   by rw [hp2_n]; omega, htck, htlk, hinvk, hmck_ok, hshrkk_ok,
                   by rw [hp2_n, show off0 + sz0 - (p.toNat + 2) = off0 + sz0 - p.toNat - 2
                        by omega]; exact hrem_next, hmk⟩
            · exact ihp (res1, p + 1 + 1, ()) m (by dsimp only; rw [hp2_n]; omega)
                ⟨rpp, mcp, tcp, tlp, antp - 1#64, sigp, shrkp, by rw [hp2_n]; omega,
                 by rw [hp2_n]; omega, htcp, htlp, hinvp1, hmcp_ok, hshrkp_ok,
                 by rw [hp2_n, show off0 + sz0 - (p.toNat + 2) = off0 + sz0 - p.toNat - 2
                      by omega]; exact hrem_next, hm_flat⟩
          · exfalso
            have ⟨h2le, _⟩ := FullBvaFwdHelpers.bva_slice_occ_info hrem (by omega) hp_ws
              (by assumption)
            have hge : ¬ (p.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 <
                ((s.core.wvec[2 * sl.toNat % 2 ^ 64]'(by rw [hmod0]; omega)).toNat +
                 (s.core.wvec[(2 * sl.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                   rw [hmod1]; omega)).toNat) % 2 ^ 64 := by assumption
            rw [hend_mod, hp1_mod] at hge; omega
        all_goals
          exact ihs (res1, sgn + 1#32, ()) mlp (by simp only [bv_c0]; omega)
            ⟨rpp, mcp, tcp, tlp, antp, sigp, shrkp, by simp only [bv_c0]; omega, htcp, htlp, hinvp,
             hmcp_ok, hshrkp_ok, hmlp⟩
      · exact hJend ⟨rp, mc, tc, tl, ant, sig, shrk⟩ ml
          ⟨htc, htl, hinv_s, hmc_ok, hshrk_ok, hml⟩
      · exact hJend ⟨rp, mc, tc, tl, ant, sig, shrk⟩ ml
          ⟨htc, htl, hinv_s, hmc_ok, hshrk_ok, hml⟩
  · c0_hsteps
    · exact hJ0 1#64 m rfl
    · exact hJ0 0#64 m rfl

/-! ## 6. Max-Degree Binary Heap Sifts (`full_fheap_up_wp`, `full_fheap_down_wp`) -/

theorem full_fheap_up_wp (Γ : Env) :
    ∀ args m Q X, fullFheapUpSpec args m Q X → Func.wp Γ full_fheap_up_body args m Q X := by
  rintro ⟨hp_ptr, ps_ptr, wvec_ptr, p0, ⟨⟩⟩ m Q X
    ⟨nlits, hp0, ps0, wvec, R, hhp_len, hps_len, hwv_len, hnl_lt, hp0_lt, hhp0_ok, hm, hQ⟩
  have hi32 : i32.bytes = 4 := rfl
  have hl0_lt : (hp0[p0.toNat]'(by omega)).toNat < nlits := by
    have := hhp0_ok p0.toNat (Nat.le_refl _)
    rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
  have h2l0 : ((BitVec.setWidth 64 (hp0[p0.toNat]'(by omega)) <<< (1 : Nat)) + 1#64).toNat =
      2 * (hp0[p0.toNat]'(by omega)).toNat + 1 := by c0_bound
  c0_hsteps_nogrp
  refine wp_join_state1 (t := i32) (α := BitVec 32 × List (BitVec 32) × List (BitVec 32))
    (fun st => st.1)
    (fun ⟨pf, hpf, psf⟩ mf =>
      pf.toNat ≤ p0.toNat ∧ hpf.length = hp0.length ∧ psf.length = ps0.length ∧
      (∀ i ≤ p0.toNat, ∃ j ≤ p0.toNat, hpf[i]? = hp0[j]?) ∧
      (∀ i, p0.toNat < i → hpf[i]? = hp0[i]?) ∧
      (array (t := i32) hp_ptr hpf ⋆ array (t := i32) ps_ptr psf ⋆
        array (t := i32) wvec_ptr wvec ⋆ R) mf)
    (fun _ ⟨pf, hpf, psf⟩ mf ⟨hpf_le, hhpf_len, hpsf_len, hsubf, houtf, hmf⟩ => ?_)
    (fun Jend hJend => ?_)
  · clear m hm; c0_hsteps
    have hset : ∀ x : BitVec 32, (BitVec.setWidth 64 x).toNat = x.toNat := bv64_setWidth_32
    let hpf' := hpf.set pf.toNat (hp0[p0.toNat]'(by omega))
    let psf' := psf.set (hp0[p0.toNat]'(by omega)).toNat pf
    have hmem : (array (t := i32) hp_ptr hpf' ⋆ array (t := i32) ps_ptr psf' ⋆
        array (t := i32) wvec_ptr wvec ⋆ R) m := by
      simp only [sep_emp] at hm
      exact sep_ac (show (array (t := i32) ps_ptr psf' ⋆ (array (t := i32) hp_ptr hpf' ⋆
          (array (t := i32) wvec_ptr wvec ⋆ R))) m from by
        dsimp only [hpf', psf']; simpa only [hset] using hm)
    refine hQ hpf' psf' _ (by simp [hpf', hhpf_len]) (by simp [psf', hpsf_len])
      (fun i hi => ?_) (fun i hi => ?_) hmem
    · dsimp only [hpf']; by_cases hie : i = pf.toNat
      · subst hie
        refine ⟨p0.toNat, Nat.le_refl _, ?_⟩
        rw [List.getElem?_set_self (by omega), List.getElem?_eq_getElem (by omega)]
      · rw [List.getElem?_set_ne (Ne.symm hie)]; exact hsubf i hi
    · dsimp only [hpf']; rw [List.getElem?_set_ne (by omega)]; exact houtf i hi
  · refine wp_loop_inv
      (fun (p, ()) ml => ∃ hpl psl,
        p.toNat ≤ p0.toNat ∧ hpl.length = hp0.length ∧ psl.length = ps0.length ∧
        (∀ i ≤ p0.toNat, ∃ j ≤ p0.toNat, hpl[i]? = hp0[j]?) ∧
        (∀ i, p0.toNat < i → hpl[i]? = hp0[i]?) ∧
        (array (t := i32) hp_ptr hpl ⋆ array (t := i32) ps_ptr psl ⋆
          array (t := i32) wvec_ptr wvec ⋆ R) ml)
      (fun (p, ()) _ => p.toNat)
      (fun J hJ => by
        c0_hsteps; exact hJ (p0, ()) m ⟨hp0, ps0, Nat.le_refl _, rfl, rfl,
          fun i hi => ⟨i, hi, rfl⟩, fun _ _ => rfl, hm⟩)
      (fun J (p, ()) ml ⟨hpl, psl, hp_le, hhpl_len, hpsl_len, hsub, hout, hml⟩ ih => ?_)
    clear m hm
    have hset : ∀ x : BitVec 32, (BitVec.setWidth 64 x).toNat = x.toNat := bv64_setWidth_32
    c0_hsteps
    · have hp_pos : 0 < p.toNat := by c0_bound
      have hpp_nat : ((p - 1) >>> (1 : Nat)).toNat = (p.toNat - 1) / 2 := by c0_bound
      have hpp_lt : ((p - 1) >>> (1 : Nat)).toNat < p.toNat := by omega
      have hpl_ok : (hpl[((p - 1) >>> (1 : Nat)).toNat]'(by omega)).toNat < nlits := by
        obtain ⟨j, hj, heq⟩ := hsub ((p - 1) >>> (1 : Nat)).toNat (by omega)
        have h1 := hhp0_ok j hj
        rw [← heq, List.getElem?_eq_getElem (by omega), Option.getD_some] at h1; exact h1
      have hpl_ok_sw : (hpl[(BitVec.setWidth 64 ((p - 1) >>> (1 : Nat))).toNat]'(by
          simp only [hset]; omega)).toNat < nlits := by simp only [hset]; exact hpl_ok
      c0_hsteps
      · exact hJend ⟨p, hpl, psl⟩ ml ⟨hp_le, hhpl_len, hpsl_len, hsub, hout, hml⟩
      · let hpl' := hpl.set p.toNat (hpl[((p - 1) >>> (1 : Nat)).toNat]'(by omega))
        let psl' := psl.set (hpl[((p - 1) >>> (1 : Nat)).toNat]'(by omega)).toNat p
        have hmem : (array (t := i32) hp_ptr hpl' ⋆ array (t := i32) ps_ptr psl' ⋆
            array (t := i32) wvec_ptr wvec ⋆ R) m := by
          simp only [sep_emp] at hm
          exact sep_ac (show (array (t := i32) ps_ptr psl' ⋆ (array (t := i32) hp_ptr hpl' ⋆
              (array (t := i32) wvec_ptr wvec ⋆ R))) m from by
            dsimp only [hpl', psl']; simpa only [hset] using hm)
        refine ih ((p - 1) >>> (1 : Nat), ()) _ hpp_lt
          ⟨hpl', psl', by omega, by simp [hpl', hhpl_len], by simp [psl', hpsl_len],
           fun i hi => ?_,
           fun i hi => by
             dsimp only [hpl']; rw [List.getElem?_set_ne (by omega)]; exact hout i hi,
           hmem⟩
        dsimp only [hpl']
        by_cases hie : i = p.toNat
        · subst hie
          obtain ⟨j, hj, heq⟩ := hsub ((p - 1) >>> (1 : Nat)).toNat (by omega)
          refine ⟨j, hj, ?_⟩
          rw [List.getElem?_set_self (by omega), ← heq, List.getElem?_eq_getElem (by omega)]
        · rw [List.getElem?_set_ne (Ne.symm hie)]; exact hsub i hi
    · exact hJend ⟨p, hpl, psl⟩ ml ⟨hp_le, hhpl_len, hpsl_len, hsub, hout, hml⟩

theorem full_fheap_down_wp (Γ : Env) :
    ∀ args m Q X, fullFheapDownSpec args m Q X → Func.wp Γ full_fheap_down_body args m Q X := by
  rintro ⟨hp_ptr, ps_ptr, wvec_ptr, p0, n, ⟨⟩⟩ m Q X
    ⟨nlits, hp0, ps0, wvec, R, hhp_len, hps_len, hwv_len, hnl_lt, hp0_lt, hn_le, hhp0_ok, hm, hQ⟩
  have hi32 : i32.bytes = 4 := rfl
  have hset : ∀ x : BitVec 32, (BitVec.setWidth 64 x).toNat = x.toNat := bv64_setWidth_32
  have hl0_lt : (hp0[p0.toNat]'(by omega)).toNat < nlits := by
    have := hhp0_ok p0.toNat hp0_lt
    rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
  have h2l0 : ((BitVec.setWidth 64 (hp0[p0.toNat]'(by omega)) <<< (1 : Nat)) + 1#64).toNat =
      2 * (hp0[p0.toNat]'(by omega)).toNat + 1 := by c0_bound
  c0_hsteps_nogrp
  refine wp_join_state1 (t := i32) (α := BitVec 32 × List (BitVec 32) × List (BitVec 32))
    (fun st => st.1)
    (fun ⟨pf, hpf, psf⟩ mf =>
      pf.toNat < n.toNat ∧ hpf.length = hp0.length ∧ psf.length = ps0.length ∧
      (∀ i < n.toNat, ∃ j < n.toNat, hpf[i]? = hp0[j]?) ∧
      (∀ i, n.toNat ≤ i → hpf[i]? = hp0[i]?) ∧
      (array (t := i32) hp_ptr hpf ⋆ array (t := i32) ps_ptr psf ⋆
        array (t := i32) wvec_ptr wvec ⋆ R) mf)
    (fun _ ⟨pf, hpf, psf⟩ mf ⟨hpf_lt, hhpf_len, hpsf_len, hsubf, houtf, hmf⟩ => ?_)
    (fun Jend hJend => ?_)
  · clear m hm; c0_hsteps
    let hpf' := hpf.set pf.toNat (hp0[p0.toNat]'(by omega))
    let psf' := psf.set (hp0[p0.toNat]'(by omega)).toNat pf
    have hmem : (array (t := i32) hp_ptr hpf' ⋆ array (t := i32) ps_ptr psf' ⋆
        array (t := i32) wvec_ptr wvec ⋆ R) m := by
      simp only [sep_emp] at hm
      exact sep_ac (show (array (t := i32) ps_ptr psf' ⋆ (array (t := i32) hp_ptr hpf' ⋆
          (array (t := i32) wvec_ptr wvec ⋆ R))) m from by
        dsimp only [hpf', psf']; simpa only [hset] using hm)
    refine hQ hpf' psf' _ (by simp [hpf', hhpf_len]) (by simp [psf', hpsf_len])
      (fun i hi => ?_) (fun i hi => ?_) hmem
    · dsimp only [hpf']; by_cases hie : i = pf.toNat
      · subst hie; refine ⟨p0.toNat, hp0_lt, ?_⟩
        rw [List.getElem?_set_self (by omega), List.getElem?_eq_getElem (by omega)]
      · rw [List.getElem?_set_ne (Ne.symm hie)]; exact hsubf i hi
    · dsimp only [hpf']; rw [List.getElem?_set_ne (by omega)]; exact houtf i hi
  · refine wp_loop_inv
      (fun (p, ()) ml => ∃ hpl psl,
        p.toNat < n.toNat ∧ hpl.length = hp0.length ∧ psl.length = ps0.length ∧
        (∀ i < n.toNat, ∃ j < n.toNat, hpl[i]? = hp0[j]?) ∧
        (∀ i, n.toNat ≤ i → hpl[i]? = hp0[i]?) ∧
        (array (t := i32) hp_ptr hpl ⋆ array (t := i32) ps_ptr psl ⋆
          array (t := i32) wvec_ptr wvec ⋆ R) ml)
      (fun (p, ()) _ => n.toNat - p.toNat)
      (fun J hJ => by
        c0_hsteps; exact hJ (p0, ()) m ⟨hp0, ps0, hp0_lt, rfl, rfl,
          fun i hi => ⟨i, hi, rfl⟩, fun _ _ => rfl, hm⟩)
      (fun J (p, ()) ml ⟨hpl, psl, hp_lt, hhpl_len, hpsl_len, hsub, hout, hml⟩ ih => ?_)
    clear m hm
    have hcp_nat : ((p <<< (1 : Nat)) + 1).toNat = 2 * p.toNat + 1 := by c0_bound
    c0_hsteps_nogrp
    · exact hJend ⟨p, hpl, psl⟩ ml ⟨hp_lt, hhpl_len, hpsl_len, hsub, hout, hml⟩
    · have hcp_lt : ((p <<< (1 : Nat)) + 1).toNat < n.toNat := by c0_bound
      have hcl_ok : (hpl[((p <<< (1 : Nat)) + 1).toNat]'(by omega)).toNat < nlits := by
        obtain ⟨j, hj, heq⟩ := hsub ((p <<< (1 : Nat)) + 1).toNat hcp_lt
        have h1 := hhp0_ok j hj
        rw [← heq, List.getElem?_eq_getElem (by omega), Option.getD_some] at h1; exact h1
      have hcl_ok_sw : (hpl[(BitVec.setWidth 64 ((p <<< (1 : Nat)) + 1)).toNat]'(by
          simp only [hset]; omega)).toNat < nlits := by simp only [hset]; exact hcl_ok
      c0_hsteps_nogrp
      refine wp_join_state (α := BitVec 32 × BitVec 32 × BitVec 32)
        (fun ⟨cp', cl', cd'⟩ => (cp', cl', cd', ()))
        (fun ⟨cp', cl', _⟩ mf =>
          p.toNat < cp'.toNat ∧ cp'.toNat < n.toNat ∧
          (∃ j < n.toNat, some cl' = hp0[j]?) ∧ cl'.toNat < nlits ∧ ml = mf)
        (fun _ ⟨cp', cl', cd'⟩ mf ⟨hgt_p, hcp'_lt, hcl'_mem, hcl'_lt, hmf⟩ => ?_)
        (fun Jc hJc => ?_)
      · rcases hmf with rfl
        c0_hsteps
        · exact hJend ⟨p, hpl, psl⟩ ml ⟨hp_lt, hhpl_len, hpsl_len, hsub, hout, hml⟩
        · let hpl' := hpl.set p.toNat cl'
          let psl' := psl.set cl'.toNat p
          refine ih (cp', ()) _ (by dsimp only; omega)
            ⟨hpl', psl', hcp'_lt, by simp [hpl', hhpl_len], by simp [psl', hpsl_len],
             fun i hi => ?_,
             fun i hi => by
               dsimp only [hpl']; rw [List.getElem?_set_ne (by omega)]; exact hout i hi,
             by dsimp only [hpl', psl'] at *; simp only [hset, sep_emp] at *; ecancel⟩
          dsimp only [hpl']
          by_cases hie : i = p.toNat
          · subst hie
            obtain ⟨j, hj, heq⟩ := hcl'_mem
            refine ⟨j, hj, ?_⟩
            rw [List.getElem?_set_self (by omega), heq]
          · rw [List.getElem?_set_ne (Ne.symm hie)]; exact hsub i hi
      · c0_hsteps
        · have hcp1_lt : (((p <<< (1 : Nat)) + 1) + 1).toNat < n.toNat := by c0_bound
          have hsl_ok :
              (hpl[(((p <<< (1 : Nat)) + 1) + 1).toNat]'(by omega)).toNat < nlits := by
            obtain ⟨j, hj, heq⟩ := hsub (((p <<< (1 : Nat)) + 1) + 1).toNat hcp1_lt
            have h1 := hhp0_ok j hj
            rw [← heq, List.getElem?_eq_getElem (by omega), Option.getD_some] at h1; exact h1
          have hsl_ok_sw :
              (hpl[(BitVec.setWidth 64 (((p <<< (1 : Nat)) + 1) + 1)).toNat]'(by
                simp only [hset]; omega)).toNat < nlits := by simp only [hset]; exact hsl_ok
          c0_hsteps
          · obtain ⟨j, hj, heq⟩ := hsub (((p <<< (1 : Nat)) + 1) + 1).toNat hcp1_lt
            exact hJc ⟨_, _, _⟩ ml ⟨by c0_bound, hcp1_lt,
              ⟨j, hj, by simp only [hset]; rw [← heq, List.getElem?_eq_getElem (by omega)]⟩,
              by simp only [hset]; exact hsl_ok, rfl⟩
          · obtain ⟨j, hj, heq⟩ := hsub ((p <<< (1 : Nat)) + 1).toNat hcp_lt
            exact hJc ⟨_, _, _⟩ ml ⟨by c0_bound, hcp_lt,
              ⟨j, hj, by simp only [hset]; rw [← heq, List.getElem?_eq_getElem (by omega)]⟩,
              by simp only [hset]; exact hcl_ok, rfl⟩
        · obtain ⟨j, hj, heq⟩ := hsub ((p <<< (1 : Nat)) + 1).toNat hcp_lt
          exact hJc ⟨_, _, _⟩ ml ⟨by c0_bound, hcp_lt,
            ⟨j, hj, by simp only [hset]; rw [← heq, List.getElem?_eq_getElem (by omega)]⟩,
            by simp only [hset]; exact hcl_ok, rfl⟩
    · exact absurd (by assumption : true = false) (by decide)

end LeanQbe.T.Examples.Kissat.FullBvaHeap
