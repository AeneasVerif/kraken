/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM7FidelityCore
public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Examples.Kissat.FullM7WalkProof0
import LeanQbe.T.AbiLemmas
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1
import LeanQbe.T.Examples.Kissat.FullOneLitConflLemmas
import LeanQbe.T.Examples.Kissat.FullPropDecLemmas
import LeanQbe.T.Logic.Bytes
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat `FullFidelityAssemblyStep7` Proof Shard 1 (`full_walk_fid_step7_wp`)

Certifies `FullM7FidelityCore.full_walk_fid_body` (slot `[169]` of `fidModule`) against
`Full.fullWalkSpec` under Step 7's strengthened `step7CbInvSpec` contract for
`full_walk_cb_inv_m7` (`0` SAT model proofs, `XPost := False`, `std3` axioms only).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep7

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM7FidelityCore
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open Kraken.Bedrock2.Test

section WalkProof

open LeanQbe.T.Examples.Kissat.FullM7Walk

private theorem fidWalk_bv64_add1_lt {x : BitVec 64} {n : Nat}
    (h1 : x.toNat < n) (h2 : n + 1 < 2 ^ 64) :
    (x + 1#64).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl,
    Nat.mod_eq_of_lt (by omega)]

private theorem fidWalk_bv64_sub1 {x : BitVec 64} (h : 0 < x.toNat) :
    (x - 1#64).toNat = x.toNat - 1 := by
  rw [BitVec.toNat_sub, show (1#64 : BitVec 64).toNat = 1 from rfl]
  have hx := x.isLt
  omega

private theorem fidWalk_bv64_shr2_add1_le {v mv : Nat}
    (hv_le : v ≤ mv) (hmv_pos : 0 < mv) (hmv : mv < 2 ^ 30) :
    ((BitVec.ofNat 64 v >>> BitVec.signExtend 64 2#32) + 1#64).toNat = v / 4 + 1 ∧
      v / 4 + 1 ≤ 2 * mv := by
  have hsh : (BitVec.ofNat 64 v >>> BitVec.signExtend 64 2#32).toNat = v / 4 := by
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (by omega)]
  have hadd :
      ((BitVec.ofNat 64 v >>> BitVec.signExtend 64 2#32) + 1#64).toNat = v / 4 + 1 := by
    rw [BitVec.toNat_add, hsh, show (1#64 : BitVec 64).toNat = 1 from rfl,
      Nat.mod_eq_of_lt (by omega)]
  exact ⟨hadd, by omega⟩

private theorem fidWalk_coreLengths_with_fuel {c : FullCfg} {k : FullCoreState} {f' : BitVec 64}
    (h : k.LengthsOk c) : ({ k with fuel := f' } : FullCoreState).LengthsOk c :=
  ⟨h.vals_len, h.lit_mark_len, h.mrk_len, h.flags_len, h.lvl_len, h.rsns_len, h.trl_len,
    h.trail_pos_len, h.tmp_len_arr, h.min_clr_len_arr, h.frame_trail_len, h.frame_dec_len,
    h.wvec_len, h.repr_len, h.min_stk_len, h.arena_len_arr, h.wstk_len_arr, h.cur_vars_ge,
    h.cur_vars_le, h.arena_len_le, h.wlen_le, h.trail_end_le, h.propagated_le, h.tmp_len_le,
    h.min_clr_len_le⟩

private theorem fidWalk_scratchLengths_with_wv {c : FullCfg} {sc : FullScratch}
    {wv' : List (BitVec 8)} (h : sc.LengthsOk c) (hl : wv'.length = c.max_vars) :
    ({ sc with walk_best := wv' } : FullScratch).LengthsOk c :=
  ⟨h.walk_vals_len, h.phases_len, h.phases_target_len, h.phases_best_len, hl, h.heap_len_arr,
    h.pos_len, h.shrink_stk_len, h.q_prev_len, h.q_next_len, h.q_stamp_len, h.wsort_len,
    h.work_stk1_len, h.work_stk2_len, h.tarjan_mark_len, h.tarjan_reach_len, h.score_len,
    h.sim_sig_len, h.glue_used_len, h.last_learned_len, h.delayed_len_arr, h.red_refs_len,
    h.extend_stk_len, h.scratch_buf_len⟩

private theorem fidWalk_scratchLengths_with_wsort {c : FullCfg} {sc : FullScratch}
    {ws' : List (BitVec 32)} (h : sc.LengthsOk c) (hl : ws'.length = 2 * c.max_vars) :
    ({ sc with wsort := ws' } : FullScratch).LengthsOk c :=
  ⟨h.walk_vals_len, h.phases_len, h.phases_target_len, h.phases_best_len, h.walk_best_len,
    h.heap_len_arr, h.pos_len, h.shrink_stk_len, h.q_prev_len, h.q_next_len, h.q_stamp_len, hl,
    h.work_stk1_len, h.work_stk2_len, h.tarjan_mark_len, h.tarjan_reach_len, h.score_len,
    h.sim_sig_len, h.glue_used_len, h.last_learned_len, h.delayed_len_arr, h.red_refs_len,
    h.extend_stk_len, h.scratch_buf_len⟩

private theorem fidWalk_bv64_shl1 {x : BitVec 64} (hx : 2 * x.toNat < 2 ^ 64) :
    (x <<< BitVec.signExtend 64 1#32).toNat = 2 * x.toNat := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

private theorem fidWalk_zext32 (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide))]

private theorem fidWalk_rshift32_lt {x : BitVec 64} :
    (x >>> 32#64).toNat < 2 ^ 32 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hx := x.isLt; omega

private theorem fidWalk_close_Q {c : FullCfg} {s s' : FullState} {fuel' : BitVec 64}
    {m' : Mem 64} {R : Mem 64 → Prop} {Q : Post []}
    (hQ : ∀ (fuel' : BitVec 64) (sc' : FullScratch) (m' : Mem 64),
      let s'' : FullState := { core := { s.core with fuel := fuel' }, scratch := sc' }
      FullState.LengthsOk c s'' → fuel'.toNat ≤ s.core.fuel.toNat →
      FullExtScratchPres s s'' → (FullMem c s'' ⋆ R) m' → Q () m')
    (hcore : s'.core = { s.core with fuel := fuel' })
    (hlen : s'.LengthsOk c) (hfuel : fuel'.toNat ≤ s.core.fuel.toNat)
    (hpres : FullExtScratchPres s s') (hm' : (FullMem c s' ⋆ R) m') : Q () m' := by
  have hst : s' = { core := { s.core with fuel := fuel' }, scratch := s'.scratch } := by
    rcases s' with ⟨c', sc'⟩; dsimp only at hcore; subst hcore; rfl
  have hfin := hQ fuel' s'.scratch m'
  rw [← hst] at hfin
  exact hfin hlen hfuel hpres hm'

private theorem fidRngNext_call {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {args : Tup (Arg Val) [i64]} {k : Tup Val [i64] → Expr Val Cont rs}
    (hRng : ∀ a m Q X, fullRngNextSpec a m Q X → Γ "full_rng_next" [i64] [i64] a m Q X)
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    (hHdr : args.fst.val = c.hdr) (hSafe : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ r s' m', s'.core = s.core → s'.LengthsOk c → FullExtScratchPres s s' →
      (FullMem c s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (Expr.call "full_rng_next" args k) m := by
  refine wp_call_of_spec args k (hRng _ m _ X ⟨c, s, R, hHdr, hSafe, hm, ?_⟩)
  rintro ⟨r, ⟨⟩⟩ s' m' hcore hs' hscr hm'
  refine hk r s' m' (fullCoreState_agrees_with_scratch hcore) hs' ⟨?_, ?_⟩ hm'
  · rw [hscr]
  · rw [hscr]

/-- Parametric `Func.wp` proof for `full_walk_fid`, directly certifying `Full.fullWalkSpec`. -/
theorem full_walk_fid_step7_wp (Γ : Env)
    (hInitVals : ∀ a m Q X, m7InitValsSpec a m Q X →
      Γ "full_walk_init_vals_m7" [i64] [] a m Q X)
    (hCollect : ∀ a m Q X, m7CollectSpec a m Q X →
      Γ "full_walk_collect_m7" [i64] [i64] a m Q X)
    (hCbInv : ∀ a m Q X, step7CbInvSpec a m Q X →
      Γ "full_walk_cb_inv_m7" [i64, i64, i64] [i64] a m Q X)
    (hInitTable : ∀ a m Q X, m7InitTableSpec a m Q X →
      Γ "full_walk_init_table_m7" [i64, i64] [] a m Q X)
    (hBuildOcc : ∀ a m Q X, m7BuildOccSpec a m Q X →
      Γ "full_walk_build_occ_m7" [i64, i64] [i64] a m Q X)
    (hEffort : ∀ a m Q X, m7EffortSpec a m Q X →
      Γ "full_walk_effort_m7" [i64, i64] [i64] a m Q X)
    (hPick : ∀ a m Q X, m7PickSpec a m Q X →
      Γ "full_walk_pick_m7" [i64, i32, i64] [i64] a m Q X)
    (hFlip : ∀ a m Q X, m7FlipSpec a m Q X →
      Γ "full_walk_flip_m7" [i64, i32, i64, i64] [i64] a m Q X)
    (hSaveMin : ∀ a m Q X, m7SaveMinSpec a m Q X →
      Γ "full_walk_save_min_m7" [i64, i64, Ty.bool] [] a m Q X)
    (hRng : ∀ a m Q X, fullRngNextSpec a m Q X →
      Γ "full_rng_next" [i64] [i64] a m Q X)
    (a : Tup Val [i64]) (m : Mem 64) (Q : Post []) (X : XPost)
    (hS : fullWalkSpec a m Q X) :
    Func.wp Γ full_walk_fid_body a m Q X := by
  rcases a with ⟨h, ⟨⟩⟩
  rcases hS with ⟨c, F0, s, R, rfl, hinv, hm, hQ⟩
  have hlen := hinv.lengths
  have hmax := c.hmaxv
  have hscr := c.hscr
  have hdb : dimacsBound = 2 ^ 28 := rfl
  have hcv_le := hlen.core_ok.cur_vars_le
  have hale := hlen.core_ok.arena_len_le
  have hwb := hlen.scratch_ok.walk_best_len
  have hwv := hlen.scratch_ok.walk_vals_len
  have hph := hlen.scratch_ok.phases_len
  have hws := hlen.scratch_ok.wsort_len
  have hsbl := hlen.scratch_ok.scratch_buf_len
  dsimp only [Func.wp, full_walk_fid_body]
  c0_hsteps_nogrp
  · exact fidWalk_close_Q hQ rfl hlen (Nat.le_refl _) ⟨rfl, rfl⟩ hm
  · exact fidWalk_close_Q hQ rfl hlen (Nat.le_refl _) ⟨rfl, rfl⟩ hm
  · exact fidWalk_close_Q hQ rfl hlen (Nat.le_refl _) ⟨rfl, rfl⟩ hm
  have hcv_ne0 : ¬BitVec.ofNat 64 s.core.cur_vars = 0 := by assumption
  have hcv_pos : 0 < s.core.cur_vars :=
    Nat.pos_of_ne_zero (fun h0 => hcv_ne0 (by rw [h0]; rfl))
  have hscr_64 : 64 ≤ c.scratch_cap := by
    rw [show c.scratch_cap % 2 ^ 64 = c.scratch_cap from Nat.mod_eq_of_lt (by omega),
      show BitVec.toNat 64 = 64 from rfl] at hc
    omega
  c0_hsteps_nogrp
  -- call full_walk_init_vals_m7
  refine m7InitVals_call hInitVals rfl hlen hm fun s1 m1 hcore1 hlen1 hpres1 hm1 => ?_
  c0_hsteps_nogrp
  -- call full_walk_collect_m7
  refine m7Collect_call hCollect rfl hlen1 hm1 fun rcol s2 m2 hcore2 hlen2 hpres2 hm2 => ?_
  have hcore20 : s2.core = s.core := hcore2.trans hcore1
  have hpres20 : FullExtScratchPres s s2 :=
    ⟨hpres2.1.trans hpres1.1, hpres2.2.trans hpres1.2⟩
  c0_hsteps_nogrp
  -- Join J26: increment walk_cnt_stat and return
  refine wp_join_group (ts := [])
    (fun _ mE => ∃ sE : FullState, sE.core = s.core ∧ sE.LengthsOk c ∧
      FullExtScratchPres s sE ∧ (FullMem c sE ⋆ R) mE)
    (fun _ ⟨⟩ mE ⟨sE, hcoreE, hlenE, hpresE, _hmE⟩ => by
      c0_hsteps
      let sE' : FullState := { sE with scratch :=
        { sE.scratch with walk_cnt_stat := sE.scratch.walk_cnt_stat + 1#64 } }
      have hlenE' : sE'.LengthsOk c := ⟨hlenE.core_ok, { hlenE.scratch_ok with }⟩
      exact fidWalk_close_Q hQ (by simp [sE', hcoreE]) hlenE' (Nat.le_refl _) hpresE
        (by assumption))
    (fun J26 hJ26 => by
      c0_hsplit
      · c0_hsteps; exact hJ26 () m2 ⟨s2, hcore20, hlen2, hpres20, hm2⟩
      have hncl_ne := hc; clear hc
      c0_hsplit
      · c0_hsteps; exact hJ26 () m2 ⟨s2, hcore20, hlen2, hpres20, hm2⟩
      clear hc
      c0_hsplit
      · c0_hsteps; exact hJ26 () m2 ⟨s2, hcore20, hlen2, hpres20, hm2⟩
      have hcap_le := hc; clear hc
      let ncl := rcol >>> 32#64
      have hncl_lt : ncl.toNat < 2 ^ 32 := fidWalk_rshift32_lt
      have hncl_pos : 0 < ncl.toNat :=
        Nat.pos_of_ne_zero (fun h0 => hncl_ne (BitVec.eq_of_toNat_eq h0))
      have hcap5 : 32 + 5 * ncl.toNat ≤ c.scratch_cap := by
        have hsc_mod : c.scratch_cap % 2 ^ 64 = c.scratch_cap := by
          have := c.hscr; unfold dimacsBound at this; omega
        have hmod : (32 + 5 * ncl.toNat) % 2 ^ 64 = 32 + 5 * ncl.toNat :=
          Nat.mod_eq_of_lt (by have := hncl_lt; omega)
        change ¬ c.scratch_cap % 2 ^ 64 < (32 + 5 * ncl.toNat) % 2 ^ 64 at hcap_le
        rw [hsc_mod, hmod] at hcap_le
        omega
      have hncl_le : ncl.toNat ≤ c.scratch_cap := by omega
      c0_hsteps_nogrp
      refine step7CbInv_call hCbInv rfl hlen2 hm2 fun cb_inv m3 _ _ hm3 => ?_
      c0_hsteps_nogrp
      refine m7InitTable_call hInitTable rfl hlen2 hm3 fun s3 m4 hcore3 hlen3 hpres3 hm4 => ?_
      have hcore30 : s3.core = s.core := hcore3.trans hcore20
      have hpres30 : FullExtScratchPres s s3 :=
        ⟨hpres3.1.trans hpres20.1, hpres3.2.trans hpres20.2⟩
      c0_hsteps_nogrp
      refine m7BuildOcc_call hBuildOcc rfl hlen3 hm4 fun ru s4 m5 hcore4 hlen4 hpres4 hru hm5 => ?_
      have hcore40 : s4.core = s.core := hcore4.trans hcore30
      have hpres40 : FullExtScratchPres s s4 :=
        ⟨hpres4.1.trans hpres30.1, hpres4.2.trans hpres30.2⟩
      c0_hsteps_nogrp
      -- effort arg: (ncl < 4096ULL) ? 4096ULL : ncl
      refine wp_join_group (ts := [i64]) (fun _ mE => (FullMem c s4 ⋆ R) mE)
        (fun _ ⟨eff_arg, ⟨⟩⟩ mE hmE => by
          c0_hsteps_nogrp
          refine m7Effort_call hEffort rfl hlen4 hmE fun eff_ticks m6 _ _ hm6 => ?_
          c0_hsteps_nogrp
          have hwcap := fidWalk_bv64_shr2_add1_le hcv_le (by omega)
            (by have := c.hmaxv; unfold dimacsBound at this; omega)
          have h2cv : (BitVec.ofNat 64 s.core.cur_vars <<<
              BitVec.signExtend 64 1#32).toNat = 2 * s.core.cur_vars := by
            rw [fidWalk_bv64_shl1 (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega),
              BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          have hbase : (32#64 + 4#64 * ncl).toNat = 32 + 4 * ncl.toNat := by
            rw [BitVec.toNat_add, BitVec.toNat_mul,
              show (32#64 : BitVec 64).toNat = 32 from rfl,
              show (4#64 : BitVec 64).toNat = 4 from rfl,
              Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
          -- J53_exit
          refine wp_join_group (ts := [i64, i64, i64, i64, Ty.bool, i64, i64])
            (fun _ mX => ∃ sX fuelX, sX.core = { s.core with fuel := fuelX } ∧
              fuelX.toNat ≤ s.core.fuel.toNat ∧ sX.LengthsOk c ∧
              FullExtScratchPres s sX ∧ (FullMem c sX ⋆ R) mX)
            (fun _ ⟨_, _, buX, _, flX, _, _, ⟨⟩⟩ mX
                ⟨sX, fuelX, hcoreX, hfuelX, hlenX, hpresX, hmX⟩ => by
              c0_hsteps_nogrp
              refine wp_join_group (ts := [])
                (fun _ mZ => ∃ sZ, sZ.core = { s.core with fuel := fuelX } ∧
                  sZ.LengthsOk c ∧ FullExtScratchPres s sZ ∧ (FullMem c sZ ⋆ R) mZ)
                (fun _ ⟨⟩ mZ ⟨sZ, hcoreZ, hlenZ, hpresZ, hmZ⟩ => by
                  c0_hsteps
                  let sZ' : FullState := { sZ with scratch :=
                    { sZ.scratch with walk_cnt_stat := sZ.scratch.walk_cnt_stat + 1#64 } }
                  have hlenZ' : sZ'.LengthsOk c := ⟨hlenZ.core_ok, { hlenZ.scratch_ok with }⟩
                  exact fidWalk_close_Q hQ (by simp [sZ', hcoreZ]) hlenZ' hfuelX
                    hpresZ (by assumption))
                (fun _ hJsave => by
                  c0_hsplit
                  · c0_hsteps_nogrp
                    refine m7SaveMin_call hSaveMin rfl hlenX hmX
                      fun sY mY hcoreY hlenY hpresY hmY => ?_
                    c0_hsteps
                    exact hJsave () mY ⟨sY, hcoreY.trans hcoreX, hlenY,
                      ⟨hpresY.1.trans hpresX.1, hpresY.2.trans hpresX.2⟩, hmY⟩
                  · c0_hsteps
                    exact hJsave () mX ⟨sX, hcoreX, hlenX, hpresX, hmX⟩))
            (fun J53X hJ53X => by
              refine wp_loop_group (ts := [i64, i64, i64, i64, Ty.bool, i64, i64])
                (fun fn _ mL => ∃ sL fuelL, sL.core = { s.core with fuel := fuelL } ∧
                  fuelL.toNat = fn ∧ fuelL.toNat ≤ s.core.fuel.toNat ∧ sL.LengthsOk c ∧
                  FullExtScratchPres s sL ∧ (FullMem c sL ⋆ R) mL) ?_ ?_
              · intro J53 fn ⟨uc, ml, bc, bu, fl, flp, tks, ⟨⟩⟩ mL hJ53
                  ⟨sL, fuelL, hcoreL, hfnL, hfuelL, hlenL, hpresL, hmL⟩
                have hcoreL_cv : sL.core.cur_vars = s.core.cur_vars := by rw [hcoreL]
                have hcoreL_fl : sL.core.fuel = fuelL := by rw [hcoreL]
                c0_hsplit
                · have huc_pos : 0 < uc.toNat := by simpa using hc
                  c0_hsplit
                  · have huc_le : uc.toNat ≤ ncl.toNat := hc
                    c0_hsplit
                    · c0_hsplit
                      · c0_hsplit
                        · have hf_pos : 0 < fuelL.toNat := by simpa [hcoreL_fl] using hc
                          have hfn_sub : (fuelL - 1#64).toNat = fn - 1 := by
                            rw [fidWalk_bv64_sub1 hf_pos, hfnL]
                          have hlt_n : fn - 1 < fn := by omega
                          have huc_ne : uc ≠ 0#64 := fun h0 => by
                            rw [h0] at huc_pos; simp at huc_pos
                          c0_hsteps_nogrp
                          let sL1 : FullState :=
                            { sL with core := { sL.core with fuel := fuelL - 1#64 } }
                          have hcoreL1 : sL1.core = { s.core with fuel := fuelL - 1#64 } := by
                            simp only [sL1, hcoreL]
                          have hfuelL1 : (fuelL - 1#64).toNat ≤ s.core.fuel.toNat := by omega
                          have hlenL1 : sL1.LengthsOk c :=
                            ⟨fidWalk_coreLengths_with_fuel hlenL.core_ok, hlenL.scratch_ok⟩
                          have hmL1 : (FullMem c sL1 ⋆ R) m := by
                            rw [hcoreL_fl] at hm; exact hm
                          refine fidRngNext_call hRng rfl hlenL1 hmL1
                            fun rng_r sLr mLr hcoreLr hlenLr hpresLr hmLr => ?_
                          have hcoreLr1 : sLr.core = { s.core with fuel := fuelL - 1#64 } :=
                            hcoreLr.trans hcoreL1
                          have hpresLr0 : FullExtScratchPres s sLr :=
                            ⟨hpresLr.1.trans hpresL.1, hpresLr.2.trans hpresL.2⟩
                          have hurem_lt : (rng_r % uc).toNat < uc.toNat := by
                            rw [BitVec.toNat_umod]; exact Nat.mod_lt _ huc_pos
                          have hslot_sb : (32#64 + 4#64 * (rcol >>> 32#64) + rng_r % uc).toNat <
                              sLr.scratch.scratch_buf.length := by
                            rw [hlenLr.scratch_ok.scratch_buf_len, BitVec.toNat_add,
                              show (32#64 + 4#64 * (rcol >>> 32#64)).toNat = 32 + 4 * ncl.toNat
                                from hbase,
                              Nat.mod_eq_of_lt (by omega)]
                            omega
                          c0_hsteps_nogrp
                          · exact hJ53X _ mLr
                              ⟨sLr, fuelL - 1#64, hcoreLr1, hfuelL1, hlenLr, hpresLr0, hmLr⟩
                          · refine m7Pick_call hPick rfl hlenLr hmLr
                              fun rpick sL2 mL2 hcoreL2 hlenL2 hpresL2 hmL2 => ?_
                            have hcoreL2' : sL2.core = { s.core with fuel := fuelL - 1#64 } :=
                              hcoreL2.trans hcoreLr1
                            have hpresL20 : FullExtScratchPres s sL2 :=
                              ⟨hpresL2.1.trans hpresLr0.1, hpresL2.2.trans hpresLr0.2⟩
                            c0_hsteps_nogrp
                            c0_hsplit
                            · c0_hsteps
                              exact hJ53 (fn - 1) _ _ hlt_n
                                ⟨sL2, fuelL - 1#64, hcoreL2', hfn_sub, hfuelL1, hlenL2,
                                  hpresL20, hmL2⟩
                            · c0_hsteps_nogrp
                              refine m7Flip_call hFlip rfl hlenL2 hmL2
                                fun rflip sL3 mL3 hcoreL3 hlenL3 hpresL3 _ hmL3 => ?_
                              have hcoreL3' : sL3.core = { s.core with fuel := fuelL - 1#64 } :=
                                hcoreL3.trans hcoreL2'
                              have hpresL30 : FullExtScratchPres s sL3 :=
                                ⟨hpresL3.1.trans hpresL20.1, hpresL3.2.trans hpresL20.2⟩
                              c0_hsteps_nogrp
                              refine wp_join_group (ts := [i64, i64, Ty.bool])
                                (fun _ mFin => ∃ sFin,
                                  sFin.core = { s.core with fuel := fuelL - 1#64 } ∧
                                  sFin.LengthsOk c ∧ FullExtScratchPres s sFin ∧
                                  (FullMem c sFin ⋆ R) mFin)
                                (fun _ ⟨mhF, bcF, flF, ⟨⟩⟩ mFin
                                    ⟨sFin, hcoreFin, hlenFin, hpresFin, hmFin⟩ => by
                                  c0_hsteps_nogrp
                                  refine wp_join_group (ts := [i64, i64, i64, Ty.bool])
                                    (fun _ mD => ∃ sD,
                                      sD.core = { s.core with fuel := fuelL - 1#64 } ∧
                                      sD.LengthsOk c ∧ FullExtScratchPres s sD ∧
                                      (FullMem c sD ⋆ R) mD)
                                    (fun _ ⟨buD, mhD, bcD, flD, ⟨⟩⟩ mD
                                        ⟨sD, hcoreD, hlenD, hpresD, hmD⟩ => by
                                      c0_hsteps
                                      exact hJ53 (fn - 1) _ _ hlt_n
                                        ⟨sD, fuelL - 1#64, hcoreD, hfn_sub, hfuelL1, hlenD,
                                          hpresD, hmD⟩)
                                    (fun J_done hJ_done => by
                                      c0_hsplit
                                      · refine wp_join_group (ts := [i64, i64, Ty.bool])
                                          (fun _ m14 => ∃ s14,
                                            s14.core = { s.core with fuel := fuelL - 1#64 } ∧
                                            s14.LengthsOk c ∧ FullExtScratchPres s s14 ∧
                                            (FullMem c s14 ⋆ R) m14)
                                          (fun _ _ m14
                                              ⟨s14, hcore14, hlen14, hpres14, hm14⟩ => by
                                            c0_hsteps
                                            exact hJ_done _ m14
                                              ⟨s14, hcore14, hlen14, hpres14, hm14⟩)
                                          (fun J14 hJ14 => by
                                            c0_hsplit
                                            · c0_hsteps
                                              exact hJ14 _ mFin
                                                ⟨sFin, hcoreFin, hlenFin, hpresFin, hmFin⟩
                                            · refine wp_loop_group (ts := [i64])
                                                (fun nb ⟨idx, ⟨⟩⟩ mB => ∃ sB,
                                                  idx.toNat ≤ s.core.cur_vars ∧
                                                  nb = s.core.cur_vars - idx.toNat ∧
                                                  sB.core = { s.core with fuel := fuelL - 1#64 } ∧
                                                  sB.LengthsOk c ∧ FullExtScratchPres s sB ∧
                                                  (FullMem c sB ⋆ R) mB)
                                                ?_ ?_
                                              · intro J97 nb ⟨idx, ⟨⟩⟩ mB hJ97
                                                  ⟨sB, hidx, hnb, hcoreB, hlenB, hpresB, hmB⟩
                                                have hcvB : sB.core.cur_vars = s.core.cur_vars := by
                                                  rw [hcoreB]
                                                c0_hsplit
                                                · have hidx_lt : idx.toNat < s.core.cur_vars := by
                                                    rw [Nat.mod_eq_of_lt (by omega)] at hc
                                                    exact hc
                                                  have h2idx :
                                                      (idx <<< (1 : BitVec 64)).toNat <
                                                      sB.scratch.walk_vals.length := by
                                                    change
                                                      (idx <<< BitVec.signExtend 64 1#32).toNat <
                                                      sB.scratch.walk_vals.length
                                                    rw [fidWalk_bv64_shl1 (by omega),
                                                      hlenB.scratch_ok.walk_vals_len]
                                                    omega
                                                  have hidx_wb :
                                                      idx.toNat < sB.scratch.walk_best.length := by
                                                    rw [hlenB.scratch_ok.walk_best_len]
                                                    omega
                                                  have hidx1 : (idx + (1 : BitVec 64)).toNat =
                                                      idx.toNat + 1 := by
                                                    simpa using
                                                      fidWalk_bv64_add1_lt hidx_lt (by omega)
                                                  c0_hsteps
                                                  let wb' := sB.scratch.walk_best.set idx.toNat
                                                    sB.scratch.walk_vals[
                                                      (idx <<< (1 : BitVec 64)).toNat]
                                                  let sB' : FullState := FullState.mk sB.core
                                                    { sB.scratch with walk_best := wb' }
                                                  have hlenB' : sB'.LengthsOk c :=
                                                    ⟨hlenB.core_ok, fidWalk_scratchLengths_with_wv
                                                      hlenB.scratch_ok
                                                      (by simp [wb',
                                                        hlenB.scratch_ok.walk_best_len])⟩
                                                  exact hJ97 (s.core.cur_vars - (idx.toNat + 1)) _ _
                                                    (by omega)
                                                    ⟨sB', by rw [hidx1]; omega, by rw [hidx1],
                                                      hcoreB, hlenB', hpresB, ‹_›⟩
                                                · c0_hsteps
                                                  exact hJ14 _ mB
                                                    ⟨sB, hcoreB, hlenB, hpresB, hmB⟩
                                              · intro J97 hJ97
                                                c0_hsteps
                                                exact hJ97 s.core.cur_vars _ mFin
                                                  ⟨sFin, Nat.zero_le _, by rfl, hcoreFin, hlenFin,
                                                    hpresFin, hmFin⟩)
                                      · c0_hsteps
                                        exact hJ_done _ mFin
                                          ⟨sFin, hcoreFin, hlenFin, hpresFin, hmFin⟩))
                                (fun J_fin hJ_fin => by
                                  c0_hsplit
                                  · clear hc
                                    refine wp_join_group (ts := [i64, i64, Ty.bool])
                                      (fun _ m93 => ∃ s93,
                                        s93.core = { s.core with fuel := fuelL - 1#64 } ∧
                                        s93.LengthsOk c ∧ FullExtScratchPres s s93 ∧
                                        (FullMem c s93 ⋆ R) m93)
                                      (fun _ ⟨ml0, bc0, fl0, ⟨⟩⟩ m93
                                          ⟨s93, hcore93, hlen93, hpres93, hm93⟩ => by
                                        refine wp_join_group (ts := [i64])
                                          (fun _ m96 => ∃ s96,
                                            s96.core = { s.core with fuel := fuelL - 1#64 } ∧
                                            s96.LengthsOk c ∧ FullExtScratchPres s s96 ∧
                                            (FullMem c s96 ⋆ R) m96)
                                          (fun _ ⟨ml1, ⟨⟩⟩ m96
                                              ⟨s96, hcore96, hlen96, hpres96, hm96⟩ => by
                                            c0_hsteps
                                            exact hJ_fin _ m96
                                              ⟨s96, hcore96, hlen96, hpres96, hm96⟩)
                                          (fun J96 hJ96 => by
                                            c0_hsplit
                                            · clear hc
                                              c0_hsplit
                                              · have hml_ws :
                                                    ml0.toNat < s93.scratch.wsort.length := by
                                                  rw [hlen93.scratch_ok.wsort_len]
                                                  have hlt : ml0.toNat < (BitVec.ofNat 64
                                                      s.core.cur_vars >>>
                                                      BitVec.signExtend 64 2#32 + 1#64).toNat := hc
                                                  omega
                                                c0_hsteps
                                                let ws96 := s93.scratch.wsort.set ml0.toNat
                                                  ((BitVec.setWidth 32
                                                    (rpick &&& 4294967295#64)) >>> 1#32)
                                                let s96 := FullState.mk s93.core
                                                  { s93.scratch with wsort := ws96 }
                                                have hws96 := hlen93.scratch_ok.wsort_len
                                                have hlen96 : s96.LengthsOk c :=
                                                  ⟨hlen93.core_ok, fidWalk_scratchLengths_with_wsort
                                                    hlen93.scratch_ok (by simp [ws96, hws96])⟩
                                                exact hJ96 _ _ ⟨s96, hcore93, hlen96, hpres93, ‹_›⟩
                                              · c0_hsteps; exact hJ96 _ m93
                                                  ⟨s93, hcore93, hlen93, hpres93, hm93⟩
                                            · c0_hsteps; exact hJ96 _ m93
                                                ⟨s93, hcore93, hlen93, hpres93, hm93⟩))
                                      (fun J93 hJ93 => by
                                        c0_hsplit
                                        · refine wp_join_group (ts := [i64, i64, Ty.bool])
                                            (fun _ mB => ∃ sB,
                                              sB.core = { s.core with fuel := fuelL - 1#64 } ∧
                                              sB.LengthsOk c ∧ FullExtScratchPres s sB ∧
                                              (FullMem c sB ⋆ R) mB)
                                            (fun _ _ mB ⟨sB, hcoreB, hlenB, hpresB, hmB⟩ => by
                                              c0_hsteps
                                              exact hJ93 _ mB ⟨sB, hcoreB, hlenB, hpresB, hmB⟩)
                                            (fun J93b hJ93b => by
                                              c0_hsplit
                                              · have hbc_pos : 0 < bc.toNat := by simpa using hc
                                                clear hc
                                                c0_hsplit
                                                · have hbc_le : bc.toNat ≤ ml.toNat := hc
                                                  clear hc
                                                  c0_hsplit
                                                  · have hml_le : ml.toNat ≤ (BitVec.ofNat 64
                                                        s.core.cur_vars >>>
                                                        BitVec.signExtend 64 2#32 + 1#64).toNat :=
                                                      hc
                                                    have hml_wsort : ml.toNat ≤ 2 * c.max_vars := by
                                                      omega
                                                    refine wp_loop_group (ts := [i64])
                                                      (fun nk ⟨k, ⟨⟩⟩ mK => ∃ sK,
                                                        k.toNat ≤ bc.toNat ∧
                                                        nk = bc.toNat - k.toNat ∧
                                                        sK.core =
                                                          { s.core with fuel := fuelL - 1#64 } ∧
                                                        sK.LengthsOk c ∧
                                                        FullExtScratchPres s sK ∧
                                                        (FullMem c sK ⋆ R) mK)
                                                      ?_ ?_
                                                    · intro J97 nk ⟨k, ⟨⟩⟩ mK hJ97
                                                        ⟨sK, hk_le, hnk, hcoreK, hlenK, hpresK, hmK⟩
                                                      have hcvK :
                                                          sK.core.cur_vars = s.core.cur_vars := by
                                                        rw [hcoreK]
                                                      c0_hsplit
                                                      · have hk_lt : k.toNat < bc.toNat := hc
                                                        clear hc
                                                        have hk_ws :
                                                            k.toNat < sK.scratch.wsort.length := by
                                                          rw [hlenK.scratch_ok.wsort_len]; omega
                                                        have hk1 : (k + (1 : BitVec 64)).toNat =
                                                            k.toNat + 1 := by
                                                          simpa using
                                                            fidWalk_bv64_add1_lt hk_lt (by omega)
                                                        c0_hsteps_nogrp
                                                        refine wp_join_group (ts := [])
                                                          (fun _ m99 => ∃ s99,
                                                            s99.core = { s.core with
                                                              fuel := fuelL - 1#64 } ∧
                                                            s99.LengthsOk c ∧
                                                            FullExtScratchPres s s99 ∧
                                                            (FullMem c s99 ⋆ R) m99)
                                                          (fun _ ⟨⟩ m99
                                                              ⟨s99, hcore99, hlen99, hpres99,
                                                                hm99⟩ => by
                                                            c0_hsteps
                                                            exact hJ97 (bc.toNat - (k.toNat + 1)) _
                                                              _ (by omega)
                                                              ⟨s99, by rw [hk1]; omega,
                                                                by rw [hk1], hcore99, hlen99,
                                                                hpres99, hm99⟩)
                                                          (fun J99 hJ99 => by
                                                            c0_hsplit
                                                            · have hw_lt_cond := hc; clear hc
                                                              let w32 := sK.scratch.wsort[k.toNat]
                                                              have hw_lt : w32.toNat <
                                                                  sK.scratch.walk_best.length := by
                                                                rw [hlenK.scratch_ok.walk_best_len]
                                                                have h0 := hw_lt_cond
                                                                rw [Nat.mod_eq_of_lt (by omega)]
                                                                  at h0
                                                                dsimp only [w32]; omega
                                                              have hw64_lt :
                                                                  (w32.setWidth 64).toNat <
                                                                  sK.scratch.walk_best.length := by
                                                                rw [BitVec.toNat_setWidth,
                                                                  Nat.mod_eq_of_lt (by
                                                                    have := w32.isLt; omega)]
                                                                exact hw_lt
                                                              c0_hsteps_nogrp
                                                              refine wp_join_group (ts := [i32])
                                                                (fun _ mP => mP = mK) ?_ ?_
                                                              · intro _ ⟨phP, ⟨⟩⟩ mP hmEq
                                                                subst hmEq
                                                                c0_hsteps!
                                                                let wb1 :=
                                                                  sK.scratch.walk_best.set
                                                                    (w32.setWidth 64).toNat
                                                                    (phP.setWidth 8)
                                                                let sP := FullState.mk sK.core
                                                                  { sK.scratch with
                                                                    walk_best := wb1 }
                                                                have hwbP :=
                                                                  hlenK.scratch_ok.walk_best_len
                                                                have hlenP : sP.LengthsOk c :=
                                                                  ⟨hlenK.core_ok,
                                                                    fidWalk_scratchLengths_with_wv
                                                                      hlenK.scratch_ok
                                                                      (by simp [wb1, hwbP])⟩
                                                                exact hJ99 () _
                                                                  ⟨sP, hcoreK, hlenP, hpresK, ‹_›⟩
                                                              · intro J106 hJ106
                                                                c0_hsteps <;> exact hJ106 _ _ rfl
                                                            · c0_hsteps
                                                              exact hJ99 () mK
                                                                ⟨sK, hcoreK, hlenK, hpresK, hmK⟩)
                                                      · c0_hsteps_nogrp
                                                        refine wp_loop_group (ts := [i64])
                                                          (fun nj ⟨j, ⟨⟩⟩ mJ => ∃ sJ,
                                                            j.toNat ≤ (ml - bc).toNat ∧
                                                            nj = (ml - bc).toNat - j.toNat ∧
                                                            sJ.core =
                                                              { s.core with fuel := fuelL - 1#64 } ∧
                                                            sJ.LengthsOk c ∧
                                                            FullExtScratchPres s sJ ∧
                                                            (FullMem c sJ ⋆ R) mJ)
                                                          ?_ ?_
                                                        · intro J100 nj ⟨j, ⟨⟩⟩ mJ hJ100
                                                            ⟨sJ, hj_le, hnj, hcoreJ, hlenJ, hpresJ,
                                                              hmJ⟩
                                                          c0_hsplit
                                                          · have hj_lt :
                                                                j.toNat < (ml - bc).toNat :=
                                                              hc
                                                            have hsub_eq : (ml - bc).toNat =
                                                                ml.toNat - bc.toNat := by
                                                              rw [BitVec.toNat_sub]
                                                              have := bc.isLt; have := ml.isLt
                                                              omega
                                                            have hsrc : (bc + j).toNat <
                                                                sJ.scratch.wsort.length := by
                                                              rw [hlenJ.scratch_ok.wsort_len,
                                                                BitVec.toNat_add,
                                                                Nat.mod_eq_of_lt (by omega)]
                                                              omega
                                                            have hdst : j.toNat <
                                                                sJ.scratch.wsort.length := by
                                                              rw [hlenJ.scratch_ok.wsort_len]; omega
                                                            have hj1 : (j + (1 : BitVec 64)).toNat =
                                                                j.toNat + 1 := by
                                                              simpa using fidWalk_bv64_add1_lt
                                                                hj_lt (by omega)
                                                            c0_hsteps
                                                            let wsJ := sJ.scratch.wsort.set j.toNat
                                                              sJ.scratch.wsort[(bc + j).toNat]
                                                            let sJ' := FullState.mk sJ.core
                                                              { sJ.scratch with wsort := wsJ }
                                                            have hwsJ := hlenJ.scratch_ok.wsort_len
                                                            have hlenJ' : sJ'.LengthsOk c :=
                                                              ⟨hlenJ.core_ok,
                                                                fidWalk_scratchLengths_with_wsort
                                                                  hlenJ.scratch_ok
                                                                  (by simp [wsJ, hwsJ])⟩
                                                            exact hJ100
                                                              ((ml - bc).toNat - (j.toNat + 1)) _ _
                                                              (by omega)
                                                              ⟨sJ', by rw [hj1]; omega,
                                                                by rw [hj1], hcoreJ, hlenJ',
                                                                hpresJ, ‹_›⟩
                                                          · c0_hsteps
                                                            exact hJ93b _ mJ
                                                              ⟨sJ, hcoreJ, hlenJ, hpresJ, hmJ⟩
                                                        · intro J100 hJ100
                                                          c0_hsteps
                                                          exact hJ100 (ml - bc).toNat _ mK
                                                            ⟨sK, Nat.zero_le _, by rfl, hcoreK,
                                                              hlenK, hpresK, hmK⟩
                                                    · intro J97 hJ97
                                                      c0_hsteps
                                                      exact hJ97 bc.toNat _ mL3
                                                        ⟨sL3, Nat.zero_le _, by rfl, hcoreL3',
                                                          hlenL3, hpresL30, hmL3⟩
                                                  · c0_hsteps; exact hJ93b _ mL3
                                                      ⟨sL3, hcoreL3', hlenL3, hpresL30, hmL3⟩
                                                · c0_hsteps; exact hJ93b _ mL3
                                                    ⟨sL3, hcoreL3', hlenL3, hpresL30, hmL3⟩
                                              · c0_hsteps; exact hJ93b _ mL3
                                                  ⟨sL3, hcoreL3', hlenL3, hpresL30, hmL3⟩)
                                        · c0_hsteps
                                          exact hJ93 _ mL3
                                            ⟨sL3, hcoreL3', hlenL3, hpresL30, hmL3⟩)
                                  · c0_hsteps
                                    exact hJ_fin _ mL3 ⟨sL3, hcoreL3', hlenL3, hpresL30, hmL3⟩)
                        · c0_hsteps; exact hJ53X _ mL
                            ⟨sL, fuelL, hcoreL, hfuelL, hlenL, hpresL, hmL⟩
                      · c0_hsteps; exact hJ53X _ mL
                          ⟨sL, fuelL, hcoreL, hfuelL, hlenL, hpresL, hmL⟩
                    · c0_hsteps; exact hJ53X _ mL
                        ⟨sL, fuelL, hcoreL, hfuelL, hlenL, hpresL, hmL⟩
                  · c0_hsteps; exact hJ53X _ mL
                      ⟨sL, fuelL, hcoreL, hfuelL, hlenL, hpresL, hmL⟩
                · c0_hsteps; exact hJ53X _ mL
                    ⟨sL, fuelL, hcoreL, hfuelL, hlenL, hpresL, hmL⟩
              · intro J53 hJ53
                c0_hsteps
                exact hJ53 s.core.fuel.toNat _ m6
                  ⟨s4, s.core.fuel, hcore40, rfl, Nat.le_refl _, hlen4, hpres40, hm6⟩))
        (fun J35 hJ35 => by
          c0_hsplit
          · c0_hsteps; exact hJ35 _ _ hm5
          · c0_hsteps; exact hJ35 _ _ hm5))

end WalkProof

end LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep7

end
