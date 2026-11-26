/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep7
public import LeanQbe.T.Examples.Kissat.FullM7FidelityCore
public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Examples.Kissat.FullM7WalkProof0
public import LeanQbe.T.Examples.Kissat.PatchModule
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

section Step7Meta

open LeanQbe.T.Examples.Kissat.PatchModule

@[expose] def sigsAtSorted7 (i : Nat) : List Nat → List Fn → List SigEntry
  | [], _ => []
  | _, [] => []
  | k :: ks, f :: fs =>
    if i == k then f.sig :: sigsAtSorted7 (i + 1) ks fs
    else sigsAtSorted7 (i + 1) (k :: ks) fs

theorem sigsAtSorted7_getElem? :
    ∀ (fs : List Fn) (i : Nat) (pairs : List (Nat × SigEntry)),
      (pairs.map Prod.fst).Pairwise (· < ·) →
      (∀ q ∈ pairs, i ≤ q.1) →
      sigsAtSorted7 i (pairs.map Prod.fst) fs = pairs.map Prod.snd →
      ∀ p ∈ pairs, fs[p.1 - i]?.map Fn.sig = some p.2
  | [], _, [], _, _, _, _, hp => nomatch hp
  | [], _, _ :: _, _, _, h, _, _ => by simp [sigsAtSorted7] at h
  | _ :: _, _, [], _, _, _, _, hp => nomatch hp
  | f :: fs, i, hd :: tl, hsort, hall, h, p, hp => by
    simp only [sigsAtSorted7, List.map_cons] at h
    simp only [List.map_cons, List.pairwise_cons, List.mem_map] at hsort
    have hi_hd : i ≤ hd.1 := hall hd List.mem_cons_self
    by_cases heq : i = hd.1
    · simp only [heq, beq_self_eq_true, ↓reduceIte, List.cons.injEq] at h
      rcases List.mem_cons.mp hp with rfl | htl
      · simp [heq, h.1]
      · have hlt : hd.1 < p.1 := hsort.1 p.1 ⟨p, htl, rfl⟩
        have h' : sigsAtSorted7 (i + 1) (tl.map Prod.fst) fs = tl.map Prod.snd := by
          rw [heq]; exact h.2
        have ih := sigsAtSorted7_getElem? fs (i + 1) tl hsort.2
          (fun q hq => by have := hsort.1 q.1 ⟨q, hq, rfl⟩; omega) h' p htl
        have hsub : p.1 - i = (p.1 - (i + 1)) + 1 := by omega
        rw [hsub]; simpa using ih
    · have hne : (i == hd.1) = false := beq_false_of_ne heq
      simp only [hne, Bool.false_eq_true, ↓reduceIte] at h
      have hall' : ∀ q ∈ hd :: tl, i + 1 ≤ q.1 := fun q hq => by
        rcases List.mem_cons.mp hq with rfl | htl
        · omega
        · have := hsort.1 q.1 ⟨q, htl, rfl⟩; omega
      have ih := sigsAtSorted7_getElem? fs (i + 1) (hd :: tl)
        (by simpa [List.map_cons, List.pairwise_cons, List.mem_map] using hsort)
        hall' h p hp
      have hp_ge : i + 1 ≤ p.1 := hall' p hp
      have hsub : p.1 - i = (p.1 - (i + 1)) + 1 := by omega
      rw [hsub]; simpa using ih

@[expose] def isSortedLt7 : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: t => a < b && isSortedLt7 (b :: t)

theorem pairwise_lt_of_isSortedLt7 :
    ∀ {xs : List Nat}, isSortedLt7 xs = true → xs.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: t, h => by
    simp only [isSortedLt7, Bool.and_eq_true, decide_eq_true_eq] at h
    have iht := pairwise_lt_of_isSortedLt7 h.2
    refine List.pairwise_cons.mpr ⟨fun z hz => ?_, iht⟩
    rcases List.mem_cons.mp hz with rfl | hzt
    · exact h.1
    · exact Nat.lt_trans h.1 ((List.pairwise_cons.mp iht).1 z hzt)

/-- Sorted `(slot, sig)` table covering all `11` Step-9 replacements, `full_zero_tables1`
(`before` anchor), and all transitive callees in `fidStep7Module.fns`. -/
@[expose] def fidStep7_step9_sigPairs : List (Nat × SigEntry) :=
  [ (8, ("full_isqrt", [i64], [i64]))
  , (11, ("full_arena_next", [i64, i32], [i32]))
  , (12, ("full_alloc_cl", [i64, i32, i32, .bool], [i64]))
  , (18, ("full_wstack_defrag", [i64], []))
  , (19, ("full_watch_push", [i64, i32, i32, i32, i32], [.bool]))
  , (32, ("full_log10_q16_m7", [i64], [i64]))
  , (33, ("full_scale_delta_m5", [i64, i64], [i64]))
  , (40, ("full_backtrack", [i64, i64], []))
  , (42, ("full_zero_tables1", [i64], []))
  , (62, ("m6_hdr_recompute_tiers", [i64], []))
  , (67, ("m6_hdr_delaying", [i64, i64], [.bool]))
  , (68, ("m6_hdr_bump_delay", [i64, i64], []))
  , (69, ("m6_hdr_reduce_delay", [i64, i64], []))
  , (71, ("m6_hdr_get_watermark", [i64, i64], [i64]))
  , (72, ("m6_hdr_set_watermark", [i64, i64, i64], []))
  , (81, ("full_unwatch_large", [i64, i32, i32], []))
  , (84, ("full_prop_flush_del_fid", [i64, i64], [.bool]))
  , (88, ("full_propagate", [i64], [i64]))
  , (93, ("full_sweep_bins_range_m6", [i64, i64], []))
  , (94, ("full_rewatch_range_m6", [i64, i64, i64], [.bool]))
  , (99, ("full_sweep_copy", [i64, i64, i64, i32, .bool], [i64]))
  , (103, ("full_move_red_end_m6", [i64, i64, i64], []))
  , (104, ("full_arena_sweep_m6", [i64], [i64]))
  , (106, ("full_arena_sweep", [i64], [i64]))
  , (107, ("full_mark_reasons", [i64, .bool], []))
  , (108, ("full_flush_trail", [i64], [i64]))
  , (111, ("full_sort_reds", [i64, i64], []))
  , (113, ("full_reduce_m6", [i64, .bool], [i64]))
  , (183, ("full_add_bin", [i64, i32, i32], [i64]))
  , (184, ("full_delete_binary", [i64, i32, i32], []))
  , (227, ("full_vivify_m6_hdr", [i64], [i64]))
  , (235, ("full_backbone_m6", [i64, i64], [i64]))
  , (238, ("full_transitive_m6", [i64, i64], [i64]))
  , (244, ("full_substitute", [i64], [i64]))
  , (245, ("full_enter_dense", [i64], [.bool]))
  , (246, ("full_sort_bin_watches_fid", [i64], []))
  , (247, ("full_rebuild_watches", [i64], [i64]))
  , (263, ("full_cong_extract_binaries", [i64, i64], [i64]))
  , (264, ("full_cong_find_units_equivs", [i64], [i64]))
  , (265, ("full_cong_extract", [i64, i64, i64], [i64]))
  , (271, ("full_cong_worklist", [i64, i64, i64, i64], [i64]))
  , (274, ("full_cong_fwd_subsume", [i64, i64], [i64]))
  , (287, ("full_cong_extract_ite_all_m7", [i64, i32, i32, i64], [i32]))
  , (288, ("full_congruence_dense", [i64, i64], [i64]))
  , (348, ("full_sweep_dense_m6", [i64, i64, i64], [i64]))
  , (420, ("full_init_fresh_var", [i64, i32], []))
  , (425, ("full_bva_steps_cap_fid", [i64], [i32]))
  , (427, ("full_fheap_up_fid", [i64, i64, i64, i32], []))
  , (428, ("full_fheap_down_fid", [i64, i64, i64, i32, i32], []))
  , (429, ("full_bva_count_lit_deg_fid", [i64, i32], [i32]))
  , (430, ("full_bva_connect_clauses_fid", [i64], []))
  , (436, ("full_bva_commit", [i64, i32], [.bool]))
  , (437, ("full_bva_try_lit", [i64, i32, i64], [.bool]))
  , (440, ("full_bva_upd_lit_fid", [i64, i64, i64, i64, i32, i64, i32], [i32]))
  , (441, ("full_factor", [i64, i64], [i64]))
  , (442, ("full_compact_needed", [i64], [.bool]))
  , (443, ("full_compact_flush", [i64], [i64]))
  , (490, ("full_probe_dticks_m6_hdr", [i64, .bool], [i64]))
  , (492, ("full_probe_m6", [i64, .bool], [i64])) ]

@[expose] def fidStep7FnNames : List Sym :=
  [ "kissat_is_ws", "kissat_is_digit", "kissat_skip_ws_comments", "kissat_skip_ws1"
  , "kissat_read_nat", "kissat_parse_header", "kissat_next_lit", "kissat_check_model"
  , "full_isqrt", "full_ilog10", "full_rng_next", "full_arena_next", "full_alloc_cl"
  , "full_wsort_sift", "full_wstack_radix_sort_m6", "full_wstack_defrag_m6"
  , "full_watch_push_slow_m6", "full_watch_push_m6", "full_wstack_defrag", "full_watch_push"
  , "full_heap_up", "full_heap_down", "full_heap_push", "full_heap_pop", "full_rescale_m6"
  , "full_rescale", "full_bump_var", "full_bump_decay", "full_queue_renumber", "full_queue_mtf"
  , "full_tick_rel", "full_log10_q16", "full_log10_q16_m7", "full_scale_delta_m5"
  , "full_ema_update", "full_scale_delta", "full_assign_lvl", "full_assign"
  , "full_save_target_best", "full_backtrack_raw_m5", "full_backtrack", "full_add_clause"
  , "full_zero_tables1", "full_zero_tables2", "full_fixed_bytes", "full_init_ptrs"
  , "full_init_hdr", "full_calc_max_v", "full_calc_ext_cap_m5", "full_calc_scr_cap_m5"
  , "full_init_arenas", "full_init_state_m5", "full_init_state", "full_m6_hdr_sizeof"
  , "full_m6_ext_sizeof", "m6_hdr_init", "m6_hdr_reset", "m6_ext_ensure_init", "m6_hdr_ext_ready"
  , "full_m6_mem_init", "m6_hdr_sync_legacy_tiers", "m6_hdr_recompute_tiers_mode"
  , "m6_hdr_recompute_tiers", "m6_hdr_update_tier_limits", "m6_hdr_record_used"
  , "m6_hdr_get_tier1", "m6_hdr_get_tier2", "m6_hdr_delaying", "m6_hdr_bump_delay"
  , "m6_hdr_reduce_delay", "m6_hdr_reset_delay", "m6_hdr_get_watermark", "m6_hdr_set_watermark"
  , "m6_hdr_add_ticks", "m6_hdr_dr_init", "m6_hdr_dr_update", "m6_hdr_dr_allow", "full_skip_cl"
  , "full_ingest_cl", "full_find_repl", "full_assign_level", "full_unwatch_large"
  , "full_prop_lit_ovf_hot", "full_prop_chrono_hot", "full_prop_flush_del_fid"
  , "full_propagate_ignore_hot", "full_bcp_hot", "full_propagate_ignore", "full_propagate"
  , "full_parse_body_m6", "full_parse_body", "full_recompute_tiers", "full_lit_rank_m6"
  , "full_sweep_bins_range_m6", "full_rewatch_range_m6", "full_rewatch_arena_m6", "full_lit_rank"
  , "full_sweep_bins_m6cf", "full_sweep_bins", "full_sweep_copy", "full_rewatch_arena"
  , "full_move_red_pass2_m6", "full_move_red_end_buf_m6", "full_move_red_end_m6"
  , "full_arena_sweep_m6", "full_mark_reasons_m6", "full_arena_sweep", "full_mark_reasons"
  , "full_flush_trail", "full_red_less", "full_red_sift", "full_sort_reds", "full_reduce"
  , "full_reduce_m6", "full_analyze_lit", "full_analyze_rsn", "full_analyze_rsn_m6_hdr"
  , "full_clear_ana", "full_ana_sift_m6", "full_sort_ana_qs_m6", "full_bump_analyzed_m6_hdr"
  , "full_restore_bump_ana_m6_hdr", "full_ana_failed_lit_m6_hdr", "full_otfs_large"
  , "full_otfs_bin", "full_otfs_subsume", "full_min_mark", "full_tmp_less", "full_sort_tmp_sift"
  , "full_sort_tmp_sift_m7", "full_sort_tmp_heap_m7", "full_sort_tmp", "full_min_lit_dfs_m6"
  , "full_min_lit_m6", "full_shrink_lower_m6", "full_shrink_blk_bool_m6", "full_shrink_blk_m6"
  , "full_min_lit_dfs_m8", "full_shrink_lower_m8", "full_shrink_blk_bool_m8", "full_min_shrink_m6"
  , "full_deduce_1uip_m6", "full_min_shrink", "full_deduce_1uip", "full_deduce_1uip_m6_hdr"
  , "full_det_new_level", "full_one_lit_confl", "full_eager_subsume", "full_learn_clause"
  , "full_bump_sift_m7", "full_bump_sort_stamps_m7", "full_bump_reasons_m7", "full_bump_analyzed"
  , "full_restore_bump_ana_m5", "full_analyze", "full_analyze_core_m6", "full_analyze_m6_hdr"
  , "full_next_dec_var", "m6_hdr_decide", "full_walk_cb_inv_m7", "full_walk_init_table_m7"
  , "full_walk_effort_m7", "full_walk_init_vals_m7", "full_walk_collect_m7"
  , "full_walk_build_occ_m7", "full_walk_break_m7", "full_walk_pick_m7", "full_walk_flip_m7"
  , "full_walk_save_min_m7", "full_walk_m7", "full_warmup_m7", "full_walk_warmup_m7"
  , "full_warmup", "full_walk", "full_rephase", "full_restart_due", "full_restart"
  , "full_extend_push2", "full_extend_push_cl", "full_extend", "full_has_bin"
  , "full_delete_bin_side", "full_add_bin_m6", "full_add_bin", "full_delete_binary"
  , "full_set_inactive", "full_add_unit", "full_lucky_scan", "full_lucky_polar", "full_lucky"
  , "full_hbr_dom", "full_probe_prop_lit", "full_probe_prop", "full_probe_flush_hbr"
  , "full_probe_assume_pair", "full_probe_run", "full_viv_unreason_m6", "full_viv_watch_rank_m6"
  , "full_viv_best_watch_m6", "full_viv_simplify_m6", "full_viv_commit_m6"
  , "full_viv_mark_garb_m6", "full_viv_subsumes_bin_m6", "full_viv_subsumes_cl_m6"
  , "full_viv_deduce_m6", "full_viv_best_implied_m6", "full_viv_reestablish_m6"
  , "full_viv_inst_check_m6", "full_viv_inst_m6", "full_viv_finish_m6", "full_viv_sort_counts_m6"
  , "full_viv_has_l0_m6", "full_viv_l0_simp_m6", "full_viv_reuse_prefix_m6", "full_viv_clause_m6"
  , "full_viv_tier_match_m6", "full_viv_collect_m6", "full_viv_count_m6", "full_viv_keys_m6"
  , "full_viv_sort_sched_m6", "full_viv_clear_tier_m6", "full_vivify_m6", "full_viv_collect_fid"
  , "full_viv_count_fid", "full_viv_sort2_fid", "full_viv_sort_fid", "full_vivify_tier_m6_hdr"
  , "full_vivify_m6_hdr", "full_prioritize_binaries_m6", "full_backbone_sched_m6"
  , "full_backbone_keep_m6", "full_backbone_unwind_m6", "full_backbone_prop_m6"
  , "full_backbone_analyze_m6", "full_backbone_round_m6", "full_backbone_m6", "full_trans_lit_m6"
  , "full_trans_sort_m6", "full_transitive_m6", "full_tarjan_pop_scc", "full_tarjan_scc"
  , "full_subst_elim_vars", "full_subst_rewrite_bins", "full_subst_rewrite_ar", "full_substitute"
  , "full_enter_dense", "full_sort_bin_watches_fid", "full_rebuild_watches", "full_cong_find"
  , "full_cong_merge", "full_cong_mark_trail", "full_cong_unit_fold", "full_cong_equiv_fold"
  , "full_has_ternary", "full_sort_u32", "full_cong_extract_ite", "full_cong_emit_xor"
  , "full_cong_has_clause_k", "full_cong_emit_xor4", "full_cong_extract_xor_k"
  , "full_cong_try_xor_ite", "full_cong_count_bins", "full_cong_eb_match"
  , "full_cong_extract_binaries", "full_cong_find_units_equivs", "full_cong_extract"
  , "full_cong_and_match", "full_cong_xor_match", "full_cong_enq_var", "full_cong_eval_gate"
  , "full_cong_work_step", "full_cong_worklist", "full_cong_sift_pairs_fid"
  , "full_cong_sort_pairs_fid", "full_cong_fwd_subsume", "full_cong_ht_hash_ent_m7"
  , "full_cong_ht_init_m7", "full_cong_ht_grow_m7", "full_cong_ht_grow_clear_m7"
  , "full_cong_ht_lookup_m7", "full_cong_ht_insert_m7", "full_cong_u64_sift_m7"
  , "full_cong_u64_sort_m7", "full_cong_bsearch_u64_m7", "full_cong_copy_condbin_m7"
  , "full_cong_extract_condeq_m7", "full_cong_merge_condeq_m7", "full_cong_extract_ite_all_m7"
  , "full_congruence_dense", "full_k512_init", "full_k512_watch", "full_k512_assign"
  , "full_k512_add_clause", "full_k512_mtf", "full_k512_backtrack", "full_k512_propagate"
  , "full_k512_ana_clause", "full_k512_analyze", "full_k512_solve", "full_k512_flip"
  , "full_k512_add_live", "full_m4_sweep_cone", "full_m4_sweep_refine_sig"
  , "full_m4_sweep_rand_phases", "full_m4_sweep_flip_round", "full_m4_sweep_sim"
  , "full_m4_sweep_rearm", "full_m4_sweep_build_pht", "full_m4_sweep_units"
  , "full_m4_sweep_classes", "full_m4_sweep_var", "full_sweep_dense_m5", "full_m6_max_v"
  , "full_k6_add_ticks", "full_k6_init", "full_k6_watch", "full_k6_assign", "full_k6_add_clause"
  , "full_k6_mtf", "full_k6_backtrack", "full_k6_propagate", "full_k6_ana_clause"
  , "full_k6_analyze", "full_k6_solve", "full_k6_flip", "full_k512_add_live_m6"
  , "full_m6_dense_prop_lit", "full_m6_dense_prop", "full_m6_sweep_cone"
  , "full_m6_sweep_refine_sig", "full_m6_sweep_rand_phases", "full_m6_sweep_solve"
  , "full_m6_sweep_flip_round", "full_m6_sweep_sim", "full_m6_sweep_rearm"
  , "full_m6_sweep_build_pht", "full_m6_extract_pht", "full_m6_refine_partition"
  , "full_m6_sweep_units", "full_m6_sweep_classes", "full_m6_els_ar", "full_m6_els_lit"
  , "full_m6_els_fold", "full_m6_dense_els", "full_m6_sweep_var", "full_m6_cand_sift"
  , "full_m6_collect_cands", "full_m6_sweep_vars", "full_sweep_dense_m6", "full_fwd_dedup_bins"
  , "full_dense_prop_unit_m7", "full_dense_flush_units_m7", "full_fwd_flush_large_m7"
  , "full_fwd_reconnect_irred_m7", "full_fwd_scan_lit_m7", "full_fwd_check_cl_m7"
  , "full_fwd_connect_subsumer_m7", "full_fwd_collect_sort_m7", "full_forward_sub_m7"
  , "full_bve_collect_m7", "full_forward_sub", "full_bve_collect", "full_bve_mark_and_m7"
  , "full_bve_find_equiv_m7", "full_bve_find_and_m7", "full_bve_get_tern_m7"
  , "full_bve_match_tern_m7", "full_bve_find_ite_side_m7", "full_bve_find_ite_m7"
  , "full_bve_xor_pat_m7", "full_bve_find_xor_m7", "full_k6_watch_m7", "full_k6_assign_m7"
  , "full_k6_mtf_m7", "full_k6_backtrack_m7", "full_k6_prop_m7", "full_k6_ana_cl_m7"
  , "full_k6_analyze_m7", "full_k6_solve_m7", "full_k6_core_m7", "full_bve_def_k6_m7"
  , "full_bve_gates_m7", "full_bve_resolve_pair", "full_bve_weaken", "full_bve_try_bce"
  , "full_bve_commit_res", "full_bve_ext_need", "full_bve_find_equiv_m8", "full_bve_find_and_m8"
  , "full_bve_match_tern_m8", "full_bve_find_ite_side_m8", "full_bve_find_ite_m8"
  , "full_k6_watch_m8", "full_k6_assign_m8", "full_k6_mtf_m8", "full_k6_backtrack_m8"
  , "full_k6_prop_m8", "full_k6_ana_cl_m8", "full_k6_analyze_m8", "full_k6_solve_m8"
  , "full_k6_core_m8", "full_k6_extract_and_solve_m8", "full_bve_def_k6_m8", "full_bve_k6_mv_fid"
  , "full_fid_k6_add_ticks", "full_k6_watch_fid", "full_k6_assign_fid", "full_k6_mtf_fid"
  , "full_k6_backtrack_fid", "full_k6_prop_fid", "full_k6_ana_cl_fid", "full_k6_analyze_fid"
  , "full_k6_solve_fid", "full_k6_core_fid", "full_k6_extract_and_solve_fid"
  , "full_bve_certify_unit_fid", "full_bve_def_k6_fid", "full_bve_gates_fid", "full_bve_var_m7"
  , "full_bve_var", "full_init_fresh_var", "full_bva_hop1", "full_bva_hop2", "full_bva_hop3"
  , "full_bva_match_large", "full_bva_steps_cap_fid", "full_bva_clines_fid", "full_fheap_up_fid"
  , "full_fheap_down_fid", "full_bva_count_lit_deg_fid", "full_bva_connect_clauses_fid"
  , "full_bva_match_large_bva_fid", "full_bva_scan_cands", "full_bva_pick_cand"
  , "full_bva_match_large_fid", "full_bva_filter_row", "full_bva_commit", "full_bva_try_lit"
  , "full_fheap_up", "full_fheap_down", "full_bva_upd_lit_fid", "full_factor"
  , "full_compact_needed", "full_compact_flush", "full_compact_mark_live"
  , "full_compact_assign_map", "full_compact_record_ext", "full_compact_bins"
  , "full_compact_arena", "full_compact_vars", "full_compact_sift_q", "full_compact_vmtf"
  , "full_compact_sift_h", "full_compact_heap", "full_compact", "full_reorder_weight_m7"
  , "full_reorder_sift_m7", "full_reorder_sift_fid", "full_reorder_queue_m7", "full_reorder_m6"
  , "full_bce_side_m4", "full_bce_pair_m4", "full_bce_var_m4", "full_bce_m4", "full_min_u64"
  , "full_max_u64", "full_elim_dticks", "full_bve_var_key_m7", "full_bve_heap_up_m7"
  , "full_bve_heap_down_m7", "full_bve_heap_push_m7", "full_bve_heap_pop_m7"
  , "full_bve_collect_nbrs_m7", "full_elim_bve_m7", "full_eliminate_m7", "full_eliminate_m6"
  , "full_lcg_next_m7", "full_m7_get64", "full_m7_set64", "full_m7_state_init"
  , "full_tumble_clause_m7", "full_tumble_clauses_m7", "full_tumble_m7", "full_lucky_polar_m7"
  , "full_lucky_late_m7", "full_randec_step_m7", "full_randec_var_m7", "full_decide_m7"
  , "full_ema_swap_m7", "full_switch_mode_m7", "full_probe_dticks_m6_hdr", "full_probe_tail_m6"
  , "full_probe_m6", "full_preprocess_m6", "full_simplify_m6", "m6_hdr_decide_fid"
  , "full_search_m6", "kissat_solve_bytes_m6", "full_preprocess", "full_search"
  , "kissat_solve_bytes" ]

@[expose] def fidStep7_step10_sigPairs : List (Nat × SigEntry) :=
  [ (9, ("full_ilog10", [i64], [i64]))
  , (21, ("full_heap_down", [i64, i32], []))
  , (30, ("full_tick_rel", [i64], []))
  , (34, ("full_ema_update", [i64, i64], []))
  , (36, ("full_assign_lvl", [i64, i32, i32, i32], []))
  , (41, ("full_add_clause", [i64, i32, i32, .bool], [i64]))
  , (64, ("m6_hdr_record_used", [i64, i64], []))
  , (114, ("full_analyze_lit", [i64, i32, i32], [.bool]))
  , (116, ("full_analyze_rsn_m6_hdr", [i64, i32, i32], [.bool]))
  , (117, ("full_clear_ana", [i64], []))
  , (120, ("full_bump_analyzed_m6_hdr", [i64], []))
  , (121, ("full_restore_bump_ana_m6_hdr", [i64], []))
  , (122, ("full_ana_failed_lit_m6_hdr", [i64], [i64]))
  , (126, ("full_min_mark", [i64, i32, i8], []))
  , (131, ("full_sort_tmp", [i64], []))
  , (137, ("full_min_lit_dfs_m8", [i64, i32, .bool, .bool], [.bool]))
  , (139, ("full_shrink_blk_bool_m8", [i64, i64, i64, i32, i64], [.bool]))
  , (140, ("full_min_shrink_m6", [i64], []))
  , (142, ("full_min_shrink", [i64], []))
  , (143, ("full_deduce_1uip", [i64], [i64]))
  , (144, ("full_deduce_1uip_m6_hdr", [i64], [i64]))
  , (145, ("full_det_new_level", [i64, i64], [i64]))
  , (146, ("full_one_lit_confl", [i64], [i64]))
  , (147, ("full_eager_subsume", [i64, i64], []))
  , (148, ("full_learn_clause", [i64, i64], [i64]))
  , (153, ("full_restore_bump_ana_m5", [i64], []))
  , (154, ("full_analyze", [i64], [i64]))
  , (155, ("full_analyze_core_m6", [i64], [i64]))
  , (189, ("full_lucky", [i64], [i64]))
  , (214, ("full_viv_clause_m6", [i64, i32], [i64]))
  , (220, ("full_viv_clear_tier_m6", [i64, i64], []))
  , (222, ("full_viv_collect_fid", [i64, i64], [i64]))
  , (223, ("full_viv_count_fid", [i64, i64], []))
  , (225, ("full_viv_sort_fid", [i64, i64], []))
  , (226, ("full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64]))
  , (257, ("full_cong_has_clause_k", [i64, i32], [.bool]))
  , (403, ("full_bve_k6_mv_fid", [i64], [i64]))
  , (414, ("full_k6_extract_and_solve_fid", [i64, i32, i32, i32, .bool, i32], [.bool]))
  , (415, ("full_bve_certify_unit_fid", [i64, i32, i32, i32, i32, i32], [.bool]))
  , (416, ("full_bve_def_k6_fid", [i64, i32, i32, i32], []))
  , (454, ("full_compact", [i64], [i64]))
  , (477, ("full_m7_get64", [i64, i64], [i64]))
  , (478, ("full_m7_set64", [i64, i64, i64], []))
  , (488, ("full_ema_swap_m7", [i64, i64, i64], []))
  , (489, ("full_switch_mode_m7", [i64], []))
  , (493, ("full_preprocess_m6", [i64], [i64])) ]

@[expose] def fidStep7_step12_sigPairs : List (Nat × SigEntry) :=
  [ (2, ("kissat_skip_ws_comments", [i64, i64], [i64]))
  , (6, ("kissat_next_lit", [i64, i64], [i64]))
  , (9, ("full_ilog10", [i64], [i64]))
  , (11, ("full_arena_next", [i64, i32], [i32]))
  , (12, ("full_alloc_cl", [i64, i32, i32, .bool], [i64]))
  , (18, ("full_wstack_defrag", [i64], []))
  , (19, ("full_watch_push", [i64, i32, i32, i32, i32], [.bool]))
  , (21, ("full_heap_down", [i64, i32], []))
  , (22, ("full_heap_push", [i64, i32], []))
  , (30, ("full_tick_rel", [i64], []))
  , (32, ("full_log10_q16_m7", [i64], [i64]))
  , (33, ("full_scale_delta_m5", [i64, i64], [i64]))
  , (34, ("full_ema_update", [i64, i64], []))
  , (36, ("full_assign_lvl", [i64, i32, i32, i32], []))
  , (37, ("full_assign", [i64, i32, i32], []))
  , (38, ("full_save_target_best", [i64], []))
  , (39, ("full_backtrack_raw_m5", [i64, i64], []))
  , (40, ("full_backtrack", [i64, i64], []))
  , (41, ("full_add_clause", [i64, i32, i32, .bool], [i64]))
  , (43, ("full_zero_tables2", [i64], []))
  , (46, ("full_init_hdr", [i64, i64, i64, i64], []))
  , (64, ("m6_hdr_record_used", [i64, i64], []))
  , (67, ("m6_hdr_delaying", [i64, i64], [.bool]))
  , (68, ("m6_hdr_bump_delay", [i64, i64], []))
  , (69, ("m6_hdr_reduce_delay", [i64, i64], []))
  , (71, ("m6_hdr_get_watermark", [i64, i64], [i64]))
  , (72, ("m6_hdr_set_watermark", [i64, i64, i64], []))
  , (77, ("full_skip_cl", [i64, i64], [.bool]))
  , (78, ("full_ingest_cl", [i64, i64], [i64]))
  , (81, ("full_unwatch_large", [i64, i32, i32], []))
  , (87, ("full_propagate_ignore", [i64, i64], [i64]))
  , (88, ("full_propagate", [i64], [i64]))
  , (89, ("full_parse_body_m6", [i64, i64], [i64]))
  , (99, ("full_sweep_copy", [i64, i64, i64, i32, .bool], [i64]))
  , (106, ("full_arena_sweep", [i64], [i64]))
  , (107, ("full_mark_reasons", [i64, .bool], []))
  , (112, ("full_reduce", [i64, .bool], [i64]))
  , (113, ("full_reduce_m6", [i64, .bool], [i64]))
  , (114, ("full_analyze_lit", [i64, i32, i32], [.bool]))
  , (115, ("full_analyze_rsn", [i64, i32, i32], [.bool]))
  , (116, ("full_analyze_rsn_m6_hdr", [i64, i32, i32], [.bool]))
  , (117, ("full_clear_ana", [i64], []))
  , (120, ("full_bump_analyzed_m6_hdr", [i64], []))
  , (121, ("full_restore_bump_ana_m6_hdr", [i64], []))
  , (122, ("full_ana_failed_lit_m6_hdr", [i64], [i64]))
  , (123, ("full_otfs_large", [i64, i32, i32], [.bool]))
  , (124, ("full_otfs_bin", [i64, i32, i32], [.bool]))
  , (125, ("full_otfs_subsume", [i64, i32, i64, i64, .bool], []))
  , (126, ("full_min_mark", [i64, i32, i8], []))
  , (131, ("full_sort_tmp", [i64], []))
  , (137, ("full_min_lit_dfs_m8", [i64, i32, .bool, .bool], [.bool]))
  , (139, ("full_shrink_blk_bool_m8", [i64, i64, i64, i32, i64], [.bool]))
  , (140, ("full_min_shrink_m6", [i64], []))
  , (141, ("full_deduce_1uip_m6", [i64], [i64]))
  , (142, ("full_min_shrink", [i64], []))
  , (143, ("full_deduce_1uip", [i64], [i64]))
  , (144, ("full_deduce_1uip_m6_hdr", [i64], [i64]))
  , (145, ("full_det_new_level", [i64, i64], [i64]))
  , (146, ("full_one_lit_confl", [i64], [i64]))
  , (147, ("full_eager_subsume", [i64, i64], []))
  , (148, ("full_learn_clause", [i64, i64], [i64]))
  , (153, ("full_restore_bump_ana_m5", [i64], []))
  , (154, ("full_analyze", [i64], [i64]))
  , (179, ("full_extend", [i64], []))
  , (183, ("full_add_bin", [i64, i32, i32], [i64]))
  , (184, ("full_delete_binary", [i64, i32, i32], []))
  , (185, ("full_set_inactive", [i64, i32, i32], []))
  , (186, ("full_add_unit", [i64, i32], [.bool]))
  , (187, ("full_lucky_scan", [i64, .bool, .bool], [i64]))
  , (205, ("full_viv_best_implied_m6", [i64, i32], [i32]))
  , (209, ("full_viv_finish_m6", [i64, i32, i32, .bool, i32, .bool], [i64]))
  , (210, ("full_viv_sort_counts_m6", [i64, i32], []))
  , (212, ("full_viv_l0_simp_m6", [i64, i32, i32], [i64]))
  , (213, ("full_viv_reuse_prefix_m6", [i64, i32, i32], []))
  , (214, ("full_viv_clause_m6", [i64, i32], [i64]))
  , (215, ("full_viv_tier_match_m6", [i64, i32, i64], [.bool]))
  , (220, ("full_viv_clear_tier_m6", [i64, i64], []))
  , (222, ("full_viv_collect_fid", [i64, i64], [i64]))
  , (224, ("full_viv_sort2_fid", [i64, i64, i64], []))
  , (225, ("full_viv_sort_fid", [i64, i64], []))
  , (226, ("full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64]))
  , (227, ("full_vivify_m6_hdr", [i64], [i64]))
  , (228, ("full_prioritize_binaries_m6", [i64], [.bool]))
  , (229, ("full_backbone_sched_m6", [i64], [i64]))
  , (230, ("full_backbone_keep_m6", [i64, i64], []))
  , (234, ("full_backbone_round_m6", [i64, i64, .bool], [i64]))
  , (235, ("full_backbone_m6", [i64, i64], [i64]))
  , (237, ("full_trans_sort_m6", [i64, i64], []))
  , (238, ("full_transitive_m6", [i64, i64], [i64]))
  , (244, ("full_substitute", [i64], [i64]))
  , (245, ("full_enter_dense", [i64], [.bool]))
  , (246, ("full_sort_bin_watches_fid", [i64], []))
  , (248, ("full_cong_find", [i64, i32], [i32]))
  , (251, ("full_cong_unit_fold", [i64, i32, i32], [i64]))
  , (252, ("full_cong_equiv_fold", [i64, i32, i32, i32], [i64]))
  , (254, ("full_sort_u32", [i64, i32], []))
  , (259, ("full_cong_extract_xor_k", [i64, i32, i32, i64, i64], [i64]))
  , (260, ("full_cong_try_xor_ite", [i64, i32, i32, i32, i64, i64], [i64]))
  , (261, ("full_cong_count_bins", [i64], []))
  , (263, ("full_cong_extract_binaries", [i64, i64], [i64]))
  , (264, ("full_cong_find_units_equivs", [i64], [i64]))
  , (265, ("full_cong_extract", [i64, i64, i64], [i64]))
  , (266, ("full_cong_and_match", [i64, i32, i32], [.bool]))
  , (267, ("full_cong_xor_match", [i64, i32, i32], [i32]))
  , (268, ("full_cong_enq_var", [i64, i64, i32], []))
  , (269, ("full_cong_eval_gate", [i64, i64, i64, i64, i32, i64], [i64]))
  , (270, ("full_cong_work_step", [i64, i64, i64, i64, i32], [i64]))
  , (271, ("full_cong_worklist", [i64, i64, i64, i64], [i64]))
  , (274, ("full_cong_fwd_subsume", [i64, i64], [i64]))
  , (287, ("full_cong_extract_ite_all_m7", [i64, i32, i32, i64], [i32]))
  , (288, ("full_congruence_dense", [i64, i64], [i64]))
  , (312, ("full_m6_max_v", [i64], [i64]))
  , (314, ("full_k6_init", [i64, i32], []))
  , (317, ("full_k6_add_clause", [i64, i64, i32], [.bool]))
  , (327, ("full_m6_dense_prop", [i64], [.bool]))
  , (328, ("full_m6_sweep_cone", [i64, i32], [i64]))
  , (329, ("full_m6_sweep_refine_sig", [i64, i32, i32], []))
  , (331, ("full_m6_sweep_solve", [i64, i32, i64], [i64]))
  , (332, ("full_m6_sweep_flip_round", [i64, i32], [i32]))
  , (333, ("full_m6_sweep_sim", [i64, i32, i64], [i32]))
  , (344, ("full_m6_sweep_var", [i64, i32, i64], [i64]))
  , (346, ("full_m6_collect_cands", [i64], [i32]))
  , (347, ("full_m6_sweep_vars", [i64, i64, i64], [i64]))
  , (348, ("full_sweep_dense_m6", [i64, i64, i64], [i64]))
  , (349, ("full_fwd_dedup_bins", [i64], [.bool]))
  , (350, ("full_dense_prop_unit_m7", [i64, i32], [.bool]))
  , (351, ("full_dense_flush_units_m7", [i64], [.bool]))
  , (352, ("full_fwd_flush_large_m7", [i64], []))
  , (353, ("full_fwd_reconnect_irred_m7", [i64], []))
  , (355, ("full_fwd_check_cl_m7", [i64, i32], [.bool]))
  , (356, ("full_fwd_connect_subsumer_m7", [i64, i32], []))
  , (357, ("full_fwd_collect_sort_m7", [i64], [i64]))
  , (358, ("full_forward_sub_m7", [i64, i64], [i64]))
  , (359, ("full_bve_collect_m7", [i64, i32, i64, i32], [i32]))
  , (381, ("full_bve_gates_m7", [i64, i32, i32, i32], []))
  , (382, ("full_bve_resolve_pair", [i64, i32, i32, i32], [.bool]))
  , (383, ("full_bve_weaken", [i64, i32, i32, i32], [.bool]))
  , (385, ("full_bve_commit_res", [i64, i64, i64], [i64]))
  , (386, ("full_bve_ext_need", [i64, i32, i32], [i64]))
  , (417, ("full_bve_gates_fid", [i64, i32, i32, i32], []))
  , (418, ("full_bve_var_m7", [i64, i32], [i64]))
  , (425, ("full_bva_steps_cap_fid", [i64], [i32]))
  , (427, ("full_fheap_up_fid", [i64, i64, i64, i32], []))
  , (428, ("full_fheap_down_fid", [i64, i64, i64, i32, i32], []))
  , (430, ("full_bva_connect_clauses_fid", [i64], []))
  , (437, ("full_bva_try_lit", [i64, i32, i64], [.bool]))
  , (441, ("full_factor", [i64, i64], [i64]))
  , (442, ("full_compact_needed", [i64], [.bool]))
  , (454, ("full_compact", [i64], [i64]))
  , (477, ("full_m7_get64", [i64, i64], [i64]))
  , (478, ("full_m7_set64", [i64, i64, i64], []))
  , (484, ("full_lucky_late_m7", [i64], [i64]))
  , (488, ("full_ema_swap_m7", [i64, i64, i64], []))
  , (489, ("full_switch_mode_m7", [i64], []))
  , (490, ("full_probe_dticks_m6_hdr", [i64, .bool], [i64]))
  , (492, ("full_probe_m6", [i64, .bool], [i64]))
  , (493, ("full_preprocess_m6", [i64], [i64])) ]

@[expose] def fidStep7_all_sigPairs : List (Nat × SigEntry) :=
  [ (2, ("kissat_skip_ws_comments", [i64, i64], [i64]))
  , (6, ("kissat_next_lit", [i64, i64], [i64]))
  , (8, ("full_isqrt", [i64], [i64]))
  , (9, ("full_ilog10", [i64], [i64]))
  , (11, ("full_arena_next", [i64, i32], [i32]))
  , (12, ("full_alloc_cl", [i64, i32, i32, .bool], [i64]))
  , (18, ("full_wstack_defrag", [i64], []))
  , (19, ("full_watch_push", [i64, i32, i32, i32, i32], [.bool]))
  , (21, ("full_heap_down", [i64, i32], []))
  , (22, ("full_heap_push", [i64, i32], []))
  , (30, ("full_tick_rel", [i64], []))
  , (32, ("full_log10_q16_m7", [i64], [i64]))
  , (33, ("full_scale_delta_m5", [i64, i64], [i64]))
  , (34, ("full_ema_update", [i64, i64], []))
  , (36, ("full_assign_lvl", [i64, i32, i32, i32], []))
  , (37, ("full_assign", [i64, i32, i32], []))
  , (38, ("full_save_target_best", [i64], []))
  , (39, ("full_backtrack_raw_m5", [i64, i64], []))
  , (40, ("full_backtrack", [i64, i64], []))
  , (41, ("full_add_clause", [i64, i32, i32, .bool], [i64]))
  , (42, ("full_zero_tables1", [i64], []))
  , (43, ("full_zero_tables2", [i64], []))
  , (46, ("full_init_hdr", [i64, i64, i64, i64], []))
  , (62, ("m6_hdr_recompute_tiers", [i64], []))
  , (64, ("m6_hdr_record_used", [i64, i64], []))
  , (67, ("m6_hdr_delaying", [i64, i64], [.bool]))
  , (68, ("m6_hdr_bump_delay", [i64, i64], []))
  , (69, ("m6_hdr_reduce_delay", [i64, i64], []))
  , (71, ("m6_hdr_get_watermark", [i64, i64], [i64]))
  , (72, ("m6_hdr_set_watermark", [i64, i64, i64], []))
  , (77, ("full_skip_cl", [i64, i64], [.bool]))
  , (78, ("full_ingest_cl", [i64, i64], [i64]))
  , (81, ("full_unwatch_large", [i64, i32, i32], []))
  , (84, ("full_prop_flush_del_fid", [i64, i64], [.bool]))
  , (87, ("full_propagate_ignore", [i64, i64], [i64]))
  , (88, ("full_propagate", [i64], [i64]))
  , (89, ("full_parse_body_m6", [i64, i64], [i64]))
  , (93, ("full_sweep_bins_range_m6", [i64, i64], []))
  , (94, ("full_rewatch_range_m6", [i64, i64, i64], [.bool]))
  , (99, ("full_sweep_copy", [i64, i64, i64, i32, .bool], [i64]))
  , (103, ("full_move_red_end_m6", [i64, i64, i64], []))
  , (104, ("full_arena_sweep_m6", [i64], [i64]))
  , (106, ("full_arena_sweep", [i64], [i64]))
  , (107, ("full_mark_reasons", [i64, .bool], []))
  , (108, ("full_flush_trail", [i64], [i64]))
  , (111, ("full_sort_reds", [i64, i64], []))
  , (112, ("full_reduce", [i64, .bool], [i64]))
  , (113, ("full_reduce_m6", [i64, .bool], [i64]))
  , (114, ("full_analyze_lit", [i64, i32, i32], [.bool]))
  , (115, ("full_analyze_rsn", [i64, i32, i32], [.bool]))
  , (116, ("full_analyze_rsn_m6_hdr", [i64, i32, i32], [.bool]))
  , (117, ("full_clear_ana", [i64], []))
  , (120, ("full_bump_analyzed_m6_hdr", [i64], []))
  , (121, ("full_restore_bump_ana_m6_hdr", [i64], []))
  , (122, ("full_ana_failed_lit_m6_hdr", [i64], [i64]))
  , (123, ("full_otfs_large", [i64, i32, i32], [.bool]))
  , (124, ("full_otfs_bin", [i64, i32, i32], [.bool]))
  , (125, ("full_otfs_subsume", [i64, i32, i64, i64, .bool], []))
  , (126, ("full_min_mark", [i64, i32, i8], []))
  , (131, ("full_sort_tmp", [i64], []))
  , (137, ("full_min_lit_dfs_m8", [i64, i32, .bool, .bool], [.bool]))
  , (139, ("full_shrink_blk_bool_m8", [i64, i64, i64, i32, i64], [.bool]))
  , (140, ("full_min_shrink_m6", [i64], []))
  , (141, ("full_deduce_1uip_m6", [i64], [i64]))
  , (142, ("full_min_shrink", [i64], []))
  , (143, ("full_deduce_1uip", [i64], [i64]))
  , (144, ("full_deduce_1uip_m6_hdr", [i64], [i64]))
  , (145, ("full_det_new_level", [i64, i64], [i64]))
  , (146, ("full_one_lit_confl", [i64], [i64]))
  , (147, ("full_eager_subsume", [i64, i64], []))
  , (148, ("full_learn_clause", [i64, i64], [i64]))
  , (153, ("full_restore_bump_ana_m5", [i64], []))
  , (154, ("full_analyze", [i64], [i64]))
  , (155, ("full_analyze_core_m6", [i64], [i64]))
  , (179, ("full_extend", [i64], []))
  , (183, ("full_add_bin", [i64, i32, i32], [i64]))
  , (184, ("full_delete_binary", [i64, i32, i32], []))
  , (185, ("full_set_inactive", [i64, i32, i32], []))
  , (186, ("full_add_unit", [i64, i32], [.bool]))
  , (187, ("full_lucky_scan", [i64, .bool, .bool], [i64]))
  , (189, ("full_lucky", [i64], [i64]))
  , (205, ("full_viv_best_implied_m6", [i64, i32], [i32]))
  , (209, ("full_viv_finish_m6", [i64, i32, i32, .bool, i32, .bool], [i64]))
  , (210, ("full_viv_sort_counts_m6", [i64, i32], []))
  , (212, ("full_viv_l0_simp_m6", [i64, i32, i32], [i64]))
  , (213, ("full_viv_reuse_prefix_m6", [i64, i32, i32], []))
  , (214, ("full_viv_clause_m6", [i64, i32], [i64]))
  , (215, ("full_viv_tier_match_m6", [i64, i32, i64], [.bool]))
  , (220, ("full_viv_clear_tier_m6", [i64, i64], []))
  , (222, ("full_viv_collect_fid", [i64, i64], [i64]))
  , (223, ("full_viv_count_fid", [i64, i64], []))
  , (224, ("full_viv_sort2_fid", [i64, i64, i64], []))
  , (225, ("full_viv_sort_fid", [i64, i64], []))
  , (226, ("full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64]))
  , (227, ("full_vivify_m6_hdr", [i64], [i64]))
  , (228, ("full_prioritize_binaries_m6", [i64], [.bool]))
  , (229, ("full_backbone_sched_m6", [i64], [i64]))
  , (230, ("full_backbone_keep_m6", [i64, i64], []))
  , (234, ("full_backbone_round_m6", [i64, i64, .bool], [i64]))
  , (235, ("full_backbone_m6", [i64, i64], [i64]))
  , (237, ("full_trans_sort_m6", [i64, i64], []))
  , (238, ("full_transitive_m6", [i64, i64], [i64]))
  , (244, ("full_substitute", [i64], [i64]))
  , (245, ("full_enter_dense", [i64], [.bool]))
  , (246, ("full_sort_bin_watches_fid", [i64], []))
  , (247, ("full_rebuild_watches", [i64], [i64]))
  , (248, ("full_cong_find", [i64, i32], [i32]))
  , (251, ("full_cong_unit_fold", [i64, i32, i32], [i64]))
  , (252, ("full_cong_equiv_fold", [i64, i32, i32, i32], [i64]))
  , (254, ("full_sort_u32", [i64, i32], []))
  , (257, ("full_cong_has_clause_k", [i64, i32], [.bool]))
  , (259, ("full_cong_extract_xor_k", [i64, i32, i32, i64, i64], [i64]))
  , (260, ("full_cong_try_xor_ite", [i64, i32, i32, i32, i64, i64], [i64]))
  , (261, ("full_cong_count_bins", [i64], []))
  , (263, ("full_cong_extract_binaries", [i64, i64], [i64]))
  , (264, ("full_cong_find_units_equivs", [i64], [i64]))
  , (265, ("full_cong_extract", [i64, i64, i64], [i64]))
  , (266, ("full_cong_and_match", [i64, i32, i32], [.bool]))
  , (267, ("full_cong_xor_match", [i64, i32, i32], [i32]))
  , (268, ("full_cong_enq_var", [i64, i64, i32], []))
  , (269, ("full_cong_eval_gate", [i64, i64, i64, i64, i32, i64], [i64]))
  , (270, ("full_cong_work_step", [i64, i64, i64, i64, i32], [i64]))
  , (271, ("full_cong_worklist", [i64, i64, i64, i64], [i64]))
  , (274, ("full_cong_fwd_subsume", [i64, i64], [i64]))
  , (287, ("full_cong_extract_ite_all_m7", [i64, i32, i32, i64], [i32]))
  , (288, ("full_congruence_dense", [i64, i64], [i64]))
  , (312, ("full_m6_max_v", [i64], [i64]))
  , (314, ("full_k6_init", [i64, i32], []))
  , (317, ("full_k6_add_clause", [i64, i64, i32], [.bool]))
  , (327, ("full_m6_dense_prop", [i64], [.bool]))
  , (328, ("full_m6_sweep_cone", [i64, i32], [i64]))
  , (329, ("full_m6_sweep_refine_sig", [i64, i32, i32], []))
  , (331, ("full_m6_sweep_solve", [i64, i32, i64], [i64]))
  , (332, ("full_m6_sweep_flip_round", [i64, i32], [i32]))
  , (333, ("full_m6_sweep_sim", [i64, i32, i64], [i32]))
  , (344, ("full_m6_sweep_var", [i64, i32, i64], [i64]))
  , (346, ("full_m6_collect_cands", [i64], [i32]))
  , (347, ("full_m6_sweep_vars", [i64, i64, i64], [i64]))
  , (348, ("full_sweep_dense_m6", [i64, i64, i64], [i64]))
  , (349, ("full_fwd_dedup_bins", [i64], [.bool]))
  , (350, ("full_dense_prop_unit_m7", [i64, i32], [.bool]))
  , (351, ("full_dense_flush_units_m7", [i64], [.bool]))
  , (352, ("full_fwd_flush_large_m7", [i64], []))
  , (353, ("full_fwd_reconnect_irred_m7", [i64], []))
  , (355, ("full_fwd_check_cl_m7", [i64, i32], [.bool]))
  , (356, ("full_fwd_connect_subsumer_m7", [i64, i32], []))
  , (357, ("full_fwd_collect_sort_m7", [i64], [i64]))
  , (358, ("full_forward_sub_m7", [i64, i64], [i64]))
  , (359, ("full_bve_collect_m7", [i64, i32, i64, i32], [i32]))
  , (381, ("full_bve_gates_m7", [i64, i32, i32, i32], []))
  , (382, ("full_bve_resolve_pair", [i64, i32, i32, i32], [.bool]))
  , (383, ("full_bve_weaken", [i64, i32, i32, i32], [.bool]))
  , (385, ("full_bve_commit_res", [i64, i64, i64], [i64]))
  , (386, ("full_bve_ext_need", [i64, i32, i32], [i64]))
  , (403, ("full_bve_k6_mv_fid", [i64], [i64]))
  , (414, ("full_k6_extract_and_solve_fid", [i64, i32, i32, i32, .bool, i32], [.bool]))
  , (415, ("full_bve_certify_unit_fid", [i64, i32, i32, i32, i32, i32], [.bool]))
  , (416, ("full_bve_def_k6_fid", [i64, i32, i32, i32], []))
  , (417, ("full_bve_gates_fid", [i64, i32, i32, i32], []))
  , (418, ("full_bve_var_m7", [i64, i32], [i64]))
  , (420, ("full_init_fresh_var", [i64, i32], []))
  , (425, ("full_bva_steps_cap_fid", [i64], [i32]))
  , (427, ("full_fheap_up_fid", [i64, i64, i64, i32], []))
  , (428, ("full_fheap_down_fid", [i64, i64, i64, i32, i32], []))
  , (429, ("full_bva_count_lit_deg_fid", [i64, i32], [i32]))
  , (430, ("full_bva_connect_clauses_fid", [i64], []))
  , (436, ("full_bva_commit", [i64, i32], [.bool]))
  , (437, ("full_bva_try_lit", [i64, i32, i64], [.bool]))
  , (440, ("full_bva_upd_lit_fid", [i64, i64, i64, i64, i32, i64, i32], [i32]))
  , (441, ("full_factor", [i64, i64], [i64]))
  , (442, ("full_compact_needed", [i64], [.bool]))
  , (443, ("full_compact_flush", [i64], [i64]))
  , (454, ("full_compact", [i64], [i64]))
  , (477, ("full_m7_get64", [i64, i64], [i64]))
  , (478, ("full_m7_set64", [i64, i64, i64], []))
  , (484, ("full_lucky_late_m7", [i64], [i64]))
  , (488, ("full_ema_swap_m7", [i64, i64, i64], []))
  , (489, ("full_switch_mode_m7", [i64], []))
  , (490, ("full_probe_dticks_m6_hdr", [i64, .bool], [i64]))
  , (492, ("full_probe_m6", [i64, .bool], [i64]))
  , (493, ("full_preprocess_m6", [i64], [i64])) ]

@[expose] def fidS12BadNames : List Sym :=
  [ "full_ingest_cl", "full_viv_collect_fid"
  , "full_cong_extract", "full_cong_and_match", "full_cong_enq_var"
  , "full_cong_eval_gate", "full_cong_worklist" ]

@[expose] def fidS12SkipNames : List Sym :=
  [ "full_cong_work_step"
  , "full_analyze_rsn_m6_hdr", "full_ana_failed_lit_m6_hdr", "full_min_shrink_m6"
  , "full_analyze", "full_analyze_core_m6", "full_vivify_tier_m6_hdr"
  , "full_switch_mode_m7", "full_preprocess_m6"
  , "full_zero_tables2", "full_init_hdr", "full_ingest_cl"
  , "full_parse_body_m6", "full_extend", "full_lucky_scan"
  , "full_m6_sweep_cone", "full_save_target_best", "full_backtrack"
  , "full_deduce_1uip_m6", "full_deduce_1uip_m6_hdr", "full_one_lit_confl"
  , "full_learn_clause", "full_viv_collect_fid", "full_viv_sort2_fid"
  , "full_viv_sort_fid", "full_viv_clause_m6"
  , "full_cong_extract", "full_cong_and_match", "full_cong_enq_var"
  , "full_cong_eval_gate", "full_cong_worklist", "full_congruence_dense"
  , "full_backbone_sched_m6", "full_backbone_m6", "full_dense_prop_unit_m7"
  , "full_forward_sub_m7", "full_bve_commit_res", "full_bve_var_m7"
  , "full_add_clause", "full_sweep_copy", "full_learn_clause_m6"
  , "full_viv_sort_counts_m6"
  , "full_trans_sort_m6", "full_m6_sweep_sim", "full_m6_sweep_vars"
  , "full_factor", "full_probe_m6" ]

end Step7Meta

end LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep7

end
