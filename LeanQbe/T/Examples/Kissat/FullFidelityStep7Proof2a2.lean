/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep7BvaSpec
public import LeanQbe.T.Examples.Kissat.FullM7BvaFactor
import LeanQbe.T.Examples.Kissat.FullM4BvaLemmas1
import LeanQbe.T.Examples.Kissat.FullBvaFwdLemmas1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step-7 BVA Proofs — Part 2a2 (`full_init_fresh_var` with `res_sz`)

Proves (`public section`, M1-clean, parametric `(Γ : Env)`) the
Step-7 contract `step7InitFreshVarSpec` for the reused M7 body
`FullM7BvaFactor.full_init_fresh_var_m7_body`, i.e. `FullM7BvaFactor.m7InitFreshVarFn`, the
`"full_init_fresh_var"` row of the Step-6/7 fidelity environment (`m7FidP3InitFreshVar_mem`):
- `full_init_fresh_var_m7_step7_wp`: the `FullM7BvaFactorProof0` proof of
  `fullInitFreshVarHeapSpec` (`2041#32` flags + `q_first` VMTF head enqueue) re-threaded with
  `res_sz` preservation (both concrete post-scratches `{ s.scratch with ... }` keep `res_sz`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep7

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullBvaFwdHelpers
open LeanQbe.T.Examples.Kissat.FullBvaHeap
open LeanQbe.T.Examples.Kissat.FullBvaHeap.FullBvaHeapHelpers
open LeanQbe.T.Examples.Kissat.FullBvaHeap.FullBvaHeapTactics
open LeanQbe.T.Examples.Kissat.FullBvaHeap.FullBvaHeapScanHelpers
open LeanQbe.T.Examples.Kissat.FullM4Bva
open Kraken.Bedrock2.Test
open scoped FullArenaTactics FullBvaHeapTactics FullBvaFwdTactics

private theorem bv64_shl2_fv_toNat (fv : BitVec 32) :
    (BitVec.setWidth 64 fv <<< (2 : Nat)).toNat = 4 * fv.toNat := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega

private theorem bv64_shl2_add1_fv_toNat (fv : BitVec 32) :
    ((BitVec.setWidth 64 fv <<< (2 : Nat)) + 1#64).toNat = 4 * fv.toNat + 1 := by
  simp [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega

private theorem bv64_shl2_add2_fv_toNat (fv : BitVec 32) :
    ((BitVec.setWidth 64 fv <<< (2 : Nat)) + 2#64).toNat = 4 * fv.toNat + 2 := by
  simp [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega

private theorem bv64_shl2_add3_fv_toNat (fv : BitVec 32) :
    ((BitVec.setWidth 64 fv <<< (2 : Nat)) + 3#64).toNat = 4 * fv.toNat + 3 := by
  simp [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega

private theorem bv64_shl1_fv_toNat (fv : BitVec 32) :
    (BitVec.setWidth 64 fv <<< (1 : Nat)).toNat = 2 * fv.toNat := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega

private theorem nat_two_mul_lor_one (n : Nat) : (2 * n) ||| 1 = 2 * n + 1 := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_or]
  cases k with
  | zero => simp [Nat.testBit_zero]
  | succ k =>
    rw [Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
    simp [Nat.zero_testBit, show (2 * n) / 2 = n by omega, show (2 * n + 1) / 2 = n by omega]

private theorem bv64_shl1_or1_fv_toNat (fv : BitVec 32) :
    ((BitVec.setWidth 64 fv <<< (1 : Nat)) ||| 1#64).toNat = 2 * fv.toNat + 1 := by
  rw [BitVec.toNat_or, bv64_shl1_fv_toNat fv, show (1#64 : BitVec 64).toNat = 1 from rfl]
  exact nat_two_mul_lor_one fv.toNat

private theorem bv64_shl2_add1_fv_ofNat (fv : BitVec 32) :
    ((BitVec.setWidth 64 fv <<< (2 : Nat)) + (1 : BitVec 64)).toNat = 4 * fv.toNat + 1 :=
  bv64_shl2_add1_fv_toNat fv

private theorem bv64_shl2_add2_fv_ofNat (fv : BitVec 32) :
    ((BitVec.setWidth 64 fv <<< (2 : Nat)) + (2 : BitVec 64)).toNat = 4 * fv.toNat + 2 :=
  bv64_shl2_add2_fv_toNat fv

private theorem bv64_shl2_add3_fv_ofNat (fv : BitVec 32) :
    ((BitVec.setWidth 64 fv <<< (2 : Nat)) + (3 : BitVec 64)).toNat = 4 * fv.toNat + 3 :=
  bv64_shl2_add3_fv_toNat fv

private theorem bv64_shl1_or1_fv_ofNat (fv : BitVec 32) :
    ((BitVec.setWidth 64 fv <<< (1 : Nat)) ||| (1 : BitVec 64)).toNat = 2 * fv.toNat + 1 :=
  bv64_shl1_or1_fv_toNat fv

/-! ## `full_init_fresh_var_m7` under `step7InitFreshVarSpec` -/

section M7InitFreshVar

private theorem m7InitFreshVar_sc_ok {c : FullCfg} {sc : FullScratch}
    (hok : FullScratch.LengthsOk c sc)
    (qf ql : BitVec 64) (ph : List (BitVec 8)) (ps qp qn qs : List (BitVec 32))
    (score : List (BitVec 64))
    (hph : ph.length = c.max_vars) (hps : ps.length = c.max_vars)
    (hqp : qp.length = c.max_vars) (hqn : qn.length = c.max_vars)
    (hqs : qs.length = c.max_vars) (hsc : score.length = c.max_vars) :
    FullScratch.LengthsOk c { sc with
      q_first := qf, q_last := ql, phases := ph, pos := ps,
      q_prev := qp, q_next := qn, q_stamp := qs, score := score } :=
  ⟨hok.walk_vals_len, hph, hok.phases_target_len, hok.phases_best_len,
   hok.walk_best_len, hok.heap_len_arr, hps, hok.shrink_stk_len, hqp, hqn, hqs,
   hok.wsort_len, hok.work_stk1_len, hok.work_stk2_len, hok.tarjan_mark_len,
   hok.tarjan_reach_len, hsc, hok.sim_sig_len, hok.glue_used_len,
   hok.last_learned_len, hok.delayed_len_arr, hok.red_refs_len,
   hok.extend_stk_len, hok.scratch_buf_len⟩

private theorem m7InitFreshVar_post {c : FullCfg} {s : FullState} {fv : BitVec 32}
    {R : Mem 64 → Prop} {Q : Post []} {m' : Mem 64}
    (hfv_lt : fv.toNat < s.core.cur_vars) (hclen : s.core.LengthsOk c)
    (_hsc_ok : FullScratch.LengthsOk c s.scratch) (hcv_le : s.core.cur_vars ≤ c.max_vars)
    (sc' : FullScratch) (hsc' : FullScratch.LengthsOk c sc')
    (hll : sc'.last_learned = s.scratch.last_learned)
    (hel : sc'.extend_len = s.scratch.extend_len)
    (hsb : sc'.scratch_buf = s.scratch.scratch_buf)
    (hws : sc'.wsort = s.scratch.wsort)
    (htm : sc'.tarjan_mark = s.scratch.tarjan_mark)
    (htr : sc'.tarjan_reach = s.scratch.tarjan_reach)
    (hsig : sc'.sim_sig = s.scratch.sim_sig)
    (hres : sc'.res_sz = s.scratch.res_sz)
    (hm' : (FullMem c { core := { s.core with
      unassigned := s.core.unassigned + 1#64,
      vals := (s.core.vals.set (2 * fv.toNat) 0#8).set (2 * fv.toNat + 1) 0#8,
      mrk := s.core.mrk.set fv.toNat 0#8,
      flags := s.core.flags.set fv.toNat 2041#32,
      lvl := s.core.lvl.set fv.toNat 0#32,
      rsns := s.core.rsns.set fv.toNat 0xFFFFFFFF#32,
      wvec := (((s.core.wvec.set (4 * fv.toNat) 0#32).set (4 * fv.toNat + 1) 0#32).set
        (4 * fv.toNat + 2) 0#32).set (4 * fv.toNat + 3) 0#32 }, scratch := sc' } ⋆ R) m')
    (hQ : ∀ (vals' mrk' : List (BitVec 8)) (flags' lvl' rsns' wvec' : List (BitVec 32))
      (unass' : BitVec 64) (sc' : FullScratch) (m' : Mem 64),
      have s' : FullState := { core := { s.core with
        unassigned := unass', vals := vals', mrk := mrk', flags := flags',
        lvl := lvl', rsns := rsns', wvec := wvec' }, scratch := sc' }
      s'.LengthsOk c → FullExtScratchPres s s' → sc'.scratch_buf = s.scratch.scratch_buf →
      sc'.wsort = s.scratch.wsort → sc'.tarjan_mark = s.scratch.tarjan_mark →
      sc'.tarjan_reach = s.scratch.tarjan_reach → sc'.sim_sig = s.scratch.sim_sig →
      sc'.res_sz = s.scratch.res_sz →
      vals'[2 * fv.toNat]?.getD 1#8 = 0#8 →
      vals'[2 * fv.toNat + 1]?.getD 1#8 = 0#8 →
      (∀ l < 2 * c.max_vars, l / 2 ≠ fv.toNat → vals'[l]? = s.core.vals[l]?) →
      mrk'[fv.toNat]?.getD 1#8 = 0#8 →
      (∀ v < c.max_vars, v ≠ fv.toNat → mrk'[v]? = s.core.mrk[v]?) →
      lvl'[fv.toNat]?.getD 1#32 = 0#32 →
      (∀ v < c.max_vars, v ≠ fv.toNat → lvl'[v]? = s.core.lvl[v]?) →
      rsns'[fv.toNat]?.getD 0#32 = 0xFFFFFFFF#32 →
      (∀ v < c.max_vars, v ≠ fv.toNat → rsns'[v]? = s.core.rsns[v]?) →
      (∀ k < 4, wvec'[4 * fv.toNat + k]?.getD 1#32 = 0#32) →
      (∀ i < 4 * c.max_vars, i / 4 ≠ fv.toNat → wvec'[i]? = s.core.wvec[i]?) →
      (FullMem c s' ⋆ R) m' → Q () m') : Q () m' := by
  have hvl := hclen.vals_len; have hml := hclen.mrk_len; have hfl := hclen.flags_len
  have hll' := hclen.lvl_len; have hrl := hclen.rsns_len; have hwl := hclen.wvec_len
  have hlen' : ({ core := { s.core with
      unassigned := s.core.unassigned + 1#64,
      vals := (s.core.vals.set (2 * fv.toNat) 0#8).set (2 * fv.toNat + 1) 0#8,
      mrk := s.core.mrk.set fv.toNat 0#8,
      flags := s.core.flags.set fv.toNat 2041#32,
      lvl := s.core.lvl.set fv.toNat 0#32,
      rsns := s.core.rsns.set fv.toNat 0xFFFFFFFF#32,
      wvec := (((s.core.wvec.set (4 * fv.toNat) 0#32).set (4 * fv.toNat + 1) 0#32).set
        (4 * fv.toNat + 2) 0#32).set (4 * fv.toNat + 3) 0#32 }, scratch := sc' } :
      FullState).LengthsOk c :=
    ⟨{ hclen with
        vals_len := by simp [hvl], mrk_len := by simp [hml], flags_len := by simp [hfl],
        lvl_len := by simp [hll'], rsns_len := by simp [hrl], wvec_len := by simp [hwl] },
     hsc'⟩
  refine hQ _ _ _ _ _ _ _ sc' m' hlen' ⟨hll, hel⟩ hsb hws htm htr hsig hres
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hm'
  · rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega), Option.getD_some]
  · rw [List.getElem?_set_self (by rw [List.length_set]; omega), Option.getD_some]
  · intro l hl hne
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  · rw [List.getElem?_set_self (by omega), Option.getD_some]
  · intro v hv hne; rw [List.getElem?_set_ne (Ne.symm hne)]
  · rw [List.getElem?_set_self (by omega), Option.getD_some]
  · intro v hv hne; rw [List.getElem?_set_ne (Ne.symm hne)]
  · rw [List.getElem?_set_self (by omega), Option.getD_some]
  · intro v hv hne; rw [List.getElem?_set_ne (Ne.symm hne)]
  · intro k hk
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
    · simp only [Nat.add_zero]
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega), Option.getD_some]
    · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_self (by rw [List.length_set]; omega), Option.getD_some]
    · rw [List.getElem?_set_ne (by omega),
        List.getElem?_set_self (by rw [List.length_set, List.length_set]; omega), Option.getD_some]
    · rw [List.getElem?_set_self
        (by rw [List.length_set, List.length_set, List.length_set]; omega), Option.getD_some]
  · intro i hi hne
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]

private def M7MemInitRest (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
  array (t := i8) c.pLitMark s.core.lit_mark ⋆
  (array (t := i32) c.pTrail s.core.trl ⋆
   array (t := i32) c.pTrailPos s.core.trail_pos ⋆
   array (t := i32) c.pTmp s.core.tmp ⋆
   array (t := i32) c.pMinClr s.core.min_clr) ⋆
  (array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
   array (t := i32) c.pFrameDec s.core.frame_dec ⋆
   array (t := i32) c.pRepr s.core.repr ⋆
   array (t := i32) c.pMinStk s.core.min_stk) ⋆
  FullCoreDynArrs c s.core ⋆
  (array (t := i8) c.pWalkVals s.scratch.walk_vals ⋆
   array (t := i8) c.pPhasesTarget s.scratch.phases_target ⋆
   array (t := i8) c.pPhasesBest s.scratch.phases_best ⋆
   array (t := i8) c.pWalkBest s.scratch.walk_best) ⋆
  (array (t := i32) c.pHeap s.scratch.heap ⋆
   array (t := i32) c.pShrinkStk s.scratch.shrink_stk ⋆
   array (t := i32) c.pQPrev s.scratch.q_prev ⋆
   array (t := i32) c.pQNext s.scratch.q_next ⋆
   array (t := i32) c.pQStamp s.scratch.q_stamp) ⋆
  FullScrWksArrs c s.scratch ⋆
  (array64 c.pSimSig s.scratch.sim_sig ⋆
   array (t := i32) c.pGlueUsed s.scratch.glue_used ⋆
   array (t := i32) c.pLastLearned s.scratch.last_learned) ⋆
  FullScrDynArrs c s.scratch ⋆ c.pad

private theorem focus_init {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) :
    (array (t := i32) c.pWvec s.core.wvec ⋆
     array (t := i8) c.pVals s.core.vals ⋆
     array (t := i8) c.pMark s.core.mrk ⋆
     array (t := i8) c.pPhases s.scratch.phases ⋆
     array (t := i32) c.pLevel s.core.lvl ⋆
     array (t := i32) c.pReason s.core.rsns ⋆
     array (t := i32) c.pPos s.scratch.pos ⋆
     array64 c.pScore s.scratch.score ⋆
     array (t := i32) c.pFlags s.core.flags ⋆
     (M7MemInitRest c s ⋆ R)) m := by
  unfold FullMem FullCoreArrays FullCoreByteArrs FullCoreU32A FullCoreU32B
    FullScratchArrays FullScrByteArrs FullScrU32A FullScrMetaArrs at hm
  unfold M7MemInitRest
  ecancel

private theorem unfocus_init_var {c : FullCfg} {s' : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (array (t := i32) c.pFlags s'.core.flags ⋆
           (array64 c.pScore s'.scratch.score ⋆
           (array (t := i32) c.pPos s'.scratch.pos ⋆
           (array (t := i32) c.pReason s'.core.rsns ⋆
           (array (t := i32) c.pLevel s'.core.lvl ⋆
           (array (t := i8) c.pPhases s'.scratch.phases ⋆
           (array (t := i8) c.pMark s'.core.mrk ⋆
           (array (t := i8) c.pVals s'.core.vals ⋆
           (array (t := i32) c.pWvec s'.core.wvec ⋆
           (M7MemInitRest c s' ⋆ R)))))))))) m) :
    (FullMem c s' ⋆ R) m := by
  unfold FullMem FullCoreArrays FullCoreByteArrs FullCoreU32A FullCoreU32B
    FullScratchArrays FullScrByteArrs FullScrU32A FullScrMetaArrs
  unfold M7MemInitRest at hm
  ecancel

private theorem unfocus_init {c : FullCfg} {s : FullState}
    {wv fl lv rs : List (BitVec 32)} {vl mk ph : List (BitVec 8)}
    {ps : List (BitVec 32)} {sc : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (array (t := i32) c.pFlags fl ⋆
           (array64 c.pScore sc ⋆
           (array (t := i32) c.pPos ps ⋆
           (array (t := i32) c.pReason rs ⋆
           (array (t := i32) c.pLevel lv ⋆
           (array (t := i8) c.pPhases ph ⋆
           (array (t := i8) c.pMark mk ⋆
           (array (t := i8) c.pVals vl ⋆
           (array (t := i32) c.pWvec wv ⋆
           (M7MemInitRest c s ⋆ R)))))))))) m) :
    (FullMem c {
      core := { s.core with
        wvec := wv, vals := vl, mrk := mk, flags := fl, lvl := lv, rsns := rs },
      scratch := { s.scratch with phases := ph, pos := ps, score := sc } } ⋆ R) m := by
  let s' : FullState := {
    core := { s.core with
      wvec := wv, vals := vl, mrk := mk, flags := fl, lvl := lv, rsns := rs },
    scratch := { s.scratch with phases := ph, pos := ps, score := sc } }
  have hm_eq : M7MemInitRest c s = M7MemInitRest c s' := rfl
  rw [hm_eq] at hm
  exact unfocus_init_var (s' := s') hm

/-- `full_init_fresh_var_m7` (`FullM7BvaFactor.m7InitFreshVarFn`, the `"full_init_fresh_var"`
row of the Step-6/7 fidelity environment) satisfies `step7InitFreshVarSpec`: the M7
`fullInitFreshVarHeapSpec` contract plus `res_sz` preservation. -/
theorem full_init_fresh_var_m7_step7_wp (Γ : Env) :
    ∀ args m Q X, step7InitFreshVarSpec args m Q X →
      Func.wp Γ FullM7BvaFactor.full_init_fresh_var_m7_body args m Q X := by
  intro (h, fv, ()) m Q X ⟨c, s, R, hh, hslen, hfv_lt, hm, hQ⟩
  subst hh
  have hclen := hslen.core_ok; have hcv_le := hclen.cur_vars_le
  have hmx : c.max_vars < 2 * 2 ^ 28 := by simpa only [dimacsBound] using c.hmaxv
  unfold Func.wp FullM7BvaFactor.full_init_fresh_var_m7_body; dsimp only
  c0_hsteps
  replace hm := focus_init hm
  have hw0 := bv64_shl2_fv_toNat fv; have hw1 := bv64_shl2_add1_fv_toNat fv
  have hw2 := bv64_shl2_add2_fv_toNat fv; have hw3 := bv64_shl2_add3_fv_toNat fv
  have hvl0 := bv64_shl1_fv_toNat fv; have hvl1 := bv64_shl1_or1_fv_toNat fv
  have h_fv_eq := bv64_setWidth_32 fv
  have h_wvec_lt0 : (BitVec.setWidth 64 fv <<< (2 : Nat)).toNat < s.core.wvec.length := by
    rw [hw0, hclen.wvec_len]; omega
  have h_wvec_lt1 : ((BitVec.setWidth 64 fv <<< (2 : Nat)) + 1#64).toNat <
      s.core.wvec.length := by
    rw [hw1, hclen.wvec_len]; omega
  have h_wvec_lt2 : ((BitVec.setWidth 64 fv <<< (2 : Nat)) + 2#64).toNat <
      s.core.wvec.length := by
    rw [hw2, hclen.wvec_len]; omega
  have h_wvec_lt3 : ((BitVec.setWidth 64 fv <<< (2 : Nat)) + 3#64).toNat <
      s.core.wvec.length := by
    rw [hw3, hclen.wvec_len]; omega
  have h_vals_lt0 : (BitVec.setWidth 64 fv <<< (1 : Nat)).toNat < s.core.vals.length := by
    rw [hvl0, hclen.vals_len]; omega
  have h_vals_lt1 : ((BitVec.setWidth 64 fv <<< (1 : Nat)) ||| 1#64).toNat <
      s.core.vals.length := by
    rw [hvl1, hclen.vals_len]; omega
  have h_fv_mrk : (BitVec.setWidth 64 fv).toNat < s.core.mrk.length := by
    rw [bv64_setWidth_32, hclen.mrk_len]; omega
  have h_fv_ph : (BitVec.setWidth 64 fv).toNat < s.scratch.phases.length := by
    rw [bv64_setWidth_32, hslen.scratch_ok.phases_len]; omega
  have h_fv_lvl : (BitVec.setWidth 64 fv).toNat < s.core.lvl.length := by
    rw [bv64_setWidth_32, hclen.lvl_len]; omega
  have h_fv_rsns : (BitVec.setWidth 64 fv).toNat < s.core.rsns.length := by
    rw [bv64_setWidth_32, hclen.rsns_len]; omega
  have h_fv_pos : (BitVec.setWidth 64 fv).toNat < s.scratch.pos.length := by
    rw [bv64_setWidth_32, hslen.scratch_ok.pos_len]; omega
  have h_fv_sc : (BitVec.setWidth 64 fv).toNat < s.scratch.score.length := by
    rw [bv64_setWidth_32, hslen.scratch_ok.score_len]; omega
  have h_fv_fl : (BitVec.setWidth 64 fv).toNat < s.core.flags.length := by
    rw [bv64_setWidth_32, hclen.flags_len]; omega
  have h_fv_qp : (BitVec.setWidth 64 fv).toNat < s.scratch.q_prev.length := by
    rw [bv64_setWidth_32, hslen.scratch_ok.q_prev_len]; omega
  c0_hsteps_nogrp
  simp only [sep_emp] at hm
  replace hm := unfocus_init hm
  have hfl_val : ((1 : BitVec 32) ||| 8 ||| 16 ||| 1024 ||| 32 ||| 64 |||
      128 ||| 256 ||| 512) = 2041#32 := by decide
  c0_hsteps_nogrp
  c0_hstep
  c0_hsplit
  · have hold_lt : (BitVec.setWidth 32 s.scratch.q_first).toNat < s.core.cur_vars := by
      have h1 : (BitVec.setWidth 64 (BitVec.setWidth 32 s.scratch.q_first)).toNat <
          s.core.cur_vars % 2 ^ 64 := by assumption
      rw [bv64_setWidth_32] at h1
      omega
    have h_fv_qn : (BitVec.setWidth 64 fv).toNat < s.scratch.q_next.length := by
      rw [bv64_setWidth_32, hslen.scratch_ok.q_next_len]; omega
    have h_old_qp : (BitVec.setWidth 64 (BitVec.setWidth 32 s.scratch.q_first)).toNat <
        (s.scratch.q_prev.set (BitVec.setWidth 64 fv).toNat 0xFFFFFFFF#32).length := by
      rw [List.length_set, bv64_setWidth_32, hslen.scratch_ok.q_prev_len]; omega
    have h_fv_qs : (BitVec.setWidth 64 fv).toNat < s.scratch.q_stamp.length := by
      rw [bv64_setWidth_32, hslen.scratch_ok.q_stamp_len]; omega
    c0_hsteps
    dsimp only at hm
    simp only [hw0, bv64_shl2_add1_fv_ofNat fv, bv64_shl2_add2_fv_ofNat fv,
      bv64_shl2_add3_fv_ofNat fv, hvl0, bv64_shl1_or1_fv_ofNat fv, h_fv_eq, hfl_val] at hm
    let sc' : FullScratch := { s.scratch with
      q_first := BitVec.setWidth 64 fv,
      phases := s.scratch.phases.set fv.toNat 1#8,
      pos := s.scratch.pos.set fv.toNat 0xFFFFFFFF#32,
      q_prev := (s.scratch.q_prev.set fv.toNat 0xFFFFFFFF#32).set
        (BitVec.setWidth 64 (BitVec.setWidth 32 s.scratch.q_first)).toNat fv,
      q_next := s.scratch.q_next.set fv.toNat (BitVec.setWidth 32 s.scratch.q_first),
      q_stamp := s.scratch.q_stamp.set fv.toNat 0#32,
      score := s.scratch.score.set fv.toNat 0#64 }
    exact m7InitFreshVar_post hfv_lt hclen hslen.scratch_ok hcv_le sc'
      (m7InitFreshVar_sc_ok hslen.scratch_ok (BitVec.setWidth 64 fv) s.scratch.q_last
        (s.scratch.phases.set fv.toNat 1#8) (s.scratch.pos.set fv.toNat 0xFFFFFFFF#32)
        ((s.scratch.q_prev.set fv.toNat 0xFFFFFFFF#32).set
          (BitVec.setWidth 64 (BitVec.setWidth 32 s.scratch.q_first)).toNat fv)
        (s.scratch.q_next.set fv.toNat (BitVec.setWidth 32 s.scratch.q_first))
        (s.scratch.q_stamp.set fv.toNat 0#32) (s.scratch.score.set fv.toNat 0#64)
        (by simp [hslen.scratch_ok.phases_len]) (by simp [hslen.scratch_ok.pos_len])
        (by simp [hslen.scratch_ok.q_prev_len]) (by simp [hslen.scratch_ok.q_next_len])
        (by simp [hslen.scratch_ok.q_stamp_len]) (by simp [hslen.scratch_ok.score_len]))
      rfl rfl rfl rfl rfl rfl rfl rfl hm hQ
  · have h_fv_qn : (BitVec.setWidth 64 fv).toNat < s.scratch.q_next.length := by
      rw [bv64_setWidth_32, hslen.scratch_ok.q_next_len]; omega
    have h_fv_qs : (BitVec.setWidth 64 fv).toNat < s.scratch.q_stamp.length := by
      rw [bv64_setWidth_32, hslen.scratch_ok.q_stamp_len]; omega
    c0_hsteps
    dsimp only at hm
    simp only [hw0, bv64_shl2_add1_fv_ofNat fv, bv64_shl2_add2_fv_ofNat fv,
      bv64_shl2_add3_fv_ofNat fv, hvl0, bv64_shl1_or1_fv_ofNat fv, h_fv_eq, hfl_val] at hm
    let sc' : FullScratch := { s.scratch with
      q_first := BitVec.setWidth 64 fv,
      q_last := BitVec.setWidth 64 fv,
      phases := s.scratch.phases.set fv.toNat 1#8,
      pos := s.scratch.pos.set fv.toNat 0xFFFFFFFF#32,
      q_prev := s.scratch.q_prev.set fv.toNat 0xFFFFFFFF#32,
      q_next := s.scratch.q_next.set fv.toNat 0xFFFFFFFF#32,
      q_stamp := s.scratch.q_stamp.set fv.toNat 0#32,
      score := s.scratch.score.set fv.toNat 0#64 }
    exact m7InitFreshVar_post hfv_lt hclen hslen.scratch_ok hcv_le sc'
      (m7InitFreshVar_sc_ok hslen.scratch_ok (BitVec.setWidth 64 fv) (BitVec.setWidth 64 fv)
        (s.scratch.phases.set fv.toNat 1#8) (s.scratch.pos.set fv.toNat 0xFFFFFFFF#32)
        (s.scratch.q_prev.set fv.toNat 0xFFFFFFFF#32)
        (s.scratch.q_next.set fv.toNat 0xFFFFFFFF#32)
        (s.scratch.q_stamp.set fv.toNat 0#32) (s.scratch.score.set fv.toNat 0#64)
        (by simp [hslen.scratch_ok.phases_len]) (by simp [hslen.scratch_ok.pos_len])
        (by simp [hslen.scratch_ok.q_prev_len]) (by simp [hslen.scratch_ok.q_next_len])
        (by simp [hslen.scratch_ok.q_stamp_len]) (by simp [hslen.scratch_ok.score_len]))
      rfl rfl rfl rfl rfl rfl rfl rfl hm hQ

end M7InitFreshVar

end LeanQbe.T.Examples.Kissat.FullFidelityStep7

end
