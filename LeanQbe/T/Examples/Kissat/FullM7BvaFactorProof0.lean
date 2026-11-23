module

public import LeanQbe.T.Examples.Kissat.FullM7BvaFactor
public import LeanQbe.T.Examples.Kissat.FullM4BvaLemmas1
import LeanQbe.T.Examples.Kissat.FullBvaFwdLemmas1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat M7 BVA/Factor Proofs — Part 0 (`init_fresh_var` & `bva_try_lit`)

Proves M1-clean (`0` `import all`, `0` `sorry`/`bv_decide`/`maxHeartbeats`) parametric `(Γ : Env)`
`Func.wp` contracts for:
1. `FullM7BvaFactor.full_init_fresh_var_m7_body`:
   - `full_init_fresh_var_m7_heap_wp` → `FullBvaHeap.fullInitFreshVarHeapSpec`
     (`2041#32` flags + **`q_first`** VMTF head enqueue, fresh variables decided last)
   - `full_init_fresh_var_m7_wp` → `Full.fullInitFreshVarSpec`
2. `FullM7BvaFactor.full_bva_try_lit_m7_body`:
   - `full_bva_try_lit_m7_wp` → `FullBvaHeap.fullBvaTryLitHeapSpec`
     (`factorsize = 5`, `red > h->elim_bound`, `256 x 32` matrix, touched-lit `work_stk2`)
-/

set_option autoImplicit false

public section

local elab "c0_hfast_nogrp" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, pruneJnz := false } 10000

namespace LeanQbe.T.Examples.Kissat.FullM7BvaFactor

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

private theorem bv64_shl1_lit_toNat (f0 : BitVec 32) :
    (BitVec.setWidth 64 f0 <<< 1#64).toNat = 2 * f0.toNat := by
  simp [BitVec.toNat_shiftLeft]; omega

private theorem bv64_shl1_lit_add1_toNat (f0 : BitVec 32) :
    ((BitVec.setWidth 64 f0 <<< 1#64) + 1#64).toNat = 2 * f0.toNat + 1 := by
  simp [BitVec.toNat_add, BitVec.toNat_shiftLeft]; omega

/-! ## 1. `full_init_fresh_var_m7` (`2041#32` Flags + `q_first` VMTF Enqueue) -/

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
  refine hQ _ _ _ _ _ _ _ sc' m' hlen' ⟨hll, hel⟩ hsb hws htm htr hsig
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

/-- `full_init_fresh_var_m7` satisfies `FullBvaHeap.fullInitFreshVarHeapSpec`
(`2041#32` flags + `q_first` VMTF head enqueue). -/
theorem full_init_fresh_var_m7_heap_wp (Γ : Env) :
    ∀ args m Q X, fullInitFreshVarHeapSpec args m Q X →
      Func.wp Γ full_init_fresh_var_m7_body args m Q X := by
  intro (h, fv, ()) m Q X ⟨c, s, R, hh, hslen, hfv_lt, hm, hQ⟩
  subst hh
  have hclen := hslen.core_ok; have hcv_le := hclen.cur_vars_le
  have hmx : c.max_vars < 2 * 2 ^ 28 := by simpa only [dimacsBound] using c.hmaxv
  unfold Func.wp full_init_fresh_var_m7_body; dsimp only
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
      rfl rfl rfl rfl rfl rfl rfl hm hQ
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
      rfl rfl rfl rfl rfl rfl rfl hm hQ

/-- Canonical `Full.fullInitFreshVarSpec` corollary for `full_init_fresh_var_m7`. -/
theorem full_init_fresh_var_m7_wp (Γ : Env) :
    ∀ args m Q X, Full.fullInitFreshVarSpec args m Q X →
      Func.wp Γ full_init_fresh_var_m7_body args m Q X := by
  intro (h, fv, ()) m Q X ⟨c, s, R, hh, hslen, hfv_lt, hm, hQ⟩
  exact full_init_fresh_var_m7_heap_wp Γ _ m Q X
    ⟨c, s, R, hh, hslen, hfv_lt, hm,
      fun vals' mrk' flags' lvl' rsns' wvec' unass' sc' m' hlen' hexts hsb _ _ _ _
          hv0 hv1 hvs hm0 hms hl0 hls hr0 hrs hw0 hws hm' =>
        hQ vals' mrk' flags' lvl' rsns' wvec' unass' sc' m' hlen' hexts hsb
          hv0 hv1 hvs hm0 hms hl0 hls hr0 hrs hw0 hws hm'⟩

end M7InitFreshVar

/-! ## 2. Matrix, `lit_mark`, and Touched-Lit Helpers for `full_bva_try_lit_m7` -/

section M7TryLitHelpers

private theorem m7BvaRowEntryOk_congr {F_cur : List (List Nat)} {s s' : FullState}
    {fr : Nat} {w : BitVec 32} {res : List Nat} (hcv : s'.core.cur_vars = s.core.cur_vars)
    (har : s'.core.arena = s.core.arena) (hal : s'.core.arena_len = s.core.arena_len)
    (h : M4BvaRowEntryOk F_cur s fr w res) : M4BvaRowEntryOk F_cur s' fr w res := by
  unfold M4BvaRowEntryOk at h ⊢
  by_cases hbin : (w &&& 0x80000000#32) ≠ 0#32
  · rw [ite_eq_left hbin] at h ⊢; rwa [hcv]
  · rw [ite_eq_right hbin] at h ⊢
    simp only [fullArenaClauseRefs, fullArenaClauseGarb, fullArenaClauseSize,
      fullArenaClauseLits, fullArenaClauseRefsCore, fullArenaClauseGarbCore,
      fullArenaClauseSizeCore, fullArenaClauseLitsCore, fullArenaHdrCore, har, hal] at h ⊢
    exact h

private theorem m7BvaMatrixInv_congr {c : FullCfg} {F_cur : List (List Nat)} {s s' : FullState}
    {step : Nat} (hcv : s'.core.cur_vars = s.core.cur_vars)
    (har : s'.core.arena = s.core.arena) (hal : s'.core.arena_len = s.core.arena_len)
    (hsb : s'.scratch.scratch_buf = s.scratch.scratch_buf)
    (h : M4BvaMatrixInv c F_cur s step) : M4BvaMatrixInv c F_cur s' step := by
  refine ⟨h.1, h.2.1, h.2.2.1, fun r hr => ?_⟩
  obtain ⟨hfr, hq2, hq256, hm⟩ := h.2.2.2 r hr
  refine ⟨by rw [hsb, hcv]; exact hfr, by rw [hsb]; exact hq2, by rw [hsb]; exact hq256,
    fun m hm_lt => ?_⟩
  rw [hsb] at hm_lt
  obtain ⟨res, hres_lt, hres_nd, hok, hent, hpar⟩ := hm m hm_lt
  refine ⟨res, fun x hx => by rw [hcv]; exact hres_lt x hx, hres_nd, ?_, ?_, ?_⟩
  · rw [hsb]; exact m7BvaRowEntryOk_congr hcv har hal hok
  · intro t ht; rw [hsb]; exact hent t ht
  · intro hr0; rw [hsb]; obtain ⟨hpi, hpok⟩ := hpar hr0
    exact ⟨hpi, m7BvaRowEntryOk_congr hcv har hal hpok⟩

private theorem m7_bv32_bin_flag_zero_of_lt {x : BitVec 32} (h : x.toNat < 2 ^ 31) :
    (x &&& 0x80000000#32) = 0#32 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (0x80000000#32).toNat = 2 ^ 31 from rfl,
    show (0#32).toNat = 0 from rfl]
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_and, Nat.zero_testBit, Nat.testBit_two_pow]
  by_cases hk : k = 31
  · subst hk; simp [Nat.testBit_lt_two_pow h]
  · simp [Ne.symm hk]

private theorem m7BvaRowEntryOk_of_large_f0 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {cr f0 : BitVec 32} (href : cr.toNat ∈ fullArenaClauseRefsCore s.core)
    (hng : fullArenaClauseGarbCore s.core cr.toNat = false)
    (hsz3 : 3 ≤ fullArenaClauseSizeCore s.core cr.toNat)
    (hsz5 : fullArenaClauseSizeCore s.core cr.toNat ≤ 5)
    (hf0_mem : f0.toNat ∈ fullArenaClauseLitsCore s.core cr.toNat) :
    ∃ res : List Nat,
      (∀ x ∈ res, x < 2 * s.core.cur_vars) ∧ (res.map (· / 2)).Nodup ∧
      M4BvaRowEntryOk F_cur s f0.toNat cr res ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause (f0.toNat :: res)) := by
  let C := fullArenaClauseLitsCore s.core cr.toNat
  let res := C.filter (· != f0.toNat)
  have hC_lt := hinv.2.1.arena.lits_lt cr.toNat href hng
  have hC_nd_vars : (C.map (· / 2)).Nodup := hinv.2.2.2.1 cr.toNat href hng
  have hC_nd : C.Nodup := nodup_of_map_div2 hC_nd_vars
  have hC_ent := hinv.2.1.arena.entails cr.toNat href hng
  have hres_sub : res.Sublist C := List.filter_sublist
  have hres_nd : (res.map (· / 2)).Nodup := hC_nd_vars.sublist (hres_sub.map _)
  have hres_lt : ∀ x ∈ res, x < 2 * s.core.cur_vars := fun x hx => hC_lt x (hres_sub.subset hx)
  have hperm_er : res.Perm (C.erase f0.toNat) := by
    have hp := (List.perm_cons_erase hf0_mem).filter (· != f0.toNat)
    have he : (f0.toNat :: C.erase f0.toNat).filter (· != f0.toNat) = C.erase f0.toNat := by
      simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      exact List.filter_eq_self.mpr fun y hy => by
        have hne : y ≠ f0.toNat := fun h => by
          subst h
          exact (List.nodup_cons.mp (hC_nd.perm (List.perm_cons_erase hf0_mem))).1 hy
        simp [hne]
    rwa [he] at hp
  have hC_perm : C.Perm (f0.toNat :: res) :=
    (List.perm_cons_erase hf0_mem).trans (hperm_er.symm.cons f0.toNat)
  have hcr_not_bin : (cr &&& 0x80000000#32) = 0#32 := by
    have hwf := hinv.2.1.arena.refs_wf cr.toNat href
    have hal := hinv.1.core_ok.arena_len_le
    have hab := c.harena; unfold dimacsBound at hab
    exact m7_bv32_bin_flag_zero_of_lt (by omega)
  refine ⟨res, hres_lt, hres_nd, ?_, clause_entails_of_perm hC_perm hC_ent⟩
  unfold M4BvaRowEntryOk; rw [ite_eq_right (fun h' => h' hcr_not_bin)]
  exact ⟨href, hng, hsz3, by
    change fullArenaClauseSizeCore s.core cr.toNat ≤ 256; omega,
    hf0_mem, List.Perm.refl _, hC_perm⟩

private theorem m7BvaMatrixInv_step1 {c : FullCfg} {F_cur : List (List Nat)} {s : FullState}
    {sb : List (BitVec 32)} {f0 qn : BitVec 32}
    (hcap : 16448 ≤ c.scratch_cap) (hsb_len : sb.length = c.scratch_cap)
    (hf0_lt : f0.toNat < 2 * s.core.cur_vars) (hq2 : 2 ≤ qn.toNat) (hq256 : qn.toNat ≤ 256)
    (hrow0 : ∀ m < qn.toNat, ∃ res : List Nat,
      (∀ x ∈ res, x < 2 * s.core.cur_vars) ∧ (res.map (· / 2)).Nodup ∧
      M4BvaRowEntryOk F_cur s f0.toNat (sb[64 + m]?.getD 0#32) res ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause (f0.toNat :: res))) :
    M4BvaMatrixInv c F_cur
      { s with scratch := { s.scratch with scratch_buf := (sb.set 0 f0).set 32 qn } } 1 := by
  let sb1 := (sb.set 0 f0).set 32 qn
  have h0 : sb1[0]?.getD 0#32 = f0 := by
    dsimp only [sb1]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega),
      Option.getD_some]
  have h32 : sb1[32]?.getD 0#32 = qn := by
    dsimp only [sb1]; rw [List.getElem?_set_self (by simp [hsb_len]; omega), Option.getD_some]
  have h64 : ∀ m < 256, sb1[64 + m]?.getD 0#32 = sb[64 + m]?.getD 0#32 := fun m _ => by
    dsimp only [sb1]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  refine ⟨hcap, Nat.le_refl 1, by omega, fun r hr => ?_⟩
  have hr0 : r = 0 := by omega
  subst hr0; dsimp only; rw [h0, h32]
  refine ⟨hf0_lt, hq2, hq256, fun m hm => ?_⟩
  obtain ⟨res, hres_lt, hres_nd, hok, hent⟩ := hrow0 m hm
  refine ⟨res, hres_lt, hres_nd, ?_, fun t ht => ?_, fun h => by omega⟩
  · rw [show 64 + 0 * 256 + m = 64 + m by omega, h64 m (by omega)]
    exact m7BvaRowEntryOk_congr rfl rfl rfl hok
  · have ht0 : t = 0 := by omega
    subst ht0; rw [h0]; exact hent

private theorem m7BvaMatrixInv_extend_step {c : FullCfg} {F_cur : List (List Nat)} {s : FullState}
    {sb' : List (BitVec 32)} {step : Nat} {best_lit new_qn : BitVec 32}
    (hstep1 : 1 ≤ step) (hstep32 : step < 32)
    (hmat : M4BvaMatrixInv c F_cur s step)
    (hsb'_len : sb'.length = c.scratch_cap)
    (hbest_lt : best_lit.toNat < 2 * s.core.cur_vars)
    (hnq2 : 2 ≤ new_qn.toNat) (hnq256 : new_qn.toNat ≤ 256)
    (hpres : ∀ idx < c.scratch_cap,
      ¬ (64 + step * 256 ≤ idx ∧ idx < 64 + step * 256 + 256) →
      ¬ (8256 + step * 256 ≤ idx ∧ idx < 8256 + step * 256 + 256) →
      sb'[idx]? = s.scratch.scratch_buf[idx]?)
    (hnew : ∀ nm < new_qn.toNat,
      let pi := (sb'[8256 + step * 256 + nm]?.getD 0#32).toNat
      pi < (s.scratch.scratch_buf[32 + (step - 1)]?.getD 0#32).toNat ∧
      ∃ res : List Nat,
        (∀ x ∈ res, x < 2 * s.core.cur_vars) ∧ (res.map (· / 2)).Nodup ∧
        M4BvaRowEntryOk F_cur s (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat
          (s.scratch.scratch_buf[64 + (step - 1) * 256 + pi]?.getD 0#32) res ∧
        M4BvaRowEntryOk F_cur s best_lit.toNat (sb'[64 + step * 256 + nm]?.getD 0#32) res ∧
        (∀ t < step, (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s.scratch.scratch_buf[t]?.getD 0#32).toNat :: res))) ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause (best_lit.toNat :: res))) :
    M4BvaMatrixInv c F_cur
      { s with scratch := { s.scratch with
          scratch_buf := (sb'.set step best_lit).set (32 + step) new_qn } }
      (step + 1) := by
  have hcap := hmat.1
  let sb2 := (sb'.set step best_lit).set (32 + step) new_qn
  have hget_lt : ∀ idx < c.scratch_cap, idx ≠ step → idx ≠ 32 + step →
      ¬ (64 + step * 256 ≤ idx ∧ idx < 64 + step * 256 + 256) →
      ¬ (8256 + step * 256 ≤ idx ∧ idx < 8256 + step * 256 + 256) →
      sb2[idx]? = s.scratch.scratch_buf[idx]? := fun idx hi h1 h2 h3 h4 => by
    dsimp only [sb2]
    rw [List.getElem?_set_ne (Ne.symm h2), List.getElem?_set_ne (Ne.symm h1)]
    exact hpres idx hi h3 h4
  have hget_step : sb2[step]?.getD 0#32 = best_lit := by
    dsimp only [sb2]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega), Option.getD_some]
  have hget_32step : sb2[32 + step]?.getD 0#32 = new_qn := by
    dsimp only [sb2]
    rw [List.getElem?_set_self (by simp [hsb'_len]; omega), Option.getD_some]
  have hget_row : ∀ nm < 256, sb2[64 + step * 256 + nm]? = sb'[64 + step * 256 + nm]? :=
    fun nm _ => by
      dsimp only [sb2]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  have hget_par : ∀ nm < 256, sb2[8256 + step * 256 + nm]? = sb'[8256 + step * 256 + nm]? :=
    fun nm _ => by
      dsimp only [sb2]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  refine ⟨hcap, by omega, by omega, fun r hr => ?_⟩
  by_cases hre : r < step
  · obtain ⟨hfr, hq2, hq256, hm⟩ := hmat.2.2.2 r hre
    have hfr_eq : sb2[r]? = s.scratch.scratch_buf[r]? :=
      hget_lt r (by omega) (by omega) (by omega) (by omega) (by omega)
    have hqn_eq : sb2[32 + r]? = s.scratch.scratch_buf[32 + r]? :=
      hget_lt (32 + r) (by omega) (by omega) (by omega) (by omega) (by omega)
    dsimp only; rw [hfr_eq, hqn_eq]
    refine ⟨hfr, hq2, hq256, fun m hm_lt => ?_⟩
    obtain ⟨res, hres_lt, hres_nd, hok, hent, hpar⟩ := hm m hm_lt
    have hcell_eq : sb2[64 + r * 256 + m]? = s.scratch.scratch_buf[64 + r * 256 + m]? :=
      hget_lt (64 + r * 256 + m) (by omega) (by omega) (by omega) (by omega) (by omega)
    refine ⟨res, hres_lt, hres_nd, ?_, fun t ht => ?_, fun hr0 => ?_⟩
    · rw [hcell_eq]; exact m7BvaRowEntryOk_congr rfl rfl rfl hok
    · rw [hget_lt t (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hent t ht
    · obtain ⟨hpi, hpok⟩ := hpar hr0
      have hpar_eq : sb2[8256 + r * 256 + m]? = s.scratch.scratch_buf[8256 + r * 256 + m]? :=
        hget_lt (8256 + r * 256 + m) (by omega) (by omega) (by omega) (by omega) (by omega)
      have hqprev_eq : sb2[32 + (r - 1)]? = s.scratch.scratch_buf[32 + (r - 1)]? :=
        hget_lt (32 + (r - 1)) (by omega) (by omega) (by omega) (by omega) (by omega)
      have hfprev_eq : sb2[r - 1]? = s.scratch.scratch_buf[r - 1]? :=
        hget_lt (r - 1) (by omega) (by omega) (by omega) (by omega) (by omega)
      have hcprev_eq : sb2[64 + (r - 1) * 256 + (s.scratch.scratch_buf[8256 + r * 256 + m]?.getD
          0#32).toNat]? = s.scratch.scratch_buf[64 + (r - 1) * 256 +
          (s.scratch.scratch_buf[8256 + r * 256 + m]?.getD 0#32).toNat]? := by
        have hqprev256 := (hmat.2.2.2 (r - 1) (by omega)).2.2.1
        exact hget_lt _ (by omega) (by omega) (by omega) (by omega) (by omega)
      rw [hpar_eq, hqprev_eq, hfprev_eq, hcprev_eq]
      exact ⟨hpi, m7BvaRowEntryOk_congr rfl rfl rfl hpok⟩
  · have hreq : r = step := by omega
    subst r; dsimp only; rw [hget_step, hget_32step]
    refine ⟨hbest_lt, hnq2, hnq256, fun nm hnm => ?_⟩
    obtain ⟨hpi, res, hres_lt, hres_nd, hpok, hok, hent_lt, hent_b⟩ := hnew nm hnm
    refine ⟨res, hres_lt, hres_nd, ?_, fun t ht => ?_, fun _ => ?_⟩
    · rw [hget_row nm (by omega)]; exact m7BvaRowEntryOk_congr rfl rfl rfl hok
    · by_cases hte : t < step
      · rw [hget_lt t (by omega) (by omega) (by omega) (by omega) (by omega)]
        exact hent_lt t hte
      · have hts : t = step := by omega
        subst hts; rw [hget_step]; exact hent_b
    · have hqprev256 := (hmat.2.2.2 (step - 1) (by omega)).2.2.1
      have hpar_eq := hget_par nm (by omega)
      have hqprev_eq : sb2[32 + (step - 1)]? = s.scratch.scratch_buf[32 + (step - 1)]? :=
        hget_lt (32 + (step - 1)) (by omega) (by omega) (by omega) (by omega) (by omega)
      have hfprev_eq : sb2[step - 1]? = s.scratch.scratch_buf[step - 1]? :=
        hget_lt (step - 1) (by omega) (by omega) (by omega) (by omega) (by omega)
      have hcprev_eq : sb2[64 + (step - 1) * 256 +
          (sb'[8256 + step * 256 + nm]?.getD 0#32).toNat]? =
          s.scratch.scratch_buf[64 + (step - 1) * 256 +
            (sb'[8256 + step * 256 + nm]?.getD 0#32).toNat]? :=
        hget_lt _ (by omega) (by omega) (by omega) (by omega) (by omega)
      rw [hpar_eq, hqprev_eq, hfprev_eq, hcprev_eq]
      exact ⟨hpi, m7BvaRowEntryOk_congr rfl rfl rfl hpok⟩

private theorem m7BvaMatrixInv_of_filter_pres {c : FullCfg} {F_cur : List (List Nat)}
    {s : FullState} {sb' : List (BitVec 32)} {step : Nat} (hstep32 : step < 32)
    (hmat : M4BvaMatrixInv c F_cur s step)
    (hpres : ∀ idx < c.scratch_cap,
      ¬ (64 + step * 256 ≤ idx ∧ idx < 64 + step * 256 + 256) →
      ¬ (8256 + step * 256 ≤ idx ∧ idx < 8256 + step * 256 + 256) →
      sb'[idx]? = s.scratch.scratch_buf[idx]?) :
    M4BvaMatrixInv c F_cur { s with scratch := { s.scratch with scratch_buf := sb' } } step := by
  have hcap := hmat.1
  refine ⟨hcap, hmat.2.1, hmat.2.2.1, fun r hr => ?_⟩
  obtain ⟨hfr, hq2, hq256, hm⟩ := hmat.2.2.2 r hr
  have hr_eq : sb'[r]? = s.scratch.scratch_buf[r]? :=
    hpres r (by omega) (by omega) (by omega)
  have h32_eq : sb'[32 + r]? = s.scratch.scratch_buf[32 + r]? :=
    hpres (32 + r) (by omega) (by omega) (by omega)
  dsimp only; rw [hr_eq, h32_eq]
  refine ⟨hfr, hq2, hq256, fun m hm_lt => ?_⟩
  obtain ⟨res, hres_lt, hres_nd, hok, hent, hpar⟩ := hm m hm_lt
  have hc_eq : sb'[64 + r * 256 + m]? = s.scratch.scratch_buf[64 + r * 256 + m]? :=
    hpres (64 + r * 256 + m) (by omega) (by omega) (by omega)
  refine ⟨res, hres_lt, hres_nd, ?_, fun t ht => ?_, fun hr0 => ?_⟩
  · rw [hc_eq]; exact m7BvaRowEntryOk_congr rfl rfl rfl hok
  · rw [hpres t (by omega) (by omega) (by omega)]; exact hent t ht
  · obtain ⟨hpi, hpok⟩ := hpar hr0
    have hp_eq : sb'[8256 + r * 256 + m]? = s.scratch.scratch_buf[8256 + r * 256 + m]? :=
      hpres (8256 + r * 256 + m) (by omega) (by omega) (by omega)
    have hqprev256 := (hmat.2.2.2 (r - 1) (by omega)).2.2.1
    rw [hp_eq, hpres (32 + (r - 1)) (by omega) (by omega) (by omega),
      hpres (r - 1) (by omega) (by omega) (by omega),
      hpres (64 + (r - 1) * 256 + (s.scratch.scratch_buf[8256 + r * 256 + m]?.getD 0#32).toNat)
        (by omega) (by omega) (by omega)]
    exact ⟨hpi, m7BvaRowEntryOk_congr rfl rfl rfl hpok⟩

private theorem m7_bva_try_lit_clear_lm_step {sb : List (BitVec 32)} {lmi : List (BitVec 8)}
    {maxv si stepf : Nat} (hsi_lt : si < stepf) (hsi_sb : si < sb.length)
    (hlmi_l : lmi.length = 2 * maxv)
    (hxl_lt : (sb[si]'hsi_sb).toNat < 2 * maxv)
    (hlmi_hi : ∀ l < 2 * maxv, (lmi[l]?.getD 0#8 &&& 0xFE#8) = 0#8)
    (hlmi_only : ∀ l < 2 * maxv, (lmi[l]?.getD 0#8 &&& 1#8) ≠ 0#8 →
      ∃ r, si ≤ r ∧ r < stepf ∧ (sb[r]?.getD 0#32).toNat = l) :
    let xl := (sb[si]'hsi_sb).toNat
    let lmi' := lmi.set xl ((lmi[xl]'(by omega)) &&& 0xFE#8)
    (∀ l < 2 * maxv, (lmi'[l]?.getD 0#8 &&& 0xFE#8) = 0#8) ∧
    (∀ l < 2 * maxv, (lmi'[l]?.getD 0#8 &&& 1#8) ≠ 0#8 →
      ∃ r, si + 1 ≤ r ∧ r < stepf ∧ (sb[r]?.getD 0#32).toNat = l) := by
  intro xl lmi'
  refine ⟨fun l hl => ?_, fun l hl hne => ?_⟩
  · dsimp only [lmi']
    by_cases hlx : l = xl
    · subst hlx; rw [List.getElem?_set_self (by omega), Option.getD_some]
      have h0 := hlmi_hi xl hl
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h0
      rw [BitVec.and_assoc, show (0xFE#8 &&& 0xFE#8) = 0xFE#8 from by decide]; exact h0
    · rw [List.getElem?_set_ne (Ne.symm hlx)]; exact hlmi_hi l hl
  · dsimp only [lmi'] at hne
    by_cases hlx : l = xl
    · subst hlx; rw [List.getElem?_set_self (by omega), Option.getD_some] at hne
      rw [BitVec.and_assoc, show (0xFE#8 &&& 1#8) = 0#8 from by decide,
        BitVec.and_zero] at hne
      exact absurd rfl hne
    · rw [List.getElem?_set_ne (Ne.symm hlx)] at hne
      obtain ⟨r, hr1, hr2, heq⟩ := hlmi_only l hl hne
      have hne_r : r ≠ si := fun h => by
        subst h; dsimp only [xl] at hlx
        rw [List.getElem?_eq_getElem hsi_sb, Option.getD_some] at heq
        exact hlx heq.symm
      exact ⟨r, by omega, hr2, heq⟩

private theorem m7_bva_try_lit_clear_lm_done {c : FullCfg} {stf : FullState}
    {lmi : List (BitVec 8)} {stepf : Nat}
    (hmrk : ∀ v < c.max_vars, stf.core.mrk[v]?.getD 0#8 = 0#8)
    (hlmi_hi : ∀ l < 2 * c.max_vars, (lmi[l]?.getD 0#8 &&& 0xFE#8) = 0#8)
    (hlmi_only : ∀ l < 2 * c.max_vars, (lmi[l]?.getD 0#8 &&& 1#8) ≠ 0#8 →
      ∃ r, stepf ≤ r ∧ r < stepf ∧ (stf.scratch.scratch_buf[r]?.getD 0#32).toNat = l) :
    FullLitMarksClear c { stf with core := { stf.core with lit_mark := lmi } } := by
  refine ⟨hmrk, fun l hl => ?_⟩
  have hhi := hlmi_hi l hl
  have hlo : (lmi[l]?.getD 0#8 &&& 1#8) = 0#8 := by
    apply Classical.byContradiction; intro hne
    obtain ⟨r, hr1, hr2, _⟩ := hlmi_only l hl hne; omega
  have hcomb : (lmi[l]?.getD 0#8 &&& 0xFE#8) ||| (lmi[l]?.getD 0#8 &&& 1#8) =
      lmi[l]?.getD 0#8 := by
    rw [← BitVec.and_or_distrib_left,
      show (0xFE#8 ||| 1#8) = 0xFF#8 from by decide,
      show ∀ x : BitVec 8, x &&& 0xFF#8 = x from fun x => by
        apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_and]
        have := x.isLt; exact Nat.and_two_pow_sub_one_eq_mod x.toNat 8 |>.trans
          (Nat.mod_eq_of_lt this)]
  rw [← hcomb, hhi, hlo]; decide

private theorem m7_bva_try_lit_extend_lm {maxv cap step : Nat}
    {lm : List (BitVec 8)} {sb2 sb3 : List (BitVec 32)} {bl new_qn : BitVec 32}
    (hcap : 16448 ≤ cap) (hstep32 : step < 32)
    (hlm_l : lm.length = 2 * maxv) (hsb3_l : sb3.length = cap)
    (hbl_lt : bl.toNat < 2 * maxv)
    (hpres : ∀ idx < cap,
      ¬ (64 + step * 256 ≤ idx ∧ idx < 64 + step * 256 + 256) →
      ¬ (8256 + step * 256 ≤ idx ∧ idx < 8256 + step * 256 + 256) →
      sb3[idx]? = sb2[idx]?)
    (hhi : ∀ l < 2 * maxv, (lm[l]?.getD 0#8 &&& 0xFE#8) = 0#8)
    (hset : ∀ r < step, (lm[(sb2[r]?.getD 0#32).toNat]?.getD 0#8 &&& 1#8) ≠ 0#8)
    (honly : ∀ l < 2 * maxv, (lm[l]?.getD 0#8 &&& 1#8) ≠ 0#8 →
      ∃ r < step, (sb2[r]?.getD 0#32).toNat = l) :
    let lm4 := lm.set bl.toNat 1#8
    let sb4 := (sb3.set step bl).set (32 + step) new_qn
    (∀ l < 2 * maxv, (lm4[l]?.getD 0#8 &&& 0xFE#8) = 0#8) ∧
    (∀ r < step + 1, (lm4[(sb4[r]?.getD 0#32).toNat]?.getD 0#8 &&& 1#8) ≠ 0#8) ∧
    (∀ l < 2 * maxv, (lm4[l]?.getD 0#8 &&& 1#8) ≠ 0#8 →
      ∃ r < step + 1, (sb4[r]?.getD 0#32).toNat = l) := by
  intro lm4 sb4
  refine ⟨fun l hl => ?_, fun r hr => ?_, fun l hl hne => ?_⟩
  · dsimp only [lm4]
    by_cases hlb : l = bl.toNat
    · subst hlb; rw [List.getElem?_set_self (by omega), Option.getD_some]; decide
    · rw [List.getElem?_set_ne (Ne.symm hlb)]; exact hhi l hl
  · dsimp only [lm4, sb4]
    by_cases hrs : r < step
    · have hreq : ((sb3.set step bl).set (32 + step) new_qn)[r]? = sb2[r]? := by
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
        exact hpres r (by omega) (by omega) (by omega)
      rw [hreq]
      by_cases hlb : (sb2[r]?.getD 0#32).toNat = bl.toNat
      · rw [hlb, List.getElem?_set_self (by omega), Option.getD_some]; decide
      · rw [List.getElem?_set_ne (Ne.symm hlb)]; exact hset r hrs
    · have hr_eq : r = step := by omega
      subst r
      have hsb_st : ((sb3.set step bl).set (32 + step) new_qn)[step]?.getD 0#32 = bl := by
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega), Option.getD_some]
      rw [hsb_st, List.getElem?_set_self (by omega), Option.getD_some]; decide
  · dsimp only [lm4, sb4] at hne ⊢
    by_cases hlb : l = bl.toNat
    · subst hlb; refine ⟨step, by omega, ?_⟩
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega), Option.getD_some]
    · rw [List.getElem?_set_ne (Ne.symm hlb)] at hne
      obtain ⟨r, hr, heq⟩ := honly l hl hne
      refine ⟨r, by omega, ?_⟩
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        hpres r (by omega) (by omega) (by omega)]
      exact heq

private theorem m7_bva_try_lit_lm1_init {maxv cap : Nat} {sb : List (BitVec 32)}
    {lm : List (BitVec 8)} {f0 qn : BitVec 32}
    (hcap : 16448 ≤ cap) (hsb_l : sb.length = cap) (hlm_l : lm.length = 2 * maxv)
    (hf0_lt : f0.toNat < 2 * maxv)
    (hlm_zero : ∀ l < 2 * maxv, lm[l]?.getD 0#8 = 0#8) :
    let sb1 := (sb.set 0 f0).set 32 qn
    let lm1 := lm.set f0.toNat 1#8
    (∀ l < 2 * maxv, (lm1[l]?.getD 0#8 &&& 0xFE#8) = 0#8) ∧
    (∀ r < 1, (lm1[(sb1[r]?.getD 0#32).toNat]?.getD 0#8 &&& 1#8) ≠ 0#8) ∧
    (∀ l < 2 * maxv, (lm1[l]?.getD 0#8 &&& 1#8) ≠ 0#8 →
      ∃ r < 1, (sb1[r]?.getD 0#32).toNat = l) := by
  intro sb1 lm1
  have hs0 : sb1[0]?.getD 0#32 = f0 := by
    dsimp only [sb1]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega), Option.getD_some]
  refine ⟨fun l hl => ?_, fun r hr => ?_, fun l hl hne => ?_⟩
  · dsimp only [lm1]
    by_cases hlf : l = f0.toNat
    · subst hlf; rw [List.getElem?_set_self (by omega), Option.getD_some]; decide
    · rw [List.getElem?_set_ne (Ne.symm hlf), hlm_zero l hl]; decide
  · have hr0 : r = 0 := by omega
    subst hr0; rw [hs0]; dsimp only [lm1]
    rw [List.getElem?_set_self (by omega), Option.getD_some]; decide
  · dsimp only [lm1] at hne
    by_cases hlf : l = f0.toNat
    · subst hlf; exact ⟨0, by omega, by rw [hs0]⟩
    · rw [List.getElem?_set_ne (Ne.symm hlf), hlm_zero l hl] at hne; exact absurd rfl hne

private def M7BvaTouchedInv (c : FullCfg) (stc : FullState) (R : Mem 64 → Prop)
    (nt : BitVec 64) (st : FullState) (m : Mem 64) : Prop :=
  st.core = stc.core ∧
  st.scratch.scratch_buf = stc.scratch.scratch_buf ∧
  st.scratch.tarjan_mark = stc.scratch.tarjan_mark ∧
  st.scratch.tarjan_reach = stc.scratch.tarjan_reach ∧
  st.scratch.last_learned = stc.scratch.last_learned ∧
  st.scratch.extend_len = stc.scratch.extend_len ∧
  st.scratch.LengthsOk c ∧
  nt.toNat ≤ 2 * stc.core.cur_vars ∧
  (∀ k < nt.toNat, (st.scratch.work_stk2[k]?.getD 0#32).toNat < 2 * stc.core.cur_vars) ∧
  (FullMem c st ⋆ R) m

private theorem m7_bva_touched_push {c : FullCfg} {stc st : FullState} {R : Mem 64 → Prop}
    {nt : BitVec 64} {m : Mem 64} {l : BitVec 32} {idx : Nat}
    (_hcv_le : stc.core.cur_vars ≤ c.max_vars) (_hmx : c.max_vars < 2 * 2 ^ 28)
    (hnt_lt : nt.toNat < 2 * stc.core.cur_vars) (hl_lt : l.toNat < 2 * stc.core.cur_vars)
    (hcore : st.core = stc.core) (hsb : st.scratch.scratch_buf = stc.scratch.scratch_buf)
    (htm : st.scratch.tarjan_mark = stc.scratch.tarjan_mark)
    (htr : st.scratch.tarjan_reach = stc.scratch.tarjan_reach)
    (hll : st.scratch.last_learned = stc.scratch.last_learned)
    (hel : st.scratch.extend_len = stc.scratch.extend_len)
    (hscl : st.scratch.LengthsOk c)
    (hws2_ok : ∀ k < nt.toNat,
      (st.scratch.work_stk2[k]?.getD 0#32).toNat < 2 * stc.core.cur_vars)
    (hm : (FullMem c { st with scratch := { st.scratch with
      wsort := st.scratch.wsort.set idx 1#32,
      work_stk2 := st.scratch.work_stk2.set nt.toNat l } } ⋆ R) m) :
    M7BvaTouchedInv c stc R (nt + 1#64) { st with scratch := { st.scratch with
      wsort := st.scratch.wsort.set idx 1#32,
      work_stk2 := st.scratch.work_stk2.set nt.toNat l } } m := by
  have hws_l := hscl.wsort_len
  have hws2_l := hscl.work_stk2_len
  have hnt1 : (nt + 1#64).toNat = nt.toNat + 1 := by simp only [bv_c0]; omega
  refine ⟨hcore, hsb, htm, htr, hll, hel,
    { hscl with wsort_len := by simp [hws_l], work_stk2_len := by simp [hws2_l] },
    by omega, fun k hk => ?_, hm⟩
  rw [hnt1] at hk
  by_cases hkn : k = nt.toNat
  · subst hkn; rw [List.getElem?_set_self (by omega), Option.getD_some]; exact hl_lt
  · rw [List.getElem?_set_ne (Ne.symm hkn)]; exact hws2_ok k (by omega)

private theorem m7_bva_touched_clear_step {c : FullCfg} {stc stm stz : FullState}
    {R : Mem 64 → Prop} {ntm tz : BitVec 64} {m : Mem 64} {idx : Nat}
    (htz_lt : tz.toNat < ntm.toNat) (htz1 : (tz + 1#64).toNat = tz.toNat + 1)
    (hcorez : stz.core = stc.core) (hsbz : stz.scratch.scratch_buf = stc.scratch.scratch_buf)
    (htmz : stz.scratch.tarjan_mark = stc.scratch.tarjan_mark)
    (htrz : stz.scratch.tarjan_reach = stc.scratch.tarjan_reach)
    (hllz : stz.scratch.last_learned = stc.scratch.last_learned)
    (helz : stz.scratch.extend_len = stc.scratch.extend_len)
    (hws2z : stz.scratch.work_stk2 = stm.scratch.work_stk2)
    (hsclz : stz.scratch.LengthsOk c)
    (hm : (FullMem c { stz with scratch :=
      { stz.scratch with wsort := stz.scratch.wsort.set idx 0#32 } } ⋆ R) m) :
    ∃ stz' : FullState, (tz + 1#64).toNat ≤ ntm.toNat ∧ stz'.core = stc.core ∧
      stz'.scratch.scratch_buf = stc.scratch.scratch_buf ∧
      stz'.scratch.tarjan_mark = stc.scratch.tarjan_mark ∧
      stz'.scratch.tarjan_reach = stc.scratch.tarjan_reach ∧
      stz'.scratch.last_learned = stc.scratch.last_learned ∧
      stz'.scratch.extend_len = stc.scratch.extend_len ∧
      stz'.scratch.work_stk2 = stm.scratch.work_stk2 ∧
      stz'.scratch.LengthsOk c ∧ (FullMem c stz' ⋆ R) m :=
  ⟨{ stz with scratch := { stz.scratch with wsort := stz.scratch.wsort.set idx 0#32 } },
   by rw [htz1]; exact htz_lt, hcorez, hsbz, htmz, htrz, hllz, helz, hws2z,
   { hsclz with wsort_len := by rw [List.length_set, hsclz.wsort_len] }, hm⟩

private theorem m7_bv64_add2_mod {x : BitVec 32} :
    (x.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 = x.toNat + 2 := by
  rw [show BitVec.toNat (2 : BitVec 64) = 2 from rfl]; omega

private theorem m7_bv32_step_row_n {step : BitVec 32} (h1 : 1 ≤ step.toNat)
    (h2 : step.toNat < 32) :
    ((64 : BitVec 32) + (step - 1) * 256).toNat = 64 + (step.toNat - 1) * 256 := by
  simp only [BitVec.toNat_add, BitVec.toNat_mul,
    BitVec.toNat_sub_of_le (show (1 : BitVec 32).toNat ≤ step.toNat from h1),
    show (64 : BitVec 32).toNat = 64 from rfl, show (256 : BitVec 32).toNat = 256 from rfl,
    show (1 : BitVec 32).toNat = 1 from rfl]; omega

private theorem m7_bv32_nrow_n {step : BitVec 32} (h : step.toNat < 32) :
    ((64 : BitVec 32) + step * 256).toNat = 64 + step.toNat * 256 := by
  simp only [BitVec.toNat_add, BitVec.toNat_mul, show (64 : BitVec 32).toNat = 64 from rfl,
    show (256 : BitVec 32).toNat = 256 from rfl]; omega

private theorem m7_bv32_par_n {step : BitVec 32} (h : step.toNat < 32) :
    ((8256 : BitVec 32) + step * 256).toNat = 8256 + step.toNat * 256 := by
  simp only [BitVec.toNat_add, BitVec.toNat_mul, show (8256 : BitVec 32).toNat = 8256 from rfl,
    show (256 : BitVec 32).toNat = 256 from rfl]; omega

private theorem m7_bv32_add1_n {x : BitVec 32} (h : x.toNat < 1000) :
    (x + 1#32).toNat = x.toNat + 1 := by simp only [bv_c0]; omega

private theorem m7_bv32_32add_n {x : BitVec 32} (h : x.toNat < 32) :
    ((32 : BitVec 32) + x).toNat = 32 + x.toNat := by
  change (32#32 + x).toNat = _; simp only [bv_c0]; omega

private theorem m7_bv32_row_idx_n {bk tm : BitVec 32} (hbk : bk.toNat < 32)
    (htm : tm.toNat < 256) :
    (64 + bk * 256 + tm).toNat = 64 + bk.toNat * 256 + tm.toNat := by
  change (64#32 + bk * 256#32 + tm).toNat = _; simp only [bv_c0]; omega

private theorem m7_bv32_row_mod_n {bk tm : BitVec 32} (hbk : bk.toNat < 32)
    (htm : tm.toNat < 256) :
    ((64 : BitVec 32).toNat + bk.toNat * (256 : BitVec 32).toNat + tm.toNat) % 2 ^ 32 =
      64 + bk.toNat * 256 + tm.toNat := by
  change (64 + bk.toNat * 256 + tm.toNat) % 2 ^ 32 = _; omega

private theorem m7_bv64_add2_n {ct : BitVec 32} :
    (BitVec.setWidth 64 ct + 2).toNat = ct.toNat + 2 := by
  change (BitVec.setWidth 64 ct + 2#64).toNat = _; simp only [bv_c0]; omega

private theorem m7_bv64_add3_n {ct tj : BitVec 32} :
    (BitVec.setWidth 64 ct + 3 + BitVec.setWidth 64 tj).toNat = ct.toNat + 3 + tj.toNat := by
  change (BitVec.setWidth 64 ct + 3#64 + BitVec.setWidth 64 tj).toNat = _; simp only [bv_c0]; omega

private theorem m7_bv64_add1_n {tz : BitVec 64} (h : tz.toNat < 4 * 2 ^ 28) :
    (tz + 1#64).toNat = tz.toNat + 1 := by simp only [bv_c0]; omega

private theorem m7_bv8_setWidth_and_fe (x : BitVec 8) :
    BitVec.setWidth 8 (BitVec.setWidth 32 x &&& 254#32) = x &&& 0xFE#8 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat]
  have hx := x.isLt
  rw [Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ 32),
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left hx)]

end M7TryLitHelpers

/-! ## 3. `full_bva_try_lit_m7_wp` (`factorsize = 5`, `red > elim_bound`, `256 x 32`) -/

theorem full_bva_try_lit_m7_wp (Γ : Env)
    (hScan : ∀ args m Q X, m4BvaScanCandsSpec args m Q X →
      Γ "full_bva_scan_cands" [i64, i32, i32, i64] [i32] args m Q X)
    (hPick : ∀ args m Q X, fullBvaPickCandSpec args m Q X →
      Γ "full_bva_pick_cand" [i64, i32, i32] [i32] args m Q X)
    (hFilter : ∀ args m Q X, m4BvaFilterRowSpec args m Q X →
      Γ "full_bva_filter_row" [i64, i32, i32, i32, i32, i32] [i32] args m Q X)
    (hCommit : ∀ args m Q X, m4BvaCommitSpec args m Q X →
      Γ "full_bva_commit" [i64, i32] [.bool] args m Q X) :
    ∀ args m Q X, fullBvaTryLitHeapSpec args m Q X →
      Func.wp Γ full_bva_try_lit_m7_body args m Q X := by
  intro (h, f0, init_cv0, ()) m Q X ⟨c, F0, s, R, hh, hinv0, hf0_lt, hm, hQ⟩
  subst hh
  obtain ⟨⟨hlen, F_cur, hw⟩, hlm, hnd, hext, hlv0, hdm⟩ := hinv0
  have hinv : FullDenseInvW c F0 F_cur s := ⟨hlen, hw, hlm, hnd, hext, hlv0, hdm⟩
  have hclen := hlen.core_ok; have hslen := hlen.scratch_ok
  have hcv_le := hclen.cur_vars_le
  have hmx : c.max_vars < 2 * 2 ^ 28 := by simpa only [dimacsBound] using c.hmaxv
  have h2cv : 2 * s.core.cur_vars < 2 ^ 64 := by omega
  have hvals_f0 : (BitVec.setWidth 64 f0).toNat < s.core.vals.length := by
    rw [bv64_setWidth_32, hclen.vals_len]; omega
  unfold Func.wp full_bva_try_lit_m7_body; dsimp only
  c0_hsplit
  · c0_hfast_nogrp
    exact hQ false s m hinv.toDense (Nat.le_refl _) rfl rfl rfl hm
  · c0_hsplit
    · c0_hfast_nogrp
      exact hQ false s m hinv.toDense (Nat.le_refl _) rfl rfl rfl hm
    · have hcap_ge : 16448 ≤ c.scratch_cap := by
        have hscr_u64 : c.scratch_cap < 2 ^ 64 := by
          have := c.hscr; unfold dimacsBound at this; omega
        have h1 : ¬ c.scratch_cap % 2 ^ 64 < (16448 : BitVec 64).toNat := by assumption
        rw [Nat.mod_eq_of_lt hscr_u64] at h1
        change ¬ c.scratch_cap < 16448 at h1; omega
      have hcv_lt : s.core.cur_vars < c.max_vars := by
        have h1 : ¬ c.max_vars % 2 ^ 64 ≤ s.core.cur_vars % 2 ^ 64 := by assumption
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h1; omega
      c0_hsplit
      · c0_hfast_nogrp
        exact hQ false s m hinv.toDense (Nat.le_refl _) rfl rfl rfl hm
      · c0_hfast_nogrp
        refine wp_join_state (α := BitVec 64) (fun x => (x, ()))
          (fun icv mf => icv.toNat ≤ 2 * s.core.cur_vars ∧ mf = m)
          (fun _ init_lits mf ⟨hinit_lits, hmf⟩ => ?_)
          (fun Jicv hJicv => ?_)
        · subst mf
          have h2f0 : (BitVec.setWidth 64 f0 <<< 1#64).toNat = 2 * f0.toNat :=
            bv64_shl1_lit_toNat f0
          have h2f1 : ((BitVec.setWidth 64 f0 <<< 1#64) + 1#64).toNat = 2 * f0.toNat + 1 :=
            bv64_shl1_lit_add1_toNat f0
          have h2f0_l : (BitVec.setWidth 64 f0 <<< 1#64).toNat < s.core.wvec.length := by
            rw [h2f0, hclen.wvec_len]; omega
          have h2f1_l : ((BitVec.setWidth 64 f0 <<< 1#64) + 1#64).toNat <
              s.core.wvec.length := by
            rw [h2f1, hclen.wvec_len]; omega
          c0_hfast_nogrp
          let off0 := s.core.wvec[2 * f0.toNat]' (by rw [hclen.wvec_len]; omega)
          let sz0 := s.core.wvec[2 * f0.toNat + 1]' (by rw [hclen.wvec_len]; omega)
          have hwatches : DenseWatchesInv F_cur s.core := by
            have hw := hinv.2.1.watches
            unfold ModeWatchesInv at hw
            simpa [hdm] using hw
          have hslice0 := hwatches.slices f0.toNat (by omega)
          have hoff_sz0 := hwatches.layout.bounds f0.toNat (by omega)
          have hws_cap := hclen.wlen_le
          have hwlen_bd := c.hwcap
          dsimp only [fullWatchOffCore, fullWatchSizeCore] at hslice0 hoff_sz0
          rw [List.getElem?_eq_getElem (by rw [hclen.wvec_len]; omega), Option.getD_some]
            at hslice0 hoff_sz0
          rw [List.getElem?_eq_getElem (by rw [hclen.wvec_len]; omega), Option.getD_some]
            at hslice0 hoff_sz0
          refine wp_loop_inv
            (fun (wi, r0n, ()) mw => ∃ sbr : List (BitVec 32),
              let stw : FullState := { s with scratch := { s.scratch with scratch_buf := sbr } }
              (FullMem c stw ⋆ R) mw ∧ sbr.length = c.scratch_cap ∧
              wi.toNat ≤ sz0.toNat ∧ r0n.toNat ≤ 256 ∧
              DenseWatchSliceOk F_cur s.core f0.toNat (off0.toNat + wi.toNat)
                (sz0.toNat - wi.toNat) ∧
              ∀ qm < r0n.toNat, ∃ res : List Nat,
                (∀ x ∈ res, x < 2 * s.core.cur_vars) ∧ (res.map (· / 2)).Nodup ∧
                M4BvaRowEntryOk F_cur s f0.toNat (sbr[64 + qm]?.getD 0#32) res ∧
                (cnfOfClauses F_cur).EntailsClause (cnfClause (f0.toNat :: res)))
            (fun (wi, _, _) _ => sz0.toNat - wi.toNat)
            (fun Jw hJw => by
              exact hJw (0#64, 0#32, ()) m
                ⟨s.scratch.scratch_buf, hm, hslen.scratch_buf_len, Nat.zero_le _, Nat.zero_le _,
                 by simpa using hslice0, fun _ hq => by simp at hq⟩)
            (fun Jw (wi, r0n, ()) mw
                ⟨sbr, hmw, hsbr_l, hwi_le, hr0n_le, hslicew, hrow⟩ ihw => ?_)
          c0_hfast_nogrp
          refine wp_join_state0 (fun (_ : Unit) mf => mf = mw)
            (fun Js _ mf hmf => ?_)
            (fun Js hJs => ?_)
          rotate_left 1
          · c0_hfast_nogrp
            rotate_left 1
            · try c0_hfast_nogrp
              exact hJs () mw rfl
            · try c0_hfast_nogrp
              exact hJs () mw rfl
            have h2f1_idx : (2 * f0.toNat + (1 : BitVec 64).toNat) % 2 ^ 64 <
                s.core.wvec.length := by
              rw [show ((1 : BitVec 64)).toNat = 1 from rfl,
                Nat.mod_eq_of_lt (by omega), hclen.wvec_len]; omega
            have hwi_hc : wi.toNat <
                (s.core.wvec[(2 * f0.toNat + (1 : BitVec 64).toNat) % 2 ^ 64]'h2f1_idx).toNat :=
              by assumption
            have hwi_lt : wi.toNat < sz0.toNat := by
              dsimp [sz0]
              simpa only [show ((1 : BitVec 64)).toNat = 1 from rfl,
                Nat.mod_eq_of_lt (by omega : 2 * f0.toNat + 1 < 2 ^ 64)] using hwi_hc
            have hr0n_hc : r0n.toNat < (256 : BitVec 32).toNat := by assumption
            have hr0n_lt : r0n.toNat < 256 := lt_of_lt_of_eq hr0n_hc (by decide)
            have hoff_wi_n : (BitVec.setWidth 64 off0 + wi).toNat = off0.toNat + wi.toNat := by
              simp only [bv_c0]
              have hmod : (off0.toNat + wi.toNat) % 2 ^ 64 = off0.toNat + wi.toNat := by
                have := hoff_sz0; unfold dimacsBound at hwlen_bd; omega
              exact hmod
            have hwi_ws : (BitVec.setWidth 64 off0 + wi).toNat < s.core.wstk.length := by
              dsimp only [off0] at hoff_wi_n
              rw [hoff_wi_n, hclen.wstk_len_arr]
              dsimp only [sz0] at hwi_lt
              omega
            have h2f0_nat : (BitVec.setWidth 64 f0 <<< (1 : Nat)).toNat = 2 * f0.toNat := by
              simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
            have h2f0_nat_l : (BitVec.setWidth 64 f0 <<< (1 : Nat)).toNat < s.core.wvec.length := by
              rw [h2f0_nat, hclen.wvec_len]; omega
            have hwi_ws_raw : (BitVec.setWidth 64
                (s.core.wvec[(BitVec.setWidth 64 f0 <<< (1 : Nat)).toNat]'h2f0_nat_l) +
                wi).toNat < s.core.wstk.length := by
              simpa only [h2f0_nat, off0] using hwi_ws
            have hwi1_n : (wi + 1#64).toNat = wi.toNat + 1 := by
              simp only [bv_c0]; have := hoff_sz0; unfold dimacsBound at hwlen_bd; omega
            have hr0n1_n : (r0n + 1#32).toNat = r0n.toNat + 1 :=
              m7_bv32_add1_n (Nat.lt_trans hr0n_lt (by decide))
            have h64r0_n : (64 + BitVec.setWidth 64 r0n).toNat = 64 + r0n.toNat := by
              change (64#64 + BitVec.setWidth 64 r0n).toNat = _
              simp only [bv_c0]; omega
            have h64r0_n' : (BitVec.setWidth 64 (64 + r0n)).toNat = 64 + r0n.toNat := by
              change (BitVec.setWidth 64 (64#32 + r0n)).toNat = _
              simp only [bv_c0]; omega
            have h64r0_sb : (64 + BitVec.setWidth 64 r0n).toNat < sbr.length := by
              rw [h64r0_n, hsbr_l]; omega
            c0_hfast_nogrp
            let Loop1ContInv : (BitVec 64 × BitVec 32) → Mem 64 → Prop :=
              fun (wi', r0n') mh => wi'.toNat ≤ sz0.toNat ∧ r0n'.toNat ≤ 256 ∧
                sz0.toNat - wi'.toNat < sz0.toNat - wi.toNat ∧
                ∃ sbr' : List (BitVec 32),
                  let stw' : FullState :=
                    { s with scratch := { s.scratch with scratch_buf := sbr' } }
                  (FullMem c stw' ⋆ R) mh ∧ sbr'.length = c.scratch_cap ∧
                  DenseWatchSliceOk F_cur s.core f0.toNat (off0.toNat + wi'.toNat)
                    (sz0.toNat - wi'.toNat) ∧
                  ∀ qm < r0n'.toNat, ∃ res : List Nat,
                    (∀ x ∈ res, x < 2 * s.core.cur_vars) ∧ (res.map (· / 2)).Nodup ∧
                    M4BvaRowEntryOk F_cur s f0.toNat (sbr'[64 + qm]?.getD 0#32) res ∧
                    (cnfOfClauses F_cur).EntailsClause (cnfClause (f0.toNat :: res))
            refine wp_join_state (α := BitVec 64 × BitVec 32) (fun p => (p.1, p.2, ()))
              Loop1ContInv
              (fun _ (wi', r0n') mh ⟨h1, h2, hdec, sbr', hmh', hsbrl', hslice', hrow'⟩ => by
                c0_hfast_nogrp
                exact ihw (wi', r0n', ()) mh hdec ⟨sbr', hmh', hsbrl', h1, h2, hslice', hrow'⟩)
              (fun Js hJs => ?_)
            c0_hfast_nogrp
            · have hbin_w0 : (s.core.wstk[off0.toNat + wi.toNat]'(by omega) &&&
                  0x80000000#32) ≠ 0#32 := by
                have h1 : (s.core.wstk[(BitVec.setWidth 64
                    (s.core.wvec[(BitVec.setWidth 64 f0 <<< (1 : Nat)).toNat]'h2f0_nat_l) +
                    wi).toNat]'hwi_ws_raw &&& (2147483648 : BitVec 32)) ≠ (0 : BitVec 32) := by
                  assumption
                simpa only [h2f0_nat, off0, hoff_wi_n,
                  show (2147483648 : BitVec 32) = 0x80000000#32 from rfl,
                  show (0 : BitVec 32) = 0#32 from rfl] using h1
              obtain ⟨hot_lt, hent_ot, hslice_next⟩ :=
                bva_slice_bin_info hslicew (by omega) (by omega) hbin_w0
              have hot_eq : (BitVec.setWidth 64
                  (s.core.wstk[(BitVec.setWidth 64 off0 + wi).toNat]'hwi_ws &&&
                    0x7FFFFFFF#32)).toNat =
                  (s.core.wstk[off0.toNat + wi.toNat]'(by omega) &&& 0x7FFFFFFF#32).toNat := by
                simp only [hoff_wi_n, bv64_setWidth_32]
              have hot_vals : (BitVec.setWidth 64
                  (s.core.wstk[(BitVec.setWidth 64 off0 + wi).toNat]'hwi_ws &&&
                    0x7FFFFFFF#32)).toNat < s.core.vals.length := by
                rw [hot_eq, hclen.vals_len]; omega
              have hot_vals_raw : (BitVec.setWidth 64
                  (s.core.wstk[(BitVec.setWidth 64
                    (s.core.wvec[(BitVec.setWidth 64 f0 <<< (1 : Nat)).toNat]'h2f0_nat_l) +
                    wi).toNat]'hwi_ws_raw &&&
                    (2147483647 : BitVec 32))).toNat < s.core.vals.length := by
                simpa only [h2f0_nat, off0,
                  show (2147483647 : BitVec 32) = 0x7FFFFFFF#32 from rfl] using hot_vals
              refine wp_join_state1 (t := i32) (α := BitVec 32) (fun r => r)
                (fun r0n' mj => r0n'.toNat ≤ 256 ∧ ∃ sbr' : List (BitVec 32),
                  let stw' : FullState :=
                    { s with scratch := { s.scratch with scratch_buf := sbr' } }
                  (FullMem c stw' ⋆ R) mj ∧ sbr'.length = c.scratch_cap ∧
                  ∀ qm < r0n'.toNat, ∃ res : List Nat,
                    (∀ x ∈ res, x < 2 * s.core.cur_vars) ∧ (res.map (· / 2)).Nodup ∧
                    M4BvaRowEntryOk F_cur s f0.toNat (sbr'[64 + qm]?.getD 0#32) res ∧
                    (cnfOfClauses F_cur).EntailsClause (cnfClause (f0.toNat :: res)))
                (fun _ r0n' mj ⟨hr0n', sbr', hmj', hsbrl', hrow'⟩ => by
                  c0_hfast_nogrp
                  exact hJs (wi + 1#64, r0n') mj
                    ⟨by rw [hwi1_n]; omega, hr0n', by rw [hwi1_n]; omega,
                     sbr', hmj', hsbrl',
                     by rw [hwi1_n, show off0.toNat + (wi.toNat + 1) = off0.toNat + wi.toNat + 1
                          by omega,
                        show sz0.toNat - (wi.toNat + 1) = sz0.toNat - wi.toNat - 1 by omega]
                        exact hslice_next,
                     hrow'⟩)
                (fun Js1 hJs1 => ?_)
              c0_hfast_nogrp
              · let w0v := s.core.wstk[off0.toNat + wi.toNat]'(by omega)
                let ot := w0v &&& 0x7FFFFFFF#32
                refine hJs1 (r0n + 1#32) m ⟨by rw [hr0n1_n]; omega,
                  sbr.set (64 + r0n.toNat) w0v,
                  by simpa only [h2f0_nat, off0, hoff_wi_n, h64r0_n'] using hm,
                  by simp [hsbr_l], fun qm hqm => ?_⟩
                rw [hr0n1_n] at hqm
                by_cases hqe : qm = r0n.toNat
                · subst hqe
                  rw [List.getElem?_set_self (by omega), Option.getD_some]
                  refine ⟨[ot.toNat], fun x hx => by simp at hx; subst hx; exact hot_lt,
                    by simp, ?_, hent_ot⟩
                  unfold M4BvaRowEntryOk; rw [ite_eq_left hbin_w0]
                  exact ⟨hot_lt, rfl, hent_ot⟩
                · rw [List.getElem?_set_ne (by omega)]
                  exact hrow qm (by omega)
              · exact hJs1 r0n mw ⟨hr0n_le, sbr, hmw, hsbr_l, hrow⟩
            · have hnbin_w0 : (s.core.wstk[off0.toNat + wi.toNat]'(by omega) &&&
                  0x80000000#32) = 0#32 := by
                have hno : (s.core.wstk[(BitVec.setWidth 64
                    (s.core.wvec[(BitVec.setWidth 64 f0 <<< (1 : Nat)).toNat]'h2f0_nat_l) +
                    wi).toNat]'hwi_ws_raw &&&
                    (2147483648 : BitVec 32)) = (0 : BitVec 32) := by assumption
                simpa only [h2f0_nat, off0, hoff_wi_n,
                  show (2147483648 : BitVec 32) = 0x80000000#32 from rfl,
                  show (0 : BitVec 32) = 0#32 from rfl] using hno
              obtain ⟨hrem2, hslice_next⟩ :=
                bva_slice_occ_info hslicew (by omega) (by omega) hnbin_w0
              have hwi_next_lt : (wi + 1#64).toNat < sz0.toNat := by rw [hwi1_n]; omega
              rcases denseWatchSliceOk_step hslicew (by omega) with
                ⟨_, hw0s, hbin_ne, _, _, _, _⟩ |
                ⟨_, cr, _, _, hcrs, _, _, _, hcr_ref, _⟩
              · exfalso
                rw [List.getElem?_eq_getElem (by omega)] at hw0s
                exact absurd (Option.some.inj hw0s ▸ hnbin_w0) hbin_ne
              have hoff_wi1_n :
                  (BitVec.setWidth 64 off0 + (wi + (1 : BitVec 64))).toNat =
                    off0.toNat + wi.toNat + 1 := by
                change (BitVec.setWidth 64 off0 + (wi + 1#64)).toNat = _
                simp only [bv_c0, hwi1_n]
                have := hoff_sz0; unfold dimacsBound at hwlen_bd; omega
              have hwi1_ws : (BitVec.setWidth 64 off0 + (wi + (1 : BitVec 64))).toNat <
                  s.core.wstk.length := by
                dsimp only [off0] at hoff_wi1_n
                rw [hoff_wi1_n, hclen.wstk_len_arr]
                dsimp only [sz0] at hwi_next_lt
                omega
              have hwi1_ws_raw : (BitVec.setWidth 64
                  (s.core.wvec[(BitVec.setWidth 64 f0 <<< (1 : Nat)).toNat]'h2f0_nat_l) +
                  (wi + (1 : BitVec 64))).toNat < s.core.wstk.length := by
                simpa only [h2f0_nat, off0] using hwi1_ws
              have hcr_val :
                  s.core.wstk[(BitVec.setWidth 64 off0 + (wi + (1 : BitVec 64))).toNat]'hwi1_ws =
                  cr := by
                have h1 : s.core.wstk[off0.toNat + wi.toNat + 1]'(by
                    rw [← hoff_wi1_n]; exact hwi1_ws) = cr :=
                  Option.some.inj (by
                    rw [← List.getElem?_eq_getElem (by rw [← hoff_wi1_n]; exact hwi1_ws)]
                    exact hcrs)
                simpa only [hoff_wi1_n] using h1
              have hcr_val_raw : s.core.wstk[(BitVec.setWidth 64
                  (s.core.wvec[(BitVec.setWidth 64 f0 <<< (1 : Nat)).toNat]'h2f0_nat_l) +
                  (wi + (1 : BitVec 64))).toNat]'hwi1_ws_raw = cr := by
                simpa only [h2f0_nat, off0] using hcr_val
              have hcr_wf := hinv.2.1.arena.refs_wf cr.toNat hcr_ref
              have halen_le := hclen.arena_len_le
              have har_bd := c.harena; unfold dimacsBound at har_bd
              have har_arr := hclen.arena_len_arr
              have hcr2_n : (BitVec.setWidth 64 cr + 2#64).toNat = cr.toNat + 2 :=
                bv64_add_toNat (by
                  rw [bv64_setWidth_32, show (2#64).toNat = 2 from rfl]
                  have := hcr_wf.1; have := halen_le; omega)
              have hcr2_n_of : (BitVec.setWidth 64 cr + (2 : BitVec 64)).toNat = cr.toNat + 2 :=
                hcr2_n
              have hcr0_ar : (BitVec.setWidth 64 cr).toNat < s.core.arena.length := by
                rw [bv64_setWidth_32]; have := hcr_wf.1; have := halen_le; rw [har_arr]; omega
              have hcr2_ar : (BitVec.setWidth 64 cr + 2#64).toNat < s.core.arena.length := by
                rw [hcr2_n]; have := hcr_wf.1; have := halen_le; rw [har_arr]; omega
              have hcr0_ar_raw : (BitVec.setWidth 64
                  (s.core.wstk[(BitVec.setWidth 64
                    (s.core.wvec[(BitVec.setWidth 64 f0 <<< (1 : Nat)).toNat]'h2f0_nat_l) +
                    (wi + (1 : BitVec 64))).toNat]'hwi1_ws_raw)).toNat <
                  s.core.arena.length := by
                rw [hcr_val_raw]; exact hcr0_ar
              have hcr2_ar_raw : (BitVec.setWidth 64
                  (s.core.wstk[(BitVec.setWidth 64
                    (s.core.wvec[(BitVec.setWidth 64 f0 <<< (1 : Nat)).toNat]'h2f0_nat_l) +
                    (wi + (1 : BitVec 64))).toNat]'hwi1_ws_raw) + (2 : BitVec 64)).toNat <
                  s.core.arena.length := by
                rw [hcr_val_raw]; exact hcr2_ar
              have hwi2_n : (wi + 1#64 + 1#64).toNat = wi.toNat + 2 := by
                simp only [bv_c0]; have := hoff_sz0; unfold dimacsBound at hwlen_bd; omega
              refine wp_join_state (α := BitVec 64 × BitVec 32) (fun p => (p.1, p.2, ()))
                Loop1ContInv
                (fun _ (wi', r0n') mh hinv' => by
                  c0_hfast_nogrp; exact hJs (wi', r0n') mh hinv')
                (fun Js1 hJs1 => ?_)
              c0_hfast_nogrp
              rotate_left 1
              · exfalso
                have hno_raw : ¬ (wi + (1 : BitVec 64)).toNat <
                    (BitVec.setWidth 64 (s.core.wvec[(2 * f0.toNat + (1 : BitVec 64).toNat) %
                      2 ^ 64]'h2f1_idx)).toNat := by assumption
                have hno : ¬ (wi + (1 : BitVec 64)).toNat < sz0.toNat := by
                  simpa only [bv64_setWidth_32, show ((1 : BitVec 64)).toNat = 1 from rfl,
                    Nat.mod_eq_of_lt (by omega : 2 * f0.toNat + 1 < 2 ^ 64), sz0] using hno_raw
                exact hno hwi_next_lt
              dsimp only; simp only [hcr_val_raw]
              refine wp_join_state1 (t := i32) (α := BitVec 32) (fun r => r)
                (fun r0n' mj => r0n'.toNat ≤ 256 ∧ ∃ sbr' : List (BitVec 32),
                  let stw' : FullState :=
                    { s with scratch := { s.scratch with scratch_buf := sbr' } }
                  (FullMem c stw' ⋆ R) mj ∧ sbr'.length = c.scratch_cap ∧
                  ∀ qm < r0n'.toNat, ∃ res : List Nat,
                    (∀ x ∈ res, x < 2 * s.core.cur_vars) ∧ (res.map (· / 2)).Nodup ∧
                    M4BvaRowEntryOk F_cur s f0.toNat (sbr'[64 + qm]?.getD 0#32) res ∧
                    (cnfOfClauses F_cur).EntailsClause (cnfClause (f0.toNat :: res)))
                (fun _ r0n' mj ⟨hr0n', sbr', hmj', hsbrl', hrow'⟩ => by
                  c0_hfast_nogrp
                  exact hJs1 (wi + 1#64 + 1#64, r0n') mj
                    ⟨by rw [hwi2_n]; omega, hr0n', by rw [hwi2_n]; omega,
                     sbr', hmj', hsbrl',
                     by rw [hwi2_n, show off0.toNat + (wi.toNat + 2) = off0.toNat + wi.toNat + 2
                          by omega,
                        show sz0.toNat - (wi.toNat + 2) = sz0.toNat - wi.toNat - 2 by omega]
                        exact hslice_next,
                     hrow'⟩)
                (fun Js2 hJs2 => ?_)
              c0_hfast_nogrp
              · have hcfl_z : (s.core.arena[cr.toNat]'(by omega) &&& 0x00480000#32) = 0#32 := by
                  have h1 :
                      (s.core.arena[cr.toNat]'(by omega) &&& ((524288 : BitVec 32) ||| 4194304)) =
                        (0 : BitVec 32) := by assumption
                  simpa only [
                    show ((524288 : BitVec 32) ||| 4194304) = 0x00480000#32 from by decide,
                    show (0 : BitVec 32) = 0#32 from rfl] using h1
                have hcr2_mod : (cr.toNat + (2 : BitVec 64).toNat) % 2 ^ 64 = cr.toNat + 2 := by
                  rw [show (2 : BitVec 64).toNat = 2 from rfl, Nat.mod_eq_of_lt (by omega)]
                have hcsz3 : 3 ≤ (s.core.arena[cr.toNat + 2]'(by omega)).toNat := by
                  have h1 : (3 : BitVec 32).toNat ≤
                      (s.core.arena[(cr.toNat + (2 : BitVec 64).toNat) % 2 ^ 64]'(by
                        rw [hcr2_mod]; omega)).toNat := by assumption
                  simp only [hcr2_mod] at h1
                  exact Nat.le_trans (by decide) h1
                have hcsz5 : (s.core.arena[cr.toNat + 2]'(by omega)).toNat ≤ 5 := by
                  have h1 :
                      (s.core.arena[(cr.toNat + (2 : BitVec 64).toNat) % 2 ^ 64]'(by
                        rw [hcr2_mod]; omega)).toNat ≤ (5 : BitVec 32).toNat := by assumption
                  simp only [hcr2_mod] at h1
                  exact Nat.le_trans h1 (by decide)
                let csz := s.core.arena[cr.toNat + 2]'(by omega)
                have hcsz_eq : csz.toNat = fullArenaClauseSizeCore s.core cr.toNat := by
                  unfold fullArenaClauseSizeCore
                  rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                have hcr_ng : fullArenaClauseGarbCore s.core cr.toNat = false := by
                  unfold fullArenaClauseGarbCore fullArenaHdrCore
                  rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                  have hbit : (s.core.arena[cr.toNat]'(by omega) &&& 524288#32) = 0#32 := by
                    have hsub : (524288#32 : BitVec 32) = 0x00480000#32 &&& 524288#32 := by decide
                    rw [hsub, ← BitVec.and_assoc, hcfl_z, BitVec.zero_and]
                  simp [hbit]
                have hcr_end_ar : cr.toNat + 3 + csz.toNat ≤ s.core.arena.length := by
                  rw [hcsz_eq]
                  exact Nat.le_trans hcr_wf.2.2.1 (Nat.le_trans hcr_wf.2.2.2.1 (by omega))
                refine wp_join_state (α := BitVec 32 × Bool × Bool)
                  (fun ⟨j', hf0, sat⟩ => (j', hf0, sat, ()))
                  (fun ⟨_, hf0, sat⟩ mf => mf = mw ∧ (sat = false → hf0 = true →
                    f0.toNat ∈ fullArenaClauseLitsCore s.core cr.toNat))
                  (fun _ ⟨_, has_f0, sat⟩ mf ⟨hmf, hmem⟩ => ?_)
                  (fun Jj hJj => ?_)
                · subst mf
                  let Js2Inv : BitVec 32 → Mem 64 → Prop := fun st m' =>
                    st.toNat ≤ 256 ∧ ∃ sbr',
                      let stw' := { s with scratch := { s.scratch with scratch_buf := sbr' } }
                      (FullMem c stw' ⋆ R) m' ∧ sbr'.length = c.scratch_cap ∧
                        ∀ qm : Nat, qm < st.toNat → ∃ res,
                          (∀ x, x ∈ res → x < 2 * s.core.cur_vars) ∧
                          (List.map (fun x => x / 2) res).Nodup ∧
                          M4BvaRowEntryOk F_cur s f0.toNat (sbr'[64 + qm]?.getD 0#32) res ∧
                          (cnfOfClauses F_cur).EntailsClause (cnfClause (f0.toNat :: res))
                  refine wp_join_state1 (fun r : BitVec 32 => r) Js2Inv
                    (fun _ st m' h => by c0_hfast_nogrp; exact hJs2 st m' h)
                    (fun Js hJs => ?_)
                  c0_hfast_nogrp
                  · exact hJs r0n mw ⟨hr0n_le, sbr, hmw, hsbr_l, hrow⟩
                  · have hok_f0 : f0.toNat ∈ fullArenaClauseLitsCore s.core cr.toNat :=
                      hmem (by cases sat <;> first | contradiction | rfl)
                        (by cases has_f0 <;> first | contradiction | rfl)
                    obtain ⟨res, hres_lt, hres_nd, hok, hent⟩ :=
                      m7BvaRowEntryOk_of_large_f0 hinv hcr_ref hcr_ng
                        (by rw [← hcsz_eq]; exact hcsz3) (by rw [← hcsz_eq]; exact hcsz5)
                        hok_f0
                    refine hJs (r0n + 1#32) m ⟨by rw [hr0n1_n]; omega,
                      sbr.set (64 + r0n.toNat) cr, by simpa only [h64r0_n'] using hm,
                      by simp [hsbr_l], fun qm hqm => ?_⟩
                    rw [hr0n1_n] at hqm
                    by_cases hqe : qm = r0n.toNat
                    · subst hqe
                      rw [List.getElem?_set_self (by omega), Option.getD_some]
                      exact ⟨res, hres_lt, hres_nd, hok, hent⟩
                    · rw [List.getElem?_set_ne (by omega)]
                      exact hrow qm (by omega)
                  · exact hJs r0n mw ⟨hr0n_le, sbr, hmw, hsbr_l, hrow⟩
                · refine wp_loop_inv
                    (fun (j, hf0, ()) mj => mj = mw ∧ j.toNat ≤ csz.toNat ∧
                      (hf0 = true → f0.toNat ∈ fullArenaClauseLitsCore s.core cr.toNat))
                    (fun (j, _, ()) _ => csz.toNat - j.toNat)
                    (fun Jl hJl => hJl (0#32, false, ()) mw
                      ⟨rfl, Nat.zero_le _, Bool.noConfusion⟩)
                    (fun Jl (j, hf0, ()) mj ⟨hmj, hj_le, hmem⟩ ihj => ?_)
                  subst mj
                  c0_hsplit
                  · have hj_lt : j.toNat < csz.toNat := by
                      have h1 : j.toNat <
                          (s.core.arena[(BitVec.setWidth 64 cr +
                            (2 : BitVec 64)).toNat]'hcr2_ar).toNat
                          := by assumption
                      simpa only [hcr2_n_of] using h1
                    have hj1 : (j + 1#32).toNat = j.toNat + 1 :=
                      m7_bv32_add1_n (Nat.lt_trans (Nat.lt_of_lt_of_le hj_lt hcsz5) (by decide))
                    have hcrj_n : (BitVec.setWidth 64 cr + 3#64 + BitVec.setWidth 64 j).toNat =
                        cr.toNat + 3 + j.toNat := m7_bv64_add3_n
                    have hcrj_ar :
                        (BitVec.setWidth 64 cr + 3#64 + BitVec.setWidth 64 j).toNat <
                          s.core.arena.length := by
                      rw [hcrj_n]; omega
                    have hl_mem : (s.core.arena[cr.toNat + 3 + j.toNat]'(by omega)).toNat ∈
                        fullArenaClauseLitsCore s.core cr.toNat :=
                      List.mem_of_getElem? (FullBvaFwdHelpers.fullArenaClauseLitsCore_getElem
                        (k := s.core) (r := cr.toNat) (j := j.toNat)
                        (by rw [← hcsz_eq]; exact hj_lt) (by omega))
                    have hl_lt : (s.core.arena[cr.toNat + 3 + j.toNat]'(by omega)).toNat <
                        2 * s.core.cur_vars :=
                      hinv.2.1.arena.lits_lt cr.toNat hcr_ref hcr_ng _ hl_mem
                    have hl_vals : (BitVec.setWidth 64
                        (s.core.arena[(BitVec.setWidth 64 cr + 3#64 +
                          BitVec.setWidth 64 j).toNat]'hcrj_ar)).toNat <
                        s.core.vals.length := by
                      simp only [bv64_setWidth_32, hcrj_n, hclen.vals_len]
                      exact Nat.lt_of_lt_of_le hl_lt (Nat.mul_le_mul_left 2 hcv_le)
                    c0_hfast_nogrp
                    · exact hJj (j, hf0, true) mw ⟨rfl, fun h _ => Bool.noConfusion h⟩
                    · refine wp_join_state1 (fun b : Bool => b)
                        (fun hf0' m' => m' = mw ∧
                          (hf0' = true → f0.toNat ∈ fullArenaClauseLitsCore s.core cr.toNat))
                        (fun _ hf0' m' ⟨hm', hmem'⟩ => by
                          subst m'
                          c0_hstep
                          exact ihj (j + 1#32, hf0', ()) mw
                            (by dsimp only; rw [hj1]
                                exact Nat.sub_lt_sub_left hj_lt (Nat.lt_succ_self _))
                            ⟨rfl, by rw [hj1]; exact hj_lt, hmem'⟩)
                        (fun Jhf0 hJhf0 => ?_)
                      c0_hsplit
                      · c0_hstep
                        have hcrj_mod :
                            (cr.toNat + (3 : BitVec 64).toNat + j.toNat) % 2 ^ 64 =
                              cr.toNat + 3 + j.toNat := by
                          rw [show (3 : BitVec 64).toNat = 3 from rfl,
                            Nat.mod_eq_of_lt (by omega)]
                        have heq : s.core.arena[cr.toNat + 3 + j.toNat]'(by omega) = f0 := by
                          have h1 :
                              s.core.arena[(cr.toNat + (3 : BitVec 64).toNat +
                                j.toNat) % 2 ^ 64]'(by rw [hcrj_mod]; omega) = f0 := by
                            assumption
                          simpa only [hcrj_mod] using h1
                        exact hJhf0 true mw ⟨rfl, fun _ => heq ▸ hl_mem⟩
                      · c0_hstep
                        exact hJhf0 hf0 mw ⟨rfl, hmem⟩
                  · exact hJj (j, hf0, false) mw ⟨rfl, fun _ hf => hmem hf⟩
              · exact hJs2 r0n mw ⟨hr0n_le, sbr, hmw, hsbr_l, hrow⟩
              · exact hJs2 r0n mw ⟨hr0n_le, sbr, hmw, hsbr_l, hrow⟩
              · exact hJs2 r0n mw ⟨hr0n_le, sbr, hmw, hsbr_l, hrow⟩
          · subst mf
            let stw : FullState := { s with scratch := { s.scratch with scratch_buf := sbr } }
            have hinvw : FullDenseInvW c F0 F_cur stw :=
              ⟨⟨hclen, { hslen with scratch_buf_len := hsbr_l }⟩,
               { hinv.2.1 with
                 arena := { hinv.2.1.arena with len_ok := hinv.2.1.arena.len_ok }
                 watches := hinv.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
               hinv.2.2.1, hinv.2.2.2.1, hinv.2.2.2.2.1, hinv.2.2.2.2.2.1, hinv.2.2.2.2.2.2⟩
            c0_hfast
            c0_hsplit
            · exact hQ false stw mw hinvw.toDense (Nat.le_refl _) rfl rfl rfl hmw
            · have hqn2 : 2 ≤ r0n.toNat := by
                have h1 : ¬ r0n.toNat < 2 := by assumption
                omega
              have hsb_len : sbr.length = c.scratch_cap := hsbr_l
              have hlm_len : s.core.lit_mark.length = 2 * c.max_vars := hclen.lit_mark_len
              have h0_sb : 0 < sbr.length := by omega
              have h32_sb : 32 < (sbr.set 0 f0).length := by rw [List.length_set]; omega
              have hf0_lm : (BitVec.setWidth 64 f0).toNat < s.core.lit_mark.length := by
                rw [bv64_setWidth_32, hlm_len]; omega
              c0_hfast_nogrp
              let sb1 := (sbr.set 0 f0).set 32 r0n
              let lm1 := s.core.lit_mark.set f0.toNat 1#8
              have hmat1 : M4BvaMatrixInv c F_cur
                  { stw with scratch := { stw.scratch with scratch_buf := sb1 } } 1 :=
                m7BvaMatrixInv_step1 hcap_ge hsbr_l hf0_lt hqn2 hr0n_le hrow
              obtain ⟨hlm1_hi, hlm1_set, hlm1_only⟩ :=
                m7_bva_try_lit_lm1_init hcap_ge hsbr_l hlm_len
                (show f0.toNat < 2 * c.max_vars by omega) hinv.2.2.1.2
              have hsb1_l : sb1.length = c.scratch_cap := by
                dsimp only [sb1]; rw [List.length_set, List.length_set, hsbr_l]
              have hlm1_l : lm1.length = 2 * c.max_vars := by
                dsimp only [lm1]; rw [List.length_set, hlm_len]
              have hinv1_core : FullState.LengthsOk c
                  ⟨{ s.core with lit_mark := lm1 }, { s.scratch with scratch_buf := sb1 }⟩ :=
                ⟨{ hclen with lit_mark_len := hlm1_l },
                 { hslen with scratch_buf_len := hsb1_l }⟩
              let StepInvBody : BitVec 32 → BitVec 32 → FullState → Mem 64 → Prop :=
                fun step best_k stl ml =>
                  (FullMem c stl ⋆ R) ml ∧
                  stl.LengthsOk c ∧ FullWitnessInv c F0 F_cur stl.core ∧
                  FullArenaVarsNodup stl ∧ FullExtScratchOk c stl ∧
                  stl.core.cur_level = 0 ∧ stl.core.dense_mode ≠ 0#64 ∧
                  stl.core.cur_vars = s.core.cur_vars ∧ stl.core.fuel = s.core.fuel ∧
                  stl.core.arena = s.core.arena ∧ stl.core.arena_len = s.core.arena_len ∧
                  stl.core.mrk = s.core.mrk ∧
                  stl.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
                  stl.scratch.tarjan_reach = s.scratch.tarjan_reach ∧
                  1 ≤ step.toNat ∧ step.toNat ≤ 32 ∧
                  M4BvaMatrixInv c F_cur stl step.toNat ∧
                  (best_k = 0#32 ∨ (1 ≤ best_k.toNat ∧ best_k.toNat < step.toNat)) ∧
                  (∀ l < 2 * c.max_vars, (stl.core.lit_mark[l]?.getD 0#8 &&& 0xFE#8) = 0#8) ∧
                  (∀ r < step.toNat,
                    (stl.core.lit_mark[(stl.scratch.scratch_buf[r]?.getD 0#32).toNat]?.getD 0#8 &&&
                      1#8) ≠ 0#8) ∧
                  (∀ l < 2 * c.max_vars, (stl.core.lit_mark[l]?.getD 0#8 &&& 1#8) ≠ 0#8 →
                    ∃ r < step.toNat, (stl.scratch.scratch_buf[r]?.getD 0#32).toNat = l)
              refine wp_join_state (α := BitVec 32 × BitVec 32 × BitVec 32 × BitVec 64)
                (fun (a, b, c, d) => (a, b, c, d, ()))
                (fun (step, _, best_k, _) ml => ∃ stl, StepInvBody step best_k stl ml)
                (fun _ (step, _, best_k, best_red) ml
                    ⟨stl, hml, hlenl, hwl, hndl, hextl, hlv0l, hdml, hcvl, hfuell, harl, hall,
                     hmrkl, html, htrl, hst1, hst32, hmatl, hbkl, hlml_hi, hlml_set,
                     hlml_only⟩ => ?_)
                (fun Jexit hJexit => ?_)
              rotate_left 1
              · refine wp_loop_inv
                  (fun (step, cur_qn, best_k, _, ()) ml => ∃ stl,
                    cur_qn.toNat =
                      (stl.scratch.scratch_buf[32 + (step.toNat - 1)]?.getD 0#32).toNat ∧
                    StepInvBody step best_k stl ml)
                  (fun (step, _, _, _, _) _ => 32 - step.toNat)
                  (fun Jst hJst => by
                    c0_hfast
                    refine hJst (1#32, r0n, 0#32, 0#64, ()) _
                      ⟨{ core := { s.core with lit_mark := lm1 }
                         scratch := { s.scratch with scratch_buf := sb1 } },
                       by dsimp only [sb1]
                          rw [show 32 + ((1#32).toNat - 1) = 32 from rfl,
                            List.getElem?_set_self (by simp [hsb_len]; omega), Option.getD_some],
                       by simp only [bv64_setWidth_32] at hm; exact hm,
                       hinv1_core,
                       { hinv.2.1 with
                         arena := { hinv.2.1.arena with len_ok := hinv.2.1.arena.len_ok }
                         watches := hinv.2.1.watches.with_wstk rfl rfl rfl rfl rfl
                           (fun _ hr => hr) },
                       hinv.2.2.2.1, hinv.2.2.2.2.1, hinv.2.2.2.2.2.1, hinv.2.2.2.2.2.2,
                       rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide,
                       m7BvaMatrixInv_congr rfl rfl rfl rfl hmat1,
                       Or.inl rfl, hlm1_hi, hlm1_set, hlm1_only⟩)
                  (fun Jst (step, cur_qn, best_k, best_red, ()) ml
                      ⟨stl, hcurqn_eq, hml, hlenl, hwl, hndl, hextl, hlv0l, hdml, hcvl, hfuell,
                       harl, hall, hmrkl, html, htrl, hst1, hst32, hmatl, hbkl, hlml_hi,
                       hlml_set, hlml_only⟩ ihst => ?_)
                clear hinv1_core hsb1_l hlm1_l hlm1_hi hlm1_set hlm1_only hmat1 sb1 lm1
                c0_hsplit
                · have hst_lt : step.toNat < 32 := by assumption
                  have hrow_off :
                      ((64 : BitVec 32) + (step - 1) * 256).toNat = 64 + (step.toNat - 1) * 256 :=
                    m7_bv32_step_row_n hst1 hst_lt
                  have hqn256_l : cur_qn.toNat ≤ 256 := by
                    rw [hcurqn_eq]; exact (hmatl.2.2.2 (step.toNat - 1) (by omega)).2.2.1
                  have hqn2_l : 2 ≤ cur_qn.toNat := by
                    rw [hcurqn_eq]; exact (hmatl.2.2.2 (step.toNat - 1) (by omega)).2.1
                  c0_hfast_nogrp
                  rotate_left 1
                  · exfalso; have h2n : ((2 : BitVec 32)).toNat = 2 := rfl; omega
                  c0_call hScan
                  refine ⟨c, F0, F_cur, stl, R, rfl, hlenl, hwl, hndl, hextl, hlv0l, hdml,
                    by have := hinit_lits; rw [hcvl]; omega, hlml_hi,
                    by have := hcap_ge; have := hst32; rw [hrow_off]; omega, hqn256_l,
                    fun qi hqi => ?_, hml,
                    fun ncntd ws' ws1' ws2' m1 hlen1 hnc_le hws1_ok hm1 => ?_⟩
                  · rw [hrow_off]
                    rw [hcurqn_eq] at hqi
                    obtain ⟨res, _, _, hok, _, _⟩ :=
                      (hmatl.2.2.2 (step.toNat - 1) (by omega)).2.2.2 qi hqi
                    unfold M4BvaRowEntryOk at hok
                    by_cases hbin :
                        (stl.scratch.scratch_buf[64 + (step.toNat - 1) * 256 + qi]?.getD 0#32 &&&
                          0x80000000#32) ≠ 0#32
                    · rw [ite_eq_left hbin] at hok ⊢; exact hok.1
                    · rw [ite_eq_right hbin] at hok ⊢; exact ⟨hok.1, hok.2.1⟩
                  · have hinit_le_stl : init_lits.toNat ≤ 2 * stl.core.cur_vars := by
                      rw [hcvl]; exact hinit_lits
                    let st1 : FullState :=
                      { stl with scratch :=
                        { stl.scratch with wsort := ws', work_stk1 := ws1', work_stk2 := ws2' } }
                    have hinv1_nl : FullDenseInvNoLm c F0 F_cur st1 :=
                      ⟨hlen1, hwl, hndl, hextl, hlv0l, hdml⟩
                    c0_call hPick
                    refine ⟨c, F0, F_cur, st1, R, rfl, hinv1_nl, by dsimp only [st1]; omega,
                      by dsimp only [st1]; omega, fun i hi => by
                        have := hws1_ok i hi; dsimp only [st1]; omega,
                      hm1, fun bl rp2 mc2 tc2 tl2 ws2 ant2 sig2 shrk2 m2 hinv2 hbl_ok hm2 => ?_⟩
                    let st2 : FullState :=
                      { core := { st1.core with repr := rp2, min_clr := mc2,
                                                tmp_cnt := tc2, tmp_len := tl2 }
                        scratch := { st1.scratch with wsort := ws2, ant_sz := ant2,
                                                      sim_sig := sig2, shrink_stk := shrk2 } }
                    have hmat2 : M4BvaMatrixInv c F_cur st2 step.toNat :=
                      m7BvaMatrixInv_congr rfl rfl rfl rfl hmatl
                    c0_hfast_nogrp
                    · exact hJexit (step, cur_qn, best_k, best_red) m2
                        ⟨st2, hm2, hinv2.1, hinv2.2.1,
                        hinv2.2.2.1, hinv2.2.2.2.1, hinv2.2.2.2.2.1, hinv2.2.2.2.2.2, hcvl, hfuell,
                        harl, hall, hmrkl, html, htrl, hst1, hst32, hmat2, hbkl, hlml_hi,
                        hlml_set, hlml_only⟩
                    · have hbl_lt : bl.toNat < 2 * s.core.cur_vars := by
                        rcases hbl_ok with hff | hlt
                        · exact absurd hff (by assumption)
                        · dsimp only [st1] at hlt; omega
                      have hnrow_off :
                          ((64 : BitVec 32) + step * 256).toNat = 64 + step.toNat * 256 :=
                        m7_bv32_nrow_n hst_lt
                      have hpar_off :
                          ((8256 : BitVec 32) + step * 256).toNat = 8256 + step.toNat * 256 :=
                        m7_bv32_par_n hst_lt
                      c0_call hFilter
                      refine ⟨c, F0, F_cur, st2, R, step.toNat, rfl, hinv2.1, hinv2.2.1,
                        hinv2.2.2.1, hinv2.2.2.2.1, hinv2.2.2.2.2.1, hinv2.2.2.2.2.2, hst1, hst_lt,
                        hcap_ge, hrow_off, hnrow_off, hpar_off, hcurqn_eq,
                        by dsimp only [st2, st1]; omega, hmat2, hlml_hi, hlml_set, hm2,
                        fun new_qn sb3 m3 hlen3 hnq256 hpres3 hnew3 hm3 => ?_⟩
                      clear hScan hPick hFilter
                      let st3 : FullState :=
                        { st2 with scratch := { st2.scratch with scratch_buf := sb3 } }
                      have hpres3' : ∀ idx < c.scratch_cap,
                          ¬ (64 + step.toNat * 256 ≤ idx ∧ idx < 64 + step.toNat * 256 + 256) →
                          ¬ (8256 + step.toNat * 256 ≤ idx ∧ idx < 8256 + step.toNat * 256 + 256) →
                          sb3[idx]? = st2.scratch.scratch_buf[idx]? := fun idx hi h1 h2 =>
                        hpres3 idx hi (by rw [hnrow_off]; exact h1) (by rw [hpar_off]; exact h2)
                      c0_hsplit
                      · c0_hfast_nogrp
                        refine hJexit (step, new_qn, best_k, best_red) m3
                          ⟨st3, hm3, hlen3, hinv2.2.1, hinv2.2.2.1, hinv2.2.2.2.1,
                           hinv2.2.2.2.2.1, hinv2.2.2.2.2.2, hcvl, hfuell,
                          harl, hall, hmrkl, html, htrl, hst1, hst32,
                          m7BvaMatrixInv_of_filter_pres hst_lt hmat2 hpres3',
                          hbkl, hlml_hi, fun r hr => by
                            dsimp only [st3]
                            rw [hpres3' r (by omega) (by omega) (by omega)]
                            exact hlml_set r hr,
                          fun l hl hne => ?_⟩
                        obtain ⟨r, hr, heq⟩ := hlml_only l hl hne
                        refine ⟨r, hr, ?_⟩
                        dsimp only [st3]; rw [hpres3' r (by omega) (by omega) (by omega)]; exact heq
                      · have hnq2 : 2 ≤ new_qn.toNat := by
                          have h1 : ¬ new_qn.toNat < (2 : BitVec 32).toNat := by assumption
                          change ¬ new_qn.toNat < 2 at h1; omega
                        have h32step : ((32 : BitVec 32) + step).toNat = 32 + step.toNat :=
                          m7_bv32_32add_n hst_lt
                        have hstep1_n : (step + 1#32).toNat = step.toNat + 1 :=
                          m7_bv32_add1_n (Nat.lt_trans hst_lt (by decide))
                        let sb4 := (sb3.set step.toNat bl).set (32 + step.toNat) new_qn
                        let lm4 := st2.core.lit_mark.set bl.toNat 1#8
                        have hsb3_l : sb3.length = c.scratch_cap := hlen3.scratch_ok.scratch_buf_len
                        have hlm3_l : st2.core.lit_mark.length = 2 * c.max_vars :=
                          hlen3.core_ok.lit_mark_len
                        have hsb4_l : sb4.length = c.scratch_cap := by
                          dsimp only [sb4]; rw [List.length_set, List.length_set, hsb3_l]
                        have hlm4_l : lm4.length = 2 * c.max_vars := by
                          dsimp only [lm4]; rw [List.length_set, hlm3_l]
                        have hmat4 := m7BvaMatrixInv_extend_step hst1 hst_lt hmat2 hsb3_l
                          (by dsimp only [st2, st1]; rw [hcvl]; exact hbl_lt) hnq2 hnq256 hpres3'
                          (fun nm hnm => by
                            have h1 := hnew3 nm hnm
                            rw [hrow_off, hnrow_off, hpar_off, hcurqn_eq] at h1; exact h1)
                        let st4 : FullState :=
                          { core := { st2.core with lit_mark := lm4 }
                            scratch := { st2.scratch with scratch_buf := sb4 } }
                        have hst_sb : (BitVec.setWidth 64 step).toNat < sb3.length := by
                          rw [bv64_setWidth_32, hsb3_l]; omega
                        have h32st_b : (BitVec.setWidth 64 ((32 : BitVec 32) + step)).toNat <
                            (sb3.set (BitVec.setWidth 64 step).toNat bl).length := by
                          rw [bv64_setWidth_32, h32step, List.length_set, hsb3_l]; omega
                        have hbl_lm : (BitVec.setWidth 64 bl).toNat < st2.core.lit_mark.length := by
                          rw [bv64_setWidth_32, hlm3_l]; omega
                        c0_hfast_nogrp
                        refine wp_join_state (α := BitVec 32 × BitVec 64)
                          (fun ⟨bk', br'⟩ => (bk', br', ()))
                          (fun ⟨bk', _⟩ mf4 =>
                            (bk' = 0#32 ∨ (1 ≤ bk'.toNat ∧ bk'.toNat < step.toNat + 1)) ∧ mf4 = m)
                          (fun _ ⟨bk', br'⟩ mf4 ⟨hbk', hmf4⟩ => ?_)
                          (fun Jbk hJbk => ?_)
                        · subst mf4
                          c0_hfast_nogrp
                          have ⟨hlm4_hi, hlm4_set, hlm4_only⟩ := m7_bva_try_lit_extend_lm (bl := bl)
                            (new_qn := new_qn) hcap_ge hst_lt hlm3_l hsb3_l (by omega) hpres3'
                            hlml_hi hlml_set hlml_only
                          refine ihst (step + 1#32, new_qn, bk', br', ()) m
                            (by dsimp only; rw [hstep1_n]
                                exact Nat.sub_lt_sub_left hst_lt (Nat.lt_succ_self _))
                            ⟨st4,
                             by dsimp only [st4, sb4]
                                rw [hstep1_n, Nat.add_sub_cancel,
                                  List.getElem?_set_self (by rw [List.length_set, hsb3_l]; omega),
                                  Option.getD_some],
                             by simp only [bv64_setWidth_32, h32step] at hm; exact hm,
                             ⟨{ hlen3.core_ok with lit_mark_len := hlm4_l },
                              { hlen3.scratch_ok with scratch_buf_len := hsb4_l }⟩,
                             { hinv2.2.1 with
                               arena := { hinv2.2.1.arena with len_ok := hinv2.2.1.arena.len_ok }
                               watches := hinv2.2.1.watches.with_wstk rfl rfl rfl rfl rfl
                                 (fun _ hr => hr) },
                             hinv2.2.2.1, hinv2.2.2.2.1, hinv2.2.2.2.2.1, hinv2.2.2.2.2.2,
                             hcvl, hfuell, harl, hall, hmrkl, html, htrl,
                             by rw [hstep1_n]; exact Nat.le_trans hst1 (Nat.le_succ _),
                             by rw [hstep1_n]; exact hst_lt,
                             by rw [hstep1_n]; exact m7BvaMatrixInv_congr rfl rfl rfl rfl hmat4,
                             by rw [hstep1_n]; exact hbk',
                             hlm4_hi, by rw [hstep1_n]; exact hlm4_set,
                             by rw [hstep1_n]; exact hlm4_only⟩
                        · clear hmat4 hmat2 hmatl hml hm1 hm2 hm hinv2 hlen3 hlenl hwl hndl hextl
                          clear hpres3 hpres3' hnew3 hlml_hi hlml_set hlml_only hst_sb
                          clear h32st_b hbl_lm
                          clear hsb4_l hlm4_l hsb3_l hlm3_l hinv1_nl hbl_ok st4 st3 st2 st1 sb4 lm4
                          c0_hfast
                          · have hstp1_sub :
                                step + (1 : BitVec 32) - (1 : BitVec 32) = step := by
                              apply BitVec.eq_of_toNat_eq
                              have h1n : ((1 : BitVec 32)).toNat = 1 := rfl
                              have h1 :
                                  ((1 : BitVec 32)).toNat ≤ (step + (1 : BitVec 32)).toNat := by
                                change 1 ≤ (step + 1#32).toNat; rw [hstep1_n]; omega
                              rw [BitVec.toNat_sub_of_le h1]
                              change (step + 1#32).toNat - 1 = step.toNat
                              rw [hstep1_n]; omega
                            rw [hstp1_sub]
                            exact hJbk ⟨step, _⟩ m ⟨Or.inr ⟨hst1, Nat.lt_succ_self _⟩, rfl⟩
                          all_goals
                            exact hJbk ⟨best_k, best_red⟩ m
                              ⟨hbkl.imp id (fun ⟨h1, h2⟩ => ⟨h1, Nat.lt_succ_of_lt h2⟩), rfl⟩
                · c0_hfast_nogrp
                  exact hJexit (step, cur_qn, best_k, best_red) ml
                    ⟨stl, hml, hlenl, hwl, hndl, hextl, hlv0l, hdml, hcvl, hfuell, harl, hall,
                     hmrkl, html, htrl, hst1, hst32, hmatl, hbkl, hlml_hi, hlml_set,
                     hlml_only⟩
              · -- Exit of `step` loop: clear `counted[scr[0..step)]`
                c0_hfast_nogrp
                refine wp_loop_inv (ts := [i32])
                  (fun (ci, ()) mc => ∃ lmi : List (BitVec 8),
                    let stc : FullState := { stl with core := { stl.core with lit_mark := lmi } }
                    (FullMem c stc ⋆ R) mc ∧ lmi.length = 2 * c.max_vars ∧
                    ci.toNat ≤ step.toNat ∧
                    (∀ l < 2 * c.max_vars, (lmi[l]?.getD 0#8 &&& 0xFE#8) = 0#8) ∧
                    (∀ l < 2 * c.max_vars, (lmi[l]?.getD 0#8 &&& 1#8) ≠ 0#8 →
                      ∃ r, ci.toNat ≤ r ∧ r < step.toNat ∧
                        (stl.scratch.scratch_buf[r]?.getD 0#32).toNat = l))
                  (fun (ci, _) _ => step.toNat - ci.toNat)
                  (fun Jci hJci => hJci (0#32, ()) ml
                    ⟨stl.core.lit_mark, hml, hlenl.core_ok.lit_mark_len, Nat.zero_le _,
                     hlml_hi, fun l hl hne => by
                       obtain ⟨r, hr, heq⟩ := hlml_only l hl hne
                       exact ⟨r, Nat.zero_le _, hr, heq⟩⟩)
                  (fun Jci (ci, ()) mc ⟨lmi, hmc, hlmi_l, hci_le, hlmi_hi, hlmi_only⟩ ihci => ?_)
                c0_hsplit
                · have hci_lt : ci.toNat < step.toNat := by assumption
                  have hci_sb : (BitVec.setWidth 64 ci).toNat < stl.scratch.scratch_buf.length := by
                    rw [bv64_setWidth_32, hlenl.scratch_ok.scratch_buf_len]; omega
                  have hci_sb' : ci.toNat < stl.scratch.scratch_buf.length := by
                    simpa only [bv64_setWidth_32] using hci_sb
                  have hci_lm : (BitVec.setWidth 64
                      (stl.scratch.scratch_buf[(BitVec.setWidth 64 ci).toNat]'hci_sb)).toNat <
                      lmi.length := by
                    have hr_lt := (hmatl.2.2.2 ci.toNat hci_lt).1
                    rw [List.getElem?_eq_getElem hci_sb', Option.getD_some] at hr_lt
                    rw [bv64_setWidth_32, hlmi_l]
                    exact Nat.lt_of_lt_of_le hr_lt
                      (Nat.mul_le_mul_left 2 (by rw [hcvl]; exact hcv_le))
                  have hci1 : (ci + 1#32).toNat = ci.toNat + 1 :=
                    m7_bv32_add1_n (Nat.lt_trans (Nat.lt_of_lt_of_le hci_lt hst32) (by decide))
                  c0_hfast_nogrp
                  exact ihci (ci + 1#32, ()) m
                    (by dsimp only; rw [hci1]
                        exact Nat.sub_lt_sub_left hci_lt (Nat.lt_succ_self _))
                    ⟨lmi.set (stl.scratch.scratch_buf[ci.toNat]'(by
                        simpa only [bv64_setWidth_32] using hci_sb)).toNat 0#8,
                     by simpa only [bv64_setWidth_32] using hm,
                     by rw [List.length_set, hlmi_l], by rw [hci1]; exact hci_lt,
                     fun l hl => by
                       by_cases he : l = (stl.scratch.scratch_buf[ci.toNat]'(by
                           simpa only [bv64_setWidth_32] using hci_sb)).toNat
                       · subst he; rw [List.getElem?_set_self (by omega), Option.getD_some]
                         decide
                       · rw [List.getElem?_set_ne (Ne.symm he)]; exact hlmi_hi l hl,
                     fun l hl hne => by
                       by_cases he : l = (stl.scratch.scratch_buf[ci.toNat]'(by
                           simpa only [bv64_setWidth_32] using hci_sb)).toNat
                       · subst he; rw [List.getElem?_set_self (by omega), Option.getD_some] at hne
                         exact absurd rfl hne
                       · rw [List.getElem?_set_ne (Ne.symm he)] at hne
                         obtain ⟨r, hr1, hr2, heq⟩ := hlmi_only l hl hne
                         have hner : r ≠ ci.toNat := fun h => by
                           subst h; rw [List.getElem?_eq_getElem (by
                             simpa only [bv64_setWidth_32] using hci_sb), Option.getD_some] at heq
                           exact he heq.symm
                         exact ⟨r, by rw [hci1]; omega, hr2, heq⟩⟩
                · have hlm_clr_done : FullLitMarksClear c
                      { stl with core := { stl.core with lit_mark := lmi } } := by
                    refine m7_bva_try_lit_clear_lm_done (stepf := step.toNat)
                      (fun v hv => ?_) hlmi_hi (fun l hl hne => ?_)
                    · have hmrk_s := hlm.1 v hv
                      rwa [hmrkl]
                    · obtain ⟨r, hr1, hr2, heq⟩ := hlmi_only l hl hne
                      have hci_eq : ci.toNat = step.toNat := by
                        have h1 : ¬ ci.toNat < step.toNat := by assumption
                        omega
                      rw [hci_eq] at hr1; exact ⟨r, hr1, hr2, heq⟩
                  let stc : FullState := { stl with core := { stl.core with lit_mark := lmi } }
                  have hinv_clr : FullDenseInvW c F0 F_cur stc :=
                    ⟨⟨{ hlenl.core_ok with lit_mark_len := hlmi_l }, hlenl.scratch_ok⟩,
                     { hwl with
                       arena := { hwl.arena with len_ok := hwl.arena.len_ok }
                       watches := hwl.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
                     hlm_clr_done, hndl, hextl, hlv0l, hdml⟩
                  have hmat_c : M4BvaMatrixInv c F_cur stc step.toNat :=
                    m7BvaMatrixInv_congr rfl rfl rfl rfl hmatl
                  c0_hsplit
                  · exact hQ false stc mc hinv_clr.toDense (by dsimp only [stc]; omega)
                      hfuell html htrl hmc
                  · have hbk1 : 1 ≤ best_k.toNat := by
                      rcases hbkl with rfl | ⟨h1, _⟩
                      · exact absurd rfl (by assumption)
                      · exact h1
                    have hbk_lt32 : best_k.toNat < 32 := by
                      rcases hbkl with rfl | ⟨_, h2⟩
                      · exact absurd rfl (by assumption)
                      · omega
                    have hbk_lt_st : best_k.toNat < step.toNat := by
                      rcases hbkl with rfl | ⟨_, h2⟩
                      · exact absurd rfl (by assumption)
                      · exact h2
                    have hcore_c : stc.core.fuel = stl.core.fuel := rfl
                    have hcv_c_le : stc.core.cur_vars ≤ c.max_vars := hinv_clr.1.core_ok.cur_vars_le
                    have hcv_c : stc.core.cur_vars = s.core.cur_vars := hcvl
                    have har_c : stc.core.arena = s.core.arena := harl
                    have halen_c : stc.core.arena_len ≤ stc.core.arena.length := by
                      rw [hinv_clr.1.core_ok.arena_len_arr]; exact hinv_clr.1.core_ok.arena_len_le
                    have hbf_end_n : (best_k + 1#32).toNat = best_k.toNat + 1 :=
                      m7_bv32_add1_n (Nat.lt_trans hbk_lt32 (by decide))
                    have h2cv_c : (stc.core.cur_vars <<< 1) % 2 ^ 64 = 2 * stc.core.cur_vars := by
                      rw [Nat.shiftLeft_eq, Nat.pow_one]; omega
                    c0_hfast_nogrp
                    -- Loop 1: collect `scr[fi]` and `scr[fi] ^ 1` for `fi < best_k + 1`
                    refine wp_loop_inv
                      (fun (nt1, fi, ()) mfi => ∃ stfi : FullState,
                        fi.toNat ≤ best_k.toNat + 1 ∧ M7BvaTouchedInv c stc R nt1 stfi mfi)
                      (fun (_, fi, _) _ => best_k.toNat + 1 - fi.toNat)
                      (fun Jfi hJfi => hJfi (0#64, 0#32, ()) mc
                        ⟨stc, Nat.zero_le _, rfl, rfl, rfl, rfl, rfl, rfl,
                         hinv_clr.1.scratch_ok, Nat.zero_le _,
                         fun _ hk => absurd hk (Nat.not_lt_zero _), hmc⟩)
                      (fun Jfi (nt1, fi, ()) mfi ⟨stfi, hfi_le, hcore1, hsb1, htm1, htr1, hll1,
                          hel1, hscl1, hnt1_le, hws2_ok1, hmfi⟩ ihfi => ?_)
                    c0_hsplit
                    · have hfi_lt : fi.toNat < best_k.toNat + 1 := by
                        simpa only [hbf_end_n] using
                          (by assumption : fi.toNat < (best_k + 1#32).toNat)
                      have hfi1 : (fi + 1#32).toNat = fi.toNat + 1 :=
                        m7_bv32_add1_n (by omega)
                      have hfi_sb :
                          (BitVec.setWidth 64 fi).toNat < stfi.scratch.scratch_buf.length := by
                        rw [bv64_setWidth_32, hscl1.scratch_buf_len]; omega
                      have hfi_sb' : fi.toNat < stfi.scratch.scratch_buf.length := by
                        simpa only [bv64_setWidth_32] using hfi_sb
                      have hfl_lt : (stfi.scratch.scratch_buf[fi.toNat]'hfi_sb').toNat <
                          2 * stc.core.cur_vars := by
                        have h1 := (hmat_c.2.2.2 fi.toNat (by omega)).1
                        have hfi_c : fi.toNat < stc.scratch.scratch_buf.length := by
                          rwa [← hsb1]
                        rw [List.getElem?_eq_getElem hfi_c, Option.getD_some] at h1
                        simpa only [hsb1, hcore1] using h1
                      have hfl_ws : (BitVec.setWidth 64
                          (stfi.scratch.scratch_buf[(BitVec.setWidth 64 fi).toNat]'hfi_sb)).toNat <
                          stfi.scratch.wsort.length := by
                        rw [bv64_setWidth_32, hscl1.wsort_len]
                        exact Nat.lt_of_lt_of_le hfl_lt (Nat.mul_le_mul_left 2 hcv_c_le)
                      c0_hfast_nogrp
                      refine wp_join_state (α := BitVec 64 × FullState) (fun x => (x.1, ()))
                        (fun ⟨nt1a, st1a⟩ m1a => M7BvaTouchedInv c stc R nt1a st1a m1a)
                        (fun _ ⟨nt1a, st1a⟩ m1a ⟨hca, hsba, htma, htra, hlla, hela, hscla,
                            hnt1a_le, hws2a_ok, hm1a⟩ => ?_)
                        (fun Ja hJa => ?_)
                      · have heq_fi :
                            stfi.scratch.scratch_buf[(BitVec.setWidth 64 fi).toNat]'hfi_sb =
                              stfi.scratch.scratch_buf[fi.toNat]'hfi_sb' := by
                          simp only [bv64_setWidth_32]
                        have hneg_lt_fi : (stfi.scratch.scratch_buf[fi.toNat]'hfi_sb' ^^^
                            1#32).toNat < 2 * stc.core.cur_vars := by
                          rw [BitVec.toNat_xor, show (1#32).toNat = 1 from rfl]
                          exact litNeg_lt_two_mul hfl_lt
                        have hneg_lt :
                            (stfi.scratch.scratch_buf[(BitVec.setWidth 64 fi).toNat]'hfi_sb ^^^
                              1#32).toNat < 2 * stc.core.cur_vars := by
                          rw [heq_fi]; exact hneg_lt_fi
                        have hneg_ws : (BitVec.setWidth 64
                            ((stfi.scratch.scratch_buf[(BitVec.setWidth 64 fi).toNat]'hfi_sb) ^^^
                              1#32)).toNat < st1a.scratch.wsort.length := by
                          rw [bv64_setWidth_32, hscla.wsort_len]
                          exact Nat.lt_of_lt_of_le hneg_lt (Nat.mul_le_mul_left 2 hcv_c_le)
                        refine wp_join_state (α := BitVec 64 × FullState) (fun x => (x.1, ()))
                          (fun ⟨nt1b, st1b⟩ m1b => M7BvaTouchedInv c stc R nt1b st1b m1b)
                          (fun _ ⟨nt1b, st1b⟩ m1b hinv1b =>
                            ihfi (nt1b, fi + 1#32, ()) m1b
                              (by dsimp only; rw [hfi1]; omega)
                              ⟨st1b, by rw [hfi1]; exact hfi_lt, hinv1b⟩)
                          (fun Jb hJb => ?_)
                        c0_hsplit
                        · c0_hsplit
                          · have hnt1a_lt : nt1a.toNat < 2 * stc.core.cur_vars := by
                              rw [show 2 * stc.core.cur_vars =
                                  2 * (stl.core.cur_vars % 2 ^ 64) % 2 ^ 64 by omega]
                              assumption
                            have hnt1a_ws2 : nt1a.toNat < st1a.scratch.work_stk2.length := by
                              rw [hscla.work_stk2_len]
                              exact Nat.lt_of_lt_of_le hnt1a_lt (Nat.mul_le_mul_left 2 hcv_c_le)
                            c0_hfast_nogrp; dsimp only at hm
                            exact hJb ⟨nt1a + 1#64, _⟩ m
                              (m7_bva_touched_push hcv_c_le hmx hnt1a_lt hneg_lt hca hsba htma htra
                                hlla hela hscla hws2a_ok hm)
                          · exact hJb ⟨nt1a, st1a⟩ m1a
                              ⟨hca, hsba, htma, htra, hlla, hela, hscla, hnt1a_le, hws2a_ok, hm1a⟩
                        · exact hJb ⟨nt1a, st1a⟩ m1a
                            ⟨hca, hsba, htma, htra, hlla, hela, hscla, hnt1a_le, hws2a_ok, hm1a⟩
                      · c0_hsplit
                        · c0_hsplit
                          · have hnt1_lt : nt1.toNat < 2 * stc.core.cur_vars := by
                              rw [show 2 * stc.core.cur_vars =
                                  2 * (stl.core.cur_vars % 2 ^ 64) % 2 ^ 64 by omega]
                              assumption
                            have hnt1_ws2 : nt1.toNat < stfi.scratch.work_stk2.length := by
                              rw [hscl1.work_stk2_len]
                              exact Nat.lt_of_lt_of_le hnt1_lt (Nat.mul_le_mul_left 2 hcv_c_le)
                            c0_hfast_nogrp; dsimp only at hm
                            exact hJa ⟨nt1 + 1#64, _⟩ m
                              (m7_bva_touched_push hcv_c_le hmx hnt1_lt hfl_lt hcore1 hsb1 htm1
                                htr1 hll1 hel1 hscl1 hws2_ok1 hm)
                          · exact hJa ⟨nt1, stfi⟩ mfi
                              ⟨hcore1, hsb1, htm1, htr1, hll1, hel1, hscl1, hnt1_le, hws2_ok1, hmfi⟩
                        · exact hJa ⟨nt1, stfi⟩ mfi
                            ⟨hcore1, hsb1, htm1, htr1, hll1, hel1, hscl1, hnt1_le, hws2_ok1, hmfi⟩
                    · -- Loop 2: collect literals from best row `scr[brow_off + qi]`
                      obtain ⟨_, hqn_best2, hqn_best256, hrow_best⟩ :=
                        hmat_c.2.2.2 best_k.toNat hbk_lt_st
                      have h32bk_n : ((32 : BitVec 32) + best_k).toNat = 32 + best_k.toNat :=
                        m7_bv32_32add_n hbk_lt32
                      have h32bk_sb : (BitVec.setWidth 64 ((32 : BitVec 32) + best_k)).toNat <
                          stfi.scratch.scratch_buf.length := by
                        rw [bv64_setWidth_32, h32bk_n, hscl1.scratch_buf_len]; omega
                      have hbk_sb : (BitVec.setWidth 64 best_k).toNat <
                          stfi.scratch.scratch_buf.length := by
                        rw [bv64_setWidth_32, hscl1.scratch_buf_len]; omega
                      have hbrow_n :
                          ((64 : BitVec 32) + best_k * 256).toNat = 64 + best_k.toNat * 256 :=
                        m7_bv32_nrow_n hbk_lt32
                      c0_hfast_nogrp
                      let qn_best := stc.scratch.scratch_buf[32 + best_k.toNat]'(by
                        rw [hinv_clr.1.scratch_ok.scratch_buf_len]; omega)
                      let bkey := stc.scratch.scratch_buf[best_k.toNat]'(by
                        rw [hinv_clr.1.scratch_ok.scratch_buf_len]; omega)
                      refine wp_loop_inv
                        (fun (ntm, qim, ()) mtm => ∃ stm : FullState,
                          qim.toNat ≤ qn_best.toNat ∧ M7BvaTouchedInv c stc R ntm stm mtm)
                        (fun (_, qim, _) _ => qn_best.toNat - qim.toNat)
                        (fun Jtm hJtm => hJtm (nt1, 0#32, ()) mfi
                          ⟨stfi, Nat.zero_le _, hcore1, hsb1, htm1, htr1, hll1, hel1, hscl1,
                           hnt1_le, hws2_ok1, hmfi⟩)
                        (fun Jtm (ntm, qim, ()) mtm ⟨stm, hqim_le, hcorem, hsbm, htmm, htrm,
                            hllm, helm, hsclm, hntm_le, hws2m_ok, hmtm⟩ ihtm => ?_)
                      c0_hsplit
                      · have h32bk_mod :
                            ((32 : BitVec 32).toNat + best_k.toNat) % 2 ^ 32 =
                              32 + best_k.toNat := by
                          rw [show (32 : BitVec 32).toNat = 32 from rfl,
                            Nat.mod_eq_of_lt (by omega)]
                        have hqim_lt : qim.toNat < qn_best.toNat := by
                          have h1 : qim.toNat <
                              (stfi.scratch.scratch_buf[
                                ((32 : BitVec 32).toNat + best_k.toNat) % 2 ^ 32]'(by
                                  rw [h32bk_mod, hscl1.scratch_buf_len]; omega)).toNat := by
                            assumption
                          simp only [h32bk_mod] at h1
                          have h1' : qim.toNat < (stc.scratch.scratch_buf[32 + best_k.toNat]'(by
                              rw [hinv_clr.1.scratch_ok.scratch_buf_len]; omega)).toNat := by
                            simpa only [← hsb1] using h1
                          exact h1'
                        have hqn_best256' : qn_best.toNat ≤ 256 := by
                          have h2 := hqn_best256
                          rw [List.getElem?_eq_getElem
                            (by rw [hinv_clr.1.scratch_ok.scratch_buf_len]; omega),
                            Option.getD_some] at h2
                          exact h2
                        have hqim1 : (qim + 1#32).toNat = qim.toNat + 1 :=
                          m7_bv32_add1_n (Nat.lt_trans (Nat.lt_of_lt_of_le hqim_lt hqn_best256')
                            (by decide))
                        have hrow_idx_n : (64 + best_k * 256 + qim).toNat =
                            64 + best_k.toNat * 256 + qim.toNat :=
                          m7_bv32_row_idx_n hbk_lt32 (by omega)
                        have hrow_idx_sb :
                            (BitVec.setWidth 64 (64 + best_k * 256 + qim)).toNat <
                              stm.scratch.scratch_buf.length := by
                          rw [bv64_setWidth_32, hrow_idx_n, hsclm.scratch_buf_len]; omega
                        have hqim_lt_row : qim.toNat <
                            (stc.scratch.scratch_buf[32 + best_k.toNat]?.getD 0#32).toNat := by
                          dsimp only [qn_best] at hqim_lt
                          rw [List.getElem?_eq_getElem
                              (by rw [hinv_clr.1.scratch_ok.scratch_buf_len]; omega),
                            Option.getD_some]
                          exact hqim_lt
                        obtain ⟨res_t, _, _, hct_ok, _, _⟩ := hrow_best qim.toNat hqim_lt_row
                        let ct := stc.scratch.scratch_buf[64 + best_k.toNat * 256 + qim.toNat]'(by
                          rw [hinv_clr.1.scratch_ok.scratch_buf_len]; omega)
                        have hct_getD :
                            stc.scratch.scratch_buf[64 + best_k.toNat * 256 + qim.toNat]?.getD
                              0#32 = ct := by
                          dsimp only [ct]
                          rw [List.getElem?_eq_getElem
                              (by rw [hinv_clr.1.scratch_ok.scratch_buf_len]; omega),
                            Option.getD_some]
                        rw [hct_getD] at hct_ok
                        have hct_eq_m :
                            stm.scratch.scratch_buf[
                              (BitVec.setWidth 64 (64 + best_k * 256 + qim)).toNat]'hrow_idx_sb =
                                ct := by
                          dsimp only [ct]
                          simp only [hsbm, bv64_setWidth_32, hrow_idx_n]
                        have hrow_mod := m7_bv32_row_mod_n hbk_lt32
                          (Nat.lt_of_lt_of_le hqim_lt hqn_best256')
                        c0_hfast_nogrp
                        c0_hstep
                        c0_hsplit
                        · have hbin_ct : (ct &&& 0x80000000#32) ≠ 0#32 := by
                            intro heq
                            have heq_m :
                                stm.scratch.scratch_buf[(BitVec.toNat 64 +
                                  best_k.toNat * BitVec.toNat 256 + qim.toNat) % 2 ^ 32]'(by
                                    rw [hrow_mod, hsbm, hinv_clr.1.scratch_ok.scratch_buf_len]
                                    omega) &&& 0x80000000#32 = 0#32 := by
                              dsimp only [ct] at heq; simpa only [hrow_mod, hsbm] using heq
                            contradiction
                          unfold M4BvaRowEntryOk at hct_ok
                          rw [ite_eq_left hbin_ct] at hct_ok
                          have hot_lt : (ct &&& 0x7FFFFFFF#32).toNat < 2 * stc.core.cur_vars :=
                            hct_ok.1
                          have hot_ws : (BitVec.setWidth 64 (ct &&& 0x7FFFFFFF#32)).toNat <
                              stm.scratch.wsort.length := by
                            rw [bv64_setWidth_32, hsclm.wsort_len]
                            exact Nat.lt_of_lt_of_le hot_lt (Nat.mul_le_mul_left 2 hcv_c_le)
                          have hot_ws_m := hot_ws
                          rw [← hct_eq_m] at hot_ws_m
                          c0_hfast_nogrp
                          c0_hstep
                          c0_hsplit
                          · c0_hsplit
                            · have hntm_lt : ntm.toNat < 2 * stc.core.cur_vars := by
                                rw [show 2 * stc.core.cur_vars =
                                    2 * (stl.core.cur_vars % 2 ^ 64) % 2 ^ 64 by omega]
                                assumption
                              have hntm_ws2 : ntm.toNat < stm.scratch.work_stk2.length := by
                                rw [hsclm.work_stk2_len]
                                exact Nat.lt_of_lt_of_le hntm_lt (Nat.mul_le_mul_left 2 hcv_c_le)
                              c0_hfast_nogrp; dsimp only at hm
                              exact ihtm (ntm + 1#64, qim + 1#32, ()) m
                                (by dsimp only; rw [hqim1]
                                    exact Nat.sub_lt_sub_left hqim_lt (Nat.lt_succ_self _))
                                ⟨_, by rw [hqim1]; exact hqim_lt,
                                 m7_bva_touched_push hcv_c_le hmx hntm_lt hot_lt
                                   hcorem hsbm htmm htrm hllm helm hsclm hws2m_ok
                                   (by rw [← hct_eq_m]; exact hm)⟩
                            · c0_hfast_nogrp
                              exact ihtm (ntm, qim + 1#32, ()) mtm
                                (by dsimp only; rw [hqim1]
                                    exact Nat.sub_lt_sub_left hqim_lt (Nat.lt_succ_self _))
                                ⟨stm, by rw [hqim1]; exact hqim_lt, hcorem, hsbm, htmm, htrm,
                                 hllm, helm, hsclm, hntm_le, hws2m_ok, hmtm⟩
                          · c0_hfast_nogrp
                            exact ihtm (ntm, qim + 1#32, ()) mtm
                              (by dsimp only; rw [hqim1]
                                  exact Nat.sub_lt_sub_left hqim_lt (Nat.lt_succ_self _))
                              ⟨stm, by rw [hqim1]; exact hqim_lt, hcorem, hsbm, htmm, htrm,
                               hllm, helm, hsclm, hntm_le, hws2m_ok, hmtm⟩
                        · have hbin_ct : (ct &&& 0x80000000#32) = 0#32 := by
                            apply Classical.byContradiction; intro hne
                            have hne_m :
                                stm.scratch.scratch_buf[(BitVec.toNat 64 +
                                  best_k.toNat * BitVec.toNat 256 + qim.toNat) % 2 ^ 32]'(by
                                    rw [hrow_mod, hsbm, hinv_clr.1.scratch_ok.scratch_buf_len]
                                    omega) &&& 0x80000000#32 ≠ 0#32 := by
                              dsimp only [ct] at hne; simpa only [hrow_mod, hsbm] using hne
                            first | exact absurd (by assumption) hne_m | contradiction
                          unfold M4BvaRowEntryOk at hct_ok
                          rw [ite_eq_right (fun h' => h' hbin_ct)] at hct_ok
                          obtain ⟨hct_ref, hct_ng, _, hct_sz256, _, _, _⟩ := hct_ok
                          have hct_wf := hinv_clr.2.1.arena.refs_wf ct.toNat hct_ref
                          have hct2_n : (BitVec.setWidth 64 ct + 2).toNat = ct.toNat + 2 :=
                            m7_bv64_add2_n
                          have hct2_lt_c : ct.toNat + 2 < stc.core.arena.length := by
                            have := hct_wf.1; exact Nat.lt_of_lt_of_le (by omega) halen_c
                          have hct2_ar : (BitVec.setWidth 64 ct + 2).toNat <
                              stm.core.arena.length := by
                            rw [hct2_n, hcorem]; exact hct2_lt_c
                          have hct_sz_eq : (stc.core.arena[ct.toNat + 2]'hct2_lt_c).toNat =
                              fullArenaClauseSizeCore stc.core ct.toNat := by
                            unfold fullArenaClauseSizeCore
                            rw [List.getElem?_eq_getElem hct2_lt_c, Option.getD_some]
                          let csz_t := stc.core.arena[ct.toNat + 2]'hct2_lt_c
                          have hcsz_256 : csz_t.toNat ≤ 256 := by
                            dsimp only [csz_t]; rw [hct_sz_eq]; exact hct_sz256
                          have hct_end_ar : ct.toNat + 3 + csz_t.toNat ≤ stc.core.arena.length := by
                            dsimp only [csz_t]; rw [hct_sz_eq]
                            exact Nat.le_trans hct_wf.2.2.1 (Nat.le_trans hct_wf.2.2.2.1 halen_c)
                          c0_hfast_nogrp
                          refine wp_loop_inv
                            (fun (ntj, tj, ()) mtj => ∃ stj : FullState,
                              tj.toNat ≤ csz_t.toNat ∧ M7BvaTouchedInv c stc R ntj stj mtj)
                            (fun (_, tj, _) _ => csz_t.toNat - tj.toNat)
                            (fun Jtj hJtj => hJtj (ntm, 0#32, ()) mtm
                              ⟨stm, Nat.zero_le _, hcorem, hsbm, htmm, htrm, hllm, helm, hsclm,
                               hntm_le, hws2m_ok, hmtm⟩)
                            (fun Jtj (ntj, tj, ()) mtj ⟨stj, htj_le, hcorej, hsbj, htmj, htrj,
                                hllj, helj, hsclj, hntj_le, hws2j_ok, hmtj⟩ ihtj => ?_)
                          c0_hsplit
                          · have htj_lt : tj.toNat < csz_t.toNat := by
                              have hmod2 : (ct.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 =
                                  ct.toNat + 2 := m7_bv64_add2_mod
                              have hsb_idx_lt : ((64 : BitVec 32).toNat +
                                  best_k.toNat * (256 : BitVec 32).toNat + qim.toNat) % 2 ^ 32 <
                                  stm.scratch.scratch_buf.length := by
                                rw [hrow_mod, hsbm, hinv_clr.1.scratch_ok.scratch_buf_len]; omega
                              have hct_mod_m : (stm.scratch.scratch_buf[((64 : BitVec 32).toNat +
                                  best_k.toNat * (256 : BitVec 32).toNat + qim.toNat) %
                                    2 ^ 32]'hsb_idx_lt).toNat = ct.toNat := by
                                dsimp only [ct]; simp only [hrow_mod, hsbm]
                              have har_idx_lt : ((stm.scratch.scratch_buf[((64 : BitVec 32).toNat +
                                  best_k.toNat * (256 : BitVec 32).toNat + qim.toNat) %
                                    2 ^ 32]'hsb_idx_lt).toNat + (2 : BitVec 64).toNat) %
                                  2 ^ 64 < stm.core.arena.length := by
                                rw [hct_mod_m, hmod2, hcorem]; exact hct2_lt_c
                              have h1 : tj.toNat < (stm.core.arena[((stm.scratch.scratch_buf[
                                  ((64 : BitVec 32).toNat + best_k.toNat * (256 : BitVec 32).toNat +
                                    qim.toNat) % 2 ^ 32]'hsb_idx_lt).toNat +
                                  (2 : BitVec 64).toNat) % 2 ^ 64]'har_idx_lt).toNat := by
                                assumption
                              simpa only [csz_t, hct_mod_m, hmod2, hcorem] using h1
                            have htj1 : (tj + 1#32).toNat = tj.toNat + 1 :=
                              m7_bv32_add1_n (Nat.lt_trans (Nat.lt_of_lt_of_le htj_lt hcsz_256)
                                (by decide))
                            have hctj_n :
                                (BitVec.setWidth 64 ct + 3 + BitVec.setWidth 64 tj).toNat =
                                  ct.toNat + 3 + tj.toNat := m7_bv64_add3_n
                            have hctj_ar_c : ct.toNat + 3 + tj.toNat < stc.core.arena.length :=
                              Nat.lt_of_lt_of_le
                                (Nat.add_lt_add_left htj_lt (ct.toNat + 3)) hct_end_ar
                            have hctj_ar_bv :
                                (BitVec.setWidth 64 ct + 3 + BitVec.setWidth 64 tj).toNat <
                                  stj.core.arena.length := by
                              rw [hctj_n, hcorej]; exact hctj_ar_c
                            have hql_mem :
                                (stc.core.arena[ct.toNat + 3 + tj.toNat]'hctj_ar_c).toNat ∈
                                  fullArenaClauseLitsCore stc.core ct.toNat :=
                              List.mem_of_getElem?
                                (FullBvaFwdHelpers.fullArenaClauseLitsCore_getElem
                                  (k := stc.core) (r := ct.toNat) (j := tj.toNat)
                                  (by rw [← hct_sz_eq]; exact htj_lt) hctj_ar_c)
                            have hql_lt :
                                (stc.core.arena[ct.toNat + 3 + tj.toNat]'hctj_ar_c).toNat <
                                  2 * stc.core.cur_vars :=
                              hinv_clr.2.1.arena.lits_lt ct.toNat hct_ref hct_ng _ hql_mem
                            have hql_lt_bv :
                                (stj.core.arena[(BitVec.setWidth 64 ct + 3 +
                                  BitVec.setWidth 64 tj).toNat]'hctj_ar_bv).toNat <
                                  2 * stc.core.cur_vars := by
                              simpa only [hctj_n, hcorej] using hql_lt
                            have hql_ws_bv : (BitVec.setWidth 64
                                (stj.core.arena[(BitVec.setWidth 64 ct + 3 +
                                  BitVec.setWidth 64 tj).toNat]'hctj_ar_bv)).toNat <
                                stj.scratch.wsort.length := by
                              rw [bv64_setWidth_32, hsclj.wsort_len]
                              exact Nat.lt_of_lt_of_le hql_lt_bv (Nat.mul_le_mul_left 2 hcv_c_le)
                            let ct_m := stm.scratch.scratch_buf[
                              (BitVec.setWidth 64 (64 + best_k * 256 + qim)).toNat]'hrow_idx_sb
                            have hctj_ar_m :
                                (BitVec.setWidth 64 ct_m + 3 + BitVec.setWidth 64 tj).toNat <
                                  stj.core.arena.length := by
                              dsimp only [ct_m]; rw [hct_eq_m]; exact hctj_ar_bv
                            have hql_lt_m :
                                (stj.core.arena[(BitVec.setWidth 64 ct_m + 3 +
                                  BitVec.setWidth 64 tj).toNat]'hctj_ar_m).toNat <
                                  2 * stc.core.cur_vars := by
                              dsimp only [ct_m]; simpa only [hct_eq_m] using hql_lt_bv
                            have hql_ws_m : (BitVec.setWidth 64
                                (stj.core.arena[(BitVec.setWidth 64 ct_m + 3 +
                                  BitVec.setWidth 64 tj).toNat]'hctj_ar_m)).toNat <
                                stj.scratch.wsort.length := by
                              rw [bv64_setWidth_32, hsclj.wsort_len]
                              exact Nat.lt_of_lt_of_le hql_lt_m (Nat.mul_le_mul_left 2 hcv_c_le)
                            c0_hfast_nogrp
                            refine wp_join_state1 (t := i64) (α := BitVec 64 × FullState)
                              (fun x => x.1)
                              (fun ⟨ntj1, stj1⟩ mj1 => M7BvaTouchedInv c stc R ntj1 stj1 mj1)
                              (fun _ ⟨ntj1, stj1⟩ mj1 hinvj => by
                                c0_hfast_nogrp
                                exact ihtj (ntj1, tj + 1#32, ()) mj1
                                  (by dsimp only; rw [htj1]
                                      exact Nat.sub_lt_sub_left htj_lt (Nat.lt_succ_self _))
                                  ⟨stj1, by rw [htj1]; exact htj_lt, hinvj⟩)
                              (fun Jq1 hJq1 => ?_)
                            c0_hsplit
                            · c0_hsplit
                              · c0_hsplit
                                · have hntj_lt : ntj.toNat < 2 * stc.core.cur_vars := by
                                    rw [show 2 * stc.core.cur_vars =
                                        2 * (stl.core.cur_vars % 2 ^ 64) % 2 ^ 64 by omega]
                                    assumption
                                  have hntj_ws2 : ntj.toNat < stj.scratch.work_stk2.length := by
                                    rw [hsclj.work_stk2_len]
                                    exact Nat.lt_of_lt_of_le hntj_lt
                                      (Nat.mul_le_mul_left 2 hcv_c_le)
                                  c0_hfast_nogrp; dsimp only at hm
                                  exact hJq1 ⟨ntj + 1#64, _⟩ m
                                    (m7_bva_touched_push hcv_c_le hmx hntj_lt hql_lt_m
                                      hcorej hsbj htmj htrj hllj helj hsclj hws2j_ok
                                      (by simp only [bv64_setWidth_32] at hm; exact hm))
                                · exact hJq1 ⟨ntj, stj⟩ mtj
                                    ⟨hcorej, hsbj, htmj, htrj, hllj, helj, hsclj, hntj_le, hws2j_ok,
                                     hmtj⟩
                              · exact hJq1 ⟨ntj, stj⟩ mtj
                                  ⟨hcorej, hsbj, htmj, htrj, hllj, helj, hsclj, hntj_le, hws2j_ok,
                                   hmtj⟩
                            · exact hJq1 ⟨ntj, stj⟩ mtj
                                ⟨hcorej, hsbj, htmj, htrj, hllj, helj, hsclj, hntj_le, hws2j_ok,
                                 hmtj⟩
                          · c0_hfast_nogrp
                            exact ihtm (ntj, qim + 1#32, ()) mtj
                              (by dsimp only; rw [hqim1]
                                  exact Nat.sub_lt_sub_left hqim_lt (Nat.lt_succ_self _))
                              ⟨stj, by rw [hqim1]; exact hqim_lt, hcorej, hsbj, htmj, htrj, hllj,
                               helj, hsclj, hntj_le, hws2j_ok, hmtj⟩
                      · -- Loop 3: clear `tmark[touched[tz]] = 0`, store `res_sz`, call commit
                        c0_hfast_nogrp
                        refine wp_loop_inv
                          (fun (tz, ()) mtz => ∃ stz : FullState,
                            tz.toNat ≤ ntm.toNat ∧ stz.core = stc.core ∧
                            stz.scratch.scratch_buf = stc.scratch.scratch_buf ∧
                            stz.scratch.tarjan_mark = stc.scratch.tarjan_mark ∧
                            stz.scratch.tarjan_reach = stc.scratch.tarjan_reach ∧
                            stz.scratch.last_learned = stc.scratch.last_learned ∧
                            stz.scratch.extend_len = stc.scratch.extend_len ∧
                            stz.scratch.work_stk2 = stm.scratch.work_stk2 ∧
                            stz.scratch.LengthsOk c ∧ (FullMem c stz ⋆ R) mtz)
                          (fun (tz, _) _ => ntm.toNat - tz.toNat)
                          (fun Jtz hJtz => hJtz (0#64, ()) mtm
                            ⟨stm, Nat.zero_le _, hcorem, hsbm, htmm, htrm, hllm, helm, rfl,
                             hsclm, hmtm⟩)
                          (fun Jtz (tz, ()) mtz ⟨stz, htz_le, hcorez, hsbz, htmz, htrz, hllz, helz,
                              hws2z, hsclz, hmtz⟩ ihtz => ?_)
                        c0_hsplit
                        · have htz_lt : tz.toNat < ntm.toNat := by assumption
                          have htz_max : tz.toNat < 2 * c.max_vars :=
                            Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le htz_lt hntm_le)
                              (Nat.mul_le_mul_left 2 hcv_c_le)
                          have htz1 : (tz + 1#64).toNat = tz.toNat + 1 :=
                            m7_bv64_add1_n (Nat.lt_trans htz_max (by omega))
                          have htz_ws2 : tz.toNat < stz.scratch.work_stk2.length := by
                            rw [hsclz.work_stk2_len]; exact htz_max
                          have htl_lt : (stz.scratch.work_stk2[tz.toNat]'htz_ws2).toNat <
                              2 * stc.core.cur_vars := by
                            have h1 := hws2m_ok tz.toNat htz_lt
                            have htz_m : tz.toNat < stm.scratch.work_stk2.length := by
                              rwa [← hws2z]
                            rw [List.getElem?_eq_getElem htz_m, Option.getD_some] at h1
                            simpa only [hws2z] using h1
                          have htl_wsz : (BitVec.setWidth 64
                              (stz.scratch.work_stk2[tz.toNat]'htz_ws2)).toNat <
                              stz.scratch.wsort.length := by
                            rw [bv64_setWidth_32, hsclz.wsort_len]
                            exact Nat.lt_of_lt_of_le htl_lt (Nat.mul_le_mul_left 2 hcv_c_le)
                          c0_hfast_nogrp; dsimp only at hm
                          exact ihtz (tz + 1#64, ()) m
                            (by dsimp only; rw [htz1]
                                exact Nat.sub_lt_sub_left htz_lt (Nat.lt_succ_self _))
                            (m7_bva_touched_clear_step htz_lt htz1 hcorez hsbz htmz htrz hllz helz
                              hws2z hsclz hm)
                        · c0_hfast
                          let st_tc : FullState :=
                            { stz with scratch := { stz.scratch with res_sz := ntm } }
                          have hinv_tc : FullDenseInvW c F0 F_cur st_tc := by
                            have htc_eq : st_tc = { stc with scratch := st_tc.scratch } := by
                              dsimp only [st_tc]
                              exact congrArg
                                (fun k => ({ core := k,
                                             scratch := { stz.scratch with res_sz := ntm } } :
                                  FullState))
                                hcorez
                            rw [htc_eq]
                            exact fullDenseInv_with_core_aux (tc' := stc.core.tmp_cnt)
                              (tl' := stc.core.tmp_len) (sc' := st_tc.scratch) hinv_clr
                              hinv_clr.1.core_ok.repr_len hinv_clr.1.core_ok.min_clr_len_arr
                              hinv_clr.1.core_ok.tmp_len_arr hinv_clr.1.core_ok.flags_len
                              hinv_clr.1.core_ok.tmp_len_le
                              { hsclz with wsort_len := hsclz.wsort_len } hllz helz
                          have hmat_wk : M4BvaMatrixInv c F_cur stc (best_k.toNat + 1) :=
                            ⟨hmat_c.1, Nat.succ_le_succ (Nat.zero_le _), by omega,
                             fun r hr => hmat_c.2.2.2 r (by omega)⟩
                          have hmat_tc : M4BvaMatrixInv c F_cur st_tc (best_k.toNat + 1) :=
                            m7BvaMatrixInv_congr
                              (by dsimp only [st_tc]; exact congrArg (·.cur_vars) hcorez)
                              (by dsimp only [st_tc]; exact congrArg (·.arena) hcorez)
                              (by dsimp only [st_tc]; exact congrArg (·.arena_len) hcorez)
                              (by dsimp only [st_tc]; exact hsbz)
                              hmat_wk
                          refine wp_call_of_spec _ _ (hCommit _ _ _ _ ?_)
                          refine ⟨c, F0, F_cur, st_tc, R, rfl, hinv_tc, hbk1, hbk_lt32,
                            hmat_tc, hm,
                            fun ok s' m' hinv' hcv' hfuel' htm' htr' hm' =>
                              hQ ok s' m' hinv' (by rw [← hcv_c, ← hcorez]; exact hcv')
                                (hfuel'.trans (by rw [hcorez]; rw [hcore_c]; exact hfuell))
                                (htm'.trans (htmz.trans html))
                                (htr'.trans (htrz.trans htrl)) hm'⟩
        · c0_hfast
          · exact hJicv _ m ⟨by simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega, rfl⟩
          · exact hJicv _ m ⟨by simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega, rfl⟩

end LeanQbe.T.Examples.Kissat.FullM7BvaFactor

