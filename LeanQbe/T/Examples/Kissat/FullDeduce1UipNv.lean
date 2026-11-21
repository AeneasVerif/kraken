module

public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Examples.Kissat.FullOneLitConflLemmas
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` Concrete `Mem 64` UNSAT Non-Vacuity for `full_deduce_1uip` (`Stage 4`)

Provides a concrete `Mem 64` UNSAT non-vacuity witness (`XPost := False`, `0` SAT proofs) for
`full_deduce_1uip` (`Full2.lean:765`, `fullFns[79]?`), parameterized over any proof of the canonical
`FullSpec2.fullDeduce1uipSpec` contract:
- `nvDeduceF0 := cnfOfClauses [[0], [1]]` (`nvDeduceF0_unsat : nvDeduceF0.Unsat`).
- `nvDeduceState`: `cur_level = 1` decision `x0` with falsified binary conflict `(¬x0 ∨ ¬x0)` on
  `nvOneLitCfg` (`hdr = 0x1000#64`, `avail = 1756`, `slack = 0`).
- `nvDeduceMem`: concrete `1756`-byte `Mem 64` heap satisfying `FullMem nvOneLitCfg nvDeduceState`,
  reusing the public `nv_*` separation helpers from `FullOneLitConflLemmas`.
- `nv_full_deduce_1uip_of_wp` & `nv_deduce_1uip_ex_of_wp`: parametric UNSAT non-vacuity
  witnesses ready for one-line instantiation by `FullDeduce1UipLemmas` / Phase 2 assembly.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

/-- Minimal 1-variable UNSAT formula `{(x0), (¬x0)}` for `full_deduce_1uip` non-vacuity. -/
def nvDeduceF0 : CNF Nat := nvOneLitF0

theorem nvDeduceF0_unsat : nvDeduceF0.Unsat := by
  rw [CNF.unsat_iff_not_sat]
  intro α hα
  have h0 : (cnfClause [0]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _
      (CNF.Internal.mem_iff.mpr (by simp [nvDeduceF0, nvOneLitF0, cnfOfClauses]))
  have h1 : (cnfClause [1]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _
      (CNF.Internal.mem_iff.mpr (by simp [nvDeduceF0, nvOneLitF0, cnfOfClauses]))
  rw [CNF.Clause.sat_iff_exists_mem_eq] at h0 h1
  obtain ⟨⟨v0, p0⟩, hm0, he0⟩ := h0; obtain ⟨⟨v1, p1⟩, hm1, he1⟩ := h1
  rw [mem_cnfClause_iff] at hm0 hm1
  simp only [List.mem_singleton] at hm0 hm1
  cases p0 <;> cases p1 <;> simp [litOfLiteral, mkLit] at hm0 hm1
  · have hv0 : v0 = 0 := by omega
    have hv1 : v1 = 0 := by omega
    subst hv0 hv1; dsimp only at he0 he1; rw [he0] at he1; cases he1
  · omega

/-- Concrete level-1 binary-conflict `FullState`: decision `x0` at level 1 (`0 < cur_level`) with
falsified binary conflict `(¬x0 ∨ ¬x0)` entailed by `nvDeduceF0 = {(x0), (¬x0)}`. -/
def nvDeduceState : FullState :=
  { nvOneLitState with
    core := { nvOneLitState.core with cur_level := 1, lvl := [1#32] } }

def nvDeduceBlockHdr : List UInt8 :=
  bytes64 [1#64, 2#64, 0#64, 0#64] ++ bytes64 (hdrTailWords nvOneLitCfg nvDeduceState)

def nvDeduceBlockU32A : List UInt8 :=
  (bytesOf (t := i32) nvDeduceState.core.flags ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvDeduceState.core.lvl ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvDeduceState.core.rsns ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvDeduceState.core.trl ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvDeduceState.core.trail_pos ++ List.replicate 4 0)

/-- Concrete `1756`-byte arena image encoding `nvOneLitCfg` and `nvDeduceState`. -/
def nvDeduceBytes : List UInt8 :=
  nvDeduceBlockHdr ++ nvBlockBytes ++ nvDeduceBlockU32A ++ nvBlockU32B ++
  nvBlockU32C ++ nvBlockWvec ++ nvBlockTail

/-- Concrete `Mem 64` heap mapped at `nvOneLitCfg.hdr` (`0x1000#64`). -/
def nvDeduceMem : Mem 64 := nvDeduceBytes.At nvOneLitCfg.hdr

theorem nvDeduceMem_ok : FullMem nvOneLitCfg nvDeduceState nvDeduceMem := by
  let c := nvOneLitCfg; let s := nvDeduceState
  have hvb : valsBytes c.max_vars - 2 * c.max_vars = 6 := by decide
  have hmb : markBytes c.max_vars - c.max_vars = 7 := by decide
  have hu4 : u32FullBytes c.max_vars - 4 * c.max_vars = 4 := by decide
  have hu8 : u32FullBytes c.max_vars - 4 * (c.max_vars + 1) = 0 := by decide
  have hmv1 : BitVec.ofNat 64 c.max_vars = 1#64 := rfl
  have hmv2 : BitVec.ofNat 64 (2 * c.max_vars) = 2#64 := rfl
  have hmv4 : BitVec.ofNat 64 (4 * c.max_vars) = 4#64 := rfl
  have hmv8 : BitVec.ofNat 64 (4 * (c.max_vars + 1)) = 8#64 := rfl
  have hHdr : nvDeduceBlockHdr.length = 1152 ∧
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
        s.core.d_cur s.core.d_val ⋆ array64 (c.hdr + 32) (hdrTailWords c s))
        (nvDeduceBlockHdr.At c.hdr) :=
    nv_join_pair
      (nv_arr64_p (a := c.hdr) (xs := [1#64, 2#64, 0#64, 0#64]) 32 rfl (by decide))
      (nv_arr64_p (a := c.hdr + 32) (xs := hdrTailWords c s) 1120
        (by rw [hdrTailWords_length]) (by decide))
      (by decide) (by decide)
  have hBytes : nvBlockBytes.length = 64 ∧
      (FullCoreByteArrs c s.core ⋆ FullScrByteArrs c s.scratch ⋆ c.padBytes)
        (nvBlockBytes.At c.pVals) := by
    have h1 := nv_arr_pad_p (t := i8) (a := c.pVals) (xs := s.core.vals) 2 6 rfl (by decide)
    have h2 := nv_arr_pad_p (t := i8) (a := c.pWalkVals) (xs := s.scratch.walk_vals) 2 6 rfl
      (by decide)
    have h3 := nv_arr_pad_p (t := i8) (a := c.pLitMark) (xs := s.core.lit_mark) 2 6 rfl
      (by decide)
    have h4 := nv_arr_pad_p (t := i8) (a := c.pMark) (xs := s.core.mrk) 1 7 rfl (by decide)
    have h5 := nv_arr_pad_p (t := i8) (a := c.pPhases) (xs := s.scratch.phases) 1 7 rfl
      (by decide)
    have h6 := nv_arr_pad_p (t := i8) (a := c.pPhasesTarget) (xs := s.scratch.phases_target) 1 7
      rfl (by decide)
    have h7 := nv_arr_pad_p (t := i8) (a := c.pPhasesBest) (xs := s.scratch.phases_best) 1 7 rfl
      (by decide)
    have h8 := nv_arr_pad_p (t := i8) (a := c.pWalkBest) (xs := s.scratch.walk_best) 1 7 rfl
      (by decide)
    let pB1 : Mem 64 → Prop :=
      region (c.pVals + 2#64) 6 ⋆ region (c.pWalkVals + 2#64) 6 ⋆
      region (c.pLitMark + 2#64) 6 ⋆ region (c.pMark + 1#64) 7
    have h12 := nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := nv_sep_reorg (nv_join_pair h123 h4 (by decide) (by decide))
      (Q := (FullCoreByteArrs c s.core ⋆ array (t := i8) c.pWalkVals s.scratch.walk_vals) ⋆ pB1)
      fun _ hm => nv_zip4 hm
    have h12345 := nv_join_pair h1234 h5 (by decide) (by decide)
    have h123456 := nv_join_pair h12345 h6 (by decide) (by decide)
    have h1234567 := nv_join_pair h123456 h7 (by decide) (by decide)
    have hall := nv_join_pair h1234567 h8 (by decide) (by decide)
    exact nv_sep_reorg hall fun _ hm => by
      have hfin := nv_zip4_tail hm
      unfold FullScrByteArrs FullCfg.padBytes
      rw [hvb, hmb, hmv2, hmv1]
      simpa only [pB1, sep_assoc] using hfin
  have hU32A : nvDeduceBlockU32A.length = 40 ∧
      ((array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
        array (t := i32) c.pReason s.core.rsns ⋆ array (t := i32) c.pTrail s.core.trl ⋆
        array (t := i32) c.pTrailPos s.core.trail_pos) ⋆ c.padU32A)
        (nvDeduceBlockU32A.At c.pFlags) := by
    have h1 := nv_arr_pad_p (t := i32) (a := c.pFlags) (xs := s.core.flags) 4 4 rfl (by decide)
    have h2 := nv_arr_pad_p (t := i32) (a := c.pLevel) (xs := s.core.lvl) 4 4 rfl (by decide)
    have h3 := nv_arr_pad_p (t := i32) (a := c.pReason) (xs := s.core.rsns) 4 4 rfl (by decide)
    have h4 := nv_arr_pad_p (t := i32) (a := c.pTrail) (xs := s.core.trl) 4 4 rfl (by decide)
    have h5 := nv_arr_pad_p (t := i32) (a := c.pTrailPos) (xs := s.core.trail_pos) 4 4 rfl
      (by decide)
    have h12 := nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := nv_join_pair h123 h4 (by decide) (by decide)
    exact nv_sep_reorg (nv_join_pair h1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32A; rw [hu4, hmv4]; exact sep_ac hm
  have hU32B : nvBlockU32B.length = 40 ∧
      ((array (t := i32) c.pTmp s.core.tmp ⋆ array (t := i32) c.pMinClr s.core.min_clr) ⋆
        (array (t := i32) c.pHeap s.scratch.heap ⋆ array (t := i32) c.pPos s.scratch.pos ⋆
         array (t := i32) c.pShrinkStk s.scratch.shrink_stk) ⋆ c.padU32B)
        (nvBlockU32B.At c.pTmp) := by
    have h1 := nv_arr_pad_p (t := i32) (a := c.pTmp) (xs := s.core.tmp) 4 4 rfl (by decide)
    have h2 := nv_arr_pad_p (t := i32) (a := c.pHeap) (xs := s.scratch.heap) 4 4 rfl (by decide)
    have h3 := nv_arr_pad_p (t := i32) (a := c.pPos) (xs := s.scratch.pos) 4 4 rfl (by decide)
    have h4 := nv_arr_pad_p (t := i32) (a := c.pMinClr) (xs := s.core.min_clr) 4 4 rfl (by decide)
    have h5 := nv_arr_pad_p (t := i32) (a := c.pShrinkStk) (xs := s.scratch.shrink_stk) 4 4 rfl
      (by decide)
    have h12 := nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := nv_join_pair h123 h4 (by decide) (by decide)
    exact nv_sep_reorg (nv_join_pair h1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32B; rw [hu4, hmv4]; exact sep_ac hm
  have hU32C : nvBlockU32C.length = 40 ∧
      ((array (t := i32) c.pQPrev s.scratch.q_prev ⋆
        array (t := i32) c.pQNext s.scratch.q_next ⋆
        array (t := i32) c.pQStamp s.scratch.q_stamp) ⋆
        (array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
         array (t := i32) c.pFrameDec s.core.frame_dec) ⋆ c.padU32C)
        (nvBlockU32C.At c.pQPrev) := by
    have h1 := nv_arr_pad_p (t := i32) (a := c.pQPrev) (xs := s.scratch.q_prev) 4 4 rfl
      (by decide)
    have h2 := nv_arr_pad_p (t := i32) (a := c.pQNext) (xs := s.scratch.q_next) 4 4 rfl
      (by decide)
    have h3 := nv_arr_pad_p (t := i32) (a := c.pQStamp) (xs := s.scratch.q_stamp) 4 4 rfl
      (by decide)
    have h4 := nv_arr_pad_p (t := i32) (a := c.pFrameTrail) (xs := s.core.frame_trail) 8 0 rfl
      (by decide)
    have h5 := nv_arr_pad_p (t := i32) (a := c.pFrameDec) (xs := s.core.frame_dec) 8 0 rfl
      (by decide)
    have h12 := nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := nv_join_pair h123 h4 (by decide) (by decide)
    exact nv_sep_reorg (nv_join_pair h1234 h5 (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32C; rw [hu4, hu8, hmv4, hmv8]; exact sep_ac hm
  have hWvec : nvBlockWvec.length = 80 ∧
      ((array (t := i32) c.pWvec s.core.wvec ⋆ array (t := i32) c.pRepr s.core.repr) ⋆
        FullScrWksArrs c s.scratch ⋆
        (array64 c.pScore s.scratch.score ⋆ array64 c.pSimSig s.scratch.sim_sig))
        (nvBlockWvec.At c.pWvec) := by
    have h1 := nv_arr_p (t := i32) (a := c.pWvec) (xs := s.core.wvec) 16 rfl (by decide)
    have h2 := nv_arr_p (t := i32) (a := c.pRepr) (xs := s.core.repr) 8 rfl (by decide)
    have h3 := nv_arr_p (t := i32) (a := c.pWsort) (xs := s.scratch.wsort) 8 rfl (by decide)
    have h4 := nv_arr_p (t := i32) (a := c.pWorkStk1) (xs := s.scratch.work_stk1) 8 rfl
      (by decide)
    have h5 := nv_arr_p (t := i32) (a := c.pWorkStk2) (xs := s.scratch.work_stk2) 8 rfl
      (by decide)
    have h6 := nv_arr_p (t := i32) (a := c.pTarjanMark) (xs := s.scratch.tarjan_mark) 8 rfl
      (by decide)
    have h7 := nv_arr_p (t := i32) (a := c.pTarjanReach) (xs := s.scratch.tarjan_reach) 8 rfl
      (by decide)
    have h8 := nv_arr64_p (a := c.pScore) (xs := s.scratch.score) 8 rfl (by decide)
    have h9 := nv_arr64_p (a := c.pSimSig) (xs := s.scratch.sim_sig) 8 rfl (by decide)
    have h12 := nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := nv_join_pair h123 h4 (by decide) (by decide)
    have h12345 := nv_join_pair h1234 h5 (by decide) (by decide)
    have h123456 := nv_join_pair h12345 h6 (by decide) (by decide)
    have h1234567 := nv_join_pair h123456 h7 (by decide) (by decide)
    have h12345678 := nv_join_pair h1234567 h8 (by decide) (by decide)
    exact nv_sep_reorg (nv_join_pair h12345678 h9 (by decide) (by decide)) fun _ hm => by
      unfold FullScrWksArrs; exact sep_ac hm
  have hTail : nvBlockTail.length = 340 ∧
      (array (t := i32) c.pMinStk s.core.min_stk ⋆
        (array (t := i32) c.pGlueUsed s.scratch.glue_used ⋆
         array (t := i32) c.pLastLearned s.scratch.last_learned) ⋆
        FullCoreDynArrs c s.core ⋆ FullScrDynArrs c s.scratch ⋆ region c.pSlack c.slack)
        (nvBlockTail.At c.pMinStk) := by
    have h1 := nv_arr_p (t := i32) (a := c.pMinStk) (xs := s.core.min_stk) 16 rfl (by decide)
    have h2 := nv_arr_p (t := i32) (a := c.pGlueUsed) (xs := s.scratch.glue_used) 256 rfl
      (by decide)
    have h3 := nv_arr_p (t := i32) (a := c.pLastLearned) (xs := s.scratch.last_learned) 64 rfl
      (by decide)
    have h4 := nv_arr_p (t := i32) (a := c.pArena) (xs := s.core.arena) 0 rfl (by decide)
    have h5 := nv_arr_p (t := i32) (a := c.pWstk) (xs := s.core.wstk) 4 rfl (by decide)
    have h6 := nv_arr_p (t := i32) (a := c.pDelayed) (xs := s.scratch.delayed) 0 rfl (by decide)
    have h7 := nv_arr_p (t := i32) (a := c.pRedRefs) (xs := s.scratch.red_refs) 0 rfl (by decide)
    have h8 := nv_arr_p (t := i32) (a := c.pExtendStk) (xs := s.scratch.extend_stk) 0 rfl
      (by decide)
    have h9 := nv_arr_p (t := i32) (a := c.pScratchBuf) (xs := s.scratch.scratch_buf) 0 rfl
      (by decide)
    have h10 : (List.replicate 0 (0 : UInt8)).length = 0 ∧
        region c.pSlack c.slack ((List.replicate 0 0).At c.pSlack) :=
      ⟨rfl, ⟨List.replicate 0 0, by decide, rfl⟩⟩
    have h12 := nv_join_pair h1 h2 (by decide) (by decide)
    have h123 := nv_join_pair h12 h3 (by decide) (by decide)
    have h1234 := nv_join_pair h123 h4 (by decide) (by decide)
    have h12345 := nv_join_pair h1234 h5 (by decide) (by decide)
    have h123456 := nv_join_pair h12345 h6 (by decide) (by decide)
    have h1234567 := nv_join_pair h123456 h7 (by decide) (by decide)
    have h12345678 := nv_join_pair h1234567 h8 (by decide) (by decide)
    have h123456789 := nv_join_pair h12345678 h9 (by decide) (by decide)
    exact nv_sep_reorg (nv_join_pair h123456789 h10 (by decide) (by decide)) fun _ hm => by
      unfold FullCoreDynArrs FullScrDynArrs; exact sep_ac hm
  have h01 := nv_join_pair hHdr hBytes (by decide) (by decide)
  have h02 := nv_join_pair h01 hU32A (by decide) (by decide)
  have h03 := nv_join_pair h02 hU32B (by decide) (by decide)
  have h04 := nv_join_pair h03 hU32C (by decide) (by decide)
  have h05 := nv_join_pair h04 hWvec (by decide) (by decide)
  exact (nv_sep_reorg (nv_join_pair h05 hTail (by decide) (by decide)) fun _ hm => by
    unfold FullMem FullCoreArrays FullCoreU32A FullCoreU32B FullScratchArrays FullScrU32A
      FullScrMetaArrs FullCfg.pad
    exact sep_ac hm).2

theorem nvDeduce_lengths : nvDeduceState.LengthsOk nvOneLitCfg :=
  ⟨{ nvOneLit_lengths.core_ok with lvl_len := rfl }, nvOneLit_lengths.scratch_ok⟩

private theorem nvDeduce_entails_11 :
    (cnfOfClauses [[0], [1]]).EntailsClause (cnfClause [1, 1]) := by
  rw [CNF.entails_clause_def]; intro α hα
  have h1 : (cnfClause [1]).Sat α :=
    (CNF.sat_iff_all_mem_sat.mp hα) _ (CNF.Internal.mem_iff.mpr (by simp [cnfOfClauses]))
  rw [CNF.Clause.sat_iff_exists_mem_eq] at h1 ⊢
  obtain ⟨lit, hm, heq⟩ := h1
  refine ⟨lit, ?_, heq⟩
  rw [mem_cnfClause_iff] at hm ⊢; simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
  exact Or.inl hm

theorem nvDeduce_witness :
    FullWitnessInv nvOneLitCfg nvDeduceF0 [[0], [1]] nvDeduceState.core := by
  have hrefs : fullArenaClauseRefsCore nvDeduceState.core = [] := rfl
  have hcv : nvDeduceState.core.cur_vars = 1 := rfl
  have hte : nvDeduceState.core.trail_end = 1 := rfl
  have hcl : nvDeduceState.core.cur_level = 1 := rfl
  have hdm : nvDeduceState.core.dense_mode = 0#64 := rfl
  have hwat : ModeWatchesInv [[0], [1]] nvDeduceState.core := by
    unfold ModeWatchesInv; rw [ite_eq_left hdm]
    refine WatchesInv.of_slices (fun l hl => ?_) (fun l hl hp => ?_) (fun l1 _ h1 _ _ hp => ?_)
      (fun l hl => ?_)
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> decide
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
        (simp [fullWatchSizeCore, nvDeduceState, nvOneLitState] at hp)
    · rw [hcv] at h1; rcases (by omega : l1 = 0 ∨ l1 = 1) with rfl | rfl <;>
        (simp [fullWatchSizeCore, nvDeduceState, nvOneLitState] at hp)
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
        exact WatchSliceOk.empty
  exact
    { ext_sound := ⟨(varsBoundedBool_iff 1 [[0], [1]]).mp rfl, id⟩
      inconsistent_sound := fun h => absurd rfl h
      arena := ⟨Or.inl rfl, fun r hr => by simp [hrefs] at hr, fun r hr => by simp [hrefs] at hr,
        fun r hr => by simp [hrefs] at hr, fun r hr => by simp [hrefs] at hr⟩
      watches := hwat
      cur_level_le := Nat.le_refl 1
      trail_lits_lt := fun i hi => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); decide
      trail_vars_nodup := fun i j hi hj _ => by rw [hte] at hi hj; omega
      vals_domain := fun l hl => by
        rw [hcv] at hl
        rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> simp [nvDeduceState, nvOneLitState]
      vals_true_iff := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · exact ⟨fun _ => ⟨0, Nat.zero_lt_one, rfl⟩, fun _ => rfl⟩
        · constructor
          · intro h; cases h
          · rintro ⟨i, hi, h⟩; rw [hte] at hi; obtain rfl : i = 0 := (by omega); cases h
      vals_false_iff := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · constructor
          · intro h; cases h
          · rintro ⟨i, hi, h⟩; rw [hte] at hi; obtain rfl : i = 0 := (by omega); cases h
        · exact ⟨fun _ => ⟨0, Nat.zero_lt_one, rfl⟩, fun _ => rfl⟩
      lvl_le := fun i hi => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact Nat.le_refl 1
      dec_earliest := fun i j hi hj _ _ => by rw [hte] at hi hj; omega
      levels_inhabited := fun L h1 h2 => by
        rw [hcl] at h2; obtain rfl : L = 1 := (by omega); exact ⟨0, Nat.zero_lt_one, rfl⟩
      level0_sound := fun i hi h0 => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); cases h0
      trail_pos_inv := fun i hi => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); rfl
      level0_rsn_none := fun i hi _ => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); rfl
      frame_trail_lt := fun L hL => by
        rw [hcl] at hL; rcases (by omega : L = 0 ∨ L = 1) with rfl | rfl <;> decide
      frame_trail_mono := fun L1 L2 _ hL2 => by
        rw [hcl] at hL2
        rcases (by omega : L1 = 0 ∨ L1 = 1) with rfl | rfl <;>
          rcases (by omega : L2 = 0 ∨ L2 = 1) with rfl | rfl <;> exact Nat.le_refl 0
      frame_trail_before_lt := fun L h1 h2 i hi => by
        rw [hcl] at h2; obtain rfl : L = 1 := (by omega)
        have : (nvDeduceState.core.frame_trail[1]?.getD 0#32).toNat = 0 := rfl
        rw [this] at hi; omega
      frame_dec_lt := fun L h1 h2 => by
        rw [hcl] at h2; obtain rfl : L = 1 := (by omega); decide
      reason_inv := fun i hi hne => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact absurd rfl hne
      reason_lit_mem := fun i hi hne => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact absurd rfl hne }

theorem nvDeduce_cutInv : FullCutInvW nvOneLitCfg nvDeduceF0 [[0], [1]] 1 nvDeduceState := by
  have hmv : nvOneLitCfg.max_vars = 1 := rfl
  have hmarks : FullLitMarksClear nvOneLitCfg nvDeduceState := by
    refine ⟨fun v hv => ?_, fun l hl => ?_⟩
    · rw [hmv] at hv; obtain rfl : v = 0 := (by omega); rfl
    · rw [hmv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl
  have hnd : FullArenaVarsNodup nvDeduceState := fun r hr => by
    have : fullArenaClauseRefs nvDeduceState = [] := rfl
    simp [this] at hr
  have hext : FullExtScratchOk nvOneLitCfg nvDeduceState :=
    ⟨FullLastLearnedWf.of_cleared fun i hi => by
      simp only [nvDeduceState, nvOneLitState, nvOneLitScratch, List.getElem?_replicate,
        show i < 16 by omega, ↓reduceIte, Option.getD_some], Nat.le_refl 0⟩
  exact ⟨nvDeduce_lengths, nvDeduce_witness.toCut, hmarks, hnd, hext, rfl⟩

theorem nvDeduce_conflCut : FullConflictOkCut [[0], [1]] 1 nvDeduceState :=
  FullConflictOkW.toCut nvDeduce_witness
    (Or.inl ⟨rfl, by decide, by decide, rfl, rfl, nvDeduce_entails_11⟩)

/-- Parametric concrete `Mem 64` UNSAT non-vacuity for `full_deduce_1uip` (`fullFns[79]?`) under
`fullEnv` with `XPost := False`, instantiated from any proof of canonical `fullDeduce1uipSpec`. -/
theorem nv_full_deduce_1uip_of_wp
    (hwp : ∀ args m Q X, fullDeduce1uipSpec args m Q X →
      Func.wp fullEnv full_deduce_1uip.body args m Q X) :
    Func.wp fullEnv full_deduce_1uip.body (nvOneLitCfg.hdr, ()) nvDeduceMem
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) ∧ nvDeduceF0.Unsat ∧
        ∃ s' : FullState, s'.LengthsOk nvOneLitCfg ∧ FullMem nvOneLitCfg s' m' ∧
          FullOtfsInvW nvOneLitCfg nvDeduceF0 [[0], [1]] s' ∧
          (r = 1#64 → s'.core.cur_level = 1 ∧ 1 ≤ s'.core.tmp_len ∧
            (cnfOfClauses [[0], [1]]).EntailsClause
              (cnfClause ((s'.core.tmp.take s'.core.tmp_len).map BitVec.toNat))) ∧
          (r = 2#64 → ∃ cut' ≤ s'.core.trail_end,
            FullCutInvW nvOneLitCfg nvDeduceF0 [[0], [1]] cut' s' ∧
            FullConflictOkCut [[0], [1]] cut' s'))
      (fun _ _ _ _ => False) := by
  refine hwp (nvOneLitCfg.hdr, ()) nvDeduceMem _ (fun _ _ _ _ => False)
    ⟨nvOneLitCfg, nvDeduceF0, [[0], [1]], 1, nvDeduceState, emp, rfl, nvDeduce_cutInv,
      Nat.zero_lt_one, nvDeduce_conflCut, by rw [sep_emp]; exact nvDeduceMem_ok, ?_⟩
  intro r s' m' hlen hr _ _ _ h20 h0 h1 h2 hm'
  rw [sep_emp] at hm'
  have hotfs : FullOtfsInvW nvOneLitCfg nvDeduceF0 [[0], [1]] s' := by
    rcases hr with rfl | rfl | rfl | rfl
    · exact h0 rfl
    · exact (h1 rfl).1
    · obtain ⟨_, _, hcut', _, _⟩ := h2 rfl; exact hcut'.toOtfs
    · exact (h20 rfl).2.1
  exact ⟨hr, nvDeduceF0_unsat, s', hlen, hm', hotfs,
    fun h1r => let ⟨_, hcl', htl1, _, _, _, _, _, hent⟩ := h1 h1r; ⟨hcl', htl1, hent⟩,
    fun h2r => let ⟨cut', hle', hcut', _, hcf'⟩ := h2 h2r; ⟨cut', hle', hcut', hcf'⟩⟩

/-- Existential concrete `Mem 64` non-vacuity wrapper at `0x1000#64` (`XPost := False`). -/
theorem nv_deduce_1uip_ex_of_wp
    (hwp : ∀ args m Q X, fullDeduce1uipSpec args m Q X →
      Func.wp fullEnv full_deduce_1uip.body args m Q X) :
    ∃ m₀ : Mem 64,
      Func.wp fullEnv full_deduce_1uip.body (0x1000#64, ()) m₀
        (fun (r, ()) m' =>
          (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) ∧ nvDeduceF0.Unsat ∧
          ∃ s' : FullState, s'.LengthsOk nvOneLitCfg ∧ FullMem nvOneLitCfg s' m' ∧
            FullOtfsInvW nvOneLitCfg nvDeduceF0 [[0], [1]] s' ∧
            (r = 1#64 → s'.core.cur_level = 1 ∧ 1 ≤ s'.core.tmp_len ∧
              (cnfOfClauses [[0], [1]]).EntailsClause
                (cnfClause ((s'.core.tmp.take s'.core.tmp_len).map BitVec.toNat))) ∧
            (r = 2#64 → ∃ cut' ≤ s'.core.trail_end,
              FullCutInvW nvOneLitCfg nvDeduceF0 [[0], [1]] cut' s' ∧
              FullConflictOkCut [[0], [1]] cut' s'))
        (fun _ _ _ _ => False) :=
  ⟨nvDeduceMem, nv_full_deduce_1uip_of_wp hwp⟩

end LeanQbe.T.Examples.Kissat.Full
