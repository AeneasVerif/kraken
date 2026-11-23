module

public import LeanQbe.T.Examples.Kissat.FullM7MemShrink
public import LeanQbe.T.Examples.Kissat.FullParseInitLemmas1
import LeanQbe.T.AbiLemmas
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.Bytes
import LeanQbe.T.Logic.Cells
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.MemLemmas
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Memory-Shrink Prototype A Proofs — Part 1 (`FullM7MemShrinkProof0`)

M1-clean verification (`public section`, zero `@[expose]`, zero `import all`) covering:
1. **Sizing & Geometry (`90 B/var` resident fixed + `58 B/var` transient pool)**:
   `m7FixedBytes`, `m7TransBytes`, `m7BvaCap`, `m7CalcMaxV`, `m7CalcExtCap`, `m7CalcScrCap`,
   `MemShrinkCfg`, `m7HdrTailWords`, `MemShrinkLengthsOk`, `MemShrinkResArrays`,
   `MemShrinkTransRegions`, `MemShrinkMem`, `MemShrinkSparseInv`, and mutually exclusive
   transient phase-view equivalences (`m7Trans_to_walk`, `m7Trans_to_cong`,
   `m7TransWalk_to_regions`, `m7TransCong_to_regions`).
2. **`array64` <-> Byte/`u32` Constant-Fill Bridges & Public `Spec` Definitions** for all `12` fns.
3. **Pure Sizing, 4x-Unrolled `u64` Fill & Header Init WP Proofs**:
   `full_fill_u64_m7_wp`, `full_fixed_bytes_m7_wp`, `full_trans_bytes_m7_wp`,
   `full_calc_max_v_m7_wp`, `full_calc_ext_cap_m7_wp`, `full_calc_scr_cap_m7_wp`,
   `full_init_ptrs_m7_wp`, `full_init_hdr_m7_wp`, `full_init_arenas_m7_wp`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7MemShrink

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open FullParseInitSpecs FullParseInitHelpers
open scoped FullArenaTactics FullParseInitTactics
open Kraken.Bedrock2.Test

/-! ## 1. Sizing Functions & `MemShrinkCfg` Geometry (`151 -> 90 B/var` Resident) -/

/-- Resident fixed byte footprint (`1472 + 90 B/var + 8 * minDepth`). -/
def m7FixedBytes (max_v : Nat) : Nat :=
  1472 + valsBytes max_v + 4 * markBytes max_v + 15 * u32FullBytes max_v +
    24 * max_v + 8 * fullMinDepthOf max_v

/-- Transient scratch pool byte footprint (`56 * max_v + valsBytes max_v = 58 B/var`). -/
def m7TransBytes (max_v : Nat) : Nat :=
  56 * max_v + valsBytes max_v

/-- Exact `extend_stk` capacity policy matching `full_calc_ext_cap_m7`. -/
def m7CalcExtCap (rem : Nat) : Nat :=
  if rem < 8192 then 0 else ((min (rem / 32) 4194304) / 2) * 2

/-- Exact `scratch_buf` capacity policy matching `full_calc_scr_cap_m7`. -/
def m7CalcScrCap (rem : Nat) : Nat :=
  if rem < 8192 then 0
  else
    let raw := if 16384 ≤ rem then rem / 16 else rem / 32
    ((min raw 1048576) / 2) * 2

/-- BVA headroom computed by `full_calc_max_v_m7`. -/
def m7BvaCap (avail mv nc f0 : Nat) : Nat :=
  if 2 ≤ mv ∧ nc * 48 + 8192 < avail - f0 then
    min (min (mv / 2 + 16) 4096) (((avail - f0) - nc * 48 - 4096) / 2688)
  else 0

/-- Variable limit selected by `full_calc_max_v_m7`. -/
def m7CalcMaxV (avail mv nc f0 : Nat) : Nat :=
  let cand := mv + m7BvaCap avail mv nc f0
  let need := m7FixedBytes cand + m7TransBytes cand
  if avail < need ∨ avail - need < nc * 40 + 136 then mv else cand

theorem m7FixedBytes_lt {max_v : Nat} (hmax : max_v < 2 * dimacsBound) :
    m7FixedBytes max_v < 2 ^ 38 := by
  unfold m7FixedBytes valsBytes markBytes u32FullBytes fullMinDepthOf dimacsBound at *
  split <;> omega

theorem m7TransBytes_lt {max_v : Nat} (hmax : max_v < 2 * dimacsBound) :
    m7TransBytes max_v < 2 ^ 38 := by unfold m7TransBytes valsBytes dimacsBound at *; omega

theorem m7Fixed_plus_trans_le (max_v : Nat) :
    m7FixedBytes max_v + m7TransBytes max_v ≤ fullFixedBytes max_v := by
  unfold m7FixedBytes m7TransBytes fullFixedBytes valsBytes markBytes u32FullBytes fullMinDepthOf
  split <;> omega

theorem m7BvaCap_le (avail mv nc f0 : Nat) : m7BvaCap avail mv nc f0 ≤ 4096 := by
  unfold m7BvaCap; split <;> omega

theorem m7CalcMaxV_ge {avail mv nc f0 : Nat} : mv ≤ m7CalcMaxV avail mv nc f0 := by
  unfold m7CalcMaxV; dsimp only
  by_cases h : avail < m7FixedBytes (mv + m7BvaCap avail mv nc f0) +
      m7TransBytes (mv + m7BvaCap avail mv nc f0) ∨
      avail - (m7FixedBytes (mv + m7BvaCap avail mv nc f0) +
        m7TransBytes (mv + m7BvaCap avail mv nc f0)) < nc * 40 + 136
  · simp [h]
  · simp only [h, ↓reduceIte]; omega

theorem m7CalcMaxV_lt {avail mv nc f0 : Nat} (hmv : mv < dimacsBound) :
    m7CalcMaxV avail mv nc f0 < 2 * dimacsBound := by
  have hb := m7BvaCap_le avail mv nc f0
  unfold m7CalcMaxV dimacsBound at *; dsimp only
  by_cases h : avail < m7FixedBytes (mv + m7BvaCap avail mv nc f0) +
      m7TransBytes (mv + m7BvaCap avail mv nc f0) ∨
      avail - (m7FixedBytes (mv + m7BvaCap avail mv nc f0) +
        m7TransBytes (mv + m7BvaCap avail mv nc f0)) < nc * 40 + 136
  · simp only [h, ↓reduceIte]; omega
  · simp only [h, ↓reduceIte]; omega

theorem m7CalcMaxV_fits {avail mv nc f0 : Nat}
    (hbase : m7FixedBytes mv + m7TransBytes mv + nc * 40 + 136 ≤ avail) :
    m7FixedBytes (m7CalcMaxV avail mv nc f0) +
      m7TransBytes (m7CalcMaxV avail mv nc f0) + nc * 40 + 136 ≤ avail := by
  unfold m7CalcMaxV; dsimp only
  by_cases h : avail < m7FixedBytes (mv + m7BvaCap avail mv nc f0) +
      m7TransBytes (mv + m7BvaCap avail mv nc f0) ∨
      avail - (m7FixedBytes (mv + m7BvaCap avail mv nc f0) +
        m7TransBytes (mv + m7BvaCap avail mv nc f0)) < nc * 40 + 136
  · simp only [h, ↓reduceIte]; exact hbase
  · simp only [h, ↓reduceIte]; omega

theorem m7CalcExtCap_le (rem : Nat) : m7CalcExtCap rem ≤ 4194304 := by
  unfold m7CalcExtCap; split <;> omega

theorem m7CalcExtCap_lt (rem : Nat) : m7CalcExtCap rem < dimacsBound := by
  have := m7CalcExtCap_le rem; unfold dimacsBound; omega

theorem m7CalcExtCap_4le (rem : Nat) : 4 * m7CalcExtCap rem ≤ rem / 8 := by
  unfold m7CalcExtCap; split <;> omega

theorem m7CalcScrCap_le (rem : Nat) : m7CalcScrCap rem ≤ 1048576 := by
  unfold m7CalcScrCap; split; omega; dsimp only; split <;> omega

theorem m7CalcScrCap_lt (rem : Nat) : m7CalcScrCap rem < dimacsBound := by
  have := m7CalcScrCap_le rem; unfold dimacsBound; omega

theorem m7CalcScrCap_4le (rem : Nat) : 4 * m7CalcScrCap rem ≤ rem / 4 := by
  unfold m7CalcScrCap; split; omega; dsimp only; split <;> omega

/-- Physical memory configuration established by `full_init_state_m7`. -/
structure MemShrinkCfg where
  hdr : BitVec 64
  avail : Nat
  mv : Nat
  max_vars : Nat
  bva_cap : Nat
  nc : Nat
  arena_cap : Nat
  wcap : Nat
  delayed_cap : Nat
  red_cap : Nat
  extend_cap : Nat
  scratch_cap : Nat
  hbva : max_vars = mv + bva_cap
  hmv : mv < dimacsBound
  hmaxv : max_vars < 2 * dimacsBound
  hnc : nc < dimacsBound
  harena : arena_cap < 2 * dimacsBound
  hwcap : wcap < 2 * dimacsBound
  hdel : delayed_cap < dimacsBound
  hred : red_cap < 2 * dimacsBound
  hext : extend_cap < dimacsBound
  hscr : scratch_cap < dimacsBound
  havail_fit : hdr.toNat + avail < 2 ^ 64
  hsize : m7FixedBytes max_vars + m7TransBytes max_vars + 4 * arena_cap + 4 * wcap +
    12 * delayed_cap + 4 * red_cap + 4 * extend_cap + 4 * scratch_cap ≤ avail

namespace MemShrinkCfg

def minDepth (c : MemShrinkCfg) : Nat := fullMinDepthOf c.max_vars

def pVals (c : MemShrinkCfg) : BitVec 64 := c.hdr + BitVec.ofNat 64 1152
def pMark (c : MemShrinkCfg) : BitVec 64 := c.pVals + BitVec.ofNat 64 (valsBytes c.max_vars)
def pPhases (c : MemShrinkCfg) : BitVec 64 := c.pMark + BitVec.ofNat 64 (markBytes c.max_vars)
def pPhasesTarget (c : MemShrinkCfg) : BitVec 64 :=
  c.pPhases + BitVec.ofNat 64 (markBytes c.max_vars)
def pPhasesBest (c : MemShrinkCfg) : BitVec 64 :=
  c.pPhasesTarget + BitVec.ofNat 64 (markBytes c.max_vars)
def pFlags (c : MemShrinkCfg) : BitVec 64 :=
  c.pPhasesBest + BitVec.ofNat 64 (markBytes c.max_vars)
def pLevel (c : MemShrinkCfg) : BitVec 64 := c.pFlags + BitVec.ofNat 64 (u32FullBytes c.max_vars)
def pReason (c : MemShrinkCfg) : BitVec 64 :=
  c.pLevel + BitVec.ofNat 64 (u32FullBytes c.max_vars)
def pTrail (c : MemShrinkCfg) : BitVec 64 :=
  c.pReason + BitVec.ofNat 64 (u32FullBytes c.max_vars)
def pTrailPos (c : MemShrinkCfg) : BitVec 64 :=
  c.pTrail + BitVec.ofNat 64 (u32FullBytes c.max_vars)
def pTmp (c : MemShrinkCfg) : BitVec 64 :=
  c.pTrailPos + BitVec.ofNat 64 (u32FullBytes c.max_vars)
def pHeap (c : MemShrinkCfg) : BitVec 64 := c.pTmp + BitVec.ofNat 64 (u32FullBytes c.max_vars)
def pPos (c : MemShrinkCfg) : BitVec 64 := c.pHeap + BitVec.ofNat 64 (u32FullBytes c.max_vars)
def pMinClr (c : MemShrinkCfg) : BitVec 64 := c.pPos + BitVec.ofNat 64 (u32FullBytes c.max_vars)
def pShrinkStk (c : MemShrinkCfg) : BitVec 64 :=
  c.pMinClr + BitVec.ofNat 64 (u32FullBytes c.max_vars)
def pQPrev (c : MemShrinkCfg) : BitVec 64 :=
  c.pShrinkStk + BitVec.ofNat 64 (u32FullBytes c.max_vars)
def pQNext (c : MemShrinkCfg) : BitVec 64 := c.pQPrev + BitVec.ofNat 64 (u32FullBytes c.max_vars)
def pQStamp (c : MemShrinkCfg) : BitVec 64 := c.pQNext + BitVec.ofNat 64 (u32FullBytes c.max_vars)
def pFrameTrail (c : MemShrinkCfg) : BitVec 64 :=
  c.pQStamp + BitVec.ofNat 64 (u32FullBytes c.max_vars)
def pFrameDec (c : MemShrinkCfg) : BitVec 64 :=
  c.pFrameTrail + BitVec.ofNat 64 (u32FullBytes c.max_vars)
def pWvec (c : MemShrinkCfg) : BitVec 64 :=
  c.pFrameDec + BitVec.ofNat 64 (u32FullBytes c.max_vars)
def pScore (c : MemShrinkCfg) : BitVec 64 := c.pWvec + BitVec.ofNat 64 (16 * c.max_vars)
def pMinStk (c : MemShrinkCfg) : BitVec 64 := c.pScore + BitVec.ofNat 64 (8 * c.max_vars)
def pGlueUsed (c : MemShrinkCfg) : BitVec 64 := c.pMinStk + BitVec.ofNat 64 (8 * c.minDepth)
def pLastLearned (c : MemShrinkCfg) : BitVec 64 := c.pGlueUsed + BitVec.ofNat 64 256
def pArena (c : MemShrinkCfg) : BitVec 64 := c.pLastLearned + BitVec.ofNat 64 64
def pWstk (c : MemShrinkCfg) : BitVec 64 := c.pArena + BitVec.ofNat 64 (4 * c.arena_cap)
def pDelayed (c : MemShrinkCfg) : BitVec 64 := c.pWstk + BitVec.ofNat 64 (4 * c.wcap)
def pRedRefs (c : MemShrinkCfg) : BitVec 64 :=
  c.pDelayed + BitVec.ofNat 64 (12 * c.delayed_cap)
def pExtendStk (c : MemShrinkCfg) : BitVec 64 := c.pRedRefs + BitVec.ofNat 64 (4 * c.red_cap)
def pScratchBuf (c : MemShrinkCfg) : BitVec 64 :=
  c.pExtendStk + BitVec.ofNat 64 (4 * c.extend_cap)
def pTrans (c : MemShrinkCfg) : BitVec 64 := c.pScratchBuf + BitVec.ofNat 64 (4 * c.scratch_cap)
def pWsort (c : MemShrinkCfg) : BitVec 64 := c.pTrans
def pWorkStk1 (c : MemShrinkCfg) : BitVec 64 := c.pTrans + BitVec.ofNat 64 (8 * c.max_vars)
def pWorkStk2 (c : MemShrinkCfg) : BitVec 64 :=
  c.pWorkStk1 + BitVec.ofNat 64 (8 * c.max_vars)
def pTarjanMark (c : MemShrinkCfg) : BitVec 64 :=
  c.pWorkStk2 + BitVec.ofNat 64 (8 * c.max_vars)
def pTarjanReach (c : MemShrinkCfg) : BitVec 64 :=
  c.pTarjanMark + BitVec.ofNat 64 (8 * c.max_vars)
def pRepr (c : MemShrinkCfg) : BitVec 64 :=
  c.pTarjanReach + BitVec.ofNat 64 (8 * c.max_vars)
def pWalkVals (c : MemShrinkCfg) : BitVec 64 := c.pRepr
def pSimSig (c : MemShrinkCfg) : BitVec 64 := c.pRepr + BitVec.ofNat 64 (8 * c.max_vars)
def pWalkBest (c : MemShrinkCfg) : BitVec 64 := c.pSimSig
def pLitMark (c : MemShrinkCfg) : BitVec 64 := c.pSimSig + BitVec.ofNat 64 (8 * c.max_vars)
def pSlack (c : MemShrinkCfg) : BitVec 64 := c.pLitMark + BitVec.ofNat 64 (valsBytes c.max_vars)

def slack (c : MemShrinkCfg) : Nat :=
  c.avail - (m7FixedBytes c.max_vars + m7TransBytes c.max_vars + 4 * c.arena_cap +
    4 * c.wcap + 12 * c.delayed_cap + 4 * c.red_cap + 4 * c.extend_cap + 4 * c.scratch_cap)

end MemShrinkCfg

/-- `FullHdr` trailing `140`-word projection under `MemShrinkCfg`. -/
def m7HdrTailWords0 (c : MemShrinkCfg) (s : FullState) : List (BitVec 64) :=
  let k := s.core; let sc := s.scratch
  [ BitVec.ofNat 64 c.arena_cap, BitVec.ofNat 64 c.wcap, BitVec.ofNat 64 k.arena_len,
    BitVec.ofNat 64 k.wlen, c.pVals, c.pMark, c.pLevel, c.pReason, c.pTrail, c.pWvec,
    c.pArena, c.pWstk, c.pDelayed, c.pTmp, BitVec.ofNat 64 k.trail_end,
    BitVec.ofNat 64 k.propagated, BitVec.ofNat 64 k.cur_level, k.fuel, k.confl_ref,
    BitVec.ofNat 64 k.tmp_cnt, BitVec.ofNat 64 k.tmp_len, c.pHeap, c.pPos, c.pScore,
    c.pPhases, c.pMinStk, c.pMinClr, BitVec.ofNat 64 sc.heap_len, sc.scinc,
    BitVec.ofNat 64 c.minDepth, BitVec.ofNat 64 k.min_clr_len, k.min_clr_full,
    sc.rel_period, sc.rel_limit, sc.rel_wait ]

def m7HdrTailWords1 (c : MemShrinkCfg) (s : FullState) : List (BitVec 64) :=
  let k := s.core; let sc := s.scratch
  [ sc.rel_u, sc.rel_v, sc.rel_trigger, sc.conflicts, sc.learned_lits, sc.min_removed,
    c.pTrailPos, c.pQPrev, c.pQNext, c.pQStamp, c.pPhasesTarget, c.pPhasesBest, c.pWsort,
    c.pShrinkStk, c.pRedRefs, c.pGlueUsed, BitVec.ofNat 64 c.red_cap,
    BitVec.ofNat 64 c.delayed_cap, BitVec.ofNat 64 sc.delayed_len, k.wusable,
    k.arena_garbage, k.first_reducible, k.num_irred, k.num_redundant, k.num_binary,
    k.unflushed, k.probing, k.confl_type, k.confl_lit0, k.confl_lit1, sc.stable,
    sc.switched, sc.mode_count, sc.mode_confl_lim, sc.mode_tick_lim ]

def m7HdrTailWords2 (c : MemShrinkCfg) (s : FullState) : List (BitVec 64) :=
  let k := s.core; let sc := s.scratch
  [ sc.mode_saved_ticks, sc.search_ticks, sc.q_first, sc.q_last, sc.q_search_idx,
    sc.q_search_stamp, sc.q_cur_stamp, sc.target_assigned, sc.best_assigned,
    sc.rephase_limit, sc.rephased, sc.reduce_limit, sc.reductions, sc.tier1, sc.tier2,
    sc.restarts, sc.restart_limit, sc.ema_fast_biased, sc.ema_fast_exp,
    sc.ema_slow_biased, sc.ema_slow_exp, k.oom, BitVec.ofNat 64 c.max_vars,
    BitVec.ofNat 64 k.cur_vars, BitVec.ofNat 64 c.bva_cap, k.unassigned, c.pFlags,
    c.pLitMark, c.pRepr, c.pSimSig, c.pFrameTrail, c.pFrameDec, c.pWorkStk1, c.pWorkStk2,
    c.pTarjanMark ]

def m7HdrTailWords3 (c : MemShrinkCfg) (s : FullState) : List (BitVec 64) :=
  let k := s.core; let sc := s.scratch
  [ c.pTarjanReach, c.pWalkVals, c.pWalkBest, c.pExtendStk, BitVec.ofNat 64 c.extend_cap,
    BitVec.ofNat 64 sc.extend_len, c.pScratchBuf, BitVec.ofNat 64 c.scratch_cap,
    c.pLastLearned, sc.rng_state, sc.chrono_levels, sc.otfs_cnt, sc.eager_sub_cnt,
    sc.probe_limit, sc.probings, sc.elim_limit, sc.eliminations, sc.elim_bound,
    k.dense_mode, k.inconsistent, sc.iterating, sc.hbr_cnt, sc.trans_cnt, sc.viv_cnt,
    sc.subst_cnt, sc.cong_cnt, sc.sweep_cnt, sc.bve_cnt, sc.bce_cnt, sc.bva_cnt,
    sc.walk_cnt_stat, sc.fwd_sub_cnt, sc.fwd_str_cnt, sc.ant_sz, sc.res_sz ]

def m7HdrTailWords (c : MemShrinkCfg) (s : FullState) : List (BitVec 64) :=
  m7HdrTailWords0 c s ++ m7HdrTailWords1 c s ++ m7HdrTailWords2 c s ++ m7HdrTailWords3 c s

theorem m7HdrTailWords_length (c : MemShrinkCfg) (s : FullState) :
    (m7HdrTailWords c s).length = 140 := by
  simp only [m7HdrTailWords, m7HdrTailWords0, m7HdrTailWords1, m7HdrTailWords2, m7HdrTailWords3,
    List.length_append, List.length_cons, List.length_nil]

/-- Resident + `lit_mark` array length invariants under `MemShrinkCfg`. -/
structure MemShrinkLengthsOk (c : MemShrinkCfg) (s : FullState) : Prop where
  vals_len : s.core.vals.length = 2 * c.max_vars
  lit_mark_len : s.core.lit_mark.length = 2 * c.max_vars
  mrk_len : s.core.mrk.length = c.max_vars
  flags_len : s.core.flags.length = c.max_vars
  lvl_len : s.core.lvl.length = c.max_vars
  rsns_len : s.core.rsns.length = c.max_vars
  trl_len : s.core.trl.length = c.max_vars
  trail_pos_len : s.core.trail_pos.length = c.max_vars
  tmp_len_arr : s.core.tmp.length = c.max_vars
  min_clr_len_arr : s.core.min_clr.length = c.max_vars
  frame_trail_len : s.core.frame_trail.length = c.max_vars + 1
  frame_dec_len : s.core.frame_dec.length = c.max_vars + 1
  wvec_len : s.core.wvec.length = 4 * c.max_vars
  min_stk_len : s.core.min_stk.length = 2 * c.minDepth
  arena_len_arr : s.core.arena.length = c.arena_cap
  wstk_len_arr : s.core.wstk.length = c.wcap
  phases_len : s.scratch.phases.length = c.max_vars
  phases_target_len : s.scratch.phases_target.length = c.max_vars
  phases_best_len : s.scratch.phases_best.length = c.max_vars
  heap_len_arr : s.scratch.heap.length = c.max_vars
  pos_len : s.scratch.pos.length = c.max_vars
  shrink_stk_len : s.scratch.shrink_stk.length = c.max_vars
  q_prev_len : s.scratch.q_prev.length = c.max_vars
  q_next_len : s.scratch.q_next.length = c.max_vars
  q_stamp_len : s.scratch.q_stamp.length = c.max_vars
  score_len : s.scratch.score.length = c.max_vars
  glue_used_len : s.scratch.glue_used.length = 64
  last_learned_len : s.scratch.last_learned.length = 16
  delayed_len_arr : s.scratch.delayed.length = 3 * c.delayed_cap
  red_refs_len : s.scratch.red_refs.length = c.red_cap
  extend_stk_len : s.scratch.extend_stk.length = c.extend_cap
  scratch_buf_len : s.scratch.scratch_buf.length = c.scratch_cap
  cur_vars_ge : c.mv ≤ s.core.cur_vars
  cur_vars_le : s.core.cur_vars ≤ c.max_vars
  arena_len_le : s.core.arena_len ≤ c.arena_cap
  wlen_le : s.core.wlen ≤ c.wcap
  trail_end_le : s.core.trail_end ≤ s.core.cur_vars
  propagated_le : s.core.propagated ≤ s.core.trail_end
  tmp_len_le : s.core.tmp_len ≤ c.max_vars
  min_clr_len_le : s.core.min_clr_len ≤ c.max_vars
  heap_len_le : s.scratch.heap_len ≤ c.max_vars
  delayed_len_le : s.scratch.delayed_len ≤ c.delayed_cap
  extend_len_le : s.scratch.extend_len ≤ c.extend_cap

/-- Resident byte arrays paired with their 8-byte alignment slack. -/
def MemShrinkResBytes (c : MemShrinkCfg) (s : FullState) : Mem 64 → Prop :=
  (array (t := i8) c.pVals s.core.vals ⋆
    region (c.pVals + BitVec.ofNat 64 (2 * c.max_vars)) (valsBytes c.max_vars - 2 * c.max_vars)) ⋆
  (array (t := i8) c.pMark s.core.mrk ⋆
    region (c.pMark + BitVec.ofNat 64 c.max_vars) (markBytes c.max_vars - c.max_vars)) ⋆
  (array (t := i8) c.pPhases s.scratch.phases ⋆
    region (c.pPhases + BitVec.ofNat 64 c.max_vars) (markBytes c.max_vars - c.max_vars)) ⋆
  (array (t := i8) c.pPhasesTarget s.scratch.phases_target ⋆
    region (c.pPhasesTarget + BitVec.ofNat 64 c.max_vars) (markBytes c.max_vars - c.max_vars)) ⋆
  (array (t := i8) c.pPhasesBest s.scratch.phases_best ⋆
    region (c.pPhasesBest + BitVec.ofNat 64 c.max_vars) (markBytes c.max_vars - c.max_vars))

/-- Resident `u32` search arrays (block A) paired with `u32FullBytes` alignment slack. -/
def MemShrinkResU32A (c : MemShrinkCfg) (s : FullState) : Mem 64 → Prop :=
  (array (t := i32) c.pFlags s.core.flags ⋆
    region (c.pFlags + BitVec.ofNat 64 (4 * c.max_vars))
      (u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
  (array (t := i32) c.pLevel s.core.lvl ⋆
    region (c.pLevel + BitVec.ofNat 64 (4 * c.max_vars))
      (u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
  (array (t := i32) c.pReason s.core.rsns ⋆
    region (c.pReason + BitVec.ofNat 64 (4 * c.max_vars))
      (u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
  (array (t := i32) c.pTrail s.core.trl ⋆
    region (c.pTrail + BitVec.ofNat 64 (4 * c.max_vars))
      (u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
  (array (t := i32) c.pTrailPos s.core.trail_pos ⋆
    region (c.pTrailPos + BitVec.ofNat 64 (4 * c.max_vars))
      (u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
  (array (t := i32) c.pTmp s.core.tmp ⋆
    region (c.pTmp + BitVec.ofNat 64 (4 * c.max_vars))
      (u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
  (array (t := i32) c.pHeap s.scratch.heap ⋆
    region (c.pHeap + BitVec.ofNat 64 (4 * c.max_vars))
      (u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
  (array (t := i32) c.pPos s.scratch.pos ⋆
    region (c.pPos + BitVec.ofNat 64 (4 * c.max_vars))
      (u32FullBytes c.max_vars - 4 * c.max_vars))

/-- Resident `u32` search arrays (block B) paired with `u32FullBytes` alignment slack. -/
def MemShrinkResU32B (c : MemShrinkCfg) (s : FullState) : Mem 64 → Prop :=
  (array (t := i32) c.pMinClr s.core.min_clr ⋆
    region (c.pMinClr + BitVec.ofNat 64 (4 * c.max_vars))
      (u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
  (array (t := i32) c.pShrinkStk s.scratch.shrink_stk ⋆
    region (c.pShrinkStk + BitVec.ofNat 64 (4 * c.max_vars))
      (u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
  (array (t := i32) c.pQPrev s.scratch.q_prev ⋆
    region (c.pQPrev + BitVec.ofNat 64 (4 * c.max_vars))
      (u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
  (array (t := i32) c.pQNext s.scratch.q_next ⋆
    region (c.pQNext + BitVec.ofNat 64 (4 * c.max_vars))
      (u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
  (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
    region (c.pQStamp + BitVec.ofNat 64 (4 * c.max_vars))
      (u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
  (array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
    region (c.pFrameTrail + BitVec.ofNat 64 (4 * (c.max_vars + 1)))
      (u32FullBytes c.max_vars - 4 * (c.max_vars + 1))) ⋆
  (array (t := i32) c.pFrameDec s.core.frame_dec ⋆
    region (c.pFrameDec + BitVec.ofNat 64 (4 * (c.max_vars + 1)))
      (u32FullBytes c.max_vars - 4 * (c.max_vars + 1)))

/-- Resident tail (`watch_vec`, `score`, `min_stk`, `glue_used`, `last_learned`, dynamic). -/
def MemShrinkResTail (c : MemShrinkCfg) (s : FullState) : Mem 64 → Prop :=
  array (t := i32) c.pWvec s.core.wvec ⋆
  array64 c.pScore s.scratch.score ⋆
  array (t := i32) c.pMinStk s.core.min_stk ⋆
  array (t := i32) c.pGlueUsed s.scratch.glue_used ⋆
  array (t := i32) c.pLastLearned s.scratch.last_learned ⋆
  array (t := i32) c.pArena s.core.arena ⋆
  array (t := i32) c.pWstk s.core.wstk ⋆
  array (t := i32) c.pDelayed s.scratch.delayed ⋆
  array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
  array (t := i32) c.pExtendStk s.scratch.extend_stk ⋆
  array (t := i32) c.pScratchBuf s.scratch.scratch_buf

/-- All resident fixed + dynamic arrays (`90 B/var` fixed + dynamic buffers). -/
def MemShrinkResArrays (c : MemShrinkCfg) (s : FullState) : Mem 64 → Prop :=
  MemShrinkResBytes c s ⋆ MemShrinkResU32A c s ⋆ MemShrinkResU32B c s ⋆ MemShrinkResTail c s

/-- Persistent dedicated `lit_mark` slot (disjoint from overlaid transient pool). -/
def MemShrinkLitMark (c : MemShrinkCfg) (s : FullState) : Mem 64 → Prop :=
  array (t := i8) c.pLitMark s.core.lit_mark ⋆
  region (c.pLitMark + BitVec.ofNat 64 (2 * c.max_vars)) (valsBytes c.max_vars - 2 * c.max_vars)

/-- Overlaid `56 B/var` transient region backing `{wsort, work_stk1, work_stk2, tarjan_mark,
tarjan_reach, repr/walk_vals, sim_sig/walk_best}`. -/
def MemShrinkTransRegions (c : MemShrinkCfg) : Mem 64 → Prop :=
  region c.pWsort (8 * c.max_vars) ⋆
  region c.pWorkStk1 (8 * c.max_vars) ⋆
  region c.pWorkStk2 (8 * c.max_vars) ⋆
  region c.pTarjanMark (8 * c.max_vars) ⋆
  region c.pTarjanReach (8 * c.max_vars) ⋆
  region c.pRepr (8 * c.max_vars) ⋆
  region c.pSimSig (8 * c.max_vars)

/-- WalkSAT view of `MemShrinkTransRegions` (`walk_vals` in `repr`, `walk_best` in `sim_sig`). -/
def MemShrinkTransWalk (c : MemShrinkCfg)
    (wsort ws1 ws2 tmk trc : List (BitVec 32)) (wvals wbest : List (BitVec 8)) : Mem 64 → Prop :=
  array (t := i32) c.pWsort wsort ⋆
  array (t := i32) c.pWorkStk1 ws1 ⋆
  array (t := i32) c.pWorkStk2 ws2 ⋆
  array (t := i32) c.pTarjanMark tmk ⋆
  array (t := i32) c.pTarjanReach trc ⋆
  (array (t := i8) c.pWalkVals wvals ⋆
    region (c.pWalkVals + BitVec.ofNat 64 (2 * c.max_vars)) (8 * c.max_vars - 2 * c.max_vars)) ⋆
  (array (t := i8) c.pWalkBest wbest ⋆
    region (c.pWalkBest + BitVec.ofNat 64 c.max_vars) (8 * c.max_vars - c.max_vars))

/-- Congruence/Tarjan/BVE view of `MemShrinkTransRegions` (`repr` & `sim_sig` unaliased). -/
def MemShrinkTransCong (c : MemShrinkCfg)
    (wsort ws1 ws2 tmk trc repr : List (BitVec 32)) (sig : List (BitVec 64)) : Mem 64 → Prop :=
  array (t := i32) c.pWsort wsort ⋆
  array (t := i32) c.pWorkStk1 ws1 ⋆
  array (t := i32) c.pWorkStk2 ws2 ⋆
  array (t := i32) c.pTarjanMark tmk ⋆
  array (t := i32) c.pTarjanReach trc ⋆
  array (t := i32) c.pRepr repr ⋆
  array64 c.pSimSig sig

/-- Complete Prototype A separation-logic memory invariant. -/
def MemShrinkMem (c : MemShrinkCfg) (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (m7HdrTailWords c s) ⋆
  MemShrinkResArrays c s ⋆
  MemShrinkLitMark c s ⋆
  MemShrinkTransRegions c ⋆
  region c.pSlack c.slack

/-- Cleared `mrk` and `lit_mark` invariant under `MemShrinkCfg`. -/
def MemShrinkMarksClear (c : MemShrinkCfg) (s : FullState) : Prop :=
  (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8) ∧
  (∀ l < 2 * c.max_vars, s.core.lit_mark[l]?.getD 0#8 = 0#8)

/-- Initial empty-formula sparse invariant established by `full_init_state_m7`. -/
def MemShrinkSparseInv (c : MemShrinkCfg) (s : FullState) : Prop :=
  MemShrinkLengthsOk c s ∧ MemShrinkMarksClear c s ∧
  (∀ i < 8, s.scratch.last_learned[i]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) ∧
  s.scratch.extend_len ≤ c.extend_cap

/-! ## 2. Transient Overlay View Equivalences & `array64` Constant Bridges -/

private theorem cell_i32_eq_int4 (a v : BitVec 64) :
    cell (t := i32) a (v.setWidth 32) = int4 a v := by
  dsimp only [cell, int4, Ty.bytes, Ty.size, toBits]
  rw [show (32 + 7) / 8 = 4 by decide, show 8 * 4 = 32 by decide]
  congr 1; congr 1
  rw [← Int.toBytes_emod (n := 4), ← Int.toBytes_emod (n := 4) (x := (v.toNat : Int))]
  congr 1; simp only [Int.take]
  rw [show BitVec.setWidth 32 (BitVec.setWidth 32 v) = BitVec.setWidth 32 v from
    BitVec.eq_of_toNat_eq (by simp), BitVec.toInt_eq_msb_cond]
  cases (v.setWidth 32).msb
  · simp [BitVec.toNat_setWidth]
  · simp only [↓reduceIte, BitVec.toNat_setWidth]
    have hsub : ((v.toNat % 2 ^ 32 : Nat) : Int) - (2 ^ 32 : Nat) =
        ((v.toNat % 2 ^ 32 : Nat) : Int) - (2 : Int) ^ 32 := by simp
    rw [hsub, Int.sub_emod_right]
    have hnat : ((v.toNat % 2 ^ 32 : Nat) : Int) = (v.toNat : Int) % (2 : Int) ^ 32 := by omega
    rw [hnat, Int.emod_emod_of_dvd _ (by decide)]

private theorem cell_i8_eq_byte1 (a v : BitVec 64) :
    cell (t := i8) a (v.setWidth 8) = byte1 a v := by
  dsimp only [cell, byte1, Ty.bytes, Ty.size, toBits]
  rw [show (8 + 7) / 8 = 1 by decide, show 8 * 1 = 8 by decide]
  congr 1; congr 1
  rw [← Int.toBytes_emod (n := 1), ← Int.toBytes_emod (n := 1) (x := (v.toNat : Int))]
  congr 1; simp only [Int.take]
  rw [show BitVec.setWidth 8 (BitVec.setWidth 8 v) = BitVec.setWidth 8 v from
    BitVec.eq_of_toNat_eq (by simp), BitVec.toInt_eq_msb_cond]
  cases (v.setWidth 8).msb
  · simp [BitVec.toNat_setWidth]
  · simp only [↓reduceIte, BitVec.toNat_setWidth]
    have hsub : ((v.toNat % 2 ^ 8 : Nat) : Int) - (2 ^ 8 : Nat) =
        ((v.toNat % 2 ^ 8 : Nat) : Int) - (2 : Int) ^ 8 := by simp
    rw [hsub, Int.sub_emod_right]
    have hnat : ((v.toNat % 2 ^ 8 : Nat) : Int) = (v.toNat : Int) % (2 : Int) ^ 8 := by omega
    rw [hnat, Int.emod_emod_of_dvd _ (by decide)]

private theorem int4Array_eq_array (a : BitVec 64) (xs64 : List (BitVec 64)) :
    int4Array a xs64 = array (t := i32) a (xs64.map (·.setWidth 32)) := by
  induction xs64 generalizing a with
  | nil => rw [int4Array_nil, List.map_nil, array_nil]
  | cons v vs ih =>
    rw [int4Array_cons, List.map_cons, array_cons, ih (a + 4), ← cell_i32_eq_int4,
      show BitVec.ofNat 64 i32.bytes = 4 from by decide]

private theorem byte1Array_eq_array (a : BitVec 64) (xs64 : List (BitVec 64)) :
    byte1Array a xs64 = array (t := i8) a (xs64.map (·.setWidth 8)) := by
  induction xs64 generalizing a with
  | nil => rw [byte1Array_nil, List.map_nil, array_nil]
  | cons v vs ih =>
    rw [byte1Array_cons, List.map_cons, array_cons, ih (a + 1), ← cell_i8_eq_byte1,
      show BitVec.ofNat 64 i8.bytes = 1 from by decide]

theorem reg_to_i32_exact {a : BitVec 64} {n : Nat} (hn : 4 * n ≤ 2 ^ 64) {m : Mem 64}
    (hm : region a (4 * n) m) :
    ∃ xs : List (BitVec 32), xs.length = n ∧ array (t := i32) a xs m := by
  obtain ⟨xs64, hlen, harr⟩ := region_to_int4Array n hn hm
  exact ⟨xs64.map (·.setWidth 32), by simp [hlen], int4Array_eq_array a xs64 ▸ harr⟩

theorem reg_to_i8_exact {a : BitVec 64} {n : Nat} (hn : n ≤ 2 ^ 64) {m : Mem 64}
    (hm : region a n m) :
    ∃ xs : List (BitVec 8), xs.length = n ∧ array (t := i8) a xs m := by
  obtain ⟨xs64, hlen, harr⟩ := region_to_byte1Array n hn hm
  exact ⟨xs64.map (·.setWidth 8), by simp [hlen], byte1Array_eq_array a xs64 ▸ harr⟩

theorem reg_to_i64_exact {a : BitVec 64} {n : Nat} (hn : 8 * n ≤ 2 ^ 64) {m : Mem 64}
    (hm : region a (8 * n) m) :
    ∃ xs : List (BitVec 64), xs.length = n ∧ array64 a xs m := by
  obtain ⟨xs, hlen, harr⟩ := region_to_word8Array n hn hm
  exact ⟨xs, hlen, (array64_eq_word8Array a xs).symm ▸ harr⟩

theorem i32_exact_to_reg {a : BitVec 64} {xs : List (BitVec 32)}
    (h : 4 * xs.length ≤ 2 ^ 64) {m : Mem 64} (hm : array (t := i32) a xs m) :
    region a (4 * xs.length) m :=
  ⟨bytesOf (t := i32) xs, by simp [bytesOf_length, Ty.bytes, Ty.size],
    array_eq_bytesOf (t := i32) a xs (by simpa [Ty.bytes, Ty.size] using h) hm⟩

theorem i8_exact_to_reg {a : BitVec 64} {xs : List (BitVec 8)}
    (h : xs.length ≤ 2 ^ 64) {m : Mem 64} (hm : array (t := i8) a xs m) :
    region a xs.length m :=
  ⟨bytesOf (t := i8) xs, by simp [bytesOf_length, Ty.bytes, Ty.size],
    array_eq_bytesOf (t := i8) a xs (by simpa [Ty.bytes, Ty.size] using h) hm⟩

private theorem bytes64_eq_bytesN8 (xs : List (BitVec 64)) :
    bytes64 xs = bytesN 8 xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    unfold bytes64 bytesN at ih ⊢
    simp only [List.flatMap_cons, ih]
    congr 1
    rw [← Int.toBytes_emod, ← Int.toBytes_emod (x := (x.toNat : Int))]
    congr 1
    simp only [Int.take]
    rw [BitVec.toInt_eq_msb_cond]
    have hlt : 0 ≤ (x.toNat : Int) ∧ (x.toNat : Int) < 2 ^ 64 :=
      ⟨Int.natCast_nonneg _, by exact_mod_cast x.isLt⟩
    cases x.msb
    · simp
    · simp only [↓reduceIte, Int.natCast_pow, Int.cast_ofNat_Int]
      rw [show (2 : Int) ^ (8 * 8) = (2 : Int) ^ 64 by decide, Int.sub_emod_right]

theorem i64_exact_to_reg {a : BitVec 64} {xs : List (BitVec 64)}
    (h : 8 * xs.length ≤ 2 ^ 64) {m : Mem 64} (hm : array64 a xs m) :
    region a (8 * xs.length) m := by
  rw [array64_eq_word8Array, word8Array_eq a xs h] at hm
  exact ⟨bytesN 8 xs, by simp [bytesN_length], hm.symm⟩

private theorem sep_mono7 {A1 A2 A3 A4 A5 A6 A7 B1 B2 B3 B4 B5 B6 B7 : Mem 64 → Prop}
    {m : Mem 64}
    (h1 : ∀ x, A1 x → B1 x) (h2 : ∀ x, A2 x → B2 x) (h3 : ∀ x, A3 x → B3 x)
    (h4 : ∀ x, A4 x → B4 x) (h5 : ∀ x, A5 x → B5 x) (h6 : ∀ x, A6 x → B6 x)
    (h7 : ∀ x, A7 x → B7 x)
    (hm : (A1 ⋆ A2 ⋆ A3 ⋆ A4 ⋆ A5 ⋆ A6 ⋆ A7) m) :
    (B1 ⋆ B2 ⋆ B3 ⋆ B4 ⋆ B5 ⋆ B6 ⋆ B7) m :=
  sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 h1 h2) h3) h4) h5) h6) h7 m hm

private theorem sep_ex_len {α : Type} {A : Mem 64 → Prop} {P : α → Mem 64 → Prop}
    {L : α → Nat} {len : Nat} {Q : Mem 64 → Prop} {m : Mem 64}
    (hA : ∀ x, A x → ∃ a, L a = len ∧ P a x) (h : (A ⋆ Q) m) :
    ∃ a, L a = len ∧ (P a ⋆ Q) m := by
  obtain ⟨a, ha⟩ := sep_ex_l.mp (sep_mono hA h)
  exact ⟨a, (sep_pure_l.mp ha).1, (sep_pure_l.mp ha).2⟩

private theorem sep_ex_len_r {α : Type} {Q A : Mem 64 → Prop} {P : α → Mem 64 → Prop}
    {L : α → Nat} {len : Nat} {m : Mem 64}
    (hA : ∀ x, A x → ∃ a, L a = len ∧ P a x) (h : (Q ⋆ A) m) :
    ∃ a, L a = len ∧ (Q ⋆ P a) m := by
  obtain ⟨a, ha⟩ := sep_ex_r.mp (sep_mono_r hA h)
  exact ⟨a, (sep_pure_r.mp ha).1, (sep_pure_r.mp ha).2⟩

private theorem sep_peel_mid {α : Type} {Q A : Mem 64 → Prop} {P : α → Mem 64 → Prop}
    {B : Mem 64 → Prop} {L : α → Nat} {len : Nat} {m : Mem 64}
    (hA : ∀ x, A x → ∃ a, L a = len ∧ P a x) (h : ((Q ⋆ A) ⋆ B) m) :
    ∃ a, L a = len ∧ ((Q ⋆ P a) ⋆ B) m := by
  obtain ⟨a, ha⟩ := sep_ex_l.mp (sep_mono (fun _ hx => sep_ex_len_r hA hx) h)
  exact ⟨a, (sep_pure_l.mp ha).1, (sep_pure_l.mp ha).2⟩

private theorem reg_to_i32_2mx {a : BitVec 64} {mx : Nat} (hmx : 8 * mx ≤ 2 ^ 64) {m : Mem 64}
    (h : region a (8 * mx) m) :
    ∃ xs : List (BitVec 32), xs.length = 2 * mx ∧ array (t := i32) a xs m :=
  reg_to_i32_exact (by omega) (show region a (4 * (2 * mx)) m by
    simpa [show 4 * (2 * mx) = 8 * mx by omega] using h)

theorem m7Trans_to_walk {c : MemShrinkCfg} {m : Mem 64}
    (h : MemShrinkTransRegions c m) :
    ∃ (ws ws1 ws2 tmk trc : List (BitVec 32)) (wv wb : List (BitVec 8)),
      ws.length = 2 * c.max_vars ∧ ws1.length = 2 * c.max_vars ∧
      ws2.length = 2 * c.max_vars ∧ tmk.length = 2 * c.max_vars ∧
      trc.length = 2 * c.max_vars ∧ wv.length = 2 * c.max_vars ∧
      wb.length = c.max_vars ∧ MemShrinkTransWalk c ws ws1 ws2 tmk trc wv wb m := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hwv_sp : 8 * c.max_vars = 2 * c.max_vars + (8 * c.max_vars - 2 * c.max_vars) := by omega
  have hwb_sp : 8 * c.max_vars = c.max_vars + (8 * c.max_vars - c.max_vars) := by omega
  unfold MemShrinkTransRegions at h
  have hwb_peel : ∀ x, region c.pSimSig (8 * c.max_vars) x →
      ∃ wb : List (BitVec 8), wb.length = c.max_vars ∧
        (array (t := i8) c.pWalkBest wb ⋆
          region (c.pWalkBest + BitVec.ofNat 64 c.max_vars) (8 * c.max_vars - c.max_vars)) x :=
    fun x rx => by
    have hp := reg_peel (b := c.pWalkBest + BitVec.ofNat 64 c.max_vars)
      (n1 := c.max_vars) (n2 := 8 * c.max_vars - c.max_vars) rx rfl hwb_sp (by omega)
    exact sep_ex_len (fun _ r => reg_to_i8_exact (by omega) r) hp
  have hwv_peel : ∀ x, region c.pRepr (8 * c.max_vars) x →
      ∃ wv : List (BitVec 8), wv.length = 2 * c.max_vars ∧
        (array (t := i8) c.pWalkVals wv ⋆
          region (c.pWalkVals + BitVec.ofNat 64 (2 * c.max_vars))
            (8 * c.max_vars - 2 * c.max_vars)) x := fun x rx => by
    have hp := reg_peel (b := c.pWalkVals + BitVec.ofNat 64 (2 * c.max_vars))
      (n1 := 2 * c.max_vars) (n2 := 8 * c.max_vars - 2 * c.max_vars) rx rfl hwv_sp (by omega)
    exact sep_ex_len (fun _ r => reg_to_i8_exact (by omega) r) hp
  obtain ⟨wb, lwb, h⟩ := sep_ex_len_r hwb_peel h
  obtain ⟨wv, lwv, h⟩ := sep_peel_mid hwv_peel h
  rw [sep_assoc] at h
  obtain ⟨trc, ltrc, h⟩ :=
    sep_peel_mid (fun _ r => reg_to_i32_2mx (mx := c.max_vars) (by omega) r) h
  rw [sep_assoc] at h
  obtain ⟨tmk, ltmk, h⟩ :=
    sep_peel_mid (fun _ r => reg_to_i32_2mx (mx := c.max_vars) (by omega) r) h
  rw [sep_assoc] at h
  obtain ⟨ws2, lws2, h⟩ :=
    sep_peel_mid (fun _ r => reg_to_i32_2mx (mx := c.max_vars) (by omega) r) h
  rw [sep_assoc] at h
  obtain ⟨ws1, lws1, h⟩ :=
    sep_peel_mid (fun _ r => reg_to_i32_2mx (mx := c.max_vars) (by omega) r) h
  rw [sep_assoc] at h
  obtain ⟨ws, lws, h⟩ := sep_ex_len (fun _ r => reg_to_i32_2mx (mx := c.max_vars) (by omega) r) h
  refine ⟨ws, ws1, ws2, tmk, trc, wv, wb, lws, lws1, lws2, ltmk, ltrc, lwv, lwb, ?_⟩
  unfold MemShrinkTransWalk
  simpa only [← sep_assoc] using h

theorem m7TransWalk_to_regions {c : MemShrinkCfg}
    {ws ws1 ws2 tmk trc : List (BitVec 32)} {wv wb : List (BitVec 8)} {m : Mem 64}
    (lws : ws.length = 2 * c.max_vars) (lws1 : ws1.length = 2 * c.max_vars)
    (lws2 : ws2.length = 2 * c.max_vars) (ltmk : tmk.length = 2 * c.max_vars)
    (ltrc : trc.length = 2 * c.max_vars) (lwv : wv.length = 2 * c.max_vars)
    (lwb : wb.length = c.max_vars)
    (h : MemShrinkTransWalk c ws ws1 ws2 tmk trc wv wb m) :
    MemShrinkTransRegions c m := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have h24 : 4 * (2 * c.max_vars) = 8 * c.max_vars := by omega
  refine sep_mono7
    (fun _ hx => h24 ▸ lws ▸ i32_exact_to_reg (xs := ws) (by rw [lws]; omega) hx)
    (fun _ hx => h24 ▸ lws1 ▸ i32_exact_to_reg (xs := ws1) (by rw [lws1]; omega) hx)
    (fun _ hx => h24 ▸ lws2 ▸ i32_exact_to_reg (xs := ws2) (by rw [lws2]; omega) hx)
    (fun _ hx => h24 ▸ ltmk ▸ i32_exact_to_reg (xs := tmk) (by rw [ltmk]; omega) hx)
    (fun _ hx => h24 ▸ ltrc ▸ i32_exact_to_reg (xs := trc) (by rw [ltrc]; omega) hx)
    (fun x hx => ?_) (fun x hx => ?_) h
  · have h1 := sep_mono (fun _ r => lwv ▸ i8_exact_to_reg (xs := wv) (by rw [lwv]; omega) r) hx
    change (region c.pWalkVals (2 * c.max_vars) ⋆
      region (c.pWalkVals + BitVec.ofNat 64 (2 * c.max_vars))
        (8 * c.max_vars - 2 * c.max_vars)) x at h1
    rwa [region_merge_eq (n := 8 * c.max_vars) (by omega) (by omega)] at h1
  · have h1 := sep_mono (fun _ r => lwb ▸ i8_exact_to_reg (xs := wb) (by rw [lwb]; omega) r) hx
    change (region c.pWalkBest c.max_vars ⋆
      region (c.pWalkBest + BitVec.ofNat 64 c.max_vars) (8 * c.max_vars - c.max_vars)) x at h1
    rwa [region_merge_eq (n := 8 * c.max_vars) (by omega) (by omega)] at h1

theorem m7Trans_to_cong {c : MemShrinkCfg} {m : Mem 64}
    (h : MemShrinkTransRegions c m) :
    ∃ (ws ws1 ws2 tmk trc repr : List (BitVec 32)) (sig : List (BitVec 64)),
      ws.length = 2 * c.max_vars ∧ ws1.length = 2 * c.max_vars ∧
      ws2.length = 2 * c.max_vars ∧ tmk.length = 2 * c.max_vars ∧
      trc.length = 2 * c.max_vars ∧ repr.length = 2 * c.max_vars ∧
      sig.length = c.max_vars ∧ MemShrinkTransCong c ws ws1 ws2 tmk trc repr sig m := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  unfold MemShrinkTransRegions at h
  obtain ⟨sig, lsg, h⟩ :=
    sep_ex_len_r (fun _ r => reg_to_i64_exact (n := c.max_vars) (by omega) r) h
  obtain ⟨repr, lrp, h⟩ :=
    sep_peel_mid (fun _ r => reg_to_i32_2mx (mx := c.max_vars) (by omega) r) h
  rw [sep_assoc] at h
  obtain ⟨trc, ltrc, h⟩ :=
    sep_peel_mid (fun _ r => reg_to_i32_2mx (mx := c.max_vars) (by omega) r) h
  rw [sep_assoc] at h
  obtain ⟨tmk, ltmk, h⟩ :=
    sep_peel_mid (fun _ r => reg_to_i32_2mx (mx := c.max_vars) (by omega) r) h
  rw [sep_assoc] at h
  obtain ⟨ws2, lws2, h⟩ :=
    sep_peel_mid (fun _ r => reg_to_i32_2mx (mx := c.max_vars) (by omega) r) h
  rw [sep_assoc] at h
  obtain ⟨ws1, lws1, h⟩ :=
    sep_peel_mid (fun _ r => reg_to_i32_2mx (mx := c.max_vars) (by omega) r) h
  rw [sep_assoc] at h
  obtain ⟨ws, lws, h⟩ := sep_ex_len (fun _ r => reg_to_i32_2mx (mx := c.max_vars) (by omega) r) h
  refine ⟨ws, ws1, ws2, tmk, trc, repr, sig, lws, lws1, lws2, ltmk, ltrc, lrp, lsg, ?_⟩
  unfold MemShrinkTransCong
  simpa only [← sep_assoc] using h

theorem m7TransCong_to_regions {c : MemShrinkCfg}
    {ws ws1 ws2 tmk trc repr : List (BitVec 32)} {sig : List (BitVec 64)} {m : Mem 64}
    (lws : ws.length = 2 * c.max_vars) (lws1 : ws1.length = 2 * c.max_vars)
    (lws2 : ws2.length = 2 * c.max_vars) (ltmk : tmk.length = 2 * c.max_vars)
    (ltrc : trc.length = 2 * c.max_vars) (lrp : repr.length = 2 * c.max_vars)
    (lsg : sig.length = c.max_vars)
    (h : MemShrinkTransCong c ws ws1 ws2 tmk trc repr sig m) :
    MemShrinkTransRegions c m := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have h24 : 4 * (2 * c.max_vars) = 8 * c.max_vars := by omega
  exact sep_mono7
    (fun _ hx => h24 ▸ lws ▸ i32_exact_to_reg (xs := ws) (by rw [lws]; omega) hx)
    (fun _ hx => h24 ▸ lws1 ▸ i32_exact_to_reg (xs := ws1) (by rw [lws1]; omega) hx)
    (fun _ hx => h24 ▸ lws2 ▸ i32_exact_to_reg (xs := ws2) (by rw [lws2]; omega) hx)
    (fun _ hx => h24 ▸ ltmk ▸ i32_exact_to_reg (xs := tmk) (by rw [ltmk]; omega) hx)
    (fun _ hx => h24 ▸ ltrc ▸ i32_exact_to_reg (xs := trc) (by rw [ltrc]; omega) hx)
    (fun _ hx => h24 ▸ lrp ▸ i32_exact_to_reg (xs := repr) (by rw [lrp]; omega) hx)
    (fun _ hx => lsg ▸ i64_exact_to_reg (xs := sig) (by rw [lsg]; omega) hx) h

private theorem array64_eq_At_bytes64 (a : BitVec 64) (ys : List (BitVec 64))
    (h : 8 * ys.length ≤ 2 ^ 64) : array64 a ys = Eq ((bytes64 ys).At a) := by
  rw [array64_eq_word8Array, word8Array_eq a ys h, bytes64_eq_bytesN8]

private theorem array_eq_At_bytesOf {t : Ty} (a : BitVec 64) (xs : List (Val t))
    (h : t.bytes * xs.length ≤ 2 ^ 64) : array a xs = Eq ((bytesOf xs).At a) := by
  funext m; apply propext; constructor
  · intro hm; exact (array_eq_bytesOf a xs h hm).symm
  · intro hm; subst hm; exact array_bytes a xs h

private theorem replicate_add_list {α : Type} (a b : Nat) (x : α) :
    List.replicate (a + b) x = List.replicate a x ++ List.replicate b x := by
  induction a with
  | zero => simp
  | succ a ih => rw [Nat.succ_add, List.replicate_succ, List.replicate_succ, ih, List.cons_append]

private theorem bytesOf_append {t : Ty} (xs ys : List (Val t)) :
    bytesOf (xs ++ ys) = bytesOf xs ++ bytesOf ys := by
  simp [bytesOf, List.flatMap_append]

private theorem bytes64_rep_eq_bytesOf {t : Ty} (w : BitVec 64) (v : Val t) (k n : Nat)
    (h1 : bytes64 [w] = bytesOf (List.replicate k v)) :
    bytes64 (List.replicate n w) = bytesOf (List.replicate (k * n) v) := by
  induction n with
  | zero => simp [bytes64, bytesOf]
  | succ n ih =>
    rw [List.replicate_succ, Nat.mul_succ, Nat.add_comm (k * n) k, replicate_add_list,
      bytesOf_append, ← ih, ← h1]
    simp [bytes64, List.flatMap_cons]

theorem array64_rep_eq_array {t : Ty} (w : BitVec 64) (v : Val t) (k : Nat)
    (hsz : t.bytes * k = 8) (h1 : bytes64 [w] = bytesOf (List.replicate k v))
    (a : BitVec 64) (n : Nat) (hn : 8 * n ≤ 2 ^ 64) :
    array64 a (List.replicate n w) = array a (List.replicate (k * n) v) := by
  rw [array64_eq_At_bytes64 a _ (by simpa using hn),
    array_eq_At_bytesOf a _
      (by simp only [List.length_replicate]; rw [← Nat.mul_assoc, hsz]; exact hn),
    bytes64_rep_eq_bytesOf w v k n h1]

theorem bytes64_zero_i8 : bytes64 [0#64] = bytesOf (t := i8) (List.replicate 8 0#8) := by decide
theorem bytes64_one_i8 :
    bytes64 [0x0101010101010101#64] = bytesOf (t := i8) (List.replicate 8 1#8) := by decide
theorem bytes64_zero_i32 : bytes64 [0#64] = bytesOf (t := i32) (List.replicate 2 0#32) := by
  decide
theorem bytes64_ff_i32 :
    bytes64 [0xFFFFFFFFFFFFFFFF#64] = bytesOf (t := i32) (List.replicate 2 0xFFFFFFFF#32) := by
  decide

theorem array_i8_pad_to_u64 {a : BitVec 64} {xs : List (BitVec 8)} {used w : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} (hx : xs.length = used) (hle : used ≤ 8 * w)
    (hfit : 8 * w ≤ 2 ^ 64)
    (hm : ((array (t := i8) a xs ⋆ region (a + BitVec.ofNat 64 used) (8 * w - used)) ⋆ R) m) :
    ∃ ys : List (BitVec 64), ys.length = w ∧ (array64 a ys ⋆ R) m := by
  refine sep_ex_len (fun x h1 => ?_) hm
  have hreg : region a (8 * w) x := by
    rw [show 8 * w = used + (8 * w - used) by omega, region_split (by omega)]
    exact sep_mono (fun _ ha => hx ▸ i8_exact_to_reg (xs := xs) (by omega) ha) h1
  exact reg_to_i64_exact hfit hreg

theorem array64_rep_to_i8_pad {a : BitVec 64} {w used : Nat} {val64 : BitVec 64} {v8 : BitVec 8}
    {R : Mem 64 → Prop} {m : Mem 64} (hle : used ≤ 8 * w) (hfit : 8 * w ≤ 2 ^ 64)
    (h1 : bytes64 [val64] = bytesOf (t := i8) (List.replicate 8 v8))
    (hm : (array64 a (List.replicate w val64) ⋆ R) m) :
    ((array (t := i8) a (List.replicate used v8) ⋆
      region (a + BitVec.ofNat 64 used) (8 * w - used)) ⋆ R) m := by
  rw [array64_rep_eq_array (t := i8) val64 v8 8 rfl h1 a w hfit,
    show 8 * w = used + (8 * w - used) by omega, replicate_add_list,
    array_append (t := i8) a] at hm
  simp only [Ty.bytes, Ty.size, i8, List.length_replicate] at hm
  exact sep_mono (fun _ h => sep_mono_r (fun _ hr => by
    simpa using i8_exact_to_reg (xs := List.replicate (8 * w - used) v8) (by simp; omega) hr) h) hm

theorem array_i32_pad_to_u64 {a : BitVec 64} {xs : List (BitVec 32)} {used w : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} (hx : xs.length = used) (hle : 4 * used ≤ 8 * w)
    (hfit : 8 * w ≤ 2 ^ 64)
    (hm : ((array (t := i32) a xs ⋆
      region (a + BitVec.ofNat 64 (4 * used)) (8 * w - 4 * used)) ⋆ R) m) :
    ∃ ys : List (BitVec 64), ys.length = w ∧ (array64 a ys ⋆ R) m := by
  refine sep_ex_len (fun x h1 => ?_) hm
  have hreg : region a (8 * w) x := by
    rw [show 8 * w = 4 * used + (8 * w - 4 * used) by omega, region_split (by omega)]
    exact sep_mono (fun _ ha => hx ▸ i32_exact_to_reg (xs := xs) (by omega) ha) h1
  exact reg_to_i64_exact hfit hreg

theorem array64_rep_to_i32_pad {a : BitVec 64} {w used : Nat} {val64 : BitVec 64} {v32 : BitVec 32}
    {R : Mem 64 → Prop} {m : Mem 64} (hle : used ≤ 2 * w) (hfit : 8 * w ≤ 2 ^ 64)
    (h1 : bytes64 [val64] = bytesOf (t := i32) (List.replicate 2 v32))
    (hm : (array64 a (List.replicate w val64) ⋆ R) m) :
    ((array (t := i32) a (List.replicate used v32) ⋆
      region (a + BitVec.ofNat 64 (4 * used)) (8 * w - 4 * used)) ⋆ R) m := by
  rw [array64_rep_eq_array (t := i32) val64 v32 2 (by decide) h1 a w hfit,
    show 2 * w = used + (2 * w - used) by omega, replicate_add_list,
    array_append (t := i32) a] at hm
  simp only [Ty.bytes, Ty.size, i32, List.length_replicate] at hm
  refine sep_mono (fun _ h => sep_mono_r (fun _ hr => ?_) h) hm
  simpa [show 8 * w - 4 * used = 4 * (2 * w - used) by omega] using
    i32_exact_to_reg (xs := List.replicate (2 * w - used) v32) (by simp; omega) hr

theorem array_i32_to_u64_exact {a : BitVec 64} {xs : List (BitVec 32)} {w : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} (hx : xs.length = 2 * w) (hfit : 8 * w ≤ 2 ^ 64)
    (hm : (array (t := i32) a xs ⋆ R) m) :
    ∃ ys : List (BitVec 64), ys.length = w ∧ (array64 a ys ⋆ R) m := by
  refine sep_ex_len (fun _ ha => ?_) hm
  have hr := i32_exact_to_reg (xs := xs) (by omega) ha
  rw [hx, show 4 * (2 * w) = 8 * w by omega] at hr
  exact reg_to_i64_exact hfit hr

theorem array64_rep_to_i32_exact {a : BitVec 64} {w : Nat} {val64 : BitVec 64} {v32 : BitVec 32}
    {R : Mem 64 → Prop} {m : Mem 64} (hfit : 8 * w ≤ 2 ^ 64)
    (h1 : bytes64 [val64] = bytesOf (t := i32) (List.replicate 2 v32))
    (hm : (array64 a (List.replicate w val64) ⋆ R) m) :
    (array (t := i32) a (List.replicate (2 * w) v32) ⋆ R) m := by
  rwa [array64_rep_eq_array (t := i32) val64 v32 2 (by decide) h1 a w hfit] at hm

/-! ## 3. Pure Header-Word Transitions & Public `Spec` Definitions (`12` Functions) -/

@[reducible] def EnvSpec (Γ : Env) (nm : String) {as rs : List Ty} (sp : Spec as rs) : Prop :=
  ∀ a m Q X, sp a m Q X → Γ nm as rs a m Q X

def m7PtrsW0 (hdr : BitVec 64) (mx : Nat) (w0 : List (BitVec 64)) : List (BitVec 64) :=
  let pV := hdr + BitVec.ofNat 64 1152
  let pMk := pV + BitVec.ofNat 64 (valsBytes mx)
  let pPh := pMk + BitVec.ofNat 64 (markBytes mx)
  let pPT := pPh + BitVec.ofNat 64 (markBytes mx)
  let pPB := pPT + BitVec.ofNat 64 (markBytes mx)
  let pFl := pPB + BitVec.ofNat 64 (markBytes mx)
  let pLv := pFl + BitVec.ofNat 64 (u32FullBytes mx)
  let pRs := pLv + BitVec.ofNat 64 (u32FullBytes mx)
  let pTr := pRs + BitVec.ofNat 64 (u32FullBytes mx)
  let pTP := pTr + BitVec.ofNat 64 (u32FullBytes mx)
  let pTm := pTP + BitVec.ofNat 64 (u32FullBytes mx)
  let pHp := pTm + BitVec.ofNat 64 (u32FullBytes mx)
  let pPs := pHp + BitVec.ofNat 64 (u32FullBytes mx)
  let pMC := pPs + BitVec.ofNat 64 (u32FullBytes mx)
  let pSS := pMC + BitVec.ofNat 64 (u32FullBytes mx)
  let pQP := pSS + BitVec.ofNat 64 (u32FullBytes mx)
  let pQN := pQP + BitVec.ofNat 64 (u32FullBytes mx)
  let pQS := pQN + BitVec.ofNat 64 (u32FullBytes mx)
  let pFT := pQS + BitVec.ofNat 64 (u32FullBytes mx)
  let pFD := pFT + BitVec.ofNat 64 (u32FullBytes mx)
  let pWv := pFD + BitVec.ofNat 64 (u32FullBytes mx)
  let pSc := pWv + BitVec.ofNat 64 (16 * mx)
  let pMS := pSc + BitVec.ofNat 64 (8 * mx)
  let pGU := pMS + BitVec.ofNat 64 (8 * fullMinDepthOf mx)
  let pLL := pGU + BitVec.ofNat 64 256
  let pAr := pLL + BitVec.ofNat 64 64
  ((((((((((((((w0.set 4 pV).set 5 pMk).set 6 pLv).set 7 pRs).set 8 pTr).set 9 pWv).set 10
    pAr).set 13 pTm).set 21 pHp).set 22 pPs).set 23 pSc).set 24 pPh).set 25 pMS).set 26
    pMC).set 29 (BitVec.ofNat 64 (fullMinDepthOf mx))

def m7PtrsW1 (hdr : BitVec 64) (mx : Nat) (w1 : List (BitVec 64)) : List (BitVec 64) :=
  let b := hdr + BitVec.ofNat 64 (1152 + valsBytes mx)
  let pMk := b
  let pPh := pMk + BitVec.ofNat 64 (markBytes mx)
  let pPT := pPh + BitVec.ofNat 64 (markBytes mx)
  let pPB := pPT + BitVec.ofNat 64 (markBytes mx)
  let pFl := pPB + BitVec.ofNat 64 (markBytes mx)
  let pTP := pFl + 4#64 * BitVec.ofNat 64 (u32FullBytes mx)
  let pSS := pTP + 5#64 * BitVec.ofNat 64 (u32FullBytes mx)
  let pQP := pSS + BitVec.ofNat 64 (u32FullBytes mx)
  let pQN := pQP + BitVec.ofNat 64 (u32FullBytes mx)
  let pQS := pQN + BitVec.ofNat 64 (u32FullBytes mx)
  let pMS := pQS + 3#64 * BitVec.ofNat 64 (u32FullBytes mx) + BitVec.ofNat 64 (24 * mx)
  let pGU := pMS + BitVec.ofNat 64 (8 * fullMinDepthOf mx)
  (((((((w1.set 6 pTP).set 7 pQP).set 8 pQN).set 9 pQS).set 10 pPT).set 11 pPB).set 13 pSS).set
    15 pGU

def m7PtrsW2 (hdr : BitVec 64) (mx : Nat) (w2 : List (BitVec 64)) : List (BitVec 64) :=
  let pFl := hdr + BitVec.ofNat 64 (1152 + valsBytes mx + 4 * markBytes mx)
  let pFT := pFl + 13#64 * BitVec.ofNat 64 (u32FullBytes mx)
  let pFD := pFT + BitVec.ofNat 64 (u32FullBytes mx)
  ((w2.set 26 pFl).set 30 pFT).set 31 pFD

def m7PtrsW3 (hdr : BitVec 64) (mx : Nat) (w3 : List (BitVec 64)) : List (BitVec 64) :=
  let pGU := hdr + BitVec.ofNat 64 (1152 + valsBytes mx + 4 * markBytes mx +
    15 * u32FullBytes mx + 24 * mx + 8 * fullMinDepthOf mx)
  w3.set 8 (pGU + BitVec.ofNat 64 256)

def m7ArenasW0 (hdr : BitVec 64) (mx avail_dyn : Nat) (w0 : List (BitVec 64)) :
    List (BitVec 64) :=
  let pAr := (m7PtrsW0 hdr mx w0)[10]!
  let ap := fullInitAp avail_dyn
  let wp := fullInitWp avail_dyn
  let pWs := pAr + BitVec.ofNat 64 (8 * ap)
  ((((m7PtrsW0 hdr mx w0).set 0 (BitVec.ofNat 64 (2 * ap))).set 1
    (BitVec.ofNat 64 (2 * wp))).set 11 pWs).set 12 (pWs + BitVec.ofNat 64 (8 * wp))

def m7ArenasW1 (hdr : BitVec 64) (mx avail_dyn del_cap ext_cap scr_cap : Nat)
    (w1 : List (BitVec 64)) : List (BitVec 64) :=
  let pAr := hdr + BitVec.ofNat 64 (m7FixedBytes mx)
  let ap := fullInitAp avail_dyn
  let rp := fullInitRp avail_dyn
  let wp := fullInitWp avail_dyn
  let pDl := pAr + BitVec.ofNat 64 (8 * ap + 8 * wp)
  let pRr := pDl + BitVec.ofNat 64 (12 * del_cap)
  let pTr := pRr + BitVec.ofNat 64 (8 * rp + 4 * ext_cap + 4 * scr_cap)
  (((m7PtrsW1 hdr mx w1).set 12 pTr).set 14 pRr).set 16 (BitVec.ofNat 64 (2 * rp))

def m7ArenasW2 (hdr : BitVec 64) (mx avail_dyn del_cap ext_cap scr_cap : Nat)
    (w2 : List (BitVec 64)) : List (BitVec 64) :=
  let pAr := hdr + BitVec.ofNat 64 (m7FixedBytes mx)
  let ap := fullInitAp avail_dyn
  let rp := fullInitRp avail_dyn
  let wp := fullInitWp avail_dyn
  let pTr := pAr + BitVec.ofNat 64 (8 * ap + 8 * wp + 12 * del_cap + 8 * rp + 4 * ext_cap +
    4 * scr_cap)
  ((((((m7PtrsW2 hdr mx w2).set 27 (pTr + BitVec.ofNat 64 (56 * mx))).set 28
    (pTr + BitVec.ofNat 64 (40 * mx))).set 29 (pTr + BitVec.ofNat 64 (48 * mx))).set 32
    (pTr + BitVec.ofNat 64 (8 * mx))).set 33 (pTr + BitVec.ofNat 64 (16 * mx))).set 34
    (pTr + BitVec.ofNat 64 (24 * mx))

def m7ArenasW3 (hdr : BitVec 64) (mx avail_dyn del_cap ext_cap scr_cap : Nat)
    (w3 : List (BitVec 64)) : List (BitVec 64) :=
  let pAr := hdr + BitVec.ofNat 64 (m7FixedBytes mx)
  let ap := fullInitAp avail_dyn
  let rp := fullInitRp avail_dyn
  let wp := fullInitWp avail_dyn
  let pEx := pAr + BitVec.ofNat 64 (8 * ap + 8 * wp + 12 * del_cap + 8 * rp)
  let pSc := pEx + BitVec.ofNat 64 (4 * ext_cap)
  let pTr := pSc + BitVec.ofNat 64 (4 * scr_cap)
  (((((m7PtrsW3 hdr mx w3).set 0 (pTr + BitVec.ofNat 64 (32 * mx))).set 1
    (pTr + BitVec.ofNat 64 (40 * mx))).set 2 (pTr + BitVec.ofNat 64 (48 * mx))).set 3 pEx).set 6
    pSc

def m7HdrW0 (mv : Nat) (fuel : BitVec 64) (w0 : List (BitVec 64)) : List (BitVec 64) :=
  (((((((((((((((w0.set 2 0#64).set 3 1#64).set 14 0#64).set 15 0#64).set 16 0#64).set 17
    fuel).set 18 0xFFFFFFFF#64).set 19 0#64).set 20 0#64).set 27 (BitVec.ofNat 64 mv)).set 28
    (1#64 <<< 28)).set 30 0#64).set 31 0#64).set 32 1024#64).set 33 1048576#64).set 34 1024#64

def m7HdrW1 (w1 : List (BitVec 64)) : List (BitVec 64) :=
  ((((((((((((((((((((((w1.set 0 1#64).set 1 1#64).set 2 0#64).set 3 0#64).set 4 0#64).set 5
    0#64).set 18 0#64).set 19 0#64).set 20 0#64).set 21 0xFFFFFFFF#64).set 22 0#64).set 23
    0#64).set 24 0#64).set 25 0#64).set 26 0#64).set 27 0#64).set 28 0#64).set 29 0#64).set 30
    0#64).set 31 0#64).set 32 0#64).set 33 1000#64).set 34 0#64

def m7HdrW2 (mv mx : Nat) (w2 : List (BitVec 64)) : List (BitVec 64) :=
  let qf := if mv == 0 then 0xFFFFFFFF#64 else 0#64
  let ql := if mv == 0 then 0xFFFFFFFF#64 else BitVec.ofNat 64 (mv - 1)
  (((((((((((((((((((((((((w2.set 0 0#64).set 1 0#64).set 2 qf).set 3 ql).set 4 ql).set 5
    (BitVec.ofNat 64 mv)).set 6 (BitVec.ofNat 64 mv)).set 7 0#64).set 8 0#64).set 9
    1000#64).set 10 0#64).set 11 1000#64).set 12 0#64).set 13 2#64).set 14 6#64).set 15
    0#64).set 16 1#64).set 17 0#64).set 18 (1#64 <<< 24)).set 19 0#64).set 20
    (1#64 <<< 24)).set 21 0#64).set 22 (BitVec.ofNat 64 mx)).set 23 (BitVec.ofNat 64 mv)).set
    24 (BitVec.ofNat 64 (mx - mv))).set 25 (BitVec.ofNat 64 mv)

def m7HdrW3 (mv : Nat) (w3 : List (BitVec 64)) : List (BitVec 64) :=
  let rng := 0x9E3779B97F4A7C15#64 ^^^ BitVec.ofNat 64 (mv + 1)
  ((((((((((((((((((((((((((w3.set 5 0#64).set 9 rng).set 10 100#64).set 11 0#64).set 12
    0#64).set 13 2000#64).set 14 0#64).set 15 5000#64).set 16 0#64).set 17 0#64).set 18
    0#64).set 19 0#64).set 20 0#64).set 21 0#64).set 22 0#64).set 23 0#64).set 24 0#64).set 25
    0#64).set 26 0#64).set 27 0#64).set 28 0#64).set 29 0#64).set 30 0#64).set 31 0#64).set 32
    0#64).set 33 0#64).set 34 0#64

def m7FillU64Spec : Spec [i64, i64, i64] [] :=
  fun (dst, n, val, _) m Q _ =>
    ∃ (xs : List (BitVec 64)) (R : Mem 64 → Prop),
      n.toNat = xs.length ∧ dst.toNat + 8 * xs.length ≤ 2 ^ 64 ∧ (array64 dst xs ⋆ R) m ∧
      (∀ m', (array64 dst (List.replicate n.toNat val) ⋆ R) m' → Q () m')

def m7FixedBytesSpec : Spec [i64] [i64] := fun (mx, _) m Q _ =>
  mx.toNat < 2 * dimacsBound ∧ Q (BitVec.ofNat 64 (m7FixedBytes mx.toNat), ()) m

def m7TransBytesSpec : Spec [i64] [i64] := fun (mx, _) m Q _ =>
  mx.toNat < 2 * dimacsBound ∧ Q (BitVec.ofNat 64 (m7TransBytes mx.toNat), ()) m

def m7CalcExtCapSpec : Spec [i64] [i64] :=
  fun (rem, _) m Q _ => Q (BitVec.ofNat 64 (m7CalcExtCap rem.toNat), ()) m

def m7CalcScrCapSpec : Spec [i64] [i64] :=
  fun (rem, _) m Q _ => Q (BitVec.ofNat 64 (m7CalcScrCap rem.toNat), ()) m

def m7CalcMaxVSpec : Spec [i64, i64, i64, i64] [i64] :=
  fun (avail, mv, nc, f0, _) m Q _ =>
    mv.toNat < dimacsBound ∧ nc.toNat < dimacsBound ∧ f0.toNat ≤ avail.toNat ∧
    Q (BitVec.ofNat 64 (m7CalcMaxV avail.toNat mv.toNat nc.toNat f0.toNat), ()) m

def m7InitPtrsSpec : Spec [i64, i64, i64] [] :=
  fun (h, hdr_addr, mx, _) m Q _ =>
    h = hdr_addr ∧ mx.toNat < 2 * dimacsBound ∧
    hdr_addr.toNat + m7FixedBytes mx.toNat < 2 ^ 64 ∧
    ∃ w0 w1 w2 w3 R, (hdrTail4 hdr_addr w0 w1 w2 w3 ⋆ R) m ∧
      (∀ m', (hdrTail4 hdr_addr (m7PtrsW0 hdr_addr mx.toNat w0) (m7PtrsW1 hdr_addr mx.toNat w1)
        (m7PtrsW2 hdr_addr mx.toNat w2) (m7PtrsW3 hdr_addr mx.toNat w3) ⋆ R) m' → Q () m')

def m7InitHdrSpec : Spec [i64, i64, i64, i64] [] :=
  fun (h, mv, mx, fuel, _) m Q _ =>
    mv.toNat ≤ mx.toNat ∧ mx.toNat < 2 * dimacsBound ∧
    ∃ w0 w1 w2 w3 R, (hdrTail4 h w0 w1 w2 w3 ⋆ R) m ∧
      (∀ m', (hdrTail4 h (m7HdrW0 mv.toNat fuel w0) (m7HdrW1 w1) (m7HdrW2 mv.toNat mx.toNat w2)
        (m7HdrW3 mv.toNat w3) ⋆ R) m' → Q () m')

def m7InitArenasSpec : Spec [i64, i64, i64, i64] [] :=
  fun (h, hdr_addr, mx, avail_dyn, _) m Q _ =>
    h = hdr_addr ∧ mx.toNat < 2 * dimacsBound ∧
    hdr_addr.toNat + m7FixedBytes mx.toNat < 2 ^ 64 ∧
    ∃ del_cap ext_cap scr_cap w0 w1 w2 w3 R,
      del_cap < dimacsBound ∧ ext_cap < dimacsBound ∧ scr_cap < dimacsBound ∧
      w1[17]? = some (BitVec.ofNat 64 del_cap) ∧
      w3[4]? = some (BitVec.ofNat 64 ext_cap) ∧
      w3[7]? = some (BitVec.ofNat 64 scr_cap) ∧
      (hdrTail4 hdr_addr w0 w1 w2 w3 ⋆ R) m ∧
      (∀ m', (hdrTail4 hdr_addr
        (m7ArenasW0 hdr_addr mx.toNat avail_dyn.toNat w0)
        (m7ArenasW1 hdr_addr mx.toNat avail_dyn.toNat del_cap ext_cap scr_cap w1)
        (m7ArenasW2 hdr_addr mx.toNat avail_dyn.toNat del_cap ext_cap scr_cap w2)
        (m7ArenasW3 hdr_addr mx.toNat avail_dyn.toNat del_cap ext_cap scr_cap w3) ⋆ R) m' →
        Q () m')

def FullHdrScalarsEq (a b : FullState) : Prop :=
  a.core.d_cur = b.core.d_cur ∧ a.core.d_val = b.core.d_val ∧ a.core.cur_vars = b.core.cur_vars ∧
  a.core.unassigned = b.core.unassigned ∧ a.core.arena_len = b.core.arena_len ∧
  a.core.wlen = b.core.wlen ∧ a.core.trail_end = b.core.trail_end ∧
  a.core.propagated = b.core.propagated ∧ a.core.cur_level = b.core.cur_level ∧
  a.core.fuel = b.core.fuel ∧ a.core.confl_ref = b.core.confl_ref ∧
  a.core.tmp_cnt = b.core.tmp_cnt ∧ a.core.tmp_len = b.core.tmp_len ∧
  a.core.min_clr_len = b.core.min_clr_len ∧ a.core.min_clr_full = b.core.min_clr_full ∧
  a.core.oom = b.core.oom ∧ a.core.inconsistent = b.core.inconsistent ∧
  a.core.num_irred = b.core.num_irred ∧ a.core.num_redundant = b.core.num_redundant ∧
  a.core.num_binary = b.core.num_binary ∧ a.core.unflushed = b.core.unflushed ∧
  a.core.probing = b.core.probing ∧ a.core.dense_mode = b.core.dense_mode ∧
  a.scratch.extend_len = b.scratch.extend_len ∧
  a.scratch.probe_limit = b.scratch.probe_limit ∧ a.scratch.elim_limit = b.scratch.elim_limit

theorem fullHdrScalarsEq_eq (a b : FullState) :
    FullHdrScalarsEq a b =
      (a.core.d_cur = b.core.d_cur ∧ a.core.d_val = b.core.d_val ∧
      a.core.cur_vars = b.core.cur_vars ∧ a.core.unassigned = b.core.unassigned ∧
      a.core.arena_len = b.core.arena_len ∧ a.core.wlen = b.core.wlen ∧
      a.core.trail_end = b.core.trail_end ∧ a.core.propagated = b.core.propagated ∧
      a.core.cur_level = b.core.cur_level ∧ a.core.fuel = b.core.fuel ∧
      a.core.confl_ref = b.core.confl_ref ∧ a.core.tmp_cnt = b.core.tmp_cnt ∧
      a.core.tmp_len = b.core.tmp_len ∧ a.core.min_clr_len = b.core.min_clr_len ∧
      a.core.min_clr_full = b.core.min_clr_full ∧ a.core.oom = b.core.oom ∧
      a.core.inconsistent = b.core.inconsistent ∧ a.core.num_irred = b.core.num_irred ∧
      a.core.num_redundant = b.core.num_redundant ∧ a.core.num_binary = b.core.num_binary ∧
      a.core.unflushed = b.core.unflushed ∧ a.core.probing = b.core.probing ∧
      a.core.dense_mode = b.core.dense_mode ∧ a.scratch.extend_len = b.scratch.extend_len ∧
      a.scratch.probe_limit = b.scratch.probe_limit ∧
      a.scratch.elim_limit = b.scratch.elim_limit) := by
  rfl

theorem fullHdrScalarsEq_trans {a b c : FullState}
    (h1 : FullHdrScalarsEq a b) (h2 : FullHdrScalarsEq b c) : FullHdrScalarsEq a c := by
  simp only [FullHdrScalarsEq] at h1 h2 ⊢; simp_all

def m7ZeroTables1Spec : Spec [i64] [] :=
  fun (hdr, _) m Q _ =>
    ∃ (c : MemShrinkCfg) (s : FullState) (R : Mem 64 → Prop),
      hdr = c.hdr ∧ MemShrinkLengthsOk c s ∧ (MemShrinkMem c s ⋆ R) m ∧
      (∀ s' m',
        FullHdrScalarsEq s' s →
        s'.core.vals = List.replicate (2 * c.max_vars) 0#8 →
        s'.core.lit_mark = List.replicate (2 * c.max_vars) 0#8 →
        s'.core.wvec = List.replicate (4 * c.max_vars) 0#32 →
        s'.core.min_stk = List.replicate (2 * c.minDepth) 0#32 →
        s'.scratch.glue_used = List.replicate 64 0#32 →
        s'.scratch.last_learned = List.replicate 16 0xFFFFFFFF#32 →
        MemShrinkLengthsOk c s' →
        (MemShrinkMem c s' ⋆ R) m' → Q () m')

def m7ZeroTables2Spec : Spec [i64] [] :=
  fun (hdr, _) m Q _ =>
    ∃ (c : MemShrinkCfg) (s : FullState) (R : Mem 64 → Prop),
      hdr = c.hdr ∧ MemShrinkLengthsOk c s ∧ (MemShrinkMem c s ⋆ R) m ∧
      (∀ s' m',
        FullHdrScalarsEq s' s →
        s'.core.vals = s.core.vals → s'.core.lit_mark = s.core.lit_mark →
        s'.core.wvec = s.core.wvec → s'.core.min_stk = s.core.min_stk →
        s'.scratch.glue_used = s.scratch.glue_used →
        s'.scratch.last_learned = s.scratch.last_learned →
        s'.core.mrk = List.replicate c.max_vars 0#8 →
        MemShrinkLengthsOk c s' →
        (MemShrinkMem c s' ⋆ R) m' → Q () m')

def m7InitStateSpec : Spec [i64, i64, i64, i64, i64] [.bool] :=
  fun (cnf_ptr, cend, hdr_addr, avail, fuel, _) m Q _ =>
    ∃ (cnfBytes : List UInt8) (R : Mem 64 → Prop),
      cend = cnf_ptr + BitVec.ofNat 64 cnfBytes.length ∧
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
      hdr_addr.toNat + avail.toNat < 2 ^ 64 ∧
      1152 ≤ avail.toNat ∧
      (bytes cnf_ptr cnfBytes ⋆ region hdr_addr avail.toNat ⋆ R) m ∧
      (∀ m', (bytes cnf_ptr cnfBytes ⋆ region hdr_addr avail.toNat ⋆ R) m' →
        (∀ mv nc rest, parseHeader cnfBytes = some (mv, nc, rest) →
          avail.toNat < m7FixedBytes mv + m7TransBytes mv + nc * 40 + 136) →
        Q (false, ()) m') ∧
      (∀ (c : MemShrinkCfg) (s : FullState) (j : Nat) (rest : List UInt8) (m' : Mem 64),
        c.hdr = hdr_addr → c.avail = avail.toNat →
        parseHeader cnfBytes = some (c.mv, c.nc, rest) →
        j ≤ cnfBytes.length → List.drop j cnfBytes = rest →
        MemShrinkSparseInv c s →
        s.core.cur_vars = c.mv → s.core.unassigned = c.mv →
        s.core.d_cur = cnf_ptr + BitVec.ofNat 64 j → s.core.d_val = BitVec.ofNat 64 c.nc →
        s.core.arena_len = 0 → s.core.wlen = 1 →
        s.core.trail_end = 0 → s.core.propagated = 0 → s.core.cur_level = 0 →
        s.core.fuel = fuel → s.core.confl_ref = 0xFFFFFFFF#64 →
        s.core.tmp_cnt = 0 → s.core.tmp_len = 0 → s.core.min_clr_len = 0 →
        s.core.min_clr_full = 0#64 → s.core.oom = 0#64 →
        s.core.inconsistent = 0#64 →
        s.core.num_irred = 0#64 → s.core.num_redundant = 0#64 →
        s.core.num_binary = 0#64 →
        s.core.unflushed = 0#64 → s.core.probing = 0#64 → s.core.dense_mode = 0#64 →
        s.core.vals = List.replicate (2 * c.max_vars) 0#8 →
        s.core.wvec = List.replicate (4 * c.max_vars) 0#32 →
        s.core.mrk = List.replicate c.max_vars 0#8 →
        s.core.lit_mark = List.replicate (2 * c.max_vars) 0#8 →
        s.scratch.extend_len = 0 →
        s.scratch.probe_limit = 2000#64 → s.scratch.elim_limit = 5000#64 →
        (bytes cnf_ptr cnfBytes ⋆ MemShrinkMem c s ⋆ R) m' → Q (true, ()) m')

/-! ## 4. Sizing, 4x-Unrolled `u64` Fill & Header Init WP Proofs (`9` Functions) -/

private theorem bv64_mdepth {mx : Nat} (hmx : mx < 2 * dimacsBound) :
    (if (BitVec.ofNat 64 mx + 1#64).toNat < 1000 then BitVec.ofNat 64 mx + 1#64 else 1000#64) =
      BitVec.ofNat 64 (fullMinDepthOf mx) := by
  unfold dimacsBound fullMinDepthOf at *
  have h1 : (BitVec.ofNat 64 mx + 1#64).toNat = mx + 1 := by
    simp [BitVec.toNat_add]; omega
  rw [h1]; split
  · exact BitVec.eq_of_toNat_eq (by simp [BitVec.toNat_add])
  · simp

private theorem bv64_self {x : BitVec 64} : BitVec.ofNat 64 x.toNat = x :=
  BitVec.eq_of_toNat_eq (by simp)

private theorem bv64_shl1_s {n : Nat} :
    BitVec.ofNat 64 n <<< (BitVec.signExtend 64 1#32).toNat = BitVec.ofNat 64 (2 * n) := by
  apply BitVec.eq_of_toNat_eq
  rw [show (BitVec.signExtend 64 1#32).toNat = 1 by decide, BitVec.toNat_shiftLeft,
    BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.pow_one, Nat.mod_mul_mod, Nat.mul_comm]; simp

private theorem bv64_shl3_s {n : Nat} :
    BitVec.ofNat 64 n <<< (BitVec.signExtend 64 3#32).toNat = BitVec.ofNat 64 (8 * n) := by
  rw [show (BitVec.signExtend 64 3#32).toNat = 3 by decide]
  apply BitVec.eq_of_toNat_eq; simp [Nat.mul_comm]

private theorem bv64_nlits_shl3 {mx : Nat} (_hmx : mx < 2 * dimacsBound) :
    (BitVec.ofNat 64 mx <<< (BitVec.signExtend 64 1#32).toNat) <<<
      (BitVec.signExtend 64 3#32).toNat = BitVec.ofNat 64 (16 * mx) := by
  rw [bv64_shl1_s, bv64_shl3_s, show 8 * (2 * mx) = 16 * mx by omega]

private theorem bv64_shr3_s {n : Nat} (h : n < 2 ^ 64) :
    BitVec.ofNat 64 n >>> (BitVec.signExtend 64 3#32).toNat = BitVec.ofNat 64 (n / 8) := by
  rw [show (BitVec.signExtend 64 3#32).toNat = (BitVec.signExtend 64 (3 : BitVec 32)).toNat % 64
    by decide]; exact fp_shr_sext3 (n := n) h

private theorem bv64_shr4_s {n : Nat} (h : n < 2 ^ 64) :
    BitVec.ofNat 64 n >>> (BitVec.signExtend 64 4#32).toNat = BitVec.ofNat 64 (n / 16) := by
  rw [show (BitVec.signExtend 64 4#32).toNat = (BitVec.signExtend 64 (4 : BitVec 32)).toNat % 64
    by decide]; exact fp_shr_sext4 (n := n) h

private theorem bv64_shr5_s {n : Nat} (h : n < 2 ^ 64) :
    BitVec.ofNat 64 n >>> (BitVec.signExtend 64 5#32).toNat = BitVec.ofNat 64 (n / 32) := by
  rw [show (BitVec.signExtend 64 5#32).toNat = (BitVec.signExtend 64 (5 : BitVec 32)).toNat % 64
    by decide]; exact fp_shr_sext5 (n := n) h

private theorem bv64_shl2_s {n : Nat} (h : 4 * n < 2 ^ 64) :
    BitVec.ofNat 64 n <<< (BitVec.signExtend 64 2#32).toNat = BitVec.ofNat 64 (4 * n) := by
  rw [show (BitVec.signExtend 64 2#32).toNat = (BitVec.signExtend 64 (2 : BitVec 32)).toNat % 64
    by decide]; exact bv64_shl2_nat h

private theorem bv64_vb_s {mx : Nat} (hmx : mx < 2 * dimacsBound) :
    (BitVec.ofNat 64 mx <<< (BitVec.signExtend 64 1#32).toNat + 7#64) &&& ~~~7#64 =
      BitVec.ofNat 64 (valsBytes mx) := by
  rw [show (BitVec.signExtend 64 1#32).toNat = (BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64
    by decide]; exact fp_vb_eq hmx

private theorem bv64_mb_s {mx : Nat} (hmx : mx < 2 * dimacsBound) :
    (BitVec.ofNat 64 mx + 7#64) &&& ~~~7#64 = BitVec.ofNat 64 (markBytes mx) := fp_mb_eq hmx

private theorem bv64_ub_s {mx : Nat} (hmx : mx < 2 * dimacsBound) :
    ((BitVec.ofNat 64 mx + 1#64) <<< (BitVec.signExtend 64 2#32).toNat + 7#64) &&& ~~~7#64 =
      BitVec.ofNat 64 (u32FullBytes mx) := by
  rw [show (BitVec.signExtend 64 2#32).toNat = (BitVec.signExtend 64 (2 : BitVec 32)).toNat % 64
    by decide]; exact fp_ub_eq hmx

private theorem bv64_vb_nat {mx : Nat} (hmx : mx < 2 * dimacsBound) :
    (BitVec.ofNat 64 mx <<< 1 + 7#64) &&& ~~~7#64 = BitVec.ofNat 64 (valsBytes mx) := by
  rw [show (1 : Nat) = (BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64 by decide]
  exact fp_vb_eq hmx

private theorem bv64_ub_nat {mx : Nat} (hmx : mx < 2 * dimacsBound) :
    ((BitVec.ofNat 64 mx + 1#64) <<< 2 + 7#64) &&& ~~~7#64 = BitVec.ofNat 64 (u32FullBytes mx) := by
  rw [show (2 : Nat) = (BitVec.signExtend 64 (2 : BitVec 32)).toNat % 64 by decide]
  exact fp_ub_eq hmx

private theorem bv64_nlits_shl3_nat {mx : Nat} (_hmx : mx < 2 * dimacsBound) :
    BitVec.ofNat 64 mx <<< 1 <<< ((BitVec.signExtend 64 (3 : BitVec 32)).toNat % 64) =
      BitVec.ofNat 64 (16 * mx) := by
  rw [show (1 : Nat) = (BitVec.signExtend 64 1#32).toNat by decide, bv64_shl1_s, fp_shl_sext3,
    show 8 * (2 * mx) = 16 * mx by omega]

private theorem fill_tail_step_inv {xs cur : List (BitVec 64)} {i : Nat} {val : BitVec 64}
    (hlen : cur.length = xs.length) (hlt : i < xs.length)
    (hpre : ∀ k < i, cur[k]? = some val) : ∀ k < i + 1, (cur.set i val)[k]? = some val := by
  intro k hk
  rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with hlt' | rfl
  · rw [List.getElem?_set_ne (by omega)]; exact hpre k hlt'
  · rw [List.getElem?_set_self (by omega)]

private theorem fill_unroll4_inv {xs cur : List (BitVec 64)} {i : Nat} {val : BitVec 64}
    (hlen : cur.length = xs.length) (hle : i + 4 ≤ xs.length)
    (hpre : ∀ k < i, cur[k]? = some val) :
    ∀ k < i + 4,
      ((((cur.set i val).set (i + 1) val).set (i + 2) val).set (i + 3) val)[k]? = some val := by
  have h1 : (cur.set i val).length = xs.length := by simp [hlen]
  have hp1 := fill_tail_step_inv hlen (by omega) hpre
  have h2 : ((cur.set i val).set (i + 1) val).length = xs.length := by simp [h1]
  have hp2 := fill_tail_step_inv h1 (by omega) hp1
  have h3 : (((cur.set i val).set (i + 1) val).set (i + 2) val).length = xs.length := by simp [h2]
  exact fill_tail_step_inv h3 (by omega) (fill_tail_step_inv h2 (by omega) hp2)

private theorem fold_bv_i8_sum (a : BitVec 64) (k : Nat) :
    a + BitVec.ofNat 64 k * 8#64 = a + BitVec.ofNat 64 (8 * k) := by
  rw [fp_mul_nat, show k * 8 = 8 * k by omega]

private theorem fold_bv_i8_sum1 (a : BitVec 64) (i k : Nat) :
    a + (BitVec.ofNat 64 i + BitVec.ofNat 64 k) * 8#64 =
      a + BitVec.ofNat 64 (8 * (i + k)) := by
  rw [← BitVec.ofNat_add, fp_mul_nat, show (i + k) * 8 = 8 * (i + k) by omega]

theorem full_fill_u64_m7_wp (Γ : Env) :
    ∀ a m Q X, m7FillU64Spec a m Q X → Func.wp Γ full_fill_u64_m7_body a m Q X := by
  rintro ⟨dst, n, val, _⟩ m Q X ⟨xs, R, hn, hfit, hm, hpost⟩
  unfold full_fill_u64_m7_body; dsimp only [Func.wp]
  have hnl : xs.length ≤ 2 ^ 61 := by omega
  have hn_bv : n = BitVec.ofNat 64 xs.length := by
    apply BitVec.eq_of_toNat_eq; simp [hn]; omega
  subst hn_bv
  c0_hsteps_nogrp
  refine wp_while_state1 (α := Nat × List (BitVec 64)) (proj := fun st => BitVec.ofNat 64 st.1)
    (μ := fun st => xs.length - st.1)
    (Inv := fun st m' => st.1 ≤ xs.length ∧ st.2.length = xs.length ∧
      (∀ k < st.1, st.2[k]? = some val) ∧ (array64 dst st.2 ⋆ R) m')
    ?_ ?_
  · intro J hJ; exact hJ (0, xs) m ⟨by omega, rfl, fun _ hk => by omega, hm⟩
  · rintro J1 ⟨i, cur⟩ m1 ⟨hi, hcl, hpre, hm1⟩ ih1
    dsimp only at hi hcl hpre hm1
    dsimp only [Blocks.get]; c0_hsplit
    · rw [show BitVec.toNat 4 = 4 from by decide] at hc
      have hle : i + 4 ≤ xs.length := by omega
      c0_hsteps
      have hi0 : (BitVec.ofNat 64 i).toNat = i := by simp; omega
      have hi1 : (BitVec.ofNat 64 i + 1).toNat = i + 1 := by simp [BitVec.toNat_add]; omega
      have hi2 : (BitVec.ofNat 64 i + 2).toNat = i + 2 := by simp [BitVec.toNat_add]; omega
      have hi3 : (BitVec.ofNat 64 i + 3).toNat = i + 3 := by simp [BitVec.toNat_add]; omega
      rw [hi0, hi1, hi2, hi3] at hm
      have hst : BitVec.ofNat 64 i + 4 = BitVec.ofNat 64 (i + 4) := by
        rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_add]
      rw [hst]
      exact ih1 (i + 4, _) m (by omega) ⟨hle, by simp [hcl], fill_unroll4_inv hcl hle hpre, hm⟩
    · rw [show BitVec.toNat 4 = 4 from by decide] at hc
      have hgt : xs.length < i + 4 := by omega
      c0_hsteps_nogrp
      refine wp_while_state1 (α := Nat × List (BitVec 64))
        (proj := fun st => BitVec.ofNat 64 st.1) (μ := fun st => xs.length - st.1)
        (Inv := fun st m' => st.1 ≤ xs.length ∧ st.2.length = xs.length ∧
          (∀ k < st.1, st.2[k]? = some val) ∧ (array64 dst st.2 ⋆ R) m')
        (fun J2 hJ2 => hJ2 (i, cur) m1 ⟨hi, hcl, hpre, hm1⟩) ?_
      rintro J2 ⟨j, cur2⟩ m2 ⟨hj, hcl2, hpre2, hm2⟩ ih2
      dsimp only at hj hcl2 hpre2 hm2
      dsimp only [Blocks.get]; c0_hsplit
      · have hjlt : j < xs.length := by omega
        c0_hsteps
        rw [show (BitVec.ofNat 64 j).toNat = j from by simp; omega] at hm
        have hst : BitVec.ofNat 64 j + 1 = BitVec.ofNat 64 (j + 1) := by
          rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
        rw [hst]
        exact ih2 (j + 1, cur2.set j val) m (by omega)
          ⟨hjlt, by simp [hcl2], fill_tail_step_inv hcl2 hjlt hpre2, hm⟩
      · have hj_eq : j = xs.length := by omega
        c0_hsteps
        apply hpost
        rw [list_eq_replicate_of_forall hcl2 (hj_eq ▸ hpre2)] at hm2
        simpa [hn] using hm2

theorem full_fixed_bytes_m7_wp (Γ : Env) :
    ∀ a m Q X, m7FixedBytesSpec a m Q X → Func.wp Γ full_fixed_bytes_m7_body a m Q X := by
  rintro ⟨mx, _⟩ m Q X ⟨hmx, hq⟩
  unfold full_fixed_bytes_m7_body; dsimp only [Func.wp]
  have hmx_nat : BitVec.ofNat 64 mx.toNat = mx := bv64_self
  c0_hsteps_nogrp
  refine wp_join_state1 (α := Unit)
    (proj := fun _ => BitVec.ofNat 64 (fullMinDepthOf mx.toNat)) (Inv := fun _ m' => m' = m) ?_ ?_
  · rintro J _ m' rfl
    c0_hsteps
    have hvb : mx <<< 1 + 7#64 &&& 18446744073709551608#64 =
        BitVec.ofNat 64 (valsBytes mx.toNat) := by
      rw [show (18446744073709551608#64 : BitVec 64) = ~~~7#64 from by decide]
      have h := bv64_vb_nat hmx; rw [hmx_nat] at h; exact h
    have hmb : mx + 7#64 &&& 18446744073709551608#64 = BitVec.ofNat 64 (markBytes mx.toNat) := by
      rw [show (18446744073709551608#64 : BitVec 64) = ~~~7#64 from by decide]
      have h := bv64_mb_s hmx; rw [hmx_nat] at h; exact h
    have hub : (mx + 1#64) <<< 2 + 7#64 &&& 18446744073709551608#64 =
        BitVec.ofNat 64 (u32FullBytes mx.toNat) := by
      rw [show (18446744073709551608#64 : BitVec 64) = ~~~7#64 from by decide]
      have h := bv64_ub_nat hmx; rw [hmx_nat] at h; exact h
    have h4 : BitVec.ofNat 64 (markBytes mx.toNat) <<< (2 : Nat) =
        BitVec.ofNat 64 (4 * markBytes mx.toNat) := by
      rw [show (2 : Nat) = (BitVec.signExtend 64 2#32).toNat by decide]
      exact bv64_shl2_s (by unfold markBytes dimacsBound at *; omega)
    have h15 : BitVec.ofNat 64 (u32FullBytes mx.toNat) * 15#64 =
        BitVec.ofNat 64 (15 * u32FullBytes mx.toNat) := by
      rw [fp_mul_nat, Nat.mul_comm]
    have h24 : mx <<< 1 <<< 3 + mx <<< 3 = BitVec.ofNat 64 (24 * mx.toNat) := by
      have h16 : mx <<< 1 <<< 3 = BitVec.ofNat 64 (16 * mx.toNat) := by
        rw [show (3 : Nat) = (BitVec.signExtend 64 (3 : BitVec 32)).toNat % 64 by decide]
        have h := bv64_nlits_shl3_nat hmx; rw [hmx_nat] at h; exact h
      have h8 : mx <<< (3 : Nat) = BitVec.ofNat 64 (8 * mx.toNat) := by
        rw [show (3 : Nat) = (BitVec.signExtend 64 3#32).toNat by decide]
        have h := bv64_shl3_s (n := mx.toNat); rw [hmx_nat] at h; exact h
      rw [h16, h8, ← BitVec.ofNat_add]; congr 1; omega
    have hmd : BitVec.ofNat 64 (fullMinDepthOf mx.toNat) <<< (3 : Nat) =
        BitVec.ofNat 64 (8 * fullMinDepthOf mx.toNat) := by
      rw [show (3 : Nat) = (BitVec.signExtend 64 3#32).toNat by decide]; exact bv64_shl3_s
    have hfin : (1152 : BitVec 64) + 320 + (mx <<< (1 : Nat) + 7 &&& ~~~7) +
        (mx + 7 &&& ~~~7) <<< (2 : Nat) +
        ((mx + 1) <<< (2 : Nat) + 7 &&& ~~~7) * 15 +
        mx <<< (1 : Nat) <<< (3 : Nat) + mx <<< (3 : Nat) +
        BitVec.ofNat 64 (fullMinDepthOf mx.toNat) <<< (3 : Nat) =
        BitVec.ofNat 64 (m7FixedBytes mx.toNat) := by
      rw [show (320 : BitVec 64) = 320#64 from rfl,
        show (7 : BitVec 64) = 7#64 from rfl,
        show (1 : BitVec 64) = 1#64 from rfl,
        show (15 : BitVec 64) = 15#64 from rfl,
        show (~~~7#64 : BitVec 64) = 18446744073709551608#64 from by decide,
        hvb, hmb, hub, h4, h15, BitVec.add_assoc _ (mx <<< 1 <<< 3) (mx <<< 3), h24,
        BitVec.add_assoc _ (BitVec.ofNat 64 (15 * u32FullBytes mx.toNat)), hmd,
        show (1152 : BitVec 64) + 320#64 = BitVec.ofNat 64 1472 from by decide]
      simp only [m7FixedBytes, ← BitVec.ofNat_add]
      congr 1; omega
    rw [hfin]; exact hq
  · intro J hJ; c0_hsplit
    · c0_hsteps
      rw [show BitVec.toNat 1000 = 1000 from by decide] at hc
      have hlt : mx.toNat + 1 < 1000 := by unfold dimacsBound at hmx; omega
      have heq : mx + 1 = BitVec.ofNat 64 (fullMinDepthOf mx.toNat) := by
        have hb := bv64_mdepth hmx
        have h1 : (BitVec.ofNat 64 mx.toNat + 1#64).toNat = mx.toNat + 1 := by
          simp [BitVec.toNat_add]; unfold dimacsBound at hmx; omega
        rw [h1, hmx_nat] at hb
        simpa [hlt] using hb
      rw [heq]; exact hJ () m rfl
    · c0_hsteps
      rw [show BitVec.toNat 1000 = 1000 from by decide] at hc
      have hge : 1000 ≤ mx.toNat + 1 := by unfold dimacsBound at hmx; omega
      have heq : (1000 : BitVec 64) = BitVec.ofNat 64 (fullMinDepthOf mx.toNat) := by
        have hb := bv64_mdepth hmx
        have h1 : (BitVec.ofNat 64 mx.toNat + 1#64).toNat = mx.toNat + 1 := by
          simp [BitVec.toNat_add]; unfold dimacsBound at hmx; omega
        rw [h1, hmx_nat] at hb
        simpa [show ¬(mx.toNat + 1 < 1000) by omega] using hb
      rw [heq]; exact hJ () m rfl

theorem full_trans_bytes_m7_wp (Γ : Env) :
    ∀ a m Q X, m7TransBytesSpec a m Q X → Func.wp Γ full_trans_bytes_m7_body a m Q X := by
  rintro ⟨mx, _⟩ m Q X ⟨hmx, hq⟩
  unfold full_trans_bytes_m7_body; dsimp only [Func.wp]
  have hmx_nat : BitVec.ofNat 64 mx.toNat = mx := bv64_self
  c0_hsteps
  have hvb : mx <<< 1 + 7#64 &&& 18446744073709551608#64 =
      BitVec.ofNat 64 (valsBytes mx.toNat) := by
    rw [show (18446744073709551608#64 : BitVec 64) = ~~~7#64 from by decide]
    have h := bv64_vb_nat hmx; rw [hmx_nat] at h; exact h
  have hsh3 : mx <<< (3 : Nat) = BitVec.ofNat 64 (8 * mx.toNat) := by
    rw [show (3 : Nat) = (BitVec.signExtend 64 3#32).toNat by decide]
    have h := bv64_shl3_s (n := mx.toNat); rw [hmx_nat] at h; exact h
  have hfin : mx <<< (3 : Nat) * 7 + (mx <<< (1 : Nat) + 7 &&& ~~~7) =
      BitVec.ofNat 64 (m7TransBytes mx.toNat) := by
    rw [show (7 : BitVec 64) = 7#64 from rfl,
      show (~~~7#64 : BitVec 64) = 18446744073709551608#64 from by decide,
      hvb, hsh3, show (7#64 : BitVec 64) = BitVec.ofNat 64 7 from rfl, fp_mul_nat,
      show 8 * mx.toNat * 7 = 56 * mx.toNat by omega, ← BitVec.ofNat_add]
    rfl
  rw [hfin]; exact hq

theorem full_calc_ext_cap_m7_wp (Γ : Env) :
    ∀ a m Q X, m7CalcExtCapSpec a m Q X → Func.wp Γ full_calc_ext_cap_m7_body a m Q X := by
  rintro ⟨rem, _⟩ m Q X hq
  dsimp only [m7CalcExtCapSpec] at hq
  unfold full_calc_ext_cap_m7_body; dsimp only [Func.wp]
  c0_hsteps_nogrp; c0_hsplit
  · c0_hsteps
    rw [show BitVec.toNat 8192 = 8192 from by decide] at hc
    have hz : m7CalcExtCap rem.toNat = 0 := by unfold m7CalcExtCap; simp [hc]
    simpa [hz] using hq
  · c0_hsteps_nogrp
    rw [show BitVec.toNat 8192 = 8192 from by decide] at hc
    have hge : 8192 ≤ rem.toNat := by omega
    have hdiv_lt : rem.toNat / 32 < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) rem.isLt
    have hc_sh : rem >>> 5 = BitVec.ofNat 64 (rem.toNat / 32) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, show (2 ^ 5 : Nat) = 32 by decide,
        BitVec.toNat_ofNat]
      exact (Nat.mod_eq_of_lt hdiv_lt).symm
    refine wp_join_state1 (α := Unit)
      (proj := fun _ => BitVec.ofNat 64 (min (rem.toNat / 32) 4194304))
      (Inv := fun _ m' => m' = m) ?_ ?_
    · rintro J _ m' hm'; subst m'
      c0_hsteps
      have hcap : BitVec.ofNat 64 (min (rem.toNat / 32) 4194304) &&& ~~~1 =
          BitVec.ofNat 64 (m7CalcExtCap rem.toNat) := by
        rw [fp_and_not1,
          show (BitVec.ofNat 64 (min (rem.toNat / 32) 4194304)).toNat =
          min (rem.toNat / 32) 4194304 by simp; omega]
        unfold m7CalcExtCap; simp [show ¬rem.toNat < 8192 by omega]
      rw [hcap]; exact hq
    · intro J hJ; c0_hsplit
      · c0_hsteps
        rw [show BitVec.toNat 4194304 = 4194304 from by decide,
          show (2 ^ OfNat.ofNat 5 : Nat) = 32 by decide] at hc
        have hgt : 4194304 < rem.toNat / 32 := hc
        rw [show (4194304 : BitVec 64) = BitVec.ofNat 64 (min (rem.toNat / 32) 4194304) from by
          simp [Nat.min_eq_right (by omega : 4194304 ≤ rem.toNat / 32)]]
        exact hJ () m rfl
      · c0_hsteps
        rw [show BitVec.toNat 4194304 = 4194304 from by decide,
          show (2 ^ OfNat.ofNat 5 : Nat) = 32 by decide] at hc
        have hle : rem.toNat / 32 ≤ 4194304 := by omega
        rw [hc_sh, show BitVec.ofNat 64 (rem.toNat / 32) =
          BitVec.ofNat 64 (min (rem.toNat / 32) 4194304) from by rw [Nat.min_eq_left hle]]
        exact hJ () m rfl

theorem full_calc_scr_cap_m7_wp (Γ : Env) :
    ∀ a m Q X, m7CalcScrCapSpec a m Q X → Func.wp Γ full_calc_scr_cap_m7_body a m Q X := by
  rintro ⟨rem, _⟩ m Q X hq
  dsimp only [m7CalcScrCapSpec] at hq
  unfold full_calc_scr_cap_m7_body; dsimp only [Func.wp]
  c0_hsteps_nogrp; c0_hsplit
  · c0_hsteps
    rw [show BitVec.toNat 8192 = 8192 from by decide] at hc
    have hz : m7CalcScrCap rem.toNat = 0 := by unfold m7CalcScrCap; simp [hc]
    simpa [hz] using hq
  · c0_hsteps_nogrp
    rw [show BitVec.toNat 8192 = 8192 from by decide] at hc
    have hge : 8192 ≤ rem.toNat := by omega
    let raw := if 16384 ≤ rem.toNat then rem.toNat / 16 else rem.toNat / 32
    have hraw_lt : raw < 2 ^ 64 := by dsimp [raw]; split <;> omega
    refine wp_join_state1 (α := Unit) (proj := fun _ => BitVec.ofNat 64 raw)
      (Inv := fun _ m' => m' = m) ?_ ?_
    · rintro J _ m' hm'; subst m'
      c0_hsteps_nogrp
      refine wp_join_state1 (α := Unit) (proj := fun _ => BitVec.ofNat 64 (min raw 1048576))
        (Inv := fun _ m'' => m'' = m) ?_ ?_
      · rintro J2 _ m'' hm''; subst m''
        c0_hsteps
        have hcap : BitVec.ofNat 64 (min raw 1048576) &&& ~~~1 =
            BitVec.ofNat 64 (m7CalcScrCap rem.toNat) := by
          rw [fp_and_not1,
            show (BitVec.ofNat 64 (min raw 1048576)).toNat = min raw 1048576 by simp [raw]; omega]
          unfold m7CalcScrCap; simp [show ¬rem.toNat < 8192 by omega, raw]
        rw [hcap]; exact hq
      · intro J2 hJ2; c0_hsplit
        · c0_hsteps
          rw [show BitVec.toNat 1048576 = 1048576 from by decide,
            Nat.mod_eq_of_lt hraw_lt] at hc
          rw [show (1048576 : BitVec 64) = BitVec.ofNat 64 (min raw 1048576) from by
            simp [Nat.min_eq_right (by omega : 1048576 ≤ raw)]]
          exact hJ2 () m rfl
        · c0_hsteps
          rw [show BitVec.toNat 1048576 = 1048576 from by decide,
            Nat.mod_eq_of_lt hraw_lt] at hc
          rw [show BitVec.ofNat 64 raw = BitVec.ofNat 64 (min raw 1048576) from by
            rw [Nat.min_eq_left (by omega : raw ≤ 1048576)]]
          exact hJ2 () m rfl
    · intro J hJ; c0_hsplit
      · c0_hsteps
        rw [show BitVec.toNat 16384 = 16384 from by decide] at hc
        have hsh : rem >>> 4 = BitVec.ofNat 64 raw := by
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
            show (2 ^ 4 : Nat) = 16 by decide, BitVec.toNat_ofNat]
          dsimp only [raw]; simp only [hc, ite_true]
          exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) rem.isLt)).symm
        rw [hsh]; exact hJ () m rfl
      · c0_hsteps
        rw [show BitVec.toNat 16384 = 16384 from by decide] at hc
        have hsh : rem >>> 5 = BitVec.ofNat 64 raw := by
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
            show (2 ^ 5 : Nat) = 32 by decide, BitVec.toNat_ofNat]
          dsimp only [raw]; simp only [hc, ite_false]
          exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) rem.isLt)).symm
        rw [hsh]; exact hJ () m rfl

private def m7CalcMaxVTailExpr (avail mv nc bva : Val i64) : Expr Val Cont [i64] :=
  Expr.let_
    { sig := [i64, i64], code := OpCode.add i64,
      args := (Arg.var mv, Arg.var bva, ()) } fun p_3 =>
  Expr.call (as := [i64]) (rs := [i64]) "full_fixed_bytes_m7" (Arg.var p_3.fst, ())
    fun (p_4 : Tup Val [i64]) =>
  Expr.call (as := [i64]) (rs := [i64]) "full_trans_bytes_m7" (Arg.var p_3.fst, ())
    fun (p_5 : Tup Val [i64]) =>
  Expr.let_
    { sig := [i64, i64], code := OpCode.add i64,
      args := (Arg.var p_4.fst, Arg.var p_5.fst, ()) } fun p_6 =>
  Expr.let_
    { sig := [i64, i64], code := OpCode.cmp .ult i64,
      args := (Arg.var avail, Arg.var p_6.fst, ()) } fun p_7 =>
  Expr.jnz (Arg.var p_7.fst)
    (Expr.ret (Arg.var mv, ()))
    (Expr.let_
       { sig := [i64, i64], code := OpCode.sub i64,
         args := (Arg.var avail, Arg.var p_6.fst, ()) } fun p_8 =>
     Expr.let_
       { sig := [i64, i64], code := OpCode.mul i64,
         args := (Arg.var nc, Arg.imm 40, ()) } fun p_9 =>
     Expr.let_
       { sig := [i64, i64], code := OpCode.add i64,
         args := (Arg.var p_9.fst, Arg.imm 136, ()) } fun p_10 =>
     Expr.let_
       { sig := [i64, i64], code := OpCode.cmp .ult i64,
         args := (Arg.var p_8.fst, Arg.var p_10.fst, ()) } fun p_11 =>
     Expr.jnz (Arg.var p_11.fst)
       (Expr.ret (Arg.var mv, ()))
       (Expr.ret (Arg.var p_3.fst, ())))

private def m7CalcMaxVCapMinExpr (nc rem p_9 : Val i64) (J : Cont [i64]) : Expr Val Cont [i64] :=
  Expr.let_
    { sig := [i64, i64], code := OpCode.mul i64,
      args := (Arg.var nc, Arg.imm 48, ()) } fun p =>
  Expr.let_
    { sig := [i64, i64], code := OpCode.sub i64,
      args := (Arg.var rem, Arg.var p.fst, ()) } fun p =>
  Expr.let_
    { sig := [i64, i64], code := OpCode.sub i64,
      args := (Arg.var p.fst, Arg.imm 4096, ()) } fun p =>
  Expr.let_
    { sig := [i64, i64], code := OpCode.udiv 64,
      args := (Arg.var p.fst, Arg.imm 2688, ()) } fun (p : Tup Val [i64]) =>
  Expr.group (sig := [[i64]])
    (fun _ => Blocks.cons (fun (p : Tup Val [i64]) => Expr.jump J (Arg.var p.fst, ())) Blocks.nil)
    fun Js =>
    Expr.let_
      { sig := [i64, i64], code := OpCode.cmp .ult i64,
        args := (Arg.var p_9, Arg.var p.fst, ()) } fun p_10 =>
    Expr.jnz (Arg.var p_10.fst)
      (Expr.jump Js.fst (Arg.var p_9, ()))
      (Expr.jump Js.fst (Arg.var p.fst, ()))

private def m7CalcMaxVBvaMidExpr (mv nc rem : Val i64) (J : Cont [i64]) : Expr Val Cont [i64] :=
  Expr.let_
    { sig := [i32], code := OpCode.sext 32 64,
      args := (Arg.imm 1, ()) } fun p_6 =>
  Expr.let_
    { sig := [i64, i64], code := OpCode.lshr i64,
      args := (Arg.var mv, Arg.var p_6.fst, ()) } fun p_7 =>
  Expr.let_
    { sig := [i64, i64], code := OpCode.add i64,
      args := (Arg.var p_7.fst, Arg.imm 16, ()) } fun p_8 =>
  Expr.group (sig := [[i64]])
    (fun _ => Blocks.cons
      (fun (p_9 : Tup Val [i64]) => m7CalcMaxVCapMinExpr nc rem p_9.fst J) Blocks.nil)
    fun Js =>
    Expr.let_
      { sig := [i64, i64], code := OpCode.cmp .ugt i64,
        args := (Arg.var p_8.fst, Arg.imm 4096, ()) } fun p =>
    Expr.jnz (Arg.var p.fst)
      (Expr.jump Js.fst (Arg.imm 4096, ()))
      (Expr.jump Js.fst (Arg.var p_8.fst, ()))

private def m7CalcMaxVBvaExpr (mv nc rem : Val i64) (J : Cont [i64]) : Expr Val Cont [i64] :=
  Expr.let_
    { sig := [i64, i64], code := OpCode.cmp .uge i64,
      args := (Arg.var mv, Arg.imm 2, ()) } fun p_2 =>
  Expr.jnz (Arg.var p_2.fst)
    (Expr.let_
       { sig := [i64, i64], code := OpCode.mul i64,
         args := (Arg.var nc, Arg.imm 48, ()) } fun p_3 =>
     Expr.let_
       { sig := [i64, i64], code := OpCode.add i64,
         args := (Arg.var p_3.fst, Arg.imm 8192, ()) } fun p_4 =>
     Expr.let_
       { sig := [i64, i64], code := OpCode.cmp .ugt i64,
         args := (Arg.var rem, Arg.var p_4.fst, ()) } fun p_5 =>
     Expr.jnz (Arg.var p_5.fst)
       (m7CalcMaxVBvaMidExpr mv nc rem J)
       (Expr.jump J (Arg.imm 0, ())))
    (Expr.jump J (Arg.imm 0, ()))

private theorem m7CalcMaxV_body_eq (avail mv nc f0 : Val i64) :
    full_calc_max_v_m7_body Val Cont (avail, mv, nc, f0, ()) =
      Expr.let_
        { sig := [i64, i64], code := OpCode.sub i64,
          args := (Arg.var avail, Arg.var f0, ()) } fun p_1 =>
      Expr.group (sig := [[i64]])
        (fun _ => Blocks.cons (fun (p_2 : Tup Val [i64]) =>
          m7CalcMaxVTailExpr avail mv nc p_2.fst) Blocks.nil)
        (fun Js => m7CalcMaxVBvaExpr mv nc p_1.fst Js.fst) := rfl

private theorem m7CalcMaxVTail_wp (Γ : Env)
    (hFixed : EnvSpec Γ "full_fixed_bytes_m7" m7FixedBytesSpec)
    (hTrans : EnvSpec Γ "full_trans_bytes_m7" m7TransBytesSpec)
    (avail mv nc f0 : BitVec 64) (m : Mem 64) (Q : Post [i64]) (X : XPost)
    (hmv : mv.toNat < dimacsBound) (hnc : nc.toNat < dimacsBound)
    (hq : Q (BitVec.ofNat 64 (m7CalcMaxV avail.toNat mv.toNat nc.toNat f0.toNat), ()) m) :
    wp Γ Q X (m7CalcMaxVTailExpr avail mv nc
      (BitVec.ofNat 64 (m7BvaCap avail.toNat mv.toNat nc.toNat f0.toNat))) m := by
  unfold m7CalcMaxVTailExpr
  c0_hsteps
  let cand := mv.toNat + m7BvaCap avail.toNat mv.toNat nc.toNat f0.toNat
  have hcand_lt : cand < 2 * dimacsBound := by
    have := m7BvaCap_le avail.toNat mv.toNat nc.toNat f0.toNat
    unfold dimacsBound at *; omega
  have hcand_bv : mv + BitVec.ofNat 64 (m7BvaCap avail.toNat mv.toNat nc.toNat f0.toNat) =
      BitVec.ofNat 64 cand := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, cand]
  have hfix_lt := m7FixedBytes_lt hcand_lt
  have htr_lt := m7TransBytes_lt hcand_lt
  refine ⟨fun r m1 => r = (BitVec.ofNat 64 (m7FixedBytes cand), ()) ∧ m1 = m, X, ?_, ?_,
    fun _ _ _ _ h => h⟩
  · apply hFixed
    dsimp only [m7FixedBytesSpec, vals, Arg.val]
    rw [hcand_bv]; simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by unfold dimacsBound at *; omega)]
    exact ⟨hcand_lt, rfl, trivial⟩
  rintro ⟨fixv, _⟩ m1 ⟨hfx, hm1⟩
  have hfx1 : fixv = BitVec.ofNat 64 (m7FixedBytes cand) := congrArg Prod.fst hfx
  subst hfx1; subst m1
  c0_hsteps
  refine ⟨fun r m2 => r = (BitVec.ofNat 64 (m7TransBytes cand), ()) ∧ m2 = m, X, ?_, ?_,
    fun _ _ _ _ h => h⟩
  · apply hTrans
    dsimp only [m7TransBytesSpec, vals, Arg.val]
    rw [hcand_bv]; simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by unfold dimacsBound at *; omega)]
    exact ⟨hcand_lt, rfl, trivial⟩
  rintro ⟨trv, _⟩ m2 ⟨htr, hm2⟩
  have htr1 : trv = BitVec.ofNat 64 (m7TransBytes cand) := congrArg Prod.fst htr
  subst htr1; subst m2
  run_tac for _ in [:64] do
    if !(← LeanQbe.T.C0HeadStep.headStepOnce { splitJnz := false, unrollGroup := false })
    then break
  let need := m7FixedBytes cand + m7TransBytes cand
  have hneed_bv : BitVec.ofNat 64 (m7FixedBytes cand) + BitVec.ofNat 64 (m7TransBytes cand) =
      BitVec.ofNat 64 need := by rw [← BitVec.ofNat_add]
  rw [hneed_bv]
  c0_hsplit
  · c0_hsteps
    have hlt : avail.toNat < need := by
      rw [Nat.mod_eq_of_lt (by omega : need < 2 ^ 64)] at hc; exact hc
    have hres : m7CalcMaxV avail.toNat mv.toNat nc.toNat f0.toNat = mv.toNat := by
      unfold m7CalcMaxV; simp [hlt, need, cand]
    simpa [hres] using hq
  · run_tac for _ in [:64] do
      if !(← LeanQbe.T.C0HeadStep.headStepOnce { splitJnz := false, unrollGroup := false })
      then break
    have hge : need ≤ avail.toNat := by
      rw [Nat.mod_eq_of_lt (by omega : need < 2 ^ 64)] at hc; omega
    have hneed_lt : need < 2 ^ 64 := lt_of_le_of_lt hge avail.isLt
    have hsub_bv2 : (2 ^ 64 - need % 2 ^ 64 + avail.toNat) % 2 ^ 64 =
        avail.toNat - need := by
      rw [Nat.mod_eq_of_lt hneed_lt]; omega
    c0_hsplit
    · c0_hsteps
      rw [show BitVec.toNat 40 = 40 from by decide,
        show BitVec.toNat 136 = 136 from by decide] at hc
      have hlt2 : avail.toNat - need < nc.toNat * 40 + 136 := by
        unfold dimacsBound at hnc
        rw [hsub_bv2, Nat.mod_eq_of_lt (by omega)] at hc
        exact hc
      have hres : m7CalcMaxV avail.toNat mv.toNat nc.toNat f0.toNat = mv.toNat := by
        unfold m7CalcMaxV; simp [hlt2, need, cand]
      simpa [hres] using hq
    · c0_hsteps
      rw [show BitVec.toNat 40 = 40 from by decide,
        show BitVec.toNat 136 = 136 from by decide] at hc
      have hge2 : ¬avail.toNat - need < nc.toNat * 40 + 136 := by
        unfold dimacsBound at hnc
        rw [hsub_bv2, Nat.mod_eq_of_lt (by omega)] at hc
        exact hc
      have hres : m7CalcMaxV avail.toNat mv.toNat nc.toNat f0.toNat = cand := by
        unfold m7CalcMaxV; simp [show ¬avail.toNat < need by omega, hge2, cand, need]
      simpa [hres, hcand_bv] using hq

private theorem m7CalcMaxVCapMin_wp (Γ : Env) (Q : Post [i64]) (X : XPost)
    (avail mv nc f0 : BitVec 64) (m : Mem 64) (J : Cont [i64])
    (hmv2 : 2 ≤ mv.toNat) (hnc : nc.toNat < dimacsBound)
    (hrem_gt : nc.toNat * 48 + 8192 < avail.toNat - f0.toNat)
    (hrem_eq : (avail - f0).toNat = avail.toNat - f0.toNat)
    (hJ : J (BitVec.ofNat 64 (m7BvaCap avail.toNat mv.toNat nc.toNat f0.toNat), ()) m) :
    wp Γ Q X (m7CalcMaxVCapMinExpr nc (avail - f0)
      (BitVec.ofNat 64 (min (mv.toNat / 2 + 16) 4096)) J) m := by
  unfold m7CalcMaxVCapMinExpr
  have hnc64 : nc.toNat * 48 + 8192 < 2 ^ 64 := by unfold dimacsBound at *; omega
  c0_hsteps_nogrp
  have hle1 : nc * 48 ≤ avail - f0 := by
    change (nc * 48).toNat ≤ (avail - f0).toNat
    rw [hrem_eq, BitVec.toNat_mul, show BitVec.toNat 48 = 48 by decide,
      Nat.mod_eq_of_lt (by omega)]
    omega
  have hsub1 : (avail - f0 - nc * 48).toNat = avail.toNat - f0.toNat - nc.toNat * 48 := by
    rw [BitVec.toNat_sub_of_le hle1, hrem_eq, BitVec.toNat_mul,
      show BitVec.toNat 48 = 48 by decide, Nat.mod_eq_of_lt (by omega)]
  have hle2 : (4096 : BitVec 64) ≤ avail - f0 - nc * 48 := by
    change (4096 : BitVec 64).toNat ≤ _
    rw [hsub1, show (4096 : BitVec 64).toNat = 4096 by decide]; omega
  have hsub2 : (avail - f0 - nc * 48 - 4096).toNat =
      avail.toNat - f0.toNat - nc.toNat * 48 - 4096 := by
    rw [BitVec.toNat_sub_of_le hle2, hsub1]; rfl
  have hdiv_lt : (avail.toNat - f0.toNat - nc.toNat * 48 - 4096) / 2688 < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _)
      (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_of_le_of_lt (Nat.sub_le _ _)
        (Nat.lt_of_le_of_lt (Nat.sub_le _ _) avail.isLt)))
  have hmb : (avail - f0 - nc * 48 - 4096) / 2688 =
      BitVec.ofNat 64 (((avail.toNat - f0.toNat) - nc.toNat * 48 - 4096) / 2688) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_udiv, hsub2, show BitVec.toNat 2688 = 2688 by decide, BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt hdiv_lt).symm
  have hfin : m7BvaCap avail.toNat mv.toNat nc.toNat f0.toNat =
      min (min (mv.toNat / 2 + 16) 4096)
        (((avail.toNat - f0.toNat) - nc.toNat * 48 - 4096) / 2688) := by
    unfold m7BvaCap; simp [hmv2, hrem_gt]
  have hmod_min : min (mv.toNat / 2 + 16) 4096 % 2 ^ 64 = min (mv.toNat / 2 + 16) 4096 :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by decide))
  have hdiv_eq : ((avail - f0 - nc * 48 - 4096) / 2688).toNat =
      ((avail.toNat - f0.toNat) - nc.toNat * 48 - 4096) / 2688 := by
    rw [hmb, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hdiv_lt
  refine wp_join_state1 (α := Unit)
    (proj := fun _ => BitVec.ofNat 64 (m7BvaCap avail.toNat mv.toNat nc.toNat f0.toNat))
    (Inv := fun _ m'' => m'' = m) ?_ ?_
  · rintro _ _ m'' hm''; subst m''
    c0_hsteps
    exact hJ
  · intro J3 hJ3; c0_hsplit
    · c0_hsteps
      rw [hmod_min, hdiv_eq] at hc
      have hlt : min (mv.toNat / 2 + 16) 4096 <
          ((avail.toNat - f0.toNat) - nc.toNat * 48 - 4096) / 2688 := hc
      rw [show BitVec.ofNat 64 (min (mv.toNat / 2 + 16) 4096) =
        BitVec.ofNat 64 (m7BvaCap avail.toNat mv.toNat nc.toNat f0.toNat) from by
        rw [hfin, Nat.min_eq_left (Nat.le_of_lt hlt)]]
      exact hJ3 () m rfl
    · c0_hsteps
      rw [hmod_min, hdiv_eq] at hc
      have hle : ((avail.toNat - f0.toNat) - nc.toNat * 48 - 4096) / 2688 ≤
          min (mv.toNat / 2 + 16) 4096 := Nat.le_of_not_lt hc
      have h_lhs : (avail - f0 - nc * 48 - 4096) / 2688 =
          BitVec.ofNat 64 (m7BvaCap avail.toNat mv.toNat nc.toNat f0.toNat) := by
        rw [hmb, hfin, Nat.min_eq_right hle]
      rw [h_lhs]; exact hJ3 () m rfl

private theorem m7CalcMaxVBvaMid_wp (Γ : Env) (Q : Post [i64]) (X : XPost)
    (avail mv nc f0 : BitVec 64) (m : Mem 64) (J : Cont [i64])
    (hmv : mv.toNat < dimacsBound) (hmv2 : 2 ≤ mv.toNat) (hnc : nc.toNat < dimacsBound)
    (hrem_gt : nc.toNat * 48 + 8192 < avail.toNat - f0.toNat)
    (hrem_eq : (avail - f0).toNat = avail.toNat - f0.toNat)
    (hJ : J (BitVec.ofNat 64 (m7BvaCap avail.toNat mv.toNat nc.toNat f0.toNat), ()) m) :
    wp Γ Q X (m7CalcMaxVBvaMidExpr mv nc (avail - f0) J) m := by
  unfold m7CalcMaxVBvaMidExpr
  c0_hsteps_nogrp
  have hsh : mv >>> 1 + 16 = BitVec.ofNat 64 (mv.toNat / 2 + 16) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_add, BitVec.toNat_ushiftRight]
    unfold dimacsBound at hmv; omega
  refine wp_join_state1 (α := Unit)
    (proj := fun _ => BitVec.ofNat 64 (min (mv.toNat / 2 + 16) 4096))
    (Inv := fun _ m' => m' = m) ?_ ?_
  · rintro J2 _ m' hm'; subst m'
    exact m7CalcMaxVCapMin_wp Γ Q X avail mv nc f0 m J hmv2 hnc hrem_gt hrem_eq hJ
  · intro J2 hJ2; c0_hsplit
    · c0_hsteps
      rw [show BitVec.toNat 4096 = 4096 from by decide,
        show BitVec.toNat 16 = 16 from by decide,
        show (2 ^ OfNat.ofNat 1 : Nat) = 2 by decide] at hc
      unfold dimacsBound at hmv
      rw [Nat.mod_eq_of_lt (by omega)] at hc
      have h4096 : 4096 < mv.toNat / 2 + 16 := hc
      rw [show (4096 : BitVec 64) = BitVec.ofNat 64 (min (mv.toNat / 2 + 16) 4096) from by
        simp [Nat.min_eq_right (by omega : 4096 ≤ mv.toNat / 2 + 16)]]
      exact hJ2 () m rfl
    · c0_hsteps
      rw [show BitVec.toNat 4096 = 4096 from by decide,
        show BitVec.toNat 16 = 16 from by decide,
        show (2 ^ OfNat.ofNat 1 : Nat) = 2 by decide] at hc
      unfold dimacsBound at hmv
      rw [Nat.mod_eq_of_lt (by omega)] at hc
      have h4096 : mv.toNat / 2 + 16 ≤ 4096 := by omega
      rw [hsh, show BitVec.ofNat 64 (mv.toNat / 2 + 16) =
        BitVec.ofNat 64 (min (mv.toNat / 2 + 16) 4096) from by rw [Nat.min_eq_left h4096]]
      exact hJ2 () m rfl

private theorem m7BvaCap_zero1 {avail mv nc f0 : Nat} (h : ¬ nc * 48 + 8192 < avail - f0) :
    m7BvaCap avail mv nc f0 = 0 := by unfold m7BvaCap; simp [h]

private theorem m7BvaCap_zero2 {avail mv nc f0 : Nat} (h : ¬ 2 ≤ mv) :
    m7BvaCap avail mv nc f0 = 0 := by unfold m7BvaCap; simp [h]

private theorem m7CalcMaxVBva_wp (Γ : Env) (Q : Post [i64]) (X : XPost)
    (avail mv nc f0 : BitVec 64) (m : Mem 64) (J : Cont [i64])
    (hmv : mv.toNat < dimacsBound) (hnc : nc.toNat < dimacsBound) (hf0 : f0.toNat ≤ avail.toNat)
    (hJ : J (BitVec.ofNat 64 (m7BvaCap avail.toNat mv.toNat nc.toNat f0.toNat), ()) m) :
    wp Γ Q X (m7CalcMaxVBvaExpr mv nc (avail - f0) J) m := by
  unfold m7CalcMaxVBvaExpr
  have hnc64 : nc.toNat * 48 + 8192 < 2 ^ 64 := by unfold dimacsBound at *; omega
  have hrem_eq : (avail - f0).toNat = avail.toNat - f0.toNat := by
    simp [BitVec.toNat_sub]; omega
  have hbound_nat : (nc * 48 + 8192 : BitVec 64).toNat = nc.toNat * 48 + 8192 := by
    rw [BitVec.toNat_add, BitVec.toNat_mul]
    rw [show (48 : BitVec 64).toNat = 48 from by decide,
      show (8192 : BitVec 64).toNat = 8192 from by decide]
    rw [Nat.mod_eq_of_lt (by omega : nc.toNat * 48 < 2 ^ 64), Nat.mod_eq_of_lt hnc64]
  c0_hsplit
  · rw [show (2 : BitVec 64).toNat = 2 from by decide] at hc
    have hmv2 : 2 ≤ mv.toNat := hc
    run_tac for _ in [:16] do
      if !(← LeanQbe.T.C0HeadStep.headStepOnce { splitJnz := false, unrollGroup := false })
      then break
    rw [wp_jnz]
    constructor
    · intro h
      have hlt : (nc * 48 + 8192).ult (avail - f0) = true := h
      rw [BitVec.ult, hbound_nat, hrem_eq] at hlt
      exact m7CalcMaxVBvaMid_wp Γ Q X avail mv nc f0 m J hmv hmv2 hnc
        (of_decide_eq_true hlt) hrem_eq hJ
    · intro h
      have hge : (nc * 48 + 8192).ult (avail - f0) = false := h
      rw [BitVec.ult, hbound_nat, hrem_eq] at hge
      have hle : ¬ nc.toNat * 48 + 8192 < avail.toNat - f0.toNat := by
        simpa using of_decide_eq_false hge
      c0_hsteps
      rw [m7BvaCap_zero1 hle] at hJ
      exact hJ
  · c0_hsteps
    rw [show (2 : BitVec 64).toNat = 2 from by decide] at hc
    rw [m7BvaCap_zero2 hc] at hJ
    exact hJ

theorem full_calc_max_v_m7_wp (Γ : Env)
    (hFixed : EnvSpec Γ "full_fixed_bytes_m7" m7FixedBytesSpec)
    (hTrans : EnvSpec Γ "full_trans_bytes_m7" m7TransBytesSpec) :
    ∀ a m Q X, m7CalcMaxVSpec a m Q X → Func.wp Γ full_calc_max_v_m7_body a m Q X := by
  rintro ⟨avail, mv, nc, f0, _⟩ m Q X ⟨hmv, hnc, hf0, hq⟩
  dsimp only [Func.wp]
  rw [m7CalcMaxV_body_eq]
  c0_hsteps_nogrp
  refine wp_join_state1 (α := Unit)
    (proj := fun _ => BitVec.ofNat 64 (m7BvaCap avail.toNat mv.toNat nc.toNat f0.toNat))
    (Inv := fun _ m' => m' = m) ?_ ?_
  · rintro _ _ m' hm'; subst m'
    exact m7CalcMaxVTail_wp Γ hFixed hTrans avail mv nc f0 m Q X hmv hnc hq
  · intro J hJ
    exact m7CalcMaxVBva_wp Γ Q X avail mv nc f0 m J hmv hnc hf0 (hJ () m rfl)

private theorem hdrTail4_elim {hdr : BitVec 64} {w0 w1 w2 w3 : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (hdrTail4 hdr w0 w1 w2 w3 ⋆ R) m) :
    w0.length = 35 ∧ w1.length = 35 ∧ w2.length = 35 ∧ w3.length = 35 ∧
      ((array64 (hdr + 32) w0 ⋆ array64 (hdr + 312) w1 ⋆
        array64 (hdr + 592) w2 ⋆ array64 (hdr + 872) w3) ⋆ R) m := by
  unfold hdrTail4 at hm
  have h0 := sep_pure_l.mp hm
  have h1 := sep_pure_l.mp h0.2
  have h2 := sep_pure_l.mp h1.2
  have h3 := sep_pure_l.mp h2.2
  exact ⟨h0.1, h1.1, h2.1, h3.1, h3.2⟩

private theorem forall_lt_succ {n : Nat} {P : Nat → Prop} (h0 : P n) (hs : ∀ i < n, P i) :
    ∀ i < n + 1, P i := fun i hi => by
  rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hlt | rfl
  · exact hs i hlt
  · exact h0

private theorem list_eq_35 {a b : List (BitVec 64)} (ha : a.length = 35) (hb : b.length = 35)
    (h : ∀ i < 35, a[i]? = b[i]?) : a = b := by
  apply List.ext_getElem?; intro i
  by_cases hi : i < 35
  · exact h i hi
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

private theorem hdrTail4_congr_set {h : BitVec 64} {w0 w1 w2 w3 w0' w1' w2' w3' : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (h0 : w0 = w0') (h1 : w1 = w1') (h2 : w2 = w2') (h3 : w3 = w3')
    (hm : (hdrTail4 h w0 w1 w2 w3 ⋆ R) m) :
    (hdrTail4 h w0' w1' w2' w3' ⋆ R) m := by
  subst h0 h1 h2 h3; exact hm

private theorem list_set_comm {α : Type} (xs : List α) {i j : Nat} (a b : α) (hne : i ≠ j) :
    (xs.set i a).set j b = (xs.set j b).set i a := by
  apply List.ext_getElem?; intro k
  by_cases h1 : i = k
  · subst h1
    have hne' : j ≠ i := fun h => hne h.symm
    simp [List.getElem?_set, hne']
  · by_cases h2 : j = k
    · subst h2; simp [List.getElem?_set, h1]
    · simp [h1, h2]

private theorem set_congr {α : Type} {xs ys : List α} {i : Nat} {a b : α}
    (hxs : xs = ys) (ha : a = b) : xs.set i a = ys.set i b := by
  subst hxs ha; rfl

private theorem ptrs_w0_perm (w0 : List (BitVec 64))
    (v4 v5 v6 v7 v8 v9 v10 v13 v21 v22 v23 v24 v25 v26 v29 : BitVec 64) :
    ((((((((((((((w0.set 4 v4).set 5 v5).set 24 v24).set 6 v6).set 7 v7).set 8 v8).set
      13 v13).set 21 v21).set 22 v22).set 26 v26).set 9 v9).set 23 v23).set 25 v25).set
      10 v10).set 29 v29 =
    ((((((((((((((w0.set 4 v4).set 5 v5).set 6 v6).set 7 v7).set 8 v8).set 9 v9).set
      10 v10).set 13 v13).set 21 v21).set 22 v22).set 23 v23).set 24 v24).set 25 v25).set
      26 v26).set 29 v29 := by
  rw [list_set_comm _ (i := 24) (j := 6) _ _ (by decide),
      list_set_comm _ (i := 24) (j := 7) _ _ (by decide),
      list_set_comm _ (i := 24) (j := 8) _ _ (by decide),
      list_set_comm _ (i := 24) (j := 13) _ _ (by decide),
      list_set_comm _ (i := 24) (j := 21) _ _ (by decide),
      list_set_comm _ (i := 24) (j := 22) _ _ (by decide),
      list_set_comm _ (i := 26) (j := 9) _ _ (by decide),
      list_set_comm _ (i := 24) (j := 9) _ _ (by decide),
      list_set_comm _ (i := 22) (j := 9) _ _ (by decide),
      list_set_comm _ (i := 21) (j := 9) _ _ (by decide),
      list_set_comm _ (i := 13) (j := 9) _ _ (by decide),
      list_set_comm _ (i := 25) (j := 10) _ _ (by decide),
      list_set_comm _ (i := 23) (j := 10) _ _ (by decide),
      list_set_comm _ (i := 26) (j := 10) _ _ (by decide),
      list_set_comm _ (i := 24) (j := 10) _ _ (by decide),
      list_set_comm _ (i := 22) (j := 10) _ _ (by decide),
      list_set_comm _ (i := 21) (j := 10) _ _ (by decide),
      list_set_comm _ (i := 13) (j := 10) _ _ (by decide),
      list_set_comm _ (i := 26) (j := 23) _ _ (by decide),
      list_set_comm _ (i := 24) (j := 23) _ _ (by decide),
      list_set_comm _ (i := 26) (j := 25) _ _ (by decide)]

private theorem ptrs_w1_perm (w1 : List (BitVec 64))
    (v6 v7 v8 v9 v10 v11 v13 v15 : BitVec 64) :
    (((((((w1.set 10 v10).set 11 v11).set 6 v6).set 13 v13).set 7 v7).set 8 v8).set
      9 v9).set 15 v15 =
    (((((((w1.set 6 v6).set 7 v7).set 8 v8).set 9 v9).set 10 v10).set 11 v11).set
      13 v13).set 15 v15 := by
  rw [list_set_comm _ (i := 11) (j := 6) _ _ (by decide),
      list_set_comm _ (i := 10) (j := 6) _ _ (by decide),
      list_set_comm _ (i := 13) (j := 7) _ _ (by decide),
      list_set_comm _ (i := 11) (j := 7) _ _ (by decide),
      list_set_comm _ (i := 10) (j := 7) _ _ (by decide),
      list_set_comm _ (i := 13) (j := 8) _ _ (by decide),
      list_set_comm _ (i := 11) (j := 8) _ _ (by decide),
      list_set_comm _ (i := 10) (j := 8) _ _ (by decide),
      list_set_comm _ (i := 13) (j := 9) _ _ (by decide),
      list_set_comm _ (i := 11) (j := 9) _ _ (by decide),
      list_set_comm _ (i := 10) (j := 9) _ _ (by decide)]

private theorem arenas_w0_perm (w0 : List (BitVec 64)) (v0 v1 v11 v12 : BitVec 64) :
    (((w0.set 11 v11).set 12 v12).set 0 v0).set 1 v1 =
    (((w0.set 0 v0).set 1 v1).set 11 v11).set 12 v12 := by
  rw [list_set_comm _ (i := 12) (j := 0) _ _ (by decide),
      list_set_comm _ (i := 11) (j := 0) _ _ (by decide),
      list_set_comm _ (i := 12) (j := 1) _ _ (by decide),
      list_set_comm _ (i := 11) (j := 1) _ _ (by decide)]

private theorem arenas_w1_perm (w1 : List (BitVec 64)) (v12 v14 v16 : BitVec 64) :
    ((w1.set 14 v14).set 16 v16).set 12 v12 = ((w1.set 12 v12).set 14 v14).set 16 v16 := by
  rw [list_set_comm _ (i := 16) (j := 12) _ _ (by decide),
      list_set_comm _ (i := 14) (j := 12) _ _ (by decide)]

private theorem arenas_w2_perm (w2 : List (BitVec 64)) (v27 v28 v29 v32 v33 v34 : BitVec 64) :
    (((((w2.set 32 v32).set 33 v33).set 34 v34).set 28 v28).set 29 v29).set 27 v27 =
    (((((w2.set 27 v27).set 28 v28).set 29 v29).set 32 v32).set 33 v33).set 34 v34 := by
  rw [list_set_comm _ (i := 34) (j := 28) _ _ (by decide),
      list_set_comm _ (i := 33) (j := 28) _ _ (by decide),
      list_set_comm _ (i := 32) (j := 28) _ _ (by decide),
      list_set_comm _ (i := 34) (j := 29) _ _ (by decide),
      list_set_comm _ (i := 33) (j := 29) _ _ (by decide),
      list_set_comm _ (i := 32) (j := 29) _ _ (by decide),
      list_set_comm _ (i := 34) (j := 27) _ _ (by decide),
      list_set_comm _ (i := 33) (j := 27) _ _ (by decide),
      list_set_comm _ (i := 32) (j := 27) _ _ (by decide),
      list_set_comm _ (i := 29) (j := 27) _ _ (by decide),
      list_set_comm _ (i := 28) (j := 27) _ _ (by decide)]

private theorem arenas_w3_perm (w3 : List (BitVec 64)) (v0 v1 v2 v3 v6 : BitVec 64) :
    ((((w3.set 3 v3).set 6 v6).set 0 v0).set 1 v1).set 2 v2 =
    ((((w3.set 0 v0).set 1 v1).set 2 v2).set 3 v3).set 6 v6 := by
  rw [list_set_comm _ (i := 6) (j := 0) _ _ (by decide),
      list_set_comm _ (i := 3) (j := 0) _ _ (by decide),
      list_set_comm _ (i := 6) (j := 1) _ _ (by decide),
      list_set_comm _ (i := 3) (j := 1) _ _ (by decide),
      list_set_comm _ (i := 6) (j := 2) _ _ (by decide),
      list_set_comm _ (i := 3) (j := 2) _ _ (by decide)]

theorem full_init_ptrs_m7_wp (Γ : Env) :
    ∀ a m Q X, m7InitPtrsSpec a m Q X → Func.wp Γ full_init_ptrs_m7_body a m Q X := by
  rintro ⟨h, hdr_addr, mx, _⟩ m Q X ⟨rfl, hmx, hfit, w0, w1, w2, w3, R, hm, hpost⟩
  have ⟨lw0, lw1, lw2, lw3, _⟩ := hdrTail4_elim hm
  unfold full_init_ptrs_m7_body; dsimp only [Func.wp]
  have hmx_nat : BitVec.ofNat 64 mx.toNat = mx := bv64_self
  c0_hsteps_nogrp
  refine wp_join_state1 (α := Unit)
    (proj := fun _ => BitVec.ofNat 64 (fullMinDepthOf mx.toNat)) (Inv := fun _ m' => m' = m) ?_ ?_
  · rintro J _ m' hm'; subst m'
    rw [Blocks.get_here]
    fp_head_steps
    apply hpost
    have hvb : mx <<< 1 + 7 &&& ~~~7 = BitVec.ofNat 64 (valsBytes mx.toNat) := by
      have hh := bv64_vb_nat hmx; rw [hmx_nat] at hh; exact hh
    have hmb : mx + 7 &&& ~~~7 = BitVec.ofNat 64 (markBytes mx.toNat) := by
      have hh := bv64_mb_s hmx; rw [hmx_nat] at hh; exact hh
    have hub : (mx + 1) <<< 2 + 7 &&& ~~~7 = BitVec.ofNat 64 (u32FullBytes mx.toNat) := by
      have hh := bv64_ub_nat hmx; rw [hmx_nat] at hh; exact hh
    have hnls3 : mx <<< 1 <<< ((BitVec.signExtend 64 (3 : BitVec 32)).toNat % 64) =
        BitVec.ofNat 64 (16 * mx.toNat) := by
      have hh := bv64_nlits_shl3_nat hmx; rw [hmx_nat] at hh; exact hh
    have hsh3mx : mx <<< (3 : Nat) = BitVec.ofNat 64 (8 * mx.toNat) := by
      rw [show (3 : Nat) = (BitVec.signExtend 64 3#32).toNat by decide]
      have hh := bv64_shl3_s (n := mx.toNat); rw [hmx_nat] at hh; exact hh
    have hsh3md : BitVec.ofNat 64 (fullMinDepthOf mx.toNat) <<<
        ((BitVec.signExtend 64 (3 : BitVec 32)).toNat % 64) =
        BitVec.ofNat 64 (8 * fullMinDepthOf mx.toNat) := fp_shl_sext3
    rw [hvb, hmb, hub, hnls3, hsh3mx, hsh3md] at hm
    simp only [show (1152 : BitVec 64) = BitVec.ofNat 64 1152 from rfl,
      show (256 : BitVec 64) = BitVec.ofNat 64 256 from rfl,
      show (64 : BitVec 64) = BitVec.ofNat 64 64 from rfl,
      BitVec.add_assoc, ← BitVec.ofNat_add] at hm
    refine hdrTail4_congr_set ?_ ?_ ?_ ?_ hm
    · rw [ptrs_w0_perm]; dsimp only [m7PtrsW0]
      simp only [BitVec.add_assoc, ← BitVec.ofNat_add]
      repeat (first | rfl |
        (refine set_congr ?_ (by
          first | rfl | (apply congrArg (fun x => h + BitVec.ofNat 64 x); omega))))
    · rw [ptrs_w1_perm]; dsimp only [m7PtrsW1]
      simp only [fp_mul_nat, BitVec.add_assoc, ← BitVec.ofNat_add]
      repeat (first | rfl |
        (refine set_congr ?_ (by
          first | rfl | (apply congrArg (fun x => h + BitVec.ofNat 64 x); omega))))
    · dsimp only [m7PtrsW2]
      simp only [fp_mul_nat, BitVec.add_assoc, ← BitVec.ofNat_add]
      repeat (first | rfl |
        (refine set_congr ?_ (by
          first | rfl | (apply congrArg (fun x => h + BitVec.ofNat 64 x); omega))))
    · dsimp only [m7PtrsW3]
      simp only [BitVec.add_assoc, ← BitVec.ofNat_add]
      refine set_congr rfl (by
        first | rfl | (apply congrArg (fun x => h + BitVec.ofNat 64 x); omega))
  · intro J hJ; c0_hsplit
    · c0_hsteps
      rw [show BitVec.toNat 1000 = 1000 from by decide] at hc
      have hlt : mx.toNat + 1 < 1000 := by unfold dimacsBound at hmx; omega
      have heq : mx + 1 = BitVec.ofNat 64 (fullMinDepthOf mx.toNat) := by
        have hb := bv64_mdepth hmx
        have h1 : (BitVec.ofNat 64 mx.toNat + 1#64).toNat = mx.toNat + 1 := by
          simp [BitVec.toNat_add]; unfold dimacsBound at hmx; omega
        rw [h1, hmx_nat] at hb; simpa [hlt] using hb
      rw [heq]; exact hJ () m rfl
    · c0_hsteps
      rw [show BitVec.toNat 1000 = 1000 from by decide] at hc
      have hge : 1000 ≤ mx.toNat + 1 := by unfold dimacsBound at hmx; omega
      have heq : (1000 : BitVec 64) = BitVec.ofNat 64 (fullMinDepthOf mx.toNat) := by
        have hb := bv64_mdepth hmx
        have h1 : (BitVec.ofNat 64 mx.toNat + 1#64).toNat = mx.toNat + 1 := by
          simp [BitVec.toNat_add]; unfold dimacsBound at hmx; omega
        rw [h1, hmx_nat] at hb; simpa [show ¬(mx.toNat + 1 < 1000) by omega] using hb
      rw [heq]; exact hJ () m rfl

theorem full_init_hdr_m7_wp (Γ : Env) :
    ∀ a m Q X, m7InitHdrSpec a m Q X → Func.wp Γ full_init_hdr_m7_body a m Q X := by
  rintro ⟨h, mv, mx, fuel, _⟩ m Q X ⟨hle, hmx, w0, w1, w2, w3, R, hm, hpost⟩
  have ⟨lw0, lw1, lw2, lw3, _⟩ := hdrTail4_elim hm
  unfold full_init_hdr_m7_body; dsimp only [Func.wp]
  have hmv_nat : BitVec.ofNat 64 mv.toNat = mv := bv64_self
  have hmx_nat : BitVec.ofNat 64 mx.toNat = mx := bv64_self
  fp_head_steps
  let qf : BitVec 64 := if mv.toNat == 0 then 0xFFFFFFFF#64 else 0#64
  let ql : BitVec 64 := if mv.toNat == 0 then 0xFFFFFFFF#64 else BitVec.ofNat 64 (mv.toNat - 1)
  refine wp_join_state1 (α := Unit) (proj := fun _ => qf) (Inv := fun _ m1 => m1 = m) ?_ ?_
  · rintro J1 _ m1 hm1; subst m1; rw [Blocks.get_here]; fp_head_steps
    refine wp_join_state1 (α := Unit) (proj := fun _ => ql) (Inv := fun _ m2 => m2 = m) ?_ ?_
    · rintro J2 _ m2 hm2; subst m2; rw [Blocks.get_here]; fp_head_steps
      refine wp_join_state1 (α := Unit) (proj := fun _ => ql) (Inv := fun _ m3 => m3 = m) ?_ ?_
      · rintro J3 _ m3 hm3; subst m3; rw [Blocks.get_here]; fp_head_steps
        apply hpost
        have hmv1 : mv + 1 = BitVec.ofNat 64 (mv.toNat + 1) := by
          apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]
        have hsub_mv : mx - mv = BitVec.ofNat 64 (mx.toNat - mv.toNat) := by
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_sub_of_le hle, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) mx.isLt)]
        have hs28 : (1 : BitVec 64) <<< ((BitVec.signExtend 64 (28 : BitVec 32)).toNat % 64) =
            1#64 <<< 28 := by decide
        have hs24 : (1 : BitVec 64) <<< ((BitVec.signExtend 64 (24 : BitVec 32)).toNat % 64) =
            1#64 <<< 24 := by decide
        have hrng : (11400714819323198485 : BitVec 64) ^^^ mv + 1 =
            0x9E3779B97F4A7C15#64 ^^^ BitVec.ofNat 64 (mv.toNat + 1) := by
          rw [hmv1]; rfl
        rw [hsub_mv, hs28, hs24, hrng, ← hmv_nat, ← hmx_nat] at hm
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt mv.isLt, Nat.mod_eq_of_lt mx.isLt] at hm
        refine hdrTail4_congr_set ?_ ?_ ?_ ?_ hm
        · dsimp only [m7HdrW0]; rfl
        · dsimp only [m7HdrW1]
          apply list_eq_35 (by simp [lw1]) (by simp [lw1])
          repeat (first | exact fun i hi => absurd hi (Nat.not_lt_zero i) |
            (apply forall_lt_succ; simp only [List.getElem?_set, List.length_set, lw1,
              Nat.reduceEqDiff, Nat.reduceLT, ite_true, ite_false,
              show (0 : BitVec 64) = 0#64 from rfl,
              show (1 : BitVec 64) = 1#64 from rfl,
              show (1000 : BitVec 64) = 1000#64 from rfl,
              show (4294967295 : BitVec 64) = 4294967295#64 from rfl]))
        · dsimp only [m7HdrW2, qf, ql]
          apply list_eq_35 (by simp [lw2]) (by simp [lw2])
          repeat (first | exact fun i hi => absurd hi (Nat.not_lt_zero i) |
            (apply forall_lt_succ; simp only [List.getElem?_set, List.length_set, lw2,
              Nat.reduceEqDiff, Nat.reduceLT, ite_true, ite_false,
              show (0 : BitVec 64) = 0#64 from rfl,
              show (1 : BitVec 64) = 1#64 from rfl,
              show (2 : BitVec 64) = 2#64 from rfl,
              show (6 : BitVec 64) = 6#64 from rfl,
              show (1000 : BitVec 64) = 1000#64 from rfl]))
        · dsimp only [m7HdrW3]
          apply list_eq_35 (by simp [lw3]) (by simp [lw3])
          repeat (first | exact fun i hi => absurd hi (Nat.not_lt_zero i) |
            (apply forall_lt_succ; simp only [List.getElem?_set, List.length_set, lw3,
              Nat.reduceEqDiff, Nat.reduceLT, ite_true, ite_false,
              show (0 : BitVec 64) = 0#64 from rfl,
              show (100 : BitVec 64) = 100#64 from rfl,
              show (2000 : BitVec 64) = 2000#64 from rfl,
              show (5000 : BitVec 64) = 5000#64 from rfl]))
      · intro J3 hJ3; c0_hsplit
        · c0_hsteps
          have h0 : mv.toNat = 0 := by rw [hc]; decide
          rw [show (4294967295 : BitVec 64) = ql from by simp [ql, h0]]
          exact hJ3 () m rfl
        · c0_hsteps
          have hnz : mv.toNat ≠ 0 := fun h0 => hc (BitVec.eq_of_toNat_eq (by simpa using h0))
          have hmv1 : mv - 1 = BitVec.ofNat 64 (mv.toNat - 1) := by
            apply BitVec.eq_of_toNat_eq
            have hle1 : (1 : BitVec 64) ≤ mv := by change 1 ≤ mv.toNat; omega
            rw [BitVec.toNat_sub_of_le hle1]; simp; omega
          rw [hmv1, show BitVec.ofNat 64 (mv.toNat - 1) = ql from by simp [ql, hnz]]
          exact hJ3 () m rfl
    · intro J2 hJ2; c0_hsplit
      · c0_hsteps
        have h0 : mv.toNat = 0 := by rw [hc]; decide
        rw [show (4294967295 : BitVec 64) = ql from by simp [ql, h0]]
        exact hJ2 () m rfl
      · c0_hsteps
        have hnz : mv.toNat ≠ 0 := fun h0 => hc (BitVec.eq_of_toNat_eq (by simpa using h0))
        have hmv1 : mv - 1 = BitVec.ofNat 64 (mv.toNat - 1) := by
          apply BitVec.eq_of_toNat_eq
          have hle1 : (1 : BitVec 64) ≤ mv := by change 1 ≤ mv.toNat; omega
          rw [BitVec.toNat_sub_of_le hle1]; simp; omega
        rw [hmv1, show BitVec.ofNat 64 (mv.toNat - 1) = ql from by simp [ql, hnz]]
        exact hJ2 () m rfl
  · intro J1 hJ1; c0_hsplit
    · c0_hsteps
      have h0 : mv.toNat = 0 := by rw [hc]; decide
      rw [show (4294967295 : BitVec 64) = qf from by simp [qf, h0]]
      exact hJ1 () m rfl
    · c0_hsteps
      have hnz : mv.toNat ≠ 0 := fun h0 => hc (BitVec.eq_of_toNat_eq (by simpa using h0))
      rw [show (0 : BitVec 64) = qf from by simp [qf, hnz]]
      exact hJ1 () m rfl

theorem m7PtrsW0_10 (hdr : BitVec 64) (mx : Nat) {w0 : List (BitVec 64)}
    (hw : w0.length = 35) :
    (m7PtrsW0 hdr mx w0)[10]? = some (hdr + BitVec.ofNat 64 (m7FixedBytes mx)) := by
  dsimp only [m7PtrsW0]
  simp only [List.getElem?_set, List.length_set, hw, Nat.reduceEqDiff, Nat.reduceLT,
    ite_true, ite_false, BitVec.add_assoc, ← BitVec.ofNat_add]
  dsimp only [m7FixedBytes]
  refine congrArg (fun x => some (hdr + BitVec.ofNat 64 x)) ?_; omega

theorem full_init_arenas_m7_wp (Γ : Env)
    (hPtrs : EnvSpec Γ "full_init_ptrs_m7" m7InitPtrsSpec) :
    ∀ a m Q X, m7InitArenasSpec a m Q X → Func.wp Γ full_init_arenas_m7_body a m Q X := by
  rintro ⟨h, hdr_addr, mx, avail_dyn, _⟩ m Q X
    ⟨rfl, hmx, hfit, del_cap, ext_cap, scr_cap, w0, w1, w2, w3, R, hd, he, hs, hw1, hw3e, hw3s,
      hm, hpost⟩
  have ⟨lw0, lw1, lw2, lw3, _⟩ := hdrTail4_elim hm
  unfold full_init_arenas_m7_body; dsimp only [Func.wp]
  have hmx_nat : BitVec.ofNat 64 mx.toNat = mx := bv64_self
  have hap_le : fullInitAp avail_dyn.toNat ≤ 134217727 := by
    unfold fullInitAp; exact Nat.min_le_right _ _
  have hap_lt : fullInitAp avail_dyn.toNat < 2 ^ 64 := by omega
  have hrp_lt : fullInitRp avail_dyn.toNat < 2 ^ 64 := by
    unfold fullInitRp; omega
  have hwp_le : fullInitWp avail_dyn.toNat ≤ 134217727 := by
    unfold fullInitWp; exact Nat.min_le_right _ _
  have hwp_lt : fullInitWp avail_dyn.toNat < 2 ^ 64 := by omega
  have hq_sub : fullInitAp avail_dyn.toNat + fullInitRp avail_dyn.toNat ≤ avail_dyn.toNat / 8 := by
    unfold fullInitRp fullInitAp; omega
  c0_hsteps_nogrp
  refine wp_join_state1 (α := Unit) (proj := fun _ => BitVec.ofNat 64 (fullInitAp avail_dyn.toNat))
    (Inv := fun _ m1 => m1 = m) ?_ ?_
  · rintro J1 _ m1 hm1; subst m1; rw [Blocks.get_here]; c0_hsteps_nogrp
    refine wp_join_state1 (α := Unit)
      (proj := fun _ => BitVec.ofNat 64 (fullInitWp avail_dyn.toNat))
      (Inv := fun _ m2 => m2 = m) ?_ ?_
    · rintro J2 _ m2 hm2; subst m2; rw [Blocks.get_here]
      refine ⟨fun r m1 => r = () ∧ (hdrTail4 h (m7PtrsW0 h mx.toNat w0)
        (m7PtrsW1 h mx.toNat w1) (m7PtrsW2 h mx.toNat w2) (m7PtrsW3 h mx.toNat w3) ⋆ R) m1,
        X, ?_, ?_, fun _ _ _ _ h => h⟩
      · apply hPtrs
        exact ⟨rfl, hmx, hfit, w0, w1, w2, w3, R, hm, fun m' hm' => ⟨rfl, hm'⟩⟩
      rintro ⟨⟩ m' ⟨_, hm'⟩
      have ⟨lp0, lp1, lp2, lp3, _⟩ := hdrTail4_elim hm'
      fp_head_steps
      apply hpost
      have h10 : (m7PtrsW0 h mx.toNat w0)[((112 : BitVec 64).toNat - 32) / 8]?.getD 0#64 =
          h + BitVec.ofNat 64 (m7FixedBytes mx.toNat) := by
        rw [show ((112 : BitVec 64).toNat - 32) / 8 = 10 by decide, m7PtrsW0_10 h mx.toNat lw0]; rfl
      have h17 : w1[((448 : BitVec 64).toNat - 312) / 8]?.getD 0#64 =
          BitVec.ofNat 64 del_cap := by
        rw [show ((448 : BitVec 64).toNat - 312) / 8 = 17 by decide, hw1]; rfl
      have h4 : w3[((904 : BitVec 64).toNat - 872) / 8]?.getD 0#64 =
          BitVec.ofNat 64 ext_cap := by
        rw [show ((904 : BitVec 64).toNat - 872) / 8 = 4 by decide, hw3e]; rfl
      have h7 : ∀ v3 v6,
          (((m7PtrsW3 h mx.toNat w3).set 3 v3).set 6 v6)[((928 : BitVec 64).toNat - 872) / 8]?.getD
            0#64 = BitVec.ofNat 64 scr_cap := fun v3 v6 => by
        rw [show ((928 : BitVec 64).toNat - 872) / 8 = 7 by decide]
        simp only [List.getElem?_set]; dsimp only [m7PtrsW3]; simp only [List.getElem?_set]
        rw [hw3s]; rfl
      rw [h10, h17, h4] at hm
      simp only [h7] at hm
      have hrp_bv : (BitVec.ofNat 64 (fullInitAp avail_dyn.toNat) + 5) / 6 =
          BitVec.ofNat 64 (fullInitRp avail_dyn.toNat) := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_udiv, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          show (5 : BitVec 64).toNat = 5 by decide, show (6 : BitVec 64).toNat = 6 by decide,
          Nat.mod_eq_of_lt hap_lt, Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_of_lt (show fullInitRp avail_dyn.toNat < 2 ^ 64 from hrp_lt)]
        rfl
      have hsh1_ap : BitVec.ofNat 64 (fullInitAp avail_dyn.toNat) <<<
          ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64) =
          BitVec.ofNat 64 (2 * fullInitAp avail_dyn.toNat) := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_shiftLeft, show (BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64 = 1
          by decide, Nat.shiftLeft_eq, Nat.pow_one]
        simp only [BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt hap_lt, Nat.mul_comm (fullInitAp avail_dyn.toNat) 2]
      have hsh1_wp : BitVec.ofNat 64 (fullInitWp avail_dyn.toNat) <<<
          ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64) =
          BitVec.ofNat 64 (2 * fullInitWp avail_dyn.toNat) := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_shiftLeft, show (BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64 = 1
          by decide, Nat.shiftLeft_eq, Nat.pow_one]
        simp only [BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt hwp_lt, Nat.mul_comm (fullInitWp avail_dyn.toNat) 2]
      have hsh1_rp : BitVec.ofNat 64 (fullInitRp avail_dyn.toNat) <<<
          ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64) =
          BitVec.ofNat 64 (2 * fullInitRp avail_dyn.toNat) := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_shiftLeft, show (BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64 = 1
          by decide, Nat.shiftLeft_eq, Nat.pow_one]
        simp only [BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt hrp_lt, Nat.mul_comm (fullInitRp avail_dyn.toNat) 2]
      have hsh3_ap : BitVec.ofNat 64 (fullInitAp avail_dyn.toNat) <<<
          ((BitVec.signExtend 64 (3 : BitVec 32)).toNat % 64) =
          BitVec.ofNat 64 (8 * fullInitAp avail_dyn.toNat) := fp_shl_sext3
      have hsh3_wp : BitVec.ofNat 64 (fullInitWp avail_dyn.toNat) <<<
          ((BitVec.signExtend 64 (3 : BitVec 32)).toNat % 64) =
          BitVec.ofNat 64 (8 * fullInitWp avail_dyn.toNat) := fp_shl_sext3
      have hsh3_rp : BitVec.ofNat 64 (fullInitRp avail_dyn.toNat) <<<
          ((BitVec.signExtend 64 (3 : BitVec 32)).toNat % 64) =
          BitVec.ofNat 64 (8 * fullInitRp avail_dyn.toNat) := fp_shl_sext3
      have hsh2_ext : BitVec.ofNat 64 ext_cap <<<
          ((BitVec.signExtend 64 (2 : BitVec 32)).toNat % 64) =
          BitVec.ofNat 64 (4 * ext_cap) := by
        unfold dimacsBound at he; exact bv64_shl2_nat (by omega)
      have hsh2_scr : BitVec.ofNat 64 scr_cap <<<
          ((BitVec.signExtend 64 (2 : BitVec 32)).toNat % 64) =
          BitVec.ofNat 64 (4 * scr_cap) := by
        unfold dimacsBound at hs; exact bv64_shl2_nat (by omega)
      have hsh3_mx : mx <<< ((BitVec.signExtend 64 (3 : BitVec 32)).toNat % 64) =
          BitVec.ofNat 64 (8 * mx.toNat) := by
        have hh := fp_shl_sext3 (n := mx.toNat); rw [hmx_nat] at hh; exact hh
      have h12_del : BitVec.ofNat 64 del_cap * 12 = BitVec.ofNat 64 (12 * del_cap) := by
        rw [show (12 : BitVec 64) = BitVec.ofNat 64 12 from rfl, fp_mul_nat, Nat.mul_comm]
      rw [hrp_bv, hsh1_ap, hsh1_wp, hsh1_rp, hsh3_ap, hsh3_wp, hsh3_rp, hsh2_ext, hsh2_scr,
        hsh3_mx, h12_del] at hm
      simp only [show (2 : BitVec 64) = BitVec.ofNat 64 2 from rfl,
        show (3 : BitVec 64) = BitVec.ofNat 64 3 from rfl,
        show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        show (5 : BitVec 64) = BitVec.ofNat 64 5 from rfl,
        show (6 : BitVec 64) = BitVec.ofNat 64 6 from rfl,
        show (7 : BitVec 64) = BitVec.ofNat 64 7 from rfl,
        fp_mul_nat, BitVec.add_assoc, ← BitVec.ofNat_add] at hm
      refine hdrTail4_congr_set ?_ ?_ ?_ ?_ hm
      · rw [arenas_w0_perm]; dsimp only [m7ArenasW0]
        rw [show (m7PtrsW0 h mx.toNat w0)[10]! = h + BitVec.ofNat 64 (m7FixedBytes mx.toNat) from by
          rw [getElem!_pos (c := m7PtrsW0 h mx.toNat w0) (i := 10) (by simp [m7PtrsW0, lw0])]
          exact Option.some.inj
            ((List.getElem?_eq_getElem (by simp [m7PtrsW0, lw0])).symm.trans
              (m7PtrsW0_10 h mx.toNat lw0))]
        simp only [BitVec.add_assoc, ← BitVec.ofNat_add]
        repeat (first | rfl |
          (refine set_congr ?_ (by
            first | rfl |
              (apply congrArg (fun x => h + BitVec.ofNat 64 x); omega) |
              (apply congrArg (BitVec.ofNat 64); omega))))
      · rw [arenas_w1_perm]; dsimp only [m7ArenasW1]
        simp only [BitVec.add_assoc, ← BitVec.ofNat_add]
        repeat (first | rfl |
          (refine set_congr ?_ (by
            first | rfl |
              (apply congrArg (fun x => h + BitVec.ofNat 64 x); omega) |
              (apply congrArg (BitVec.ofNat 64); omega))))
      · rw [arenas_w2_perm]; dsimp only [m7ArenasW2]
        simp only [BitVec.add_assoc, ← BitVec.ofNat_add]
        repeat (first | rfl |
          (refine set_congr ?_ (by
            first | rfl | (apply congrArg (fun x => h + BitVec.ofNat 64 x); omega))))
      · rw [arenas_w3_perm]; dsimp only [m7ArenasW3]
        simp only [BitVec.add_assoc, ← BitVec.ofNat_add]
        repeat (first | rfl |
          (refine set_congr ?_ (by
            first | rfl | (apply congrArg (fun x => h + BitVec.ofNat 64 x); omega))))
    · intro J2 hJ2; c0_hsplit
      · c0_hsteps
        rw [show BitVec.toNat 134217727 = 134217727 from by decide] at hc
        have h_eq : ((BitVec.ofNat 64 (fullInitAp avail_dyn.toNat) + 5) / 6).toNat =
            fullInitRp avail_dyn.toNat := by
          rw [BitVec.toNat_udiv, BitVec.toNat_add, BitVec.toNat_ofNat,
            show (5 : BitVec 64).toNat = 5 by decide, show (6 : BitVec 64).toNat = 6 by decide,
            Nat.mod_eq_of_lt hap_lt, Nat.mod_eq_of_lt (by omega)]; rfl
        have h_ap_mod : fullInitAp avail_dyn.toNat % 2 ^ 64 = fullInitAp avail_dyn.toNat :=
          Nat.mod_eq_of_lt hap_lt
        have h_shr : avail_dyn.toNat / 2 ^ OfNat.ofNat 3 = avail_dyn.toNat / 8 := by rfl
        rw [h_eq, h_ap_mod, h_shr] at hc
        have h_sub_nat : (2 ^ 64 - fullInitRp avail_dyn.toNat +
            (2 ^ 64 - fullInitAp avail_dyn.toNat + avail_dyn.toNat / 8)) % 2 ^ 64 =
            avail_dyn.toNat / 8 - fullInitAp avail_dyn.toNat - fullInitRp avail_dyn.toNat := by
          omega
        rw [h_sub_nat] at hc
        have hgt : 134217727 < avail_dyn.toNat / 8 - fullInitAp avail_dyn.toNat -
            fullInitRp avail_dyn.toNat := hc
        rw [show (134217727 : BitVec 64) = BitVec.ofNat 64 (fullInitWp avail_dyn.toNat) from by
          unfold fullInitWp; rw [Nat.min_eq_right (Nat.le_of_lt hgt)]; rfl]
        exact hJ2 () m rfl
      · c0_hsteps
        rw [show BitVec.toNat 134217727 = 134217727 from by decide] at hc
        have h_eq : ((BitVec.ofNat 64 (fullInitAp avail_dyn.toNat) + 5) / 6).toNat =
            fullInitRp avail_dyn.toNat := by
          rw [BitVec.toNat_udiv, BitVec.toNat_add, BitVec.toNat_ofNat,
            show (5 : BitVec 64).toNat = 5 by decide, show (6 : BitVec 64).toNat = 6 by decide,
            Nat.mod_eq_of_lt hap_lt, Nat.mod_eq_of_lt (by omega)]; rfl
        have h_ap_mod : fullInitAp avail_dyn.toNat % 2 ^ 64 = fullInitAp avail_dyn.toNat :=
          Nat.mod_eq_of_lt hap_lt
        have h_shr : avail_dyn.toNat / 2 ^ OfNat.ofNat 3 = avail_dyn.toNat / 8 := by rfl
        rw [h_eq, h_ap_mod, h_shr] at hc
        have h_sub_nat : (2 ^ 64 - fullInitRp avail_dyn.toNat +
            (2 ^ 64 - fullInitAp avail_dyn.toNat + avail_dyn.toNat / 8)) % 2 ^ 64 =
            avail_dyn.toNat / 8 - fullInitAp avail_dyn.toNat - fullInitRp avail_dyn.toNat := by
          omega
        rw [h_sub_nat] at hc
        have hle : avail_dyn.toNat / 8 - fullInitAp avail_dyn.toNat -
            fullInitRp avail_dyn.toNat ≤ 134217727 := by omega
        have hw_bv : avail_dyn >>> OfNat.ofNat 3 - BitVec.ofNat 64 (fullInitAp avail_dyn.toNat) -
            (BitVec.ofNat 64 (fullInitAp avail_dyn.toNat) + 5) / 6 =
            BitVec.ofNat 64 (fullInitWp avail_dyn.toNat) := by
          apply BitVec.eq_of_toNat_eq
          have h1 : avail_dyn >>> OfNat.ofNat 3 = BitVec.ofNat 64 (avail_dyn.toNat / 8) := by
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
              show (2 ^ 3 : Nat) = 8 by decide, BitVec.toNat_ofNat]
            exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) avail_dyn.isLt)).symm
          have hrp_eq : (BitVec.ofNat 64 (fullInitAp avail_dyn.toNat) + 5) / 6 =
              BitVec.ofNat 64 (fullInitRp avail_dyn.toNat) := by
            apply BitVec.eq_of_toNat_eq; rw [h_eq, BitVec.toNat_ofNat]
            exact (Nat.mod_eq_of_lt hrp_lt).symm
          rw [h1, hrp_eq]
          have hle1 : BitVec.ofNat 64 (fullInitAp avail_dyn.toNat) ≤
              BitVec.ofNat 64 (avail_dyn.toNat / 8) := by
            change (BitVec.ofNat 64 (fullInitAp avail_dyn.toNat)).toNat ≤
              (BitVec.ofNat 64 (avail_dyn.toNat / 8)).toNat
            rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hap_lt,
              Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) avail_dyn.isLt)]
            omega
          have hle2 : BitVec.ofNat 64 (fullInitRp avail_dyn.toNat) ≤
              BitVec.ofNat 64 (avail_dyn.toNat / 8) -
                BitVec.ofNat 64 (fullInitAp avail_dyn.toNat) := by
            change (BitVec.ofNat 64 (fullInitRp avail_dyn.toNat)).toNat ≤ _
            rw [BitVec.toNat_sub_of_le hle1, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
              BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrp_lt, Nat.mod_eq_of_lt hap_lt,
              Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) avail_dyn.isLt)]
            omega
          rw [BitVec.toNat_sub_of_le hle2, BitVec.toNat_sub_of_le hle1, BitVec.toNat_ofNat,
            BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt hrp_lt, Nat.mod_eq_of_lt hap_lt,
            Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) avail_dyn.isLt),
            Nat.mod_eq_of_lt hwp_lt]
          unfold fullInitWp; rw [Nat.min_eq_left hle]
        rw [hw_bv]; exact hJ2 () m rfl
  · intro J1 hJ1; c0_hsplit
    · c0_hsteps
      rw [show BitVec.toNat 134217727 = 134217727 from by decide] at hc
      have ha_nat : (avail_dyn >>> OfNat.ofNat 3 * 3 / 5).toNat = avail_dyn.toNat / 8 * 3 / 5 := by
        rw [BitVec.toNat_udiv, BitVec.toNat_mul, BitVec.toNat_ushiftRight,
          Nat.shiftRight_eq_div_pow, show (2 ^ 3 : Nat) = 8 by decide,
          show (3 : BitVec 64).toNat = 3 by decide, show (5 : BitVec 64).toNat = 5 by decide]
        have := avail_dyn.isLt
        rw [Nat.mod_eq_of_lt (by omega)]
      rw [ha_nat] at hc
      rw [show (134217727 : BitVec 64) = BitVec.ofNat 64 (fullInitAp avail_dyn.toNat) from by
        unfold fullInitAp; rw [Nat.min_eq_right (Nat.le_of_lt hc)]; rfl]
      exact hJ1 () m rfl
    · c0_hsteps
      rw [show BitVec.toNat 134217727 = 134217727 from by decide] at hc
      have ha_nat : (avail_dyn >>> OfNat.ofNat 3 * 3 / 5).toNat = avail_dyn.toNat / 8 * 3 / 5 := by
        rw [BitVec.toNat_udiv, BitVec.toNat_mul, BitVec.toNat_ushiftRight,
          Nat.shiftRight_eq_div_pow, show (2 ^ 3 : Nat) = 8 by decide,
          show (3 : BitVec 64).toNat = 3 by decide, show (5 : BitVec 64).toNat = 5 by decide]
        have := avail_dyn.isLt
        rw [Nat.mod_eq_of_lt (by omega)]
      rw [ha_nat] at hc
      have ha_bv : avail_dyn >>> OfNat.ofNat 3 * 3 / 5 =
          BitVec.ofNat 64 (fullInitAp avail_dyn.toNat) := by
        apply BitVec.eq_of_toNat_eq
        rw [ha_nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hap_lt]
        unfold fullInitAp; rw [Nat.min_eq_left (by omega)]
      rw [ha_bv]; exact hJ1 () m rfl

/-! ## 5. Defining Equation Lemmas (`public` M1 Interface Without `@[expose]`) -/

theorem m7FixedBytes_eq (max_v : Nat) : m7FixedBytes max_v = 1472 + valsBytes max_v +
    4 * markBytes max_v + 15 * u32FullBytes max_v + 24 * max_v + 8 * fullMinDepthOf max_v := by rfl

theorem m7TransBytes_eq (max_v : Nat) :
    m7TransBytes max_v = 56 * max_v + valsBytes max_v := by rfl

theorem m7CalcExtCap_eq (rem : Nat) : m7CalcExtCap rem =
    if rem < 8192 then 0 else ((min (rem / 32) 4194304) / 2) * 2 := by rfl

theorem m7CalcScrCap_eq (rem : Nat) : m7CalcScrCap rem =
    if rem < 8192 then 0 else
      let raw := if 16384 ≤ rem then rem / 16 else rem / 32; ((min raw 1048576) / 2) * 2 := by rfl

theorem m7BvaCap_eq (avail mv nc f0 : Nat) : m7BvaCap avail mv nc f0 =
    if 2 ≤ mv ∧ nc * 48 + 8192 < avail - f0 then
      min (min (mv / 2 + 16) 4096) (((avail - f0) - nc * 48 - 4096) / 2688)
    else 0 := by rfl

theorem m7CalcMaxV_eq (avail mv nc f0 : Nat) : m7CalcMaxV avail mv nc f0 =
    let cand := mv + m7BvaCap avail mv nc f0; let need := m7FixedBytes cand + m7TransBytes cand
    if avail < need ∨ avail - need < nc * 40 + 136 then mv else cand := by rfl

namespace MemShrinkCfg
section Eq
variable (c : MemShrinkCfg)
theorem minDepth_eq : c.minDepth = fullMinDepthOf c.max_vars := by rfl
theorem pVals_eq : c.pVals = c.hdr + BitVec.ofNat 64 1152 := by rfl
theorem pMark_eq : c.pMark = c.pVals + BitVec.ofNat 64 (valsBytes c.max_vars) := by rfl
theorem pPhases_eq : c.pPhases = c.pMark + BitVec.ofNat 64 (markBytes c.max_vars) := by rfl
theorem pPhasesTarget_eq :
    c.pPhasesTarget = c.pPhases + BitVec.ofNat 64 (markBytes c.max_vars) := by rfl
theorem pPhasesBest_eq :
    c.pPhasesBest = c.pPhasesTarget + BitVec.ofNat 64 (markBytes c.max_vars) := by rfl
theorem pFlags_eq : c.pFlags = c.pPhasesBest + BitVec.ofNat 64 (markBytes c.max_vars) := by rfl
theorem pLevel_eq : c.pLevel = c.pFlags + BitVec.ofNat 64 (u32FullBytes c.max_vars) := by rfl
theorem pReason_eq : c.pReason = c.pLevel + BitVec.ofNat 64 (u32FullBytes c.max_vars) := by rfl
theorem pTrail_eq : c.pTrail = c.pReason + BitVec.ofNat 64 (u32FullBytes c.max_vars) := by rfl
theorem pTrailPos_eq : c.pTrailPos = c.pTrail + BitVec.ofNat 64 (u32FullBytes c.max_vars) := by rfl
theorem pTmp_eq : c.pTmp = c.pTrailPos + BitVec.ofNat 64 (u32FullBytes c.max_vars) := by rfl
theorem pHeap_eq : c.pHeap = c.pTmp + BitVec.ofNat 64 (u32FullBytes c.max_vars) := by rfl
theorem pPos_eq : c.pPos = c.pHeap + BitVec.ofNat 64 (u32FullBytes c.max_vars) := by rfl
theorem pMinClr_eq : c.pMinClr = c.pPos + BitVec.ofNat 64 (u32FullBytes c.max_vars) := by rfl
theorem pShrinkStk_eq :
    c.pShrinkStk = c.pMinClr + BitVec.ofNat 64 (u32FullBytes c.max_vars) := by rfl
theorem pQPrev_eq : c.pQPrev = c.pShrinkStk + BitVec.ofNat 64 (u32FullBytes c.max_vars) := by rfl
theorem pQNext_eq : c.pQNext = c.pQPrev + BitVec.ofNat 64 (u32FullBytes c.max_vars) := by rfl
theorem pQStamp_eq : c.pQStamp = c.pQNext + BitVec.ofNat 64 (u32FullBytes c.max_vars) := by rfl
theorem pFrameTrail_eq :
    c.pFrameTrail = c.pQStamp + BitVec.ofNat 64 (u32FullBytes c.max_vars) := by rfl
theorem pFrameDec_eq :
    c.pFrameDec = c.pFrameTrail + BitVec.ofNat 64 (u32FullBytes c.max_vars) := by rfl
theorem pWvec_eq : c.pWvec = c.pFrameDec + BitVec.ofNat 64 (u32FullBytes c.max_vars) := by rfl
theorem pScore_eq : c.pScore = c.pWvec + BitVec.ofNat 64 (16 * c.max_vars) := by rfl
theorem pMinStk_eq : c.pMinStk = c.pScore + BitVec.ofNat 64 (8 * c.max_vars) := by rfl
theorem pGlueUsed_eq : c.pGlueUsed = c.pMinStk + BitVec.ofNat 64 (8 * c.minDepth) := by rfl
theorem pLastLearned_eq : c.pLastLearned = c.pGlueUsed + BitVec.ofNat 64 256 := by rfl
theorem pArena_eq : c.pArena = c.pLastLearned + BitVec.ofNat 64 64 := by rfl
theorem pWstk_eq : c.pWstk = c.pArena + BitVec.ofNat 64 (4 * c.arena_cap) := by rfl
theorem pDelayed_eq : c.pDelayed = c.pWstk + BitVec.ofNat 64 (4 * c.wcap) := by rfl
theorem pRedRefs_eq : c.pRedRefs = c.pDelayed + BitVec.ofNat 64 (12 * c.delayed_cap) := by rfl
theorem pExtendStk_eq : c.pExtendStk = c.pRedRefs + BitVec.ofNat 64 (4 * c.red_cap) := by rfl
theorem pScratchBuf_eq : c.pScratchBuf = c.pExtendStk + BitVec.ofNat 64 (4 * c.extend_cap) := by rfl
theorem pTrans_eq : c.pTrans = c.pScratchBuf + BitVec.ofNat 64 (4 * c.scratch_cap) := by rfl
theorem pWsort_eq : c.pWsort = c.pTrans := by rfl
theorem pWorkStk1_eq : c.pWorkStk1 = c.pTrans + BitVec.ofNat 64 (8 * c.max_vars) := by rfl
theorem pWorkStk2_eq : c.pWorkStk2 = c.pWorkStk1 + BitVec.ofNat 64 (8 * c.max_vars) := by rfl
theorem pTarjanMark_eq : c.pTarjanMark = c.pWorkStk2 + BitVec.ofNat 64 (8 * c.max_vars) := by rfl
theorem pTarjanReach_eq :
    c.pTarjanReach = c.pTarjanMark + BitVec.ofNat 64 (8 * c.max_vars) := by rfl
theorem pRepr_eq : c.pRepr = c.pTarjanReach + BitVec.ofNat 64 (8 * c.max_vars) := by rfl
theorem pWalkVals_eq : c.pWalkVals = c.pRepr := by rfl
theorem pSimSig_eq : c.pSimSig = c.pRepr + BitVec.ofNat 64 (8 * c.max_vars) := by rfl
theorem pWalkBest_eq : c.pWalkBest = c.pSimSig := by rfl
theorem pLitMark_eq : c.pLitMark = c.pSimSig + BitVec.ofNat 64 (8 * c.max_vars) := by rfl
theorem pSlack_eq : c.pSlack = c.pLitMark + BitVec.ofNat 64 (valsBytes c.max_vars) := by rfl
theorem slack_eq :
    c.slack = c.avail - (m7FixedBytes c.max_vars + m7TransBytes c.max_vars + 4 * c.arena_cap +
      4 * c.wcap + 12 * c.delayed_cap + 4 * c.red_cap + 4 * c.extend_cap + 4 * c.scratch_cap) := by
  rfl
end Eq
end MemShrinkCfg

theorem m7HdrTailWords0_eq (c : MemShrinkCfg) (s : FullState) :
    m7HdrTailWords0 c s =
      let k := s.core; let sc := s.scratch
      [ BitVec.ofNat 64 c.arena_cap, BitVec.ofNat 64 c.wcap, BitVec.ofNat 64 k.arena_len,
        BitVec.ofNat 64 k.wlen, c.pVals, c.pMark, c.pLevel, c.pReason, c.pTrail, c.pWvec,
        c.pArena, c.pWstk, c.pDelayed, c.pTmp, BitVec.ofNat 64 k.trail_end,
        BitVec.ofNat 64 k.propagated, BitVec.ofNat 64 k.cur_level, k.fuel, k.confl_ref,
        BitVec.ofNat 64 k.tmp_cnt, BitVec.ofNat 64 k.tmp_len, c.pHeap, c.pPos, c.pScore,
        c.pPhases, c.pMinStk, c.pMinClr, BitVec.ofNat 64 sc.heap_len, sc.scinc,
        BitVec.ofNat 64 c.minDepth, BitVec.ofNat 64 k.min_clr_len, k.min_clr_full,
        sc.rel_period, sc.rel_limit, sc.rel_wait ] := by rfl

theorem m7HdrTailWords1_eq (c : MemShrinkCfg) (s : FullState) :
    m7HdrTailWords1 c s =
      let k := s.core; let sc := s.scratch
      [ sc.rel_u, sc.rel_v, sc.rel_trigger, sc.conflicts, sc.learned_lits, sc.min_removed,
        c.pTrailPos, c.pQPrev, c.pQNext, c.pQStamp, c.pPhasesTarget, c.pPhasesBest, c.pWsort,
        c.pShrinkStk, c.pRedRefs, c.pGlueUsed, BitVec.ofNat 64 c.red_cap,
        BitVec.ofNat 64 c.delayed_cap, BitVec.ofNat 64 sc.delayed_len, k.wusable,
        k.arena_garbage, k.first_reducible, k.num_irred, k.num_redundant, k.num_binary,
        k.unflushed, k.probing, k.confl_type, k.confl_lit0, k.confl_lit1, sc.stable,
        sc.switched, sc.mode_count, sc.mode_confl_lim, sc.mode_tick_lim ] := by rfl

theorem m7HdrTailWords2_eq (c : MemShrinkCfg) (s : FullState) :
    m7HdrTailWords2 c s =
      let k := s.core; let sc := s.scratch
      [ sc.mode_saved_ticks, sc.search_ticks, sc.q_first, sc.q_last, sc.q_search_idx,
        sc.q_search_stamp, sc.q_cur_stamp, sc.target_assigned, sc.best_assigned,
        sc.rephase_limit, sc.rephased, sc.reduce_limit, sc.reductions, sc.tier1, sc.tier2,
        sc.restarts, sc.restart_limit, sc.ema_fast_biased, sc.ema_fast_exp,
        sc.ema_slow_biased, sc.ema_slow_exp, k.oom, BitVec.ofNat 64 c.max_vars,
        BitVec.ofNat 64 k.cur_vars, BitVec.ofNat 64 c.bva_cap, k.unassigned, c.pFlags,
        c.pLitMark, c.pRepr, c.pSimSig, c.pFrameTrail, c.pFrameDec, c.pWorkStk1, c.pWorkStk2,
        c.pTarjanMark ] := by rfl

theorem m7HdrTailWords3_eq (c : MemShrinkCfg) (s : FullState) :
    m7HdrTailWords3 c s =
      let k := s.core; let sc := s.scratch
      [ c.pTarjanReach, c.pWalkVals, c.pWalkBest, c.pExtendStk, BitVec.ofNat 64 c.extend_cap,
        BitVec.ofNat 64 sc.extend_len, c.pScratchBuf, BitVec.ofNat 64 c.scratch_cap,
        c.pLastLearned, sc.rng_state, sc.chrono_levels, sc.otfs_cnt, sc.eager_sub_cnt,
        sc.probe_limit, sc.probings, sc.elim_limit, sc.eliminations, sc.elim_bound,
        k.dense_mode, k.inconsistent, sc.iterating, sc.hbr_cnt, sc.trans_cnt, sc.viv_cnt,
        sc.subst_cnt, sc.cong_cnt, sc.sweep_cnt, sc.bve_cnt, sc.bce_cnt, sc.bva_cnt,
        sc.walk_cnt_stat, sc.fwd_sub_cnt, sc.fwd_str_cnt, sc.ant_sz, sc.res_sz ] := by rfl

theorem m7HdrTailWords_eq (c : MemShrinkCfg) (s : FullState) :
    m7HdrTailWords c s =
      m7HdrTailWords0 c s ++ m7HdrTailWords1 c s ++ m7HdrTailWords2 c s ++ m7HdrTailWords3 c s := by
  rfl

theorem MemShrinkResBytes_eq (c : MemShrinkCfg) (s : FullState) :
    MemShrinkResBytes c s =
      (array (t := i8) c.pVals s.core.vals ⋆
        region (c.pVals + BitVec.ofNat 64 (2 * c.max_vars))
          (valsBytes c.max_vars - 2 * c.max_vars)) ⋆
      (array (t := i8) c.pMark s.core.mrk ⋆
        region (c.pMark + BitVec.ofNat 64 c.max_vars) (markBytes c.max_vars - c.max_vars)) ⋆
      (array (t := i8) c.pPhases s.scratch.phases ⋆
        region (c.pPhases + BitVec.ofNat 64 c.max_vars) (markBytes c.max_vars - c.max_vars)) ⋆
      (array (t := i8) c.pPhasesTarget s.scratch.phases_target ⋆
        region (c.pPhasesTarget + BitVec.ofNat 64 c.max_vars)
          (markBytes c.max_vars - c.max_vars)) ⋆
      (array (t := i8) c.pPhasesBest s.scratch.phases_best ⋆
        region (c.pPhasesBest + BitVec.ofNat 64 c.max_vars)
          (markBytes c.max_vars - c.max_vars)) := by rfl

theorem MemShrinkResU32A_eq (c : MemShrinkCfg) (s : FullState) :
    MemShrinkResU32A c s =
      (array (t := i32) c.pFlags s.core.flags ⋆
        region (c.pFlags + BitVec.ofNat 64 (4 * c.max_vars))
          (u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
      (array (t := i32) c.pLevel s.core.lvl ⋆
        region (c.pLevel + BitVec.ofNat 64 (4 * c.max_vars))
          (u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
      (array (t := i32) c.pReason s.core.rsns ⋆
        region (c.pReason + BitVec.ofNat 64 (4 * c.max_vars))
          (u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
      (array (t := i32) c.pTrail s.core.trl ⋆
        region (c.pTrail + BitVec.ofNat 64 (4 * c.max_vars))
          (u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
      (array (t := i32) c.pTrailPos s.core.trail_pos ⋆
        region (c.pTrailPos + BitVec.ofNat 64 (4 * c.max_vars))
          (u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
      (array (t := i32) c.pTmp s.core.tmp ⋆
        region (c.pTmp + BitVec.ofNat 64 (4 * c.max_vars))
          (u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
      (array (t := i32) c.pHeap s.scratch.heap ⋆
        region (c.pHeap + BitVec.ofNat 64 (4 * c.max_vars))
          (u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
      (array (t := i32) c.pPos s.scratch.pos ⋆
        region (c.pPos + BitVec.ofNat 64 (4 * c.max_vars))
          (u32FullBytes c.max_vars - 4 * c.max_vars)) := by rfl

theorem MemShrinkResU32B_eq (c : MemShrinkCfg) (s : FullState) :
    MemShrinkResU32B c s =
      (array (t := i32) c.pMinClr s.core.min_clr ⋆
        region (c.pMinClr + BitVec.ofNat 64 (4 * c.max_vars))
          (u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
      (array (t := i32) c.pShrinkStk s.scratch.shrink_stk ⋆
        region (c.pShrinkStk + BitVec.ofNat 64 (4 * c.max_vars))
          (u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
      (array (t := i32) c.pQPrev s.scratch.q_prev ⋆
        region (c.pQPrev + BitVec.ofNat 64 (4 * c.max_vars))
          (u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
      (array (t := i32) c.pQNext s.scratch.q_next ⋆
        region (c.pQNext + BitVec.ofNat 64 (4 * c.max_vars))
          (u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
      (array (t := i32) c.pQStamp s.scratch.q_stamp ⋆
        region (c.pQStamp + BitVec.ofNat 64 (4 * c.max_vars))
          (u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
      (array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
        region (c.pFrameTrail + BitVec.ofNat 64 (4 * (c.max_vars + 1)))
          (u32FullBytes c.max_vars - 4 * (c.max_vars + 1))) ⋆
      (array (t := i32) c.pFrameDec s.core.frame_dec ⋆
        region (c.pFrameDec + BitVec.ofNat 64 (4 * (c.max_vars + 1)))
          (u32FullBytes c.max_vars - 4 * (c.max_vars + 1))) := by rfl

theorem MemShrinkResTail_eq (c : MemShrinkCfg) (s : FullState) :
    MemShrinkResTail c s =
      array (t := i32) c.pWvec s.core.wvec ⋆ array64 c.pScore s.scratch.score ⋆
      array (t := i32) c.pMinStk s.core.min_stk ⋆
      array (t := i32) c.pGlueUsed s.scratch.glue_used ⋆
      array (t := i32) c.pLastLearned s.scratch.last_learned ⋆
      array (t := i32) c.pArena s.core.arena ⋆ array (t := i32) c.pWstk s.core.wstk ⋆
      array (t := i32) c.pDelayed s.scratch.delayed ⋆
      array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
      array (t := i32) c.pExtendStk s.scratch.extend_stk ⋆
      array (t := i32) c.pScratchBuf s.scratch.scratch_buf := by rfl

theorem MemShrinkResArrays_eq (c : MemShrinkCfg) (s : FullState) :
    MemShrinkResArrays c s =
      MemShrinkResBytes c s ⋆ MemShrinkResU32A c s ⋆ MemShrinkResU32B c s ⋆
        MemShrinkResTail c s := by rfl

theorem MemShrinkLitMark_eq (c : MemShrinkCfg) (s : FullState) :
    MemShrinkLitMark c s =
      array (t := i8) c.pLitMark s.core.lit_mark ⋆
      region (c.pLitMark + BitVec.ofNat 64 (2 * c.max_vars))
        (valsBytes c.max_vars - 2 * c.max_vars) := by rfl

theorem MemShrinkTransRegions_eq (c : MemShrinkCfg) :
    MemShrinkTransRegions c =
      region c.pWsort (8 * c.max_vars) ⋆ region c.pWorkStk1 (8 * c.max_vars) ⋆
      region c.pWorkStk2 (8 * c.max_vars) ⋆ region c.pTarjanMark (8 * c.max_vars) ⋆
      region c.pTarjanReach (8 * c.max_vars) ⋆ region c.pRepr (8 * c.max_vars) ⋆
      region c.pSimSig (8 * c.max_vars) := by rfl

theorem MemShrinkMem_eq (c : MemShrinkCfg) (s : FullState) :
    MemShrinkMem c s =
      dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
      array64 (c.hdr + 32) (m7HdrTailWords c s) ⋆ MemShrinkResArrays c s ⋆
      MemShrinkLitMark c s ⋆ MemShrinkTransRegions c ⋆ region c.pSlack c.slack := by rfl

theorem MemShrinkMarksClear_eq (c : MemShrinkCfg) (s : FullState) :
    MemShrinkMarksClear c s =
      ((∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8) ∧
       (∀ l < 2 * c.max_vars, s.core.lit_mark[l]?.getD 0#8 = 0#8)) := by rfl

theorem MemShrinkSparseInv_eq (c : MemShrinkCfg) (s : FullState) :
    MemShrinkSparseInv c s =
      (MemShrinkLengthsOk c s ∧ MemShrinkMarksClear c s ∧
       (∀ i < 8, s.scratch.last_learned[i]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) ∧
       s.scratch.extend_len ≤ c.extend_cap) := by rfl

theorem m7PtrsW0_eq (hdr : BitVec 64) (mx : Nat) (w0 : List (BitVec 64)) :
    m7PtrsW0 hdr mx w0 =
      let pV := hdr + BitVec.ofNat 64 1152
      let pMk := pV + BitVec.ofNat 64 (valsBytes mx)
      let pPh := pMk + BitVec.ofNat 64 (markBytes mx)
      let pPT := pPh + BitVec.ofNat 64 (markBytes mx)
      let pPB := pPT + BitVec.ofNat 64 (markBytes mx)
      let pFl := pPB + BitVec.ofNat 64 (markBytes mx)
      let pLv := pFl + BitVec.ofNat 64 (u32FullBytes mx)
      let pRs := pLv + BitVec.ofNat 64 (u32FullBytes mx)
      let pTr := pRs + BitVec.ofNat 64 (u32FullBytes mx)
      let pTP := pTr + BitVec.ofNat 64 (u32FullBytes mx)
      let pTm := pTP + BitVec.ofNat 64 (u32FullBytes mx)
      let pHp := pTm + BitVec.ofNat 64 (u32FullBytes mx)
      let pPs := pHp + BitVec.ofNat 64 (u32FullBytes mx)
      let pMC := pPs + BitVec.ofNat 64 (u32FullBytes mx)
      let pSS := pMC + BitVec.ofNat 64 (u32FullBytes mx)
      let pQP := pSS + BitVec.ofNat 64 (u32FullBytes mx)
      let pQN := pQP + BitVec.ofNat 64 (u32FullBytes mx)
      let pQS := pQN + BitVec.ofNat 64 (u32FullBytes mx)
      let pFT := pQS + BitVec.ofNat 64 (u32FullBytes mx)
      let pFD := pFT + BitVec.ofNat 64 (u32FullBytes mx)
      let pWv := pFD + BitVec.ofNat 64 (u32FullBytes mx)
      let pSc := pWv + BitVec.ofNat 64 (16 * mx)
      let pMS := pSc + BitVec.ofNat 64 (8 * mx)
      let pGU := pMS + BitVec.ofNat 64 (8 * fullMinDepthOf mx)
      let pLL := pGU + BitVec.ofNat 64 256
      let pAr := pLL + BitVec.ofNat 64 64
      ((((((((((((((w0.set 4 pV).set 5 pMk).set 6 pLv).set 7 pRs).set 8 pTr).set 9 pWv).set 10
        pAr).set 13 pTm).set 21 pHp).set 22 pPs).set 23 pSc).set 24 pPh).set 25 pMS).set 26
        pMC).set 29 (BitVec.ofNat 64 (fullMinDepthOf mx)) := by rfl

theorem m7PtrsW1_eq (hdr : BitVec 64) (mx : Nat) (w1 : List (BitVec 64)) :
    m7PtrsW1 hdr mx w1 =
      let b := hdr + BitVec.ofNat 64 (1152 + valsBytes mx)
      let pMk := b
      let pPh := pMk + BitVec.ofNat 64 (markBytes mx)
      let pPT := pPh + BitVec.ofNat 64 (markBytes mx)
      let pPB := pPT + BitVec.ofNat 64 (markBytes mx)
      let pFl := pPB + BitVec.ofNat 64 (markBytes mx)
      let pTP := pFl + 4#64 * BitVec.ofNat 64 (u32FullBytes mx)
      let pSS := pTP + 5#64 * BitVec.ofNat 64 (u32FullBytes mx)
      let pQP := pSS + BitVec.ofNat 64 (u32FullBytes mx)
      let pQN := pQP + BitVec.ofNat 64 (u32FullBytes mx)
      let pQS := pQN + BitVec.ofNat 64 (u32FullBytes mx)
      let pMS := pQS + 3#64 * BitVec.ofNat 64 (u32FullBytes mx) + BitVec.ofNat 64 (24 * mx)
      let pGU := pMS + BitVec.ofNat 64 (8 * fullMinDepthOf mx)
      (((((((w1.set 6 pTP).set 7 pQP).set 8 pQN).set 9 pQS).set 10 pPT).set 11 pPB).set 13
        pSS).set 15 pGU := by rfl

theorem m7PtrsW2_eq (hdr : BitVec 64) (mx : Nat) (w2 : List (BitVec 64)) :
    m7PtrsW2 hdr mx w2 =
      let pFl := hdr + BitVec.ofNat 64 (1152 + valsBytes mx + 4 * markBytes mx)
      let pFT := pFl + 13#64 * BitVec.ofNat 64 (u32FullBytes mx)
      let pFD := pFT + BitVec.ofNat 64 (u32FullBytes mx)
      ((w2.set 26 pFl).set 30 pFT).set 31 pFD := by rfl

theorem m7PtrsW3_eq (hdr : BitVec 64) (mx : Nat) (w3 : List (BitVec 64)) :
    m7PtrsW3 hdr mx w3 =
      let pGU := hdr + BitVec.ofNat 64 (1152 + valsBytes mx + 4 * markBytes mx +
        15 * u32FullBytes mx + 24 * mx + 8 * fullMinDepthOf mx)
      w3.set 8 (pGU + BitVec.ofNat 64 256) := by rfl

theorem m7ArenasW0_eq (hdr : BitVec 64) (mx avail_dyn : Nat) (w0 : List (BitVec 64)) :
    m7ArenasW0 hdr mx avail_dyn w0 =
      let pAr := (m7PtrsW0 hdr mx w0)[10]!
      let ap := fullInitAp avail_dyn
      let wp := fullInitWp avail_dyn
      let pWs := pAr + BitVec.ofNat 64 (8 * ap)
      ((((m7PtrsW0 hdr mx w0).set 0 (BitVec.ofNat 64 (2 * ap))).set 1
        (BitVec.ofNat 64 (2 * wp))).set 11 pWs).set 12 (pWs + BitVec.ofNat 64 (8 * wp)) := by rfl

theorem m7ArenasW1_eq (hdr : BitVec 64) (mx avail_dyn del_cap ext_cap scr_cap : Nat)
    (w1 : List (BitVec 64)) :
    m7ArenasW1 hdr mx avail_dyn del_cap ext_cap scr_cap w1 =
      let pAr := hdr + BitVec.ofNat 64 (m7FixedBytes mx)
      let ap := fullInitAp avail_dyn
      let rp := fullInitRp avail_dyn
      let wp := fullInitWp avail_dyn
      let pDl := pAr + BitVec.ofNat 64 (8 * ap + 8 * wp)
      let pRr := pDl + BitVec.ofNat 64 (12 * del_cap)
      let pTr := pRr + BitVec.ofNat 64 (8 * rp + 4 * ext_cap + 4 * scr_cap)
      (((m7PtrsW1 hdr mx w1).set 12 pTr).set 14 pRr).set 16 (BitVec.ofNat 64 (2 * rp)) := by rfl

theorem m7ArenasW2_eq (hdr : BitVec 64) (mx avail_dyn del_cap ext_cap scr_cap : Nat)
    (w2 : List (BitVec 64)) :
    m7ArenasW2 hdr mx avail_dyn del_cap ext_cap scr_cap w2 =
      let pAr := hdr + BitVec.ofNat 64 (m7FixedBytes mx)
      let ap := fullInitAp avail_dyn
      let rp := fullInitRp avail_dyn
      let wp := fullInitWp avail_dyn
      let pTr := pAr + BitVec.ofNat 64 (8 * ap + 8 * wp + 12 * del_cap + 8 * rp + 4 * ext_cap +
        4 * scr_cap)
      ((((((m7PtrsW2 hdr mx w2).set 27 (pTr + BitVec.ofNat 64 (56 * mx))).set 28
        (pTr + BitVec.ofNat 64 (40 * mx))).set 29 (pTr + BitVec.ofNat 64 (48 * mx))).set 32
        (pTr + BitVec.ofNat 64 (8 * mx))).set 33 (pTr + BitVec.ofNat 64 (16 * mx))).set 34
        (pTr + BitVec.ofNat 64 (24 * mx)) := by rfl

theorem m7ArenasW3_eq (hdr : BitVec 64) (mx avail_dyn del_cap ext_cap scr_cap : Nat)
    (w3 : List (BitVec 64)) :
    m7ArenasW3 hdr mx avail_dyn del_cap ext_cap scr_cap w3 =
      let pAr := hdr + BitVec.ofNat 64 (m7FixedBytes mx)
      let ap := fullInitAp avail_dyn
      let rp := fullInitRp avail_dyn
      let wp := fullInitWp avail_dyn
      let pEx := pAr + BitVec.ofNat 64 (8 * ap + 8 * wp + 12 * del_cap + 8 * rp)
      let pSc := pEx + BitVec.ofNat 64 (4 * ext_cap)
      let pTr := pSc + BitVec.ofNat 64 (4 * scr_cap)
      (((((m7PtrsW3 hdr mx w3).set 0 (pTr + BitVec.ofNat 64 (32 * mx))).set 1
        (pTr + BitVec.ofNat 64 (40 * mx))).set 2 (pTr + BitVec.ofNat 64 (48 * mx))).set 3 pEx).set
        6 pSc := by rfl

theorem m7HdrW0_eq (mv : Nat) (fuel : BitVec 64) (w0 : List (BitVec 64)) :
    m7HdrW0 mv fuel w0 =
      (((((((((((((((w0.set 2 0#64).set 3 1#64).set 14 0#64).set 15 0#64).set 16 0#64).set 17
        fuel).set 18 0xFFFFFFFF#64).set 19 0#64).set 20 0#64).set 27 (BitVec.ofNat 64 mv)).set 28
        (1#64 <<< 28)).set 30 0#64).set 31 0#64).set 32 1024#64).set 33 1048576#64).set 34
        1024#64 := by rfl

theorem m7HdrW1_eq (w1 : List (BitVec 64)) :
    m7HdrW1 w1 =
      ((((((((((((((((((((((w1.set 0 1#64).set 1 1#64).set 2 0#64).set 3 0#64).set 4 0#64).set 5
        0#64).set 18 0#64).set 19 0#64).set 20 0#64).set 21 0xFFFFFFFF#64).set 22 0#64).set 23
        0#64).set 24 0#64).set 25 0#64).set 26 0#64).set 27 0#64).set 28 0#64).set 29 0#64).set
        30 0#64).set 31 0#64).set 32 0#64).set 33 1000#64).set 34 0#64 := by rfl

theorem m7HdrW2_eq (mv mx : Nat) (w2 : List (BitVec 64)) :
    m7HdrW2 mv mx w2 =
      let qf := if mv == 0 then 0xFFFFFFFF#64 else 0#64
      let ql := if mv == 0 then 0xFFFFFFFF#64 else BitVec.ofNat 64 (mv - 1)
      (((((((((((((((((((((((((w2.set 0 0#64).set 1 0#64).set 2 qf).set 3 ql).set 4 ql).set 5
        (BitVec.ofNat 64 mv)).set 6 (BitVec.ofNat 64 mv)).set 7 0#64).set 8 0#64).set 9
        1000#64).set 10 0#64).set 11 1000#64).set 12 0#64).set 13 2#64).set 14 6#64).set 15
        0#64).set 16 1#64).set 17 0#64).set 18 (1#64 <<< 24)).set 19 0#64).set 20
        (1#64 <<< 24)).set 21 0#64).set 22 (BitVec.ofNat 64 mx)).set 23 (BitVec.ofNat 64 mv)).set
        24 (BitVec.ofNat 64 (mx - mv))).set 25 (BitVec.ofNat 64 mv) := by rfl

theorem m7HdrW3_eq (mv : Nat) (w3 : List (BitVec 64)) :
    m7HdrW3 mv w3 =
      let rng := 0x9E3779B97F4A7C15#64 ^^^ BitVec.ofNat 64 (mv + 1)
      ((((((((((((((((((((((((((w3.set 5 0#64).set 9 rng).set 10 100#64).set 11 0#64).set 12
        0#64).set 13 2000#64).set 14 0#64).set 15 5000#64).set 16 0#64).set 17 0#64).set 18
        0#64).set 19 0#64).set 20 0#64).set 21 0#64).set 22 0#64).set 23 0#64).set 24 0#64).set 25
        0#64).set 26 0#64).set 27 0#64).set 28 0#64).set 29 0#64).set 30 0#64).set 31 0#64).set 32
        0#64).set 33 0#64).set 34 0#64 := by rfl

theorem envSpec_eq (Γ : Env) (nm : String) {as rs : List Ty} (sp : Spec as rs) :
    EnvSpec Γ nm sp = (∀ a m Q X, sp a m Q X → Γ nm as rs a m Q X) := by rfl

theorem m7FillU64Spec_eq (a : Tup Val [i64, i64, i64]) (m : Mem 64)
    (Q : Post []) (X : XPost) :
    m7FillU64Spec a m Q X =
      ∃ (xs : List (BitVec 64)) (R : Mem 64 → Prop),
        a.2.1.toNat = xs.length ∧ a.1.toNat + 8 * xs.length ≤ 2 ^ 64 ∧
        (array64 a.1 xs ⋆ R) m ∧
        (∀ m', (array64 a.1 (List.replicate a.2.1.toNat a.2.2.1) ⋆ R) m' → Q () m') := by rfl

theorem m7ZeroTables1Spec_eq (hdr : BitVec 64) (m : Mem 64) (Q : Post []) (X : XPost) :
    m7ZeroTables1Spec (hdr, ()) m Q X =
      ∃ (c : MemShrinkCfg) (s : FullState) (R : Mem 64 → Prop),
        hdr = c.hdr ∧ MemShrinkLengthsOk c s ∧ (MemShrinkMem c s ⋆ R) m ∧
        (∀ s' m',
          FullHdrScalarsEq s' s →
          s'.core.vals = List.replicate (2 * c.max_vars) 0#8 →
          s'.core.lit_mark = List.replicate (2 * c.max_vars) 0#8 →
          s'.core.wvec = List.replicate (4 * c.max_vars) 0#32 →
          s'.core.min_stk = List.replicate (2 * c.minDepth) 0#32 →
          s'.scratch.glue_used = List.replicate 64 0#32 →
          s'.scratch.last_learned = List.replicate 16 0xFFFFFFFF#32 →
          MemShrinkLengthsOk c s' → (MemShrinkMem c s' ⋆ R) m' → Q () m') := by rfl

theorem m7ZeroTables2Spec_eq (hdr : BitVec 64) (m : Mem 64) (Q : Post []) (X : XPost) :
    m7ZeroTables2Spec (hdr, ()) m Q X =
      ∃ (c : MemShrinkCfg) (s : FullState) (R : Mem 64 → Prop),
        hdr = c.hdr ∧ MemShrinkLengthsOk c s ∧ (MemShrinkMem c s ⋆ R) m ∧
        (∀ s' m',
          FullHdrScalarsEq s' s →
          s'.core.vals = s.core.vals → s'.core.lit_mark = s.core.lit_mark →
          s'.core.wvec = s.core.wvec → s'.core.min_stk = s.core.min_stk →
          s'.scratch.glue_used = s.scratch.glue_used →
          s'.scratch.last_learned = s.scratch.last_learned →
          s'.core.mrk = List.replicate c.max_vars 0#8 →
          MemShrinkLengthsOk c s' → (MemShrinkMem c s' ⋆ R) m' → Q () m') := by rfl

theorem m7InitStateSpec_eq (cnf_ptr cend hdr_addr avail fuel : BitVec 64)
    (m : Mem 64) (Q : Post [.bool]) (X : XPost) :
    m7InitStateSpec (cnf_ptr, cend, hdr_addr, avail, fuel, ()) m Q X =
      ∃ (cnfBytes : List UInt8) (R : Mem 64 → Prop),
        cend = cnf_ptr + BitVec.ofNat 64 cnfBytes.length ∧
        cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
        hdr_addr.toNat + avail.toNat < 2 ^ 64 ∧
        1152 ≤ avail.toNat ∧
        (bytes cnf_ptr cnfBytes ⋆ region hdr_addr avail.toNat ⋆ R) m ∧
        (∀ m', (bytes cnf_ptr cnfBytes ⋆ region hdr_addr avail.toNat ⋆ R) m' →
          (∀ mv nc rest, parseHeader cnfBytes = some (mv, nc, rest) →
            avail.toNat < m7FixedBytes mv + m7TransBytes mv + nc * 40 + 136) →
          Q (false, ()) m') ∧
        (∀ (c : MemShrinkCfg) (s : FullState) (j : Nat) (rest : List UInt8) (m' : Mem 64),
          c.hdr = hdr_addr → c.avail = avail.toNat →
          parseHeader cnfBytes = some (c.mv, c.nc, rest) →
          j ≤ cnfBytes.length → List.drop j cnfBytes = rest →
          MemShrinkSparseInv c s →
          s.core.cur_vars = c.mv → s.core.unassigned = c.mv →
          s.core.d_cur = cnf_ptr + BitVec.ofNat 64 j → s.core.d_val = BitVec.ofNat 64 c.nc →
          s.core.arena_len = 0 → s.core.wlen = 1 →
          s.core.trail_end = 0 → s.core.propagated = 0 → s.core.cur_level = 0 →
          s.core.fuel = fuel → s.core.confl_ref = 0xFFFFFFFF#64 →
          s.core.tmp_cnt = 0 → s.core.tmp_len = 0 → s.core.min_clr_len = 0 →
          s.core.min_clr_full = 0#64 → s.core.oom = 0#64 → s.core.inconsistent = 0#64 →
          s.core.num_irred = 0#64 → s.core.num_redundant = 0#64 →
          s.core.num_binary = 0#64 →
          s.core.unflushed = 0#64 → s.core.probing = 0#64 → s.core.dense_mode = 0#64 →
          s.core.vals = List.replicate (2 * c.max_vars) 0#8 →
          s.core.wvec = List.replicate (4 * c.max_vars) 0#32 →
          s.core.mrk = List.replicate c.max_vars 0#8 →
          s.core.lit_mark = List.replicate (2 * c.max_vars) 0#8 →
          s.scratch.extend_len = 0 →
          s.scratch.probe_limit = 2000#64 → s.scratch.elim_limit = 5000#64 →
          (bytes cnf_ptr cnfBytes ⋆ MemShrinkMem c s ⋆ R) m' → Q (true, ()) m') := by rfl

theorem m7FixedBytesSpec_eq (a : Tup Val [i64]) (m : Mem 64) (Q : Post [i64]) (X : XPost) :
    m7FixedBytesSpec a m Q X =
      (a.1.toNat < 2 * dimacsBound ∧ Q (BitVec.ofNat 64 (m7FixedBytes a.1.toNat), ()) m) := by rfl

theorem m7TransBytesSpec_eq (a : Tup Val [i64]) (m : Mem 64) (Q : Post [i64]) (X : XPost) :
    m7TransBytesSpec a m Q X =
      (a.1.toNat < 2 * dimacsBound ∧ Q (BitVec.ofNat 64 (m7TransBytes a.1.toNat), ()) m) := by rfl

theorem m7CalcExtCapSpec_eq (a : Tup Val [i64]) (m : Mem 64) (Q : Post [i64]) (X : XPost) :
    m7CalcExtCapSpec a m Q X = Q (BitVec.ofNat 64 (m7CalcExtCap a.1.toNat), ()) m := by rfl

theorem m7CalcScrCapSpec_eq (a : Tup Val [i64]) (m : Mem 64) (Q : Post [i64]) (X : XPost) :
    m7CalcScrCapSpec a m Q X = Q (BitVec.ofNat 64 (m7CalcScrCap a.1.toNat), ()) m := by rfl

theorem m7CalcMaxVSpec_eq (avail mv nc f0 : BitVec 64) (m : Mem 64) (Q : Post [i64]) (X : XPost) :
    m7CalcMaxVSpec (avail, mv, nc, f0, ()) m Q X =
      (mv.toNat < dimacsBound ∧ nc.toNat < dimacsBound ∧ f0.toNat ≤ avail.toNat ∧
       Q (BitVec.ofNat 64 (m7CalcMaxV avail.toNat mv.toNat nc.toNat f0.toNat), ()) m) := by rfl

theorem m7InitPtrsSpec_eq (h hdr_addr mx : BitVec 64) (m : Mem 64) (Q : Post []) (X : XPost) :
    m7InitPtrsSpec (h, hdr_addr, mx, ()) m Q X =
      (h = hdr_addr ∧ mx.toNat < 2 * dimacsBound ∧
       hdr_addr.toNat + m7FixedBytes mx.toNat < 2 ^ 64 ∧
       ∃ w0 w1 w2 w3 R, (hdrTail4 hdr_addr w0 w1 w2 w3 ⋆ R) m ∧
         (∀ m', (hdrTail4 hdr_addr (m7PtrsW0 hdr_addr mx.toNat w0) (m7PtrsW1 hdr_addr mx.toNat w1)
           (m7PtrsW2 hdr_addr mx.toNat w2) (m7PtrsW3 hdr_addr mx.toNat w3) ⋆ R) m' →
           Q () m')) := by rfl

theorem m7InitHdrSpec_eq (h mv mx fuel : BitVec 64) (m : Mem 64) (Q : Post []) (X : XPost) :
    m7InitHdrSpec (h, mv, mx, fuel, ()) m Q X =
      (mv.toNat ≤ mx.toNat ∧ mx.toNat < 2 * dimacsBound ∧
       ∃ w0 w1 w2 w3 R, (hdrTail4 h w0 w1 w2 w3 ⋆ R) m ∧
         (∀ m', (hdrTail4 h (m7HdrW0 mv.toNat fuel w0) (m7HdrW1 w1)
           (m7HdrW2 mv.toNat mx.toNat w2) (m7HdrW3 mv.toNat w3) ⋆ R) m' → Q () m')) := by rfl

theorem m7InitArenasSpec_eq (h hdr_addr mx avail_dyn : BitVec 64)
    (m : Mem 64) (Q : Post []) (X : XPost) :
    m7InitArenasSpec (h, hdr_addr, mx, avail_dyn, ()) m Q X =
      (h = hdr_addr ∧ mx.toNat < 2 * dimacsBound ∧
       hdr_addr.toNat + m7FixedBytes mx.toNat < 2 ^ 64 ∧
       ∃ del_cap ext_cap scr_cap w0 w1 w2 w3 R,
         del_cap < dimacsBound ∧ ext_cap < dimacsBound ∧ scr_cap < dimacsBound ∧
         w1[17]? = some (BitVec.ofNat 64 del_cap) ∧
         w3[4]? = some (BitVec.ofNat 64 ext_cap) ∧
         w3[7]? = some (BitVec.ofNat 64 scr_cap) ∧
         (hdrTail4 hdr_addr w0 w1 w2 w3 ⋆ R) m ∧
         (∀ m', (hdrTail4 hdr_addr
           (m7ArenasW0 hdr_addr mx.toNat avail_dyn.toNat w0)
           (m7ArenasW1 hdr_addr mx.toNat avail_dyn.toNat del_cap ext_cap scr_cap w1)
           (m7ArenasW2 hdr_addr mx.toNat avail_dyn.toNat del_cap ext_cap scr_cap w2)
           (m7ArenasW3 hdr_addr mx.toNat avail_dyn.toNat del_cap ext_cap scr_cap w3) ⋆ R) m' →
           Q () m')) := by rfl

theorem m7FixedBytes_def (n : Nat) :
    m7FixedBytes n = valsBytes n + 4 * markBytes n + 15 * u32FullBytes n + 24 * n +
      8 * fullMinDepthOf n + 1472 := by unfold m7FixedBytes; omega

theorem m7TransBytes_def (n : Nat) :
    m7TransBytes n = 56 * n + valsBytes n := by unfold m7TransBytes; omega

theorem m7_init_sparse_inv (c : MemShrinkCfg) {sF : FullState}
    (hlen : MemShrinkLengthsOk c sF) (hmrk : sF.core.mrk = List.replicate c.max_vars 0#8)
    (hlm : sF.core.lit_mark = List.replicate (2 * c.max_vars) 0#8)
    (hll : sF.scratch.last_learned = List.replicate 16 0xFFFFFFFF#32)
    (hext : sF.scratch.extend_len = 0) : MemShrinkSparseInv c sF := by
  refine ⟨hlen, ⟨fun v hv => ?_, fun l hl => ?_⟩, fun i hi => ?_, by omega⟩
  · simp only [hmrk, List.getElem?_replicate, hv, ↓reduceIte, Option.getD_some]
  · simp only [hlm, List.getElem?_replicate, hl, ↓reduceIte, Option.getD_some]
  · simp only [hll, List.getElem?_replicate, show i < 16 by omega, ↓reduceIte, Option.getD_some]
