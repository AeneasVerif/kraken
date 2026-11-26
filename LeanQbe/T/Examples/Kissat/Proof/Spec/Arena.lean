/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
public import LeanQbe.T.Examples.Kissat.Ref.Chrono
public import LeanQbe.T.Logic.C0Agrees
public import Kraken.SeparationTactics
public import Kraken.Mem
public import Kraken.Separation
import LeanQbe.T.Logic.SlabChain
meta import Lean.Elab.Command

/-!
# Kissat `D-Full` Arena Layout, State, Indexed Field Tables, and Memory Bridges (`Stage 4`)

Defines:
1. `fullMinDepthOf`, `u32FullBytes`, `fullFixedBytes`, `FullCfg` matching frozen `FullHdr`
   (`144` `u64` words = `1,152` bytes, offsets `0..1144`, `41` contiguous arrays), and
   `SlabChain`-backed `regions_to_avail`.
2. Named `FullScratch`, `FullCoreState`, and `FullState` structures with `LengthsOk`.
3. Single-source-of-truth indexed `HdrWordField` (`144` words) and `ArrayField` (`41` arrays)
   tables with `hdrTailWords`, `ofOff?` lookup, and `O(1)` `ArrayField.focus` / `unfocus` bridges.
4. `FullMem`, `FullArenaInv`, `FullCheckRest`, `fullMem_anyDimacs_to_region`, `check_model`
   framing bridges, and `C0Agrees.SafetySlice` instantiations.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Spec

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

/-! ## 1. Arithmetic, alignment, and `FullHdr` layout sizes -/

@[expose] def fullMinDepthOf (max_v : Nat) : Nat :=
  if max_v + 1 < 1000 then max_v + 1 else 1000

/-- Rounded 8-byte-aligned size for `u32[max_v + 1]` tables (`frame_trail`, `frame_dec`,
and all `u32[max_v]` tables) matching `full_init_ptrs`. -/
@[expose] def u32FullBytes (max_v : Nat) : Nat := ((4 * (max_v + 1) + 7) / 8) * 8

/-- Fixed byte footprint required by `full_init_state` (`sizeof(FullHdr) = 1152`,
`glue_used = 256`, `last_learned = 64`, plus variable tables up to `max_v`). -/
@[expose] def fullFixedBytes (max_v : Nat) : Nat :=
  1472 + 3 * valsBytes max_v + 5 * markBytes max_v + 15 * u32FullBytes max_v +
    80 * max_v + 8 * fullMinDepthOf max_v

theorem fullMinDepthOf_pos (max_v : Nat) : 1 ≤ fullMinDepthOf max_v := by
  unfold fullMinDepthOf; split <;> omega

theorem fullMinDepthOf_le (max_v : Nat) : fullMinDepthOf max_v ≤ 1000 := by
  unfold fullMinDepthOf; split <;> omega

theorem u32FullBytes_ge (max_v : Nat) : 4 * (max_v + 1) ≤ u32FullBytes max_v := by
  unfold u32FullBytes; omega

theorem u32FullBytes_ge4 (max_v : Nat) : 4 * max_v ≤ u32FullBytes max_v := by
  unfold u32FullBytes; omega

theorem u32FullBytes_le (max_v : Nat) : u32FullBytes max_v ≤ 4 * max_v + 11 := by
  unfold u32FullBytes; omega

theorem fullFixedBytes_lt {max_v : Nat} (hmax : max_v < 2 * dimacsBound) :
    fullFixedBytes max_v < 2 ^ 38 := by
  unfold fullFixedBytes valsBytes markBytes u32FullBytes fullMinDepthOf dimacsBound at *
  split <;> omega

@[expose] def fullAlignPad (p : BitVec 64) : Nat :=
  if p.toNat % 8 = 0 then 0 else 8 - p.toNat % 8

theorem fullAlignPad_lt8 (p : BitVec 64) : fullAlignPad p < 8 := by
  unfold fullAlignPad; split <;> omega

theorem fullAlignPad_eq (p : BitVec 64) :
    ((8#64 - (p &&& 7#64)) &&& 7#64).toNat = fullAlignPad p := by
  unfold fullAlignPad
  have hmod : (p &&& 7#64).toNat = p.toNat % 8 := by
    rw [BitVec.toNat_and, show (7#64).toNat = 7 by rfl]
    simpa using Nat.and_two_pow_sub_one_eq_mod p.toNat 3
  have hp : p &&& 7#64 = BitVec.ofNat 64 (p.toNat % 8) := by
    apply BitVec.eq_of_toNat_eq
    rw [hmod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : p.toNat % 8 < 2 ^ 64)]
  rw [hp]
  by_cases hz : p.toNat % 8 = 0
  · simp [hz]
  · have hsub : 8#64 - BitVec.ofNat 64 (p.toNat % 8) = BitVec.ofNat 64 (8 - p.toNat % 8) :=
      bv_sub_ofNat (a := 8) (b := p.toNat % 8) (by omega) (by decide)
    rw [hsub, BitVec.toNat_and, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 8 - p.toNat % 8 < 2 ^ 64), show (7#64).toNat = 7 by rfl]
    have h2 : (8 - p.toNat % 8) &&& 7 = (8 - p.toNat % 8) % 8 := by
      simpa using Nat.and_two_pow_sub_one_eq_mod (8 - p.toNat % 8) 3
    rw [h2]; simp [hz]; omega

/-! ## 2. `FullCfg` arena geometry (`FullHdr` = `144` words, `41` arrays) -/

/-- Static arena geometry established by `full_init_state` in `Full1`. -/
structure FullCfg where
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
  hsize : fullFixedBytes max_vars + 4 * arena_cap + 4 * wcap + 12 * delayed_cap +
    4 * red_cap + 4 * extend_cap + 4 * scratch_cap ≤ avail

namespace FullCfg

@[expose] def minDepth (c : FullCfg) : Nat := fullMinDepthOf c.max_vars

@[expose] def pVals (c : FullCfg) : BitVec 64 := c.hdr + BitVec.ofNat 64 1152
@[expose]
def pWalkVals (c : FullCfg) : BitVec 64 := c.pVals + BitVec.ofNat 64 (valsBytes c.max_vars)
@[expose]
def pLitMark (c : FullCfg) : BitVec 64 := c.pWalkVals + BitVec.ofNat 64 (valsBytes c.max_vars)
@[expose] def pMark (c : FullCfg) : BitVec 64 := c.pLitMark + BitVec.ofNat 64 (valsBytes c.max_vars)
@[expose] def pPhases (c : FullCfg) : BitVec 64 := c.pMark + BitVec.ofNat 64 (markBytes c.max_vars)
@[expose] def pPhasesTarget (c : FullCfg) : BitVec 64 :=
  c.pPhases + BitVec.ofNat 64 (markBytes c.max_vars)
@[expose] def pPhasesBest (c : FullCfg) : BitVec 64 :=
  c.pPhasesTarget + BitVec.ofNat 64 (markBytes c.max_vars)
@[expose] def pWalkBest (c : FullCfg) : BitVec 64 :=
  c.pPhasesBest + BitVec.ofNat 64 (markBytes c.max_vars)
@[expose]
def pFlags (c : FullCfg) : BitVec 64 := c.pWalkBest + BitVec.ofNat 64 (markBytes c.max_vars)
@[expose]
def pLevel (c : FullCfg) : BitVec 64 := c.pFlags + BitVec.ofNat 64 (u32FullBytes c.max_vars)
@[expose]
def pReason (c : FullCfg) : BitVec 64 := c.pLevel + BitVec.ofNat 64 (u32FullBytes c.max_vars)
@[expose]
def pTrail (c : FullCfg) : BitVec 64 := c.pReason + BitVec.ofNat 64 (u32FullBytes c.max_vars)
@[expose]
def pTrailPos (c : FullCfg) : BitVec 64 := c.pTrail + BitVec.ofNat 64 (u32FullBytes c.max_vars)
@[expose]
def pTmp (c : FullCfg) : BitVec 64 := c.pTrailPos + BitVec.ofNat 64 (u32FullBytes c.max_vars)
@[expose] def pHeap (c : FullCfg) : BitVec 64 := c.pTmp + BitVec.ofNat 64 (u32FullBytes c.max_vars)
@[expose] def pPos (c : FullCfg) : BitVec 64 := c.pHeap + BitVec.ofNat 64 (u32FullBytes c.max_vars)
@[expose]
def pMinClr (c : FullCfg) : BitVec 64 := c.pPos + BitVec.ofNat 64 (u32FullBytes c.max_vars)
@[expose] def pShrinkStk (c : FullCfg) : BitVec 64 :=
  c.pMinClr + BitVec.ofNat 64 (u32FullBytes c.max_vars)
@[expose] def pQPrev (c : FullCfg) : BitVec 64 :=
  c.pShrinkStk + BitVec.ofNat 64 (u32FullBytes c.max_vars)
@[expose]
def pQNext (c : FullCfg) : BitVec 64 := c.pQPrev + BitVec.ofNat 64 (u32FullBytes c.max_vars)
@[expose]
def pQStamp (c : FullCfg) : BitVec 64 := c.pQNext + BitVec.ofNat 64 (u32FullBytes c.max_vars)
@[expose] def pFrameTrail (c : FullCfg) : BitVec 64 :=
  c.pQStamp + BitVec.ofNat 64 (u32FullBytes c.max_vars)
@[expose] def pFrameDec (c : FullCfg) : BitVec 64 :=
  c.pFrameTrail + BitVec.ofNat 64 (u32FullBytes c.max_vars)
@[expose]
def pWvec (c : FullCfg) : BitVec 64 := c.pFrameDec + BitVec.ofNat 64 (u32FullBytes c.max_vars)
@[expose] def pRepr (c : FullCfg) : BitVec 64 := c.pWvec + BitVec.ofNat 64 (16 * c.max_vars)
@[expose] def pWsort (c : FullCfg) : BitVec 64 := c.pRepr + BitVec.ofNat 64 (8 * c.max_vars)
@[expose] def pWorkStk1 (c : FullCfg) : BitVec 64 := c.pWsort + BitVec.ofNat 64 (8 * c.max_vars)
@[expose] def pWorkStk2 (c : FullCfg) : BitVec 64 := c.pWorkStk1 + BitVec.ofNat 64 (8 * c.max_vars)
@[expose]
def pTarjanMark (c : FullCfg) : BitVec 64 := c.pWorkStk2 + BitVec.ofNat 64 (8 * c.max_vars)
@[expose] def pTarjanReach (c : FullCfg) : BitVec 64 :=
  c.pTarjanMark + BitVec.ofNat 64 (8 * c.max_vars)
@[expose] def pScore (c : FullCfg) : BitVec 64 := c.pTarjanReach + BitVec.ofNat 64 (8 * c.max_vars)
@[expose] def pSimSig (c : FullCfg) : BitVec 64 := c.pScore + BitVec.ofNat 64 (8 * c.max_vars)
@[expose] def pMinStk (c : FullCfg) : BitVec 64 := c.pSimSig + BitVec.ofNat 64 (8 * c.max_vars)
@[expose] def pGlueUsed (c : FullCfg) : BitVec 64 := c.pMinStk + BitVec.ofNat 64 (8 * c.minDepth)
@[expose] def pLastLearned (c : FullCfg) : BitVec 64 := c.pGlueUsed + BitVec.ofNat 64 256
@[expose] def pArena (c : FullCfg) : BitVec 64 := c.pLastLearned + BitVec.ofNat 64 64
@[expose] def pWstk (c : FullCfg) : BitVec 64 := c.pArena + BitVec.ofNat 64 (4 * c.arena_cap)
@[expose] def pDelayed (c : FullCfg) : BitVec 64 := c.pWstk + BitVec.ofNat 64 (4 * c.wcap)
@[expose]
def pRedRefs (c : FullCfg) : BitVec 64 := c.pDelayed + BitVec.ofNat 64 (12 * c.delayed_cap)
@[expose] def pExtendStk (c : FullCfg) : BitVec 64 := c.pRedRefs + BitVec.ofNat 64 (4 * c.red_cap)
@[expose]
def pScratchBuf (c : FullCfg) : BitVec 64 := c.pExtendStk + BitVec.ofNat 64 (4 * c.extend_cap)
@[expose]
def pSlack (c : FullCfg) : BitVec 64 := c.pScratchBuf + BitVec.ofNat 64 (4 * c.scratch_cap)

@[expose] def slack (c : FullCfg) : Nat :=
  c.avail - (fullFixedBytes c.max_vars + 4 * c.arena_cap + 4 * c.wcap + 12 * c.delayed_cap +
    4 * c.red_cap + 4 * c.extend_cap + 4 * c.scratch_cap)

@[expose] def padBytes (c : FullCfg) : Mem 64 → Prop :=
  region (c.pVals + BitVec.ofNat 64 (2 * c.max_vars)) (valsBytes c.max_vars - 2 * c.max_vars) ⋆
  region (c.pWalkVals + BitVec.ofNat 64 (2 * c.max_vars))
    (valsBytes c.max_vars - 2 * c.max_vars) ⋆
  region (c.pLitMark + BitVec.ofNat 64 (2 * c.max_vars))
    (valsBytes c.max_vars - 2 * c.max_vars) ⋆
  region (c.pMark + BitVec.ofNat 64 c.max_vars) (markBytes c.max_vars - c.max_vars) ⋆
  region (c.pPhases + BitVec.ofNat 64 c.max_vars) (markBytes c.max_vars - c.max_vars) ⋆
  region (c.pPhasesTarget + BitVec.ofNat 64 c.max_vars) (markBytes c.max_vars - c.max_vars) ⋆
  region (c.pPhasesBest + BitVec.ofNat 64 c.max_vars) (markBytes c.max_vars - c.max_vars) ⋆
  region (c.pWalkBest + BitVec.ofNat 64 c.max_vars) (markBytes c.max_vars - c.max_vars)

@[expose] def padU32A (c : FullCfg) : Mem 64 → Prop :=
  region (c.pFlags + BitVec.ofNat 64 (4 * c.max_vars)) (u32FullBytes c.max_vars - 4 * c.max_vars) ⋆
  region (c.pLevel + BitVec.ofNat 64 (4 * c.max_vars)) (u32FullBytes c.max_vars - 4 * c.max_vars) ⋆
  region (c.pReason + BitVec.ofNat 64 (4 * c.max_vars))
    (u32FullBytes c.max_vars - 4 * c.max_vars) ⋆
  region (c.pTrail + BitVec.ofNat 64 (4 * c.max_vars)) (u32FullBytes c.max_vars - 4 * c.max_vars) ⋆
  region (c.pTrailPos + BitVec.ofNat 64 (4 * c.max_vars))
    (u32FullBytes c.max_vars - 4 * c.max_vars)

@[expose] def padU32B (c : FullCfg) : Mem 64 → Prop :=
  region (c.pTmp + BitVec.ofNat 64 (4 * c.max_vars)) (u32FullBytes c.max_vars - 4 * c.max_vars) ⋆
  region (c.pHeap + BitVec.ofNat 64 (4 * c.max_vars)) (u32FullBytes c.max_vars - 4 * c.max_vars) ⋆
  region (c.pPos + BitVec.ofNat 64 (4 * c.max_vars)) (u32FullBytes c.max_vars - 4 * c.max_vars) ⋆
  region (c.pMinClr + BitVec.ofNat 64 (4 * c.max_vars))
    (u32FullBytes c.max_vars - 4 * c.max_vars) ⋆
  region (c.pShrinkStk + BitVec.ofNat 64 (4 * c.max_vars))
    (u32FullBytes c.max_vars - 4 * c.max_vars)

@[expose] def padU32C (c : FullCfg) : Mem 64 → Prop :=
  region (c.pQPrev + BitVec.ofNat 64 (4 * c.max_vars)) (u32FullBytes c.max_vars - 4 * c.max_vars) ⋆
  region (c.pQNext + BitVec.ofNat 64 (4 * c.max_vars)) (u32FullBytes c.max_vars - 4 * c.max_vars) ⋆
  region (c.pQStamp + BitVec.ofNat 64 (4 * c.max_vars))
    (u32FullBytes c.max_vars - 4 * c.max_vars) ⋆
  region (c.pFrameTrail + BitVec.ofNat 64 (4 * (c.max_vars + 1)))
    (u32FullBytes c.max_vars - 4 * (c.max_vars + 1)) ⋆
  region (c.pFrameDec + BitVec.ofNat 64 (4 * (c.max_vars + 1)))
    (u32FullBytes c.max_vars - 4 * (c.max_vars + 1))

/-- Combined alignment padding and trailing slack regions (untouched after `full_init_state`). -/
@[expose] def pad (c : FullCfg) : Mem 64 → Prop :=
  c.padBytes ⋆ c.padU32A ⋆ c.padU32B ⋆ c.padU32C ⋆ region c.pSlack c.slack

private def hdrRegSeg : SlabSeg where
  stride := 1152
  pred a := region a 32 ⋆ region (a + BitVec.ofNat 64 32) 1120
  toReg a m hfit h := (congrFun (region_merge_eq (by decide) hfit) m).mp h

private def padRegSeg (active stride : Nat) (hle : active ≤ stride) : SlabSeg where
  stride := stride
  pred a := region a active ⋆ region (a + BitVec.ofNat 64 active) (stride - active)
  toReg a m hfit h := (congrFun (region_merge_eq (by omega) hfit) m).mp h

private def segsBytes (c : FullCfg) : List SlabSeg :=
  let v := padRegSeg (2 * c.max_vars) (valsBytes c.max_vars) (valsBytes_ge c.max_vars)
  let mk := padRegSeg c.max_vars (markBytes c.max_vars) (markBytes_ge c.max_vars)
  [hdrRegSeg, v, v, v, mk, mk, mk, mk, mk]

private def segsU32_5 (c : FullCfg) : List SlabSeg :=
  let u := padRegSeg (4 * c.max_vars) (u32FullBytes c.max_vars) (u32FullBytes_ge4 c.max_vars)
  [u, u, u, u, u]

private def segsU32C (c : FullCfg) : List SlabSeg :=
  let u := padRegSeg (4 * c.max_vars) (u32FullBytes c.max_vars) (u32FullBytes_ge4 c.max_vars)
  let uf := padRegSeg (4 * (c.max_vars + 1)) (u32FullBytes c.max_vars) (u32FullBytes_ge c.max_vars)
  [u, u, u, uf, uf]

private def segsTail (c : FullCfg) : List SlabSeg :=
  let r8 := SlabSeg.ofRegion (8 * c.max_vars)
  [SlabSeg.ofRegion (16 * c.max_vars), r8, r8, r8, r8, r8, r8, r8, r8,
   SlabSeg.ofRegion (8 * c.minDepth), SlabSeg.ofRegion 256, SlabSeg.ofRegion 64,
   SlabSeg.ofRegion (4 * c.arena_cap), SlabSeg.ofRegion (4 * c.wcap),
   SlabSeg.ofRegion (12 * c.delayed_cap), SlabSeg.ofRegion (4 * c.red_cap),
   SlabSeg.ofRegion (4 * c.extend_cap), SlabSeg.ofRegion (4 * c.scratch_cap),
   SlabSeg.ofRegion c.slack]

/-- Collapse all `41` active array regions, header prefix/tail, and padding back into
`region c.hdr c.avail` via `SlabChain.to_region_eq`. -/
theorem regions_to_avail (c : FullCfg) {m : Mem 64}
    (hm : ((region c.hdr 32 ⋆ region (c.hdr + BitVec.ofNat 64 32) 1120) ⋆
      ((region c.pVals (2 * c.max_vars) ⋆ region c.pWalkVals (2 * c.max_vars) ⋆
        region c.pLitMark (2 * c.max_vars)) ⋆
       (region c.pMark c.max_vars ⋆ region c.pPhases c.max_vars ⋆
        region c.pPhasesTarget c.max_vars ⋆ region c.pPhasesBest c.max_vars ⋆
        region c.pWalkBest c.max_vars)) ⋆
      (region c.pFlags (4 * c.max_vars) ⋆ region c.pLevel (4 * c.max_vars) ⋆
       region c.pReason (4 * c.max_vars) ⋆ region c.pTrail (4 * c.max_vars) ⋆
       region c.pTrailPos (4 * c.max_vars)) ⋆
      (region c.pTmp (4 * c.max_vars) ⋆ region c.pHeap (4 * c.max_vars) ⋆
       region c.pPos (4 * c.max_vars) ⋆ region c.pMinClr (4 * c.max_vars) ⋆
       region c.pShrinkStk (4 * c.max_vars)) ⋆
      (region c.pQPrev (4 * c.max_vars) ⋆ region c.pQNext (4 * c.max_vars) ⋆
       region c.pQStamp (4 * c.max_vars) ⋆ region c.pFrameTrail (4 * (c.max_vars + 1)) ⋆
       region c.pFrameDec (4 * (c.max_vars + 1))) ⋆
      (region c.pWvec (16 * c.max_vars) ⋆ region c.pRepr (8 * c.max_vars) ⋆
       region c.pWsort (8 * c.max_vars) ⋆ region c.pWorkStk1 (8 * c.max_vars) ⋆
       region c.pWorkStk2 (8 * c.max_vars) ⋆ region c.pTarjanMark (8 * c.max_vars) ⋆
       region c.pTarjanReach (8 * c.max_vars) ⋆ region c.pScore (8 * c.max_vars) ⋆
       region c.pSimSig (8 * c.max_vars)) ⋆
      (region c.pMinStk (8 * c.minDepth) ⋆ region c.pGlueUsed 256 ⋆
       region c.pLastLearned 64 ⋆ region c.pArena (4 * c.arena_cap) ⋆
       region c.pWstk (4 * c.wcap) ⋆ region c.pDelayed (12 * c.delayed_cap) ⋆
       region c.pRedRefs (4 * c.red_cap) ⋆ region c.pExtendStk (4 * c.extend_cap) ⋆
       region c.pScratchBuf (4 * c.scratch_cap)) ⋆
      c.pad) m) : region c.hdr c.avail m := by
  have hfit : c.avail ≤ 2 ^ 64 := by have := c.havail_fit; omega
  have htot : SlabChain.totalBytes
      (c.segsBytes ++ c.segsU32_5 ++ c.segsU32_5 ++ c.segsU32C ++ c.segsTail) = c.avail := by
    simp only [SlabChain.totalBytes_append, segsBytes, segsU32_5, segsU32C, segsTail,
      SlabChain.totalBytes, hdrRegSeg, padRegSeg, SlabSeg.ofRegion]
    have hsz := c.hsize; unfold slack fullFixedBytes minDepth at *; omega
  refine SlabChain.to_region_eq htot hfit ?_
  simp only [SlabChain.eval_append]
  unfold pad at hm
  have hgrp : ∀ {H B U1 U2 U3 T1 T2 PB PA PC PD PS : Mem 64 → Prop} {k : Mem 64},
      (H ⋆ B ⋆ U1 ⋆ U2 ⋆ U3 ⋆ T1 ⋆ T2 ⋆ (PB ⋆ PA ⋆ PC ⋆ PD ⋆ PS)) k →
      ((((H ⋆ B ⋆ PB) ⋆ (U1 ⋆ PA)) ⋆ (U2 ⋆ PC)) ⋆ (U3 ⋆ PD) ⋆ (T1 ⋆ T2 ⋆ PS)) k := fun x => sep_ac x
  have hm' := hgrp hm
  refine sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2
    (fun _ h => by
      simp only [segsBytes, SlabChain.eval, hdrRegSeg, padRegSeg, sep_emp]
      unfold padBytes pWalkBest pPhasesBest pPhasesTarget pPhases pMark pLitMark pWalkVals pVals
        at h
      exact sep_ac h)
    (fun _ h => by
      change SlabChain.eval c.pFlags c.segsU32_5 _
      simp only [segsU32_5, SlabChain.eval, padRegSeg, sep_emp]
      unfold padU32A pTrailPos pTrail pReason pLevel at h; exact sep_ac h))
    (fun _ h => by
      change SlabChain.eval c.pTmp c.segsU32_5 _
      simp only [segsU32_5, SlabChain.eval, padRegSeg, sep_emp]
      unfold padU32B pShrinkStk pMinClr pPos pHeap at h; exact sep_ac h))
    (fun _ h => by
      change SlabChain.eval c.pQPrev c.segsU32C _
      simp only [segsU32C, SlabChain.eval, padRegSeg, sep_emp]
      unfold padU32C pFrameDec pFrameTrail pQStamp pQNext at h; exact sep_ac h))
    (fun _ h => by
      change SlabChain.eval c.pWvec c.segsTail _
      simp only [segsTail, SlabChain.eval, SlabSeg.ofRegion, sep_emp]
      unfold pSlack pScratchBuf pExtendStk pRedRefs pDelayed pWstk pArena pLastLearned pGlueUsed
        pMinStk pSimSig pScore pTarjanReach pTarjanMark pWorkStk2 pWorkStk1 pWsort pRepr at h
      exact sep_ac h) m hm'

end FullCfg

/-! ## 3. Named `FullScratch`, `FullCoreState`, `FullState`, and `LengthsOk` -/

/-- Non-soundness heuristic, WalkSAT, VMTF queue, phase, reduction, Tarjan/simulation, and
scratch arrays/scalars separated cleanly from `FullCoreState`. -/
structure FullScratch where
  heap_len : Nat
  scinc : BitVec 64
  rel_period : BitVec 64
  rel_limit : BitVec 64
  rel_wait : BitVec 64
  rel_u : BitVec 64
  rel_v : BitVec 64
  rel_trigger : BitVec 64
  conflicts : BitVec 64
  learned_lits : BitVec 64
  min_removed : BitVec 64
  delayed_len : Nat
  stable : BitVec 64
  switched : BitVec 64
  mode_count : BitVec 64
  mode_confl_lim : BitVec 64
  mode_tick_lim : BitVec 64
  mode_saved_ticks : BitVec 64
  search_ticks : BitVec 64
  q_first : BitVec 64
  q_last : BitVec 64
  q_search_idx : BitVec 64
  q_search_stamp : BitVec 64
  q_cur_stamp : BitVec 64
  target_assigned : BitVec 64
  best_assigned : BitVec 64
  rephase_limit : BitVec 64
  rephased : BitVec 64
  reduce_limit : BitVec 64
  reductions : BitVec 64
  tier1 : BitVec 64
  tier2 : BitVec 64
  restarts : BitVec 64
  restart_limit : BitVec 64
  ema_fast_biased : BitVec 64
  ema_fast_exp : BitVec 64
  ema_slow_biased : BitVec 64
  ema_slow_exp : BitVec 64
  extend_len : Nat
  rng_state : BitVec 64
  chrono_levels : BitVec 64
  otfs_cnt : BitVec 64
  eager_sub_cnt : BitVec 64
  probe_limit : BitVec 64
  probings : BitVec 64
  elim_limit : BitVec 64
  eliminations : BitVec 64
  elim_bound : BitVec 64
  iterating : BitVec 64
  hbr_cnt : BitVec 64
  trans_cnt : BitVec 64
  viv_cnt : BitVec 64
  subst_cnt : BitVec 64
  cong_cnt : BitVec 64
  sweep_cnt : BitVec 64
  bve_cnt : BitVec 64
  bce_cnt : BitVec 64
  bva_cnt : BitVec 64
  walk_cnt_stat : BitVec 64
  fwd_sub_cnt : BitVec 64
  fwd_str_cnt : BitVec 64
  ant_sz : BitVec 64
  res_sz : BitVec 64
  walk_vals : List (BitVec 8)
  phases : List (BitVec 8)
  phases_target : List (BitVec 8)
  phases_best : List (BitVec 8)
  walk_best : List (BitVec 8)
  heap : List (BitVec 32)
  pos : List (BitVec 32)
  shrink_stk : List (BitVec 32)
  q_prev : List (BitVec 32)
  q_next : List (BitVec 32)
  q_stamp : List (BitVec 32)
  wsort : List (BitVec 32)
  work_stk1 : List (BitVec 32)
  work_stk2 : List (BitVec 32)
  tarjan_mark : List (BitVec 32)
  tarjan_reach : List (BitVec 32)
  score : List (BitVec 64)
  sim_sig : List (BitVec 64)
  glue_used : List (BitVec 32)
  last_learned : List (BitVec 32)
  delayed : List (BitVec 32)
  red_refs : List (BitVec 32)
  extend_stk : List (BitVec 32)
  scratch_buf : List (BitVec 32)

structure FullScratch.LengthsOk (c : FullCfg) (sc : FullScratch) : Prop where
  walk_vals_len : sc.walk_vals.length = 2 * c.max_vars
  phases_len : sc.phases.length = c.max_vars
  phases_target_len : sc.phases_target.length = c.max_vars
  phases_best_len : sc.phases_best.length = c.max_vars
  walk_best_len : sc.walk_best.length = c.max_vars
  heap_len_arr : sc.heap.length = c.max_vars
  pos_len : sc.pos.length = c.max_vars
  shrink_stk_len : sc.shrink_stk.length = c.max_vars
  q_prev_len : sc.q_prev.length = c.max_vars
  q_next_len : sc.q_next.length = c.max_vars
  q_stamp_len : sc.q_stamp.length = c.max_vars
  wsort_len : sc.wsort.length = 2 * c.max_vars
  work_stk1_len : sc.work_stk1.length = 2 * c.max_vars
  work_stk2_len : sc.work_stk2.length = 2 * c.max_vars
  tarjan_mark_len : sc.tarjan_mark.length = 2 * c.max_vars
  tarjan_reach_len : sc.tarjan_reach.length = 2 * c.max_vars
  score_len : sc.score.length = c.max_vars
  sim_sig_len : sc.sim_sig.length = c.max_vars
  glue_used_len : sc.glue_used.length = 64
  last_learned_len : sc.last_learned.length = 16
  delayed_len_arr : sc.delayed.length = 3 * c.delayed_cap
  red_refs_len : sc.red_refs.length = c.red_cap
  extend_stk_len : sc.extend_stk.length = c.extend_cap
  scratch_buf_len : sc.scratch_buf.length = c.scratch_cap

/-- Soundness-bearing CDCL / inprocessing core state for `D-Full`. -/
structure FullCoreState where
  d_cur : BitVec 64
  d_val : BitVec 64
  cur_vars : Nat
  unassigned : BitVec 64
  arena_len : Nat
  wlen : Nat
  wusable : BitVec 64
  arena_garbage : BitVec 64
  first_reducible : BitVec 64
  num_irred : BitVec 64
  num_redundant : BitVec 64
  num_binary : BitVec 64
  unflushed : BitVec 64
  probing : BitVec 64
  trail_end : Nat
  propagated : Nat
  cur_level : Nat
  fuel : BitVec 64
  confl_ref : BitVec 64
  confl_type : BitVec 64
  confl_lit0 : BitVec 64
  confl_lit1 : BitVec 64
  tmp_cnt : Nat
  tmp_len : Nat
  min_clr_len : Nat
  min_clr_full : BitVec 64
  oom : BitVec 64
  dense_mode : BitVec 64
  inconsistent : BitVec 64
  vals : List (BitVec 8)
  lit_mark : List (BitVec 8)
  mrk : List (BitVec 8)
  flags : List (BitVec 32)
  lvl : List (BitVec 32)
  rsns : List (BitVec 32)
  trl : List (BitVec 32)
  trail_pos : List (BitVec 32)
  tmp : List (BitVec 32)
  min_clr : List (BitVec 32)
  frame_trail : List (BitVec 32)
  frame_dec : List (BitVec 32)
  wvec : List (BitVec 32)
  repr : List (BitVec 32)
  min_stk : List (BitVec 32)
  arena : List (BitVec 32)
  wstk : List (BitVec 32)

structure FullCoreState.LengthsOk (c : FullCfg) (k : FullCoreState) : Prop where
  vals_len : k.vals.length = 2 * c.max_vars
  lit_mark_len : k.lit_mark.length = 2 * c.max_vars
  mrk_len : k.mrk.length = c.max_vars
  flags_len : k.flags.length = c.max_vars
  lvl_len : k.lvl.length = c.max_vars
  rsns_len : k.rsns.length = c.max_vars
  trl_len : k.trl.length = c.max_vars
  trail_pos_len : k.trail_pos.length = c.max_vars
  tmp_len_arr : k.tmp.length = c.max_vars
  min_clr_len_arr : k.min_clr.length = c.max_vars
  frame_trail_len : k.frame_trail.length = c.max_vars + 1
  frame_dec_len : k.frame_dec.length = c.max_vars + 1
  wvec_len : k.wvec.length = 4 * c.max_vars
  repr_len : k.repr.length = 2 * c.max_vars
  min_stk_len : k.min_stk.length = 2 * c.minDepth
  arena_len_arr : k.arena.length = c.arena_cap
  wstk_len_arr : k.wstk.length = c.wcap
  cur_vars_ge : c.mv ≤ k.cur_vars
  cur_vars_le : k.cur_vars ≤ c.max_vars
  arena_len_le : k.arena_len ≤ c.arena_cap
  wlen_le : k.wlen ≤ c.wcap
  trail_end_le : k.trail_end ≤ k.cur_vars
  propagated_le : k.propagated ≤ k.trail_end
  tmp_len_le : k.tmp_len ≤ c.max_vars
  min_clr_len_le : k.min_clr_len ≤ c.max_vars

/-- Combined Stage-4 C0 solver state, partitioned into `core` and `scratch`. -/
structure FullState where
  core : FullCoreState
  scratch : FullScratch

structure FullState.LengthsOk (c : FullCfg) (s : FullState) : Prop where
  core_ok : s.core.LengthsOk c
  scratch_ok : s.scratch.LengthsOk c

theorem FullState.LengthsOk.with_scratch {c : FullCfg} {s : FullState}
    (hlen : s.LengthsOk c) {sc' : FullScratch} (hok : sc'.LengthsOk c) :
    ({ s with scratch := sc' } : FullState).LengthsOk c :=
  ⟨hlen.core_ok, hok⟩

/-! ## 4. Single-Source-of-Truth Indexed `HdrWordField` Table (`144` Words) -/

/-- Storage class of one `u64` word in `FullHdr` (`0..143`). -/
meta inductive HdrWordKind where
  | cfgNat (fld : String)
  | cfgPtr (fld : String)
  | coreNat (fld : String)
  | coreBv (fld : String)
  | scrNat (fld : String)
  | scrBv (fld : String)
  deriving Repr, BEq, Inhabited

/-- Descriptor for one `FullHdr` `u64` word; its array index is its word index (`byteOff = 8*i`). -/
meta structure HdrWordSpec where
  ctor : String
  kind : HdrWordKind
  deriving Repr, Inhabited

private meta def hCfgN (s : String) (f : String := s) : HdrWordSpec := ⟨s, .cfgNat f⟩
private meta def hCfgP (s : String) (f : String) : HdrWordSpec := ⟨s, .cfgPtr f⟩
private meta def hCorN (s : String) : HdrWordSpec := ⟨s, .coreNat s⟩
private meta def hCorB (s : String) (f : String := s) : HdrWordSpec := ⟨s, .coreBv f⟩
private meta def hScrN (s : String) : HdrWordSpec := ⟨s, .scrNat s⟩
private meta def hScrB (s : String) : HdrWordSpec := ⟨s, .scrBv s⟩

/-- Canonical `144`-word `FullHdr` layout table (word indices `0..143`, byte offsets `0..1144`). -/
meta def hdrWordSpecs : Array HdrWordSpec := #[
  -- Prefix words `0..3` (`KissatDimacs`, offsets `0..24`)
  hCfgN "mv", hCfgN "nc", hCorB "cur" "d_cur", hCorB "val" "d_val",
  -- Tail `0..34` (words `4..38`, offsets `32..304`)
  hCfgN "arena_cap", hCfgN "wcap", hCorN "arena_len", hCorN "wlen",
  hCfgP "values_ptr" "pVals", hCfgP "mark_ptr" "pMark", hCfgP "level_ptr" "pLevel",
  hCfgP "reason_ptr" "pReason", hCfgP "trail_ptr" "pTrail", hCfgP "watch_vec_ptr" "pWvec",
  hCfgP "arena_ptr" "pArena", hCfgP "watch_stk_ptr" "pWstk", hCfgP "delayed_ptr" "pDelayed",
  hCfgP "tmp_lits_ptr" "pTmp", hCorN "trail_end", hCorN "propagated", hCorN "cur_level",
  hCorB "fuel", hCorB "confl_ref", hCorN "tmp_cnt", hCorN "tmp_len",
  hCfgP "heap_ptr" "pHeap", hCfgP "pos_ptr" "pPos", hCfgP "score_ptr" "pScore",
  hCfgP "phases_ptr" "pPhases", hCfgP "min_stk_ptr" "pMinStk", hCfgP "min_clr_ptr" "pMinClr",
  hScrN "heap_len", hScrB "scinc", hCfgN "min_depth" "minDepth", hCorN "min_clr_len",
  hCorB "min_clr_full", hScrB "rel_period", hScrB "rel_limit", hScrB "rel_wait",
  -- Tail `35..69` (words `39..73`, offsets `312..584`)
  hScrB "rel_u", hScrB "rel_v", hScrB "rel_trigger", hScrB "conflicts", hScrB "learned_lits",
  hScrB "min_removed", hCfgP "trail_pos_ptr" "pTrailPos", hCfgP "q_prev_ptr" "pQPrev",
  hCfgP "q_next_ptr" "pQNext", hCfgP "q_stamp_ptr" "pQStamp",
  hCfgP "phases_target_ptr" "pPhasesTarget", hCfgP "phases_best_ptr" "pPhasesBest",
  hCfgP "wsort_ptr" "pWsort", hCfgP "shrink_stk_ptr" "pShrinkStk",
  hCfgP "red_refs_ptr" "pRedRefs", hCfgP "glue_used_ptr" "pGlueUsed",
  hCfgN "red_cap", hCfgN "delayed_cap", hScrN "delayed_len",
  hCorB "wusable", hCorB "arena_garbage", hCorB "first_reducible", hCorB "num_irred",
  hCorB "num_redundant", hCorB "num_binary", hCorB "unflushed", hCorB "probing",
  hCorB "confl_type", hCorB "confl_lit0", hCorB "confl_lit1",
  hScrB "stable", hScrB "switched", hScrB "mode_count", hScrB "mode_confl_lim",
  hScrB "mode_tick_lim",
  -- Tail `70..104` (words `74..108`, offsets `592..864`)
  hScrB "mode_saved_ticks", hScrB "search_ticks", hScrB "q_first", hScrB "q_last",
  hScrB "q_search_idx", hScrB "q_search_stamp", hScrB "q_cur_stamp", hScrB "target_assigned",
  hScrB "best_assigned", hScrB "rephase_limit", hScrB "rephased", hScrB "reduce_limit",
  hScrB "reductions", hScrB "tier1", hScrB "tier2", hScrB "restarts", hScrB "restart_limit",
  hScrB "ema_fast_biased", hScrB "ema_fast_exp", hScrB "ema_slow_biased", hScrB "ema_slow_exp",
  hCorB "oom", hCfgN "max_vars", hCorN "cur_vars", hCfgN "bva_cap", hCorB "unassigned",
  hCfgP "flags_ptr" "pFlags", hCfgP "lit_mark_ptr" "pLitMark", hCfgP "repr_ptr" "pRepr",
  hCfgP "sim_sig_ptr" "pSimSig", hCfgP "frame_trail_ptr" "pFrameTrail",
  hCfgP "frame_dec_ptr" "pFrameDec", hCfgP "work_stk1_ptr" "pWorkStk1",
  hCfgP "work_stk2_ptr" "pWorkStk2", hCfgP "tarjan_mark_ptr" "pTarjanMark",
  -- Tail `105..139` (words `109..143`, offsets `872..1144`)
  hCfgP "tarjan_reach_ptr" "pTarjanReach", hCfgP "walk_vals_ptr" "pWalkVals",
  hCfgP "walk_best_ptr" "pWalkBest", hCfgP "extend_stk_ptr" "pExtendStk",
  hCfgN "extend_cap", hScrN "extend_len", hCfgP "scratch_buf_ptr" "pScratchBuf",
  hCfgN "scratch_cap", hCfgP "last_learned_ptr" "pLastLearned",
  hScrB "rng_state", hScrB "chrono_levels", hScrB "otfs_cnt", hScrB "eager_sub_cnt",
  hScrB "probe_limit", hScrB "probings", hScrB "elim_limit", hScrB "eliminations",
  hScrB "elim_bound", hCorB "dense_mode", hCorB "inconsistent",
  hScrB "iterating", hScrB "hbr_cnt", hScrB "trans_cnt", hScrB "viv_cnt",
  hScrB "subst_cnt", hScrB "cong_cnt", hScrB "sweep_cnt", hScrB "bve_cnt",
  hScrB "bce_cnt", hScrB "bva_cnt", hScrB "walk_cnt_stat", hScrB "fwd_sub_cnt",
  hScrB "fwd_str_cnt", hScrB "ant_sz", hScrB "res_sz"
]

private meta def elabSrcCmd (tag src : String) : Lean.Elab.Command.CommandElabM Unit := do
  match Lean.Parser.runParserCategory (← Lean.getEnv) `command src tag with
  | .ok stx => Lean.Elab.Command.elabCommand stx
  | .error err => throwError "{tag}: generated code failed to parse: {err}\n{src}"

local elab "gen_full_hdr_table!" : command => do
  if hdrWordSpecs.size != 144 then
    throwError "hdrWordSpecs must have 144 entries, got {hdrWordSpecs.size}"
  let mut ctors : Array String := #[]
  let mut idxArms : Array String := #[]
  let mut mutArms : Array String := #[]
  let mut natArms : Array String := #[]
  let mut getArms : Array String := #[]
  let mut setArms : Array String := #[]
  let mut setNatArms : Array String := #[]
  let mut ofIdxArms : Array String := #[]
  let mut tailElems : Array String := #[]
  let mut tailExprs : Array String := #[]
  for i in [:hdrWordSpecs.size] do
    let sp := hdrWordSpecs[i]!
    ctors := ctors.push s!"  | {sp.ctor}"
    idxArms := idxArms.push s!"  | .{sp.ctor} => {i}"
    ofIdxArms := ofIdxArms.push s!"  | {i} => some .{sp.ctor}"
    let exprStr := match sp.kind with
      | .cfgNat f => s!"BitVec.ofNat 64 c.{f}"
      | .cfgPtr f => s!"c.{f}"
      | .coreNat f => s!"BitVec.ofNat 64 s.core.{f}"
      | .coreBv f => s!"s.core.{f}"
      | .scrNat f => s!"BitVec.ofNat 64 s.scratch.{f}"
      | .scrBv f => s!"s.scratch.{f}"
    if i ≥ 4 then
      tailElems := tailElems.push s!".{sp.ctor}"
      tailExprs := tailExprs.push exprStr
    getArms := getArms.push s!"  | .{sp.ctor} => {exprStr}"
    match sp.kind with
    | .cfgNat _ | .cfgPtr _ => pure ()
    | .coreNat f =>
      mutArms := mutArms.push s!"  | .{sp.ctor} => true"
      natArms := natArms.push s!"  | .{sp.ctor} => true"
      setArms := setArms.push
        s!"  | .{sp.ctor} => \{ s with core := \{ s.core with {f} := v.toNat } }"
      setNatArms := setNatArms.push
        s!"  | .{sp.ctor} => \{ s with core := \{ s.core with {f} := v } }"
    | .coreBv f =>
      mutArms := mutArms.push s!"  | .{sp.ctor} => true"
      setArms := setArms.push s!"  | .{sp.ctor} => \{ s with core := \{ s.core with {f} := v } }"
    | .scrNat f =>
      mutArms := mutArms.push s!"  | .{sp.ctor} => true"
      natArms := natArms.push s!"  | .{sp.ctor} => true"
      setArms := setArms.push
        s!"  | .{sp.ctor} => \{ s with scratch := \{ s.scratch with {f} := v.toNat } }"
      setNatArms := setNatArms.push
        s!"  | .{sp.ctor} => \{ s with scratch := \{ s.scratch with {f} := v } }"
    | .scrBv f =>
      mutArms := mutArms.push s!"  | .{sp.ctor} => true"
      setArms := setArms.push
        s!"  | .{sp.ctor} => \{ s with scratch := \{ s.scratch with {f} := v } }"
  elabSrcCmd "HdrWordField" <|
    "inductive HdrWordField where\n" ++ String.intercalate "\n" ctors.toList ++
    "\n  deriving DecidableEq, Repr"
  elabSrcCmd "HdrWordField.wordIdx" <|
    "@[expose] def HdrWordField.wordIdx : HdrWordField → Nat\n" ++
    String.intercalate "\n" idxArms.toList
  elabSrcCmd "HdrWordField.isMutable" <|
    "@[expose] def HdrWordField.isMutable : HdrWordField → Bool\n" ++
    String.intercalate "\n" mutArms.toList ++ "\n  | _ => false"
  elabSrcCmd "HdrWordField.isNat" <|
    "@[expose] def HdrWordField.isNat : HdrWordField → Bool\n" ++
    String.intercalate "\n" natArms.toList ++ "\n  | _ => false"
  elabSrcCmd "HdrWordField.get" <|
    "@[expose] def HdrWordField.get (f : HdrWordField) (c : FullCfg) (s : FullState) :\n" ++
    "    BitVec 64 :=\n  match f with\n" ++ String.intercalate "\n" getArms.toList
  elabSrcCmd "HdrWordField.set" <|
    "@[expose] def HdrWordField.set (f : HdrWordField) (s : FullState) (v : BitVec 64) :\n" ++
    "    FullState :=\n  match f with\n" ++ String.intercalate "\n" setArms.toList ++ "\n  | _ => s"
  elabSrcCmd "HdrWordField.setNat" <|
    "@[expose] def HdrWordField.setNat (f : HdrWordField) (s : FullState) (v : Nat) :\n" ++
    "    FullState :=\n  match f with\n" ++ String.intercalate "\n" setNatArms.toList ++
    "\n  | _ => s"
  elabSrcCmd "HdrWordField.ofWordIdx?" <|
    "@[expose] def HdrWordField.ofWordIdx? : Nat → Option HdrWordField\n" ++
    String.intercalate "\n" ofIdxArms.toList ++ "\n  | _ => none"
  elabSrcCmd "HdrWordField.tailList" <|
    "@[expose] def HdrWordField.tailList : List HdrWordField :=\n  [" ++
    String.intercalate ", " tailElems.toList ++ "]"
  for k in [:4] do
    let chunk := (tailExprs.extract (35 * k) (35 * (k + 1))).toList
    elabSrcCmd s!"HdrWordField.tailChunk{k}" <|
      s!"@[expose] def HdrWordField.tailChunk{k} (c : FullCfg) (s : FullState) :\n" ++
      "    List (BitVec 64) := [" ++ String.intercalate ", " chunk ++ "]"

gen_full_hdr_table!

namespace HdrWordField

@[expose] def byteOff (f : HdrWordField) : Nat := 8 * f.wordIdx

@[expose] def addr (f : HdrWordField) (c : FullCfg) : BitVec 64 :=
  if f.wordIdx = 0 then c.hdr else c.hdr + BitVec.ofNat 64 f.byteOff

@[expose] def isTailMut (f : HdrWordField) : Bool :=
  f.isMutable && decide (4 ≤ f.wordIdx)

@[expose] def ofOff? (off : Nat) : Option HdrWordField :=
  if off % 8 = 0 then ofWordIdx? (off / 8) else none

theorem wordIdx_lt (f : HdrWordField) : f.wordIdx < 144 := by
  cases f <;> decide

theorem ofWordIdx?_wordIdx (f : HdrWordField) : ofWordIdx? f.wordIdx = some f := by
  cases f <;> rfl

theorem ofWordIdx?_eq_some {n : Nat} {f : HdrWordField} (h : ofWordIdx? n = some f) :
    f.wordIdx = n := by
  unfold ofWordIdx? at h; split at h <;> cases h <;> rfl

theorem ofOff?_byteOff (f : HdrWordField) : ofOff? f.byteOff = some f := by
  cases f <;> rfl

theorem ofOff?_eq_some {off : Nat} {f : HdrWordField} (h : ofOff? off = some f) :
    f.byteOff = off := by
  unfold ofOff? at h
  split at h
  · rename_i hmod
    have hidx := ofWordIdx?_eq_some h
    unfold byteOff; omega
  · cases h

theorem prefix_cases {f : HdrWordField} (h : f.wordIdx < 4) :
    f = .mv ∨ f = .nc ∨ f = .cur ∨ f = .val := by
  cases f <;> first
    | (simp [wordIdx] at h; done)
    | exact Or.inl rfl | exact Or.inr (Or.inl rfl)
    | exact Or.inr (Or.inr (Or.inl rfl)) | exact Or.inr (Or.inr (Or.inr rfl))

theorem isNat_ge4 {f : HdrWordField} (h : f.isNat = true) : 4 ≤ f.wordIdx := by
  cases f <;> first | (simp [isNat] at h; done) | decide

end HdrWordField

/-- The `140` trailing `u64` words of `FullHdr` starting at offset `c.hdr + 32`
(byte offsets `32..1144`), generated directly from `hdrWordSpecs` in four `35`-word chunks. -/
@[expose] def hdrTailWords (c : FullCfg) (s : FullState) : List (BitVec 64) :=
  HdrWordField.tailChunk0 c s ++ HdrWordField.tailChunk1 c s ++
  HdrWordField.tailChunk2 c s ++ HdrWordField.tailChunk3 c s

@[simp] theorem hdrTailWords_length (c : FullCfg) (s : FullState) :
    (hdrTailWords c s).length = 140 := by
  simp only [hdrTailWords, HdrWordField.tailChunk0, HdrWordField.tailChunk1,
    HdrWordField.tailChunk2, HdrWordField.tailChunk3, List.length_append, List.length_cons,
    List.length_nil]

theorem HdrWordField.hdrTailWords_get (f : HdrWordField) (ht : 4 ≤ f.wordIdx)
    (c : FullCfg) (s : FullState) :
    (hdrTailWords c s)[f.wordIdx - 4]'(by rw [hdrTailWords_length]; have := f.wordIdx_lt; omega) =
      f.get c s := by
  cases f <;> first | (simp [wordIdx] at ht; done) | rfl

theorem HdrWordField.hdrTailWords_set (f : HdrWordField) (hm : f.isTailMut = true)
    (c : FullCfg) (s : FullState) (v : BitVec 64) :
    hdrTailWords c (f.set s v) = (hdrTailWords c s).set (f.wordIdx - 4) v := by
  cases f <;> first
    | (simp [isTailMut, isMutable, wordIdx] at hm; done)
    | rfl
    | ((conv => rhs; rw [← @bv_ofNat_toNat_eq 64 v]); rfl)

theorem HdrWordField.hdrTailWords_setNat (f : HdrWordField) (hn : f.isNat = true)
    (c : FullCfg) (s : FullState) (v : Nat) :
    hdrTailWords c (f.setNat s v) = (hdrTailWords c s).set (f.wordIdx - 4) (BitVec.ofNat 64 v) := by
  cases f <;> first | (simp [isNat] at hn; done) | rfl

/-! ## 5. Partitioned array footprints, collapse, and framing bridges -/

@[expose] def FullCoreByteArrs (c : FullCfg) (k : FullCoreState) : Mem 64 → Prop :=
  array (t := i8) c.pVals k.vals ⋆ array (t := i8) c.pLitMark k.lit_mark ⋆
  array (t := i8) c.pMark k.mrk

@[expose] def FullCoreU32A (c : FullCfg) (k : FullCoreState) : Mem 64 → Prop :=
  array (t := i32) c.pFlags k.flags ⋆ array (t := i32) c.pLevel k.lvl ⋆
  array (t := i32) c.pReason k.rsns ⋆ array (t := i32) c.pTrail k.trl ⋆
  array (t := i32) c.pTrailPos k.trail_pos ⋆ array (t := i32) c.pTmp k.tmp ⋆
  array (t := i32) c.pMinClr k.min_clr

@[expose] def FullCoreU32B (c : FullCfg) (k : FullCoreState) : Mem 64 → Prop :=
  array (t := i32) c.pFrameTrail k.frame_trail ⋆ array (t := i32) c.pFrameDec k.frame_dec ⋆
  array (t := i32) c.pWvec k.wvec ⋆ array (t := i32) c.pRepr k.repr ⋆
  array (t := i32) c.pMinStk k.min_stk

@[expose] def FullCoreDynArrs (c : FullCfg) (k : FullCoreState) : Mem 64 → Prop :=
  array (t := i32) c.pArena k.arena ⋆ array (t := i32) c.pWstk k.wstk

@[expose] def FullCoreArrays (c : FullCfg) (k : FullCoreState) : Mem 64 → Prop :=
  FullCoreByteArrs c k ⋆ FullCoreU32A c k ⋆ FullCoreU32B c k ⋆ FullCoreDynArrs c k

@[expose] def FullScrByteArrs (c : FullCfg) (sc : FullScratch) : Mem 64 → Prop :=
  array (t := i8) c.pWalkVals sc.walk_vals ⋆ array (t := i8) c.pPhases sc.phases ⋆
  array (t := i8) c.pPhasesTarget sc.phases_target ⋆
  array (t := i8) c.pPhasesBest sc.phases_best ⋆ array (t := i8) c.pWalkBest sc.walk_best

@[expose] def FullScrU32A (c : FullCfg) (sc : FullScratch) : Mem 64 → Prop :=
  array (t := i32) c.pHeap sc.heap ⋆ array (t := i32) c.pPos sc.pos ⋆
  array (t := i32) c.pShrinkStk sc.shrink_stk ⋆ array (t := i32) c.pQPrev sc.q_prev ⋆
  array (t := i32) c.pQNext sc.q_next ⋆ array (t := i32) c.pQStamp sc.q_stamp

@[expose] def FullScrWksArrs (c : FullCfg) (sc : FullScratch) : Mem 64 → Prop :=
  array (t := i32) c.pWsort sc.wsort ⋆ array (t := i32) c.pWorkStk1 sc.work_stk1 ⋆
  array (t := i32) c.pWorkStk2 sc.work_stk2 ⋆ array (t := i32) c.pTarjanMark sc.tarjan_mark ⋆
  array (t := i32) c.pTarjanReach sc.tarjan_reach

@[expose] def FullScrMetaArrs (c : FullCfg) (sc : FullScratch) : Mem 64 → Prop :=
  array64 c.pScore sc.score ⋆ array64 c.pSimSig sc.sim_sig ⋆
  array (t := i32) c.pGlueUsed sc.glue_used ⋆ array (t := i32) c.pLastLearned sc.last_learned

@[expose] def FullScrDynArrs (c : FullCfg) (sc : FullScratch) : Mem 64 → Prop :=
  array (t := i32) c.pDelayed sc.delayed ⋆ array (t := i32) c.pRedRefs sc.red_refs ⋆
  array (t := i32) c.pExtendStk sc.extend_stk ⋆ array (t := i32) c.pScratchBuf sc.scratch_buf

@[expose] def FullScratchArrays (c : FullCfg) (sc : FullScratch) : Mem 64 → Prop :=
  FullScrByteArrs c sc ⋆ FullScrU32A c sc ⋆ FullScrWksArrs c sc ⋆ FullScrMetaArrs c sc ⋆
  FullScrDynArrs c sc

@[expose] def FullMem (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (hdrTailWords c s) ⋆ FullCoreArrays c s.core ⋆
  FullScratchArrays c s.scratch ⋆ c.pad

@[expose] def FullArenaInv (c : FullCfg) (s : FullState) (m : Mem 64) : Prop :=
  s.LengthsOk c ∧ FullMem c s m

@[expose] def FullRest (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  array64 (c.hdr + 32) (hdrTailWords c s) ⋆ FullCoreArrays c s.core ⋆
  FullScratchArrays c s.scratch ⋆ c.pad

theorem fullMem_eq_dimacs_sep (c : FullCfg) (s : FullState) :
    FullMem c s =
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
        FullRest c s) := by
  unfold FullMem FullRest; ac_rfl

theorem fullRest_d_irrel (c : FullCfg) (s : FullState) (cur' val' : BitVec 64) :
    FullRest c { s with core := { s.core with d_cur := cur', d_val := val' } } = FullRest c s := rfl

theorem HdrWordField.set_frame (f : HdrWordField) (hm : f.isTailMut = true)
    (c : FullCfg) (s : FullState) (v : BitVec 64) :
    (f.set s v).core.d_cur = s.core.d_cur ∧ (f.set s v).core.d_val = s.core.d_val ∧
      FullCoreArrays c (f.set s v).core = FullCoreArrays c s.core ∧
      FullScratchArrays c (f.set s v).scratch = FullScratchArrays c s.scratch := by
  cases f <;> first
    | (simp [isTailMut, isMutable, wordIdx] at hm; done)
    | exact ⟨rfl, rfl, rfl, rfl⟩

theorem HdrWordField.setNat_frame (f : HdrWordField) (hn : f.isNat = true)
    (c : FullCfg) (s : FullState) (v : Nat) :
    (f.setNat s v).core.d_cur = s.core.d_cur ∧ (f.setNat s v).core.d_val = s.core.d_val ∧
      FullCoreArrays c (f.setNat s v).core = FullCoreArrays c s.core ∧
      FullScratchArrays c (f.setNat s v).scratch = FullScratchArrays c s.scratch := by
  cases f <;> first | (simp [isNat] at hn; done) | exact ⟨rfl, rfl, rfl, rfl⟩

private theorem fArr8 {a : BitVec 64} {xs : List (BitVec 8)} {n : Nat}
    (hn : xs.length = n) (hbd : n ≤ 2 ^ 64) {f : Mem 64} (hf : array (t := i8) a xs f) :
    region a n f := by
  simpa [Ty.bytes, Ty.size, i8, hn] using
    array_to_region (t := i8) (by simp [Ty.bytes, Ty.size, i8, hn, hbd]) hf

private theorem fArr32 {a : BitVec 64} {xs : List (BitVec 32)} {n m : Nat}
    (hn : xs.length = n) (hm : 4 * n = m) (hbd : m ≤ 2 ^ 64) {f : Mem 64}
    (hf : array (t := i32) a xs f) : region a m f := by
  simpa [Ty.bytes, Ty.size, i32, hn, hm] using
    array_to_region (t := i32) (by simp [Ty.bytes, Ty.size, i32, hn]; omega) hf

private theorem fArr64 {a : BitVec 64} {xs : List (BitVec 64)} {n m : Nat}
    (hn : xs.length = n) (hm : 8 * n = m) (hbd : m ≤ 2 ^ 64) {f : Mem 64}
    (hf : array64 a xs f) : region a m f := by
  simpa [Ty.bytes, Ty.size, i64, hn, hm] using
    array_to_region (t := i64) (xs := xs) (by simp [Ty.bytes, Ty.size, i64, hn]; omega)
      ((array64_eq_array a xs) ▸ hf)

private theorem fullCoreByte_to_regs {c : FullCfg} {k : FullCoreState} (h : k.LengthsOk c)
    {f : Mem 64} (hf : FullCoreByteArrs c k f) :
    (region c.pVals (2 * c.max_vars) ⋆ region c.pLitMark (2 * c.max_vars) ⋆
      region c.pMark c.max_vars) f := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx; unfold FullCoreByteArrs at hf
  exact sep_mono2 (sep_mono2
    (fun _ => fArr8 h.vals_len (by omega)) (fun _ => fArr8 h.lit_mark_len (by omega)))
    (fun _ => fArr8 h.mrk_len (by omega)) f hf

private theorem fullCoreU32A_to_regs {c : FullCfg} {k : FullCoreState} (h : k.LengthsOk c)
    {f : Mem 64} (hf : FullCoreU32A c k f) :
    (region c.pFlags (4 * c.max_vars) ⋆ region c.pLevel (4 * c.max_vars) ⋆
      region c.pReason (4 * c.max_vars) ⋆ region c.pTrail (4 * c.max_vars) ⋆
      region c.pTrailPos (4 * c.max_vars) ⋆ region c.pTmp (4 * c.max_vars) ⋆
      region c.pMinClr (4 * c.max_vars)) f := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx; unfold FullCoreU32A at hf
  exact sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2
    (fun _ => fArr32 h.flags_len rfl (by omega)) (fun _ => fArr32 h.lvl_len rfl (by omega)))
    (fun _ => fArr32 h.rsns_len rfl (by omega))) (fun _ => fArr32 h.trl_len rfl (by omega)))
    (fun _ => fArr32 h.trail_pos_len rfl (by omega)))
    (fun _ => fArr32 h.tmp_len_arr rfl (by omega)))
    (fun _ => fArr32 h.min_clr_len_arr rfl (by omega)) f hf

private theorem fullCoreU32B_to_regs {c : FullCfg} {k : FullCoreState} (h : k.LengthsOk c)
    {f : Mem 64} (hf : FullCoreU32B c k f) :
    (region c.pFrameTrail (4 * (c.max_vars + 1)) ⋆ region c.pFrameDec (4 * (c.max_vars + 1)) ⋆
      region c.pWvec (16 * c.max_vars) ⋆ region c.pRepr (8 * c.max_vars) ⋆
      region c.pMinStk (8 * c.minDepth)) f := by
  have hmx := c.hmaxv; have hmd := fullMinDepthOf_le c.max_vars
  unfold dimacsBound FullCfg.minDepth at *; unfold FullCoreU32B at hf
  exact sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2
    (fun _ => fArr32 h.frame_trail_len rfl (by omega))
    (fun _ => fArr32 h.frame_dec_len rfl (by omega)))
    (fun _ => fArr32 h.wvec_len (by omega) (by omega)))
    (fun _ => fArr32 h.repr_len (by omega) (by omega)))
    (fun _ => fArr32 h.min_stk_len (by unfold FullCfg.minDepth; omega) (by omega)) f hf

private theorem fullCoreDyn_to_regs {c : FullCfg} {k : FullCoreState} (h : k.LengthsOk c)
    {f : Mem 64} (hf : FullCoreDynArrs c k f) :
    (region c.pArena (4 * c.arena_cap) ⋆ region c.pWstk (4 * c.wcap)) f := by
  have ha := c.harena; have hw := c.hwcap; unfold dimacsBound at ha hw
  unfold FullCoreDynArrs at hf
  exact sep_mono2 (fun _ => fArr32 h.arena_len_arr rfl (by omega))
    (fun _ => fArr32 h.wstk_len_arr rfl (by omega)) f hf

private theorem fullScrByte_to_regs {c : FullCfg} {sc : FullScratch} (h : sc.LengthsOk c)
    {f : Mem 64} (hf : FullScrByteArrs c sc f) :
    (region c.pWalkVals (2 * c.max_vars) ⋆ region c.pPhases c.max_vars ⋆
      region c.pPhasesTarget c.max_vars ⋆ region c.pPhasesBest c.max_vars ⋆
      region c.pWalkBest c.max_vars) f := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx; unfold FullScrByteArrs at hf
  exact sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2
    (fun _ => fArr8 h.walk_vals_len (by omega)) (fun _ => fArr8 h.phases_len (by omega)))
    (fun _ => fArr8 h.phases_target_len (by omega)))
    (fun _ => fArr8 h.phases_best_len (by omega)))
    (fun _ => fArr8 h.walk_best_len (by omega)) f hf

private theorem fullScrU32A_to_regs {c : FullCfg} {sc : FullScratch} (h : sc.LengthsOk c)
    {f : Mem 64} (hf : FullScrU32A c sc f) :
    (region c.pHeap (4 * c.max_vars) ⋆ region c.pPos (4 * c.max_vars) ⋆
      region c.pShrinkStk (4 * c.max_vars) ⋆ region c.pQPrev (4 * c.max_vars) ⋆
      region c.pQNext (4 * c.max_vars) ⋆ region c.pQStamp (4 * c.max_vars)) f := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx; unfold FullScrU32A at hf
  exact sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2
    (fun _ => fArr32 h.heap_len_arr rfl (by omega)) (fun _ => fArr32 h.pos_len rfl (by omega)))
    (fun _ => fArr32 h.shrink_stk_len rfl (by omega)))
    (fun _ => fArr32 h.q_prev_len rfl (by omega)))
    (fun _ => fArr32 h.q_next_len rfl (by omega)))
    (fun _ => fArr32 h.q_stamp_len rfl (by omega)) f hf

private theorem fullScrWks_to_regs {c : FullCfg} {sc : FullScratch} (h : sc.LengthsOk c)
    {f : Mem 64} (hf : FullScrWksArrs c sc f) :
    (region c.pWsort (8 * c.max_vars) ⋆ region c.pWorkStk1 (8 * c.max_vars) ⋆
      region c.pWorkStk2 (8 * c.max_vars) ⋆ region c.pTarjanMark (8 * c.max_vars) ⋆
      region c.pTarjanReach (8 * c.max_vars)) f := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx; unfold FullScrWksArrs at hf
  exact sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2
    (fun _ => fArr32 h.wsort_len (by omega) (by omega))
    (fun _ => fArr32 h.work_stk1_len (by omega) (by omega)))
    (fun _ => fArr32 h.work_stk2_len (by omega) (by omega)))
    (fun _ => fArr32 h.tarjan_mark_len (by omega) (by omega)))
    (fun _ => fArr32 h.tarjan_reach_len (by omega) (by omega)) f hf

private theorem fullScrMeta_to_regs {c : FullCfg} {sc : FullScratch} (h : sc.LengthsOk c)
    {f : Mem 64} (hf : FullScrMetaArrs c sc f) :
    (region c.pScore (8 * c.max_vars) ⋆ region c.pSimSig (8 * c.max_vars) ⋆
      region c.pGlueUsed 256 ⋆ region c.pLastLearned 64) f := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx; unfold FullScrMetaArrs at hf
  exact sep_mono2 (sep_mono2 (sep_mono2
    (fun _ => fArr64 h.score_len rfl (by omega))
    (fun _ => fArr64 h.sim_sig_len rfl (by omega)))
    (fun _ => fArr32 h.glue_used_len (by decide) (by decide)))
    (fun _ => fArr32 h.last_learned_len (by decide) (by decide)) f hf

private theorem fullScrDyn_to_regs {c : FullCfg} {sc : FullScratch} (h : sc.LengthsOk c)
    {f : Mem 64} (hf : FullScrDynArrs c sc f) :
    (region c.pDelayed (12 * c.delayed_cap) ⋆ region c.pRedRefs (4 * c.red_cap) ⋆
      region c.pExtendStk (4 * c.extend_cap) ⋆ region c.pScratchBuf (4 * c.scratch_cap)) f := by
  have hd := c.hdel; have hr := c.hred; have he := c.hext; have hs := c.hscr
  unfold dimacsBound at hd hr he hs; unfold FullScrDynArrs at hf
  exact sep_mono2 (sep_mono2 (sep_mono2
    (fun _ => fArr32 h.delayed_len_arr (by omega) (by omega))
    (fun _ => fArr32 h.red_refs_len rfl (by omega)))
    (fun _ => fArr32 h.extend_stk_len rfl (by omega)))
    (fun _ => fArr32 h.scratch_buf_len rfl (by omega)) f hf

private theorem fullRegs_grouped_to_avail (c : FullCfg) {m : Mem 64}
    (hm : ((region c.hdr 32 ⋆ region (c.hdr + BitVec.ofNat 64 32) 1120) ⋆
      (((region c.pVals (2 * c.max_vars) ⋆ region c.pLitMark (2 * c.max_vars) ⋆
          region c.pMark c.max_vars) ⋆
        (region c.pFlags (4 * c.max_vars) ⋆ region c.pLevel (4 * c.max_vars) ⋆
          region c.pReason (4 * c.max_vars) ⋆ region c.pTrail (4 * c.max_vars) ⋆
          region c.pTrailPos (4 * c.max_vars) ⋆ region c.pTmp (4 * c.max_vars) ⋆
          region c.pMinClr (4 * c.max_vars)) ⋆
        (region c.pFrameTrail (4 * (c.max_vars + 1)) ⋆ region c.pFrameDec (4 * (c.max_vars + 1)) ⋆
          region c.pWvec (16 * c.max_vars) ⋆ region c.pRepr (8 * c.max_vars) ⋆
          region c.pMinStk (8 * c.minDepth)) ⋆
        (region c.pArena (4 * c.arena_cap) ⋆ region c.pWstk (4 * c.wcap))) ⋆
       (((region c.pWalkVals (2 * c.max_vars) ⋆ region c.pPhases c.max_vars ⋆
           region c.pPhasesTarget c.max_vars ⋆ region c.pPhasesBest c.max_vars ⋆
           region c.pWalkBest c.max_vars) ⋆
         (region c.pHeap (4 * c.max_vars) ⋆ region c.pPos (4 * c.max_vars) ⋆
           region c.pShrinkStk (4 * c.max_vars) ⋆ region c.pQPrev (4 * c.max_vars) ⋆
           region c.pQNext (4 * c.max_vars) ⋆ region c.pQStamp (4 * c.max_vars)) ⋆
         (region c.pWsort (8 * c.max_vars) ⋆ region c.pWorkStk1 (8 * c.max_vars) ⋆
           region c.pWorkStk2 (8 * c.max_vars) ⋆ region c.pTarjanMark (8 * c.max_vars) ⋆
           region c.pTarjanReach (8 * c.max_vars)) ⋆
         (region c.pScore (8 * c.max_vars) ⋆ region c.pSimSig (8 * c.max_vars) ⋆
           region c.pGlueUsed 256 ⋆ region c.pLastLearned 64) ⋆
         (region c.pDelayed (12 * c.delayed_cap) ⋆ region c.pRedRefs (4 * c.red_cap) ⋆
           region c.pExtendStk (4 * c.extend_cap) ⋆ region c.pScratchBuf (4 * c.scratch_cap))) ⋆
        c.pad))) m) : region c.hdr c.avail m :=
  c.regions_to_avail (sep_ac hm)

/-- Non-`vals` remainder of `FullMem` for `kissat_check_model` framing. -/
@[expose] def FullCheckRest (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  array64 (c.hdr + 32) (hdrTailWords c s) ⋆
  array (t := i8) c.pLitMark s.core.lit_mark ⋆ array (t := i8) c.pMark s.core.mrk ⋆
  FullCoreU32A c s.core ⋆ FullCoreU32B c s.core ⋆ FullCoreDynArrs c s.core ⋆
  FullScratchArrays c s.scratch ⋆ c.pad

theorem fullCheckRest_d_irrel (c : FullCfg) (s : FullState) (cur' val' : BitVec 64) :
    FullCheckRest c { s with core := { s.core with d_cur := cur', d_val := val' } } =
      FullCheckRest c s := rfl

private theorem fullCheckRest_to_region {c : FullCfg} {s : FullState}
    {mv' nc' cur' val' : BitVec 64} {m : Mem 64} (hlen : s.LengthsOk c)
    (hm : (dimacsState c.hdr mv' nc' cur' val' ⋆
      region c.pVals (2 * c.max_vars) ⋆ FullCheckRest c s) m) :
    region c.hdr c.avail m := by
  have hmx := c.hmaxv; unfold dimacsBound FullCheckRest FullScratchArrays at *
  have hm1 : ((dimacsState c.hdr mv' nc' cur' val' ⋆ array64 (c.hdr + 32) (hdrTailWords c s)) ⋆
      (((region c.pVals (2 * c.max_vars) ⋆ array (t := i8) c.pLitMark s.core.lit_mark ⋆
          array (t := i8) c.pMark s.core.mrk) ⋆
        FullCoreU32A c s.core ⋆ FullCoreU32B c s.core ⋆ FullCoreDynArrs c s.core) ⋆
       ((FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆ FullScrWksArrs c s.scratch ⋆
         FullScrMetaArrs c s.scratch ⋆ FullScrDynArrs c s.scratch) ⋆ c.pad))) m := sep_ac hm
  refine fullRegs_grouped_to_avail c ?_
  exact sep_mono2
    (sep_mono2 (fun _ hb => dimacsState_to_region hb)
      (fun _ hb => fArr64 (hdrTailWords_length c s) (m := 1120) (by decide) (by decide) hb))
    (sep_mono2
      (sep_mono2 (sep_mono2 (sep_mono2
        (sep_mono2 (sep_mono2 (fun _ hb => hb)
          (fun _ => fArr8 hlen.core_ok.lit_mark_len (by omega)))
          (fun _ => fArr8 hlen.core_ok.mrk_len (by omega)))
        (fun _ => fullCoreU32A_to_regs hlen.core_ok))
        (fun _ => fullCoreU32B_to_regs hlen.core_ok))
        (fun _ => fullCoreDyn_to_regs hlen.core_ok))
      (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2
        (fun _ => fullScrByte_to_regs hlen.scratch_ok)
        (fun _ => fullScrU32A_to_regs hlen.scratch_ok))
        (fun _ => fullScrWks_to_regs hlen.scratch_ok))
        (fun _ => fullScrMeta_to_regs hlen.scratch_ok))
        (fun _ => fullScrDyn_to_regs hlen.scratch_ok))
        (fun _ hb => hb)))
    m hm1

theorem fullMem_anyDimacs_to_region {c : FullCfg} {s : FullState}
    {mv' nc' cur' val' : BitVec 64} {m : Mem 64} (hlen : s.LengthsOk c)
    (hm : (dimacsState c.hdr mv' nc' cur' val' ⋆
      array64 (c.hdr + 32) (hdrTailWords c s) ⋆
      FullCoreArrays c s.core ⋆ FullScratchArrays c s.scratch ⋆ c.pad) m) :
    region c.hdr c.avail m := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hm1 : (array (t := i8) c.pVals s.core.vals ⋆
      (dimacsState c.hdr mv' nc' cur' val' ⋆ FullCheckRest c s)) m := by
    unfold FullCoreArrays FullCoreByteArrs at hm; unfold FullCheckRest; exact sep_ac hm
  have hm2 : (region c.pVals (2 * c.max_vars) ⋆
      (dimacsState c.hdr mv' nc' cur' val' ⋆ FullCheckRest c s)) m :=
    sep_mono (fun _ => fArr8 hlen.core_ok.vals_len (by omega)) hm1
  exact fullCheckRest_to_region (mv' := mv') (nc' := nc') (cur' := cur') (val' := val')
    hlen (sep_ac hm2)

theorem FullArenaInv.to_region {c : FullCfg} {s : FullState} {m : Mem 64}
    (h : FullArenaInv c s m) : region c.hdr c.avail m :=
  fullMem_anyDimacs_to_region h.1 h.2

/-- Alignment decomposition of `region work_ptr wlen` into leading alignment padding + aligned
`FullHdr` arena region (`hdr = work_ptr + pad`, `avail = wlen - pad`). -/
theorem region_work_to_hdr {work_ptr : BitVec 64} {wlen : Nat} {m : Mem 64}
    (hle : fullAlignPad work_ptr + 1152 ≤ wlen) (hfit : wlen ≤ 2 ^ 64)
    (hm : region work_ptr wlen m) :
    (region work_ptr (fullAlignPad work_ptr) ⋆
      region (work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr))
        (wlen - fullAlignPad work_ptr)) m := by
  have heq : fullAlignPad work_ptr + (wlen - fullAlignPad work_ptr) = wlen := by omega
  exact (congrFun (region_merge_eq heq hfit) m).mpr hm

theorem fullMem_to_checkModel {c : FullCfg} {s : FullState}
    {cnf_ptr : BitVec 64} {cnfBytes : List UInt8} {R : Mem 64 → Prop} {m : Mem 64}
    (hlen : s.LengthsOk c) (hm : (bytes cnf_ptr cnfBytes ⋆ FullMem c s ⋆ R) m) :
    (bytes cnf_ptr cnfBytes ⋆
      dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
      bytes c.pVals (s.core.vals.map UInt8.ofBitVec) ⋆
      (FullCheckRest c s ⋆ R)) m := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hm1 : (array (t := i8) c.pVals s.core.vals ⋆
      (bytes cnf_ptr cnfBytes ⋆
        dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
          s.core.d_cur s.core.d_val ⋆
        (FullCheckRest c s ⋆ R))) m := by
    unfold FullMem FullCoreArrays FullCoreByteArrs at hm; unfold FullCheckRest
    exact sep_ac hm
  have hm2 : (bytes c.pVals (s.core.vals.map UInt8.ofBitVec) ⋆
      (bytes cnf_ptr cnfBytes ⋆
        dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
          s.core.d_cur s.core.d_val ⋆
        (FullCheckRest c s ⋆ R))) m := by
    refine sep_mono (fun f hf => ?_) hm1
    have hbytes := array_eq_bytesOf (t := i8) c.pVals s.core.vals
      (by simp [Ty.bytes, Ty.size, i8, hlen.core_ok.vals_len]; omega) hf
    rw [bytesOf_i8_eq_map] at hbytes; exact hbytes.symm
  exact sep_ac hm2

theorem checkModel_post_to_region {c : FullCfg} {s : FullState}
    {mv' nc' cur' val' : BitVec 64} {cnf_ptr : BitVec 64} {cnfBytes : List UInt8}
    {R : Mem 64 → Prop} {m : Mem 64} (hlen : s.LengthsOk c)
    (hm : (bytes cnf_ptr cnfBytes ⋆ dimacsState c.hdr mv' nc' cur' val' ⋆
      bytes c.pVals (s.core.vals.map UInt8.ofBitVec) ⋆ (FullCheckRest c s ⋆ R)) m) :
    (bytes cnf_ptr cnfBytes ⋆ region c.hdr c.avail ⋆ R) m := by
  have hm1 : ((bytes cnf_ptr cnfBytes ⋆ R) ⋆
      (bytes c.pVals (s.core.vals.map UInt8.ofBitVec) ⋆
        (dimacsState c.hdr mv' nc' cur' val' ⋆ FullCheckRest c s))) m := sep_ac hm
  have hm2 : ((bytes cnf_ptr cnfBytes ⋆ R) ⋆ region c.hdr c.avail) m := by
    refine sep_mono_r (fun _ h => ?_) hm1
    have h' : (region c.pVals (2 * c.max_vars) ⋆
        (dimacsState c.hdr mv' nc' cur' val' ⋆ FullCheckRest c s)) _ :=
      sep_mono (fun _ hb => by
        have hb' := bytes_to_region hb; simpa [hlen.core_ok.vals_len] using hb') h
    exact fullCheckRest_to_region (mv' := mv') (nc' := nc') (cur' := cur') (val' := val')
      hlen (sep_ac h')
  exact sep_ac hm2

/-! ## 6. `SafetySlice` instantiations and header / group-focus primitives -/

/-- Primary Stage-4 `SafetySlice`: `FullMem` + `FullState.core` projection + `FullState.LengthsOk`.
Any WalkSAT, VMTF, EVSIDS, rephase, mode-switch, or scratch helper proving
`SafetySlice.spec fullSafetySlice Pre Post` preserves `FullState.core` verbatim (`rfl`). -/
@[expose] def fullSafetySlice (c : FullCfg) : SafetySlice FullState FullCoreState where
  mem := FullMem c
  coreProj := FullState.core
  safe := FullState.LengthsOk c

@[simp] theorem fullSafetySlice_mem (c : FullCfg) : (fullSafetySlice c).mem = FullMem c := rfl
@[simp] theorem fullSafetySlice_coreProj (c : FullCfg) :
    (fullSafetySlice c).coreProj = FullState.core := rfl
@[simp] theorem fullSafetySlice_safe (c : FullCfg) :
    (fullSafetySlice c).safe = FullState.LengthsOk c := rfl

theorem fullCoreState_agrees_with_scratch {c : FullCfg} {s s' : FullState}
    (h : PreservesCoreSlice (fullSafetySlice c).coreProj s s') : s'.core = s.core := h

/-- Values-only `AgreesExcept` mask for `full_extend`: permits mutating only `core.vals`,
preserving every other field of `FullState` (including `cur_vars`, `d_cur`, `d_val`, and `pad`). -/
@[expose] def fullExtendMask (s : FullState) : FullState :=
  { s with core := { s.core with vals := [] } }

@[expose] def fullExtendSlice (c : FullCfg) : SafetySlice FullState FullState :=
  SafetySlice.ofMask (FullMem c) fullExtendMask (FullState.LengthsOk c)

@[simp] theorem fullExtendSlice_mem (c : FullCfg) : (fullExtendSlice c).mem = FullMem c := rfl
@[simp] theorem fullExtendSlice_coreProj (c : FullCfg) :
    (fullExtendSlice c).coreProj = fullExtendMask := rfl
@[simp] theorem fullExtendSlice_safe (c : FullCfg) :
    (fullExtendSlice c).safe = FullState.LengthsOk c := rfl

theorem fullExtend_preserves_nonVals {c : FullCfg} {s s' : FullState}
    (h : PreservesCoreSlice (fullExtendSlice c).coreProj s s') :
    s'.scratch = s.scratch ∧ s'.core.d_cur = s.core.d_cur ∧ s'.core.d_val = s.core.d_val ∧
    s'.core.cur_vars = s.core.cur_vars ∧ s'.core.arena = s.core.arena ∧
    s'.core.arena_len = s.core.arena_len := by
  have hm : fullExtendMask s' = fullExtendMask s := h
  have h1 := congrArg FullState.scratch hm; have h2 := congrArg (fun t => t.core.d_cur) hm
  have h3 := congrArg (fun t => t.core.d_val) hm; have h4 := congrArg (fun t => t.core.cur_vars) hm
  have h5 := congrArg (fun t => t.core.arena) hm; have h6 := congrArg (fun t => t.core.arena_len) hm
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem focus_dimacs {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) :
    (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
      (FullRest c s ⋆ R)) m := by rw [fullMem_eq_dimacs_sep, sep_assoc] at hm; exact hm

theorem unfocus_dimacs {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {cur' val' : BitVec 64} {m' : Mem 64}
    (hm : (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) cur' val' ⋆
      (FullRest c s ⋆ R)) m') :
    (FullMem c { s with core := { s.core with d_cur := cur', d_val := val' } } ⋆ R) m' := by
  rw [fullMem_eq_dimacs_sep, fullRest_d_irrel, sep_assoc]; exact hm

theorem fullHdrTailGet {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (i : Nat) (hi : i < 140) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + BitVec.ofNat 64 (32 + 8 * i)) =
      some ((hdrTailWords c s)[i]'(by simpa using hi)) := by
  have h1 : (array64 (c.hdr + 32) (hdrTailWords c s) ⋆
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
        s.core.d_cur s.core.d_val ⋆
       FullCoreArrays c s.core ⋆ FullScratchArrays c s.scratch ⋆ c.pad ⋆ R)) m := by
    unfold FullMem at hm; exact sep_ac hm
  have hload := loadVal_array64 (i := i) (by simpa using hi) h1
  rwa [show c.hdr + (32 : BitVec 64) + BitVec.ofNat 64 (8 * i) =
    c.hdr + BitVec.ofNat 64 (32 + 8 * i) from ptr_add_ofNat c.hdr 32 (8 * i)] at hload

theorem fullHdrTailPut {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (i : Nat) (hi : i < 140) (v : BitVec 64) (s' : FullState) (hm : (FullMem c s ⋆ R) m)
    (heq : hdrTailWords c s' = (hdrTailWords c s).set i v)
    (hd1 : s'.core.d_cur = s.core.d_cur) (hd2 : s'.core.d_val = s.core.d_val)
    (hca : FullCoreArrays c s'.core = FullCoreArrays c s.core)
    (hsa : FullScratchArrays c s'.scratch = FullScratchArrays c s.scratch) :
    storeOk m i64 (c.hdr + BitVec.ofNat 64 (32 + 8 * i)) ∧
      (FullMem c s' ⋆ R) (storeMem m i64 (c.hdr + BitVec.ofNat 64 (32 + 8 * i)) v) := by
  have h1 : (array64 (c.hdr + 32) (hdrTailWords c s) ⋆
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
        s.core.d_cur s.core.d_val ⋆
       FullCoreArrays c s.core ⋆ FullScratchArrays c s.scratch ⋆ c.pad ⋆ R)) m := by
    unfold FullMem at hm; exact sep_ac hm
  obtain ⟨hok, hst⟩ := store_array64 (i := i) v (by simpa using hi) h1
  rw [show c.hdr + (32 : BitVec 64) + BitVec.ofNat 64 (8 * i) =
    c.hdr + BitVec.ofNat 64 (32 + 8 * i) from ptr_add_ofNat c.hdr 32 (8 * i)] at hok hst
  refine ⟨hok, ?_⟩
  rw [← heq] at hst; unfold FullMem; rw [hd1, hd2, hca, hsa]; exact sep_ac hst

@[expose] def fullCoreOuter (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (hdrTailWords c s) ⋆ FullScratchArrays c s.scratch ⋆ c.pad

@[expose] def fullScrOuter (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (hdrTailWords c s) ⋆ FullCoreArrays c s.core ⋆ c.pad

/-! ## 7. Single-Source-of-Truth Indexed `ArrayField` Table (`41` Arrays) -/

/-- Descriptor for one of the `41` typed arrays owned by `FullMem`. -/
meta structure ArrayFieldSpec where
  ctor : String
  isCore : Bool
  grp : String
  elemTy : String
  ptrFld : String
  idx0 : Bool := false
  deriving Repr, Inhabited

private meta def aCor (c g t p : String) (z : Bool := false) : ArrayFieldSpec :=
  ⟨c, true, g, t, p, z⟩
private meta def aScr (c g t p : String) (z : Bool := false) : ArrayFieldSpec :=
  ⟨c, false, g, t, p, z⟩

/-- Canonical `41`-array table matching `FullCoreArrays` (`17`) and `FullScratchArrays` (`24`). -/
meta def arrayFieldSpecs : Array ArrayFieldSpec := #[
  -- `FullCoreArrays` (`17` arrays)
  aCor "vals" "coreByte" "i8" "pVals", aCor "lit_mark" "coreByte" "i8" "pLitMark",
  aCor "mrk" "coreByte" "i8" "pMark",
  aCor "flags" "coreU32A" "i32" "pFlags", aCor "lvl" "coreU32A" "i32" "pLevel",
  aCor "rsns" "coreU32A" "i32" "pReason", aCor "trl" "coreU32A" "i32" "pTrail",
  aCor "trail_pos" "coreU32A" "i32" "pTrailPos", aCor "tmp" "coreU32A" "i32" "pTmp",
  aCor "min_clr" "coreU32A" "i32" "pMinClr",
  aCor "frame_trail" "coreU32B" "i32" "pFrameTrail",
  aCor "frame_dec" "coreU32B" "i32" "pFrameDec", aCor "wvec" "coreU32B" "i32" "pWvec",
  aCor "repr" "coreU32B" "i32" "pRepr", aCor "min_stk" "coreU32B" "i32" "pMinStk" true,
  aCor "arena" "coreDyn" "i32" "pArena", aCor "wstk" "coreDyn" "i32" "pWstk" true,
  -- `FullScratchArrays` (`24` arrays)
  aScr "walk_vals" "scrByte" "i8" "pWalkVals", aScr "phases" "scrByte" "i8" "pPhases",
  aScr "phases_target" "scrByte" "i8" "pPhasesTarget",
  aScr "phases_best" "scrByte" "i8" "pPhasesBest", aScr "walk_best" "scrByte" "i8" "pWalkBest",
  aScr "heap" "scrU32A" "i32" "pHeap" true, aScr "pos" "scrU32A" "i32" "pPos",
  aScr "shrink_stk" "scrU32A" "i32" "pShrinkStk", aScr "q_prev" "scrU32A" "i32" "pQPrev",
  aScr "q_next" "scrU32A" "i32" "pQNext", aScr "q_stamp" "scrU32A" "i32" "pQStamp",
  aScr "wsort" "scrWks" "i32" "pWsort" true, aScr "work_stk1" "scrWks" "i32" "pWorkStk1",
  aScr "work_stk2" "scrWks" "i32" "pWorkStk2", aScr "tarjan_mark" "scrWks" "i32" "pTarjanMark",
  aScr "tarjan_reach" "scrWks" "i32" "pTarjanReach",
  aScr "score" "scrMeta" "i64" "pScore", aScr "sim_sig" "scrMeta" "i64" "pSimSig",
  aScr "glue_used" "scrMeta" "i32" "pGlueUsed", aScr "last_learned" "scrMeta" "i32" "pLastLearned",
  aScr "delayed" "scrDyn" "i32" "pDelayed", aScr "red_refs" "scrDyn" "i32" "pRedRefs",
  aScr "extend_stk" "scrDyn" "i32" "pExtendStk", aScr "scratch_buf" "scrDyn" "i32" "pScratchBuf"
]

private meta def arrGrpDefName : String → String
  | "coreByte" => "FullCoreByteArrs" | "coreU32A" => "FullCoreU32A"
  | "coreU32B" => "FullCoreU32B" | "coreDyn" => "FullCoreDynArrs"
  | "scrByte" => "FullScrByteArrs" | "scrU32A" => "FullScrU32A"
  | "scrWks" => "FullScrWksArrs" | "scrMeta" => "FullScrMetaArrs"
  | _ => "FullScrDynArrs"

private meta def arrGrpOuterExpr (g : String) : String :=
  let coreGrps := #["coreByte", "coreU32A", "coreU32B", "coreDyn"]
  let scrGrps := #["scrByte", "scrU32A", "scrWks", "scrMeta", "scrDyn"]
  let isCore := coreGrps.contains g
  let (grps, sub, outer) :=
    if isCore then (coreGrps, "s.core", "fullCoreOuter c s")
    else (scrGrps, "s.scratch", "fullScrOuter c s")
  let others := (grps.filter (· != g)).map fun o => s!"{arrGrpDefName o} c {sub}"
  "(" ++ String.intercalate " ⋆ " (others.toList ++ [outer]) ++ ")"

local elab "gen_full_array_table!" : command => do
  if arrayFieldSpecs.size != 41 then
    throwError "arrayFieldSpecs must have 41 entries, got {arrayFieldSpecs.size}"
  for g in #["coreByte", "coreU32A", "coreU32B", "coreDyn",
             "scrByte", "scrU32A", "scrWks", "scrMeta", "scrDyn"] do
    let isCore := g.startsWith "core"
    let (sub, arrs, outer) :=
      if isCore then ("s.core", "FullCoreArrays", "fullCoreOuter")
      else ("s.scratch", "FullScratchArrays", "fullScrOuter")
    elabSrcCmd s!"fullMem_eq_{g}" <|
      s!"theorem fullMem_eq_{g} (c : FullCfg) (s : FullState) :\n" ++
      s!"    FullMem c s = ({arrGrpDefName g} c {sub} ⋆ {arrGrpOuterExpr g}) := by\n" ++
      s!"  unfold FullMem {arrs} {outer}; ac_rfl"
  let mut ctors : Array String := #[]
  let mut tyArms : Array String := #[]
  let mut ptrArms : Array String := #[]
  let mut getArms : Array String := #[]
  let mut setArms : Array String := #[]
  let mut restArms : Array String := #[]
  let mut focusArms : Array String := #[]
  for sp in arrayFieldSpecs do
    let sub := if sp.isCore then "core" else "scratch"
    ctors := ctors.push s!"  | {sp.ctor}"
    tyArms := tyArms.push s!"  | .{sp.ctor} => {sp.elemTy}"
    ptrArms := ptrArms.push s!"  | .{sp.ctor} => c.{sp.ptrFld}"
    getArms := getArms.push s!"  | .{sp.ctor} => s.{sub}.{sp.ctor}"
    setArms := setArms.push
      s!"  | .{sp.ctor} => fun xs => \{ s with {sub} := \{ s.{sub} with {sp.ctor} := xs } }"
    let peers := (arrayFieldSpecs.filter fun o => o.grp == sp.grp && o.ctor != sp.ctor).map fun o =>
      let osub := if o.isCore then "core" else "scratch"
      if o.elemTy == "i64" then s!"array64 c.{o.ptrFld} s.{osub}.{o.ctor}"
      else s!"array (t := {o.elemTy}) c.{o.ptrFld} s.{osub}.{o.ctor}"
    let restExpr := String.intercalate " ⋆ " (peers.toList ++ [arrGrpOuterExpr sp.grp])
    restArms := restArms.push s!"  | .{sp.ctor} => {restExpr}"
    let arr64Rw := if sp.elemTy == "i64" then " simp only [array64_eq_array];" else ""
    focusArms := focusArms.push <|
      s!"  | {sp.ctor} => rw [fullMem_eq_{sp.grp}]; unfold {arrGrpDefName sp.grp};" ++
      s!" dsimp only [ArrayField.elemTy, ArrayField.ptr, ArrayField.get, ArrayField.rest];" ++
      s!"{arr64Rw} ac_rfl"
  elabSrcCmd "ArrayField" <|
    "inductive ArrayField where\n" ++ String.intercalate "\n" ctors.toList ++
    "\n  deriving DecidableEq, Repr"
  elabSrcCmd "ArrayField.elemTy" <|
    "@[expose] def ArrayField.elemTy : ArrayField → Ty\n" ++ String.intercalate "\n" tyArms.toList
  elabSrcCmd "ArrayField.ptr" <|
    "@[expose] def ArrayField.ptr (a : ArrayField) (c : FullCfg) : BitVec 64 :=\n" ++
    "  match a with\n" ++ String.intercalate "\n" ptrArms.toList
  elabSrcCmd "ArrayField.get" <|
    "@[expose] def ArrayField.get (a : ArrayField) (s : FullState) : List (Val a.elemTy) :=\n" ++
    "  match a with\n" ++ String.intercalate "\n" getArms.toList
  elabSrcCmd "ArrayField.set" <|
    "@[expose] def ArrayField.set (a : ArrayField) (s : FullState) :\n" ++
    "    List (Val a.elemTy) → FullState :=\n  match a with\n" ++
    String.intercalate "\n" setArms.toList
  elabSrcCmd "ArrayField.rest" <|
    "@[expose] def ArrayField.rest (a : ArrayField) (c : FullCfg) (s : FullState) :\n" ++
    "    Mem 64 → Prop :=\n  match a with\n" ++ String.intercalate "\n" restArms.toList
  elabSrcCmd "ArrayField.focus_eq" <|
    "theorem ArrayField.focus_eq (a : ArrayField) (c : FullCfg) (s : FullState) :\n" ++
    "    FullMem c s = (array (t := a.elemTy) (a.ptr c) (a.get s) ⋆ a.rest c s) := by\n" ++
    "  cases a with\n" ++ String.intercalate "\n" focusArms.toList

gen_full_array_table!

namespace ArrayField

@[expose] def elemAddr (a : ArrayField) (c : FullCfg) (i : Nat) : BitVec 64 :=
  match a.elemTy with
  | .bits 8 => a.ptr c + BitVec.ofNat 64 i
  | .bits 32 => a.ptr c + BitVec.ofNat 64 (4 * i)
  | _ => a.ptr c + BitVec.ofNat 64 (8 * i)

@[expose] def elemAddrBv (a : ArrayField) (c : FullCfg) (i : BitVec 64) : BitVec 64 :=
  match a.elemTy with
  | .bits 8 => a.ptr c + i
  | .bits 32 => a.ptr c + i * 4
  | _ => a.ptr c + i * 8

theorem elemTy_cases (a : ArrayField) : a.elemTy = i8 ∨ a.elemTy = i32 ∨ a.elemTy = i64 := by
  cases a <;> simp [elemTy]

theorem get_set (a : ArrayField) (s : FullState) (xs : List (Val a.elemTy)) :
    a.get (a.set s xs) = xs := by
  cases a <;> rfl

theorem rest_set (a : ArrayField) (c : FullCfg) (s : FullState) (xs : List (Val a.elemTy)) :
    a.rest c (a.set s xs) = a.rest c s := by
  cases a <;> rfl

theorem focus (a : ArrayField) {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) :
    (array (t := a.elemTy) (a.ptr c) (a.get s) ⋆ (a.rest c s ⋆ R)) m := by
  rw [a.focus_eq, sep_assoc] at hm; exact hm

theorem unfocus (a : ArrayField) {c : FullCfg} {s : FullState} {xs : List (Val a.elemTy)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (array (t := a.elemTy) (a.ptr c) xs ⋆ (a.rest c s ⋆ R)) m) :
    (FullMem c (a.set s xs) ⋆ R) m := by
  rw [a.focus_eq, a.get_set, a.rest_set, sep_assoc]; exact hm

end ArrayField

end LeanQbe.T.Examples.Kissat.Proof.Spec
