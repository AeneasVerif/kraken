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

/-!
# Kissat `D-Full` Arena Layout, State, and Memory Bridges — Part 1 (`Stage 4`)

Defines:
1. `fullMinDepthOf`, `u32FullBytes`, `fullFixedBytes`, and `FullCfg` matching frozen `FullHdr`
   (`144` `u64` words = `1,152` bytes, offsets `0..1144`, `41` contiguous arrays) and
   `regions_to_avail`.
2. `FullScratch` (non-soundness heuristic / phase / WalkSAT / VMTF queue / Tarjan / sim /
   extend / scratch arrays and stat scalars) separated from soundness-bearing `FullCoreState`
   and `FullState`, with `LengthsOk` and the `140`-word `hdrTailWords` projection.
3. `FullMem`, `FullArenaInv`, `FullCheckRest`, `fullMem_anyDimacs_to_region`, and `check_model` /
   alignment framing bridges (`fullMem_to_checkModel`, `checkModel_post_to_region`,
   `region_work_to_hdr`).
4. `C0Agrees.SafetySlice` instantiations (`fullSafetySlice`, `fullExtendSlice`) and group-focus
   header/array primitives (zero global tactic attributes).
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

private theorem fPair {a : BitVec 64} {n1 n2 n : Nat}
    (hn : n1 + n2 = n) (hfit : n ≤ 2 ^ 64) {f : Mem 64}
    (hf : (region a n1 ⋆ region (a + BitVec.ofNat 64 n1) n2) f) : region a n f :=
  (congrFun (region_merge_eq hn hfit) f).mp hf

private theorem fStep {P : Mem 64 → Prop} {m0 : Mem 64} {n1 n2 : Nat} {a1 a2 : BitVec 64}
    (h : (region a1 n1 ⋆ (region a2 n2 ⋆ P)) m0)
    (hadd : a2 = a1 + BitVec.ofNat 64 n1) (hfit : n1 + n2 ≤ 2 ^ 64) :
    (region a1 (n1 + n2) ⋆ P) m0 := by
  rw [← sep_assoc, hadd] at h
  rwa [region_merge_eq rfl hfit] at h

private theorem fStep2 {m0 : Mem 64} {n1 n2 : Nat} {a1 a2 : BitVec 64}
    (h : (region a1 n1 ⋆ region a2 n2) m0)
    (hadd : a2 = a1 + BitVec.ofNat 64 n1) (hfit : n1 + n2 ≤ 2 ^ 64) :
    region a1 (n1 + n2) m0 := by
  rw [hadd] at h
  rwa [region_merge_eq rfl hfit] at h

private theorem rassoc5 {A B C D E : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ B ⋆ C ⋆ D ⋆ E) m) : (A ⋆ (B ⋆ (C ⋆ (D ⋆ E)))) m := sep_ac h

private theorem rassoc6 {A B C D E F : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ B ⋆ C ⋆ D ⋆ E ⋆ F) m) : (A ⋆ (B ⋆ (C ⋆ (D ⋆ (E ⋆ F))))) m := sep_ac h

private theorem collapse_u32_5 {a1 a2 a3 a4 a5 : BitVec 64} {n1 n2 n3 n4 n5 u : Nat}
    {m0 : Mem 64}
    (h2 : a2 = a1 + BitVec.ofNat 64 u) (h3 : a3 = a2 + BitVec.ofNat 64 u)
    (h4 : a4 = a3 + BitVec.ofNat 64 u) (h5 : a5 = a4 + BitVec.ofNat 64 u)
    (hle1 : n1 ≤ u) (hle2 : n2 ≤ u) (hle3 : n3 ≤ u) (hle4 : n4 ≤ u) (hle5 : n5 ≤ u)
    (hfit : 5 * u ≤ 2 ^ 64)
    (hf : ((region a1 n1 ⋆ region a2 n2 ⋆ region a3 n3 ⋆ region a4 n4 ⋆ region a5 n5) ⋆
      (region (a1 + BitVec.ofNat 64 n1) (u - n1) ⋆ region (a2 + BitVec.ofNat 64 n2) (u - n2) ⋆
       region (a3 + BitVec.ofNat 64 n3) (u - n3) ⋆ region (a4 + BitVec.ofNat 64 n4) (u - n4) ⋆
       region (a5 + BitVec.ofNat 64 n5) (u - n5))) m0) :
    region a1 (5 * u) m0 := by
  have zip5 : ∀ {A B C D E A' B' C' D' E' : Mem 64 → Prop} {k : Mem 64},
      ((A ⋆ B ⋆ C ⋆ D ⋆ E) ⋆ (A' ⋆ B' ⋆ C' ⋆ D' ⋆ E')) k →
      ((A ⋆ A') ⋆ (B ⋆ B') ⋆ (C ⋆ C') ⋆ (D ⋆ D') ⋆ (E ⋆ E')) k := fun x => sep_ac x
  have r1 : (region a1 u ⋆ region a2 u ⋆ region a3 u ⋆ region a4 u ⋆ region a5 u) m0 :=
    sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2
      (fun _ => fPair (n := u) (by omega) (by omega))
      (fun _ => fPair (n := u) (by omega) (by omega)))
      (fun _ => fPair (n := u) (by omega) (by omega)))
      (fun _ => fPair (n := u) (by omega) (by omega)))
      (fun _ => fPair (n := u) (by omega) (by omega)) m0 (zip5 hf)
  have r2 := rassoc5 r1
  have s1 := fStep r2 h2 (by omega)
  have h3' : a3 = a1 + BitVec.ofNat 64 (u + u) := by rw [h3, h2, ptr_add_ofNat]
  have s2 := fStep s1 h3' (by omega)
  have h4' : a4 = a1 + BitVec.ofNat 64 (u + u + u) := by rw [h4, h3', ptr_add_ofNat]
  have s3 := fStep s2 h4' (by omega)
  have h5' : a5 = a1 + BitVec.ofNat 64 (u + u + u + u) := by rw [h5, h4', ptr_add_ofNat]
  have s4 := fStep2 s3 h5' (by omega)
  rwa [show u + u + u + u + u = 5 * u by omega] at s4

private theorem collapse_bytes (c : FullCfg) {m : Mem 64}
    (hf : ((region c.hdr 32 ⋆ region (c.hdr + BitVec.ofNat 64 32) 1120) ⋆
      ((region c.pVals (2 * c.max_vars) ⋆ region c.pWalkVals (2 * c.max_vars) ⋆
        region c.pLitMark (2 * c.max_vars)) ⋆
       (region c.pMark c.max_vars ⋆ region c.pPhases c.max_vars ⋆
        region c.pPhasesTarget c.max_vars ⋆ region c.pPhasesBest c.max_vars ⋆
        region c.pWalkBest c.max_vars)) ⋆ c.padBytes) m) :
    region c.hdr (1152 + 3 * valsBytes c.max_vars + 5 * markBytes c.max_vars) m := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hv := valsBytes_ge c.max_vars; have hmk := markBytes_ge c.max_vars
  have hvlt : valsBytes c.max_vars ≤ 2 * c.max_vars + 7 := by unfold valsBytes; omega
  have hmlt : markBytes c.max_vars ≤ c.max_vars + 7 := by unfold markBytes; omega
  have hhdr : (region c.hdr 32 ⋆ region (c.hdr + BitVec.ofNat 64 32) 1120) =
      region c.hdr 1152 := region_merge_eq (by decide) (by decide)
  rw [hhdr] at hf; unfold padBytes at hf
  have reorg : ∀ {H V1 V2 V3 M1 M2 M3 M4 M5 PV1 PV2 PV3 PM1 PM2 PM3 PM4 PM5 : Mem 64 → Prop}
      {k : Mem 64},
      (H ⋆ ((V1 ⋆ V2 ⋆ V3) ⋆ (M1 ⋆ M2 ⋆ M3 ⋆ M4 ⋆ M5)) ⋆
        (PV1 ⋆ PV2 ⋆ PV3 ⋆ PM1 ⋆ PM2 ⋆ PM3 ⋆ PM4 ⋆ PM5)) k →
      (H ⋆ (((V1 ⋆ PV1) ⋆ (V2 ⋆ PV2) ⋆ (V3 ⋆ PV3)) ⋆
        ((M1 ⋆ PM1) ⋆ (M2 ⋆ PM2) ⋆ (M3 ⋆ PM3) ⋆ (M4 ⋆ PM4) ⋆ (M5 ⋆ PM5)))) k := fun x => sep_ac x
  have hzip := reorg hf
  have hvs : (region c.pVals (2 * c.max_vars) ⋆
        region (c.pVals + BitVec.ofNat 64 (2 * c.max_vars))
          (valsBytes c.max_vars - 2 * c.max_vars)) ⋆
      (region c.pWalkVals (2 * c.max_vars) ⋆
        region (c.pWalkVals + BitVec.ofNat 64 (2 * c.max_vars))
          (valsBytes c.max_vars - 2 * c.max_vars)) ⋆
      (region c.pLitMark (2 * c.max_vars) ⋆
        region (c.pLitMark + BitVec.ofNat 64 (2 * c.max_vars))
          (valsBytes c.max_vars - 2 * c.max_vars)) =
      (region c.pVals (valsBytes c.max_vars) ⋆ region c.pWalkVals (valsBytes c.max_vars) ⋆
        region c.pLitMark (valsBytes c.max_vars)) := by
    rw [region_merge_eq (n := valsBytes c.max_vars) (by omega) (by omega),
      region_merge_eq (n := valsBytes c.max_vars) (by omega) (by omega),
      region_merge_eq (n := valsBytes c.max_vars) (by omega) (by omega)]
  have hms : (region c.pMark c.max_vars ⋆
        region (c.pMark + BitVec.ofNat 64 c.max_vars) (markBytes c.max_vars - c.max_vars)) ⋆
      (region c.pPhases c.max_vars ⋆
        region (c.pPhases + BitVec.ofNat 64 c.max_vars) (markBytes c.max_vars - c.max_vars)) ⋆
      (region c.pPhasesTarget c.max_vars ⋆
        region (c.pPhasesTarget + BitVec.ofNat 64 c.max_vars)
          (markBytes c.max_vars - c.max_vars)) ⋆
      (region c.pPhasesBest c.max_vars ⋆
        region (c.pPhasesBest + BitVec.ofNat 64 c.max_vars) (markBytes c.max_vars - c.max_vars)) ⋆
      (region c.pWalkBest c.max_vars ⋆
        region (c.pWalkBest + BitVec.ofNat 64 c.max_vars) (markBytes c.max_vars - c.max_vars)) =
      (region c.pMark (markBytes c.max_vars) ⋆ region c.pPhases (markBytes c.max_vars) ⋆
        region c.pPhasesTarget (markBytes c.max_vars) ⋆
        region c.pPhasesBest (markBytes c.max_vars) ⋆
        region c.pWalkBest (markBytes c.max_vars)) := by
    rw [region_merge_eq (n := markBytes c.max_vars) (by omega) (by omega),
      region_merge_eq (n := markBytes c.max_vars) (by omega) (by omega),
      region_merge_eq (n := markBytes c.max_vars) (by omega) (by omega),
      region_merge_eq (n := markBytes c.max_vars) (by omega) (by omega),
      region_merge_eq (n := markBytes c.max_vars) (by omega) (by omega)]
  rw [hvs, hms] at hzip
  have flat : ∀ {H V1 V2 V3 M1 M2 M3 M4 M5 : Mem 64 → Prop} {k : Mem 64},
      (H ⋆ ((V1 ⋆ V2 ⋆ V3) ⋆ (M1 ⋆ M2 ⋆ M3 ⋆ M4 ⋆ M5))) k →
      (H ⋆ (V1 ⋆ (V2 ⋆ (V3 ⋆ (M1 ⋆ (M2 ⋆ (M3 ⋆ (M4 ⋆ M5)))))))) k := fun x => sep_ac x
  have h1 := flat hzip
  have s1 := fStep h1 rfl (by omega)
  have ha2' : c.pWalkVals = c.hdr + BitVec.ofNat 64 (1152 + valsBytes c.max_vars) := by
    rw [FullCfg.pWalkVals, FullCfg.pVals, ptr_add_ofNat]
  have s2 := fStep s1 ha2' (by omega)
  have ha3' : c.pLitMark =
      c.hdr + BitVec.ofNat 64 (1152 + valsBytes c.max_vars + valsBytes c.max_vars) := by
    rw [FullCfg.pLitMark, ha2', ptr_add_ofNat]
  have s3 := fStep s2 ha3' (by omega)
  have ha4' : c.pMark = c.hdr + BitVec.ofNat 64
      (1152 + valsBytes c.max_vars + valsBytes c.max_vars + valsBytes c.max_vars) := by
    rw [FullCfg.pMark, ha3', ptr_add_ofNat]
  have s4 := fStep s3 ha4' (by omega)
  have ha5' : c.pPhases = c.hdr + BitVec.ofNat 64 (1152 + valsBytes c.max_vars +
      valsBytes c.max_vars + valsBytes c.max_vars + markBytes c.max_vars) := by
    rw [FullCfg.pPhases, ha4', ptr_add_ofNat]
  have s5 := fStep s4 ha5' (by omega)
  have ha6' : c.pPhasesTarget = c.hdr + BitVec.ofNat 64 (1152 + valsBytes c.max_vars +
      valsBytes c.max_vars + valsBytes c.max_vars + markBytes c.max_vars +
      markBytes c.max_vars) := by
    rw [FullCfg.pPhasesTarget, ha5', ptr_add_ofNat]
  have s6 := fStep s5 ha6' (by omega)
  have ha7' : c.pPhasesBest = c.hdr + BitVec.ofNat 64 (1152 + valsBytes c.max_vars +
      valsBytes c.max_vars + valsBytes c.max_vars + markBytes c.max_vars + markBytes c.max_vars +
      markBytes c.max_vars) := by
    rw [FullCfg.pPhasesBest, ha6', ptr_add_ofNat]
  have s7 := fStep s6 ha7' (by omega)
  have ha8' : c.pWalkBest = c.hdr + BitVec.ofNat 64 (1152 + valsBytes c.max_vars +
      valsBytes c.max_vars + valsBytes c.max_vars + markBytes c.max_vars + markBytes c.max_vars +
      markBytes c.max_vars + markBytes c.max_vars) := by
    rw [FullCfg.pWalkBest, ha7', ptr_add_ofNat]
  have s8 := fStep2 s7 ha8' (by omega)
  rwa [show 1152 + valsBytes c.max_vars + valsBytes c.max_vars + valsBytes c.max_vars +
      markBytes c.max_vars + markBytes c.max_vars + markBytes c.max_vars + markBytes c.max_vars +
      markBytes c.max_vars =
      1152 + 3 * valsBytes c.max_vars + 5 * markBytes c.max_vars by omega] at s8

private theorem collapse_tail (c : FullCfg) {m : Mem 64}
    (hf : ((region c.pWvec (16 * c.max_vars) ⋆ region c.pRepr (8 * c.max_vars) ⋆
        region c.pWsort (8 * c.max_vars) ⋆ region c.pWorkStk1 (8 * c.max_vars) ⋆
        region c.pWorkStk2 (8 * c.max_vars) ⋆ region c.pTarjanMark (8 * c.max_vars) ⋆
        region c.pTarjanReach (8 * c.max_vars) ⋆ region c.pScore (8 * c.max_vars) ⋆
        region c.pSimSig (8 * c.max_vars)) ⋆
      (region c.pMinStk (8 * c.minDepth) ⋆ region c.pGlueUsed 256 ⋆
        region c.pLastLearned 64 ⋆ region c.pArena (4 * c.arena_cap) ⋆
        region c.pWstk (4 * c.wcap) ⋆ region c.pDelayed (12 * c.delayed_cap) ⋆
        region c.pRedRefs (4 * c.red_cap) ⋆ region c.pExtendStk (4 * c.extend_cap) ⋆
        region c.pScratchBuf (4 * c.scratch_cap)) ⋆
      region c.pSlack c.slack) m) :
    region c.pWvec (c.avail - (1152 + 3 * valsBytes c.max_vars + 5 * markBytes c.max_vars +
      15 * u32FullBytes c.max_vars)) m := by
  have hfit := c.havail_fit; have hsz := c.hsize; have hmx := c.hmaxv
  have ha := c.harena; have hw := c.hwcap; have hd := c.hdel
  have hr := c.hred; have he := c.hext; have hs := c.hscr
  have hmd := fullMinDepthOf_le c.max_vars
  have hmd_pos := fullMinDepthOf_pos c.max_vars
  unfold dimacsBound at hmx ha hw hd hr he hs
  have hslack_eq : c.slack = c.avail - (fullFixedBytes c.max_vars + 4 * c.arena_cap +
      4 * c.wcap + 12 * c.delayed_cap + 4 * c.red_cap + 4 * c.extend_cap +
      4 * c.scratch_cap) := rfl
  have hfb_eq : fullFixedBytes c.max_vars = 1472 + 3 * valsBytes c.max_vars +
      5 * markBytes c.max_vars + 15 * u32FullBytes c.max_vars + 80 * c.max_vars +
      8 * c.minDepth := rfl
  have hsz' : fullFixedBytes c.max_vars + 4 * c.arena_cap + 4 * c.wcap + 12 * c.delayed_cap +
      4 * c.red_cap + 4 * c.extend_cap + 4 * c.scratch_cap ≤ c.avail := hsz
  have spl1 : ∀ {k : Mem 64}, (region c.pWvec (16 * c.max_vars) ⋆ region c.pRepr (8 * c.max_vars) ⋆
      region c.pWsort (8 * c.max_vars) ⋆ region c.pWorkStk1 (8 * c.max_vars) ⋆
      region c.pWorkStk2 (8 * c.max_vars) ⋆ region c.pTarjanMark (8 * c.max_vars) ⋆
      region c.pTarjanReach (8 * c.max_vars) ⋆ region c.pScore (8 * c.max_vars) ⋆
      region c.pSimSig (8 * c.max_vars)) k → region c.pWvec (80 * c.max_vars) k := by
    intro k hk
    have r9 : (region c.pWvec (16 * c.max_vars) ⋆ (region c.pRepr (8 * c.max_vars) ⋆
        (region c.pWsort (8 * c.max_vars) ⋆ (region c.pWorkStk1 (8 * c.max_vars) ⋆
        (region c.pWorkStk2 (8 * c.max_vars) ⋆ (region c.pTarjanMark (8 * c.max_vars) ⋆
        (region c.pTarjanReach (8 * c.max_vars) ⋆ (region c.pScore (8 * c.max_vars) ⋆
        region c.pSimSig (8 * c.max_vars))))))))) k := sep_ac hk
    have a1 : c.pRepr = c.pWvec + BitVec.ofNat 64 (16 * c.max_vars) := rfl
    have a2 : c.pWsort = c.pWvec + BitVec.ofNat 64 (16 * c.max_vars + 8 * c.max_vars) := by
      unfold pWsort; rw [a1, ptr_add_ofNat]
    have a3 : c.pWorkStk1 =
        c.pWvec + BitVec.ofNat 64 (16 * c.max_vars + 8 * c.max_vars + 8 * c.max_vars) := by
      unfold pWorkStk1; rw [a2, ptr_add_ofNat]
    have a4 : c.pWorkStk2 = c.pWvec + BitVec.ofNat 64
        (16 * c.max_vars + 8 * c.max_vars + 8 * c.max_vars + 8 * c.max_vars) := by
      unfold pWorkStk2; rw [a3, ptr_add_ofNat]
    have a5 : c.pTarjanMark = c.pWvec + BitVec.ofNat 64 (16 * c.max_vars + 8 * c.max_vars +
        8 * c.max_vars + 8 * c.max_vars + 8 * c.max_vars) := by
      unfold pTarjanMark; rw [a4, ptr_add_ofNat]
    have a6 : c.pTarjanReach = c.pWvec + BitVec.ofNat 64 (16 * c.max_vars + 8 * c.max_vars +
        8 * c.max_vars + 8 * c.max_vars + 8 * c.max_vars + 8 * c.max_vars) := by
      unfold pTarjanReach; rw [a5, ptr_add_ofNat]
    have a7 : c.pScore = c.pWvec + BitVec.ofNat 64 (16 * c.max_vars + 8 * c.max_vars +
        8 * c.max_vars + 8 * c.max_vars + 8 * c.max_vars + 8 * c.max_vars + 8 * c.max_vars) := by
      unfold pScore; rw [a6, ptr_add_ofNat]
    have a8 : c.pSimSig = c.pWvec + BitVec.ofNat 64 (16 * c.max_vars + 8 * c.max_vars +
        8 * c.max_vars + 8 * c.max_vars + 8 * c.max_vars + 8 * c.max_vars + 8 * c.max_vars +
        8 * c.max_vars) := by
      unfold pSimSig; rw [a7, ptr_add_ofNat]
    have s := fStep2 (fStep (fStep (fStep (fStep (fStep (fStep (fStep r9 a1 (by omega))
      a2 (by omega)) a3 (by omega)) a4 (by omega)) a5 (by omega)) a6 (by omega)) a7 (by omega))
      a8 (by omega)
    rwa [show 16 * c.max_vars + 8 * c.max_vars + 8 * c.max_vars + 8 * c.max_vars +
        8 * c.max_vars + 8 * c.max_vars + 8 * c.max_vars + 8 * c.max_vars + 8 * c.max_vars =
        80 * c.max_vars by omega] at s
  have hrem_bound : 8 * c.minDepth + 320 + 4 * c.arena_cap + 4 * c.wcap + 12 * c.delayed_cap +
      4 * c.red_cap + 4 * c.extend_cap + 4 * c.scratch_cap + c.slack ≤ c.avail ∧
      8 * c.minDepth + 256 + 64 + 4 * c.arena_cap + 4 * c.wcap + 12 * c.delayed_cap +
      4 * c.red_cap + 4 * c.extend_cap + 4 * c.scratch_cap + c.slack =
      c.avail - (1152 + 3 * valsBytes c.max_vars + 5 * markBytes c.max_vars +
        15 * u32FullBytes c.max_vars + 80 * c.max_vars) := by
    rw [hslack_eq, hfb_eq] at *; change _ ≤ _ ∧ _ at *; constructor <;> omega
  have spl2 : ∀ {k : Mem 64}, (region c.pMinStk (8 * c.minDepth) ⋆ region c.pGlueUsed 256 ⋆
      region c.pLastLearned 64 ⋆ region c.pArena (4 * c.arena_cap) ⋆
      region c.pWstk (4 * c.wcap) ⋆ region c.pDelayed (12 * c.delayed_cap) ⋆
      region c.pRedRefs (4 * c.red_cap) ⋆ region c.pExtendStk (4 * c.extend_cap) ⋆
      region c.pScratchBuf (4 * c.scratch_cap) ⋆ region c.pSlack c.slack) k →
      region c.pMinStk (c.avail - (1152 + 3 * valsBytes c.max_vars + 5 * markBytes c.max_vars +
        15 * u32FullBytes c.max_vars + 80 * c.max_vars)) k := by
    intro k hk
    have hm_le : c.minDepth ≤ 1000 := hmd
    have r10 : (region c.pMinStk (8 * c.minDepth) ⋆ (region c.pGlueUsed 256 ⋆
        (region c.pLastLearned 64 ⋆ (region c.pArena (4 * c.arena_cap) ⋆
        (region c.pWstk (4 * c.wcap) ⋆ (region c.pDelayed (12 * c.delayed_cap) ⋆
        (region c.pRedRefs (4 * c.red_cap) ⋆ (region c.pExtendStk (4 * c.extend_cap) ⋆
        (region c.pScratchBuf (4 * c.scratch_cap) ⋆ region c.pSlack c.slack))))))))) k :=
      sep_ac hk
    have a1 : c.pGlueUsed = c.pMinStk + BitVec.ofNat 64 (8 * c.minDepth) := rfl
    have a2 : c.pLastLearned = c.pMinStk + BitVec.ofNat 64 (8 * c.minDepth + 256) := by
      unfold pLastLearned; rw [a1, ptr_add_ofNat]
    have a3 : c.pArena = c.pMinStk + BitVec.ofNat 64 (8 * c.minDepth + 256 + 64) := by
      unfold pArena; rw [a2, ptr_add_ofNat]
    have a4 : c.pWstk =
        c.pMinStk + BitVec.ofNat 64 (8 * c.minDepth + 256 + 64 + 4 * c.arena_cap) := by
      unfold pWstk; rw [a3, ptr_add_ofNat]
    have a5 : c.pDelayed = c.pMinStk +
        BitVec.ofNat 64 (8 * c.minDepth + 256 + 64 + 4 * c.arena_cap + 4 * c.wcap) := by
      unfold pDelayed; rw [a4, ptr_add_ofNat]
    have a6 : c.pRedRefs = c.pMinStk + BitVec.ofNat 64
        (8 * c.minDepth + 256 + 64 + 4 * c.arena_cap + 4 * c.wcap + 12 * c.delayed_cap) := by
      unfold pRedRefs; rw [a5, ptr_add_ofNat]
    have a7 : c.pExtendStk = c.pMinStk + BitVec.ofNat 64 (8 * c.minDepth + 256 + 64 +
        4 * c.arena_cap + 4 * c.wcap + 12 * c.delayed_cap + 4 * c.red_cap) := by
      unfold pExtendStk; rw [a6, ptr_add_ofNat]
    have a8 : c.pScratchBuf = c.pMinStk + BitVec.ofNat 64 (8 * c.minDepth + 256 + 64 +
        4 * c.arena_cap + 4 * c.wcap + 12 * c.delayed_cap + 4 * c.red_cap + 4 * c.extend_cap) := by
      unfold pScratchBuf; rw [a7, ptr_add_ofNat]
    have a9 : c.pSlack = c.pMinStk + BitVec.ofNat 64 (8 * c.minDepth + 256 + 64 +
        4 * c.arena_cap + 4 * c.wcap + 12 * c.delayed_cap + 4 * c.red_cap + 4 * c.extend_cap +
        4 * c.scratch_cap) := by
      unfold pSlack; rw [a8, ptr_add_ofNat]
    have s := fStep2 (fStep (fStep (fStep (fStep (fStep (fStep (fStep (fStep r10 a1
      (by omega)) a2 (by omega)) a3 (by omega)) a4 (by omega)) a5 (by omega)) a6 (by omega))
      a7 (by omega)) a8 (by omega)) a9 (by omega)
    rwa [hrem_bound.2] at s
  have htop : ((region c.pWvec (16 * c.max_vars) ⋆ region c.pRepr (8 * c.max_vars) ⋆
        region c.pWsort (8 * c.max_vars) ⋆ region c.pWorkStk1 (8 * c.max_vars) ⋆
        region c.pWorkStk2 (8 * c.max_vars) ⋆ region c.pTarjanMark (8 * c.max_vars) ⋆
        region c.pTarjanReach (8 * c.max_vars) ⋆ region c.pScore (8 * c.max_vars) ⋆
        region c.pSimSig (8 * c.max_vars)) ⋆
      (region c.pMinStk (8 * c.minDepth) ⋆ region c.pGlueUsed 256 ⋆
        region c.pLastLearned 64 ⋆ region c.pArena (4 * c.arena_cap) ⋆
        region c.pWstk (4 * c.wcap) ⋆ region c.pDelayed (12 * c.delayed_cap) ⋆
        region c.pRedRefs (4 * c.red_cap) ⋆ region c.pExtendStk (4 * c.extend_cap) ⋆
        region c.pScratchBuf (4 * c.scratch_cap) ⋆ region c.pSlack c.slack)) m := sep_ac hf
  have hmerged := sep_mono2 (fun _ => spl1) (fun _ => spl2) m htop
  have hpM : c.pMinStk = c.pWvec + BitVec.ofNat 64 (80 * c.max_vars) := by
    unfold pMinStk pSimSig pScore pTarjanReach pTarjanMark pWorkStk2 pWorkStk1 pWsort pRepr
    repeat rw [ptr_add_ofNat]
    exact congrArg (fun n => c.pWvec + BitVec.ofNat 64 n) (by omega)
  have hfinal := fStep2 hmerged hpM (by omega)
  rwa [show 80 * c.max_vars + (c.avail - (1152 + 3 * valsBytes c.max_vars +
      5 * markBytes c.max_vars + 15 * u32FullBytes c.max_vars + 80 * c.max_vars)) =
      c.avail - (1152 + 3 * valsBytes c.max_vars + 5 * markBytes c.max_vars +
        15 * u32FullBytes c.max_vars) by omega] at hfinal

private theorem grouped_to_avail (c : FullCfg) {m : Mem 64}
    (hsplit : (((region c.hdr 32 ⋆ region (c.hdr + BitVec.ofNat 64 32) 1120) ⋆
        ((region c.pVals (2 * c.max_vars) ⋆ region c.pWalkVals (2 * c.max_vars) ⋆
          region c.pLitMark (2 * c.max_vars)) ⋆
         (region c.pMark c.max_vars ⋆ region c.pPhases c.max_vars ⋆
          region c.pPhasesTarget c.max_vars ⋆ region c.pPhasesBest c.max_vars ⋆
          region c.pWalkBest c.max_vars)) ⋆ c.padBytes) ⋆
      ((region c.pFlags (4 * c.max_vars) ⋆ region c.pLevel (4 * c.max_vars) ⋆
        region c.pReason (4 * c.max_vars) ⋆ region c.pTrail (4 * c.max_vars) ⋆
        region c.pTrailPos (4 * c.max_vars)) ⋆ c.padU32A) ⋆
      ((region c.pTmp (4 * c.max_vars) ⋆ region c.pHeap (4 * c.max_vars) ⋆
        region c.pPos (4 * c.max_vars) ⋆ region c.pMinClr (4 * c.max_vars) ⋆
        region c.pShrinkStk (4 * c.max_vars)) ⋆ c.padU32B) ⋆
      ((region c.pQPrev (4 * c.max_vars) ⋆ region c.pQNext (4 * c.max_vars) ⋆
        region c.pQStamp (4 * c.max_vars) ⋆ region c.pFrameTrail (4 * (c.max_vars + 1)) ⋆
        region c.pFrameDec (4 * (c.max_vars + 1))) ⋆ c.padU32C) ⋆
      ((region c.pWvec (16 * c.max_vars) ⋆ region c.pRepr (8 * c.max_vars) ⋆
        region c.pWsort (8 * c.max_vars) ⋆ region c.pWorkStk1 (8 * c.max_vars) ⋆
        region c.pWorkStk2 (8 * c.max_vars) ⋆ region c.pTarjanMark (8 * c.max_vars) ⋆
        region c.pTarjanReach (8 * c.max_vars) ⋆ region c.pScore (8 * c.max_vars) ⋆
        region c.pSimSig (8 * c.max_vars)) ⋆
       (region c.pMinStk (8 * c.minDepth) ⋆ region c.pGlueUsed 256 ⋆
        region c.pLastLearned 64 ⋆ region c.pArena (4 * c.arena_cap) ⋆
        region c.pWstk (4 * c.wcap) ⋆ region c.pDelayed (12 * c.delayed_cap) ⋆
        region c.pRedRefs (4 * c.red_cap) ⋆ region c.pExtendStk (4 * c.extend_cap) ⋆
        region c.pScratchBuf (4 * c.scratch_cap)) ⋆
       region c.pSlack c.slack)) m) :
    region c.hdr c.avail m := by
  have hfit := c.havail_fit; have hsz := c.hsize; have hmx := c.hmaxv
  have hu := u32FullBytes_ge c.max_vars; have hu4 := u32FullBytes_ge4 c.max_vars
  have hult := u32FullBytes_le c.max_vars
  have hle : fullFixedBytes c.max_vars ≤ c.avail := by unfold fullFixedBytes at *; omega
  unfold fullFixedBytes at hsz hle; unfold dimacsBound at hmx
  have hc : (region c.hdr (1152 + 3 * valsBytes c.max_vars + 5 * markBytes c.max_vars) ⋆
      region c.pFlags (5 * u32FullBytes c.max_vars) ⋆
      region c.pTmp (5 * u32FullBytes c.max_vars) ⋆
      region c.pQPrev (5 * u32FullBytes c.max_vars) ⋆
      region c.pWvec (c.avail - (1152 + 3 * valsBytes c.max_vars + 5 * markBytes c.max_vars +
        15 * u32FullBytes c.max_vars))) m :=
    sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (fun _ => collapse_bytes c)
      (fun _ g => by
        unfold padU32A at g
        exact collapse_u32_5 rfl rfl rfl rfl (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) g))
      (fun _ g => by
        unfold padU32B at g
        exact collapse_u32_5 rfl rfl rfl rfl (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) g))
      (fun _ g => by
        unfold padU32C at g
        exact collapse_u32_5 rfl rfl rfl rfl (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) g))
      (fun _ => collapse_tail c) m hsplit
  have hc5 := rassoc5 hc
  have hp1 : c.pFlags = c.hdr + BitVec.ofNat 64
      (1152 + 3 * valsBytes c.max_vars + 5 * markBytes c.max_vars) := by
    unfold pFlags pWalkBest pPhasesBest pPhasesTarget pPhases pMark pLitMark pWalkVals pVals
    repeat rw [ptr_add_ofNat]
    exact congrArg (fun n => c.hdr + BitVec.ofNat 64 n) (by omega)
  have hp2 : c.pTmp = c.hdr + BitVec.ofNat 64 (1152 + 3 * valsBytes c.max_vars +
      5 * markBytes c.max_vars + 5 * u32FullBytes c.max_vars) := by
    unfold pTmp pTrailPos pTrail pReason pLevel
    rw [hp1]; repeat rw [ptr_add_ofNat]
    exact congrArg (fun n => c.hdr + BitVec.ofNat 64 n) (by omega)
  have hp3 : c.pQPrev = c.hdr + BitVec.ofNat 64 (1152 + 3 * valsBytes c.max_vars +
      5 * markBytes c.max_vars + 5 * u32FullBytes c.max_vars + 5 * u32FullBytes c.max_vars) := by
    unfold pQPrev pShrinkStk pMinClr pPos pHeap
    rw [hp2]; repeat rw [ptr_add_ofNat]
    exact congrArg (fun n => c.hdr + BitVec.ofNat 64 n) (by omega)
  have hp4 : c.pWvec = c.hdr + BitVec.ofNat 64 (1152 + 3 * valsBytes c.max_vars +
      5 * markBytes c.max_vars + 5 * u32FullBytes c.max_vars + 5 * u32FullBytes c.max_vars +
      5 * u32FullBytes c.max_vars) := by
    unfold pWvec pFrameDec pFrameTrail pQStamp pQNext
    rw [hp3]; repeat rw [ptr_add_ofNat]
    exact congrArg (fun n => c.hdr + BitVec.ofNat 64 n) (by omega)
  have hm := fStep2 (fStep (fStep (fStep hc5 hp1 (by omega)) hp2 (by omega)) hp3 (by omega))
    hp4 (by omega)
  rwa [show 1152 + 3 * valsBytes c.max_vars + 5 * markBytes c.max_vars +
      5 * u32FullBytes c.max_vars + 5 * u32FullBytes c.max_vars +
      5 * u32FullBytes c.max_vars + (c.avail - (1152 + 3 * valsBytes c.max_vars +
        5 * markBytes c.max_vars + 15 * u32FullBytes c.max_vars)) = c.avail by omega] at hm

/-- Collapse all `41` active array regions, header prefix/tail, and padding back into
`region c.hdr c.avail`. -/
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
  unfold pad at hm
  have p : ∀ {H B U1 U2 U3 T1 T2 PB PA PC PD PS : Mem 64 → Prop} {k : Mem 64},
      (H ⋆ B ⋆ U1 ⋆ U2 ⋆ U3 ⋆ T1 ⋆ T2 ⋆ (PB ⋆ PA ⋆ PC ⋆ PD ⋆ PS)) k →
      ((H ⋆ B ⋆ PB) ⋆ (U1 ⋆ PA) ⋆ (U2 ⋆ PC) ⋆ (U3 ⋆ PD) ⋆ (T1 ⋆ T2 ⋆ PS)) k := fun x => sep_ac x
  exact c.grouped_to_avail (p hm)

end FullCfg

/-! ## 3. `FullScratch`, `FullCoreState`, `FullState`, `LengthsOk`, and `hdrTailWords` -/

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

@[expose] def hdrTailWords0 (c : FullCfg) (s : FullState) : List (BitVec 64) :=
  let k := s.core; let sc := s.scratch
  [ BitVec.ofNat 64 c.arena_cap, BitVec.ofNat 64 c.wcap, BitVec.ofNat 64 k.arena_len,
    BitVec.ofNat 64 k.wlen, c.pVals, c.pMark, c.pLevel, c.pReason, c.pTrail, c.pWvec,
    c.pArena, c.pWstk, c.pDelayed, c.pTmp, BitVec.ofNat 64 k.trail_end,
    BitVec.ofNat 64 k.propagated, BitVec.ofNat 64 k.cur_level, k.fuel, k.confl_ref,
    BitVec.ofNat 64 k.tmp_cnt, BitVec.ofNat 64 k.tmp_len, c.pHeap, c.pPos, c.pScore,
    c.pPhases, c.pMinStk, c.pMinClr, BitVec.ofNat 64 sc.heap_len, sc.scinc,
    BitVec.ofNat 64 c.minDepth, BitVec.ofNat 64 k.min_clr_len, k.min_clr_full,
    sc.rel_period, sc.rel_limit, sc.rel_wait ]

@[expose] def hdrTailWords1 (c : FullCfg) (s : FullState) : List (BitVec 64) :=
  let k := s.core; let sc := s.scratch
  [ sc.rel_u, sc.rel_v, sc.rel_trigger, sc.conflicts, sc.learned_lits, sc.min_removed,
    c.pTrailPos, c.pQPrev, c.pQNext, c.pQStamp, c.pPhasesTarget, c.pPhasesBest, c.pWsort,
    c.pShrinkStk, c.pRedRefs, c.pGlueUsed, BitVec.ofNat 64 c.red_cap,
    BitVec.ofNat 64 c.delayed_cap, BitVec.ofNat 64 sc.delayed_len, k.wusable,
    k.arena_garbage, k.first_reducible, k.num_irred, k.num_redundant, k.num_binary,
    k.unflushed, k.probing, k.confl_type, k.confl_lit0, k.confl_lit1, sc.stable,
    sc.switched, sc.mode_count, sc.mode_confl_lim, sc.mode_tick_lim ]

@[expose] def hdrTailWords2 (c : FullCfg) (s : FullState) : List (BitVec 64) :=
  let k := s.core; let sc := s.scratch
  [ sc.mode_saved_ticks, sc.search_ticks, sc.q_first, sc.q_last, sc.q_search_idx,
    sc.q_search_stamp, sc.q_cur_stamp, sc.target_assigned, sc.best_assigned,
    sc.rephase_limit, sc.rephased, sc.reduce_limit, sc.reductions, sc.tier1, sc.tier2,
    sc.restarts, sc.restart_limit, sc.ema_fast_biased, sc.ema_fast_exp,
    sc.ema_slow_biased, sc.ema_slow_exp, k.oom, BitVec.ofNat 64 c.max_vars,
    BitVec.ofNat 64 k.cur_vars, BitVec.ofNat 64 c.bva_cap, k.unassigned, c.pFlags,
    c.pLitMark, c.pRepr, c.pSimSig, c.pFrameTrail, c.pFrameDec, c.pWorkStk1, c.pWorkStk2,
    c.pTarjanMark ]

@[expose] def hdrTailWords3 (c : FullCfg) (s : FullState) : List (BitVec 64) :=
  let k := s.core; let sc := s.scratch
  [ c.pTarjanReach, c.pWalkVals, c.pWalkBest, c.pExtendStk, BitVec.ofNat 64 c.extend_cap,
    BitVec.ofNat 64 sc.extend_len, c.pScratchBuf, BitVec.ofNat 64 c.scratch_cap,
    c.pLastLearned, sc.rng_state, sc.chrono_levels, sc.otfs_cnt, sc.eager_sub_cnt,
    sc.probe_limit, sc.probings, sc.elim_limit, sc.eliminations, sc.elim_bound,
    k.dense_mode, k.inconsistent, sc.iterating, sc.hbr_cnt, sc.trans_cnt, sc.viv_cnt,
    sc.subst_cnt, sc.cong_cnt, sc.sweep_cnt, sc.bve_cnt, sc.bce_cnt, sc.bva_cnt,
    sc.walk_cnt_stat, sc.fwd_sub_cnt, sc.fwd_str_cnt, sc.ant_sz, sc.res_sz ]

/-- The `140` trailing `u64` words of `FullHdr` starting at offset `c.hdr + 32`
(byte offsets `32..1144`). -/
@[expose] def hdrTailWords (c : FullCfg) (s : FullState) : List (BitVec 64) :=
  hdrTailWords0 c s ++ hdrTailWords1 c s ++ hdrTailWords2 c s ++ hdrTailWords3 c s

@[simp] theorem hdrTailWords_length (c : FullCfg) (s : FullState) :
    (hdrTailWords c s).length = 140 := by
  simp only [hdrTailWords, hdrTailWords0, hdrTailWords1, hdrTailWords2, hdrTailWords3,
    List.length_append, List.length_cons, List.length_nil]

/-! ## 4. Partitioned array footprints, collapse, and framing bridges -/

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

theorem fullMem_anyDimacs_to_region {c : FullCfg} {s : FullState}
    {mv' nc' cur' val' : BitVec 64} {m : Mem 64} (hlen : s.LengthsOk c)
    (hm : (dimacsState c.hdr mv' nc' cur' val' ⋆
      array64 (c.hdr + 32) (hdrTailWords c s) ⋆
      FullCoreArrays c s.core ⋆ FullScratchArrays c s.scratch ⋆ c.pad) m) :
    region c.hdr c.avail m := by
  have hm1 : ((dimacsState c.hdr mv' nc' cur' val' ⋆ array64 (c.hdr + 32) (hdrTailWords c s)) ⋆
      ((FullCoreByteArrs c s.core ⋆ FullCoreU32A c s.core ⋆ FullCoreU32B c s.core ⋆
        FullCoreDynArrs c s.core) ⋆
       ((FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆ FullScrWksArrs c s.scratch ⋆
         FullScrMetaArrs c s.scratch ⋆ FullScrDynArrs c s.scratch) ⋆ c.pad))) m := by
    unfold FullCoreArrays FullScratchArrays at hm; exact sep_ac hm
  refine fullRegs_grouped_to_avail c ?_
  exact sep_mono2
    (sep_mono2 (fun _ h => dimacsState_to_region h)
      (fun _ h => fArr64 (hdrTailWords_length c s) (m := 1120) (by decide) (by decide) h))
    (sep_mono2
      (sep_mono2 (sep_mono2 (sep_mono2
        (fun _ => fullCoreByte_to_regs hlen.core_ok)
        (fun _ => fullCoreU32A_to_regs hlen.core_ok))
        (fun _ => fullCoreU32B_to_regs hlen.core_ok))
        (fun _ => fullCoreDyn_to_regs hlen.core_ok))
      (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2
        (fun _ => fullScrByte_to_regs hlen.scratch_ok)
        (fun _ => fullScrU32A_to_regs hlen.scratch_ok))
        (fun _ => fullScrWks_to_regs hlen.scratch_ok))
        (fun _ => fullScrMeta_to_regs hlen.scratch_ok))
        (fun _ => fullScrDyn_to_regs hlen.scratch_ok))
        (fun _ h => h)))
    m hm1

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

/-- Non-`vals` remainder of `FullMem` for `kissat_check_model` framing. -/
@[expose] def FullCheckRest (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  array64 (c.hdr + 32) (hdrTailWords c s) ⋆
  array (t := i8) c.pLitMark s.core.lit_mark ⋆ array (t := i8) c.pMark s.core.mrk ⋆
  FullCoreU32A c s.core ⋆ FullCoreU32B c s.core ⋆ FullCoreDynArrs c s.core ⋆
  FullScratchArrays c s.scratch ⋆ c.pad

theorem fullCheckRest_d_irrel (c : FullCfg) (s : FullState) (cur' val' : BitVec 64) :
    FullCheckRest c { s with core := { s.core with d_cur := cur', d_val := val' } } =
      FullCheckRest c s := rfl

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
  have hmx := c.hmaxv; unfold dimacsBound FullCheckRest FullScratchArrays at *
  have hm1 : ((bytes cnf_ptr cnfBytes ⋆ R) ⋆
      ((dimacsState c.hdr mv' nc' cur' val' ⋆ array64 (c.hdr + 32) (hdrTailWords c s)) ⋆
      (((bytes c.pVals (s.core.vals.map UInt8.ofBitVec) ⋆
          array (t := i8) c.pLitMark s.core.lit_mark ⋆
          array (t := i8) c.pMark s.core.mrk) ⋆
        FullCoreU32A c s.core ⋆ FullCoreU32B c s.core ⋆ FullCoreDynArrs c s.core) ⋆
       ((FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆ FullScrWksArrs c s.scratch ⋆
         FullScrMetaArrs c s.scratch ⋆ FullScrDynArrs c s.scratch) ⋆ c.pad)))) m := sep_ac hm
  have hm2 : ((bytes cnf_ptr cnfBytes ⋆ R) ⋆ region c.hdr c.avail) m := by
    refine sep_mono_r (fun _ h => fullRegs_grouped_to_avail c ?_) hm1
    exact sep_mono2
      (sep_mono2 (fun _ hb => dimacsState_to_region hb)
        (fun _ hb => fArr64 (hdrTailWords_length c s) (m := 1120) (by decide) (by decide) hb))
      (sep_mono2
        (sep_mono2 (sep_mono2 (sep_mono2
          (sep_mono2 (sep_mono2
            (fun _ (hb : bytes c.pVals (s.core.vals.map UInt8.ofBitVec) _) => by
              have hb' := bytes_to_region hb; simpa [hlen.core_ok.vals_len] using hb')
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
      _ h
  exact sep_ac hm2

/-! ## 5. `SafetySlice` instantiations and header / group-focus primitives -/

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

theorem fullMem_eq_coreByte (c : FullCfg) (s : FullState) :
    FullMem c s = (FullCoreByteArrs c s.core ⋆ (FullCoreU32A c s.core ⋆
      FullCoreU32B c s.core ⋆ FullCoreDynArrs c s.core ⋆ fullCoreOuter c s)) := by
  unfold FullMem FullCoreArrays fullCoreOuter; ac_rfl
theorem fullMem_eq_coreU32A (c : FullCfg) (s : FullState) :
    FullMem c s = (FullCoreU32A c s.core ⋆ (FullCoreByteArrs c s.core ⋆
      FullCoreU32B c s.core ⋆ FullCoreDynArrs c s.core ⋆ fullCoreOuter c s)) := by
  unfold FullMem FullCoreArrays fullCoreOuter; ac_rfl
theorem fullMem_eq_coreU32B (c : FullCfg) (s : FullState) :
    FullMem c s = (FullCoreU32B c s.core ⋆ (FullCoreByteArrs c s.core ⋆
      FullCoreU32A c s.core ⋆ FullCoreDynArrs c s.core ⋆ fullCoreOuter c s)) := by
  unfold FullMem FullCoreArrays fullCoreOuter; ac_rfl
theorem fullMem_eq_coreDyn (c : FullCfg) (s : FullState) :
    FullMem c s = (FullCoreDynArrs c s.core ⋆ (FullCoreByteArrs c s.core ⋆
      FullCoreU32A c s.core ⋆ FullCoreU32B c s.core ⋆ fullCoreOuter c s)) := by
  unfold FullMem FullCoreArrays fullCoreOuter; ac_rfl
theorem fullMem_eq_scrByte (c : FullCfg) (s : FullState) :
    FullMem c s = (FullScrByteArrs c s.scratch ⋆ (FullScrU32A c s.scratch ⋆
      FullScrWksArrs c s.scratch ⋆ FullScrMetaArrs c s.scratch ⋆
      FullScrDynArrs c s.scratch ⋆ fullScrOuter c s)) := by
  unfold FullMem FullScratchArrays fullScrOuter; ac_rfl
theorem fullMem_eq_scrU32A (c : FullCfg) (s : FullState) :
    FullMem c s = (FullScrU32A c s.scratch ⋆ (FullScrByteArrs c s.scratch ⋆
      FullScrWksArrs c s.scratch ⋆ FullScrMetaArrs c s.scratch ⋆
      FullScrDynArrs c s.scratch ⋆ fullScrOuter c s)) := by
  unfold FullMem FullScratchArrays fullScrOuter; ac_rfl
theorem fullMem_eq_scrWks (c : FullCfg) (s : FullState) :
    FullMem c s = (FullScrWksArrs c s.scratch ⋆ (FullScrByteArrs c s.scratch ⋆
      FullScrU32A c s.scratch ⋆ FullScrMetaArrs c s.scratch ⋆
      FullScrDynArrs c s.scratch ⋆ fullScrOuter c s)) := by
  unfold FullMem FullScratchArrays fullScrOuter; ac_rfl
theorem fullMem_eq_scrMeta (c : FullCfg) (s : FullState) :
    FullMem c s = (FullScrMetaArrs c s.scratch ⋆ (FullScrByteArrs c s.scratch ⋆
      FullScrU32A c s.scratch ⋆ FullScrWksArrs c s.scratch ⋆
      FullScrDynArrs c s.scratch ⋆ fullScrOuter c s)) := by
  unfold FullMem FullScratchArrays fullScrOuter; ac_rfl
theorem fullMem_eq_scrDyn (c : FullCfg) (s : FullState) :
    FullMem c s = (FullScrDynArrs c s.scratch ⋆ (FullScrByteArrs c s.scratch ⋆
      FullScrU32A c s.scratch ⋆ FullScrWksArrs c s.scratch ⋆
      FullScrMetaArrs c s.scratch ⋆ fullScrOuter c s)) := by
  unfold FullMem FullScratchArrays fullScrOuter; ac_rfl

end LeanQbe.T.Examples.Kissat.Proof.Spec
