module

public import LeanQbe.T.Examples.Kissat.Plain
public import LeanQbe.T.Examples.Kissat.SolverArena
public import LeanQbe.T.Logic.C0StepAttr
public import Kraken.SeparationTactics
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Plain` Arena Layout, State, and Memory Bridges — Part 1 (`Stage 3`)

Defines:
1. `plainMinDepthOf`, `plainFixedBytes`, and `PlainCfg` (`COMPACT` 32-bit word `arena`,
   contiguous `watch_vec` / `watch_stk`, `trail_pos`, `shrink_stk`, `red_refs`,
   `glue_used`, `delayed`, and dual-mode VSIDS/VMTF arrays), plus `regions_to_avail`.
2. `PlainHeur` (non-soundness heuristic fields & arrays), `PlainState`, `LengthsOk`, and
   the 92-word `hdrTailWords` projection matching `PlainHdr` byte offsets `32..760`.
3. `PlainMem`, `PlainArenaInv`, `PlainRest`, `plainMem_anyDimacs_to_region`, and
   `check_model` framing bridges (`plainMem_to_checkModel`, `checkModel_post_to_region`).
4. `@[c0_load]` / `@[c0_store]` helpers for `KissatDimacs` and header words `0..40`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Plain

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

/-! ## 1. Arithmetic, alignment, and `PlainHdr` layout sizes -/

def plainMinDepthOf (mv : Nat) : Nat :=
  if mv + 1 < 1000 then mv + 1 else 1000

/-- Fixed byte footprint required by `plain_init_state` (`sizeof(PlainHdr) = 768`,
`glue_used = 256`, plus variable tables). -/
def plainFixedBytes (mv : Nat) : Nat :=
  1024 + valsBytes mv + 4 * markBytes mv + 12 * u32VarBytes mv + 32 * mv +
    8 * plainMinDepthOf mv

theorem plainMinDepthOf_pos (mv : Nat) : 1 ≤ plainMinDepthOf mv := by
  unfold plainMinDepthOf; split <;> omega

theorem plainMinDepthOf_le (mv : Nat) : plainMinDepthOf mv ≤ 1000 := by
  unfold plainMinDepthOf; split <;> omega

theorem plainFixedBytes_lt {mv : Nat} (hmv : mv < dimacsBound) :
    plainFixedBytes mv < 2 ^ 35 := by
  unfold plainFixedBytes valsBytes markBytes u32VarBytes plainMinDepthOf dimacsBound at *
  split <;> omega

def plainAlignPad (p : BitVec 64) : Nat :=
  if p.toNat % 8 = 0 then 0 else 8 - p.toNat % 8

theorem plainAlignPad_lt8 (p : BitVec 64) : plainAlignPad p < 8 := by
  unfold plainAlignPad; split <;> omega

theorem plain_bv64_sub_pad {w : Nat} {p : BitVec 64}
    (hle : plainAlignPad p ≤ w) (hw : w < 2 ^ 64) :
    BitVec.ofNat 64 w - BitVec.ofNat 64 (plainAlignPad p) =
      BitVec.ofNat 64 (w - plainAlignPad p) :=
  bv_sub_ofNat hle hw

/-! ## 2. `PlainCfg` arena geometry -/

/-- Static arena geometry established by `plain_init_state` in `Plain1`. -/
structure PlainCfg where
  hdr : BitVec 64
  avail : Nat
  mv : Nat
  nc : Nat
  arena_cap : Nat
  wcap : Nat
  delayed_cap : Nat
  red_cap : Nat
  hmv : mv < dimacsBound
  hnc : nc < dimacsBound
  harena : arena_cap < 2 * dimacsBound
  hwcap : wcap < 2 * dimacsBound
  hdel : delayed_cap < dimacsBound
  hred : red_cap < 2 * dimacsBound
  havail_fit : hdr.toNat + avail < 2 ^ 64
  hsize : plainFixedBytes mv + 4 * arena_cap + 4 * wcap + 12 * delayed_cap +
    4 * red_cap ≤ avail

namespace PlainCfg

def minDepth (c : PlainCfg) : Nat := plainMinDepthOf c.mv

def pVals (c : PlainCfg) : BitVec 64 := c.hdr + BitVec.ofNat 64 768
def pMark (c : PlainCfg) : BitVec 64 := c.pVals + BitVec.ofNat 64 (valsBytes c.mv)
def pPhases (c : PlainCfg) : BitVec 64 := c.pMark + BitVec.ofNat 64 (markBytes c.mv)
def pPhasesTarget (c : PlainCfg) : BitVec 64 :=
  c.pPhases + BitVec.ofNat 64 (markBytes c.mv)
def pPhasesBest (c : PlainCfg) : BitVec 64 :=
  c.pPhasesTarget + BitVec.ofNat 64 (markBytes c.mv)
def pLevel (c : PlainCfg) : BitVec 64 :=
  c.pPhasesBest + BitVec.ofNat 64 (markBytes c.mv)
def pReason (c : PlainCfg) : BitVec 64 := c.pLevel + BitVec.ofNat 64 (u32VarBytes c.mv)
def pTrail (c : PlainCfg) : BitVec 64 := c.pReason + BitVec.ofNat 64 (u32VarBytes c.mv)
def pTrailPos (c : PlainCfg) : BitVec 64 := c.pTrail + BitVec.ofNat 64 (u32VarBytes c.mv)
def pTmp (c : PlainCfg) : BitVec 64 := c.pTrailPos + BitVec.ofNat 64 (u32VarBytes c.mv)
def pHeap (c : PlainCfg) : BitVec 64 := c.pTmp + BitVec.ofNat 64 (u32VarBytes c.mv)
def pPos (c : PlainCfg) : BitVec 64 := c.pHeap + BitVec.ofNat 64 (u32VarBytes c.mv)
def pMinClr (c : PlainCfg) : BitVec 64 := c.pPos + BitVec.ofNat 64 (u32VarBytes c.mv)
def pShrinkStk (c : PlainCfg) : BitVec 64 :=
  c.pMinClr + BitVec.ofNat 64 (u32VarBytes c.mv)
def pQPrev (c : PlainCfg) : BitVec 64 :=
  c.pShrinkStk + BitVec.ofNat 64 (u32VarBytes c.mv)
def pQNext (c : PlainCfg) : BitVec 64 := c.pQPrev + BitVec.ofNat 64 (u32VarBytes c.mv)
def pQStamp (c : PlainCfg) : BitVec 64 := c.pQNext + BitVec.ofNat 64 (u32VarBytes c.mv)
def pWvec (c : PlainCfg) : BitVec 64 := c.pQStamp + BitVec.ofNat 64 (u32VarBytes c.mv)
def pWsort (c : PlainCfg) : BitVec 64 := c.pWvec + BitVec.ofNat 64 (16 * c.mv)
def pScore (c : PlainCfg) : BitVec 64 := c.pWsort + BitVec.ofNat 64 (8 * c.mv)
def pMinStk (c : PlainCfg) : BitVec 64 := c.pScore + BitVec.ofNat 64 (8 * c.mv)
def pGlueUsed (c : PlainCfg) : BitVec 64 := c.pMinStk + BitVec.ofNat 64 (8 * c.minDepth)
def pArena (c : PlainCfg) : BitVec 64 := c.pGlueUsed + BitVec.ofNat 64 256
def pWstk (c : PlainCfg) : BitVec 64 := c.pArena + BitVec.ofNat 64 (4 * c.arena_cap)
def pDelayed (c : PlainCfg) : BitVec 64 := c.pWstk + BitVec.ofNat 64 (4 * c.wcap)
def pRedRefs (c : PlainCfg) : BitVec 64 := c.pDelayed + BitVec.ofNat 64 (12 * c.delayed_cap)
def pSlack (c : PlainCfg) : BitVec 64 := c.pRedRefs + BitVec.ofNat 64 (4 * c.red_cap)
def slack (c : PlainCfg) : Nat :=
  c.avail - (plainFixedBytes c.mv + 4 * c.arena_cap + 4 * c.wcap +
    12 * c.delayed_cap + 4 * c.red_cap)

def padMarks (c : PlainCfg) : Mem 64 → Prop :=
  region (c.pVals + BitVec.ofNat 64 (2 * c.mv)) (valsBytes c.mv - 2 * c.mv) ⋆
  region (c.pMark + BitVec.ofNat 64 c.mv) (markBytes c.mv - c.mv) ⋆
  region (c.pPhases + BitVec.ofNat 64 c.mv) (markBytes c.mv - c.mv) ⋆
  region (c.pPhasesTarget + BitVec.ofNat 64 c.mv) (markBytes c.mv - c.mv) ⋆
  region (c.pPhasesBest + BitVec.ofNat 64 c.mv) (markBytes c.mv - c.mv)

def padU32A (c : PlainCfg) : Mem 64 → Prop :=
  region (c.pLevel + BitVec.ofNat 64 (4 * c.mv)) (u32VarBytes c.mv - 4 * c.mv) ⋆
  region (c.pReason + BitVec.ofNat 64 (4 * c.mv)) (u32VarBytes c.mv - 4 * c.mv) ⋆
  region (c.pTrail + BitVec.ofNat 64 (4 * c.mv)) (u32VarBytes c.mv - 4 * c.mv) ⋆
  region (c.pTrailPos + BitVec.ofNat 64 (4 * c.mv)) (u32VarBytes c.mv - 4 * c.mv) ⋆
  region (c.pTmp + BitVec.ofNat 64 (4 * c.mv)) (u32VarBytes c.mv - 4 * c.mv) ⋆
  region (c.pHeap + BitVec.ofNat 64 (4 * c.mv)) (u32VarBytes c.mv - 4 * c.mv)

def padU32B (c : PlainCfg) : Mem 64 → Prop :=
  region (c.pPos + BitVec.ofNat 64 (4 * c.mv)) (u32VarBytes c.mv - 4 * c.mv) ⋆
  region (c.pMinClr + BitVec.ofNat 64 (4 * c.mv)) (u32VarBytes c.mv - 4 * c.mv) ⋆
  region (c.pShrinkStk + BitVec.ofNat 64 (4 * c.mv)) (u32VarBytes c.mv - 4 * c.mv) ⋆
  region (c.pQPrev + BitVec.ofNat 64 (4 * c.mv)) (u32VarBytes c.mv - 4 * c.mv) ⋆
  region (c.pQNext + BitVec.ofNat 64 (4 * c.mv)) (u32VarBytes c.mv - 4 * c.mv) ⋆
  region (c.pQStamp + BitVec.ofNat 64 (4 * c.mv)) (u32VarBytes c.mv - 4 * c.mv)

/-- Combined alignment padding and trailing slack regions (untouched after `plain_init_state`). -/
def pad (c : PlainCfg) : Mem 64 → Prop :=
  c.padMarks ⋆ c.padU32A ⋆ c.padU32B ⋆ region c.pSlack c.slack

private theorem pair_merge {a : BitVec 64} {n1 n2 n : Nat}
    (hn : n1 + n2 = n) (hfit : n ≤ 2 ^ 64) {f : Mem 64}
    (hf : (region a n1 ⋆ region (a + BitVec.ofNat 64 n1) n2) f) : region a n f :=
  (congrFun (region_merge_eq hn hfit) f).mp hf

private theorem step_merge {P : Mem 64 → Prop} {m0 : Mem 64} {n1 n2 : Nat} {a1 a2 : BitVec 64}
    (h : (region a1 n1 ⋆ (region a2 n2 ⋆ P)) m0)
    (hadd : a2 = a1 + BitVec.ofNat 64 n1) (hfit : n1 + n2 ≤ 2 ^ 64) :
    (region a1 (n1 + n2) ⋆ P) m0 := by
  rw [← sep_assoc, hadd] at h
  rwa [region_merge_eq rfl hfit] at h

private theorem step_merge2 {m0 : Mem 64} {n1 n2 : Nat} {a1 a2 : BitVec 64}
    (h : (region a1 n1 ⋆ region a2 n2) m0)
    (hadd : a2 = a1 + BitVec.ofNat 64 n1) (hfit : n1 + n2 ≤ 2 ^ 64) :
    region a1 (n1 + n2) m0 := by
  rw [hadd] at h
  rwa [region_merge_eq rfl hfit] at h

private theorem rassoc6 {A B C D E F : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ B ⋆ C ⋆ D ⋆ E ⋆ F) m) : (A ⋆ (B ⋆ (C ⋆ (D ⋆ (E ⋆ F))))) m := sep_ac h

private theorem rassoc10 {A B C D E F G H I J : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ B ⋆ C ⋆ D ⋆ E ⋆ F ⋆ G ⋆ H ⋆ I ⋆ J) m) :
    (A ⋆ (B ⋆ (C ⋆ (D ⋆ (E ⋆ (F ⋆ (G ⋆ (H ⋆ (I ⋆ J))))))))) m := sep_ac h

private theorem sep_zip5 {A B C D E A' B' C' D' E' : Mem 64 → Prop} {m : Mem 64}
    (h : ((A ⋆ B ⋆ C ⋆ D ⋆ E) ⋆ (A' ⋆ B' ⋆ C' ⋆ D' ⋆ E')) m) :
    ((A ⋆ A') ⋆ (B ⋆ B') ⋆ (C ⋆ C') ⋆ (D ⋆ D') ⋆ (E ⋆ E')) m := sep_ac h

private theorem sep_zip6 {A B C D E F A' B' C' D' E' F' : Mem 64 → Prop} {m : Mem 64}
    (h : ((A ⋆ B ⋆ C ⋆ D ⋆ E ⋆ F) ⋆ (A' ⋆ B' ⋆ C' ⋆ D' ⋆ E' ⋆ F')) m) :
    ((A ⋆ A') ⋆ (B ⋆ B') ⋆ (C ⋆ C') ⋆ (D ⋆ D') ⋆ (E ⋆ E') ⋆ (F ⋆ F')) m := sep_ac h

private theorem sep_group_all {H M A B T PM PA PB PS : Mem 64 → Prop} {m : Mem 64}
    (h : ((H ⋆ M ⋆ A ⋆ B ⋆ T) ⋆ (PM ⋆ PA ⋆ PB ⋆ PS)) m) :
    (((H ⋆ M ⋆ PM) ⋆ (A ⋆ PA)) ⋆ ((B ⋆ PB) ⋆ (T ⋆ PS))) m := sep_ac h

private theorem collapse_marks (c : PlainCfg) {f : Mem 64}
    (hf : ((region c.hdr 32 ⋆ region (c.hdr + BitVec.ofNat 64 32) 736) ⋆
      (region c.pVals (2 * c.mv) ⋆ region c.pMark c.mv ⋆ region c.pPhases c.mv ⋆
      region c.pPhasesTarget c.mv ⋆ region c.pPhasesBest c.mv) ⋆ c.padMarks) f) :
    region c.hdr (768 + valsBytes c.mv + 4 * markBytes c.mv) f := by
  have hmv := c.hmv; unfold dimacsBound at hmv
  have hv := valsBytes_ge c.mv; have hmk := markBytes_ge c.mv
  have hvlt : valsBytes c.mv ≤ 2 * c.mv + 7 := by unfold valsBytes; omega
  have hmlt : markBytes c.mv ≤ c.mv + 7 := by unfold markBytes; omega
  have hhdr : (region c.hdr 32 ⋆ region (c.hdr + BitVec.ofNat 64 32) 736) =
      region c.hdr 768 := region_merge_eq (by decide) (by decide)
  rw [hhdr] at hf
  have hf0 : (region c.hdr 768 ⋆
      ((region c.pVals (2 * c.mv) ⋆ region c.pMark c.mv ⋆ region c.pPhases c.mv ⋆
        region c.pPhasesTarget c.mv ⋆ region c.pPhasesBest c.mv) ⋆ c.padMarks)) f := by
    rwa [sep_assoc] at hf
  have hz : (region c.hdr 768 ⋆
      (region c.pVals (valsBytes c.mv) ⋆ region c.pMark (markBytes c.mv) ⋆
       region c.pPhases (markBytes c.mv) ⋆ region c.pPhasesTarget (markBytes c.mv) ⋆
       region c.pPhasesBest (markBytes c.mv))) f := by
    refine sep_mono_r (fun _ g => ?_) hf0
    unfold padMarks at g
    exact sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2
      (fun _ => pair_merge (n := valsBytes c.mv) (by omega) (by omega))
      (fun _ => pair_merge (n := markBytes c.mv) (by omega) (by omega)))
      (fun _ => pair_merge (n := markBytes c.mv) (by omega) (by omega)))
      (fun _ => pair_merge (n := markBytes c.mv) (by omega) (by omega)))
      (fun _ => pair_merge (n := markBytes c.mv) (by omega) (by omega)) _ (sep_zip5 g)
  have h2 := rassoc6 (sep_ac hz : (region c.hdr 768 ⋆ region c.pVals (valsBytes c.mv) ⋆
      region c.pMark (markBytes c.mv) ⋆ region c.pPhases (markBytes c.mv) ⋆
      region c.pPhasesTarget (markBytes c.mv) ⋆ region c.pPhasesBest (markBytes c.mv)) f)
  have hbase : c.pVals = c.hdr + BitVec.ofNat 64 768 := rfl
  have ha1 : c.pMark = c.pVals + BitVec.ofNat 64 (valsBytes c.mv) := rfl
  have ha2 : c.pPhases = c.pMark + BitVec.ofNat 64 (markBytes c.mv) := rfl
  have ha3 : c.pPhasesTarget = c.pPhases + BitVec.ofNat 64 (markBytes c.mv) := rfl
  have ha4 : c.pPhasesBest = c.pPhasesTarget + BitVec.ofNat 64 (markBytes c.mv) := rfl
  have s1 := step_merge h2 hbase (by omega)
  have ha1' : c.pMark = c.hdr + BitVec.ofNat 64 (768 + valsBytes c.mv) := by
    rw [ha1, hbase, ptr_add_ofNat]
  have s2 := step_merge s1 ha1' (by omega)
  have ha2' : c.pPhases = c.hdr + BitVec.ofNat 64 (768 + valsBytes c.mv + markBytes c.mv) := by
    rw [ha2, ha1', ptr_add_ofNat]
  have s3 := step_merge s2 ha2' (by omega)
  have ha3' : c.pPhasesTarget = c.hdr +
      BitVec.ofNat 64 (768 + valsBytes c.mv + markBytes c.mv + markBytes c.mv) := by
    rw [ha3, ha2', ptr_add_ofNat]
  have s4 := step_merge s3 ha3' (by omega)
  have ha4' : c.pPhasesBest = c.hdr +
      BitVec.ofNat 64 (768 + valsBytes c.mv + markBytes c.mv + markBytes c.mv +
        markBytes c.mv) := by
    rw [ha4, ha3', ptr_add_ofNat]
  have s5 := step_merge2 s4 ha4' (by omega)
  have hlen : 768 + valsBytes c.mv + markBytes c.mv + markBytes c.mv + markBytes c.mv +
      markBytes c.mv = 768 + valsBytes c.mv + 4 * markBytes c.mv := by omega
  rwa [hlen] at s5

private theorem collapse_u32a (c : PlainCfg) {f : Mem 64}
    (hf : ((region c.pLevel (4 * c.mv) ⋆ region c.pReason (4 * c.mv) ⋆
      region c.pTrail (4 * c.mv) ⋆ region c.pTrailPos (4 * c.mv) ⋆
      region c.pTmp (4 * c.mv) ⋆ region c.pHeap (4 * c.mv)) ⋆ c.padU32A) f) :
    region c.pLevel (6 * u32VarBytes c.mv) f := by
  have hmv := c.hmv; unfold dimacsBound at hmv
  have hu := u32VarBytes_ge c.mv
  have hult : u32VarBytes c.mv ≤ 4 * c.mv + 7 := by unfold u32VarBytes; omega
  unfold padU32A at hf
  have h2 := rassoc6 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2
    (fun _ => pair_merge (n := u32VarBytes c.mv) (by omega) (by omega))
    (fun _ => pair_merge (n := u32VarBytes c.mv) (by omega) (by omega)))
    (fun _ => pair_merge (n := u32VarBytes c.mv) (by omega) (by omega)))
    (fun _ => pair_merge (n := u32VarBytes c.mv) (by omega) (by omega)))
    (fun _ => pair_merge (n := u32VarBytes c.mv) (by omega) (by omega)))
    (fun _ => pair_merge (n := u32VarBytes c.mv) (by omega) (by omega)) f (sep_zip6 hf))
  have ha1 : c.pReason = c.pLevel + BitVec.ofNat 64 (u32VarBytes c.mv) := rfl
  have ha2 : c.pTrail = c.pReason + BitVec.ofNat 64 (u32VarBytes c.mv) := rfl
  have ha3 : c.pTrailPos = c.pTrail + BitVec.ofNat 64 (u32VarBytes c.mv) := rfl
  have ha4 : c.pTmp = c.pTrailPos + BitVec.ofNat 64 (u32VarBytes c.mv) := rfl
  have ha5 : c.pHeap = c.pTmp + BitVec.ofNat 64 (u32VarBytes c.mv) := rfl
  have s1 := step_merge h2 ha1 (by omega)
  have ha2' : c.pTrail = c.pLevel + BitVec.ofNat 64 (u32VarBytes c.mv + u32VarBytes c.mv) := by
    rw [ha2, ha1, ptr_add_ofNat]
  have s2 := step_merge s1 ha2' (by omega)
  have ha3' : c.pTrailPos = c.pLevel +
      BitVec.ofNat 64 (u32VarBytes c.mv + u32VarBytes c.mv + u32VarBytes c.mv) := by
    rw [ha3, ha2', ptr_add_ofNat]
  have s3 := step_merge s2 ha3' (by omega)
  have ha4' : c.pTmp = c.pLevel + BitVec.ofNat 64
      (u32VarBytes c.mv + u32VarBytes c.mv + u32VarBytes c.mv + u32VarBytes c.mv) := by
    rw [ha4, ha3', ptr_add_ofNat]
  have s4 := step_merge s3 ha4' (by omega)
  have ha5' : c.pHeap = c.pLevel + BitVec.ofNat 64 (u32VarBytes c.mv + u32VarBytes c.mv +
      u32VarBytes c.mv + u32VarBytes c.mv + u32VarBytes c.mv) := by
    rw [ha5, ha4', ptr_add_ofNat]
  have s5 := step_merge2 s4 ha5' (by omega)
  have hlen : u32VarBytes c.mv + u32VarBytes c.mv + u32VarBytes c.mv +
      u32VarBytes c.mv + u32VarBytes c.mv + u32VarBytes c.mv = 6 * u32VarBytes c.mv := by omega
  rwa [hlen] at s5

private theorem collapse_u32b (c : PlainCfg) {f : Mem 64}
    (hf : ((region c.pPos (4 * c.mv) ⋆ region c.pMinClr (4 * c.mv) ⋆
      region c.pShrinkStk (4 * c.mv) ⋆ region c.pQPrev (4 * c.mv) ⋆
      region c.pQNext (4 * c.mv) ⋆ region c.pQStamp (4 * c.mv)) ⋆ c.padU32B) f) :
    region c.pPos (6 * u32VarBytes c.mv) f := by
  have hmv := c.hmv; unfold dimacsBound at hmv
  have hu := u32VarBytes_ge c.mv
  have hult : u32VarBytes c.mv ≤ 4 * c.mv + 7 := by unfold u32VarBytes; omega
  unfold padU32B at hf
  have h2 := rassoc6 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2
    (fun _ => pair_merge (n := u32VarBytes c.mv) (by omega) (by omega))
    (fun _ => pair_merge (n := u32VarBytes c.mv) (by omega) (by omega)))
    (fun _ => pair_merge (n := u32VarBytes c.mv) (by omega) (by omega)))
    (fun _ => pair_merge (n := u32VarBytes c.mv) (by omega) (by omega)))
    (fun _ => pair_merge (n := u32VarBytes c.mv) (by omega) (by omega)))
    (fun _ => pair_merge (n := u32VarBytes c.mv) (by omega) (by omega)) f (sep_zip6 hf))
  have ha1 : c.pMinClr = c.pPos + BitVec.ofNat 64 (u32VarBytes c.mv) := rfl
  have ha2 : c.pShrinkStk = c.pMinClr + BitVec.ofNat 64 (u32VarBytes c.mv) := rfl
  have ha3 : c.pQPrev = c.pShrinkStk + BitVec.ofNat 64 (u32VarBytes c.mv) := rfl
  have ha4 : c.pQNext = c.pQPrev + BitVec.ofNat 64 (u32VarBytes c.mv) := rfl
  have ha5 : c.pQStamp = c.pQNext + BitVec.ofNat 64 (u32VarBytes c.mv) := rfl
  have s1 := step_merge h2 ha1 (by omega)
  have ha2' : c.pShrinkStk = c.pPos + BitVec.ofNat 64 (u32VarBytes c.mv + u32VarBytes c.mv) := by
    rw [ha2, ha1, ptr_add_ofNat]
  have s2 := step_merge s1 ha2' (by omega)
  have ha3' : c.pQPrev = c.pPos +
      BitVec.ofNat 64 (u32VarBytes c.mv + u32VarBytes c.mv + u32VarBytes c.mv) := by
    rw [ha3, ha2', ptr_add_ofNat]
  have s3 := step_merge s2 ha3' (by omega)
  have ha4' : c.pQNext = c.pPos + BitVec.ofNat 64
      (u32VarBytes c.mv + u32VarBytes c.mv + u32VarBytes c.mv + u32VarBytes c.mv) := by
    rw [ha4, ha3', ptr_add_ofNat]
  have s4 := step_merge s3 ha4' (by omega)
  have ha5' : c.pQStamp = c.pPos + BitVec.ofNat 64 (u32VarBytes c.mv + u32VarBytes c.mv +
      u32VarBytes c.mv + u32VarBytes c.mv + u32VarBytes c.mv) := by
    rw [ha5, ha4', ptr_add_ofNat]
  have s5 := step_merge2 s4 ha5' (by omega)
  have hlen : u32VarBytes c.mv + u32VarBytes c.mv + u32VarBytes c.mv +
      u32VarBytes c.mv + u32VarBytes c.mv + u32VarBytes c.mv = 6 * u32VarBytes c.mv := by omega
  rwa [hlen] at s5

private theorem collapse_tail (c : PlainCfg) {f : Mem 64}
    (hf : ((region c.pWvec (16 * c.mv) ⋆ region c.pWsort (8 * c.mv) ⋆
      region c.pScore (8 * c.mv) ⋆ region c.pMinStk (8 * c.minDepth) ⋆
      region c.pGlueUsed 256 ⋆ region c.pArena (4 * c.arena_cap) ⋆
      region c.pWstk (4 * c.wcap) ⋆ region c.pDelayed (12 * c.delayed_cap) ⋆
      region c.pRedRefs (4 * c.red_cap)) ⋆ region c.pSlack c.slack) f) :
    region c.pWvec (c.avail - (768 + valsBytes c.mv + 4 * markBytes c.mv +
      12 * u32VarBytes c.mv)) f := by
  have hfit := c.havail_fit; have hsz := c.hsize; have hmv := c.hmv
  have hf' := rassoc10 hf
  have ha1 : c.pWsort = c.pWvec + BitVec.ofNat 64 (16 * c.mv) := rfl
  have ha2 : c.pScore = c.pWsort + BitVec.ofNat 64 (8 * c.mv) := rfl
  have ha3 : c.pMinStk = c.pScore + BitVec.ofNat 64 (8 * c.mv) := rfl
  have ha4 : c.pGlueUsed = c.pMinStk + BitVec.ofNat 64 (8 * c.minDepth) := rfl
  have ha5 : c.pArena = c.pGlueUsed + BitVec.ofNat 64 256 := rfl
  have ha6 : c.pWstk = c.pArena + BitVec.ofNat 64 (4 * c.arena_cap) := rfl
  have ha7 : c.pDelayed = c.pWstk + BitVec.ofNat 64 (4 * c.wcap) := rfl
  have ha8 : c.pRedRefs = c.pDelayed + BitVec.ofNat 64 (12 * c.delayed_cap) := rfl
  have ha9 : c.pSlack = c.pRedRefs + BitVec.ofNat 64 (4 * c.red_cap) := rfl
  unfold plainFixedBytes minDepth slack dimacsBound plainMinDepthOf at *
  have s1 := step_merge hf' ha1 (by omega)
  have ha2' : c.pScore = c.pWvec + BitVec.ofNat 64 (16 * c.mv + 8 * c.mv) := by
    rw [ha2, ha1, ptr_add_ofNat]
  have s2 := step_merge s1 ha2' (by omega)
  have ha3' : c.pMinStk = c.pWvec + BitVec.ofNat 64 (16 * c.mv + 8 * c.mv + 8 * c.mv) := by
    rw [ha3, ha2', ptr_add_ofNat]
  have s3 := step_merge s2 ha3' (by omega)
  have ha4' : c.pGlueUsed = c.pWvec + BitVec.ofNat 64
      (16 * c.mv + 8 * c.mv + 8 * c.mv + 8 * (if c.mv + 1 < 1000 then c.mv + 1 else 1000)) := by
    rw [ha4, ha3', ptr_add_ofNat]
  have s4 := step_merge s3 ha4' (by omega)
  have ha5' : c.pArena = c.pWvec + BitVec.ofNat 64
      (16 * c.mv + 8 * c.mv + 8 * c.mv +
        8 * (if c.mv + 1 < 1000 then c.mv + 1 else 1000) + 256) := by
    rw [ha5, ha4', ptr_add_ofNat]
  have s5 := step_merge s4 ha5' (by omega)
  have ha6' : c.pWstk = c.pWvec + BitVec.ofNat 64
      (16 * c.mv + 8 * c.mv + 8 * c.mv +
        8 * (if c.mv + 1 < 1000 then c.mv + 1 else 1000) + 256 + 4 * c.arena_cap) := by
    rw [ha6, ha5', ptr_add_ofNat]
  have s6 := step_merge s5 ha6' (by omega)
  have ha7' : c.pDelayed = c.pWvec + BitVec.ofNat 64
      (16 * c.mv + 8 * c.mv + 8 * c.mv +
        8 * (if c.mv + 1 < 1000 then c.mv + 1 else 1000) + 256 +
        4 * c.arena_cap + 4 * c.wcap) := by
    rw [ha7, ha6', ptr_add_ofNat]
  have s7 := step_merge s6 ha7' (by omega)
  have ha8' : c.pRedRefs = c.pWvec + BitVec.ofNat 64
      (16 * c.mv + 8 * c.mv + 8 * c.mv +
        8 * (if c.mv + 1 < 1000 then c.mv + 1 else 1000) + 256 +
        4 * c.arena_cap + 4 * c.wcap + 12 * c.delayed_cap) := by
    rw [ha8, ha7', ptr_add_ofNat]
  have s8 := step_merge s7 ha8' (by omega)
  have ha9' : c.pSlack = c.pWvec + BitVec.ofNat 64
      (16 * c.mv + 8 * c.mv + 8 * c.mv +
        8 * (if c.mv + 1 < 1000 then c.mv + 1 else 1000) + 256 +
        4 * c.arena_cap + 4 * c.wcap + 12 * c.delayed_cap + 4 * c.red_cap) := by
    rw [ha9, ha8', ptr_add_ofNat]
  have s9 := step_merge2 s8 ha9' (by unfold plainFixedBytes plainMinDepthOf; omega)
  have hlen : 16 * c.mv + 8 * c.mv + 8 * c.mv +
      8 * (if c.mv + 1 < 1000 then c.mv + 1 else 1000) + 256 + 4 * c.arena_cap +
      4 * c.wcap + 12 * c.delayed_cap + 4 * c.red_cap +
      (c.avail - (1024 + valsBytes c.mv + 4 * markBytes c.mv + 12 * u32VarBytes c.mv +
        32 * c.mv + 8 * (if c.mv + 1 < 1000 then c.mv + 1 else 1000) +
        4 * c.arena_cap + 4 * c.wcap + 12 * c.delayed_cap + 4 * c.red_cap)) =
      c.avail - (768 + valsBytes c.mv + 4 * markBytes c.mv + 12 * u32VarBytes c.mv) := by
    omega
  unfold plainFixedBytes plainMinDepthOf at s9
  rwa [hlen] at s9

private theorem grouped_to_avail (c : PlainCfg) {m : Mem 64}
    (hsplit : ((region c.hdr 32 ⋆ region (c.hdr + BitVec.ofNat 64 32) 736) ⋆
      (region c.pVals (2 * c.mv) ⋆ region c.pMark c.mv ⋆ region c.pPhases c.mv ⋆
      region c.pPhasesTarget c.mv ⋆ region c.pPhasesBest c.mv) ⋆
      (region c.pLevel (4 * c.mv) ⋆ region c.pReason (4 * c.mv) ⋆
      region c.pTrail (4 * c.mv) ⋆ region c.pTrailPos (4 * c.mv) ⋆
      region c.pTmp (4 * c.mv) ⋆ region c.pHeap (4 * c.mv)) ⋆
      (region c.pPos (4 * c.mv) ⋆ region c.pMinClr (4 * c.mv) ⋆
      region c.pShrinkStk (4 * c.mv) ⋆ region c.pQPrev (4 * c.mv) ⋆
      region c.pQNext (4 * c.mv) ⋆ region c.pQStamp (4 * c.mv)) ⋆
      (region c.pWvec (16 * c.mv) ⋆ region c.pWsort (8 * c.mv) ⋆
      region c.pScore (8 * c.mv) ⋆ region c.pMinStk (8 * c.minDepth) ⋆
      region c.pGlueUsed 256 ⋆ region c.pArena (4 * c.arena_cap) ⋆
      region c.pWstk (4 * c.wcap) ⋆ region c.pDelayed (12 * c.delayed_cap) ⋆
      region c.pRedRefs (4 * c.red_cap)) ⋆
      (c.padMarks ⋆ c.padU32A ⋆ c.padU32B ⋆ region c.pSlack c.slack)) m) :
    region c.hdr c.avail m := by
  have hfit := c.havail_fit; have hsz := c.hsize; have hmv := c.hmv
  have hle : plainFixedBytes c.mv ≤ c.avail := by
    unfold plainFixedBytes at *; omega
  unfold plainFixedBytes at hsz hle; unfold dimacsBound at hmv
  have hg := sep_group_all hsplit
  have hc : ((region c.hdr (768 + valsBytes c.mv + 4 * markBytes c.mv) ⋆
      region c.pLevel (6 * u32VarBytes c.mv)) ⋆
      (region c.pPos (6 * u32VarBytes c.mv) ⋆
      region c.pWvec (c.avail - (768 + valsBytes c.mv + 4 * markBytes c.mv +
        12 * u32VarBytes c.mv)))) m :=
    sep_mono2 (sep_mono2 (fun _ h => collapse_marks c h) (fun _ h => collapse_u32a c h))
      (sep_mono2 (fun _ h => collapse_u32b c h) (fun _ h => collapse_tail c h)) m hg
  have hpL : c.pLevel = c.hdr + BitVec.ofNat 64 (768 + valsBytes c.mv + 4 * markBytes c.mv) := by
    unfold pLevel pPhasesBest pPhasesTarget pPhases pMark pVals
    rw [ptr_add_ofNat, ptr_add_ofNat, ptr_add_ofNat, ptr_add_ofNat, ptr_add_ofNat]
    exact congrArg (fun n => c.hdr + BitVec.ofNat 64 n) (by omega)
  have hpP : c.pPos = c.hdr + BitVec.ofNat 64 (768 + valsBytes c.mv + 4 * markBytes c.mv +
      6 * u32VarBytes c.mv) := by
    unfold pPos pHeap pTmp pTrailPos pTrail pReason
    rw [hpL, ptr_add_ofNat, ptr_add_ofNat, ptr_add_ofNat, ptr_add_ofNat, ptr_add_ofNat,
      ptr_add_ofNat]
    exact congrArg (fun n => c.hdr + BitVec.ofNat 64 n) (by omega)
  have hpW : c.pWvec = c.hdr + BitVec.ofNat 64 (768 + valsBytes c.mv + 4 * markBytes c.mv +
      12 * u32VarBytes c.mv) := by
    unfold pWvec pQStamp pQNext pQPrev pShrinkStk pMinClr
    rw [hpP, ptr_add_ofNat, ptr_add_ofNat, ptr_add_ofNat, ptr_add_ofNat, ptr_add_ofNat,
      ptr_add_ofNat]
    exact congrArg (fun n => c.hdr + BitVec.ofNat 64 n) (by omega)
  have hL : (region c.hdr (768 + valsBytes c.mv + 4 * markBytes c.mv + 6 * u32VarBytes c.mv) ⋆
      (region c.pPos (6 * u32VarBytes c.mv) ⋆
      region c.pWvec (c.avail - (768 + valsBytes c.mv + 4 * markBytes c.mv +
        12 * u32VarBytes c.mv)))) m :=
    sep_mono (fun _ h => step_merge2 h hpL (by unfold valsBytes markBytes u32VarBytes; omega)) hc
  have hP := step_merge hL hpP (by unfold valsBytes markBytes u32VarBytes; omega)
  have h12 : (768 + valsBytes c.mv + 4 * markBytes c.mv + 6 * u32VarBytes c.mv) +
      6 * u32VarBytes c.mv =
      768 + valsBytes c.mv + 4 * markBytes c.mv + 12 * u32VarBytes c.mv := by omega
  rw [h12] at hP
  have hW := step_merge2 hP hpW (by omega)
  have htot : (768 + valsBytes c.mv + 4 * markBytes c.mv + 12 * u32VarBytes c.mv) +
      (c.avail - (768 + valsBytes c.mv + 4 * markBytes c.mv + 12 * u32VarBytes c.mv)) =
      c.avail := by omega
  rwa [htot] at hW

/-- Collapse all 28 active memory regions + padding back into `region c.hdr c.avail`. -/
theorem regions_to_avail (c : PlainCfg) {m : Mem 64}
    (hm : (region c.hdr 32 ⋆ region (c.hdr + BitVec.ofNat 64 32) 736 ⋆
      region c.pVals (2 * c.mv) ⋆ region c.pMark c.mv ⋆ region c.pPhases c.mv ⋆
      region c.pPhasesTarget c.mv ⋆ region c.pPhasesBest c.mv ⋆
      region c.pLevel (4 * c.mv) ⋆ region c.pReason (4 * c.mv) ⋆
      region c.pTrail (4 * c.mv) ⋆ region c.pTrailPos (4 * c.mv) ⋆
      region c.pTmp (4 * c.mv) ⋆ region c.pHeap (4 * c.mv) ⋆
      region c.pPos (4 * c.mv) ⋆ region c.pMinClr (4 * c.mv) ⋆
      region c.pShrinkStk (4 * c.mv) ⋆ region c.pQPrev (4 * c.mv) ⋆
      region c.pQNext (4 * c.mv) ⋆ region c.pQStamp (4 * c.mv) ⋆
      region c.pWvec (16 * c.mv) ⋆ region c.pWsort (8 * c.mv) ⋆
      region c.pScore (8 * c.mv) ⋆ region c.pMinStk (8 * c.minDepth) ⋆
      region c.pGlueUsed 256 ⋆ region c.pArena (4 * c.arena_cap) ⋆
      region c.pWstk (4 * c.wcap) ⋆ region c.pDelayed (12 * c.delayed_cap) ⋆
      region c.pRedRefs (4 * c.red_cap) ⋆ c.pad) m) : region c.hdr c.avail m := by
  unfold pad at hm
  refine grouped_to_avail c ?_
  have g9 : ∀ {X A B C D E F G H I : Mem 64 → Prop} {k : Mem 64},
      (X ⋆ A ⋆ B ⋆ C ⋆ D ⋆ E ⋆ F ⋆ G ⋆ H ⋆ I) k →
      (X ⋆ (A ⋆ B ⋆ C ⋆ D ⋆ E ⋆ F ⋆ G ⋆ H ⋆ I)) k := fun h => sep_ac h
  have g6 : ∀ {X A B C D E F : Mem 64 → Prop} {k : Mem 64},
      (X ⋆ A ⋆ B ⋆ C ⋆ D ⋆ E ⋆ F) k → (X ⋆ (A ⋆ B ⋆ C ⋆ D ⋆ E ⋆ F)) k := fun h => sep_ac h
  have g5 : ∀ {X A B C D E : Mem 64 → Prop} {k : Mem 64},
      (X ⋆ A ⋆ B ⋆ C ⋆ D ⋆ E) k → (X ⋆ (A ⋆ B ⋆ C ⋆ D ⋆ E)) k := fun h => sep_ac h
  have s1 := sep_mono (fun _ h => g9 h) hm
  have s2 := sep_mono (fun _ g => sep_mono (fun _ h => g6 h) g) s1
  have s3 := sep_mono (fun _ g1 => sep_mono (fun _ g2 => sep_mono (fun _ h => g6 h) g2) g1) s2
  exact sep_mono (fun _ g1 => sep_mono (fun _ g2 => sep_mono (fun _ g3 =>
    sep_mono (fun _ h => g5 h) g3) g2) g1) s3

end PlainCfg

/-! ## 3. `PlainHeur`, `PlainState`, `LengthsOk`, and `hdrTailWords` -/

/-- Non-soundness heuristic scalars and arrays separated from `PlainState` core soundness
obligations (`heap`, `pos`, `score`, `phases*`, `wsort`, `shrink_stk`, `red_refs`, `glue_used`,
VMTF queue, mode switching, rephasing, restart EMAs/Luby, `delayed`). -/
structure PlainHeur where
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
  heap : List (BitVec 32)
  pos : List (BitVec 32)
  score : List (BitVec 64)
  phases : List (BitVec 8)
  phases_target : List (BitVec 8)
  phases_best : List (BitVec 8)
  wsort : List (BitVec 32)
  shrink_stk : List (BitVec 32)
  red_refs : List (BitVec 32)
  glue_used : List (BitVec 32)
  q_prev : List (BitVec 32)
  q_next : List (BitVec 32)
  q_stamp : List (BitVec 32)
  delayed : List (BitVec 32)

structure PlainHeur.LengthsOk (c : PlainCfg) (h : PlainHeur) : Prop where
  heap_len_arr : h.heap.length = c.mv
  pos_len : h.pos.length = c.mv
  score_len : h.score.length = c.mv
  phases_len : h.phases.length = c.mv
  phases_target_len : h.phases_target.length = c.mv
  phases_best_len : h.phases_best.length = c.mv
  wsort_len : h.wsort.length = 2 * c.mv
  shrink_stk_len : h.shrink_stk.length = c.mv
  red_refs_len : h.red_refs.length = c.red_cap
  glue_used_len : h.glue_used.length = 64
  q_prev_len : h.q_prev.length = c.mv
  q_next_len : h.q_next.length = c.mv
  q_stamp_len : h.q_stamp.length = c.mv
  delayed_len_arr : h.delayed.length = 3 * c.delayed_cap

/-- Soundness-relevant C0 solver state for `D-Plain`. -/
structure PlainState where
  d_cur : BitVec 64
  d_val : BitVec 64
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
  vals : List (BitVec 8)
  mrk : List (BitVec 8)
  lvl : List (BitVec 32)
  rsns : List (BitVec 32)
  trl : List (BitVec 32)
  trail_pos : List (BitVec 32)
  tmp : List (BitVec 32)
  wvec : List (BitVec 32)
  arena : List (BitVec 32)
  wstk : List (BitVec 32)
  min_stk : List (BitVec 32)
  min_clr : List (BitVec 32)
  heur : PlainHeur

structure PlainState.LengthsOk (c : PlainCfg) (s : PlainState) : Prop where
  vals_len : s.vals.length = 2 * c.mv
  mrk_len : s.mrk.length = c.mv
  lvl_len : s.lvl.length = c.mv
  rsns_len : s.rsns.length = c.mv
  trl_len : s.trl.length = c.mv
  trail_pos_len : s.trail_pos.length = c.mv
  tmp_len_arr : s.tmp.length = c.mv
  wvec_len : s.wvec.length = 4 * c.mv
  arena_len_arr : s.arena.length = c.arena_cap
  wstk_len_arr : s.wstk.length = c.wcap
  min_stk_len : s.min_stk.length = 2 * c.minDepth
  min_clr_len_arr : s.min_clr.length = c.mv
  arena_len_le : s.arena_len ≤ c.arena_cap
  wlen_le : s.wlen ≤ c.wcap
  trail_end_le : s.trail_end ≤ c.mv
  propagated_le : s.propagated ≤ s.trail_end
  tmp_len_le : s.tmp_len ≤ c.mv
  min_clr_len_le : s.min_clr_len ≤ c.mv
  heur_ok : s.heur.LengthsOk c

/-- The 92 trailing `u64` words of `PlainHdr` starting at offset `c.hdr + 32`. -/
def hdrTailWords (c : PlainCfg) (s : PlainState) : List (BitVec 64) :=
  [ BitVec.ofNat 64 c.arena_cap, BitVec.ofNat 64 c.wcap
  , BitVec.ofNat 64 s.arena_len, BitVec.ofNat 64 s.wlen
  , c.pVals, c.pMark, c.pLevel, c.pReason, c.pTrail, c.pWvec
  , c.pArena, c.pWstk, c.pDelayed, c.pTmp
  , BitVec.ofNat 64 s.trail_end, BitVec.ofNat 64 s.propagated
  , BitVec.ofNat 64 s.cur_level, s.fuel, s.confl_ref
  , BitVec.ofNat 64 s.tmp_cnt, BitVec.ofNat 64 s.tmp_len
  , c.pHeap, c.pPos, c.pScore, c.pPhases, c.pMinStk, c.pMinClr
  , BitVec.ofNat 64 s.heur.heap_len, s.heur.scinc, BitVec.ofNat 64 c.minDepth
  , BitVec.ofNat 64 s.min_clr_len, s.min_clr_full
  , s.heur.rel_period, s.heur.rel_limit, s.heur.rel_wait, s.heur.rel_u
  , s.heur.rel_v, s.heur.rel_trigger
  , s.heur.conflicts, s.heur.learned_lits, s.heur.min_removed
  , c.pTrailPos, c.pQPrev, c.pQNext, c.pQStamp
  , c.pPhasesTarget, c.pPhasesBest, c.pWsort, c.pShrinkStk, c.pRedRefs, c.pGlueUsed
  , BitVec.ofNat 64 c.red_cap, BitVec.ofNat 64 c.delayed_cap
  , BitVec.ofNat 64 s.heur.delayed_len, s.wusable, s.arena_garbage, s.first_reducible
  , s.num_irred, s.num_redundant, s.num_binary, s.unflushed, s.probing
  , s.confl_type, s.confl_lit0, s.confl_lit1
  , s.heur.stable, s.heur.switched, s.heur.mode_count
  , s.heur.mode_confl_lim, s.heur.mode_tick_lim, s.heur.mode_saved_ticks
  , s.heur.search_ticks
  , s.heur.q_first, s.heur.q_last, s.heur.q_search_idx, s.heur.q_search_stamp
  , s.heur.q_cur_stamp, s.heur.target_assigned, s.heur.best_assigned
  , s.heur.rephase_limit, s.heur.rephased, s.heur.reduce_limit, s.heur.reductions
  , s.heur.tier1, s.heur.tier2, s.heur.restarts, s.heur.restart_limit
  , s.heur.ema_fast_biased, s.heur.ema_fast_exp
  , s.heur.ema_slow_biased, s.heur.ema_slow_exp
  , s.oom ]

@[simp] theorem hdrTailWords_length (c : PlainCfg) (s : PlainState) :
    (hdrTailWords c s).length = 92 := rfl

/-! ## 4. Memory footprints, collapse, and `check_model` bridge -/

def PlainCoreArrays (c : PlainCfg) (s : PlainState) : Mem 64 → Prop :=
  array (t := i8) c.pVals s.vals ⋆ array (t := i8) c.pMark s.mrk ⋆
  array (t := i32) c.pLevel s.lvl ⋆ array (t := i32) c.pReason s.rsns ⋆
  array (t := i32) c.pTrail s.trl ⋆ array (t := i32) c.pTrailPos s.trail_pos ⋆
  array (t := i32) c.pTmp s.tmp ⋆ array (t := i32) c.pWvec s.wvec ⋆
  array (t := i32) c.pArena s.arena ⋆ array (t := i32) c.pWstk s.wstk ⋆
  array (t := i32) c.pMinStk s.min_stk ⋆ array (t := i32) c.pMinClr s.min_clr

def PlainHeurArrays (c : PlainCfg) (h : PlainHeur) : Mem 64 → Prop :=
  array (t := i32) c.pHeap h.heap ⋆ array (t := i32) c.pPos h.pos ⋆
  array64 c.pScore h.score ⋆ array (t := i8) c.pPhases h.phases ⋆
  array (t := i8) c.pPhasesTarget h.phases_target ⋆
  array (t := i8) c.pPhasesBest h.phases_best ⋆
  array (t := i32) c.pWsort h.wsort ⋆ array (t := i32) c.pShrinkStk h.shrink_stk ⋆
  array (t := i32) c.pRedRefs h.red_refs ⋆ array (t := i32) c.pGlueUsed h.glue_used ⋆
  array (t := i32) c.pQPrev h.q_prev ⋆ array (t := i32) c.pQNext h.q_next ⋆
  array (t := i32) c.pQStamp h.q_stamp ⋆ array (t := i32) c.pDelayed h.delayed

def PlainMem (c : PlainCfg) (s : PlainState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.d_cur s.d_val ⋆
  array64 (c.hdr + 32) (hdrTailWords c s) ⋆ PlainCoreArrays c s ⋆ PlainHeurArrays c s.heur ⋆ c.pad

def PlainArenaInv (c : PlainCfg) (s : PlainState) (m : Mem 64) : Prop :=
  s.LengthsOk c ∧ PlainMem c s m

def PlainRest (c : PlainCfg) (s : PlainState) : Mem 64 → Prop :=
  array64 (c.hdr + 32) (hdrTailWords c s) ⋆ PlainCoreArrays c s ⋆ PlainHeurArrays c s.heur ⋆ c.pad

theorem plainMem_eq_dimacs_sep (c : PlainCfg) (s : PlainState) :
    PlainMem c s =
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.d_cur s.d_val ⋆
        PlainRest c s) := by
  unfold PlainMem PlainRest; ac_rfl

theorem plainRest_d_irrel (c : PlainCfg) (s : PlainState) (cur' val' : BitVec 64) :
    PlainRest c { s with d_cur := cur', d_val := val' } = PlainRest c s := rfl

private theorem pArr8 {a : BitVec 64} {xs : List (BitVec 8)} {n : Nat}
    (hn : xs.length = n) (hbd : n ≤ 2 ^ 64) {f : Mem 64} (hf : array (t := i8) a xs f) :
    region a n f := by
  simpa [Ty.bytes, Ty.size, i8, hn] using
    array_to_region (t := i8) (by simp [Ty.bytes, Ty.size, i8, hn, hbd]) hf

private theorem pArr32 {a : BitVec 64} {xs : List (BitVec 32)} {n m : Nat}
    (hn : xs.length = n) (hm : 4 * n = m) (hbd : m ≤ 2 ^ 64) {f : Mem 64}
    (hf : array (t := i32) a xs f) : region a m f := by
  simpa [Ty.bytes, Ty.size, i32, hn, hm] using
    array_to_region (t := i32) (by simp [Ty.bytes, Ty.size, i32, hn]; omega) hf

private theorem pArr64 {a : BitVec 64} {xs : List (BitVec 64)} {n m : Nat}
    (hn : xs.length = n) (hm : 8 * n = m) (hbd : m ≤ 2 ^ 64) {f : Mem 64}
    (hf : array64 a xs f) : region a m f := by
  simpa [Ty.bytes, Ty.size, i64, hn, hm] using
    array_to_region (t := i64) (xs := xs) (by simp [Ty.bytes, Ty.size, i64, hn]; omega)
      ((array64_eq_array a xs) ▸ hf)

private theorem plainCoreArrays_to_regions {c : PlainCfg} {s : PlainState} (hlen : s.LengthsOk c)
    {f : Mem 64} (hf : PlainCoreArrays c s f) :
    (region c.pVals (2 * c.mv) ⋆ region c.pMark c.mv ⋆
      region c.pLevel (4 * c.mv) ⋆ region c.pReason (4 * c.mv) ⋆
      region c.pTrail (4 * c.mv) ⋆ region c.pTrailPos (4 * c.mv) ⋆
      region c.pTmp (4 * c.mv) ⋆ region c.pWvec (16 * c.mv) ⋆
      region c.pArena (4 * c.arena_cap) ⋆ region c.pWstk (4 * c.wcap) ⋆
      region c.pMinStk (8 * c.minDepth) ⋆ region c.pMinClr (4 * c.mv)) f := by
  have hmv := c.hmv; have har := c.harena; have hw := c.hwcap
  have hmd := plainMinDepthOf_le c.mv
  unfold dimacsBound at hmv har hw; unfold PlainCfg.minDepth at *; unfold PlainCoreArrays at hf
  refine sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2
    (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2
      (fun _ => pArr8 hlen.vals_len (by omega))
      (fun _ => pArr8 hlen.mrk_len (by omega)))
      (fun _ => pArr32 hlen.lvl_len rfl (by omega)))
      (fun _ => pArr32 hlen.rsns_len rfl (by omega)))
      (fun _ => pArr32 hlen.trl_len rfl (by omega)))
      (fun _ => pArr32 hlen.trail_pos_len rfl (by omega)))
      (fun _ => pArr32 hlen.tmp_len_arr rfl (by omega)))
      (fun _ => pArr32 hlen.wvec_len (by omega) (by omega)))
      (fun _ => pArr32 hlen.arena_len_arr rfl (by omega)))
      (fun _ => pArr32 hlen.wstk_len_arr rfl (by omega)))
      (fun _ => pArr32 hlen.min_stk_len (by unfold PlainCfg.minDepth; omega) (by omega)))
      (fun _ => pArr32 hlen.min_clr_len_arr rfl (by omega)) f hf

private theorem plainHeurArrays_to_regions {c : PlainCfg} {h : PlainHeur} (hok : h.LengthsOk c)
    {f : Mem 64} (hf : PlainHeurArrays c h f) :
    (region c.pHeap (4 * c.mv) ⋆ region c.pPos (4 * c.mv) ⋆
      region c.pScore (8 * c.mv) ⋆ region c.pPhases c.mv ⋆
      region c.pPhasesTarget c.mv ⋆ region c.pPhasesBest c.mv ⋆
      region c.pWsort (8 * c.mv) ⋆ region c.pShrinkStk (4 * c.mv) ⋆
      region c.pRedRefs (4 * c.red_cap) ⋆ region c.pGlueUsed 256 ⋆
      region c.pQPrev (4 * c.mv) ⋆ region c.pQNext (4 * c.mv) ⋆
      region c.pQStamp (4 * c.mv) ⋆ region c.pDelayed (12 * c.delayed_cap)) f := by
  have hmv := c.hmv; have hdl := c.hdel; have hrd := c.hred
  unfold dimacsBound at hmv hdl hrd; unfold PlainHeurArrays at hf
  refine sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2
    (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2
      (fun _ => pArr32 hok.heap_len_arr rfl (by omega))
      (fun _ => pArr32 hok.pos_len rfl (by omega)))
      (fun _ => pArr64 hok.score_len rfl (by omega)))
      (fun _ => pArr8 hok.phases_len (by omega)))
      (fun _ => pArr8 hok.phases_target_len (by omega)))
      (fun _ => pArr8 hok.phases_best_len (by omega)))
      (fun _ => pArr32 hok.wsort_len (by omega) (by omega)))
      (fun _ => pArr32 hok.shrink_stk_len rfl (by omega)))
      (fun _ => pArr32 hok.red_refs_len rfl (by omega)))
      (fun _ => pArr32 hok.glue_used_len (by omega) (by omega)))
      (fun _ => pArr32 hok.q_prev_len rfl (by omega)))
      (fun _ => pArr32 hok.q_next_len rfl (by omega)))
      (fun _ => pArr32 hok.q_stamp_len rfl (by omega)))
      (fun _ => pArr32 hok.delayed_len_arr (by omega) (by omega)) f hf

private theorem perm_core12 {V M L R T TP TM W A WS MS MC : Mem 64 → Prop} {f : Mem 64}
    (h : (V ⋆ M ⋆ L ⋆ R ⋆ T ⋆ TP ⋆ TM ⋆ W ⋆ A ⋆ WS ⋆ MS ⋆ MC) f) :
    ((V ⋆ M) ⋆ (L ⋆ R ⋆ T ⋆ TP ⋆ TM) ⋆ MC ⋆ (W ⋆ MS ⋆ A ⋆ WS)) f := sep_ac h

private theorem perm_heur14 {Hp Ps Sc Ph Pt Pb Ws Sh Rd Gu Qp Qn Qs Dl : Mem 64 → Prop}
    {f : Mem 64}
    (h : (Hp ⋆ Ps ⋆ Sc ⋆ Ph ⋆ Pt ⋆ Pb ⋆ Ws ⋆ Sh ⋆ Rd ⋆ Gu ⋆ Qp ⋆ Qn ⋆ Qs ⋆ Dl) f) :
    ((Ph ⋆ Pt ⋆ Pb) ⋆ Hp ⋆ (Ps ⋆ Sh ⋆ Qp ⋆ Qn ⋆ Qs) ⋆ (Ws ⋆ Sc ⋆ Gu ⋆ Dl ⋆ Rd)) f := by
  have g4 : ∀ {X A B C D : Mem 64 → Prop} {k : Mem 64},
      (X ⋆ A ⋆ B ⋆ C ⋆ D) k → (X ⋆ (A ⋆ B ⋆ C ⋆ D)) k := fun x => sep_ac x
  have g3 : ∀ {X A B C : Mem 64 → Prop} {k : Mem 64},
      (X ⋆ A ⋆ B ⋆ C) k → (X ⋆ (A ⋆ B ⋆ C)) k := fun x => sep_ac x
  have s1 := g4 h
  have s2 := sep_mono (fun _ x => g4 x) s1
  have s3 := sep_mono (fun _ g => sep_mono (fun _ x => g3 x) g) s2
  have s4 : (((Hp ⋆ Ps ⋆ Sc) ⋆ (Ph ⋆ Pt ⋆ Pb) ⋆ (Ws ⋆ Sh ⋆ Rd ⋆ Gu)) ⋆
      (Qp ⋆ Qn ⋆ Qs ⋆ Dl)) f := s3
  have s4'' : (((Hp ⋆ Ps ⋆ Sc) ⋆ (Ph ⋆ Pt ⋆ Pb) ⋆ (Ws ⋆ Sh ⋆ Rd ⋆ Gu)) ⋆
      ((Qp ⋆ Qn ⋆ Qs) ⋆ Dl)) f := sep_mono_r (fun _ x => sep_ac x) s4
  have p1 : ∀ {X1 X2 X3 X4 Y1 Y2 Y3 Y4 Z1 Z2 : Mem 64 → Prop} {k : Mem 64},
      ((((X1 ⋆ X2) ⋆ X3) ⋆ X4 ⋆ (Y1 ⋆ Y2 ⋆ Y3 ⋆ Y4)) ⋆ (Z1 ⋆ Z2)) k →
      (X4 ⋆ X1 ⋆ (X2 ⋆ Y2 ⋆ Z1) ⋆ (Y1 ⋆ X3 ⋆ Y4 ⋆ Z2 ⋆ Y3)) k := fun x => sep_ac x
  have s5 : ((Ph ⋆ Pt ⋆ Pb) ⋆ Hp ⋆ (Ps ⋆ Sh ⋆ (Qp ⋆ Qn ⋆ Qs)) ⋆
      (Ws ⋆ Sc ⋆ Gu ⋆ Dl ⋆ Rd)) f := p1 s4''
  have t1 : ∀ {H0 H1 A1 A2 A3 A4 A5 B0 : Mem 64 → Prop} {k : Mem 64},
      (H0 ⋆ H1 ⋆ (A1 ⋆ A2 ⋆ (A3 ⋆ A4 ⋆ A5)) ⋆ B0) k →
      (H0 ⋆ H1 ⋆ (A1 ⋆ A2 ⋆ A3 ⋆ A4 ⋆ A5) ⋆ B0) k := fun x => sep_ac x
  exact t1 s5

private theorem unmix_m {V M Ph Pt Pb : Mem 64 → Prop} {f : Mem 64}
    (h : ((V ⋆ M) ⋆ (Ph ⋆ Pt ⋆ Pb)) f) : (V ⋆ M ⋆ Ph ⋆ Pt ⋆ Pb) f := sep_ac h

private theorem unmix_a {L R T TP TM Hp : Mem 64 → Prop} {f : Mem 64}
    (h : ((L ⋆ R ⋆ T ⋆ TP ⋆ TM) ⋆ Hp) f) : (L ⋆ R ⋆ T ⋆ TP ⋆ TM ⋆ Hp) f := sep_ac h

private theorem unmix_b {MC Ps Sh Qp Qn Qs : Mem 64 → Prop} {f : Mem 64}
    (h : (MC ⋆ (Ps ⋆ Sh ⋆ Qp ⋆ Qn ⋆ Qs)) f) : (Ps ⋆ MC ⋆ Sh ⋆ Qp ⋆ Qn ⋆ Qs) f := sep_ac h

private theorem unmix_t {W MS A WS Ws Sc Gu Dl Rd : Mem 64 → Prop} {f : Mem 64}
    (h : ((W ⋆ MS ⋆ A ⋆ WS) ⋆ (Ws ⋆ Sc ⋆ Gu ⋆ Dl ⋆ Rd)) f) :
    (W ⋆ Ws ⋆ Sc ⋆ MS ⋆ Gu ⋆ A ⋆ WS ⋆ Dl ⋆ Rd) f := sep_ac h

private theorem sep_combine_groups
    {H cM cA cB cT hM hA hB hT P : Mem 64 → Prop} {f : Mem 64}
    (h : ((H ⋆ (cM ⋆ cA ⋆ cB ⋆ cT) ⋆ (hM ⋆ hA ⋆ hB ⋆ hT) ⋆ P)) f) :
    (H ⋆ (cM ⋆ hM) ⋆ (cA ⋆ hA) ⋆ (cB ⋆ hB) ⋆ (cT ⋆ hT) ⋆ P) f := sep_ac h

private theorem plainRegs_to_avail {c : PlainCfg} {m : Mem 64}
    (hm2 : ((region c.hdr 32 ⋆ region (c.hdr + BitVec.ofNat 64 32) 736) ⋆
      (region c.pVals (2 * c.mv) ⋆ region c.pMark c.mv ⋆
        region c.pLevel (4 * c.mv) ⋆ region c.pReason (4 * c.mv) ⋆
        region c.pTrail (4 * c.mv) ⋆ region c.pTrailPos (4 * c.mv) ⋆
        region c.pTmp (4 * c.mv) ⋆ region c.pWvec (16 * c.mv) ⋆
        region c.pArena (4 * c.arena_cap) ⋆ region c.pWstk (4 * c.wcap) ⋆
        region c.pMinStk (8 * c.minDepth) ⋆ region c.pMinClr (4 * c.mv)) ⋆
      (region c.pHeap (4 * c.mv) ⋆ region c.pPos (4 * c.mv) ⋆
        region c.pScore (8 * c.mv) ⋆ region c.pPhases c.mv ⋆
        region c.pPhasesTarget c.mv ⋆ region c.pPhasesBest c.mv ⋆
        region c.pWsort (8 * c.mv) ⋆ region c.pShrinkStk (4 * c.mv) ⋆
        region c.pRedRefs (4 * c.red_cap) ⋆ region c.pGlueUsed 256 ⋆
        region c.pQPrev (4 * c.mv) ⋆ region c.pQNext (4 * c.mv) ⋆
        region c.pQStamp (4 * c.mv) ⋆ region c.pDelayed (12 * c.delayed_cap)) ⋆ c.pad) m) :
    region c.hdr c.avail m := by
  have hm3 :=
    sep_mono (fun _ g1 => sep_mono (fun _ g2 => sep_mono_r (fun _ h => perm_core12 h) g2) g1) hm2
  have hm4 := sep_mono (fun _ g => sep_mono_r (fun _ h => perm_heur14 h) g) hm3
  have hm5 := sep_combine_groups hm4
  unfold PlainCfg.pad at hm5
  have hm6 := sep_mono (fun _ g1 => sep_mono (fun _ g2 => sep_mono (fun _ g3 =>
    sep_mono (fun _ g4 => sep_mono_r (fun _ h => unmix_m h) g4) g3) g2) g1) hm5
  have hm7 := sep_mono (fun _ g1 => sep_mono (fun _ g2 => sep_mono (fun _ g3 =>
    sep_mono_r (fun _ h => unmix_a h) g3) g2) g1) hm6
  have hm8 := sep_mono (fun _ g1 => sep_mono (fun _ g2 =>
    sep_mono_r (fun _ h => unmix_b h) g2) g1) hm7
  have hm9 := sep_mono (fun _ g => sep_mono_r (fun _ h => unmix_t h) g) hm8
  exact c.grouped_to_avail hm9

theorem plainMem_anyDimacs_to_region {c : PlainCfg} {s : PlainState}
    {mv' nc' cur' val' : BitVec 64} {m : Mem 64} (hlen : s.LengthsOk c)
    (hm : (dimacsState c.hdr mv' nc' cur' val' ⋆
      array64 (c.hdr + 32) (hdrTailWords c s) ⋆
      PlainCoreArrays c s ⋆ PlainHeurArrays c s.heur ⋆ c.pad) m) : region c.hdr c.avail m := by
  have hm1 : ((dimacsState c.hdr mv' nc' cur' val' ⋆ array64 (c.hdr + 32) (hdrTailWords c s)) ⋆
      PlainCoreArrays c s ⋆ PlainHeurArrays c s.heur ⋆ c.pad) m := sep_ac hm
  refine plainRegs_to_avail ?_
  exact sep_mono2 (sep_mono2 (sep_mono2
    (sep_mono2 (fun _ h => dimacsState_to_region h)
      (fun _ h => pArr64 (hdrTailWords_length c s) (m := 736) (by decide) (by omega) h))
    (fun _ h => plainCoreArrays_to_regions hlen h))
    (fun _ h => plainHeurArrays_to_regions hlen.heur_ok h))
    (fun _ h => h) m hm1

theorem PlainArenaInv.to_region {c : PlainCfg} {s : PlainState} {m : Mem 64}
    (h : PlainArenaInv c s m) : region c.hdr c.avail m :=
  plainMem_anyDimacs_to_region h.1 h.2

/-- Non-`vals` remainder of `PlainMem` for `kissat_check_model` framing. -/
def PlainCheckRest (c : PlainCfg) (s : PlainState) : Mem 64 → Prop :=
  array64 (c.hdr + 32) (hdrTailWords c s) ⋆
  array (t := i8) c.pMark s.mrk ⋆ array (t := i32) c.pLevel s.lvl ⋆
  array (t := i32) c.pReason s.rsns ⋆ array (t := i32) c.pTrail s.trl ⋆
  array (t := i32) c.pTrailPos s.trail_pos ⋆ array (t := i32) c.pTmp s.tmp ⋆
  array (t := i32) c.pWvec s.wvec ⋆ array (t := i32) c.pArena s.arena ⋆
  array (t := i32) c.pWstk s.wstk ⋆ array (t := i32) c.pMinStk s.min_stk ⋆
  array (t := i32) c.pMinClr s.min_clr ⋆ PlainHeurArrays c s.heur ⋆ c.pad

theorem plainMem_to_checkModel {c : PlainCfg} {s : PlainState}
    {cnf_ptr : BitVec 64} {cnfBytes : List UInt8} {R : Mem 64 → Prop} {m : Mem 64}
    (hlen : s.LengthsOk c) (hm : (bytes cnf_ptr cnfBytes ⋆ PlainMem c s ⋆ R) m) :
    (bytes cnf_ptr cnfBytes ⋆
      dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.d_cur s.d_val ⋆
      bytes c.pVals (s.vals.map UInt8.ofBitVec) ⋆
      (PlainCheckRest c s ⋆ R)) m := by
  have hmv := c.hmv; unfold dimacsBound at hmv
  have hm1 : (array (t := i8) c.pVals s.vals ⋆
      (bytes cnf_ptr cnfBytes ⋆
        dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.d_cur s.d_val ⋆
        (PlainCheckRest c s ⋆ R))) m := by
    unfold PlainMem PlainCoreArrays at hm; unfold PlainCheckRest; exact sep_ac hm
  have hm2 : (bytes c.pVals (s.vals.map UInt8.ofBitVec) ⋆
      (bytes cnf_ptr cnfBytes ⋆
        dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.d_cur s.d_val ⋆
        (PlainCheckRest c s ⋆ R))) m := by
    refine sep_mono (fun f hf => ?_) hm1
    have hbytes := array_eq_bytesOf (t := i8) c.pVals s.vals
      (by simp [Ty.bytes, Ty.size, i8, hlen.vals_len]; omega) hf
    rw [bytesOf_i8_eq_map] at hbytes; exact hbytes.symm
  exact sep_ac hm2

theorem checkModel_post_to_region {c : PlainCfg} {s : PlainState}
    {mv' nc' cur' val' : BitVec 64} {cnf_ptr : BitVec 64} {cnfBytes : List UInt8}
    {R : Mem 64 → Prop} {m : Mem 64} (hlen : s.LengthsOk c)
    (hm : (bytes cnf_ptr cnfBytes ⋆ dimacsState c.hdr mv' nc' cur' val' ⋆
      bytes c.pVals (s.vals.map UInt8.ofBitVec) ⋆ (PlainCheckRest c s ⋆ R)) m) :
    (bytes cnf_ptr cnfBytes ⋆ region c.hdr c.avail ⋆ R) m := by
  have hmv := c.hmv; have har := c.harena; have hw := c.hwcap
  have hmd := plainMinDepthOf_le c.mv
  unfold dimacsBound PlainCheckRest at *
  have hm1 : ((bytes cnf_ptr cnfBytes ⋆ R) ⋆
      ((dimacsState c.hdr mv' nc' cur' val' ⋆ array64 (c.hdr + 32) (hdrTailWords c s)) ⋆
      (bytes c.pVals (s.vals.map UInt8.ofBitVec) ⋆ array (t := i8) c.pMark s.mrk ⋆
        array (t := i32) c.pLevel s.lvl ⋆ array (t := i32) c.pReason s.rsns ⋆
        array (t := i32) c.pTrail s.trl ⋆ array (t := i32) c.pTrailPos s.trail_pos ⋆
        array (t := i32) c.pTmp s.tmp ⋆ array (t := i32) c.pWvec s.wvec ⋆
        array (t := i32) c.pArena s.arena ⋆ array (t := i32) c.pWstk s.wstk ⋆
        array (t := i32) c.pMinStk s.min_stk ⋆ array (t := i32) c.pMinClr s.min_clr) ⋆
      PlainHeurArrays c s.heur ⋆ c.pad)) m := sep_ac hm
  have hm2 : ((bytes cnf_ptr cnfBytes ⋆ R) ⋆ region c.hdr c.avail) m := by
    refine sep_mono_r (fun _ h => plainRegs_to_avail ?_) hm1
    exact sep_mono2 (sep_mono2 (sep_mono2
      (sep_mono2 (fun _ hb => dimacsState_to_region hb)
        (fun _ hb => pArr64 (hdrTailWords_length c s) (m := 736) (by decide) (by omega) hb))
      (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2
        (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2
          (fun _ (hb : bytes c.pVals (s.vals.map UInt8.ofBitVec) _) => by
            have hb' := bytes_to_region hb; simpa [hlen.vals_len] using hb')
          (fun _ => pArr8 hlen.mrk_len (by omega)))
          (fun _ => pArr32 hlen.lvl_len rfl (by omega)))
          (fun _ => pArr32 hlen.rsns_len rfl (by omega)))
          (fun _ => pArr32 hlen.trl_len rfl (by omega)))
          (fun _ => pArr32 hlen.trail_pos_len rfl (by omega)))
          (fun _ => pArr32 hlen.tmp_len_arr rfl (by omega)))
          (fun _ => pArr32 hlen.wvec_len (by omega) (by omega)))
          (fun _ => pArr32 hlen.arena_len_arr rfl (by omega)))
          (fun _ => pArr32 hlen.wstk_len_arr rfl (by omega)))
          (fun _ => pArr32 hlen.min_stk_len
            (by unfold PlainCfg.minDepth; omega) (by unfold PlainCfg.minDepth; omega)))
          (fun _ => pArr32 hlen.min_clr_len_arr rfl (by omega))))
      (fun _ hb => plainHeurArrays_to_regions hlen.heur_ok hb))
      (fun _ hb => hb) _ h
  exact sep_ac hm2

/-! ## 5. Direct `PlainMem` accessors (`KissatDimacs` + header words `0..40`) -/

section PlainAccess1
variable {c : PlainCfg} {s : PlainState} {R : Mem 64 → Prop} {m : Mem 64}

private theorem focus_dimacs (hm : (PlainMem c s ⋆ R) m) :
    (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.d_cur s.d_val ⋆
      (PlainRest c s ⋆ R)) m := by
  rw [plainMem_eq_dimacs_sep, sep_assoc] at hm; exact hm

private theorem unfocus_dimacs {cur' val' : BitVec 64} {m' : Mem 64}
    (hm : (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) cur' val' ⋆
      (PlainRest c s ⋆ R)) m') :
    (PlainMem c { s with d_cur := cur', d_val := val' } ⋆ R) m' := by
  rw [plainMem_eq_dimacs_sep, plainRest_d_irrel, sep_assoc]; exact hm

theorem plainHdrTailGet (i : Nat) (hi : i < 92) (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + BitVec.ofNat 64 (32 + 8 * i)) =
      some ((hdrTailWords c s)[i]'(by simpa using hi)) := by
  have h1 : (array64 (c.hdr + 32) (hdrTailWords c s) ⋆
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.d_cur s.d_val ⋆
        PlainCoreArrays c s ⋆ PlainHeurArrays c s.heur ⋆ c.pad ⋆ R)) m := by
    unfold PlainMem at hm; exact sep_ac hm
  have hload := loadVal_array64 (i := i) (by simpa using hi) h1
  rwa [show c.hdr + (32 : BitVec 64) + BitVec.ofNat 64 (8 * i) =
    c.hdr + BitVec.ofNat 64 (32 + 8 * i) from ptr_add_ofNat c.hdr 32 (8 * i)] at hload

theorem plainHdrTailPut (i : Nat) (hi : i < 92) (v : BitVec 64) (s' : PlainState)
    (hm : (PlainMem c s ⋆ R) m)
    (heq : hdrTailWords c s' = (hdrTailWords c s).set i v)
    (hd1 : s'.d_cur = s.d_cur) (hd2 : s'.d_val = s.d_val)
    (hca : PlainCoreArrays c s' = PlainCoreArrays c s)
    (hha : PlainHeurArrays c s'.heur = PlainHeurArrays c s.heur) :
    storeOk m i64 (c.hdr + BitVec.ofNat 64 (32 + 8 * i)) ∧
      (PlainMem c s' ⋆ R) (storeMem m i64 (c.hdr + BitVec.ofNat 64 (32 + 8 * i)) v) := by
  have h1 : (array64 (c.hdr + 32) (hdrTailWords c s) ⋆
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.d_cur s.d_val ⋆
        PlainCoreArrays c s ⋆ PlainHeurArrays c s.heur ⋆ c.pad ⋆ R)) m := by
    unfold PlainMem at hm; exact sep_ac hm
  obtain ⟨hok, hst⟩ := store_array64 (i := i) v (by simpa using hi) h1
  rw [show c.hdr + (32 : BitVec 64) + BitVec.ofNat 64 (8 * i) =
    c.hdr + BitVec.ofNat 64 (32 + 8 * i) from ptr_add_ofNat c.hdr 32 (8 * i)] at hok hst
  refine ⟨hok, ?_⟩
  rw [← heq] at hst; unfold PlainMem; rw [hd1, hd2, hca, hha]; exact sep_ac hst

@[c0_load] theorem load_arena_mv (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 c.hdr = some (BitVec.ofNat 64 c.mv) := load_dimacs_mv (focus_dimacs hm)
@[c0_load] theorem load_arena_nc (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 8) = some (BitVec.ofNat 64 c.nc) := load_dimacs_nc (focus_dimacs hm)
@[c0_load] theorem load_arena_cur (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 16) = some s.d_cur := load_dimacs_cur (focus_dimacs hm)
@[c0_load] theorem load_arena_val (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 24) = some s.d_val := load_dimacs_val (focus_dimacs hm)

@[c0_store] theorem store_arena_cur (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 16) ∧
      (PlainMem c { s with d_cur := v } ⋆ R) (storeMem m i64 (c.hdr + 16) v) := by
  obtain ⟨hok, hst⟩ := store_dimacs_cur v (focus_dimacs hm)
  exact ⟨hok, unfocus_dimacs hst⟩

@[c0_load] theorem load_arena_cap (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 32) = some (BitVec.ofNat 64 c.arena_cap) :=
  plainHdrTailGet 0 (by decide) hm
@[c0_load] theorem load_arena_wcap (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 40) = some (BitVec.ofNat 64 c.wcap) :=
  plainHdrTailGet 1 (by decide) hm
@[c0_load] theorem load_arena_len (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 48) = some (BitVec.ofNat 64 s.arena_len) :=
  plainHdrTailGet 2 (by decide) hm
@[c0_load] theorem load_arena_wlen (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 56) = some (BitVec.ofNat 64 s.wlen) :=
  plainHdrTailGet 3 (by decide) hm
@[c0_load] theorem load_arena_values (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 64) = some c.pVals := plainHdrTailGet 4 (by decide) hm
@[c0_load] theorem load_arena_mark (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 72) = some c.pMark := plainHdrTailGet 5 (by decide) hm
@[c0_load] theorem load_arena_level (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 80) = some c.pLevel := plainHdrTailGet 6 (by decide) hm
@[c0_load] theorem load_arena_reason (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 88) = some c.pReason := plainHdrTailGet 7 (by decide) hm
@[c0_load] theorem load_arena_trail (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 96) = some c.pTrail := plainHdrTailGet 8 (by decide) hm
@[c0_load] theorem load_arena_watch_vec (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 104) = some c.pWvec := plainHdrTailGet 9 (by decide) hm
@[c0_load] theorem load_arena_arena_ptr (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 112) = some c.pArena := plainHdrTailGet 10 (by decide) hm
@[c0_load] theorem load_arena_watch_stk (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 120) = some c.pWstk := plainHdrTailGet 11 (by decide) hm
@[c0_load] theorem load_arena_delayed (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 128) = some c.pDelayed := plainHdrTailGet 12 (by decide) hm
@[c0_load] theorem load_arena_tmp_lits (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 136) = some c.pTmp := plainHdrTailGet 13 (by decide) hm
@[c0_load] theorem load_arena_trail_end (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 144) = some (BitVec.ofNat 64 s.trail_end) :=
  plainHdrTailGet 14 (by decide) hm
@[c0_load] theorem load_arena_propagated (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 152) = some (BitVec.ofNat 64 s.propagated) :=
  plainHdrTailGet 15 (by decide) hm
@[c0_load] theorem load_arena_cur_level (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 160) = some (BitVec.ofNat 64 s.cur_level) :=
  plainHdrTailGet 16 (by decide) hm
@[c0_load] theorem load_arena_fuel (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 168) = some s.fuel := plainHdrTailGet 17 (by decide) hm
@[c0_load] theorem load_arena_confl_ref (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 176) = some s.confl_ref := plainHdrTailGet 18 (by decide) hm
@[c0_load] theorem load_arena_tmp_cnt (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 184) = some (BitVec.ofNat 64 s.tmp_cnt) :=
  plainHdrTailGet 19 (by decide) hm
@[c0_load] theorem load_arena_tmp_len (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 192) = some (BitVec.ofNat 64 s.tmp_len) :=
  plainHdrTailGet 20 (by decide) hm
@[c0_load] theorem load_arena_heap_ptr (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 200) = some c.pHeap := plainHdrTailGet 21 (by decide) hm
@[c0_load] theorem load_arena_pos_ptr (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 208) = some c.pPos := plainHdrTailGet 22 (by decide) hm
@[c0_load] theorem load_arena_score_ptr (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 216) = some c.pScore := plainHdrTailGet 23 (by decide) hm
@[c0_load] theorem load_arena_phases_ptr (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 224) = some c.pPhases := plainHdrTailGet 24 (by decide) hm
@[c0_load] theorem load_arena_min_stk_ptr (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 232) = some c.pMinStk := plainHdrTailGet 25 (by decide) hm
@[c0_load] theorem load_arena_min_clr_ptr (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 240) = some c.pMinClr := plainHdrTailGet 26 (by decide) hm
@[c0_load] theorem load_arena_heap_len (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 248) = some (BitVec.ofNat 64 s.heur.heap_len) :=
  plainHdrTailGet 27 (by decide) hm
@[c0_load] theorem load_arena_scinc (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 256) = some s.heur.scinc := plainHdrTailGet 28 (by decide) hm
@[c0_load] theorem load_arena_min_depth (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 264) = some (BitVec.ofNat 64 c.minDepth) :=
  plainHdrTailGet 29 (by decide) hm
@[c0_load] theorem load_arena_min_clr_len (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 272) = some (BitVec.ofNat 64 s.min_clr_len) :=
  plainHdrTailGet 30 (by decide) hm
@[c0_load] theorem load_arena_min_clr_full (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 280) = some s.min_clr_full := plainHdrTailGet 31 (by decide) hm
@[c0_load] theorem load_arena_rel_period (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 288) = some s.heur.rel_period :=
  plainHdrTailGet 32 (by decide) hm
@[c0_load] theorem load_arena_rel_limit (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 296) = some s.heur.rel_limit := plainHdrTailGet 33 (by decide) hm
@[c0_load] theorem load_arena_rel_wait (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 304) = some s.heur.rel_wait := plainHdrTailGet 34 (by decide) hm
@[c0_load] theorem load_arena_rel_u (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 312) = some s.heur.rel_u := plainHdrTailGet 35 (by decide) hm
@[c0_load] theorem load_arena_rel_v (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 320) = some s.heur.rel_v := plainHdrTailGet 36 (by decide) hm
@[c0_load] theorem load_arena_rel_trigger (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 328) = some s.heur.rel_trigger :=
  plainHdrTailGet 37 (by decide) hm
@[c0_load] theorem load_arena_conflicts (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 336) = some s.heur.conflicts := plainHdrTailGet 38 (by decide) hm
@[c0_load] theorem load_arena_learned_lits (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 344) = some s.heur.learned_lits :=
  plainHdrTailGet 39 (by decide) hm
@[c0_load] theorem load_arena_min_removed (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 352) = some s.heur.min_removed :=
  plainHdrTailGet 40 (by decide) hm

@[c0_store] theorem store_arena_len (v : Nat) (_hv : v < 2 ^ 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 48) ∧
      (PlainMem c { s with arena_len := v } ⋆ R)
        (storeMem m i64 (c.hdr + 48) (BitVec.ofNat 64 v)) :=
  plainHdrTailPut 2 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem c0_store_arena_len (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 48) ∧
      (PlainMem c { s with arena_len := v.toNat } ⋆ R) (storeMem m i64 (c.hdr + 48) v) := by
  simpa [bv_ofNat_toNat_eq] using store_arena_len v.toNat v.isLt hm
@[c0_store] theorem store_arena_wlen (v : Nat) (_hv : v < 2 ^ 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 56) ∧
      (PlainMem c { s with wlen := v } ⋆ R) (storeMem m i64 (c.hdr + 56) (BitVec.ofNat 64 v)) :=
  plainHdrTailPut 3 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem c0_store_arena_wlen (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 56) ∧
      (PlainMem c { s with wlen := v.toNat } ⋆ R) (storeMem m i64 (c.hdr + 56) v) := by
  simpa [bv_ofNat_toNat_eq] using store_arena_wlen v.toNat v.isLt hm
@[c0_store] theorem store_arena_trail_end (v : Nat) (_hv : v < 2 ^ 64)
    (hm : (PlainMem c s ⋆ R) m) : storeOk m i64 (c.hdr + 144) ∧
      (PlainMem c { s with trail_end := v } ⋆ R)
        (storeMem m i64 (c.hdr + 144) (BitVec.ofNat 64 v)) :=
  plainHdrTailPut 14 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem c0_store_arena_trail_end (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 144) ∧
      (PlainMem c { s with trail_end := v.toNat } ⋆ R) (storeMem m i64 (c.hdr + 144) v) := by
  simpa [bv_ofNat_toNat_eq] using store_arena_trail_end v.toNat v.isLt hm
@[c0_store] theorem store_arena_propagated (v : Nat) (_hv : v < 2 ^ 64)
    (hm : (PlainMem c s ⋆ R) m) : storeOk m i64 (c.hdr + 152) ∧
      (PlainMem c { s with propagated := v } ⋆ R)
        (storeMem m i64 (c.hdr + 152) (BitVec.ofNat 64 v)) :=
  plainHdrTailPut 15 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem c0_store_arena_propagated (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 152) ∧
      (PlainMem c { s with propagated := v.toNat } ⋆ R) (storeMem m i64 (c.hdr + 152) v) := by
  simpa [bv_ofNat_toNat_eq] using store_arena_propagated v.toNat v.isLt hm
@[c0_store] theorem store_arena_cur_level (v : Nat) (_hv : v < 2 ^ 64)
    (hm : (PlainMem c s ⋆ R) m) : storeOk m i64 (c.hdr + 160) ∧
      (PlainMem c { s with cur_level := v } ⋆ R)
        (storeMem m i64 (c.hdr + 160) (BitVec.ofNat 64 v)) :=
  plainHdrTailPut 16 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem c0_store_arena_cur_level (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 160) ∧
      (PlainMem c { s with cur_level := v.toNat } ⋆ R) (storeMem m i64 (c.hdr + 160) v) := by
  simpa [bv_ofNat_toNat_eq] using store_arena_cur_level v.toNat v.isLt hm
@[c0_store] theorem store_arena_fuel (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 168) ∧
      (PlainMem c { s with fuel := v } ⋆ R) (storeMem m i64 (c.hdr + 168) v) :=
  plainHdrTailPut 17 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_confl_ref (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 176) ∧
      (PlainMem c { s with confl_ref := v } ⋆ R) (storeMem m i64 (c.hdr + 176) v) :=
  plainHdrTailPut 18 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_tmp_cnt (v : Nat) (_hv : v < 2 ^ 64)
    (hm : (PlainMem c s ⋆ R) m) : storeOk m i64 (c.hdr + 184) ∧
      (PlainMem c { s with tmp_cnt := v } ⋆ R)
        (storeMem m i64 (c.hdr + 184) (BitVec.ofNat 64 v)) :=
  plainHdrTailPut 19 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem c0_store_arena_tmp_cnt (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 184) ∧
      (PlainMem c { s with tmp_cnt := v.toNat } ⋆ R) (storeMem m i64 (c.hdr + 184) v) := by
  simpa [bv_ofNat_toNat_eq] using store_arena_tmp_cnt v.toNat v.isLt hm
@[c0_store] theorem store_arena_tmp_len (v : Nat) (_hv : v < 2 ^ 64)
    (hm : (PlainMem c s ⋆ R) m) : storeOk m i64 (c.hdr + 192) ∧
      (PlainMem c { s with tmp_len := v } ⋆ R)
        (storeMem m i64 (c.hdr + 192) (BitVec.ofNat 64 v)) :=
  plainHdrTailPut 20 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem c0_store_arena_tmp_len (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 192) ∧
      (PlainMem c { s with tmp_len := v.toNat } ⋆ R) (storeMem m i64 (c.hdr + 192) v) := by
  simpa [bv_ofNat_toNat_eq] using store_arena_tmp_len v.toNat v.isLt hm
@[c0_store] theorem store_arena_heap_len (v : Nat) (_hv : v < 2 ^ 64)
    (hm : (PlainMem c s ⋆ R) m) : storeOk m i64 (c.hdr + 248) ∧
      (PlainMem c { s with heur := { s.heur with heap_len := v } } ⋆ R)
        (storeMem m i64 (c.hdr + 248) (BitVec.ofNat 64 v)) :=
  plainHdrTailPut 27 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem c0_store_arena_heap_len (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 248) ∧
      (PlainMem c { s with heur := { s.heur with heap_len := v.toNat } } ⋆ R)
        (storeMem m i64 (c.hdr + 248) v) := by
  simpa [bv_ofNat_toNat_eq] using store_arena_heap_len v.toNat v.isLt hm
@[c0_store] theorem store_arena_scinc (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 256) ∧
      (PlainMem c { s with heur := { s.heur with scinc := v } } ⋆ R)
        (storeMem m i64 (c.hdr + 256) v) :=
  plainHdrTailPut 28 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_min_clr_len (v : Nat) (_hv : v < 2 ^ 64)
    (hm : (PlainMem c s ⋆ R) m) : storeOk m i64 (c.hdr + 272) ∧
      (PlainMem c { s with min_clr_len := v } ⋆ R)
        (storeMem m i64 (c.hdr + 272) (BitVec.ofNat 64 v)) :=
  plainHdrTailPut 30 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem c0_store_arena_min_clr_len (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 272) ∧
      (PlainMem c { s with min_clr_len := v.toNat } ⋆ R) (storeMem m i64 (c.hdr + 272) v) := by
  simpa [bv_ofNat_toNat_eq] using store_arena_min_clr_len v.toNat v.isLt hm
@[c0_store] theorem store_arena_min_clr_full (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 280) ∧
      (PlainMem c { s with min_clr_full := v } ⋆ R) (storeMem m i64 (c.hdr + 280) v) :=
  plainHdrTailPut 31 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_rel_period (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 288) ∧
      (PlainMem c { s with heur := { s.heur with rel_period := v } } ⋆ R)
        (storeMem m i64 (c.hdr + 288) v) :=
  plainHdrTailPut 32 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_rel_limit (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 296) ∧
      (PlainMem c { s with heur := { s.heur with rel_limit := v } } ⋆ R)
        (storeMem m i64 (c.hdr + 296) v) :=
  plainHdrTailPut 33 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_rel_wait (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 304) ∧
      (PlainMem c { s with heur := { s.heur with rel_wait := v } } ⋆ R)
        (storeMem m i64 (c.hdr + 304) v) :=
  plainHdrTailPut 34 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_rel_u (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 312) ∧
      (PlainMem c { s with heur := { s.heur with rel_u := v } } ⋆ R)
        (storeMem m i64 (c.hdr + 312) v) :=
  plainHdrTailPut 35 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_rel_v (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 320) ∧
      (PlainMem c { s with heur := { s.heur with rel_v := v } } ⋆ R)
        (storeMem m i64 (c.hdr + 320) v) :=
  plainHdrTailPut 36 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_rel_trigger (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 328) ∧
      (PlainMem c { s with heur := { s.heur with rel_trigger := v } } ⋆ R)
        (storeMem m i64 (c.hdr + 328) v) :=
  plainHdrTailPut 37 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_conflicts (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 336) ∧
      (PlainMem c { s with heur := { s.heur with conflicts := v } } ⋆ R)
        (storeMem m i64 (c.hdr + 336) v) :=
  plainHdrTailPut 38 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_learned_lits (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 344) ∧
      (PlainMem c { s with heur := { s.heur with learned_lits := v } } ⋆ R)
        (storeMem m i64 (c.hdr + 344) v) :=
  plainHdrTailPut 39 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_min_removed (v : BitVec 64) (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 352) ∧
      (PlainMem c { s with heur := { s.heur with min_removed := v } } ⋆ R)
        (storeMem m i64 (c.hdr + 352) v) :=
  plainHdrTailPut 40 (by decide) _ _ hm rfl rfl rfl rfl rfl

end PlainAccess1

end LeanQbe.T.Examples.Kissat.Plain
