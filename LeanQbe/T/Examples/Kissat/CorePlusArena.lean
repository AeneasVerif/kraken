module

public import LeanQbe.T.Examples.Kissat.CorePlus
public import LeanQbe.T.Examples.Kissat.SolverArena
public import LeanQbe.T.Logic.C0StepAttr
public import Kraken.SeparationTactics
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `CorePlus` Arena Layout, State, and Separation-Logic Helpers (`Stage 2`)

Defines:
1. `CorePlusCfg` extending the `D-Min` `ArenaCfg` layout with `pHeap`, `pPos`, `pScore`,
   `pPhases`, `pMinStk`, `pMinClr`, and `minDepth` (`pMinDepth`), plus `regions_to_avail`.
2. `HeurState` (heuristic scalars & arrays, zero soundness invariants), `CorePlusState`, and
   `LengthsOk` bounds predicates.
3. `CorePlusMem`, `CorePlusArenaInv`, `CorePlusRest`, region collapse (`to_region`),
   `check_model` bridge (`corePlusMem_to_checkModel`), and direct load/store accessors.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.CorePlus

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

/-! ## 1. Arithmetic, alignment, and size helpers -/

def minDepthOf (mv : Nat) : Nat :=
  if mv + 1 < 1000 then mv + 1 else 1000

def phasesBytes (mv : Nat) : Nat := markBytes mv

def cpFixedBytes (mv : Nat) : Nat :=
  360 + valsBytes mv + 2 * markBytes mv + 7 * u32VarBytes mv + 8 * mv +
    whBytes mv + 8 * minDepthOf mv

theorem minDepthOf_pos (mv : Nat) : 1 ≤ minDepthOf mv := by
  unfold minDepthOf; split <;> omega

theorem minDepthOf_le (mv : Nat) : minDepthOf mv ≤ 1000 := by
  unfold minDepthOf; split <;> omega

theorem cpFixedBytes_lt {mv : Nat} (hmv : mv < dimacsBound) : cpFixedBytes mv < 2 ^ 34 := by
  unfold cpFixedBytes valsBytes markBytes u32VarBytes whBytes minDepthOf dimacsBound at *
  split <;> omega

theorem bv8_zext32_eq_zero (b : BitVec 8) : b.setWidth 32 = 0#32 ↔ b = 0#8 := by
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    have hb := b.isLt
    have ht := congrArg BitVec.toNat h
    simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ 32)] at ht
    exact ht
  · rintro rfl; rfl

theorem bv64_sub1_toNat {f : BitVec 64} (hf : f ≠ 0) : (f - 1).toNat = f.toNat - 1 := by
  have hpos : 0 < f.toNat := Nat.pos_of_ne_zero fun h0 =>
    hf (BitVec.eq_of_toNat_eq (by simpa using h0))
  have hsub := bv_sub_ofNat (a := f.toNat) (b := 1) (by omega) f.isLt
  rw [bv_ofNat_toNat_eq f] at hsub
  change (f - 1#64).toNat = f.toNat - 1
  rw [hsub, bv64_ofNat_toNat (by omega)]

theorem bv64_ugt_max_sub_false {p : BitVec 64} {n : Nat}
    (hfit : p.toNat + n < 2 ^ 64) :
    ((0xFFFFFFFFFFFFFFFF#64 - p).ult (BitVec.ofNat 64 n)) = false := by
  have hp := p.isLt
  have hmax : (0xFFFFFFFFFFFFFFFF#64 : BitVec 64).toNat = 2 ^ 64 - 1 := rfl
  have hsub : 0xFFFFFFFFFFFFFFFF#64 - p = BitVec.ofNat 64 (2 ^ 64 - 1 - p.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, hmax, bv64_ofNat_toNat (by omega)]
    omega
  rw [hsub, bv_ult_eq (by omega) (by omega)]
  simp only [decide_eq_false_iff_not]; omega

def alignPad (p : BitVec 64) : Nat :=
  if p.toNat % 8 = 0 then 0 else 8 - p.toNat % 8

theorem alignPad_lt8 (p : BitVec 64) : alignPad p < 8 := by
  unfold alignPad; split <;> omega

theorem bv64_sub_pad {w : Nat} {p : BitVec 64} (hle : alignPad p ≤ w) (hw : w < 2 ^ 64) :
    BitVec.ofNat 64 w - BitVec.ofNat 64 (alignPad p) = BitVec.ofNat 64 (w - alignPad p) :=
  bv_sub_ofNat hle hw

/-! ## 2. `CorePlusCfg` arena geometry -/

/-- Static arena geometry established by `kissat_init_state` in `CorePlus`. -/
structure CorePlusCfg where
  hdr : BitVec 64
  avail : Nat
  mv : Nat
  nc : Nat
  max_c : Nat
  lcap : Nat
  hmv : mv < dimacsBound
  hnc : nc < dimacsBound
  hmax_c : max_c < dimacsBound
  hlcap : lcap < dimacsBound
  havail_fit : hdr.toNat + avail < 2 ^ 64
  hsize : cpFixedBytes mv + 24 * max_c + 4 * lcap ≤ avail

namespace CorePlusCfg

def minDepth (c : CorePlusCfg) : Nat := minDepthOf c.mv
abbrev pMinDepth (c : CorePlusCfg) : Nat := c.minDepth

def pVals (c : CorePlusCfg) : BitVec 64 := c.hdr + BitVec.ofNat 64 360
def pMark (c : CorePlusCfg) : BitVec 64 := c.pVals + BitVec.ofNat 64 (valsBytes c.mv)
def pPhases (c : CorePlusCfg) : BitVec 64 := c.pMark + BitVec.ofNat 64 (markBytes c.mv)
def pLevel (c : CorePlusCfg) : BitVec 64 := c.pPhases + BitVec.ofNat 64 (markBytes c.mv)
def pReason (c : CorePlusCfg) : BitVec 64 := c.pLevel + BitVec.ofNat 64 (u32VarBytes c.mv)
def pTrail (c : CorePlusCfg) : BitVec 64 := c.pReason + BitVec.ofNat 64 (u32VarBytes c.mv)
def pTmp (c : CorePlusCfg) : BitVec 64 := c.pTrail + BitVec.ofNat 64 (u32VarBytes c.mv)
def pHeap (c : CorePlusCfg) : BitVec 64 := c.pTmp + BitVec.ofNat 64 (u32VarBytes c.mv)
def pPos (c : CorePlusCfg) : BitVec 64 := c.pHeap + BitVec.ofNat 64 (u32VarBytes c.mv)
def pMinClr (c : CorePlusCfg) : BitVec 64 := c.pPos + BitVec.ofNat 64 (u32VarBytes c.mv)
def pScore (c : CorePlusCfg) : BitVec 64 := c.pMinClr + BitVec.ofNat 64 (u32VarBytes c.mv)
def pWh (c : CorePlusCfg) : BitVec 64 := c.pScore + BitVec.ofNat 64 (8 * c.mv)
def pMinStk (c : CorePlusCfg) : BitVec 64 := c.pWh + BitVec.ofNat 64 (whBytes c.mv)
def pClauses (c : CorePlusCfg) : BitVec 64 := c.pMinStk + BitVec.ofNat 64 (8 * c.minDepth)
def pWn (c : CorePlusCfg) : BitVec 64 := c.pClauses + BitVec.ofNat 64 (16 * c.max_c)
def pLpool (c : CorePlusCfg) : BitVec 64 := c.pClauses + BitVec.ofNat 64 (24 * c.max_c)
def pSlack (c : CorePlusCfg) : BitVec 64 := c.pLpool + BitVec.ofNat 64 (4 * c.lcap)
def slack (c : CorePlusCfg) : Nat := c.avail - (cpFixedBytes c.mv + 24 * c.max_c + 4 * c.lcap)

/-- Combined alignment padding and trailing slack regions (untouched after `init_state`). -/
def pad (c : CorePlusCfg) : Mem 64 → Prop :=
  region (c.pVals + BitVec.ofNat 64 (2 * c.mv)) (valsBytes c.mv - 2 * c.mv) ⋆
  region (c.pMark + BitVec.ofNat 64 c.mv) (markBytes c.mv - c.mv) ⋆
  region (c.pPhases + BitVec.ofNat 64 c.mv) (markBytes c.mv - c.mv) ⋆
  region (c.pLevel + BitVec.ofNat 64 (4 * c.mv)) (u32VarBytes c.mv - 4 * c.mv) ⋆
  region (c.pReason + BitVec.ofNat 64 (4 * c.mv)) (u32VarBytes c.mv - 4 * c.mv) ⋆
  region (c.pTrail + BitVec.ofNat 64 (4 * c.mv)) (u32VarBytes c.mv - 4 * c.mv) ⋆
  region (c.pTmp + BitVec.ofNat 64 (4 * c.mv)) (u32VarBytes c.mv - 4 * c.mv) ⋆
  region (c.pHeap + BitVec.ofNat 64 (4 * c.mv)) (u32VarBytes c.mv - 4 * c.mv) ⋆
  region (c.pPos + BitVec.ofNat 64 (4 * c.mv)) (u32VarBytes c.mv - 4 * c.mv) ⋆
  region (c.pMinClr + BitVec.ofNat 64 (4 * c.mv)) (u32VarBytes c.mv - 4 * c.mv) ⋆
  region (c.pWh + BitVec.ofNat 64 (8 * c.mv)) (whBytes c.mv - 8 * c.mv) ⋆
  region c.pSlack c.slack

/-- Collapse all 18 active regions + static padding back into `region c.hdr c.avail`. -/
theorem regions_to_avail (c : CorePlusCfg) {m : Mem 64}
    (hm : (region c.hdr 32 ⋆ region (c.hdr + BitVec.ofNat 64 32) 328 ⋆
      region c.pVals (2 * c.mv) ⋆ region c.pMark c.mv ⋆ region c.pPhases c.mv ⋆
      region c.pLevel (4 * c.mv) ⋆ region c.pReason (4 * c.mv) ⋆
      region c.pTrail (4 * c.mv) ⋆ region c.pTmp (4 * c.mv) ⋆
      region c.pHeap (4 * c.mv) ⋆ region c.pPos (4 * c.mv) ⋆
      region c.pMinClr (4 * c.mv) ⋆ region c.pScore (8 * c.mv) ⋆
      region c.pWh (8 * c.mv) ⋆ region c.pMinStk (8 * c.minDepth) ⋆
      region c.pClauses (16 * c.max_c) ⋆ region c.pWn (8 * c.max_c) ⋆
      region c.pLpool (4 * c.lcap) ⋆ c.pad) m) : region c.hdr c.avail m := by
  have hfit := c.havail_fit
  have hsz := c.hsize
  have hv := valsBytes_ge c.mv; have hmk := markBytes_ge c.mv
  have hu := u32VarBytes_ge c.mv; have hw := whBytes_ge c.mv
  have hfx := cpFixedBytes_lt c.hmv
  unfold pad at hm
  have hm2 : ((region c.hdr 32 ⋆ region (c.hdr + BitVec.ofNat 64 32) 328) ⋆
      ((region c.pVals (2 * c.mv) ⋆
          region (c.pVals + BitVec.ofNat 64 (2 * c.mv)) (valsBytes c.mv - 2 * c.mv)) ⋆
      ((region c.pMark c.mv ⋆
          region (c.pMark + BitVec.ofNat 64 c.mv) (markBytes c.mv - c.mv)) ⋆
      ((region c.pPhases c.mv ⋆
          region (c.pPhases + BitVec.ofNat 64 c.mv) (markBytes c.mv - c.mv)) ⋆
      ((region c.pLevel (4 * c.mv) ⋆
          region (c.pLevel + BitVec.ofNat 64 (4 * c.mv)) (u32VarBytes c.mv - 4 * c.mv)) ⋆
      ((region c.pReason (4 * c.mv) ⋆
          region (c.pReason + BitVec.ofNat 64 (4 * c.mv)) (u32VarBytes c.mv - 4 * c.mv)) ⋆
      ((region c.pTrail (4 * c.mv) ⋆
          region (c.pTrail + BitVec.ofNat 64 (4 * c.mv)) (u32VarBytes c.mv - 4 * c.mv)) ⋆
      ((region c.pTmp (4 * c.mv) ⋆
          region (c.pTmp + BitVec.ofNat 64 (4 * c.mv)) (u32VarBytes c.mv - 4 * c.mv)) ⋆
      ((region c.pHeap (4 * c.mv) ⋆
          region (c.pHeap + BitVec.ofNat 64 (4 * c.mv)) (u32VarBytes c.mv - 4 * c.mv)) ⋆
      ((region c.pPos (4 * c.mv) ⋆
          region (c.pPos + BitVec.ofNat 64 (4 * c.mv)) (u32VarBytes c.mv - 4 * c.mv)) ⋆
      ((region c.pMinClr (4 * c.mv) ⋆
          region (c.pMinClr + BitVec.ofNat 64 (4 * c.mv)) (u32VarBytes c.mv - 4 * c.mv)) ⋆
      (region c.pScore (8 * c.mv) ⋆
      ((region c.pWh (8 * c.mv) ⋆
          region (c.pWh + BitVec.ofNat 64 (8 * c.mv)) (whBytes c.mv - 8 * c.mv)) ⋆
      (region c.pMinStk (8 * c.minDepth) ⋆
      ((region c.pClauses (16 * c.max_c) ⋆ region c.pWn (8 * c.max_c)) ⋆
      (region c.pLpool (4 * c.lcap) ⋆ region c.pSlack c.slack)))))))))))))))) m := sep_ac hm
  have hle : cpFixedBytes c.mv ≤ c.avail := by omega
  unfold cpFixedBytes at hsz hle
  simp only [minDepth] at hm2
  rw [
    region_merge_eq (a := c.hdr) (n1 := 32) (n2 := 328) (n := 360) rfl (by decide),
    region_merge_eq (a := c.pVals) (n1 := 2 * c.mv) (n2 := valsBytes c.mv - 2 * c.mv)
      (n := valsBytes c.mv) (by omega) (by omega),
    region_merge_eq (a := c.pMark) (n1 := c.mv) (n2 := markBytes c.mv - c.mv)
      (n := markBytes c.mv) (by omega) (by omega),
    region_merge_eq (a := c.pPhases) (n1 := c.mv) (n2 := markBytes c.mv - c.mv)
      (n := markBytes c.mv) (by omega) (by omega),
    region_merge_eq (a := c.pLevel) (n1 := 4 * c.mv) (n2 := u32VarBytes c.mv - 4 * c.mv)
      (n := u32VarBytes c.mv) (by omega) (by omega),
    region_merge_eq (a := c.pReason) (n1 := 4 * c.mv) (n2 := u32VarBytes c.mv - 4 * c.mv)
      (n := u32VarBytes c.mv) (by omega) (by omega),
    region_merge_eq (a := c.pTrail) (n1 := 4 * c.mv) (n2 := u32VarBytes c.mv - 4 * c.mv)
      (n := u32VarBytes c.mv) (by omega) (by omega),
    region_merge_eq (a := c.pTmp) (n1 := 4 * c.mv) (n2 := u32VarBytes c.mv - 4 * c.mv)
      (n := u32VarBytes c.mv) (by omega) (by omega),
    region_merge_eq (a := c.pHeap) (n1 := 4 * c.mv) (n2 := u32VarBytes c.mv - 4 * c.mv)
      (n := u32VarBytes c.mv) (by omega) (by omega),
    region_merge_eq (a := c.pPos) (n1 := 4 * c.mv) (n2 := u32VarBytes c.mv - 4 * c.mv)
      (n := u32VarBytes c.mv) (by omega) (by omega),
    region_merge_eq (a := c.pMinClr) (n1 := 4 * c.mv) (n2 := u32VarBytes c.mv - 4 * c.mv)
      (n := u32VarBytes c.mv) (by omega) (by omega),
    region_merge_eq (a := c.pWh) (n1 := 8 * c.mv) (n2 := whBytes c.mv - 8 * c.mv)
      (n := whBytes c.mv) (by omega) (by omega),
    show c.pWn = c.pClauses + BitVec.ofNat 64 (16 * c.max_c) from rfl,
    region_merge_eq (a := c.pClauses) (n1 := 16 * c.max_c) (n2 := 8 * c.max_c)
      (n := 24 * c.max_c) (by omega) (by omega),
    show c.pSlack = c.pLpool + BitVec.ofNat 64 (4 * c.lcap) from rfl,
    region_merge_eq (a := c.pLpool) (n1 := 4 * c.lcap) (n2 := c.slack)
      (n := 4 * c.lcap + c.slack) rfl (by unfold slack cpFixedBytes; omega),
    show c.pLpool = c.pClauses + BitVec.ofNat 64 (24 * c.max_c) from rfl,
    region_merge_eq (a := c.pClauses) (n1 := 24 * c.max_c) (n2 := 4 * c.lcap + c.slack)
      (n := 24 * c.max_c + (4 * c.lcap + c.slack)) rfl (by unfold slack cpFixedBytes; omega),
    show c.pClauses = c.pMinStk + BitVec.ofNat 64 (8 * minDepthOf c.mv) from rfl,
    region_merge_eq (a := c.pMinStk) (n1 := 8 * minDepthOf c.mv)
      (n2 := 24 * c.max_c + (4 * c.lcap + c.slack))
      (n := 8 * minDepthOf c.mv + (24 * c.max_c + (4 * c.lcap + c.slack))) rfl
      (by unfold slack cpFixedBytes; omega),
    show c.pMinStk = c.pWh + BitVec.ofNat 64 (whBytes c.mv) from rfl,
    region_merge_eq (a := c.pWh) (n1 := whBytes c.mv)
      (n := whBytes c.mv + (8 * minDepthOf c.mv + (24 * c.max_c + (4 * c.lcap + c.slack)))) rfl
      (by unfold slack cpFixedBytes; omega),
    show c.pWh = c.pScore + BitVec.ofNat 64 (8 * c.mv) from rfl,
    region_merge_eq (a := c.pScore) (n1 := 8 * c.mv)
      (n := 8 * c.mv + (whBytes c.mv + (8 * minDepthOf c.mv +
        (24 * c.max_c + (4 * c.lcap + c.slack))))) rfl
      (by unfold slack cpFixedBytes; omega),
    show c.pScore = c.pMinClr + BitVec.ofNat 64 (u32VarBytes c.mv) from rfl,
    region_merge_eq (a := c.pMinClr) (n1 := u32VarBytes c.mv)
      (n := u32VarBytes c.mv + (8 * c.mv + (whBytes c.mv + (8 * minDepthOf c.mv +
        (24 * c.max_c + (4 * c.lcap + c.slack)))))) rfl
      (by unfold slack cpFixedBytes; omega),
    show c.pMinClr = c.pPos + BitVec.ofNat 64 (u32VarBytes c.mv) from rfl,
    region_merge_eq (a := c.pPos) (n1 := u32VarBytes c.mv)
      (n := 2 * u32VarBytes c.mv + (8 * c.mv + (whBytes c.mv + (8 * minDepthOf c.mv +
        (24 * c.max_c + (4 * c.lcap + c.slack)))))) (by omega)
      (by unfold slack cpFixedBytes; omega),
    show c.pPos = c.pHeap + BitVec.ofNat 64 (u32VarBytes c.mv) from rfl,
    region_merge_eq (a := c.pHeap) (n1 := u32VarBytes c.mv)
      (n := 3 * u32VarBytes c.mv + (8 * c.mv + (whBytes c.mv + (8 * minDepthOf c.mv +
        (24 * c.max_c + (4 * c.lcap + c.slack)))))) (by omega)
      (by unfold slack cpFixedBytes; omega),
    show c.pHeap = c.pTmp + BitVec.ofNat 64 (u32VarBytes c.mv) from rfl,
    region_merge_eq (a := c.pTmp) (n1 := u32VarBytes c.mv)
      (n := 4 * u32VarBytes c.mv + (8 * c.mv + (whBytes c.mv + (8 * minDepthOf c.mv +
        (24 * c.max_c + (4 * c.lcap + c.slack)))))) (by omega)
      (by unfold slack cpFixedBytes; omega),
    show c.pTmp = c.pTrail + BitVec.ofNat 64 (u32VarBytes c.mv) from rfl,
    region_merge_eq (a := c.pTrail) (n1 := u32VarBytes c.mv)
      (n := 5 * u32VarBytes c.mv + (8 * c.mv + (whBytes c.mv + (8 * minDepthOf c.mv +
        (24 * c.max_c + (4 * c.lcap + c.slack)))))) (by omega)
      (by unfold slack cpFixedBytes; omega),
    show c.pTrail = c.pReason + BitVec.ofNat 64 (u32VarBytes c.mv) from rfl,
    region_merge_eq (a := c.pReason) (n1 := u32VarBytes c.mv)
      (n := 6 * u32VarBytes c.mv + (8 * c.mv + (whBytes c.mv + (8 * minDepthOf c.mv +
        (24 * c.max_c + (4 * c.lcap + c.slack)))))) (by omega)
      (by unfold slack cpFixedBytes; omega),
    show c.pReason = c.pLevel + BitVec.ofNat 64 (u32VarBytes c.mv) from rfl,
    region_merge_eq (a := c.pLevel) (n1 := u32VarBytes c.mv)
      (n := 7 * u32VarBytes c.mv + (8 * c.mv + (whBytes c.mv + (8 * minDepthOf c.mv +
        (24 * c.max_c + (4 * c.lcap + c.slack)))))) (by omega)
      (by unfold slack cpFixedBytes; omega),
    show c.pLevel = c.pPhases + BitVec.ofNat 64 (markBytes c.mv) from rfl,
    region_merge_eq (a := c.pPhases) (n1 := markBytes c.mv)
      (n := markBytes c.mv + (7 * u32VarBytes c.mv + (8 * c.mv + (whBytes c.mv +
        (8 * minDepthOf c.mv + (24 * c.max_c + (4 * c.lcap + c.slack))))))) rfl
      (by unfold slack cpFixedBytes; omega),
    show c.pPhases = c.pMark + BitVec.ofNat 64 (markBytes c.mv) from rfl,
    region_merge_eq (a := c.pMark) (n1 := markBytes c.mv)
      (n := 2 * markBytes c.mv + (7 * u32VarBytes c.mv + (8 * c.mv + (whBytes c.mv +
        (8 * minDepthOf c.mv + (24 * c.max_c + (4 * c.lcap + c.slack))))))) (by omega)
      (by unfold slack cpFixedBytes; omega),
    show c.pMark = c.pVals + BitVec.ofNat 64 (valsBytes c.mv) from rfl,
    region_merge_eq (a := c.pVals) (n1 := valsBytes c.mv)
      (n := valsBytes c.mv + (2 * markBytes c.mv + (7 * u32VarBytes c.mv + (8 * c.mv +
        (whBytes c.mv + (8 * minDepthOf c.mv + (24 * c.max_c + (4 * c.lcap + c.slack)))))))) rfl
      (by unfold slack cpFixedBytes; omega),
    show c.pVals = c.hdr + BitVec.ofNat 64 360 from rfl,
    region_merge_eq (a := c.hdr) (n1 := 360) (n := c.avail)
      (by unfold slack cpFixedBytes; omega) (by omega)] at hm2
  exact hm2

end CorePlusCfg

/-! ## 3. `HeurState`, `CorePlusState`, `LengthsOk`, and `CorePlusMem` -/

/-- Purely heuristic state (bounds-only in `LengthsOk`, zero soundness obligations). -/
structure HeurState where
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
  heap : List (BitVec 32)
  pos : List (BitVec 32)
  score : List (BitVec 64)
  phases : List (BitVec 8)

/-- Bounds-only consistency of `HeurState` against `CorePlusCfg`. -/
structure HeurState.LengthsOk (c : CorePlusCfg) (h : HeurState) : Prop where
  heap_len_arr : h.heap.length = c.mv
  pos_len : h.pos.length = c.mv
  score_len : h.score.length = c.mv
  phases_len : h.phases.length = c.mv
  heap_len_le : h.heap_len ≤ c.mv

/-- Dynamic logical state of `CorePlusHdr` + all 16 arena sub-arrays. -/
structure CorePlusState where
  d_cur : BitVec 64
  d_val : BitVec 64
  lit_len : Nat
  num_clauses : Nat
  trail_end : Nat
  propagated : Nat
  cur_level : Nat
  fuel : BitVec 64
  confl_cid : BitVec 64
  tmp_cnt : Nat
  tmp_len : Nat
  min_clr_len : Nat
  min_clr_full : BitVec 64
  vals : List (BitVec 8)
  mrk : List (BitVec 8)
  lvl : List (BitVec 32)
  rsns : List (BitVec 32)
  trl : List (BitVec 32)
  tmp : List (BitVec 32)
  wh : List (BitVec 32)
  cls : List (BitVec 32)
  wn : List (BitVec 32)
  lpool : List (BitVec 32)
  min_stk : List (BitVec 32)
  min_clr : List (BitVec 32)
  heur : HeurState

/-- Array-length and scalar-bound consistency of `CorePlusState` against `CorePlusCfg`. -/
structure CorePlusState.LengthsOk (c : CorePlusCfg) (s : CorePlusState) : Prop where
  vals_len : s.vals.length = 2 * c.mv
  mrk_len : s.mrk.length = c.mv
  lvl_len : s.lvl.length = c.mv
  rsns_len : s.rsns.length = c.mv
  trl_len : s.trl.length = c.mv
  tmp_len_arr : s.tmp.length = c.mv
  wh_len : s.wh.length = 2 * c.mv
  cls_len : s.cls.length = 4 * c.max_c
  wn_len : s.wn.length = 2 * c.max_c
  lpool_len : s.lpool.length = c.lcap
  min_stk_len : s.min_stk.length = 2 * c.minDepth
  min_clr_len_arr : s.min_clr.length = c.mv
  lit_len_le : s.lit_len ≤ c.lcap
  num_clauses_le : s.num_clauses ≤ c.max_c
  trail_end_le : s.trail_end ≤ c.mv
  propagated_le : s.propagated ≤ s.trail_end
  cur_level_lt : s.cur_level < 2 ^ 32
  tmp_cnt_lt : s.tmp_cnt < 2 ^ 64
  tmp_len_lt : s.tmp_len < 2 ^ 64
  min_clr_len_le : s.min_clr_len ≤ c.mv
  heur_ok : s.heur.LengthsOk c

/-- The 41 `u64` words of `CorePlusHdr` after `KissatDimacs d` (offsets `32 .. 352`). -/
def hdrTailWords (c : CorePlusCfg) (s : CorePlusState) : List (BitVec 64) :=
  [ BitVec.ofNat 64 c.max_c,
    BitVec.ofNat 64 c.lcap,
    BitVec.ofNat 64 s.lit_len,
    BitVec.ofNat 64 s.num_clauses,
    c.pVals, c.pMark, c.pLevel, c.pReason, c.pTrail,
    c.pWh, c.pClauses, c.pWn, c.pLpool, c.pTmp,
    BitVec.ofNat 64 s.trail_end,
    BitVec.ofNat 64 s.propagated,
    BitVec.ofNat 64 s.cur_level,
    s.fuel,
    s.confl_cid,
    BitVec.ofNat 64 s.tmp_cnt,
    BitVec.ofNat 64 s.tmp_len,
    c.pHeap, c.pPos, c.pScore, c.pPhases, c.pMinStk, c.pMinClr,
    BitVec.ofNat 64 s.heur.heap_len,
    s.heur.scinc,
    BitVec.ofNat 64 c.minDepth,
    BitVec.ofNat 64 s.min_clr_len,
    s.min_clr_full,
    s.heur.rel_period,
    s.heur.rel_limit,
    s.heur.rel_wait,
    s.heur.rel_u,
    s.heur.rel_v,
    s.heur.rel_trigger,
    s.heur.conflicts,
    s.heur.learned_lits,
    s.heur.min_removed ]

@[simp] theorem hdrTailWords_length (c : CorePlusCfg) (s : CorePlusState) :
    (hdrTailWords c s).length = 41 := rfl

/-- Core and minimization arrays in `CorePlusMem`. -/
def CoreArrays (c : CorePlusCfg) (s : CorePlusState) : Mem 64 → Prop :=
  array (t := i8) c.pVals s.vals ⋆
  array (t := i8) c.pMark s.mrk ⋆
  array (t := i32) c.pLevel s.lvl ⋆
  array (t := i32) c.pReason s.rsns ⋆
  array (t := i32) c.pTrail s.trl ⋆
  array (t := i32) c.pTmp s.tmp ⋆
  array (t := i32) c.pWh s.wh ⋆
  array (t := i32) c.pClauses s.cls ⋆
  array (t := i32) c.pWn s.wn ⋆
  array (t := i32) c.pLpool s.lpool ⋆
  array (t := i32) c.pMinStk s.min_stk ⋆
  array (t := i32) c.pMinClr s.min_clr

/-- Purely heuristic arrays in `CorePlusMem` (isolated from core soundness proofs). -/
def HeurArrays (c : CorePlusCfg) (h : HeurState) : Mem 64 → Prop :=
  array (t := i32) c.pHeap h.heap ⋆
  array (t := i32) c.pPos h.pos ⋆
  array64 c.pScore h.score ⋆
  array (t := i8) c.pPhases h.phases

/-- Spatial separation predicate for the entire partitioned `CorePlus` arena at `c.hdr`. -/
def CorePlusMem (c : CorePlusCfg) (s : CorePlusState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.d_cur s.d_val ⋆
  array64 (c.hdr + 32) (hdrTailWords c s) ⋆
  CoreArrays c s ⋆
  HeurArrays c s.heur ⋆
  c.pad

/-- Combined arena invariant (`LengthsOk` + `CorePlusMem`). -/
def CorePlusArenaInv (c : CorePlusCfg) (s : CorePlusState) : Mem 64 → Prop := fun m =>
  s.LengthsOk c ∧ CorePlusMem c s m

/-- Rest of `CorePlusMem` after factoring out `dimacsState c.hdr ...`. -/
def CorePlusRest (c : CorePlusCfg) (s : CorePlusState) : Mem 64 → Prop :=
  array64 (c.hdr + 32) (hdrTailWords c s) ⋆ CoreArrays c s ⋆ HeurArrays c s.heur ⋆ c.pad

theorem corePlusMem_eq_dimacs_sep (c : CorePlusCfg) (s : CorePlusState) :
    CorePlusMem c s =
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.d_cur s.d_val ⋆
        CorePlusRest c s) := by
  unfold CorePlusMem CorePlusRest; ac_rfl

theorem corePlusRest_d_irrel (c : CorePlusCfg) (s : CorePlusState) (cur' val' : BitVec 64) :
    CorePlusRest c { s with d_cur := cur', d_val := val' } = CorePlusRest c s := rfl

private theorem arr_i8_reg {a : BitVec 64} {xs : List (BitVec 8)} {n : Nat}
    (hn : xs.length = n) (hbd : n ≤ 2 ^ 64) {f : Mem 64} (hf : array (t := i8) a xs f) :
    region a n f := by
  simpa [Ty.bytes, Ty.size, i8, hn] using
    array_to_region (t := i8) (by simp [Ty.bytes, Ty.size, i8, hn, hbd]) hf

private theorem arr_i32_reg {a : BitVec 64} {xs : List (BitVec 32)} {n m : Nat}
    (hn : xs.length = n) (hm : 4 * n = m) (hbd : m ≤ 2 ^ 64) {f : Mem 64}
    (hf : array (t := i32) a xs f) : region a m f := by
  simpa [Ty.bytes, Ty.size, i32, hn, hm] using
    array_to_region (t := i32) (by simp [Ty.bytes, Ty.size, i32, hn]; omega) hf

private theorem arr64_reg {a : BitVec 64} {xs : List (BitVec 64)} {n m : Nat}
    (hn : xs.length = n) (hm : 8 * n = m) (hbd : m ≤ 2 ^ 64) {f : Mem 64}
    (hf : array64 a xs f) : region a m f := by
  simpa [Ty.bytes, Ty.size, i64, hn, hm] using
    array_to_region (t := i64) (xs := xs) (by simp [Ty.bytes, Ty.size, i64, hn]; omega)
      ((array64_eq_array a xs) ▸ hf)

private theorem coreArrays_to_regions {c : CorePlusCfg} {s : CorePlusState} (hlen : s.LengthsOk c)
    {f : Mem 64} (hf : CoreArrays c s f) :
    (region c.pVals (2 * c.mv) ⋆ region c.pMark c.mv ⋆
      region c.pLevel (4 * c.mv) ⋆ region c.pReason (4 * c.mv) ⋆
      region c.pTrail (4 * c.mv) ⋆ region c.pTmp (4 * c.mv) ⋆
      region c.pWh (8 * c.mv) ⋆ region c.pClauses (16 * c.max_c) ⋆
      region c.pWn (8 * c.max_c) ⋆ region c.pLpool (4 * c.lcap) ⋆
      region c.pMinStk (8 * c.minDepth) ⋆ region c.pMinClr (4 * c.mv)) f := by
  have hmv := c.hmv; have hmc := c.hmax_c; have hlc := c.hlcap
  have hmd := minDepthOf_le c.mv
  unfold dimacsBound at hmv hmc hlc
  unfold CorePlusCfg.minDepth at *; unfold CoreArrays at hf
  refine sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2
    (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2
      (fun _ => arr_i8_reg hlen.vals_len (by omega))
      (fun _ => arr_i8_reg hlen.mrk_len (by omega)))
      (fun _ => arr_i32_reg hlen.lvl_len rfl (by omega)))
      (fun _ => arr_i32_reg hlen.rsns_len rfl (by omega)))
      (fun _ => arr_i32_reg hlen.trl_len rfl (by omega)))
      (fun _ => arr_i32_reg hlen.tmp_len_arr rfl (by omega)))
      (fun _ => arr_i32_reg hlen.wh_len (by omega) (by omega)))
      (fun _ => arr_i32_reg hlen.cls_len (by omega) (by omega)))
      (fun _ => arr_i32_reg hlen.wn_len (by omega) (by omega)))
      (fun _ => arr_i32_reg hlen.lpool_len rfl (by omega)))
      (fun _ => arr_i32_reg hlen.min_stk_len
        (by unfold CorePlusCfg.minDepth; omega) (by omega)))
      (fun _ => arr_i32_reg hlen.min_clr_len_arr rfl (by omega)) f hf

private theorem heurArrays_to_regions {c : CorePlusCfg} {h : HeurState} (hok : h.LengthsOk c)
    {f : Mem 64} (hf : HeurArrays c h f) :
    (region c.pHeap (4 * c.mv) ⋆ region c.pPos (4 * c.mv) ⋆
      region c.pScore (8 * c.mv) ⋆ region c.pPhases c.mv) f := by
  have hmv := c.hmv; unfold dimacsBound at hmv
  unfold HeurArrays at hf
  refine sep_mono2 (sep_mono2 (sep_mono2
    (fun _ => arr_i32_reg hok.heap_len_arr rfl (by omega))
    (fun _ => arr_i32_reg hok.pos_len rfl (by omega)))
    (fun _ => arr64_reg hok.score_len rfl (by omega)))
    (fun _ => arr_i8_reg hok.phases_len (by omega)) f hf

/-- Collapse `CorePlusMem` (with arbitrary `dimacsState` prefix, e.g. after `kissat_check_model`)
back into `region c.hdr c.avail`. -/
theorem corePlusMem_anyDimacs_to_region {c : CorePlusCfg} {s : CorePlusState}
    {mv' nc' cur' val' : BitVec 64} {m : Mem 64} (hlen : s.LengthsOk c)
    (hm : (dimacsState c.hdr mv' nc' cur' val' ⋆
      array64 (c.hdr + 32) (hdrTailWords c s) ⋆
      CoreArrays c s ⋆ HeurArrays c s.heur ⋆ c.pad) m) : region c.hdr c.avail m := by
  refine c.regions_to_avail ?_
  have hm1 : ((dimacsState c.hdr mv' nc' cur' val' ⋆ array64 (c.hdr + 32) (hdrTailWords c s)) ⋆
      ((CoreArrays c s ⋆ HeurArrays c s.heur) ⋆ c.pad)) m := sep_ac hm
  have hm2 : ((region c.hdr 32 ⋆ region (c.hdr + BitVec.ofNat 64 32) 328) ⋆
      (((region c.pVals (2 * c.mv) ⋆ region c.pMark c.mv ⋆
        region c.pLevel (4 * c.mv) ⋆ region c.pReason (4 * c.mv) ⋆
        region c.pTrail (4 * c.mv) ⋆ region c.pTmp (4 * c.mv) ⋆
        region c.pWh (8 * c.mv) ⋆ region c.pClauses (16 * c.max_c) ⋆
        region c.pWn (8 * c.max_c) ⋆ region c.pLpool (4 * c.lcap) ⋆
        region c.pMinStk (8 * c.minDepth) ⋆ region c.pMinClr (4 * c.mv)) ⋆
      (region c.pHeap (4 * c.mv) ⋆ region c.pPos (4 * c.mv) ⋆
        region c.pScore (8 * c.mv) ⋆ region c.pPhases c.mv)) ⋆ c.pad)) m :=
    sep_mono2
      (sep_mono2 (fun _ h => dimacsState_to_region h)
        (fun _ => arr64_reg (hdrTailWords_length c s) rfl (by omega)))
      (sep_mono2 (sep_mono2 (fun _ => coreArrays_to_regions hlen)
        (fun _ => heurArrays_to_regions hlen.heur_ok)) (fun _ h => h)) m hm1
  exact sep_ac hm2

theorem CorePlusArenaInv.to_region {c : CorePlusCfg} {s : CorePlusState} {m : Mem 64}
    (h : CorePlusArenaInv c s m) : region c.hdr c.avail m :=
  corePlusMem_anyDimacs_to_region h.1 h.2

/-- Non-`vals` remainder of `CorePlusMem` for `kissat_check_model` framing. -/
def CorePlusCheckRest (c : CorePlusCfg) (s : CorePlusState) : Mem 64 → Prop :=
  array64 (c.hdr + 32) (hdrTailWords c s) ⋆
  array (t := i8) c.pMark s.mrk ⋆ array (t := i32) c.pLevel s.lvl ⋆
  array (t := i32) c.pReason s.rsns ⋆ array (t := i32) c.pTrail s.trl ⋆
  array (t := i32) c.pTmp s.tmp ⋆ array (t := i32) c.pWh s.wh ⋆
  array (t := i32) c.pClauses s.cls ⋆ array (t := i32) c.pWn s.wn ⋆
  array (t := i32) c.pLpool s.lpool ⋆ array (t := i32) c.pMinStk s.min_stk ⋆
  array (t := i32) c.pMinClr s.min_clr ⋆ HeurArrays c s.heur ⋆ c.pad

theorem corePlusMem_to_checkModel {c : CorePlusCfg} {s : CorePlusState}
    {cnf_ptr : BitVec 64} {cnfBytes : List UInt8} {R : Mem 64 → Prop} {m : Mem 64}
    (hlen : s.LengthsOk c) (hm : (bytes cnf_ptr cnfBytes ⋆ CorePlusMem c s ⋆ R) m) :
    (bytes cnf_ptr cnfBytes ⋆
      dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.d_cur s.d_val ⋆
      bytes c.pVals (s.vals.map UInt8.ofBitVec) ⋆
      (CorePlusCheckRest c s ⋆ R)) m := by
  have hmv := c.hmv; unfold dimacsBound at hmv
  have hm1 : (array (t := i8) c.pVals s.vals ⋆
      (bytes cnf_ptr cnfBytes ⋆
        dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.d_cur s.d_val ⋆
        (CorePlusCheckRest c s ⋆ R))) m := by
    unfold CorePlusMem CoreArrays at hm
    unfold CorePlusCheckRest
    exact sep_ac hm
  have hm2 : (bytes c.pVals (s.vals.map UInt8.ofBitVec) ⋆
      (bytes cnf_ptr cnfBytes ⋆
        dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.d_cur s.d_val ⋆
        (CorePlusCheckRest c s ⋆ R))) m := by
    refine sep_mono (fun f hf => ?_) hm1
    have hbytes := array_eq_bytesOf (t := i8) c.pVals s.vals
      (by simp [Ty.bytes, Ty.size, i8, hlen.vals_len]; omega) hf
    rw [bytesOf_i8_eq_map] at hbytes; exact hbytes.symm
  exact sep_ac hm2

theorem checkModel_post_to_region {c : CorePlusCfg} {s : CorePlusState}
    {mv' nc' cur' val' : BitVec 64} {cnf_ptr : BitVec 64} {cnfBytes : List UInt8}
    {R : Mem 64 → Prop} {m : Mem 64} (hlen : s.LengthsOk c)
    (hm : (bytes cnf_ptr cnfBytes ⋆ dimacsState c.hdr mv' nc' cur' val' ⋆
      bytes c.pVals (s.vals.map UInt8.ofBitVec) ⋆ (CorePlusCheckRest c s ⋆ R)) m) :
    (bytes cnf_ptr cnfBytes ⋆ region c.hdr c.avail ⋆ R) m := by
  have hmv := c.hmv; have hmc := c.hmax_c; have hlc := c.hlcap
  unfold dimacsBound at hmv hmc hlc
  unfold CorePlusCheckRest at hm
  have hm1 : (((dimacsState c.hdr mv' nc' cur' val' ⋆ array64 (c.hdr + 32) (hdrTailWords c s)) ⋆
      (((bytes c.pVals (s.vals.map UInt8.ofBitVec) ⋆ array (t := i8) c.pMark s.mrk ⋆
        array (t := i32) c.pLevel s.lvl ⋆ array (t := i32) c.pReason s.rsns ⋆
        array (t := i32) c.pTrail s.trl ⋆ array (t := i32) c.pTmp s.tmp ⋆
        array (t := i32) c.pWh s.wh ⋆ array (t := i32) c.pClauses s.cls ⋆
        array (t := i32) c.pWn s.wn ⋆ array (t := i32) c.pLpool s.lpool ⋆
        array (t := i32) c.pMinStk s.min_stk ⋆ array (t := i32) c.pMinClr s.min_clr) ⋆
        HeurArrays c s.heur) ⋆ c.pad)) ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m := sep_ac hm
  have hm2 : (region c.hdr c.avail ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m := by
    have hmd := minDepthOf_le c.mv
    unfold CorePlusCfg.minDepth at *
    refine sep_mono (fun f hf => c.regions_to_avail ?_) hm1
    have hf' : ((region c.hdr 32 ⋆ region (c.hdr + BitVec.ofNat 64 32) 328) ⋆
        (((region c.pVals (2 * c.mv) ⋆ region c.pMark c.mv ⋆
          region c.pLevel (4 * c.mv) ⋆ region c.pReason (4 * c.mv) ⋆
          region c.pTrail (4 * c.mv) ⋆ region c.pTmp (4 * c.mv) ⋆
          region c.pWh (8 * c.mv) ⋆ region c.pClauses (16 * c.max_c) ⋆
          region c.pWn (8 * c.max_c) ⋆ region c.pLpool (4 * c.lcap) ⋆
          region c.pMinStk (8 * c.minDepth) ⋆ region c.pMinClr (4 * c.mv)) ⋆
        (region c.pHeap (4 * c.mv) ⋆ region c.pPos (4 * c.mv) ⋆
          region c.pScore (8 * c.mv) ⋆ region c.pPhases c.mv)) ⋆ c.pad)) f := by
      refine sep_mono2
        (sep_mono2 (fun _ h => dimacsState_to_region h)
          (fun _ => arr64_reg (hdrTailWords_length c s) rfl (by omega)))
        (sep_mono2 (sep_mono2
          (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2
            (sep_mono2 (sep_mono2 (sep_mono2
              (fun f' (h : bytes c.pVals (s.vals.map UInt8.ofBitVec) f') => by
                have h' := bytes_to_region h; simpa [hlen.vals_len] using h')
              (fun _ => arr_i8_reg hlen.mrk_len (by omega)))
              (fun _ => arr_i32_reg hlen.lvl_len rfl (by omega)))
              (fun _ => arr_i32_reg hlen.rsns_len rfl (by omega)))
              (fun _ => arr_i32_reg hlen.trl_len rfl (by omega)))
              (fun _ => arr_i32_reg hlen.tmp_len_arr rfl (by omega)))
              (fun _ => arr_i32_reg hlen.wh_len (by omega) (by omega)))
              (fun _ => arr_i32_reg hlen.cls_len (by omega) (by omega)))
              (fun _ => arr_i32_reg hlen.wn_len (by omega) (by omega)))
              (fun _ => arr_i32_reg hlen.lpool_len rfl (by omega)))
              (fun _ => arr_i32_reg hlen.min_stk_len
                (by unfold CorePlusCfg.minDepth; omega)
                (by unfold CorePlusCfg.minDepth; omega)))
              (fun _ => arr_i32_reg hlen.min_clr_len_arr rfl (by omega)))
            (fun _ h => heurArrays_to_regions hlen.heur_ok h)) (fun _ h => h)) f hf
    exact sep_ac hf'
  exact sep_ac hm2

/-! ## 4. Direct `CorePlusMem` load / store / framing helpers -/

section CorePlusAccess
variable {c : CorePlusCfg} {s : CorePlusState} {R : Mem 64 → Prop} {m : Mem 64}

private theorem focus_dimacs (hm : (CorePlusMem c s ⋆ R) m) :
    (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.d_cur s.d_val ⋆
      (CorePlusRest c s ⋆ R)) m := by
  rw [corePlusMem_eq_dimacs_sep, sep_assoc] at hm; exact hm

private theorem unfocus_dimacs {cur' val' : BitVec 64} {m' : Mem 64}
    (hm : (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) cur' val' ⋆
      (CorePlusRest c s ⋆ R)) m') :
    (CorePlusMem c { s with d_cur := cur', d_val := val' } ⋆ R) m' := by
  rw [corePlusMem_eq_dimacs_sep, corePlusRest_d_irrel, sep_assoc]; exact hm

private theorem load_hdr_tail (i : Nat) (hi : i < 41) (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + BitVec.ofNat 64 (32 + 8 * i)) =
      some ((hdrTailWords c s)[i]'(by simpa using hi)) := by
  have h1 : (array64 (c.hdr + 32) (hdrTailWords c s) ⋆
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.d_cur s.d_val ⋆
        CoreArrays c s ⋆ HeurArrays c s.heur ⋆ c.pad ⋆ R)) m := by
    unfold CorePlusMem at hm; exact sep_ac hm
  have hload := loadVal_array64 (i := i) (by simpa using hi) h1
  rwa [show c.hdr + (32 : BitVec 64) + BitVec.ofNat 64 (8 * i) =
    c.hdr + BitVec.ofNat 64 (32 + 8 * i) from ptr_add_ofNat c.hdr 32 (8 * i)] at hload

private theorem store_hdr_tail (i : Nat) (hi : i < 41) (v : BitVec 64) (s' : CorePlusState)
    (hm : (CorePlusMem c s ⋆ R) m)
    (heq : hdrTailWords c s' = (hdrTailWords c s).set i v)
    (hd1 : s'.d_cur = s.d_cur) (hd2 : s'.d_val = s.d_val)
    (hca : CoreArrays c s' = CoreArrays c s) (hha : HeurArrays c s'.heur = HeurArrays c s.heur) :
    storeOk m i64 (c.hdr + BitVec.ofNat 64 (32 + 8 * i)) ∧
      (CorePlusMem c s' ⋆ R) (storeMem m i64 (c.hdr + BitVec.ofNat 64 (32 + 8 * i)) v) := by
  have h1 : (array64 (c.hdr + 32) (hdrTailWords c s) ⋆
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.d_cur s.d_val ⋆
        CoreArrays c s ⋆ HeurArrays c s.heur ⋆ c.pad ⋆ R)) m := by
    unfold CorePlusMem at hm; exact sep_ac hm
  obtain ⟨hok, hst⟩ := store_array64 (i := i) v (by simpa using hi) h1
  rw [show c.hdr + (32 : BitVec 64) + BitVec.ofNat 64 (8 * i) =
    c.hdr + BitVec.ofNat 64 (32 + 8 * i) from ptr_add_ofNat c.hdr 32 (8 * i)] at hok hst
  refine ⟨hok, ?_⟩
  rw [← heq] at hst
  unfold CorePlusMem
  rw [hd1, hd2, hca, hha]
  exact sep_ac hst

@[c0_load] theorem load_arena_mv (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i64 c.hdr = some (BitVec.ofNat 64 c.mv) := load_dimacs_mv (focus_dimacs hm)
@[c0_load] theorem load_arena_nc (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 8) = some (BitVec.ofNat 64 c.nc) := load_dimacs_nc (focus_dimacs hm)
@[c0_load] theorem load_arena_cur (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 16) = some s.d_cur := load_dimacs_cur (focus_dimacs hm)
@[c0_load] theorem load_arena_val (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 24) = some s.d_val := load_dimacs_val (focus_dimacs hm)

@[c0_store] theorem store_arena_cur (v : BitVec 64) (hm : (CorePlusMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 16) ∧
      (CorePlusMem c { s with d_cur := v } ⋆ R) (storeMem m i64 (c.hdr + 16) v) := by
  obtain ⟨hok, hst⟩ := store_dimacs_cur v (focus_dimacs hm)
  exact ⟨hok, unfocus_dimacs hst⟩

@[c0_load] theorem load_arena_max_clauses (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 32) = some (BitVec.ofNat 64 c.max_c) := load_hdr_tail 0 (by decide) hm
@[c0_load] theorem load_arena_lit_cap (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 40) = some (BitVec.ofNat 64 c.lcap) := load_hdr_tail 1 (by decide) hm
@[c0_load] theorem load_arena_lit_len (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 48) = some (BitVec.ofNat 64 s.lit_len) :=
  load_hdr_tail 2 (by decide) hm
@[c0_load] theorem load_arena_num_clauses (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 56) = some (BitVec.ofNat 64 s.num_clauses) :=
  load_hdr_tail 3 (by decide) hm
@[c0_load] theorem load_arena_values (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 64) = some c.pVals := load_hdr_tail 4 (by decide) hm
@[c0_load] theorem load_arena_mark (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 72) = some c.pMark := load_hdr_tail 5 (by decide) hm
@[c0_load] theorem load_arena_level (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 80) = some c.pLevel := load_hdr_tail 6 (by decide) hm
@[c0_load] theorem load_arena_reason (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 88) = some c.pReason := load_hdr_tail 7 (by decide) hm
@[c0_load] theorem load_arena_trail (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 96) = some c.pTrail := load_hdr_tail 8 (by decide) hm
@[c0_load] theorem load_arena_watch_head (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 104) = some c.pWh := load_hdr_tail 9 (by decide) hm
@[c0_load] theorem load_arena_clauses (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 112) = some c.pClauses := load_hdr_tail 10 (by decide) hm
@[c0_load] theorem load_arena_watch_next (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 120) = some c.pWn := load_hdr_tail 11 (by decide) hm
@[c0_load] theorem load_arena_lit_pool (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 128) = some c.pLpool := load_hdr_tail 12 (by decide) hm
@[c0_load] theorem load_arena_tmp_lits (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 136) = some c.pTmp := load_hdr_tail 13 (by decide) hm
@[c0_load] theorem load_arena_trail_end (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 144) = some (BitVec.ofNat 64 s.trail_end) :=
  load_hdr_tail 14 (by decide) hm
@[c0_load] theorem load_arena_propagated (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 152) = some (BitVec.ofNat 64 s.propagated) :=
  load_hdr_tail 15 (by decide) hm
@[c0_load] theorem load_arena_cur_level (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 160) = some (BitVec.ofNat 64 s.cur_level) :=
  load_hdr_tail 16 (by decide) hm
@[c0_load] theorem load_arena_fuel (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 168) = some s.fuel := load_hdr_tail 17 (by decide) hm
@[c0_load] theorem load_arena_confl_cid (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 176) = some s.confl_cid := load_hdr_tail 18 (by decide) hm
@[c0_load] theorem load_arena_tmp_cnt (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 184) = some (BitVec.ofNat 64 s.tmp_cnt) :=
  load_hdr_tail 19 (by decide) hm
@[c0_load] theorem load_arena_tmp_len (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 192) = some (BitVec.ofNat 64 s.tmp_len) :=
  load_hdr_tail 20 (by decide) hm
@[c0_load] theorem load_arena_heap_ptr (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 200) = some c.pHeap := load_hdr_tail 21 (by decide) hm
@[c0_load] theorem load_arena_pos_ptr (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 208) = some c.pPos := load_hdr_tail 22 (by decide) hm
@[c0_load] theorem load_arena_score_ptr (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 216) = some c.pScore := load_hdr_tail 23 (by decide) hm
@[c0_load] theorem load_arena_phases_ptr (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 224) = some c.pPhases := load_hdr_tail 24 (by decide) hm
@[c0_load] theorem load_arena_min_stk_ptr (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 232) = some c.pMinStk := load_hdr_tail 25 (by decide) hm
@[c0_load] theorem load_arena_min_clr_ptr (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 240) = some c.pMinClr := load_hdr_tail 26 (by decide) hm
@[c0_load] theorem load_arena_heap_len (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 248) = some (BitVec.ofNat 64 s.heur.heap_len) :=
  load_hdr_tail 27 (by decide) hm
@[c0_load] theorem load_arena_scinc (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 256) = some s.heur.scinc := load_hdr_tail 28 (by decide) hm
@[c0_load] theorem load_arena_min_depth (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 264) = some (BitVec.ofNat 64 c.minDepth) :=
  load_hdr_tail 29 (by decide) hm
@[c0_load] theorem load_arena_min_clr_len (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 272) = some (BitVec.ofNat 64 s.min_clr_len) :=
  load_hdr_tail 30 (by decide) hm
@[c0_load] theorem load_arena_min_clr_full (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 280) = some s.min_clr_full := load_hdr_tail 31 (by decide) hm
@[c0_load] theorem load_arena_rel_period (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 288) = some s.heur.rel_period := load_hdr_tail 32 (by decide) hm
@[c0_load] theorem load_arena_rel_limit (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 296) = some s.heur.rel_limit := load_hdr_tail 33 (by decide) hm
@[c0_load] theorem load_arena_rel_wait (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 304) = some s.heur.rel_wait := load_hdr_tail 34 (by decide) hm
@[c0_load] theorem load_arena_rel_u (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 312) = some s.heur.rel_u := load_hdr_tail 35 (by decide) hm
@[c0_load] theorem load_arena_rel_v (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 320) = some s.heur.rel_v := load_hdr_tail 36 (by decide) hm
@[c0_load] theorem load_arena_rel_trigger (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 328) = some s.heur.rel_trigger := load_hdr_tail 37 (by decide) hm
@[c0_load] theorem load_arena_conflicts (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 336) = some s.heur.conflicts := load_hdr_tail 38 (by decide) hm
@[c0_load] theorem load_arena_learned_lits (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 344) = some s.heur.learned_lits := load_hdr_tail 39 (by decide) hm
@[c0_load] theorem load_arena_min_removed (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 352) = some s.heur.min_removed := load_hdr_tail 40 (by decide) hm

@[c0_store] theorem store_arena_lit_len (v : Nat) (hm : (CorePlusMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 48) ∧ (CorePlusMem c { s with lit_len := v } ⋆ R)
      (storeMem m i64 (c.hdr + 48) (BitVec.ofNat 64 v)) :=
  store_hdr_tail 2 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem c0_store_arena_lit_len (v : BitVec 64) (hm : (CorePlusMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 48) ∧
      (CorePlusMem c { s with lit_len := v.toNat } ⋆ R) (storeMem m i64 (c.hdr + 48) v) := by
  simpa [bv_ofNat_toNat_eq] using store_arena_lit_len v.toNat hm
@[c0_store] theorem store_arena_num_clauses (v : Nat) (hm : (CorePlusMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 56) ∧ (CorePlusMem c { s with num_clauses := v } ⋆ R)
      (storeMem m i64 (c.hdr + 56) (BitVec.ofNat 64 v)) :=
  store_hdr_tail 3 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem c0_store_arena_num_clauses (v : BitVec 64) (hm : (CorePlusMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 56) ∧
      (CorePlusMem c { s with num_clauses := v.toNat } ⋆ R) (storeMem m i64 (c.hdr + 56) v) := by
  simpa [bv_ofNat_toNat_eq] using store_arena_num_clauses v.toNat hm
@[c0_store] theorem store_arena_trail_end (v : Nat) (hm : (CorePlusMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 144) ∧ (CorePlusMem c { s with trail_end := v } ⋆ R)
      (storeMem m i64 (c.hdr + 144) (BitVec.ofNat 64 v)) :=
  store_hdr_tail 14 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem c0_store_arena_trail_end (v : BitVec 64) (hm : (CorePlusMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 144) ∧
      (CorePlusMem c { s with trail_end := v.toNat } ⋆ R) (storeMem m i64 (c.hdr + 144) v) := by
  simpa [bv_ofNat_toNat_eq] using store_arena_trail_end v.toNat hm
@[c0_store] theorem store_arena_propagated (v : Nat) (hm : (CorePlusMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 152) ∧ (CorePlusMem c { s with propagated := v } ⋆ R)
      (storeMem m i64 (c.hdr + 152) (BitVec.ofNat 64 v)) :=
  store_hdr_tail 15 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem c0_store_arena_propagated (v : BitVec 64) (hm : (CorePlusMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 152) ∧
      (CorePlusMem c { s with propagated := v.toNat } ⋆ R) (storeMem m i64 (c.hdr + 152) v) := by
  simpa [bv_ofNat_toNat_eq] using store_arena_propagated v.toNat hm
@[c0_store] theorem store_arena_cur_level (v : Nat) (hm : (CorePlusMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 160) ∧ (CorePlusMem c { s with cur_level := v } ⋆ R)
      (storeMem m i64 (c.hdr + 160) (BitVec.ofNat 64 v)) :=
  store_hdr_tail 16 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem c0_store_arena_cur_level (v : BitVec 64) (hm : (CorePlusMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 160) ∧
      (CorePlusMem c { s with cur_level := v.toNat } ⋆ R) (storeMem m i64 (c.hdr + 160) v) := by
  simpa [bv_ofNat_toNat_eq] using store_arena_cur_level v.toNat hm
@[c0_store] theorem store_arena_fuel (v : BitVec 64) (hm : (CorePlusMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 168) ∧ (CorePlusMem c { s with fuel := v } ⋆ R)
      (storeMem m i64 (c.hdr + 168) v) :=
  store_hdr_tail 17 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_confl_cid (v : BitVec 64) (hm : (CorePlusMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 176) ∧ (CorePlusMem c { s with confl_cid := v } ⋆ R)
      (storeMem m i64 (c.hdr + 176) v) :=
  store_hdr_tail 18 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_tmp_cnt (v : Nat) (hm : (CorePlusMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 184) ∧ (CorePlusMem c { s with tmp_cnt := v } ⋆ R)
      (storeMem m i64 (c.hdr + 184) (BitVec.ofNat 64 v)) :=
  store_hdr_tail 19 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem c0_store_arena_tmp_cnt (v : BitVec 64) (hm : (CorePlusMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 184) ∧
      (CorePlusMem c { s with tmp_cnt := v.toNat } ⋆ R) (storeMem m i64 (c.hdr + 184) v) := by
  simpa [bv_ofNat_toNat_eq] using store_arena_tmp_cnt v.toNat hm
@[c0_store] theorem store_arena_tmp_len (v : Nat) (hm : (CorePlusMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 192) ∧ (CorePlusMem c { s with tmp_len := v } ⋆ R)
      (storeMem m i64 (c.hdr + 192) (BitVec.ofNat 64 v)) :=
  store_hdr_tail 20 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem c0_store_arena_tmp_len (v : BitVec 64) (hm : (CorePlusMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 192) ∧
      (CorePlusMem c { s with tmp_len := v.toNat } ⋆ R) (storeMem m i64 (c.hdr + 192) v) := by
  simpa [bv_ofNat_toNat_eq] using store_arena_tmp_len v.toNat hm
@[c0_store] theorem store_arena_heap_len (v : Nat) (hm : (CorePlusMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 248) ∧
      (CorePlusMem c { s with heur := { s.heur with heap_len := v } } ⋆ R)
        (storeMem m i64 (c.hdr + 248) (BitVec.ofNat 64 v)) :=
  store_hdr_tail 27 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem c0_store_arena_heap_len (v : BitVec 64) (hm : (CorePlusMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 248) ∧
      (CorePlusMem c { s with heur := { s.heur with heap_len := v.toNat } } ⋆ R)
        (storeMem m i64 (c.hdr + 248) v) := by
  simpa [bv_ofNat_toNat_eq] using store_arena_heap_len v.toNat hm
@[c0_store] theorem store_arena_scinc (v : BitVec 64) (hm : (CorePlusMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 256) ∧
      (CorePlusMem c { s with heur := { s.heur with scinc := v } } ⋆ R)
        (storeMem m i64 (c.hdr + 256) v) :=
  store_hdr_tail 28 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_min_clr_len (v : Nat) (hm : (CorePlusMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 272) ∧ (CorePlusMem c { s with min_clr_len := v } ⋆ R)
      (storeMem m i64 (c.hdr + 272) (BitVec.ofNat 64 v)) :=
  store_hdr_tail 30 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem c0_store_arena_min_clr_len (v : BitVec 64) (hm : (CorePlusMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 272) ∧
      (CorePlusMem c { s with min_clr_len := v.toNat } ⋆ R) (storeMem m i64 (c.hdr + 272) v) := by
  simpa [bv_ofNat_toNat_eq] using store_arena_min_clr_len v.toNat hm
@[c0_store] theorem store_arena_min_clr_full (v : BitVec 64) (hm : (CorePlusMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 280) ∧ (CorePlusMem c { s with min_clr_full := v } ⋆ R)
      (storeMem m i64 (c.hdr + 280) v) :=
  store_hdr_tail 31 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_rel_wait (v : BitVec 64) (hm : (CorePlusMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 304) ∧
      (CorePlusMem c { s with heur := { s.heur with rel_wait := v } } ⋆ R)
        (storeMem m i64 (c.hdr + 304) v) :=
  store_hdr_tail 34 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_rel_u (v : BitVec 64) (hm : (CorePlusMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 312) ∧
      (CorePlusMem c { s with heur := { s.heur with rel_u := v } } ⋆ R)
        (storeMem m i64 (c.hdr + 312) v) :=
  store_hdr_tail 35 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_rel_v (v : BitVec 64) (hm : (CorePlusMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 320) ∧
      (CorePlusMem c { s with heur := { s.heur with rel_v := v } } ⋆ R)
        (storeMem m i64 (c.hdr + 320) v) :=
  store_hdr_tail 36 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_rel_trigger (v : BitVec 64) (hm : (CorePlusMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 328) ∧
      (CorePlusMem c { s with heur := { s.heur with rel_trigger := v } } ⋆ R)
        (storeMem m i64 (c.hdr + 328) v) :=
  store_hdr_tail 37 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_conflicts (v : BitVec 64) (hm : (CorePlusMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 336) ∧
      (CorePlusMem c { s with heur := { s.heur with conflicts := v } } ⋆ R)
        (storeMem m i64 (c.hdr + 336) v) :=
  store_hdr_tail 38 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_learned_lits (v : BitVec 64) (hm : (CorePlusMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 344) ∧
      (CorePlusMem c { s with heur := { s.heur with learned_lits := v } } ⋆ R)
        (storeMem m i64 (c.hdr + 344) v) :=
  store_hdr_tail 39 (by decide) _ _ hm rfl rfl rfl rfl rfl
@[c0_store] theorem store_arena_min_removed (v : BitVec 64) (hm : (CorePlusMem c s ⋆ R) m) :
    storeOk m i64 (c.hdr + 352) ∧
      (CorePlusMem c { s with heur := { s.heur with min_removed := v } } ⋆ R)
        (storeMem m i64 (c.hdr + 352) v) :=
  store_hdr_tail 40 (by decide) _ _ hm rfl rfl rfl rfl rfl

private theorem load_arr_i8 {a : BitVec 64} {xs : List (BitVec 8)} {F : Mem 64 → Prop} {i : Nat}
    (hi : i < xs.length) (h : (array (t := i8) a xs ⋆ F) m) :
    loadVal m i8 (a + BitVec.ofNat 64 i) = some xs[i] := by
  simpa [Ty.bytes, Ty.size, i8] using loadVal_array (t := i8) (by decide) hi h
private theorem store_arr_i8 {a : BitVec 64} {xs : List (BitVec 8)} {F : Mem 64 → Prop} {i : Nat}
    (v : BitVec 8) (hi : i < xs.length) (h : (array (t := i8) a xs ⋆ F) m) :
    storeOk m i8 (a + BitVec.ofNat 64 i) ∧
      (array (t := i8) a (xs.set i v) ⋆ F) (storeMem m i8 (a + BitVec.ofNat 64 i) v) := by
  simpa [Ty.bytes, Ty.size, i8] using store_array (t := i8) v (by decide) hi h
private theorem load_arr_i32 {a : BitVec 64} {xs : List (BitVec 32)} {F : Mem 64 → Prop} {i : Nat}
    (hi : i < xs.length) (h : (array (t := i32) a xs ⋆ F) m) :
    loadVal m i32 (a + BitVec.ofNat 64 (4 * i)) = some xs[i] :=
  loadVal_array (t := i32) (by decide) hi h
private theorem store_arr_i32 {a : BitVec 64} {xs : List (BitVec 32)} {F : Mem 64 → Prop}
    {i : Nat} (v : BitVec 32) (hi : i < xs.length) (h : (array (t := i32) a xs ⋆ F) m) :
    storeOk m i32 (a + BitVec.ofNat 64 (4 * i)) ∧
      (array (t := i32) a (xs.set i v) ⋆ F) (storeMem m i32 (a + BitVec.ofNat 64 (4 * i)) v) :=
  store_array (t := i32) v (by decide) hi h
private theorem load_arr_i64 {a : BitVec 64} {xs : List (BitVec 64)} {F : Mem 64 → Prop} {i : Nat}
    (hi : i < xs.length) (h : (array64 a xs ⋆ F) m) :
    loadVal m i64 (a + BitVec.ofNat 64 (8 * i)) = some xs[i] :=
  loadVal_array64 hi h
private theorem store_arr_i64 {a : BitVec 64} {xs : List (BitVec 64)} {F : Mem 64 → Prop}
    {i : Nat} (v : BitVec 64) (hi : i < xs.length) (h : (array64 a xs ⋆ F) m) :
    storeOk m i64 (a + BitVec.ofNat 64 (8 * i)) ∧
      (array64 a (xs.set i v) ⋆ F) (storeMem m i64 (a + BitVec.ofNat 64 (8 * i)) v) :=
  store_array64 v hi h

private def coreMemOuter (c : CorePlusCfg) (s : CorePlusState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.d_cur s.d_val ⋆
  array64 (c.hdr + 32) (hdrTailWords c s) ⋆ HeurArrays c s.heur ⋆ c.pad

private def heurMemOuter (c : CorePlusCfg) (s : CorePlusState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.d_cur s.d_val ⋆
  array64 (c.hdr + 32) (hdrTailWords c s) ⋆ CoreArrays c s ⋆ c.pad

private theorem corePlusMem_eq_core (c : CorePlusCfg) (s : CorePlusState) :
    CorePlusMem c s = (coreMemOuter c s ⋆ CoreArrays c s) := by
  unfold CorePlusMem coreMemOuter; ac_rfl

private theorem corePlusMem_eq_heur (c : CorePlusCfg) (s : CorePlusState) :
    CorePlusMem c s = (heurMemOuter c s ⋆ HeurArrays c s.heur) := by
  unfold CorePlusMem heurMemOuter; ac_rfl

private theorem c0_bv_mul (i : BitVec 64) (k : Nat) :
    i * BitVec.ofNat 64 k = BitVec.ofNat 64 (k * i.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mul_mod_mod, Nat.mul_comm]

private theorem unfocus_core (s s' : CorePlusState) {m' : Mem 64}
    (ho : coreMemOuter c s' = coreMemOuter c s)
    (h : ((coreMemOuter c s ⋆ CoreArrays c s') ⋆ R) m') : (CorePlusMem c s' ⋆ R) m' := by
  rw [corePlusMem_eq_core, ho]; exact h

private theorem unfocus_heur (s s' : CorePlusState) {m' : Mem 64}
    (ho : heurMemOuter c s' = heurMemOuter c s)
    (h : ((heurMemOuter c s ⋆ HeurArrays c s'.heur) ⋆ R) m') : (CorePlusMem c s' ⋆ R) m' := by
  rw [corePlusMem_eq_heur, ho]; exact h

@[c0_load] theorem load_arena_vals {i : Nat} (hi : i < s.vals.length)
    (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i8 (c.pVals + BitVec.ofNat 64 i) = some s.vals[i] := by
  rw [corePlusMem_eq_core] at hm; unfold CoreArrays at hm; exact load_arr_i8 hi (by ecancel)
@[c0_load] theorem c0_load_arena_vals {i : BitVec 64} (hi : i.toNat < s.vals.length)
    (hm : (CorePlusMem c s ⋆ R) m) : loadVal m i8 (c.pVals + i) = some s.vals[i.toNat] := by
  simpa [bv_ofNat_toNat_eq] using load_arena_vals hi hm
@[c0_store] theorem store_arena_vals {i : Nat} (v : BitVec 8) (hi : i < s.vals.length)
    (hm : (CorePlusMem c s ⋆ R) m) : storeOk m i8 (c.pVals + BitVec.ofNat 64 i) ∧
      (CorePlusMem c { s with vals := s.vals.set i v } ⋆ R)
        (storeMem m i8 (c.pVals + BitVec.ofNat 64 i) v) := by
  rw [corePlusMem_eq_core] at hm; unfold CoreArrays at hm
  obtain ⟨hok, hst⟩ := store_arr_i8 v hi (F := _) (by ecancel)
  refine ⟨hok, unfocus_core s _ rfl ?_⟩; unfold CoreArrays; dsimp only; ecancel
@[c0_store] theorem c0_store_arena_vals {i : BitVec 64} (v : BitVec 8)
    (hi : i.toNat < s.vals.length) (hm : (CorePlusMem c s ⋆ R) m) :
    storeOk m i8 (c.pVals + i) ∧ (CorePlusMem c { s with vals := s.vals.set i.toNat v } ⋆ R)
      (storeMem m i8 (c.pVals + i) v) := by
  simpa [bv_ofNat_toNat_eq] using store_arena_vals v hi hm

@[c0_load] theorem load_arena_mrk {i : Nat} (hi : i < s.mrk.length)
    (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i8 (c.pMark + BitVec.ofNat 64 i) = some s.mrk[i] := by
  rw [corePlusMem_eq_core] at hm; unfold CoreArrays at hm; exact load_arr_i8 hi (by ecancel)
@[c0_load] theorem c0_load_arena_mrk {i : BitVec 64} (hi : i.toNat < s.mrk.length)
    (hm : (CorePlusMem c s ⋆ R) m) : loadVal m i8 (c.pMark + i) = some s.mrk[i.toNat] := by
  simpa [bv_ofNat_toNat_eq] using load_arena_mrk hi hm
@[c0_store] theorem store_arena_mrk {i : Nat} (v : BitVec 8) (hi : i < s.mrk.length)
    (hm : (CorePlusMem c s ⋆ R) m) : storeOk m i8 (c.pMark + BitVec.ofNat 64 i) ∧
      (CorePlusMem c { s with mrk := s.mrk.set i v } ⋆ R)
        (storeMem m i8 (c.pMark + BitVec.ofNat 64 i) v) := by
  rw [corePlusMem_eq_core] at hm; unfold CoreArrays at hm
  obtain ⟨hok, hst⟩ := store_arr_i8 v hi (F := _) (by ecancel)
  refine ⟨hok, unfocus_core s _ rfl ?_⟩; unfold CoreArrays; dsimp only; ecancel
@[c0_store] theorem c0_store_arena_mrk {i : BitVec 64} (v : BitVec 8)
    (hi : i.toNat < s.mrk.length) (hm : (CorePlusMem c s ⋆ R) m) :
    storeOk m i8 (c.pMark + i) ∧ (CorePlusMem c { s with mrk := s.mrk.set i.toNat v } ⋆ R)
      (storeMem m i8 (c.pMark + i) v) := by
  simpa [bv_ofNat_toNat_eq] using store_arena_mrk v hi hm

@[c0_load] theorem load_arena_lvl {i : Nat} (hi : i < s.lvl.length)
    (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i32 (c.pLevel + BitVec.ofNat 64 (4 * i)) = some s.lvl[i] := by
  rw [corePlusMem_eq_core] at hm; unfold CoreArrays at hm; exact load_arr_i32 hi (by ecancel)
@[c0_load] theorem c0_load_arena_lvl {i : BitVec 64} (hi : i.toNat < s.lvl.length)
    (hm : (CorePlusMem c s ⋆ R) m) : loadVal m i32 (c.pLevel + i * 4) = some s.lvl[i.toNat] := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_bv_mul]; exact load_arena_lvl hi hm
@[c0_store] theorem store_arena_lvl {i : Nat} (v : BitVec 32) (hi : i < s.lvl.length)
    (hm : (CorePlusMem c s ⋆ R) m) : storeOk m i32 (c.pLevel + BitVec.ofNat 64 (4 * i)) ∧
      (CorePlusMem c { s with lvl := s.lvl.set i v } ⋆ R)
        (storeMem m i32 (c.pLevel + BitVec.ofNat 64 (4 * i)) v) := by
  rw [corePlusMem_eq_core] at hm; unfold CoreArrays at hm
  obtain ⟨hok, hst⟩ := store_arr_i32 v hi (F := _) (by ecancel)
  refine ⟨hok, unfocus_core s _ rfl ?_⟩; unfold CoreArrays; dsimp only; ecancel
@[c0_store] theorem c0_store_arena_lvl {i : BitVec 64} (v : BitVec 32)
    (hi : i.toNat < s.lvl.length) (hm : (CorePlusMem c s ⋆ R) m) :
    storeOk m i32 (c.pLevel + i * 4) ∧ (CorePlusMem c { s with lvl := s.lvl.set i.toNat v } ⋆ R)
      (storeMem m i32 (c.pLevel + i * 4) v) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_bv_mul]; exact store_arena_lvl v hi hm

@[c0_load] theorem load_arena_rsns {i : Nat} (hi : i < s.rsns.length)
    (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i32 (c.pReason + BitVec.ofNat 64 (4 * i)) = some s.rsns[i] := by
  rw [corePlusMem_eq_core] at hm; unfold CoreArrays at hm; exact load_arr_i32 hi (by ecancel)
@[c0_load] theorem c0_load_arena_rsns {i : BitVec 64} (hi : i.toNat < s.rsns.length)
    (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i32 (c.pReason + i * 4) = some s.rsns[i.toNat] := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_bv_mul]; exact load_arena_rsns hi hm
@[c0_store] theorem store_arena_rsns {i : Nat} (v : BitVec 32) (hi : i < s.rsns.length)
    (hm : (CorePlusMem c s ⋆ R) m) : storeOk m i32 (c.pReason + BitVec.ofNat 64 (4 * i)) ∧
      (CorePlusMem c { s with rsns := s.rsns.set i v } ⋆ R)
        (storeMem m i32 (c.pReason + BitVec.ofNat 64 (4 * i)) v) := by
  rw [corePlusMem_eq_core] at hm; unfold CoreArrays at hm
  obtain ⟨hok, hst⟩ := store_arr_i32 v hi (F := _) (by ecancel)
  refine ⟨hok, unfocus_core s _ rfl ?_⟩; unfold CoreArrays; dsimp only; ecancel
@[c0_store] theorem c0_store_arena_rsns {i : BitVec 64} (v : BitVec 32)
    (hi : i.toNat < s.rsns.length) (hm : (CorePlusMem c s ⋆ R) m) :
    storeOk m i32 (c.pReason + i * 4) ∧ (CorePlusMem c { s with rsns := s.rsns.set i.toNat v } ⋆ R)
      (storeMem m i32 (c.pReason + i * 4) v) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_bv_mul]; exact store_arena_rsns v hi hm

@[c0_load] theorem load_arena_trl {i : Nat} (hi : i < s.trl.length)
    (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i32 (c.pTrail + BitVec.ofNat 64 (4 * i)) = some s.trl[i] := by
  rw [corePlusMem_eq_core] at hm; unfold CoreArrays at hm; exact load_arr_i32 hi (by ecancel)
@[c0_load] theorem c0_load_arena_trl {i : BitVec 64} (hi : i.toNat < s.trl.length)
    (hm : (CorePlusMem c s ⋆ R) m) : loadVal m i32 (c.pTrail + i * 4) = some s.trl[i.toNat] := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_bv_mul]; exact load_arena_trl hi hm
@[c0_store] theorem store_arena_trl {i : Nat} (v : BitVec 32) (hi : i < s.trl.length)
    (hm : (CorePlusMem c s ⋆ R) m) : storeOk m i32 (c.pTrail + BitVec.ofNat 64 (4 * i)) ∧
      (CorePlusMem c { s with trl := s.trl.set i v } ⋆ R)
        (storeMem m i32 (c.pTrail + BitVec.ofNat 64 (4 * i)) v) := by
  rw [corePlusMem_eq_core] at hm; unfold CoreArrays at hm
  obtain ⟨hok, hst⟩ := store_arr_i32 v hi (F := _) (by ecancel)
  refine ⟨hok, unfocus_core s _ rfl ?_⟩; unfold CoreArrays; dsimp only; ecancel
@[c0_store] theorem c0_store_arena_trl {i : BitVec 64} (v : BitVec 32)
    (hi : i.toNat < s.trl.length) (hm : (CorePlusMem c s ⋆ R) m) :
    storeOk m i32 (c.pTrail + i * 4) ∧ (CorePlusMem c { s with trl := s.trl.set i.toNat v } ⋆ R)
      (storeMem m i32 (c.pTrail + i * 4) v) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_bv_mul]; exact store_arena_trl v hi hm

@[c0_load] theorem load_arena_tmp {i : Nat} (hi : i < s.tmp.length)
    (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i32 (c.pTmp + BitVec.ofNat 64 (4 * i)) = some s.tmp[i] := by
  rw [corePlusMem_eq_core] at hm; unfold CoreArrays at hm; exact load_arr_i32 hi (by ecancel)
@[c0_load] theorem c0_load_arena_tmp {i : BitVec 64} (hi : i.toNat < s.tmp.length)
    (hm : (CorePlusMem c s ⋆ R) m) : loadVal m i32 (c.pTmp + i * 4) = some s.tmp[i.toNat] := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_bv_mul]; exact load_arena_tmp hi hm
@[c0_store] theorem store_arena_tmp {i : Nat} (v : BitVec 32) (hi : i < s.tmp.length)
    (hm : (CorePlusMem c s ⋆ R) m) : storeOk m i32 (c.pTmp + BitVec.ofNat 64 (4 * i)) ∧
      (CorePlusMem c { s with tmp := s.tmp.set i v } ⋆ R)
        (storeMem m i32 (c.pTmp + BitVec.ofNat 64 (4 * i)) v) := by
  rw [corePlusMem_eq_core] at hm; unfold CoreArrays at hm
  obtain ⟨hok, hst⟩ := store_arr_i32 v hi (F := _) (by ecancel)
  refine ⟨hok, unfocus_core s _ rfl ?_⟩; unfold CoreArrays; dsimp only; ecancel
@[c0_store] theorem c0_store_arena_tmp {i : BitVec 64} (v : BitVec 32)
    (hi : i.toNat < s.tmp.length) (hm : (CorePlusMem c s ⋆ R) m) :
    storeOk m i32 (c.pTmp + i * 4) ∧ (CorePlusMem c { s with tmp := s.tmp.set i.toNat v } ⋆ R)
      (storeMem m i32 (c.pTmp + i * 4) v) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_bv_mul]; exact store_arena_tmp v hi hm

@[c0_load] theorem load_arena_wh {i : Nat} (hi : i < s.wh.length)
    (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i32 (c.pWh + BitVec.ofNat 64 (4 * i)) = some s.wh[i] := by
  rw [corePlusMem_eq_core] at hm; unfold CoreArrays at hm; exact load_arr_i32 hi (by ecancel)
@[c0_load] theorem c0_load_arena_wh {i : BitVec 64} (hi : i.toNat < s.wh.length)
    (hm : (CorePlusMem c s ⋆ R) m) : loadVal m i32 (c.pWh + i * 4) = some s.wh[i.toNat] := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_bv_mul]; exact load_arena_wh hi hm
@[c0_store] theorem store_arena_wh {i : Nat} (v : BitVec 32) (hi : i < s.wh.length)
    (hm : (CorePlusMem c s ⋆ R) m) : storeOk m i32 (c.pWh + BitVec.ofNat 64 (4 * i)) ∧
      (CorePlusMem c { s with wh := s.wh.set i v } ⋆ R)
        (storeMem m i32 (c.pWh + BitVec.ofNat 64 (4 * i)) v) := by
  rw [corePlusMem_eq_core] at hm; unfold CoreArrays at hm
  obtain ⟨hok, hst⟩ := store_arr_i32 v hi (F := _) (by ecancel)
  refine ⟨hok, unfocus_core s _ rfl ?_⟩; unfold CoreArrays; dsimp only; ecancel
@[c0_store] theorem c0_store_arena_wh {i : BitVec 64} (v : BitVec 32)
    (hi : i.toNat < s.wh.length) (hm : (CorePlusMem c s ⋆ R) m) :
    storeOk m i32 (c.pWh + i * 4) ∧ (CorePlusMem c { s with wh := s.wh.set i.toNat v } ⋆ R)
      (storeMem m i32 (c.pWh + i * 4) v) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_bv_mul]; exact store_arena_wh v hi hm

@[c0_load] theorem load_arena_cls {i : Nat} (hi : i < s.cls.length)
    (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i32 (c.pClauses + BitVec.ofNat 64 (4 * i)) = some s.cls[i] := by
  rw [corePlusMem_eq_core] at hm; unfold CoreArrays at hm; exact load_arr_i32 hi (by ecancel)
@[c0_load] theorem c0_load_arena_cls {i : BitVec 64} (hi : i.toNat < s.cls.length)
    (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i32 (c.pClauses + i * 4) = some s.cls[i.toNat] := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_bv_mul]; exact load_arena_cls hi hm
@[c0_store] theorem store_arena_cls {i : Nat} (v : BitVec 32) (hi : i < s.cls.length)
    (hm : (CorePlusMem c s ⋆ R) m) : storeOk m i32 (c.pClauses + BitVec.ofNat 64 (4 * i)) ∧
      (CorePlusMem c { s with cls := s.cls.set i v } ⋆ R)
        (storeMem m i32 (c.pClauses + BitVec.ofNat 64 (4 * i)) v) := by
  rw [corePlusMem_eq_core] at hm; unfold CoreArrays at hm
  obtain ⟨hok, hst⟩ := store_arr_i32 v hi (F := _) (by ecancel)
  refine ⟨hok, unfocus_core s _ rfl ?_⟩; unfold CoreArrays; dsimp only; ecancel
@[c0_store] theorem c0_store_arena_cls {i : BitVec 64} (v : BitVec 32)
    (hi : i.toNat < s.cls.length) (hm : (CorePlusMem c s ⋆ R) m) :
    storeOk m i32 (c.pClauses + i * 4) ∧ (CorePlusMem c { s with cls := s.cls.set i.toNat v } ⋆ R)
      (storeMem m i32 (c.pClauses + i * 4) v) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_bv_mul]; exact store_arena_cls v hi hm

@[c0_load] theorem load_arena_wn {i : Nat} (hi : i < s.wn.length)
    (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i32 (c.pWn + BitVec.ofNat 64 (4 * i)) = some s.wn[i] := by
  rw [corePlusMem_eq_core] at hm; unfold CoreArrays at hm; exact load_arr_i32 hi (by ecancel)
@[c0_load] theorem c0_load_arena_wn {i : BitVec 64} (hi : i.toNat < s.wn.length)
    (hm : (CorePlusMem c s ⋆ R) m) : loadVal m i32 (c.pWn + i * 4) = some s.wn[i.toNat] := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_bv_mul]; exact load_arena_wn hi hm
@[c0_store] theorem store_arena_wn {i : Nat} (v : BitVec 32) (hi : i < s.wn.length)
    (hm : (CorePlusMem c s ⋆ R) m) : storeOk m i32 (c.pWn + BitVec.ofNat 64 (4 * i)) ∧
      (CorePlusMem c { s with wn := s.wn.set i v } ⋆ R)
        (storeMem m i32 (c.pWn + BitVec.ofNat 64 (4 * i)) v) := by
  rw [corePlusMem_eq_core] at hm; unfold CoreArrays at hm
  obtain ⟨hok, hst⟩ := store_arr_i32 v hi (F := _) (by ecancel)
  refine ⟨hok, unfocus_core s _ rfl ?_⟩; unfold CoreArrays; dsimp only; ecancel
@[c0_store] theorem c0_store_arena_wn {i : BitVec 64} (v : BitVec 32)
    (hi : i.toNat < s.wn.length) (hm : (CorePlusMem c s ⋆ R) m) :
    storeOk m i32 (c.pWn + i * 4) ∧ (CorePlusMem c { s with wn := s.wn.set i.toNat v } ⋆ R)
      (storeMem m i32 (c.pWn + i * 4) v) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_bv_mul]; exact store_arena_wn v hi hm

@[c0_load] theorem load_arena_lpool {i : Nat} (hi : i < s.lpool.length)
    (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i32 (c.pLpool + BitVec.ofNat 64 (4 * i)) = some s.lpool[i] := by
  rw [corePlusMem_eq_core] at hm; unfold CoreArrays at hm; exact load_arr_i32 hi (by ecancel)
@[c0_load] theorem c0_load_arena_lpool {i : BitVec 64} (hi : i.toNat < s.lpool.length)
    (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i32 (c.pLpool + i * 4) = some s.lpool[i.toNat] := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_bv_mul]; exact load_arena_lpool hi hm
@[c0_store] theorem store_arena_lpool {i : Nat} (v : BitVec 32) (hi : i < s.lpool.length)
    (hm : (CorePlusMem c s ⋆ R) m) : storeOk m i32 (c.pLpool + BitVec.ofNat 64 (4 * i)) ∧
      (CorePlusMem c { s with lpool := s.lpool.set i v } ⋆ R)
        (storeMem m i32 (c.pLpool + BitVec.ofNat 64 (4 * i)) v) := by
  rw [corePlusMem_eq_core] at hm; unfold CoreArrays at hm
  obtain ⟨hok, hst⟩ := store_arr_i32 v hi (F := _) (by ecancel)
  refine ⟨hok, unfocus_core s _ rfl ?_⟩; unfold CoreArrays; dsimp only; ecancel
@[c0_store] theorem c0_store_arena_lpool {i : BitVec 64} (v : BitVec 32)
    (hi : i.toNat < s.lpool.length) (hm : (CorePlusMem c s ⋆ R) m) :
    storeOk m i32 (c.pLpool + i * 4) ∧
      (CorePlusMem c { s with lpool := s.lpool.set i.toNat v } ⋆ R)
        (storeMem m i32 (c.pLpool + i * 4) v) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_bv_mul]; exact store_arena_lpool v hi hm

@[c0_load] theorem load_arena_min_stk {i : Nat} (hi : i < s.min_stk.length)
    (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i32 (c.pMinStk + BitVec.ofNat 64 (4 * i)) = some s.min_stk[i] := by
  rw [corePlusMem_eq_core] at hm; unfold CoreArrays at hm; exact load_arr_i32 hi (by ecancel)
@[c0_load] theorem c0_load_arena_min_stk {i : BitVec 64} (hi : i.toNat < s.min_stk.length)
    (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i32 (c.pMinStk + i * 4) = some s.min_stk[i.toNat] := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_bv_mul]
  exact load_arena_min_stk hi hm
@[c0_store] theorem store_arena_min_stk {i : Nat} (v : BitVec 32) (hi : i < s.min_stk.length)
    (hm : (CorePlusMem c s ⋆ R) m) : storeOk m i32 (c.pMinStk + BitVec.ofNat 64 (4 * i)) ∧
      (CorePlusMem c { s with min_stk := s.min_stk.set i v } ⋆ R)
        (storeMem m i32 (c.pMinStk + BitVec.ofNat 64 (4 * i)) v) := by
  rw [corePlusMem_eq_core] at hm; unfold CoreArrays at hm
  obtain ⟨hok, hst⟩ := store_arr_i32 v hi (F := _) (by ecancel)
  refine ⟨hok, unfocus_core s _ rfl ?_⟩; unfold CoreArrays; dsimp only; ecancel
@[c0_store] theorem c0_store_arena_min_stk {i : BitVec 64} (v : BitVec 32)
    (hi : i.toNat < s.min_stk.length) (hm : (CorePlusMem c s ⋆ R) m) :
    storeOk m i32 (c.pMinStk + i * 4) ∧
      (CorePlusMem c { s with min_stk := s.min_stk.set i.toNat v } ⋆ R)
        (storeMem m i32 (c.pMinStk + i * 4) v) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_bv_mul]
  exact store_arena_min_stk v hi hm

@[c0_load] theorem load_arena_min_clr {i : Nat} (hi : i < s.min_clr.length)
    (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i32 (c.pMinClr + BitVec.ofNat 64 (4 * i)) = some s.min_clr[i] := by
  rw [corePlusMem_eq_core] at hm; unfold CoreArrays at hm; exact load_arr_i32 hi (by ecancel)
@[c0_load] theorem c0_load_arena_min_clr {i : BitVec 64} (hi : i.toNat < s.min_clr.length)
    (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i32 (c.pMinClr + i * 4) = some s.min_clr[i.toNat] := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_bv_mul]
  exact load_arena_min_clr hi hm
@[c0_store] theorem store_arena_min_clr {i : Nat} (v : BitVec 32) (hi : i < s.min_clr.length)
    (hm : (CorePlusMem c s ⋆ R) m) : storeOk m i32 (c.pMinClr + BitVec.ofNat 64 (4 * i)) ∧
      (CorePlusMem c { s with min_clr := s.min_clr.set i v } ⋆ R)
        (storeMem m i32 (c.pMinClr + BitVec.ofNat 64 (4 * i)) v) := by
  rw [corePlusMem_eq_core] at hm; unfold CoreArrays at hm
  obtain ⟨hok, hst⟩ := store_arr_i32 v hi (F := _) (by ecancel)
  refine ⟨hok, unfocus_core s _ rfl ?_⟩; unfold CoreArrays; dsimp only; ecancel
@[c0_store] theorem c0_store_arena_min_clr {i : BitVec 64} (v : BitVec 32)
    (hi : i.toNat < s.min_clr.length) (hm : (CorePlusMem c s ⋆ R) m) :
    storeOk m i32 (c.pMinClr + i * 4) ∧
      (CorePlusMem c { s with min_clr := s.min_clr.set i.toNat v } ⋆ R)
        (storeMem m i32 (c.pMinClr + i * 4) v) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_bv_mul]
  exact store_arena_min_clr v hi hm

@[c0_load] theorem load_arena_heap {i : Nat} (hi : i < s.heur.heap.length)
    (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i32 (c.pHeap + BitVec.ofNat 64 (4 * i)) = some s.heur.heap[i] := by
  rw [corePlusMem_eq_heur] at hm; unfold HeurArrays at hm; exact load_arr_i32 hi (by ecancel)
@[c0_load] theorem c0_load_arena_heap {i : BitVec 64} (hi : i.toNat < s.heur.heap.length)
    (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i32 (c.pHeap + i * 4) = some s.heur.heap[i.toNat] := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_bv_mul]; exact load_arena_heap hi hm
@[c0_store] theorem store_arena_heap {i : Nat} (v : BitVec 32) (hi : i < s.heur.heap.length)
    (hm : (CorePlusMem c s ⋆ R) m) : storeOk m i32 (c.pHeap + BitVec.ofNat 64 (4 * i)) ∧
      (CorePlusMem c { s with heur := { s.heur with heap := s.heur.heap.set i v } } ⋆ R)
        (storeMem m i32 (c.pHeap + BitVec.ofNat 64 (4 * i)) v) := by
  rw [corePlusMem_eq_heur] at hm; unfold HeurArrays at hm
  obtain ⟨hok, hst⟩ := store_arr_i32 v hi (F := _) (by ecancel)
  refine ⟨hok, unfocus_heur s _ rfl ?_⟩; unfold HeurArrays; dsimp only; ecancel
@[c0_store] theorem c0_store_arena_heap {i : BitVec 64} (v : BitVec 32)
    (hi : i.toNat < s.heur.heap.length) (hm : (CorePlusMem c s ⋆ R) m) :
    storeOk m i32 (c.pHeap + i * 4) ∧
      (CorePlusMem c { s with
          heur := { s.heur with heap := s.heur.heap.set i.toNat v } } ⋆ R)
        (storeMem m i32 (c.pHeap + i * 4) v) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_bv_mul]; exact store_arena_heap v hi hm

@[c0_load] theorem load_arena_pos {i : Nat} (hi : i < s.heur.pos.length)
    (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i32 (c.pPos + BitVec.ofNat 64 (4 * i)) = some s.heur.pos[i] := by
  rw [corePlusMem_eq_heur] at hm; unfold HeurArrays at hm; exact load_arr_i32 hi (by ecancel)
@[c0_load] theorem c0_load_arena_pos {i : BitVec 64} (hi : i.toNat < s.heur.pos.length)
    (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i32 (c.pPos + i * 4) = some s.heur.pos[i.toNat] := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_bv_mul]; exact load_arena_pos hi hm
@[c0_store] theorem store_arena_pos {i : Nat} (v : BitVec 32) (hi : i < s.heur.pos.length)
    (hm : (CorePlusMem c s ⋆ R) m) : storeOk m i32 (c.pPos + BitVec.ofNat 64 (4 * i)) ∧
      (CorePlusMem c { s with heur := { s.heur with pos := s.heur.pos.set i v } } ⋆ R)
        (storeMem m i32 (c.pPos + BitVec.ofNat 64 (4 * i)) v) := by
  rw [corePlusMem_eq_heur] at hm; unfold HeurArrays at hm
  obtain ⟨hok, hst⟩ := store_arr_i32 v hi (F := _) (by ecancel)
  refine ⟨hok, unfocus_heur s _ rfl ?_⟩; unfold HeurArrays; dsimp only; ecancel
@[c0_store] theorem c0_store_arena_pos {i : BitVec 64} (v : BitVec 32)
    (hi : i.toNat < s.heur.pos.length) (hm : (CorePlusMem c s ⋆ R) m) :
    storeOk m i32 (c.pPos + i * 4) ∧
      (CorePlusMem c { s with
          heur := { s.heur with pos := s.heur.pos.set i.toNat v } } ⋆ R)
        (storeMem m i32 (c.pPos + i * 4) v) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_bv_mul]; exact store_arena_pos v hi hm

@[c0_load] theorem load_arena_score {i : Nat} (hi : i < s.heur.score.length)
    (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i64 (c.pScore + BitVec.ofNat 64 (8 * i)) = some s.heur.score[i] := by
  rw [corePlusMem_eq_heur] at hm; unfold HeurArrays at hm; exact load_arr_i64 hi (by ecancel)
@[c0_load] theorem c0_load_arena_score {i : BitVec 64} (hi : i.toNat < s.heur.score.length)
    (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i64 (c.pScore + i * 8) = some s.heur.score[i.toNat] := by
  rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, c0_bv_mul]; exact load_arena_score hi hm
@[c0_store] theorem store_arena_score {i : Nat} (v : BitVec 64) (hi : i < s.heur.score.length)
    (hm : (CorePlusMem c s ⋆ R) m) : storeOk m i64 (c.pScore + BitVec.ofNat 64 (8 * i)) ∧
      (CorePlusMem c { s with heur := { s.heur with score := s.heur.score.set i v } } ⋆ R)
        (storeMem m i64 (c.pScore + BitVec.ofNat 64 (8 * i)) v) := by
  rw [corePlusMem_eq_heur] at hm; unfold HeurArrays at hm
  obtain ⟨hok, hst⟩ := store_arr_i64 v hi (F := _) (by ecancel)
  refine ⟨hok, unfocus_heur s _ rfl ?_⟩; unfold HeurArrays; dsimp only; ecancel
@[c0_store] theorem c0_store_arena_score {i : BitVec 64} (v : BitVec 64)
    (hi : i.toNat < s.heur.score.length) (hm : (CorePlusMem c s ⋆ R) m) :
    storeOk m i64 (c.pScore + i * 8) ∧
      (CorePlusMem c { s with
          heur := { s.heur with score := s.heur.score.set i.toNat v } } ⋆ R)
        (storeMem m i64 (c.pScore + i * 8) v) := by
  rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, c0_bv_mul]; exact store_arena_score v hi hm

@[c0_load] theorem load_arena_phases {i : Nat} (hi : i < s.heur.phases.length)
    (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i8 (c.pPhases + BitVec.ofNat 64 i) = some s.heur.phases[i] := by
  rw [corePlusMem_eq_heur] at hm; unfold HeurArrays at hm; exact load_arr_i8 hi (by ecancel)
@[c0_load] theorem c0_load_arena_phases {i : BitVec 64} (hi : i.toNat < s.heur.phases.length)
    (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i8 (c.pPhases + i) = some s.heur.phases[i.toNat] := by
  simpa [bv_ofNat_toNat_eq] using load_arena_phases hi hm
@[c0_store] theorem store_arena_phases {i : Nat} (v : BitVec 8) (hi : i < s.heur.phases.length)
    (hm : (CorePlusMem c s ⋆ R) m) : storeOk m i8 (c.pPhases + BitVec.ofNat 64 i) ∧
      (CorePlusMem c { s with
          heur := { s.heur with phases := s.heur.phases.set i v } } ⋆ R)
        (storeMem m i8 (c.pPhases + BitVec.ofNat 64 i) v) := by
  rw [corePlusMem_eq_heur] at hm; unfold HeurArrays at hm
  obtain ⟨hok, hst⟩ := store_arr_i8 v hi (F := _) (by ecancel)
  refine ⟨hok, unfocus_heur s _ rfl ?_⟩; unfold HeurArrays; dsimp only; ecancel
@[c0_store] theorem c0_store_arena_phases {i : BitVec 64} (v : BitVec 8)
    (hi : i.toNat < s.heur.phases.length) (hm : (CorePlusMem c s ⋆ R) m) :
    storeOk m i8 (c.pPhases + i) ∧
      (CorePlusMem c { s with
          heur := { s.heur with phases := s.heur.phases.set i.toNat v } } ⋆ R)
        (storeMem m i8 (c.pPhases + i) v) := by
  simpa [bv_ofNat_toNat_eq] using store_arena_phases v hi hm

end CorePlusAccess

end LeanQbe.T.Examples.Kissat.CorePlus
