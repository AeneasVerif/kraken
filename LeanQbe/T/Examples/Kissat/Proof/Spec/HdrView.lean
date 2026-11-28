/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
public import LeanQbe.T.Logic.C0Agrees

/-!
# Kissat `FullHdr` Static Layout View & Framing Algebra (`Proof.Spec.HdrView`)

Additive zero-cache-bust leaf replacing raw `ws[0]? = some ... ∧ ... ∧ ws[113]? = some ...`
positional list-index conjunctions and `List.getElem?_set_ne` chains with:
1. `HdrField`: `48`-constructor enum covering all static pointer/capacity header tail slots.
2. `HdrView`: named `48`-field layout view with `HdrView.decode`, `HdrView.ofCfg`, `HdrView.get`,
   and `HdrView.set`.
3. `@[simp]` projection, round-trip (`HdrView.decode_ofCfg`), and single-word update preservation
   lemmas (`HdrView.decode_set`, `HdrView.decode_set_of_none`).
4. `HdrModifies` / `HdrWsModifies`: lightweight framing predicates with `refl`, `trans`, `mono`,
   `set`, and `get_of_not_mem` lemmas.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Spec

open LeanQbe.T

/-! ## 1. `HdrField` Enum & Index Mapping (`48` Static Header Tail Words) -/

/-- Named descriptor for the `48` static pointer/capacity `u64` slots in `FullHdr` tail
(`hdrTailWords`, words `0..113` relative to `c.hdr + 32`, i.e., `FullHdr` words `4..117`). -/
inductive HdrField where
  | arenaCap | wcap
  | pVals | pMark | pLevel | pReason | pTrail | pWvec | pArena | pWstk | pDelayed | pTmp
  | pHeap | pPos | pScore | pPhases | pMinStk | pMinClr | minDepth
  | pTrailPos | pQPrev | pQNext | pQStamp | pPhasesTarget | pPhasesBest | pWsort | pShrinkStk
  | pRedRefs | pGlueUsed | redCap | delayedCap
  | pFlags | pLitMark | pRepr | pSimSig | pFrameTrail | pFrameDec | pWorkStk1 | pWorkStk2
  | pTarjanMark | pTarjanReach | pWalkVals | pWalkBest | pExtendStk | extendCap
  | pScratchBuf | scratchCap | pLastLearned
  deriving DecidableEq, Repr

namespace HdrField

/-- Word index inside the `140`-word `hdrTailWords` array (`c.hdr + 32`). -/
@[expose] def tailIdx : HdrField → Nat
  | .arenaCap => 0 | .wcap => 1
  | .pVals => 4 | .pMark => 5 | .pLevel => 6 | .pReason => 7 | .pTrail => 8
  | .pWvec => 9 | .pArena => 10 | .pWstk => 11 | .pDelayed => 12 | .pTmp => 13
  | .pHeap => 21 | .pPos => 22 | .pScore => 23 | .pPhases => 24
  | .pMinStk => 25 | .pMinClr => 26 | .minDepth => 29
  | .pTrailPos => 41 | .pQPrev => 42 | .pQNext => 43 | .pQStamp => 44
  | .pPhasesTarget => 45 | .pPhasesBest => 46 | .pWsort => 47 | .pShrinkStk => 48
  | .pRedRefs => 49 | .pGlueUsed => 50 | .redCap => 51 | .delayedCap => 52
  | .pFlags => 96 | .pLitMark => 97 | .pRepr => 98 | .pSimSig => 99
  | .pFrameTrail => 100 | .pFrameDec => 101 | .pWorkStk1 => 102 | .pWorkStk2 => 103
  | .pTarjanMark => 104 | .pTarjanReach => 105 | .pWalkVals => 106 | .pWalkBest => 107
  | .pExtendStk => 108 | .extendCap => 109 | .pScratchBuf => 111
  | .scratchCap => 112 | .pLastLearned => 113

/-- Inverse lookup from `hdrTailWords` index (`0..113`) to `HdrField`. -/
@[expose] def ofTailIdx? : Nat → Option HdrField
  | 0 => some .arenaCap | 1 => some .wcap
  | 4 => some .pVals | 5 => some .pMark | 6 => some .pLevel | 7 => some .pReason
  | 8 => some .pTrail | 9 => some .pWvec | 10 => some .pArena | 11 => some .pWstk
  | 12 => some .pDelayed | 13 => some .pTmp
  | 21 => some .pHeap | 22 => some .pPos | 23 => some .pScore | 24 => some .pPhases
  | 25 => some .pMinStk | 26 => some .pMinClr | 29 => some .minDepth
  | 41 => some .pTrailPos | 42 => some .pQPrev | 43 => some .pQNext | 44 => some .pQStamp
  | 45 => some .pPhasesTarget | 46 => some .pPhasesBest | 47 => some .pWsort
  | 48 => some .pShrinkStk | 49 => some .pRedRefs | 50 => some .pGlueUsed
  | 51 => some .redCap | 52 => some .delayedCap
  | 96 => some .pFlags | 97 => some .pLitMark | 98 => some .pRepr | 99 => some .pSimSig
  | 100 => some .pFrameTrail | 101 => some .pFrameDec | 102 => some .pWorkStk1
  | 103 => some .pWorkStk2 | 104 => some .pTarjanMark | 105 => some .pTarjanReach
  | 106 => some .pWalkVals | 107 => some .pWalkBest | 108 => some .pExtendStk
  | 109 => some .extendCap | 111 => some .pScratchBuf | 112 => some .scratchCap
  | 113 => some .pLastLearned
  | _ => none

/-- Dense `0..47` position of a `HdrField` in `HdrView.toList`. -/
@[expose] def idx : HdrField → Nat
  | .arenaCap => 0 | .wcap => 1 | .pVals => 2 | .pMark => 3 | .pLevel => 4
  | .pReason => 5 | .pTrail => 6 | .pWvec => 7 | .pArena => 8 | .pWstk => 9
  | .pDelayed => 10 | .pTmp => 11 | .pHeap => 12 | .pPos => 13 | .pScore => 14
  | .pPhases => 15 | .pMinStk => 16 | .pMinClr => 17 | .minDepth => 18 | .pTrailPos => 19
  | .pQPrev => 20 | .pQNext => 21 | .pQStamp => 22 | .pPhasesTarget => 23 | .pPhasesBest => 24
  | .pWsort => 25 | .pShrinkStk => 26 | .pRedRefs => 27 | .pGlueUsed => 28 | .redCap => 29
  | .delayedCap => 30 | .pFlags => 31 | .pLitMark => 32 | .pRepr => 33 | .pSimSig => 34
  | .pFrameTrail => 35 | .pFrameDec => 36 | .pWorkStk1 => 37 | .pWorkStk2 => 38
  | .pTarjanMark => 39 | .pTarjanReach => 40 | .pWalkVals => 41 | .pWalkBest => 42
  | .pExtendStk => 43 | .extendCap => 44 | .pScratchBuf => 45 | .scratchCap => 46
  | .pLastLearned => 47

/-- Inverse of `HdrField.idx` for `O(N)` injectivity. -/
@[expose] def ofIdx? : Nat → Option HdrField
  | 0 => some .arenaCap | 1 => some .wcap | 2 => some .pVals | 3 => some .pMark
  | 4 => some .pLevel | 5 => some .pReason | 6 => some .pTrail | 7 => some .pWvec
  | 8 => some .pArena | 9 => some .pWstk | 10 => some .pDelayed | 11 => some .pTmp
  | 12 => some .pHeap | 13 => some .pPos | 14 => some .pScore | 15 => some .pPhases
  | 16 => some .pMinStk | 17 => some .pMinClr | 18 => some .minDepth | 19 => some .pTrailPos
  | 20 => some .pQPrev | 21 => some .pQNext | 22 => some .pQStamp | 23 => some .pPhasesTarget
  | 24 => some .pPhasesBest | 25 => some .pWsort | 26 => some .pShrinkStk | 27 => some .pRedRefs
  | 28 => some .pGlueUsed | 29 => some .redCap | 30 => some .delayedCap | 31 => some .pFlags
  | 32 => some .pLitMark | 33 => some .pRepr | 34 => some .pSimSig | 35 => some .pFrameTrail
  | 36 => some .pFrameDec | 37 => some .pWorkStk1 | 38 => some .pWorkStk2
  | 39 => some .pTarjanMark | 40 => some .pTarjanReach | 41 => some .pWalkVals
  | 42 => some .pWalkBest | 43 => some .pExtendStk | 44 => some .extendCap
  | 45 => some .pScratchBuf | 46 => some .scratchCap | 47 => some .pLastLearned
  | _ => none

/-- Bridge to the canonical `144`-word `HdrWordField` table in `Proof.Spec.Arena`. -/
@[expose] def toHdrWordField : HdrField → HdrWordField
  | .arenaCap => .arena_cap | .wcap => .wcap
  | .pVals => .values_ptr | .pMark => .mark_ptr | .pLevel => .level_ptr
  | .pReason => .reason_ptr | .pTrail => .trail_ptr | .pWvec => .watch_vec_ptr
  | .pArena => .arena_ptr | .pWstk => .watch_stk_ptr | .pDelayed => .delayed_ptr
  | .pTmp => .tmp_lits_ptr | .pHeap => .heap_ptr | .pPos => .pos_ptr | .pScore => .score_ptr
  | .pPhases => .phases_ptr | .pMinStk => .min_stk_ptr | .pMinClr => .min_clr_ptr
  | .minDepth => .min_depth | .pTrailPos => .trail_pos_ptr | .pQPrev => .q_prev_ptr
  | .pQNext => .q_next_ptr | .pQStamp => .q_stamp_ptr | .pPhasesTarget => .phases_target_ptr
  | .pPhasesBest => .phases_best_ptr | .pWsort => .wsort_ptr | .pShrinkStk => .shrink_stk_ptr
  | .pRedRefs => .red_refs_ptr | .pGlueUsed => .glue_used_ptr | .redCap => .red_cap
  | .delayedCap => .delayed_cap | .pFlags => .flags_ptr | .pLitMark => .lit_mark_ptr
  | .pRepr => .repr_ptr | .pSimSig => .sim_sig_ptr | .pFrameTrail => .frame_trail_ptr
  | .pFrameDec => .frame_dec_ptr | .pWorkStk1 => .work_stk1_ptr | .pWorkStk2 => .work_stk2_ptr
  | .pTarjanMark => .tarjan_mark_ptr | .pTarjanReach => .tarjan_reach_ptr
  | .pWalkVals => .walk_vals_ptr | .pWalkBest => .walk_best_ptr
  | .pExtendStk => .extend_stk_ptr | .extendCap => .extend_cap
  | .pScratchBuf => .scratch_buf_ptr | .scratchCap => .scratch_cap
  | .pLastLearned => .last_learned_ptr

/-- Complete list of all `48` `HdrField` constructors. -/
@[expose] def all : List HdrField :=
  [ .arenaCap, .wcap, .pVals, .pMark, .pLevel, .pReason, .pTrail, .pWvec, .pArena, .pWstk,
    .pDelayed, .pTmp, .pHeap, .pPos, .pScore, .pPhases, .pMinStk, .pMinClr, .minDepth,
    .pTrailPos, .pQPrev, .pQNext, .pQStamp, .pPhasesTarget, .pPhasesBest, .pWsort, .pShrinkStk,
    .pRedRefs, .pGlueUsed, .redCap, .delayedCap, .pFlags, .pLitMark, .pRepr, .pSimSig,
    .pFrameTrail, .pFrameDec, .pWorkStk1, .pWorkStk2, .pTarjanMark, .pTarjanReach, .pWalkVals,
    .pWalkBest, .pExtendStk, .extendCap, .pScratchBuf, .scratchCap, .pLastLearned ]

/-- The `11` dynamic arena/buffer fields preserved by `full_init_ptrs`. -/
@[expose] def arenaDynFields : List HdrField :=
  [ .arenaCap, .wcap, .pWstk, .pDelayed, .pRedRefs, .redCap, .delayedCap,
    .pExtendStk, .extendCap, .pScratchBuf, .scratchCap ]

/-- The `37` fixed pointer/depth fields initialized by `full_init_ptrs`. -/
@[expose] def fixedPtrFields : List HdrField :=
  all.filter (· ∉ arenaDynFields)

theorem tailIdx_lt (f : HdrField) : f.tailIdx < 114 := by cases f <;> decide
theorem idx_lt (f : HdrField) : f.idx < 48 := by cases f <;> decide
theorem ofTailIdx?_tailIdx (f : HdrField) : ofTailIdx? f.tailIdx = some f := by cases f <;> rfl
theorem ofIdx?_idx (f : HdrField) : ofIdx? f.idx = some f := by cases f <;> rfl
theorem mem_all (f : HdrField) : f ∈ all := by cases f <;> decide

theorem tailIdx_inj {f g : HdrField} (h : f.tailIdx = g.tailIdx) : f = g := by
  have h1 := congrArg ofTailIdx? h
  rw [ofTailIdx?_tailIdx, ofTailIdx?_tailIdx] at h1
  exact Option.some.inj h1

theorem idx_inj {f g : HdrField} (h : f.idx = g.idx) : f = g := by
  have h1 := congrArg ofIdx? h
  rw [ofIdx?_idx, ofIdx?_idx] at h1
  exact Option.some.inj h1

theorem ofTailIdx?_eq_none_tailIdx_ne {idx : Nat} (hnone : ofTailIdx? idx = none)
    (f : HdrField) : f.tailIdx ≠ idx := by
  intro heq; rw [← heq, ofTailIdx?_tailIdx] at hnone; cases hnone

theorem toHdrWordField_wordIdx (f : HdrField) : f.toHdrWordField.wordIdx = f.tailIdx + 4 := by
  cases f <;> rfl

theorem not_mem_fixedPtrFields_iff (f : HdrField) :
    f ∉ fixedPtrFields ↔ f ∈ arenaDynFields := by
  simp [fixedPtrFields, mem_all f]

theorem not_mem_arenaDynFields_iff (f : HdrField) :
    f ∉ arenaDynFields ↔ f ∈ fixedPtrFields := by
  simp [fixedPtrFields, mem_all f]

end HdrField

/-! ## 2. `HdrView` Structure, `decode`, `ofCfg`, `get` & `set` -/

/-- Named layout view of the `48` static pointer/capacity slots in `FullHdr` tail (`ws`). -/
structure HdrView where
  arenaCap : BitVec 64
  wcap : BitVec 64
  pVals : BitVec 64
  pMark : BitVec 64
  pLevel : BitVec 64
  pReason : BitVec 64
  pTrail : BitVec 64
  pWvec : BitVec 64
  pArena : BitVec 64
  pWstk : BitVec 64
  pDelayed : BitVec 64
  pTmp : BitVec 64
  pHeap : BitVec 64
  pPos : BitVec 64
  pScore : BitVec 64
  pPhases : BitVec 64
  pMinStk : BitVec 64
  pMinClr : BitVec 64
  minDepth : BitVec 64
  pTrailPos : BitVec 64
  pQPrev : BitVec 64
  pQNext : BitVec 64
  pQStamp : BitVec 64
  pPhasesTarget : BitVec 64
  pPhasesBest : BitVec 64
  pWsort : BitVec 64
  pShrinkStk : BitVec 64
  pRedRefs : BitVec 64
  pGlueUsed : BitVec 64
  redCap : BitVec 64
  delayedCap : BitVec 64
  pFlags : BitVec 64
  pLitMark : BitVec 64
  pRepr : BitVec 64
  pSimSig : BitVec 64
  pFrameTrail : BitVec 64
  pFrameDec : BitVec 64
  pWorkStk1 : BitVec 64
  pWorkStk2 : BitVec 64
  pTarjanMark : BitVec 64
  pTarjanReach : BitVec 64
  pWalkVals : BitVec 64
  pWalkBest : BitVec 64
  pExtendStk : BitVec 64
  extendCap : BitVec 64
  pScratchBuf : BitVec 64
  scratchCap : BitVec 64
  pLastLearned : BitVec 64
  deriving DecidableEq, Repr

namespace HdrView

/-- Read a named `HdrField` from `HdrView`. -/
@[expose] def get (v : HdrView) : HdrField → BitVec 64
  | .arenaCap => v.arenaCap | .wcap => v.wcap
  | .pVals => v.pVals | .pMark => v.pMark | .pLevel => v.pLevel | .pReason => v.pReason
  | .pTrail => v.pTrail | .pWvec => v.pWvec | .pArena => v.pArena | .pWstk => v.pWstk
  | .pDelayed => v.pDelayed | .pTmp => v.pTmp | .pHeap => v.pHeap | .pPos => v.pPos
  | .pScore => v.pScore | .pPhases => v.pPhases | .pMinStk => v.pMinStk
  | .pMinClr => v.pMinClr | .minDepth => v.minDepth | .pTrailPos => v.pTrailPos
  | .pQPrev => v.pQPrev | .pQNext => v.pQNext | .pQStamp => v.pQStamp
  | .pPhasesTarget => v.pPhasesTarget | .pPhasesBest => v.pPhasesBest
  | .pWsort => v.pWsort | .pShrinkStk => v.pShrinkStk | .pRedRefs => v.pRedRefs
  | .pGlueUsed => v.pGlueUsed | .redCap => v.redCap | .delayedCap => v.delayedCap
  | .pFlags => v.pFlags | .pLitMark => v.pLitMark | .pRepr => v.pRepr | .pSimSig => v.pSimSig
  | .pFrameTrail => v.pFrameTrail | .pFrameDec => v.pFrameDec | .pWorkStk1 => v.pWorkStk1
  | .pWorkStk2 => v.pWorkStk2 | .pTarjanMark => v.pTarjanMark
  | .pTarjanReach => v.pTarjanReach | .pWalkVals => v.pWalkVals | .pWalkBest => v.pWalkBest
  | .pExtendStk => v.pExtendStk | .extendCap => v.extendCap
  | .pScratchBuf => v.pScratchBuf | .scratchCap => v.scratchCap
  | .pLastLearned => v.pLastLearned

/-- Functional single-field update on `HdrView`. -/
@[expose] def set (v : HdrView) (f : HdrField) (w : BitVec 64) : HdrView :=
  match f with
  | .arenaCap => { v with arenaCap := w } | .wcap => { v with wcap := w }
  | .pVals => { v with pVals := w } | .pMark => { v with pMark := w }
  | .pLevel => { v with pLevel := w } | .pReason => { v with pReason := w }
  | .pTrail => { v with pTrail := w } | .pWvec => { v with pWvec := w }
  | .pArena => { v with pArena := w } | .pWstk => { v with pWstk := w }
  | .pDelayed => { v with pDelayed := w } | .pTmp => { v with pTmp := w }
  | .pHeap => { v with pHeap := w } | .pPos => { v with pPos := w }
  | .pScore => { v with pScore := w } | .pPhases => { v with pPhases := w }
  | .pMinStk => { v with pMinStk := w } | .pMinClr => { v with pMinClr := w }
  | .minDepth => { v with minDepth := w } | .pTrailPos => { v with pTrailPos := w }
  | .pQPrev => { v with pQPrev := w } | .pQNext => { v with pQNext := w }
  | .pQStamp => { v with pQStamp := w } | .pPhasesTarget => { v with pPhasesTarget := w }
  | .pPhasesBest => { v with pPhasesBest := w } | .pWsort => { v with pWsort := w }
  | .pShrinkStk => { v with pShrinkStk := w } | .pRedRefs => { v with pRedRefs := w }
  | .pGlueUsed => { v with pGlueUsed := w } | .redCap => { v with redCap := w }
  | .delayedCap => { v with delayedCap := w } | .pFlags => { v with pFlags := w }
  | .pLitMark => { v with pLitMark := w } | .pRepr => { v with pRepr := w }
  | .pSimSig => { v with pSimSig := w } | .pFrameTrail => { v with pFrameTrail := w }
  | .pFrameDec => { v with pFrameDec := w } | .pWorkStk1 => { v with pWorkStk1 := w }
  | .pWorkStk2 => { v with pWorkStk2 := w } | .pTarjanMark => { v with pTarjanMark := w }
  | .pTarjanReach => { v with pTarjanReach := w } | .pWalkVals => { v with pWalkVals := w }
  | .pWalkBest => { v with pWalkBest := w } | .pExtendStk => { v with pExtendStk := w }
  | .extendCap => { v with extendCap := w } | .pScratchBuf => { v with pScratchBuf := w }
  | .scratchCap => { v with scratchCap := w } | .pLastLearned => { v with pLastLearned := w }

/-- Flat `48`-element list representation of `HdrView` for `O(N)` `get_set_ne`. -/
@[expose] def toList (v : HdrView) : List (BitVec 64) :=
  [ v.arenaCap, v.wcap, v.pVals, v.pMark, v.pLevel, v.pReason, v.pTrail, v.pWvec, v.pArena,
    v.pWstk, v.pDelayed, v.pTmp, v.pHeap, v.pPos, v.pScore, v.pPhases, v.pMinStk, v.pMinClr,
    v.minDepth, v.pTrailPos, v.pQPrev, v.pQNext, v.pQStamp, v.pPhasesTarget, v.pPhasesBest,
    v.pWsort, v.pShrinkStk, v.pRedRefs, v.pGlueUsed, v.redCap, v.delayedCap, v.pFlags,
    v.pLitMark, v.pRepr, v.pSimSig, v.pFrameTrail, v.pFrameDec, v.pWorkStk1, v.pWorkStk2,
    v.pTarjanMark, v.pTarjanReach, v.pWalkVals, v.pWalkBest, v.pExtendStk, v.extendCap,
    v.pScratchBuf, v.scratchCap, v.pLastLearned ]

/-- Expected `HdrView` derived from static `FullCfg`. -/
@[expose] def ofCfg (c : FullCfg) : HdrView where
  arenaCap := BitVec.ofNat 64 c.arena_cap
  wcap := BitVec.ofNat 64 c.wcap
  pVals := c.pVals
  pMark := c.pMark
  pLevel := c.pLevel
  pReason := c.pReason
  pTrail := c.pTrail
  pWvec := c.pWvec
  pArena := c.pArena
  pWstk := c.pWstk
  pDelayed := c.pDelayed
  pTmp := c.pTmp
  pHeap := c.pHeap
  pPos := c.pPos
  pScore := c.pScore
  pPhases := c.pPhases
  pMinStk := c.pMinStk
  pMinClr := c.pMinClr
  minDepth := BitVec.ofNat 64 c.minDepth
  pTrailPos := c.pTrailPos
  pQPrev := c.pQPrev
  pQNext := c.pQNext
  pQStamp := c.pQStamp
  pPhasesTarget := c.pPhasesTarget
  pPhasesBest := c.pPhasesBest
  pWsort := c.pWsort
  pShrinkStk := c.pShrinkStk
  pRedRefs := c.pRedRefs
  pGlueUsed := c.pGlueUsed
  redCap := BitVec.ofNat 64 c.red_cap
  delayedCap := BitVec.ofNat 64 c.delayed_cap
  pFlags := c.pFlags
  pLitMark := c.pLitMark
  pRepr := c.pRepr
  pSimSig := c.pSimSig
  pFrameTrail := c.pFrameTrail
  pFrameDec := c.pFrameDec
  pWorkStk1 := c.pWorkStk1
  pWorkStk2 := c.pWorkStk2
  pTarjanMark := c.pTarjanMark
  pTarjanReach := c.pTarjanReach
  pWalkVals := c.pWalkVals
  pWalkBest := c.pWalkBest
  pExtendStk := c.pExtendStk
  extendCap := BitVec.ofNat 64 c.extend_cap
  pScratchBuf := c.pScratchBuf
  scratchCap := BitVec.ofNat 64 c.scratch_cap
  pLastLearned := c.pLastLearned

/-- Decode `HdrView` from a `FullHdr` tail word list (`c.hdr + 32`); returns `none` if
`ws.length < 114`. -/
@[expose] def decode (ws : List (BitVec 64)) : Option HdrView :=
  if h : 114 ≤ ws.length then
    some
      { arenaCap := ws[0]'(by omega), wcap := ws[1]'(by omega)
        pVals := ws[4]'(by omega), pMark := ws[5]'(by omega)
        pLevel := ws[6]'(by omega), pReason := ws[7]'(by omega)
        pTrail := ws[8]'(by omega), pWvec := ws[9]'(by omega)
        pArena := ws[10]'(by omega), pWstk := ws[11]'(by omega)
        pDelayed := ws[12]'(by omega), pTmp := ws[13]'(by omega)
        pHeap := ws[21]'(by omega), pPos := ws[22]'(by omega)
        pScore := ws[23]'(by omega), pPhases := ws[24]'(by omega)
        pMinStk := ws[25]'(by omega), pMinClr := ws[26]'(by omega)
        minDepth := ws[29]'(by omega), pTrailPos := ws[41]'(by omega)
        pQPrev := ws[42]'(by omega), pQNext := ws[43]'(by omega)
        pQStamp := ws[44]'(by omega), pPhasesTarget := ws[45]'(by omega)
        pPhasesBest := ws[46]'(by omega), pWsort := ws[47]'(by omega)
        pShrinkStk := ws[48]'(by omega), pRedRefs := ws[49]'(by omega)
        pGlueUsed := ws[50]'(by omega), redCap := ws[51]'(by omega)
        delayedCap := ws[52]'(by omega), pFlags := ws[96]'(by omega)
        pLitMark := ws[97]'(by omega), pRepr := ws[98]'(by omega)
        pSimSig := ws[99]'(by omega), pFrameTrail := ws[100]'(by omega)
        pFrameDec := ws[101]'(by omega), pWorkStk1 := ws[102]'(by omega)
        pWorkStk2 := ws[103]'(by omega), pTarjanMark := ws[104]'(by omega)
        pTarjanReach := ws[105]'(by omega), pWalkVals := ws[106]'(by omega)
        pWalkBest := ws[107]'(by omega), pExtendStk := ws[108]'(by omega)
        extendCap := ws[109]'(by omega), pScratchBuf := ws[111]'(by omega)
        scratchCap := ws[112]'(by omega), pLastLearned := ws[113]'(by omega) }
  else
    none

/-! ## 3. `@[simp]` Projection, Round-Trip & Single-Word Update Lemmas -/

theorem toList_length (v : HdrView) : v.toList.length = 48 := rfl

theorem get_eq_toList (v : HdrView) (f : HdrField) :
    v.get f = v.toList[f.idx]'(by rw [toList_length]; exact f.idx_lt) := by
  cases f <;> rfl

theorem toList_set (v : HdrView) (f : HdrField) (w : BitVec 64) :
    (v.set f w).toList = v.toList.set f.idx w := by
  cases f <;> rfl

theorem ext_get {v1 v2 : HdrView} (h : ∀ f : HdrField, v1.get f = v2.get f) : v1 = v2 := by
  cases v1; cases v2; congr 1
  · exact h .arenaCap
  · exact h .wcap
  · exact h .pVals
  · exact h .pMark
  · exact h .pLevel
  · exact h .pReason
  · exact h .pTrail
  · exact h .pWvec
  · exact h .pArena
  · exact h .pWstk
  · exact h .pDelayed
  · exact h .pTmp
  · exact h .pHeap
  · exact h .pPos
  · exact h .pScore
  · exact h .pPhases
  · exact h .pMinStk
  · exact h .pMinClr
  · exact h .minDepth
  · exact h .pTrailPos
  · exact h .pQPrev
  · exact h .pQNext
  · exact h .pQStamp
  · exact h .pPhasesTarget
  · exact h .pPhasesBest
  · exact h .pWsort
  · exact h .pShrinkStk
  · exact h .pRedRefs
  · exact h .pGlueUsed
  · exact h .redCap
  · exact h .delayedCap
  · exact h .pFlags
  · exact h .pLitMark
  · exact h .pRepr
  · exact h .pSimSig
  · exact h .pFrameTrail
  · exact h .pFrameDec
  · exact h .pWorkStk1
  · exact h .pWorkStk2
  · exact h .pTarjanMark
  · exact h .pTarjanReach
  · exact h .pWalkVals
  · exact h .pWalkBest
  · exact h .pExtendStk
  · exact h .extendCap
  · exact h .pScratchBuf
  · exact h .scratchCap
  · exact h .pLastLearned

@[simp] theorem get_set_self (v : HdrView) (f : HdrField) (w : BitVec 64) :
    (v.set f w).get f = w := by
  cases f <;> rfl

@[simp] theorem get_set_ne (v : HdrView) {f g : HdrField} (hne : f ≠ g) (w : BitVec 64) :
    (v.set f w).get g = v.get g := by
  have hidx : f.idx ≠ g.idx := fun h => hne (HdrField.idx_inj h)
  rw [get_eq_toList, get_eq_toList]
  simp [toList_set, List.getElem_set_ne, hidx]

@[simp] theorem decode_ofCfg (c : FullCfg) (s : FullState) :
    decode (hdrTailWords c s) = some (ofCfg c) := rfl

theorem toHdrWordField_get (c : FullCfg) (s : FullState) (f : HdrField) :
    f.toHdrWordField.get c s = (ofCfg c).get f := by
  cases f <;> rfl

@[simp] theorem get_arenaCap (v : HdrView) : v.get .arenaCap = v.arenaCap := rfl
@[simp] theorem get_wcap (v : HdrView) : v.get .wcap = v.wcap := rfl
@[simp] theorem get_pVals (v : HdrView) : v.get .pVals = v.pVals := rfl
@[simp] theorem get_pMark (v : HdrView) : v.get .pMark = v.pMark := rfl
@[simp] theorem get_pLevel (v : HdrView) : v.get .pLevel = v.pLevel := rfl
@[simp] theorem get_pReason (v : HdrView) : v.get .pReason = v.pReason := rfl
@[simp] theorem get_pTrail (v : HdrView) : v.get .pTrail = v.pTrail := rfl
@[simp] theorem get_pWvec (v : HdrView) : v.get .pWvec = v.pWvec := rfl
@[simp] theorem get_pArena (v : HdrView) : v.get .pArena = v.pArena := rfl
@[simp] theorem get_pWstk (v : HdrView) : v.get .pWstk = v.pWstk := rfl
@[simp] theorem get_pDelayed (v : HdrView) : v.get .pDelayed = v.pDelayed := rfl
@[simp] theorem get_pTmp (v : HdrView) : v.get .pTmp = v.pTmp := rfl
@[simp] theorem get_pHeap (v : HdrView) : v.get .pHeap = v.pHeap := rfl
@[simp] theorem get_pPos (v : HdrView) : v.get .pPos = v.pPos := rfl
@[simp] theorem get_pScore (v : HdrView) : v.get .pScore = v.pScore := rfl
@[simp] theorem get_pPhases (v : HdrView) : v.get .pPhases = v.pPhases := rfl
@[simp] theorem get_pMinStk (v : HdrView) : v.get .pMinStk = v.pMinStk := rfl
@[simp] theorem get_pMinClr (v : HdrView) : v.get .pMinClr = v.pMinClr := rfl
@[simp] theorem get_minDepth (v : HdrView) : v.get .minDepth = v.minDepth := rfl
@[simp] theorem get_pTrailPos (v : HdrView) : v.get .pTrailPos = v.pTrailPos := rfl
@[simp] theorem get_pQPrev (v : HdrView) : v.get .pQPrev = v.pQPrev := rfl
@[simp] theorem get_pQNext (v : HdrView) : v.get .pQNext = v.pQNext := rfl
@[simp] theorem get_pQStamp (v : HdrView) : v.get .pQStamp = v.pQStamp := rfl
@[simp] theorem get_pPhasesTarget (v : HdrView) : v.get .pPhasesTarget = v.pPhasesTarget := rfl
@[simp] theorem get_pPhasesBest (v : HdrView) : v.get .pPhasesBest = v.pPhasesBest := rfl
@[simp] theorem get_pWsort (v : HdrView) : v.get .pWsort = v.pWsort := rfl
@[simp] theorem get_pShrinkStk (v : HdrView) : v.get .pShrinkStk = v.pShrinkStk := rfl
@[simp] theorem get_pRedRefs (v : HdrView) : v.get .pRedRefs = v.pRedRefs := rfl
@[simp] theorem get_pGlueUsed (v : HdrView) : v.get .pGlueUsed = v.pGlueUsed := rfl
@[simp] theorem get_redCap (v : HdrView) : v.get .redCap = v.redCap := rfl
@[simp] theorem get_delayedCap (v : HdrView) : v.get .delayedCap = v.delayedCap := rfl
@[simp] theorem get_pFlags (v : HdrView) : v.get .pFlags = v.pFlags := rfl
@[simp] theorem get_pLitMark (v : HdrView) : v.get .pLitMark = v.pLitMark := rfl
@[simp] theorem get_pRepr (v : HdrView) : v.get .pRepr = v.pRepr := rfl
@[simp] theorem get_pSimSig (v : HdrView) : v.get .pSimSig = v.pSimSig := rfl
@[simp] theorem get_pFrameTrail (v : HdrView) : v.get .pFrameTrail = v.pFrameTrail := rfl
@[simp] theorem get_pFrameDec (v : HdrView) : v.get .pFrameDec = v.pFrameDec := rfl
@[simp] theorem get_pWorkStk1 (v : HdrView) : v.get .pWorkStk1 = v.pWorkStk1 := rfl
@[simp] theorem get_pWorkStk2 (v : HdrView) : v.get .pWorkStk2 = v.pWorkStk2 := rfl
@[simp] theorem get_pTarjanMark (v : HdrView) : v.get .pTarjanMark = v.pTarjanMark := rfl
@[simp] theorem get_pTarjanReach (v : HdrView) : v.get .pTarjanReach = v.pTarjanReach := rfl
@[simp] theorem get_pWalkVals (v : HdrView) : v.get .pWalkVals = v.pWalkVals := rfl
@[simp] theorem get_pWalkBest (v : HdrView) : v.get .pWalkBest = v.pWalkBest := rfl
@[simp] theorem get_pExtendStk (v : HdrView) : v.get .pExtendStk = v.pExtendStk := rfl
@[simp] theorem get_extendCap (v : HdrView) : v.get .extendCap = v.extendCap := rfl
@[simp] theorem get_pScratchBuf (v : HdrView) : v.get .pScratchBuf = v.pScratchBuf := rfl
@[simp] theorem get_scratchCap (v : HdrView) : v.get .scratchCap = v.scratchCap := rfl
@[simp] theorem get_pLastLearned (v : HdrView) : v.get .pLastLearned = v.pLastLearned := rfl

@[simp] theorem set_arenaCap (v : HdrView) (w : BitVec 64) :
    v.set .arenaCap w = { v with arenaCap := w } := rfl
@[simp] theorem set_wcap (v : HdrView) (w : BitVec 64) :
    v.set .wcap w = { v with wcap := w } := rfl
@[simp] theorem set_pVals (v : HdrView) (w : BitVec 64) :
    v.set .pVals w = { v with pVals := w } := rfl
@[simp] theorem set_pMark (v : HdrView) (w : BitVec 64) :
    v.set .pMark w = { v with pMark := w } := rfl
@[simp] theorem set_pLevel (v : HdrView) (w : BitVec 64) :
    v.set .pLevel w = { v with pLevel := w } := rfl
@[simp] theorem set_pReason (v : HdrView) (w : BitVec 64) :
    v.set .pReason w = { v with pReason := w } := rfl
@[simp] theorem set_pTrail (v : HdrView) (w : BitVec 64) :
    v.set .pTrail w = { v with pTrail := w } := rfl
@[simp] theorem set_pWvec (v : HdrView) (w : BitVec 64) :
    v.set .pWvec w = { v with pWvec := w } := rfl
@[simp] theorem set_pArena (v : HdrView) (w : BitVec 64) :
    v.set .pArena w = { v with pArena := w } := rfl
@[simp] theorem set_pWstk (v : HdrView) (w : BitVec 64) :
    v.set .pWstk w = { v with pWstk := w } := rfl
@[simp] theorem set_pDelayed (v : HdrView) (w : BitVec 64) :
    v.set .pDelayed w = { v with pDelayed := w } := rfl
@[simp] theorem set_pTmp (v : HdrView) (w : BitVec 64) :
    v.set .pTmp w = { v with pTmp := w } := rfl
@[simp] theorem set_pHeap (v : HdrView) (w : BitVec 64) :
    v.set .pHeap w = { v with pHeap := w } := rfl
@[simp] theorem set_pPos (v : HdrView) (w : BitVec 64) :
    v.set .pPos w = { v with pPos := w } := rfl
@[simp] theorem set_pScore (v : HdrView) (w : BitVec 64) :
    v.set .pScore w = { v with pScore := w } := rfl
@[simp] theorem set_pPhases (v : HdrView) (w : BitVec 64) :
    v.set .pPhases w = { v with pPhases := w } := rfl
@[simp] theorem set_pMinStk (v : HdrView) (w : BitVec 64) :
    v.set .pMinStk w = { v with pMinStk := w } := rfl
@[simp] theorem set_pMinClr (v : HdrView) (w : BitVec 64) :
    v.set .pMinClr w = { v with pMinClr := w } := rfl
@[simp] theorem set_minDepth (v : HdrView) (w : BitVec 64) :
    v.set .minDepth w = { v with minDepth := w } := rfl
@[simp] theorem set_pTrailPos (v : HdrView) (w : BitVec 64) :
    v.set .pTrailPos w = { v with pTrailPos := w } := rfl
@[simp] theorem set_pQPrev (v : HdrView) (w : BitVec 64) :
    v.set .pQPrev w = { v with pQPrev := w } := rfl
@[simp] theorem set_pQNext (v : HdrView) (w : BitVec 64) :
    v.set .pQNext w = { v with pQNext := w } := rfl
@[simp] theorem set_pQStamp (v : HdrView) (w : BitVec 64) :
    v.set .pQStamp w = { v with pQStamp := w } := rfl
@[simp] theorem set_pPhasesTarget (v : HdrView) (w : BitVec 64) :
    v.set .pPhasesTarget w = { v with pPhasesTarget := w } := rfl
@[simp] theorem set_pPhasesBest (v : HdrView) (w : BitVec 64) :
    v.set .pPhasesBest w = { v with pPhasesBest := w } := rfl
@[simp] theorem set_pWsort (v : HdrView) (w : BitVec 64) :
    v.set .pWsort w = { v with pWsort := w } := rfl
@[simp] theorem set_pShrinkStk (v : HdrView) (w : BitVec 64) :
    v.set .pShrinkStk w = { v with pShrinkStk := w } := rfl
@[simp] theorem set_pRedRefs (v : HdrView) (w : BitVec 64) :
    v.set .pRedRefs w = { v with pRedRefs := w } := rfl
@[simp] theorem set_pGlueUsed (v : HdrView) (w : BitVec 64) :
    v.set .pGlueUsed w = { v with pGlueUsed := w } := rfl
@[simp] theorem set_redCap (v : HdrView) (w : BitVec 64) :
    v.set .redCap w = { v with redCap := w } := rfl
@[simp] theorem set_delayedCap (v : HdrView) (w : BitVec 64) :
    v.set .delayedCap w = { v with delayedCap := w } := rfl
@[simp] theorem set_pFlags (v : HdrView) (w : BitVec 64) :
    v.set .pFlags w = { v with pFlags := w } := rfl
@[simp] theorem set_pLitMark (v : HdrView) (w : BitVec 64) :
    v.set .pLitMark w = { v with pLitMark := w } := rfl
@[simp] theorem set_pRepr (v : HdrView) (w : BitVec 64) :
    v.set .pRepr w = { v with pRepr := w } := rfl
@[simp] theorem set_pSimSig (v : HdrView) (w : BitVec 64) :
    v.set .pSimSig w = { v with pSimSig := w } := rfl
@[simp] theorem set_pFrameTrail (v : HdrView) (w : BitVec 64) :
    v.set .pFrameTrail w = { v with pFrameTrail := w } := rfl
@[simp] theorem set_pFrameDec (v : HdrView) (w : BitVec 64) :
    v.set .pFrameDec w = { v with pFrameDec := w } := rfl
@[simp] theorem set_pWorkStk1 (v : HdrView) (w : BitVec 64) :
    v.set .pWorkStk1 w = { v with pWorkStk1 := w } := rfl
@[simp] theorem set_pWorkStk2 (v : HdrView) (w : BitVec 64) :
    v.set .pWorkStk2 w = { v with pWorkStk2 := w } := rfl
@[simp] theorem set_pTarjanMark (v : HdrView) (w : BitVec 64) :
    v.set .pTarjanMark w = { v with pTarjanMark := w } := rfl
@[simp] theorem set_pTarjanReach (v : HdrView) (w : BitVec 64) :
    v.set .pTarjanReach w = { v with pTarjanReach := w } := rfl
@[simp] theorem set_pWalkVals (v : HdrView) (w : BitVec 64) :
    v.set .pWalkVals w = { v with pWalkVals := w } := rfl
@[simp] theorem set_pWalkBest (v : HdrView) (w : BitVec 64) :
    v.set .pWalkBest w = { v with pWalkBest := w } := rfl
@[simp] theorem set_pExtendStk (v : HdrView) (w : BitVec 64) :
    v.set .pExtendStk w = { v with pExtendStk := w } := rfl
@[simp] theorem set_extendCap (v : HdrView) (w : BitVec 64) :
    v.set .extendCap w = { v with extendCap := w } := rfl
@[simp] theorem set_pScratchBuf (v : HdrView) (w : BitVec 64) :
    v.set .pScratchBuf w = { v with pScratchBuf := w } := rfl
@[simp] theorem set_scratchCap (v : HdrView) (w : BitVec 64) :
    v.set .scratchCap w = { v with scratchCap := w } := rfl
@[simp] theorem set_pLastLearned (v : HdrView) (w : BitVec 64) :
    v.set .pLastLearned w = { v with pLastLearned := w } := rfl

@[simp] theorem ofCfg_arenaCap (c : FullCfg) :
    (ofCfg c).arenaCap = BitVec.ofNat 64 c.arena_cap := rfl
@[simp] theorem ofCfg_wcap (c : FullCfg) : (ofCfg c).wcap = BitVec.ofNat 64 c.wcap := rfl
@[simp] theorem ofCfg_pVals (c : FullCfg) : (ofCfg c).pVals = c.pVals := rfl
@[simp] theorem ofCfg_pMark (c : FullCfg) : (ofCfg c).pMark = c.pMark := rfl
@[simp] theorem ofCfg_pLevel (c : FullCfg) : (ofCfg c).pLevel = c.pLevel := rfl
@[simp] theorem ofCfg_pReason (c : FullCfg) : (ofCfg c).pReason = c.pReason := rfl
@[simp] theorem ofCfg_pTrail (c : FullCfg) : (ofCfg c).pTrail = c.pTrail := rfl
@[simp] theorem ofCfg_pWvec (c : FullCfg) : (ofCfg c).pWvec = c.pWvec := rfl
@[simp] theorem ofCfg_pArena (c : FullCfg) : (ofCfg c).pArena = c.pArena := rfl
@[simp] theorem ofCfg_pWstk (c : FullCfg) : (ofCfg c).pWstk = c.pWstk := rfl
@[simp] theorem ofCfg_pDelayed (c : FullCfg) : (ofCfg c).pDelayed = c.pDelayed := rfl
@[simp] theorem ofCfg_pTmp (c : FullCfg) : (ofCfg c).pTmp = c.pTmp := rfl
@[simp] theorem ofCfg_pHeap (c : FullCfg) : (ofCfg c).pHeap = c.pHeap := rfl
@[simp] theorem ofCfg_pPos (c : FullCfg) : (ofCfg c).pPos = c.pPos := rfl
@[simp] theorem ofCfg_pScore (c : FullCfg) : (ofCfg c).pScore = c.pScore := rfl
@[simp] theorem ofCfg_pPhases (c : FullCfg) : (ofCfg c).pPhases = c.pPhases := rfl
@[simp] theorem ofCfg_pMinStk (c : FullCfg) : (ofCfg c).pMinStk = c.pMinStk := rfl
@[simp] theorem ofCfg_pMinClr (c : FullCfg) : (ofCfg c).pMinClr = c.pMinClr := rfl
@[simp] theorem ofCfg_minDepth (c : FullCfg) :
    (ofCfg c).minDepth = BitVec.ofNat 64 c.minDepth := rfl
@[simp] theorem ofCfg_pTrailPos (c : FullCfg) : (ofCfg c).pTrailPos = c.pTrailPos := rfl
@[simp] theorem ofCfg_pQPrev (c : FullCfg) : (ofCfg c).pQPrev = c.pQPrev := rfl
@[simp] theorem ofCfg_pQNext (c : FullCfg) : (ofCfg c).pQNext = c.pQNext := rfl
@[simp] theorem ofCfg_pQStamp (c : FullCfg) : (ofCfg c).pQStamp = c.pQStamp := rfl
@[simp] theorem ofCfg_pPhasesTarget (c : FullCfg) :
    (ofCfg c).pPhasesTarget = c.pPhasesTarget := rfl
@[simp] theorem ofCfg_pPhasesBest (c : FullCfg) :
    (ofCfg c).pPhasesBest = c.pPhasesBest := rfl
@[simp] theorem ofCfg_pWsort (c : FullCfg) : (ofCfg c).pWsort = c.pWsort := rfl
@[simp] theorem ofCfg_pShrinkStk (c : FullCfg) : (ofCfg c).pShrinkStk = c.pShrinkStk := rfl
@[simp] theorem ofCfg_pRedRefs (c : FullCfg) : (ofCfg c).pRedRefs = c.pRedRefs := rfl
@[simp] theorem ofCfg_pGlueUsed (c : FullCfg) : (ofCfg c).pGlueUsed = c.pGlueUsed := rfl
@[simp] theorem ofCfg_redCap (c : FullCfg) :
    (ofCfg c).redCap = BitVec.ofNat 64 c.red_cap := rfl
@[simp] theorem ofCfg_delayedCap (c : FullCfg) :
    (ofCfg c).delayedCap = BitVec.ofNat 64 c.delayed_cap := rfl
@[simp] theorem ofCfg_pFlags (c : FullCfg) : (ofCfg c).pFlags = c.pFlags := rfl
@[simp] theorem ofCfg_pLitMark (c : FullCfg) : (ofCfg c).pLitMark = c.pLitMark := rfl
@[simp] theorem ofCfg_pRepr (c : FullCfg) : (ofCfg c).pRepr = c.pRepr := rfl
@[simp] theorem ofCfg_pSimSig (c : FullCfg) : (ofCfg c).pSimSig = c.pSimSig := rfl
@[simp] theorem ofCfg_pFrameTrail (c : FullCfg) : (ofCfg c).pFrameTrail = c.pFrameTrail := rfl
@[simp] theorem ofCfg_pFrameDec (c : FullCfg) : (ofCfg c).pFrameDec = c.pFrameDec := rfl
@[simp] theorem ofCfg_pWorkStk1 (c : FullCfg) : (ofCfg c).pWorkStk1 = c.pWorkStk1 := rfl
@[simp] theorem ofCfg_pWorkStk2 (c : FullCfg) : (ofCfg c).pWorkStk2 = c.pWorkStk2 := rfl
@[simp] theorem ofCfg_pTarjanMark (c : FullCfg) : (ofCfg c).pTarjanMark = c.pTarjanMark := rfl
@[simp] theorem ofCfg_pTarjanReach (c : FullCfg) :
    (ofCfg c).pTarjanReach = c.pTarjanReach := rfl
@[simp] theorem ofCfg_pWalkVals (c : FullCfg) : (ofCfg c).pWalkVals = c.pWalkVals := rfl
@[simp] theorem ofCfg_pWalkBest (c : FullCfg) : (ofCfg c).pWalkBest = c.pWalkBest := rfl
@[simp] theorem ofCfg_pExtendStk (c : FullCfg) : (ofCfg c).pExtendStk = c.pExtendStk := rfl
@[simp] theorem ofCfg_extendCap (c : FullCfg) :
    (ofCfg c).extendCap = BitVec.ofNat 64 c.extend_cap := rfl
@[simp] theorem ofCfg_pScratchBuf (c : FullCfg) : (ofCfg c).pScratchBuf = c.pScratchBuf := rfl
@[simp] theorem ofCfg_scratchCap (c : FullCfg) :
    (ofCfg c).scratchCap = BitVec.ofNat 64 c.scratch_cap := rfl
@[simp] theorem ofCfg_pLastLearned (c : FullCfg) :
    (ofCfg c).pLastLearned = c.pLastLearned := rfl

theorem decode_of_len {ws : List (BitVec 64)} (h : 114 ≤ ws.length) :
    ∃ v, decode ws = some v := by
  unfold decode; simp [h]

theorem decode_len_le {ws : List (BitVec 64)} {v : HdrView} (h : decode ws = some v) :
    114 ≤ ws.length := by
  unfold decode at h
  split at h
  · assumption
  · cases h

theorem decode_get {ws : List (BitVec 64)} {v : HdrView} (h : decode ws = some v)
    (f : HdrField) : ws[f.tailIdx]? = some (v.get f) := by
  have hlen := decode_len_le h
  unfold decode at h
  simp only [hlen, ↓reduceDIte, Option.some.injEq] at h
  subst h
  have hlt : f.tailIdx < ws.length := Nat.lt_of_lt_of_le f.tailIdx_lt hlen
  rw [List.getElem?_eq_getElem hlt]
  cases f <;> rfl

theorem decode_getElem {ws : List (BitVec 64)} {v : HdrView} (h : decode ws = some v)
    (f : HdrField) :
    ws[f.tailIdx]'(Nat.lt_of_lt_of_le f.tailIdx_lt (decode_len_le h)) = v.get f := by
  have hopt := decode_get h f
  rw [List.getElem?_eq_getElem (Nat.lt_of_lt_of_le f.tailIdx_lt (decode_len_le h))] at hopt
  exact Option.some.inj hopt

theorem decode_eq_some_iff (ws : List (BitVec 64)) (v : HdrView) :
    decode ws = some v ↔ ∀ f : HdrField, ws[f.tailIdx]? = some (v.get f) := by
  constructor
  · intro h f; exact decode_get h f
  · intro h
    have h113 := h .pLastLearned
    change ws[113]? = some v.pLastLearned at h113
    have hlen : 114 ≤ ws.length := by
      have ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp h113
      omega
    obtain ⟨v', hv'⟩ := decode_of_len hlen
    have heq : v' = v := by
      apply ext_get
      intro f
      have h1 := decode_get hv' f
      rw [h f] at h1
      exact (Option.some.inj h1).symm
    rwa [← heq]

theorem decode_eq_some_conj_iff (ws : List (BitVec 64)) (v : HdrView) :
    decode ws = some v ↔
      ws[0]? = some v.arenaCap ∧ ws[1]? = some v.wcap ∧
      ws[4]? = some v.pVals ∧ ws[5]? = some v.pMark ∧ ws[6]? = some v.pLevel ∧
      ws[7]? = some v.pReason ∧ ws[8]? = some v.pTrail ∧ ws[9]? = some v.pWvec ∧
      ws[10]? = some v.pArena ∧ ws[11]? = some v.pWstk ∧ ws[12]? = some v.pDelayed ∧
      ws[13]? = some v.pTmp ∧ ws[21]? = some v.pHeap ∧ ws[22]? = some v.pPos ∧
      ws[23]? = some v.pScore ∧ ws[24]? = some v.pPhases ∧ ws[25]? = some v.pMinStk ∧
      ws[26]? = some v.pMinClr ∧ ws[29]? = some v.minDepth ∧ ws[41]? = some v.pTrailPos ∧
      ws[42]? = some v.pQPrev ∧ ws[43]? = some v.pQNext ∧ ws[44]? = some v.pQStamp ∧
      ws[45]? = some v.pPhasesTarget ∧ ws[46]? = some v.pPhasesBest ∧
      ws[47]? = some v.pWsort ∧ ws[48]? = some v.pShrinkStk ∧ ws[49]? = some v.pRedRefs ∧
      ws[50]? = some v.pGlueUsed ∧ ws[51]? = some v.redCap ∧ ws[52]? = some v.delayedCap ∧
      ws[96]? = some v.pFlags ∧ ws[97]? = some v.pLitMark ∧ ws[98]? = some v.pRepr ∧
      ws[99]? = some v.pSimSig ∧ ws[100]? = some v.pFrameTrail ∧
      ws[101]? = some v.pFrameDec ∧ ws[102]? = some v.pWorkStk1 ∧
      ws[103]? = some v.pWorkStk2 ∧ ws[104]? = some v.pTarjanMark ∧
      ws[105]? = some v.pTarjanReach ∧ ws[106]? = some v.pWalkVals ∧
      ws[107]? = some v.pWalkBest ∧ ws[108]? = some v.pExtendStk ∧
      ws[109]? = some v.extendCap ∧ ws[111]? = some v.pScratchBuf ∧
      ws[112]? = some v.scratchCap ∧ ws[113]? = some v.pLastLearned := by
  rw [decode_eq_some_iff]
  constructor
  · intro h
    refine ⟨h .arenaCap, h .wcap, h .pVals, h .pMark, h .pLevel, h .pReason, h .pTrail,
      h .pWvec, h .pArena, h .pWstk, h .pDelayed, h .pTmp, h .pHeap, h .pPos, h .pScore,
      h .pPhases, h .pMinStk, h .pMinClr, h .minDepth, h .pTrailPos, h .pQPrev, h .pQNext,
      h .pQStamp, h .pPhasesTarget, h .pPhasesBest, h .pWsort, h .pShrinkStk, h .pRedRefs,
      h .pGlueUsed, h .redCap, h .delayedCap, h .pFlags, h .pLitMark, h .pRepr, h .pSimSig,
      h .pFrameTrail, h .pFrameDec, h .pWorkStk1, h .pWorkStk2, h .pTarjanMark,
      h .pTarjanReach, h .pWalkVals, h .pWalkBest, h .pExtendStk, h .extendCap,
      h .pScratchBuf, h .scratchCap, h .pLastLearned⟩
  · rintro ⟨h0, h1, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h21, h22, h23, h24, h25,
      h26, h29, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50, h51, h52, h96, h97, h98,
      h99, h100, h101, h102, h103, h104, h105, h106, h107, h108, h109, h111, h112, h113⟩ f
    cases f <;> assumption

@[simp] theorem decode_set (ws : List (BitVec 64)) (f : HdrField) (w : BitVec 64) :
    decode (ws.set f.tailIdx w) = (decode ws).map (fun v => v.set f w) := by
  by_cases hlen : 114 ≤ ws.length
  · obtain ⟨v, hv⟩ := decode_of_len hlen
    have hlen' : 114 ≤ (ws.set f.tailIdx w).length := by simpa using hlen
    obtain ⟨v', hv'⟩ := decode_of_len hlen'
    rw [hv, hv', Option.map_some]
    congr 1
    apply ext_get
    intro g
    have h1 := decode_get hv' g
    by_cases hgf : g = f
    · subst hgf
      have hlt : g.tailIdx < ws.length := Nat.lt_of_lt_of_le g.tailIdx_lt hlen
      rw [List.getElem?_set_self hlt] at h1
      rw [get_set_self]
      exact (Option.some.inj h1).symm
    · have hne : f.tailIdx ≠ g.tailIdx := fun heq => hgf (HdrField.tailIdx_inj heq.symm)
      rw [List.getElem?_set_ne hne, decode_get hv g] at h1
      rw [get_set_ne v (Ne.symm hgf)]
      exact (Option.some.inj h1).symm
  · have h1 : decode ws = none := by unfold decode; simp [hlen]
    have h2 : decode (ws.set f.tailIdx w) = none := by
      unfold decode; simp [hlen]
    rw [h1, h2, Option.map_none]

@[simp] theorem decode_set_of_none (ws : List (BitVec 64)) {idx : Nat}
    (hnone : HdrField.ofTailIdx? idx = none) (w : BitVec 64) :
    decode (ws.set idx w) = decode ws := by
  by_cases hlen : 114 ≤ ws.length
  · obtain ⟨v, hv⟩ := decode_of_len hlen
    have hlen' : 114 ≤ (ws.set idx w).length := by simpa using hlen
    obtain ⟨v', hv'⟩ := decode_of_len hlen'
    rw [hv, hv']
    congr 1
    apply ext_get
    intro f
    have hne : idx ≠ f.tailIdx := (HdrField.ofTailIdx?_eq_none_tailIdx_ne hnone f).symm
    have h1 := decode_get hv' f
    rw [List.getElem?_set_ne hne, decode_get hv f] at h1
    exact (Option.some.inj h1).symm
  · have h1 : decode ws = none := by unfold decode; simp [hlen]
    have h2 : decode (ws.set idx w) = none := by
      unfold decode; simp [hlen]
    rw [h1, h2]

theorem decode_set_eq {ws : List (BitVec 64)} {v : HdrView} (h : decode ws = some v)
    (f : HdrField) (w : BitVec 64) :
    decode (ws.set f.tailIdx w) = some (v.set f w) := by
  rw [decode_set, h, Option.map_some]

theorem decode_hdrWordField_set {c : FullCfg} {s : FullState} {wf : HdrWordField}
    (hm : wf.isTailMut = true) (v : BitVec 64)
    (hnone : HdrField.ofTailIdx? (wf.wordIdx - 4) = none) :
    decode (hdrTailWords c (wf.set s v)) = some (ofCfg c) := by
  rw [wf.hdrTailWords_set hm c s v, decode_set_of_none _ hnone, decode_ofCfg]

theorem decode_hdrWordField_setNat {c : FullCfg} {s : FullState} {wf : HdrWordField}
    (hn : wf.isNat = true) (v : Nat)
    (hnone : HdrField.ofTailIdx? (wf.wordIdx - 4) = none) :
    decode (hdrTailWords c (wf.setNat s v)) = some (ofCfg c) := by
  rw [wf.hdrTailWords_setNat hn c s v, decode_set_of_none _ hnone, decode_ofCfg]

/-- Named projection helpers from `HdrView.decode ws = some v`. -/
theorem decode_arenaCap {ws : List (BitVec 64)} {v : HdrView} (h : decode ws = some v) :
    ws[0]? = some v.arenaCap := decode_get h .arenaCap
theorem decode_wcap {ws : List (BitVec 64)} {v : HdrView} (h : decode ws = some v) :
    ws[1]? = some v.wcap := decode_get h .wcap
theorem decode_pVals {ws : List (BitVec 64)} {v : HdrView} (h : decode ws = some v) :
    ws[4]? = some v.pVals := decode_get h .pVals
theorem decode_pMark {ws : List (BitVec 64)} {v : HdrView} (h : decode ws = some v) :
    ws[5]? = some v.pMark := decode_get h .pMark
theorem decode_pLevel {ws : List (BitVec 64)} {v : HdrView} (h : decode ws = some v) :
    ws[6]? = some v.pLevel := decode_get h .pLevel
theorem decode_pReason {ws : List (BitVec 64)} {v : HdrView} (h : decode ws = some v) :
    ws[7]? = some v.pReason := decode_get h .pReason
theorem decode_pTrail {ws : List (BitVec 64)} {v : HdrView} (h : decode ws = some v) :
    ws[8]? = some v.pTrail := decode_get h .pTrail
theorem decode_pWvec {ws : List (BitVec 64)} {v : HdrView} (h : decode ws = some v) :
    ws[9]? = some v.pWvec := decode_get h .pWvec
theorem decode_pArena {ws : List (BitVec 64)} {v : HdrView} (h : decode ws = some v) :
    ws[10]? = some v.pArena := decode_get h .pArena
theorem decode_pWstk {ws : List (BitVec 64)} {v : HdrView} (h : decode ws = some v) :
    ws[11]? = some v.pWstk := decode_get h .pWstk
theorem decode_pDelayed {ws : List (BitVec 64)} {v : HdrView} (h : decode ws = some v) :
    ws[12]? = some v.pDelayed := decode_get h .pDelayed
theorem decode_pTmp {ws : List (BitVec 64)} {v : HdrView} (h : decode ws = some v) :
    ws[13]? = some v.pTmp := decode_get h .pTmp
theorem decode_pHeap {ws : List (BitVec 64)} {v : HdrView} (h : decode ws = some v) :
    ws[21]? = some v.pHeap := decode_get h .pHeap
theorem decode_pPos {ws : List (BitVec 64)} {v : HdrView} (h : decode ws = some v) :
    ws[22]? = some v.pPos := decode_get h .pPos
theorem decode_pScore {ws : List (BitVec 64)} {v : HdrView} (h : decode ws = some v) :
    ws[23]? = some v.pScore := decode_get h .pScore
theorem decode_pPhases {ws : List (BitVec 64)} {v : HdrView} (h : decode ws = some v) :
    ws[24]? = some v.pPhases := decode_get h .pPhases
theorem decode_pMinStk {ws : List (BitVec 64)} {v : HdrView} (h : decode ws = some v) :
    ws[25]? = some v.pMinStk := decode_get h .pMinStk
theorem decode_pMinClr {ws : List (BitVec 64)} {v : HdrView} (h : decode ws = some v) :
    ws[26]? = some v.pMinClr := decode_get h .pMinClr
theorem decode_minDepth {ws : List (BitVec 64)} {v : HdrView} (h : decode ws = some v) :
    ws[29]? = some v.minDepth := decode_get h .minDepth
theorem decode_pTrailPos {ws : List (BitVec 64)} {v : HdrView} (h : decode ws = some v) :
    ws[41]? = some v.pTrailPos := decode_get h .pTrailPos
theorem decode_pQPrev {ws : List (BitVec 64)} {v : HdrView} (h : decode ws = some v) :
    ws[42]? = some v.pQPrev := decode_get h .pQPrev
theorem decode_pQNext {ws : List (BitVec 64)} {v : HdrView} (h : decode ws = some v) :
    ws[43]? = some v.pQNext := decode_get h .pQNext
theorem decode_pQStamp {ws : List (BitVec 64)} {v : HdrView} (h : decode ws = some v) :
    ws[44]? = some v.pQStamp := decode_get h .pQStamp
theorem decode_pPhasesTarget {ws : List (BitVec 64)} {v : HdrView} (h : decode ws = some v) :
    ws[45]? = some v.pPhasesTarget := decode_get h .pPhasesTarget
theorem decode_pPhasesBest {ws : List (BitVec 64)} {v : HdrView} (h : decode ws = some v) :
    ws[46]? = some v.pPhasesBest := decode_get h .pPhasesBest
theorem decode_pWsort {ws : List (BitVec 64)} {v : HdrView} (h : decode ws = some v) :
    ws[47]? = some v.pWsort := decode_get h .pWsort
theorem decode_pShrinkStk {ws : List (BitVec 64)} {v : HdrView} (h : decode ws = some v) :
    ws[48]? = some v.pShrinkStk := decode_get h .pShrinkStk
theorem decode_pRedRefs {ws : List (BitVec 64)} {v : HdrView} (h : decode ws = some v) :
    ws[49]? = some v.pRedRefs := decode_get h .pRedRefs
theorem decode_pGlueUsed {ws : List (BitVec 64)} {v : HdrView} (h : decode ws = some v) :
    ws[50]? = some v.pGlueUsed := decode_get h .pGlueUsed
theorem decode_redCap {ws : List (BitVec 64)} {v : HdrView} (h : decode ws = some v) :
    ws[51]? = some v.redCap := decode_get h .redCap
theorem decode_delayedCap {ws : List (BitVec 64)} {v : HdrView} (h : decode ws = some v) :
    ws[52]? = some v.delayedCap := decode_get h .delayedCap
theorem decode_pFlags {ws : List (BitVec 64)} {v : HdrView} (h : decode ws = some v) :
    ws[96]? = some v.pFlags := decode_get h .pFlags
theorem decode_pLitMark {ws : List (BitVec 64)} {v : HdrView} (h : decode ws = some v) :
    ws[97]? = some v.pLitMark := decode_get h .pLitMark
theorem decode_pRepr {ws : List (BitVec 64)} {v : HdrView} (h : decode ws = some v) :
    ws[98]? = some v.pRepr := decode_get h .pRepr
theorem decode_pSimSig {ws : List (BitVec 64)} {v : HdrView} (h : decode ws = some v) :
    ws[99]? = some v.pSimSig := decode_get h .pSimSig
theorem decode_pFrameTrail {ws : List (BitVec 64)} {v : HdrView} (h : decode ws = some v) :
    ws[100]? = some v.pFrameTrail := decode_get h .pFrameTrail
theorem decode_pFrameDec {ws : List (BitVec 64)} {v : HdrView} (h : decode ws = some v) :
    ws[101]? = some v.pFrameDec := decode_get h .pFrameDec
theorem decode_pWorkStk1 {ws : List (BitVec 64)} {v : HdrView} (h : decode ws = some v) :
    ws[102]? = some v.pWorkStk1 := decode_get h .pWorkStk1
theorem decode_pWorkStk2 {ws : List (BitVec 64)} {v : HdrView} (h : decode ws = some v) :
    ws[103]? = some v.pWorkStk2 := decode_get h .pWorkStk2
theorem decode_pTarjanMark {ws : List (BitVec 64)} {v : HdrView} (h : decode ws = some v) :
    ws[104]? = some v.pTarjanMark := decode_get h .pTarjanMark
theorem decode_pTarjanReach {ws : List (BitVec 64)} {v : HdrView} (h : decode ws = some v) :
    ws[105]? = some v.pTarjanReach := decode_get h .pTarjanReach
theorem decode_pWalkVals {ws : List (BitVec 64)} {v : HdrView} (h : decode ws = some v) :
    ws[106]? = some v.pWalkVals := decode_get h .pWalkVals
theorem decode_pWalkBest {ws : List (BitVec 64)} {v : HdrView} (h : decode ws = some v) :
    ws[107]? = some v.pWalkBest := decode_get h .pWalkBest
theorem decode_pExtendStk {ws : List (BitVec 64)} {v : HdrView} (h : decode ws = some v) :
    ws[108]? = some v.pExtendStk := decode_get h .pExtendStk
theorem decode_extendCap {ws : List (BitVec 64)} {v : HdrView} (h : decode ws = some v) :
    ws[109]? = some v.extendCap := decode_get h .extendCap
theorem decode_pScratchBuf {ws : List (BitVec 64)} {v : HdrView} (h : decode ws = some v) :
    ws[111]? = some v.pScratchBuf := decode_get h .pScratchBuf
theorem decode_scratchCap {ws : List (BitVec 64)} {v : HdrView} (h : decode ws = some v) :
    ws[112]? = some v.scratchCap := decode_get h .scratchCap
theorem decode_pLastLearned {ws : List (BitVec 64)} {v : HdrView} (h : decode ws = some v) :
    ws[113]? = some v.pLastLearned := decode_get h .pLastLearned

end HdrView

/-! ## 4. `HdrModifies` & `HdrWsModifies` Framing Algebra -/

/-- Framing predicate over `HdrView`: `v2` agrees with `v1` on every `HdrField` not in `S`. -/
@[expose] def HdrModifies (S : List HdrField) (v1 v2 : HdrView) : Prop :=
  ∀ f, f ∉ S → v2.get f = v1.get f

namespace HdrModifies

theorem refl (S : List HdrField) (v : HdrView) : HdrModifies S v v :=
  fun _ _ => rfl

theorem of_eq (S : List HdrField) {v1 v2 : HdrView} (h : v2 = v1) : HdrModifies S v1 v2 :=
  h ▸ refl S v1

theorem trans {S T : List HdrField} {v1 v2 v3 : HdrView}
    (h12 : HdrModifies S v1 v2) (h23 : HdrModifies T v2 v3) :
    HdrModifies (S ++ T) v1 v3 := by
  intro f hf
  rw [List.mem_append, not_or] at hf
  exact (h23 f hf.2).trans (h12 f hf.1)

theorem trans_same {S : List HdrField} {v1 v2 v3 : HdrView}
    (h12 : HdrModifies S v1 v2) (h23 : HdrModifies S v2 v3) :
    HdrModifies S v1 v3 :=
  fun f hf => (h23 f hf).trans (h12 f hf)

theorem mono {S T : List HdrField} {v1 v2 : HdrView}
    (hsub : S ⊆ T) (h : HdrModifies S v1 v2) : HdrModifies T v1 v2 :=
  fun f hf => h f (fun hs => hf (hsub hs))

theorem get_of_not_mem {S : List HdrField} {v1 v2 : HdrView}
    (h : HdrModifies S v1 v2) {f : HdrField} (hf : f ∉ S) :
    v2.get f = v1.get f :=
  h f hf

theorem set {v : HdrView} {f : HdrField} (w : BitVec 64) {S : List HdrField} (hf : f ∈ S) :
    HdrModifies S v (v.set f w) := by
  intro g hg
  have hne : f ≠ g := fun heq => hg (heq ▸ hf)
  exact HdrView.get_set_ne v hne w

theorem set_singleton (v : HdrView) (f : HdrField) (w : BitVec 64) :
    HdrModifies [f] v (v.set f w) :=
  set w (by simp)

theorem eq_of_nil {v1 v2 : HdrView} (h : HdrModifies [] v1 v2) : v2 = v1 :=
  HdrView.ext_get (fun f => h f (by simp))

theorem of_decode_set {ws : List (BitVec 64)} {v : HdrView} (h : HdrView.decode ws = some v)
    {f : HdrField} (w : BitVec 64) {S : List HdrField} (hf : f ∈ S) :
    ∃ v', HdrView.decode (ws.set f.tailIdx w) = some v' ∧ HdrModifies S v v' :=
  ⟨v.set f w, HdrView.decode_set_eq h f w, set w hf⟩

end HdrModifies

/-- Raw word-list framing predicate over `HdrField` slots (`ws2[f.tailIdx]? = ws1[f.tailIdx]?`). -/
@[expose] def HdrWsModifies (S : List HdrField) (ws1 ws2 : List (BitVec 64)) : Prop :=
  ∀ f, f ∉ S → ws2[f.tailIdx]? = ws1[f.tailIdx]?

namespace HdrWsModifies

theorem refl (S : List HdrField) (ws : List (BitVec 64)) : HdrWsModifies S ws ws :=
  fun _ _ => rfl

theorem trans {S T : List HdrField} {ws1 ws2 ws3 : List (BitVec 64)}
    (h12 : HdrWsModifies S ws1 ws2) (h23 : HdrWsModifies T ws2 ws3) :
    HdrWsModifies (S ++ T) ws1 ws3 := by
  intro f hf
  rw [List.mem_append, not_or] at hf
  exact (h23 f hf.2).trans (h12 f hf.1)

theorem mono {S T : List HdrField} {ws1 ws2 : List (BitVec 64)}
    (hsub : S ⊆ T) (h : HdrWsModifies S ws1 ws2) : HdrWsModifies T ws1 ws2 :=
  fun f hf => h f (fun hs => hf (hsub hs))

theorem get_of_not_mem {S : List HdrField} {ws1 ws2 : List (BitVec 64)}
    (h : HdrWsModifies S ws1 ws2) {f : HdrField} (hf : f ∉ S) :
    ws2[f.tailIdx]? = ws1[f.tailIdx]? :=
  h f hf

theorem set {ws : List (BitVec 64)} {f : HdrField} (w : BitVec 64)
    {S : List HdrField} (hf : f ∈ S) : HdrWsModifies S ws (ws.set f.tailIdx w) := by
  intro g hg
  have hne : f.tailIdx ≠ g.tailIdx := fun heq => hg (HdrField.tailIdx_inj heq ▸ hf)
  exact List.getElem?_set_ne hne

theorem iff_hdrModifies {S : List HdrField} {ws1 ws2 : List (BitVec 64)} {v1 v2 : HdrView}
    (h1 : HdrView.decode ws1 = some v1) (h2 : HdrView.decode ws2 = some v2) :
    HdrWsModifies S ws1 ws2 ↔ HdrModifies S v1 v2 := by
  constructor
  · intro hw f hf
    have hget := hw f hf
    rw [HdrView.decode_get h1 f, HdrView.decode_get h2 f] at hget
    exact Option.some.inj hget
  · intro hm f hf
    rw [HdrView.decode_get h1 f, HdrView.decode_get h2 f, hm f hf]

end HdrWsModifies

/-- Fixed-pointer consistency predicate: all `37` non-dynamic `HdrView` slots match `c`. -/
@[expose] def HdrView.MatchesFixedPtrs (c : FullCfg) (v : HdrView) : Prop :=
  HdrModifies HdrField.arenaDynFields (.ofCfg c) v

end LeanQbe.T.Examples.Kissat.Proof.Spec
