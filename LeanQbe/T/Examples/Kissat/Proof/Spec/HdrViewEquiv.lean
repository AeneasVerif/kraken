/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Spec.HdrView
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts2
public import LeanQbe.T.Logic.CanonicalEnv

/-!
# Bidirectional `HdrView` Spec Equivalences (`Proof.Spec.HdrViewEquiv`)

Additive zero-cache-bust leaf providing concise `HdrView` / `HdrModifies` / `AgreesExcept`
versions of the 4 largest `Contracts1` / `Contracts2` specifications, together with exact
bidirectional equivalence (`↔`) and `Spec.Le` bridges in both directions:
1. `fullInitPtrsHdrSpec` ↔ `fullInitPtrsSpec` (`41` conjuncts → `HdrView` + `HdrModifies`)
2. `fullInitArenasHdrSpec` ↔ `fullInitArenasSpec` (`58` conjuncts → `HdrView.decode`)
3. `fullSweepCopyHdrSpec` ↔ `fullSweepCopySpec` (`41` conjuncts → `AgreesExcept` + bundles)
4. `fullAnalyzeRsnHdrSpec` ↔ `fullAnalyzeRsnSpec` (`29` conjuncts → `AgreesExcept` + bundles)
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

/-! ## 1. `fullInitPtrsSpec` ↔ `fullInitPtrsHdrSpec` -/

private theorem matchesFixedPtrs_iff_conj {ws : List (BitVec 64)} {v : HdrView}
    (hdec : HdrView.decode ws = some v) (c : FullCfg) :
    v.MatchesFixedPtrs c ↔
      ws[4]? = some c.pVals ∧ ws[5]? = some c.pMark ∧ ws[6]? = some c.pLevel ∧
      ws[7]? = some c.pReason ∧ ws[8]? = some c.pTrail ∧ ws[9]? = some c.pWvec ∧
      ws[10]? = some c.pArena ∧ ws[13]? = some c.pTmp ∧ ws[21]? = some c.pHeap ∧
      ws[22]? = some c.pPos ∧ ws[23]? = some c.pScore ∧ ws[24]? = some c.pPhases ∧
      ws[25]? = some c.pMinStk ∧ ws[26]? = some c.pMinClr ∧
      ws[29]? = some (BitVec.ofNat 64 c.minDepth) ∧ ws[41]? = some c.pTrailPos ∧
      ws[42]? = some c.pQPrev ∧ ws[43]? = some c.pQNext ∧ ws[44]? = some c.pQStamp ∧
      ws[45]? = some c.pPhasesTarget ∧ ws[46]? = some c.pPhasesBest ∧
      ws[47]? = some c.pWsort ∧ ws[48]? = some c.pShrinkStk ∧ ws[50]? = some c.pGlueUsed ∧
      ws[96]? = some c.pFlags ∧ ws[97]? = some c.pLitMark ∧ ws[98]? = some c.pRepr ∧
      ws[99]? = some c.pSimSig ∧ ws[100]? = some c.pFrameTrail ∧
      ws[101]? = some c.pFrameDec ∧ ws[102]? = some c.pWorkStk1 ∧
      ws[103]? = some c.pWorkStk2 ∧ ws[104]? = some c.pTarjanMark ∧
      ws[105]? = some c.pTarjanReach ∧ ws[106]? = some c.pWalkVals ∧
      ws[107]? = some c.pWalkBest ∧ ws[113]? = some c.pLastLearned := by
  have hg : ∀ f : HdrField,
      (v.get f = (HdrView.ofCfg c).get f) ↔ ws[f.tailIdx]? = some ((HdrView.ofCfg c).get f) :=
    fun f => by rw [HdrView.decode_get hdec f]; exact ⟨fun h => congrArg some h, Option.some.inj⟩
  constructor
  · intro hm
    refine ⟨(hg .pVals).mp (hm .pVals (by decide)),
      (hg .pMark).mp (hm .pMark (by decide)),
      (hg .pLevel).mp (hm .pLevel (by decide)),
      (hg .pReason).mp (hm .pReason (by decide)),
      (hg .pTrail).mp (hm .pTrail (by decide)),
      (hg .pWvec).mp (hm .pWvec (by decide)),
      (hg .pArena).mp (hm .pArena (by decide)),
      (hg .pTmp).mp (hm .pTmp (by decide)),
      (hg .pHeap).mp (hm .pHeap (by decide)),
      (hg .pPos).mp (hm .pPos (by decide)),
      (hg .pScore).mp (hm .pScore (by decide)),
      (hg .pPhases).mp (hm .pPhases (by decide)),
      (hg .pMinStk).mp (hm .pMinStk (by decide)),
      (hg .pMinClr).mp (hm .pMinClr (by decide)),
      (hg .minDepth).mp (hm .minDepth (by decide)),
      (hg .pTrailPos).mp (hm .pTrailPos (by decide)),
      (hg .pQPrev).mp (hm .pQPrev (by decide)),
      (hg .pQNext).mp (hm .pQNext (by decide)),
      (hg .pQStamp).mp (hm .pQStamp (by decide)),
      (hg .pPhasesTarget).mp (hm .pPhasesTarget (by decide)),
      (hg .pPhasesBest).mp (hm .pPhasesBest (by decide)),
      (hg .pWsort).mp (hm .pWsort (by decide)),
      (hg .pShrinkStk).mp (hm .pShrinkStk (by decide)),
      (hg .pGlueUsed).mp (hm .pGlueUsed (by decide)),
      (hg .pFlags).mp (hm .pFlags (by decide)),
      (hg .pLitMark).mp (hm .pLitMark (by decide)),
      (hg .pRepr).mp (hm .pRepr (by decide)),
      (hg .pSimSig).mp (hm .pSimSig (by decide)),
      (hg .pFrameTrail).mp (hm .pFrameTrail (by decide)),
      (hg .pFrameDec).mp (hm .pFrameDec (by decide)),
      (hg .pWorkStk1).mp (hm .pWorkStk1 (by decide)),
      (hg .pWorkStk2).mp (hm .pWorkStk2 (by decide)),
      (hg .pTarjanMark).mp (hm .pTarjanMark (by decide)),
      (hg .pTarjanReach).mp (hm .pTarjanReach (by decide)),
      (hg .pWalkVals).mp (hm .pWalkVals (by decide)),
      (hg .pWalkBest).mp (hm .pWalkBest (by decide)),
      (hg .pLastLearned).mp (hm .pLastLearned (by decide))⟩
  · rintro ⟨h4, h5, h6, h7, h8, h9, h10, h13, h21, h22, h23, h24, h25, h26, h29, h41, h42, h43,
      h44, h45, h46, h47, h48, h50, h96, h97, h98, h99, h100, h101, h102, h103, h104, h105,
      h106, h107, h113⟩ f hf
    rw [hg f]
    cases f <;> first | exact False.elim (hf (by decide)) | assumption

private theorem fixedPtrFields_frame_iff {ws ws' : List (BitVec 64)} {v v' : HdrView}
    (hdec : HdrView.decode ws = some v) (hdec' : HdrView.decode ws' = some v') :
    HdrModifies HdrField.fixedPtrFields v v' ↔
      ∀ i ∈ [0, 1, 11, 12, 49, 51, 52, 108, 109, 111, 112], ws'[i]? = ws[i]? := by
  constructor
  · intro hm i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [HdrView.decode_arenaCap hdec', HdrView.decode_arenaCap hdec]
      exact congrArg some (hm .arenaCap (by decide))
    · rw [HdrView.decode_wcap hdec', HdrView.decode_wcap hdec]
      exact congrArg some (hm .wcap (by decide))
    · rw [HdrView.decode_pWstk hdec', HdrView.decode_pWstk hdec]
      exact congrArg some (hm .pWstk (by decide))
    · rw [HdrView.decode_pDelayed hdec', HdrView.decode_pDelayed hdec]
      exact congrArg some (hm .pDelayed (by decide))
    · rw [HdrView.decode_pRedRefs hdec', HdrView.decode_pRedRefs hdec]
      exact congrArg some (hm .pRedRefs (by decide))
    · rw [HdrView.decode_redCap hdec', HdrView.decode_redCap hdec]
      exact congrArg some (hm .redCap (by decide))
    · rw [HdrView.decode_delayedCap hdec', HdrView.decode_delayedCap hdec]
      exact congrArg some (hm .delayedCap (by decide))
    · rw [HdrView.decode_pExtendStk hdec', HdrView.decode_pExtendStk hdec]
      exact congrArg some (hm .pExtendStk (by decide))
    · rw [HdrView.decode_extendCap hdec', HdrView.decode_extendCap hdec]
      exact congrArg some (hm .extendCap (by decide))
    · rw [HdrView.decode_pScratchBuf hdec', HdrView.decode_pScratchBuf hdec]
      exact congrArg some (hm .pScratchBuf (by decide))
    · rw [HdrView.decode_scratchCap hdec', HdrView.decode_scratchCap hdec]
      exact congrArg some (hm .scratchCap (by decide))
  · intro h f hf
    rw [HdrField.not_mem_fixedPtrFields_iff] at hf
    have hidx : f.tailIdx ∈ [0, 1, 11, 12, 49, 51, 52, 108, 109, 111, 112] := by
      cases f <;> first | (simp [HdrField.arenaDynFields] at hf; done) | decide
    have hws := h f.tailIdx hidx
    rw [HdrView.decode_get hdec' f, HdrView.decode_get hdec f] at hws
    exact Option.some.inj hws

/-- Postcondition package for `full_init_ptrs` over decoded `HdrView`. -/
structure FullInitPtrsPost (hdr_addr max_v : BitVec 64) (v v' : HdrView) : Prop where
  ptrs_ok : ∀ (c : FullCfg), c.hdr = hdr_addr → c.max_vars = max_v.toNat →
    v'.MatchesFixedPtrs c
  frame : HdrModifies HdrField.fixedPtrFields v v'

/-- Concise `HdrView`-based contract equivalent to `fullInitPtrsSpec`. -/
@[expose] def fullInitPtrsHdrSpec : Spec [i64, i64, i64] [] :=
  fun (h, hdr_addr, max_v, ()) m Q _ =>
    ∃ (ws : List (BitVec 64)) (v : HdrView) (R : Mem 64 → Prop),
      h = hdr_addr ∧ ws.length = 140 ∧ HdrView.decode ws = some v ∧
      max_v.toNat < 2 * dimacsBound ∧
      hdr_addr.toNat + fullFixedBytes max_v.toNat < 2 ^ 64 ∧
      (array64 (hdr_addr + 32) ws ⋆ R) m ∧
      ∀ ws' v' m', ws'.length = 140 → HdrView.decode ws' = some v' →
        FullInitPtrsPost hdr_addr max_v v v' →
        (array64 (hdr_addr + 32) ws' ⋆ R) m' → Q () m'

theorem fullInitPtrsSpec_iff_hdr (a : Tup Val [i64, i64, i64]) (m : Mem 64)
    (Q : Post []) (X : XPost) :
    fullInitPtrsSpec a m Q X ↔ fullInitPtrsHdrSpec a m Q X := by
  rcases a with ⟨h, hdr_addr, max_v, ⟨⟩⟩
  constructor
  · rintro ⟨ws, R, rfl, hlen, hmax, hfit, hm, hQ⟩
    obtain ⟨v, hdec⟩ := HdrView.decode_of_len (by omega : 114 ≤ ws.length)
    refine ⟨ws, v, R, rfl, hlen, hdec, hmax, hfit, hm, fun ws' v' m' hlen' hdec' hpost hm' => ?_⟩
    exact hQ ws' m' hlen'
      (fun c hc hm => (matchesFixedPtrs_iff_conj hdec' c).mp (hpost.ptrs_ok c hc hm))
      ((fixedPtrFields_frame_iff hdec hdec').mp hpost.frame) hm'
  · rintro ⟨ws, v, R, rfl, hlen, hdec, hmax, hfit, hm, hQ⟩
    refine ⟨ws, R, rfl, hlen, hmax, hfit, hm, fun ws' m' hlen' hptrs hfrm hm' => ?_⟩
    obtain ⟨v', hdec'⟩ := HdrView.decode_of_len (by omega : 114 ≤ ws'.length)
    exact hQ ws' v' m' hlen' hdec'
      ⟨fun c hc hm => (matchesFixedPtrs_iff_conj hdec' c).mpr (hptrs c hc hm),
        (fixedPtrFields_frame_iff hdec hdec').mpr hfrm⟩ hm'

theorem fullInitPtrsSpec_le_hdr : fullInitPtrsSpec.Le fullInitPtrsHdrSpec :=
  fun a m Q X h => (fullInitPtrsSpec_iff_hdr a m Q X).mp h

theorem fullInitPtrsHdrSpec_le : fullInitPtrsHdrSpec.Le fullInitPtrsSpec :=
  fun a m Q X h => (fullInitPtrsSpec_iff_hdr a m Q X).mpr h

theorem fullInitPtrsHdrSpec_xfree : Spec.XFree fullInitPtrsHdrSpec := by xfree

/-! ## 2. `fullInitArenasSpec` ↔ `fullInitArenasHdrSpec` -/

private theorem decode_ofCfg_iff_conj48 (ws' : List (BitVec 64)) (c : FullCfg) :
    HdrView.decode ws' = some (HdrView.ofCfg c) ↔
      ws'[0]? = some (BitVec.ofNat 64 c.arena_cap) ∧
      ws'[1]? = some (BitVec.ofNat 64 c.wcap) ∧
      ws'[4]? = some c.pVals ∧ ws'[5]? = some c.pMark ∧ ws'[6]? = some c.pLevel ∧
      ws'[7]? = some c.pReason ∧ ws'[8]? = some c.pTrail ∧ ws'[9]? = some c.pWvec ∧
      ws'[10]? = some c.pArena ∧ ws'[11]? = some c.pWstk ∧ ws'[12]? = some c.pDelayed ∧
      ws'[13]? = some c.pTmp ∧ ws'[21]? = some c.pHeap ∧ ws'[22]? = some c.pPos ∧
      ws'[23]? = some c.pScore ∧ ws'[24]? = some c.pPhases ∧ ws'[25]? = some c.pMinStk ∧
      ws'[26]? = some c.pMinClr ∧ ws'[29]? = some (BitVec.ofNat 64 c.minDepth) ∧
      ws'[41]? = some c.pTrailPos ∧ ws'[42]? = some c.pQPrev ∧ ws'[43]? = some c.pQNext ∧
      ws'[44]? = some c.pQStamp ∧ ws'[45]? = some c.pPhasesTarget ∧
      ws'[46]? = some c.pPhasesBest ∧ ws'[47]? = some c.pWsort ∧
      ws'[48]? = some c.pShrinkStk ∧ ws'[49]? = some c.pRedRefs ∧
      ws'[50]? = some c.pGlueUsed ∧ ws'[51]? = some (BitVec.ofNat 64 c.red_cap) ∧
      ws'[52]? = some (BitVec.ofNat 64 c.delayed_cap) ∧ ws'[96]? = some c.pFlags ∧
      ws'[97]? = some c.pLitMark ∧ ws'[98]? = some c.pRepr ∧ ws'[99]? = some c.pSimSig ∧
      ws'[100]? = some c.pFrameTrail ∧ ws'[101]? = some c.pFrameDec ∧
      ws'[102]? = some c.pWorkStk1 ∧ ws'[103]? = some c.pWorkStk2 ∧
      ws'[104]? = some c.pTarjanMark ∧ ws'[105]? = some c.pTarjanReach ∧
      ws'[106]? = some c.pWalkVals ∧ ws'[107]? = some c.pWalkBest ∧
      ws'[108]? = some c.pExtendStk ∧ ws'[109]? = some (BitVec.ofNat 64 c.extend_cap) ∧
      ws'[111]? = some c.pScratchBuf ∧ ws'[112]? = some (BitVec.ofNat 64 c.scratch_cap) ∧
      ws'[113]? = some c.pLastLearned := by
  simpa using HdrView.decode_eq_some_conj_iff ws' (HdrView.ofCfg c)

/-- Precondition package for `full_init_arenas` over decoded `HdrView`. -/
structure FullInitArenasPre (hdr_addr max_v avail_dyn : BitVec 64)
    (dcap ecap scap : Nat) (v : HdrView) : Prop where
  max_v_lt : max_v.toNat < 2 * dimacsBound
  dcap_lt : dcap < dimacsBound
  ecap_lt : ecap < dimacsBound
  scap_lt : scap < dimacsBound
  delayed_eq : v.delayedCap = BitVec.ofNat 64 dcap
  extend_eq : v.extendCap = BitVec.ofNat 64 ecap
  scratch_eq : v.scratchCap = BitVec.ofNat 64 scap
  fit : hdr_addr.toNat + fullFixedBytes max_v.toNat + avail_dyn.toNat +
    12 * dcap + 4 * ecap + 4 * scap < 2 ^ 64

/-- Postcondition package for `full_init_arenas` replacing all `48` raw index checks by
`HdrView.decode ws' = some (HdrView.ofCfg c)`. -/
structure FullInitArenasPost (hdr_addr max_v avail_dyn : BitVec 64)
    (dcap ecap scap acap wcap rcap : Nat) (ws' : List (BitVec 64)) : Prop where
  len : ws'.length = 140
  acap_lt : acap < 2 * dimacsBound
  wcap_lt : wcap < 2 * dimacsBound
  rcap_lt : rcap < 2 * dimacsBound
  dyn_fit : 4 * acap + 4 * wcap + 4 * rcap ≤ avail_dyn.toNat
  wcap_pos : 40 ≤ avail_dyn.toNat → 1 ≤ wcap
  hdr_ok : ∀ (c : FullCfg), c.hdr = hdr_addr → c.max_vars = max_v.toNat →
    c.arena_cap = acap → c.wcap = wcap → c.delayed_cap = dcap → c.red_cap = rcap →
    c.extend_cap = ecap → c.scratch_cap = scap →
    HdrView.decode ws' = some (HdrView.ofCfg c)

/-- Concise `HdrView`-based contract equivalent to `fullInitArenasSpec`. -/
@[expose] def fullInitArenasHdrSpec : Spec [i64, i64, i64, i64] [] :=
  fun (h, hdr_addr, max_v, avail_dyn, ()) m Q _ =>
    ∃ (ws : List (BitVec 64)) (v : HdrView) (dcap ecap scap : Nat) (R : Mem 64 → Prop),
      h = hdr_addr ∧ ws.length = 140 ∧ HdrView.decode ws = some v ∧
      FullInitArenasPre hdr_addr max_v avail_dyn dcap ecap scap v ∧
      (array64 (hdr_addr + 32) ws ⋆ R) m ∧
      ∀ (acap wcap rcap : Nat) (ws' : List (BitVec 64)) m',
        FullInitArenasPost hdr_addr max_v avail_dyn dcap ecap scap acap wcap rcap ws' →
        (array64 (hdr_addr + 32) ws' ⋆ R) m' → Q () m'

theorem fullInitArenasSpec_iff_hdr (a : Tup Val [i64, i64, i64, i64]) (m : Mem 64)
    (Q : Post []) (X : XPost) :
    fullInitArenasSpec a m Q X ↔ fullInitArenasHdrSpec a m Q X := by
  rcases a with ⟨h, hdr_addr, max_v, avail_dyn, ⟨⟩⟩
  constructor
  · rintro ⟨ws, dcap, ecap, scap, R, rfl, hlen, hmx, hdel, hext, hscr,
      h52, h109, h112, hfit, hm, hQ⟩
    obtain ⟨v, hdec⟩ := HdrView.decode_of_len (by omega : 114 ≤ ws.length)
    have hv52 : v.delayedCap = BitVec.ofNat 64 dcap := by
      have h' := HdrView.decode_delayedCap hdec; rw [h52] at h'; exact (Option.some.inj h').symm
    have hv109 : v.extendCap = BitVec.ofNat 64 ecap := by
      have h' := HdrView.decode_extendCap hdec; rw [h109] at h'; exact (Option.some.inj h').symm
    have hv112 : v.scratchCap = BitVec.ofNat 64 scap := by
      have h' := HdrView.decode_scratchCap hdec; rw [h112] at h'; exact (Option.some.inj h').symm
    refine ⟨ws, v, dcap, ecap, scap, R, rfl, hlen, hdec,
      ⟨hmx, hdel, hext, hscr, hv52, hv109, hv112, hfit⟩, hm,
      fun acap wcap rcap ws' m' hpost hm' => ?_⟩
    exact hQ acap wcap rcap ws' m' hpost.len hpost.acap_lt hpost.wcap_lt hpost.rcap_lt
      hpost.dyn_fit hpost.wcap_pos
      (fun c h1 h2 h3 h4 h5 h6 h7 h8 =>
        (decode_ofCfg_iff_conj48 ws' c).mp (hpost.hdr_ok c h1 h2 h3 h4 h5 h6 h7 h8)) hm'
  · rintro ⟨ws, v, dcap, ecap, scap, R, rfl, hlen, hdec, hpre, hm, hQ⟩
    refine ⟨ws, dcap, ecap, scap, R, rfl, hlen, hpre.max_v_lt, hpre.dcap_lt, hpre.ecap_lt,
      hpre.scap_lt, ?_, ?_, ?_, hpre.fit, hm,
      fun acap wcap rcap ws' m' hl' ha hw hr hdyn hwp hconj hm' => ?_⟩
    · rw [HdrView.decode_delayedCap hdec, hpre.delayed_eq]
    · rw [HdrView.decode_extendCap hdec, hpre.extend_eq]
    · rw [HdrView.decode_scratchCap hdec, hpre.scratch_eq]
    · exact hQ acap wcap rcap ws' m'
        ⟨hl', ha, hw, hr, hdyn, hwp, fun c h1 h2 h3 h4 h5 h6 h7 h8 =>
          (decode_ofCfg_iff_conj48 ws' c).mpr (hconj c h1 h2 h3 h4 h5 h6 h7 h8)⟩ hm'

theorem fullInitArenasSpec_le_hdr : fullInitArenasSpec.Le fullInitArenasHdrSpec :=
  fun a m Q X h => (fullInitArenasSpec_iff_hdr a m Q X).mp h

theorem fullInitArenasHdrSpec_le : fullInitArenasHdrSpec.Le fullInitArenasSpec :=
  fun a m Q X h => (fullInitArenasSpec_iff_hdr a m Q X).mpr h

theorem fullInitArenasHdrSpec_xfree : Spec.XFree fullInitArenasHdrSpec := by xfree

/-! ## 3. `fullSweepCopySpec` ↔ `fullSweepCopyHdrSpec` -/

/-- `AgreesExcept` mask for `full_sweep_copy`: permits mutating only the `16` core fields
and `2` scratch fields touched at root level, preserving all other `FullState` fields. -/
@[expose] def sweepCopyMask (s : FullState) : FullState :=
  { s with
    core := { s.core with
      arena := [], vals := [], flags := [], lvl := [], rsns := [], trl := [],
      trail_pos := [], trail_end := 0, unassigned := 0#64, unflushed := 0#64,
      wvec := [], wstk := [], wlen := 0, wusable := 0#64, num_binary := 0#64, oom := 0#64 }
    scratch := { s.scratch with phases := [], wsort := [] } }

/-- `AgreesExcept` mask permitting mutation of `core.arena` only (`at_root = false`). -/
@[expose] def arenaOnlyMask (s : FullState) : FullState :=
  { s with core := { s.core with arena := [] } }

private theorem agreesExcept_sweepCopyMask_iff (s s' : FullState) :
    AgreesExcept sweepCopyMask s s' ↔
      s' = { s with
        core := { s.core with
          arena := s'.core.arena, vals := s'.core.vals, flags := s'.core.flags,
          lvl := s'.core.lvl, rsns := s'.core.rsns, trl := s'.core.trl,
          trail_pos := s'.core.trail_pos, trail_end := s'.core.trail_end,
          unassigned := s'.core.unassigned, unflushed := s'.core.unflushed,
          wvec := s'.core.wvec, wstk := s'.core.wstk, wlen := s'.core.wlen,
          wusable := s'.core.wusable, num_binary := s'.core.num_binary,
          oom := s'.core.oom }
        scratch := { s.scratch with phases := s'.scratch.phases, wsort := s'.scratch.wsort } } := by
  constructor
  · intro h
    rcases s with ⟨c1, sc1⟩
    rcases s' with ⟨c2, sc2⟩
    cases c1; cases c2; cases sc1; cases sc2
    simp only [AgreesExcept, sweepCopyMask] at h
    injection h with hc hsc
    cases hc; cases hsc; rfl
  · intro h; rw [h]; rfl

private theorem agreesExcept_arenaOnlyMask_iff (s s' : FullState) :
    AgreesExcept arenaOnlyMask s s' ↔
      s' = { s with core := { s.core with arena := s'.core.arena } } := by
  constructor
  · intro h
    rcases s with ⟨c1, sc1⟩
    rcases s' with ⟨c2, sc2⟩
    cases c1; cases c2; cases sc1; cases sc2
    simp only [AgreesExcept, arenaOnlyMask] at h
    injection h with hc hsc
    cases hc; cases hsc; rfl
  · intro h; rw [h]; rfl

private theorem agreesExcept_arenaOnly_of_sweepCopy {s s' : FullState}
    (hsw : AgreesExcept sweepCopyMask s s') :
    AgreesExcept arenaOnlyMask s s' ↔
      (s'.core.vals = s.core.vals ∧ s'.core.flags = s.core.flags ∧
       s'.core.lvl = s.core.lvl ∧ s'.core.rsns = s.core.rsns ∧
       s'.core.trl = s.core.trl ∧ s'.core.trail_pos = s.core.trail_pos ∧
       s'.core.trail_end = s.core.trail_end ∧ s'.core.unassigned = s.core.unassigned ∧
       s'.core.unflushed = s.core.unflushed ∧ s'.core.wvec = s.core.wvec ∧
       s'.core.wstk = s.core.wstk ∧ s'.core.wlen = s.core.wlen ∧
       s'.core.wusable = s.core.wusable ∧ s'.core.num_binary = s.core.num_binary ∧
       s'.core.oom = s.core.oom ∧ s'.scratch.phases = s.scratch.phases ∧
       s'.scratch.wsort = s.scratch.wsort) := by
  constructor
  · intro ha
    rw [(agreesExcept_arenaOnlyMask_iff s s').mp ha]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩
    rw [agreesExcept_arenaOnlyMask_iff]
    have hsw' := (agreesExcept_sweepCopyMask_iff s s').mp hsw
    rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17] at hsw'
    exact hsw'

/-- Precondition package for `full_sweep_copy`. -/
structure FullSweepCopyPre (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s : FullState) (src dst : BitVec 64) (old_sz : BitVec 32) (at_root : Bool) : Prop where
  lengths : s.LengthsOk c
  dst_le_src : dst.toNat ≤ src.toNat
  old_sz_ge : 3 ≤ old_sz.toNat
  src_bound : src.toNat + 3 + old_sz.toNat ≤ s.core.arena_len
  at_root_eq : at_root = decide (s.core.cur_level = 0)
  src_lits_lt : ∀ j < old_sz.toNat,
    (s.core.arena[src.toNat + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars
  root_inv : at_root = true →
    FullWitnessInv c F0 F_cur { s.core with arena_len := dst.toNat } ∧
    FullBinOnlyWatchesInv F_cur s.core ∧
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause (((s.core.arena.drop (src.toNat + 3)).take old_sz.toNat).map BitVec.toNat))

/-- Root-level (`at_root = true`) postcondition package for `full_sweep_copy`. -/
structure FullSweepCopyRootPost (c : FullCfg) (F0 : CNF Nat)
    (F_cur : List (List Nat)) (s s' : FullState) (src dst : BitVec 64)
    (old_sz : BitVec 32) (r : BitVec 64) : Prop where
  witness : FullWitnessInv c F0 F_cur { s'.core with arena_len := dst.toNat }
  watches : FullBinOnlyWatchesInv F_cur s'.core
  trail_mono : s.core.trail_end ≤ s'.core.trail_end
  ret_cases : r = 0xFFFFFFFE#64 ∨ r = 0xFFFFFFFD#64 ∨ r = 1#64 ∨ r = 0xFFFFFFFF#64 ∨
    (3 ≤ r.toNat ∧ r.toNat ≤ old_sz.toNat)
  unsat_of_ret : r = 0xFFFFFFFE#64 → F0.Unsat
  oom_of_ret : r = 0xFFFFFFFD#64 → s'.core.oom = 1#64
  oom_pres : r ≠ 0xFFFFFFFD#64 → s'.core.oom = s.core.oom
  unit_trail : r = 1#64 → s.core.trail_end < s'.core.trail_end
  copied_ok : 3 ≤ r.toNat ∧ r.toNat ≤ old_sz.toNat →
    (∀ j < r.toNat, (s'.core.arena[dst.toNat + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
    List.Sublist (((s'.core.arena.drop (dst.toNat + 3)).take r.toNat).map BitVec.toNat)
      (((s.core.arena.drop (src.toNat + 3)).take old_sz.toNat).map BitVec.toNat) ∧
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause (((s'.core.arena.drop (dst.toNat + 3)).take r.toNat).map BitVec.toNat))

/-- Non-root (`at_root = false`) postcondition package using `AgreesExcept arenaOnlyMask`. -/
structure FullSweepCopyNonRootPost (s s' : FullState) (src dst : BitVec 64)
    (old_sz : BitVec 32) (r : BitVec 64) : Prop where
  ret_eq : r = old_sz.setWidth 64
  frame : AgreesExcept arenaOnlyMask s s'
  copied : ∀ j < old_sz.toNat,
    s'.core.arena[dst.toNat + 3 + j]? = s.core.arena[src.toNat + 3 + j]?

/-- Postcondition package for `full_sweep_copy` replacing `18`-field reconstruction and `17`
frame equalities with `AgreesExcept sweepCopyMask` and `FullSweepCopyNonRootPost`. -/
structure FullSweepCopyPost (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s s' : FullState) (src dst : BitVec 64) (old_sz : BitVec 32) (at_root : Bool)
    (r : BitVec 64) : Prop where
  frame : AgreesExcept sweepCopyMask s s'
  lengths : s'.LengthsOk c
  arena_frame : ∀ i, (i < dst.toNat + 3 ∨ dst.toNat + 3 + old_sz.toNat ≤ i) →
    s'.core.arena[i]? = s.core.arena[i]?
  non_root : at_root = false → FullSweepCopyNonRootPost s s' src dst old_sz r
  root : at_root = true → FullSweepCopyRootPost c F0 F_cur s s' src dst old_sz r

theorem FullSweepCopyPost.hdrView_eq {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} {src dst : BitVec 64} {old_sz : BitVec 32} {at_root : Bool}
    {r : BitVec 64} (_h : FullSweepCopyPost c F0 F_cur s s' src dst old_sz at_root r) :
    HdrView.decode (hdrTailWords c s') = some (HdrView.ofCfg c) :=
  HdrView.decode_ofCfg c s'

/-- Concise `HdrView`/`AgreesExcept` contract equivalent to `fullSweepCopySpec`. -/
@[expose] def fullSweepCopyHdrSpec : Spec [i64, i64, i64, i32, .bool] [i64] :=
  fun (h, src, dst, old_sz, at_root, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ FullSweepCopyPre c F0 F_cur s src dst old_sz at_root ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
        FullSweepCopyPost c F0 F_cur s s' src dst old_sz at_root r →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

theorem fullSweepCopySpec_iff_hdr (a : Tup Val [i64, i64, i64, i32, .bool]) (m : Mem 64)
    (Q : Post [i64]) (X : XPost) :
    fullSweepCopySpec a m Q X ↔ fullSweepCopyHdrSpec a m Q X := by
  rcases a with ⟨h, src, dst, old_sz, at_root, ⟨⟩⟩
  constructor
  · rintro ⟨c, F0, F_cur, s, R, rfl, hlen, hds, hos, hsrc, hat, hlts, hrt, hm, hQ⟩
    refine ⟨c, F0, F_cur, s, R, rfl, ⟨hlen, hds, hos, hsrc, hat, hlts, hrt⟩, hm,
      fun r s' m' hpost hm' => ?_⟩
    have heq := (agreesExcept_sweepCopyMask_iff s s').mp hpost.frame
    rw [heq] at hm'
    have hlen' : FullState.LengthsOk c { s with
        core := { s.core with
          arena := s'.core.arena, vals := s'.core.vals, flags := s'.core.flags,
          lvl := s'.core.lvl, rsns := s'.core.rsns, trl := s'.core.trl,
          trail_pos := s'.core.trail_pos, trail_end := s'.core.trail_end,
          unassigned := s'.core.unassigned, unflushed := s'.core.unflushed,
          wvec := s'.core.wvec, wstk := s'.core.wstk, wlen := s'.core.wlen,
          wusable := s'.core.wusable, num_binary := s'.core.num_binary, oom := s'.core.oom }
        scratch := { s.scratch with phases := s'.scratch.phases,
                                      wsort := s'.scratch.wsort } } := by
      simpa [← heq] using hpost.lengths
    refine hQ r s'.core.arena s'.core.vals s'.core.flags s'.core.lvl s'.core.rsns s'.core.trl
      s'.core.trail_pos s'.core.trail_end s'.core.unassigned s'.core.unflushed s'.core.wvec
      s'.core.wstk s'.core.wlen s'.core.wusable s'.core.num_binary s'.core.oom
      s'.scratch.phases s'.scratch.wsort m' hlen' hpost.arena_frame
      (fun hf => by
        have hnr := hpost.non_root hf
        have hfr := (agreesExcept_arenaOnly_of_sweepCopy hpost.frame).mp hnr.frame
        exact ⟨hnr.ret_eq, hfr.1, hfr.2.1, hfr.2.2.1, hfr.2.2.2.1, hfr.2.2.2.2.1,
          hfr.2.2.2.2.2.1, hfr.2.2.2.2.2.2.1, hfr.2.2.2.2.2.2.2.1, hfr.2.2.2.2.2.2.2.2.1,
          hfr.2.2.2.2.2.2.2.2.2.1, hfr.2.2.2.2.2.2.2.2.2.2.1, hfr.2.2.2.2.2.2.2.2.2.2.2.1,
          hfr.2.2.2.2.2.2.2.2.2.2.2.2.1, hfr.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          hfr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hfr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          hfr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, hnr.copied⟩)
      (fun ht => by
        have hrt' := hpost.root ht
        have hw1 := hrt'.witness; have hw2 := hrt'.watches
        rw [← heq]
        exact ⟨hw1, hw2, hrt'.trail_mono, hrt'.ret_cases, hrt'.unsat_of_ret, hrt'.oom_of_ret,
          hrt'.oom_pres, hrt'.unit_trail, hrt'.copied_ok⟩)
      hm'
  · rintro ⟨c, F0, F_cur, s, R, rfl, hpre, hm, hQ⟩
    refine ⟨c, F0, F_cur, s, R, rfl, hpre.lengths, hpre.dst_le_src, hpre.old_sz_ge,
      hpre.src_bound, hpre.at_root_eq, hpre.src_lits_lt, hpre.root_inv, hm,
      fun r arena' vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' wlen' wu'
          nb' oom' ph' wsort' m' hlen' har hnr hrt hm' => ?_⟩
    let s' : FullState :=
      { s with
        core := { s.core with
          arena := arena', vals := vals', flags := flags', lvl := lvl', rsns := rsns',
          trl := trl', trail_pos := tp', trail_end := te', unassigned := unass',
          unflushed := unfl', wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu',
          num_binary := nb', oom := oom' }
        scratch := { s.scratch with phases := ph', wsort := wsort' } }
    have hfrm : AgreesExcept sweepCopyMask s s' :=
      (agreesExcept_sweepCopyMask_iff s s').mpr rfl
    exact hQ r s' m'
      ⟨hfrm, hlen', har,
        (fun hf => by
          obtain ⟨hr, hv, hfl, hlv, hrs, htr, htp, hte, hun, huf, hwv, hws, hwl, hwu, hnb,
            hoo, hph, hwso, hcp⟩ := hnr hf
          refine ⟨hr, (agreesExcept_arenaOnly_of_sweepCopy hfrm).mpr
            ⟨hv, hfl, hlv, hrs, htr, htp, hte, hun, huf, hwv, hws, hwl, hwu, hnb, hoo, hph,
              hwso⟩, hcp⟩),
        (fun ht => by
          obtain ⟨hw1, hw2, htm, hrc, hu, ho1, ho2, hut, hco⟩ := hrt ht
          exact ⟨hw1, hw2, htm, hrc, hu, ho1, ho2, hut, hco⟩)⟩ hm'

theorem fullSweepCopySpec_le_hdr : fullSweepCopySpec.Le fullSweepCopyHdrSpec :=
  fun a m Q X h => (fullSweepCopySpec_iff_hdr a m Q X).mp h

theorem fullSweepCopyHdrSpec_le : fullSweepCopyHdrSpec.Le fullSweepCopySpec :=
  fun a m Q X h => (fullSweepCopySpec_iff_hdr a m Q X).mpr h

theorem fullSweepCopyHdrSpec_xfree : Spec.XFree fullSweepCopyHdrSpec := by xfree

/-! ## 4. `fullAnalyzeRsnSpec` ↔ `fullAnalyzeRsnHdrSpec` -/

/-- `AgreesExcept` mask over `FullCoreState` for `full_analyze_rsn`: permits mutating only
`mrk`, `tmp`, `tmp_cnt`, `tmp_len`, `min_clr_len`, and `arena`. -/
@[expose] def analyzeRsnCoreMask (k : FullCoreState) : FullCoreState :=
  { k with mrk := [], tmp := [], tmp_cnt := 0, tmp_len := 0, min_clr_len := 0, arena := [] }

private theorem agreesExcept_analyzeRsnCore_iff (k k' : FullCoreState) :
    AgreesExcept analyzeRsnCoreMask k k' ↔
      k' = { k with
        mrk := k'.mrk, tmp := k'.tmp, tmp_cnt := k'.tmp_cnt,
        tmp_len := k'.tmp_len, min_clr_len := k'.min_clr_len, arena := k'.arena } := by
  constructor
  · intro h
    cases k; cases k'
    simp only [AgreesExcept, analyzeRsnCoreMask] at h
    cases h; rfl
  · intro h; rw [h]; rfl

/-- Precondition package for `full_analyze_rsn`. -/
structure FullAnalyzeRsnPre (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (cut : Nat) (s : FullState) (rsn : BitVec 32) : Prop where
  lengths : s.LengthsOk c
  witness_cut : FullWitnessCutInv c F0 F_cur cut s.core
  marks_cov : FullAnaMarksCov c s
  tmp_le : s.core.tmp_len ≤ s.core.cur_vars
  tmp_cnt_fit : s.core.tmp_cnt + s.core.cur_vars + 1 < 2 ^ 64
  rsn_ref : rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 →
    rsn.toNat ∈ fullArenaClauseRefs s

/-- Frame and invariant preservation sub-package for `full_analyze_rsn`. -/
structure FullAnalyzeRsnFrame (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (cut : Nat) (s s' : FullState) : Prop where
  core_frame : AgreesExcept analyzeRsnCoreMask s.core s'.core
  lengths : s'.LengthsOk c
  witness_cut : FullWitnessCutInv c F0 F_cur cut s'.core
  marks_cov : FullAnaMarksCov c s'
  ext_pres : FullExtScratchPres s s'
  work_stk2_eq : s'.scratch.work_stk2 = s.scratch.work_stk2
  tmp_len_ge : s.core.tmp_len ≤ s'.core.tmp_len
  tmp_len_le : s'.core.tmp_len ≤ s'.core.cur_vars
  tmp_cnt_ge : s.core.tmp_cnt ≤ s'.core.tmp_cnt
  arena_refs : fullArenaClauseRefs s' = fullArenaClauseRefs s
  arena_clauses : ∀ r ∈ fullArenaClauseRefs s,
    fullArenaClauseSize s' r = fullArenaClauseSize s r ∧
    fullArenaClauseGarb s' r = fullArenaClauseGarb s r ∧
    fullArenaClauseLits s' r = fullArenaClauseLits s r

/-- Mark, `tmp`-buffer, and counter sub-package for `full_analyze_rsn`. -/
structure FullAnalyzeRsnMarks (c : FullCfg) (s s' : FullState)
    (rsn skip_var : BitVec 32) (ok : Bool) : Prop where
  mrk_pres : ∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 ≠ 0#8 →
    s'.core.mrk[v]?.getD 0#8 = s.core.mrk[v]?.getD 0#8
  tmp_pres : ∀ k < s.core.tmp_len, s'.core.tmp[k]? = s.core.tmp[k]?
  new_mrk : ∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8 →
    s'.core.mrk[v]?.getD 0#8 ≠ 0#8 →
    ∃ l ∈ fullRsnLits s rsn, l / 2 = v ∧ v < s.core.cur_vars ∧ v ≠ skip_var.toNat ∧
      0 < (s.core.lvl[v]?.getD 0#32).toNat ∧
      (s.core.lvl[v]?.getD 0#32).toNat ≤ s.core.cur_level
  new_tmp : ∀ j, s.core.tmp_len ≤ j → j < s'.core.tmp_len →
    let l := (s'.core.tmp[j]?.getD 0#32).toNat
    l ∈ fullRsnLits s rsn ∧ l < 2 * s.core.cur_vars ∧ l / 2 ≠ skip_var.toNat ∧
    s.core.mrk[l / 2]?.getD 0#8 = 0#8 ∧ 0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
    (s.core.lvl[l / 2]?.getD 0#32).toNat < s.core.cur_level ∧
    s'.core.mrk[l / 2]?.getD 0#8 ≠ 0#8
  tmp_nodup : ∀ j1 j2, s.core.tmp_len ≤ j1 → j1 < j2 → j2 < s'.core.tmp_len →
    (s'.core.tmp[j1]?.getD 0#32).toNat / 2 ≠ (s'.core.tmp[j2]?.getD 0#32).toNat / 2
  tmp_cnt_eq : s'.core.tmp_cnt - s.core.tmp_cnt =
    ((List.range s.core.cur_vars).filter fun w =>
      decide (s.core.mrk[w]?.getD 0#8 = 0#8) && decide (s'.core.mrk[w]?.getD 0#8 ≠ 0#8) &&
      decide ((s.core.lvl[w]?.getD 0#32).toNat = s.core.cur_level)).length
  res_sz_eq : s'.scratch.res_sz = s.scratch.res_sz + BitVec.ofNat 64
    ((List.range s.core.cur_vars).filter fun w =>
      decide (s.core.mrk[w]?.getD 0#8 = 0#8) && decide (s'.core.mrk[w]?.getD 0#8 ≠ 0#8)).length
  ok_post : ok = true → rsn ≠ 0xFFFFFFFF#32 ∧
    s'.scratch.ant_sz = s.scratch.ant_sz + BitVec.ofNat 64 ((fullRsnLits s rsn).countP fun l =>
      decide (l / 2 < s.core.cur_vars ∧ 0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
        (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level)) ∧
    ∀ l ∈ fullRsnLits s rsn, l / 2 < s.core.cur_vars ∧
      (l / 2 ≠ skip_var.toNat →
        (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat → s'.core.mrk[l / 2]?.getD 0#8 ≠ 0#8) ∧
        (s.core.mrk[l / 2]?.getD 0#8 = 0#8 →
          (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level ∧
          (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat →
            (s.core.lvl[l / 2]?.getD 0#32).toNat < s.core.cur_level →
            ∃ j, s.core.tmp_len ≤ j ∧ j < s'.core.tmp_len ∧
              (s'.core.tmp[j]?.getD 0#32).toNat / 2 = l / 2)))

/-- Combined postcondition package for `full_analyze_rsn`. -/
structure FullAnalyzeRsnPost (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (cut : Nat) (s s' : FullState) (rsn skip_var : BitVec 32) (ok : Bool) : Prop where
  frame : FullAnalyzeRsnFrame c F0 F_cur cut s s'
  marks : FullAnalyzeRsnMarks c s s' rsn skip_var ok

theorem FullAnalyzeRsnPost.hdrView_eq {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {s s' : FullState} {rsn skip_var : BitVec 32} {ok : Bool}
    (_h : FullAnalyzeRsnPost c F0 F_cur cut s s' rsn skip_var ok) :
    HdrView.decode (hdrTailWords c s') = some (HdrView.ofCfg c) :=
  HdrView.decode_ofCfg c s'

/-- Concise `HdrView`/`AgreesExcept` contract equivalent to `fullAnalyzeRsnSpec`. -/
@[expose] def fullAnalyzeRsnHdrSpec : Spec [i64, i32, i32] [.bool] :=
  fun (h, rsn, skip_var, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (cut : Nat) (s : FullState)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ FullAnalyzeRsnPre c F0 F_cur cut s rsn ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
        FullAnalyzeRsnPost c F0 F_cur cut s s' rsn skip_var ok →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

theorem fullAnalyzeRsnSpec_iff_hdr (a : Tup Val [i64, i32, i32]) (m : Mem 64)
    (Q : Post [.bool]) (X : XPost) :
    fullAnalyzeRsnSpec a m Q X ↔ fullAnalyzeRsnHdrSpec a m Q X := by
  rcases a with ⟨h, rsn, skip_var, ⟨⟩⟩
  constructor
  · rintro ⟨c, F0, F_cur, cut, s, R, rfl, hlen, hwc, hmc, htl, htc, href, hm, hQ⟩
    refine ⟨c, F0, F_cur, cut, s, R, rfl, ⟨hlen, hwc, hmc, htl, htc, href⟩, hm,
      fun ok s' m' hpost hm' => ?_⟩
    have hcore := (agreesExcept_analyzeRsnCore_iff s.core s'.core).mp hpost.frame.core_frame
    have hs' : s' = { s with
        core := { s.core with
          mrk := s'.core.mrk, tmp := s'.core.tmp, tmp_cnt := s'.core.tmp_cnt,
          tmp_len := s'.core.tmp_len, min_clr_len := s'.core.min_clr_len,
          arena := s'.core.arena }
        scratch := s'.scratch } := by
      cases s'; dsimp only at *; rw [← hcore]
    rw [hs'] at hm'
    have hfr := hpost.frame; have hmk := hpost.marks
    have hl' := hfr.lengths; have hwc' := hfr.witness_cut; have hmc' := hfr.marks_cov
    have hep := hfr.ext_pres; have har := hfr.arena_refs; have hac := hfr.arena_clauses
    have hcv : s'.core.cur_vars = s.core.cur_vars := by rw [hcore]
    have htll : s'.core.tmp_len ≤ s.core.cur_vars := hcv ▸ hfr.tmp_len_le
    rw [hs'] at hl' hwc' hmc' hep har hac
    exact hQ ok s'.core.mrk s'.core.tmp s'.core.tmp_cnt s'.core.tmp_len s'.core.min_clr_len
      s'.core.arena s'.scratch m' hl' hwc' hmc' hep hfr.work_stk2_eq hfr.tmp_len_ge
      htll hfr.tmp_cnt_ge har hac hmk.mrk_pres hmk.tmp_pres hmk.new_mrk
      hmk.new_tmp hmk.tmp_nodup hmk.tmp_cnt_eq hmk.res_sz_eq hmk.ok_post hm'
  · rintro ⟨c, F0, F_cur, cut, s, R, rfl, hpre, hm, hQ⟩
    refine ⟨c, F0, F_cur, cut, s, R, rfl, hpre.lengths, hpre.witness_cut, hpre.marks_cov,
      hpre.tmp_le, hpre.tmp_cnt_fit, hpre.rsn_ref, hm,
      fun ok mrk' tmp' tc' tl' mcl' arena' sc' m'
          hl' hwc' hmc' hep hws2 hlg hll hcg har hac hmp htp hnm hnt hnd htc hrs hok hm' => ?_⟩
    let s' : FullState :=
      { s with
        core := { s.core with
          mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl', min_clr_len := mcl',
          arena := arena' }
        scratch := sc' }
    have hcore : AgreesExcept analyzeRsnCoreMask s.core s'.core :=
      (agreesExcept_analyzeRsnCore_iff s.core s'.core).mpr rfl
    exact hQ ok s' m'
      ⟨⟨hcore, hl', hwc', hmc', hep, hws2, hlg, hll, hcg, har, hac⟩,
        ⟨hmp, htp, hnm, hnt, hnd, htc, hrs, hok⟩⟩ hm'

theorem fullAnalyzeRsnSpec_le_hdr : fullAnalyzeRsnSpec.Le fullAnalyzeRsnHdrSpec :=
  fun a m Q X h => (fullAnalyzeRsnSpec_iff_hdr a m Q X).mp h

theorem fullAnalyzeRsnHdrSpec_le : fullAnalyzeRsnHdrSpec.Le fullAnalyzeRsnSpec :=
  fun a m Q X h => (fullAnalyzeRsnSpec_iff_hdr a m Q X).mpr h

theorem fullAnalyzeRsnHdrSpec_xfree : Spec.XFree fullAnalyzeRsnHdrSpec := by xfree

end LeanQbe.T.Examples.Kissat.Proof.Spec