/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.LayerAXorF2
public import LeanQbe.T.Examples.Kissat.FullM8XorGauss
public import LeanQbe.T.Examples.Kissat.FullSpec2
public import LeanQbe.T.Examples.Kissat.FullSpec3
import LeanQbe.T.Examples.Kissat.FullAssignAddLemmas1
import LeanQbe.T.Examples.Kissat.FullLearnAnaLemmas1
import LeanQbe.T.Examples.Kissat.FullM6ProofUtil
import LeanQbe.T.Examples.Kissat.FullM4VivBceProof1
import LeanQbe.T.Examples.Kissat.FullM6Transport1
public meta import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.C0Agrees
public meta import Lean.Elab.Tactic
public meta import LeanQbe.T.Logic.C0Step

/-!
# Kissat M8 XOR / $\mathbb{F}_2$ Gauss-Jordan Proofs — Core & Leaf Helpers (`FullM8XorGaussProof0`)

Shared bitvector, framing, and witness helpers, soundness invariants (`XorHtInv`, `XorEqPoolOk`,
`XorMatOk`, `ufRoot`), leaf contracts, and `8` leaf `Func.wp` proofs (`full_xor_parity_mask`,
`full_xor_read_u64`, `full_xor_write_u64`, `full_xor_swap_rows`, `full_xor_xor_rows`,
`full_xor_set_bit`, `full_xor_uf_find`, `full_xor_sort5`).
-/

set_option autoImplicit false

local elab "c0_hstraight" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, splitJnz := false } 2000

local elab "c0_hstraight!" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, splitJnz := false, strictMem := true } 2000

public section

namespace LeanQbe.T.Examples.Kissat.FullM8XorGauss

open Std Std.Sat Std.ExtHashMap LeanQbe.T.C0Step
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

open scoped FullArenaTactics FullAssignAddTactics
open FullAssignAddTactics LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open LeanQbe.T.Examples.Kissat.Full.FullDenseWatchHelpers

/-! ## 1. Bitvector, Array, Framing & Witness Helpers (`private`) -/

theorem bv_zext32_toNat (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide))]

theorem bv64_toNat_setWidth32_lt {x : BitVec 64} (hx : x.toNat < 2 ^ 32) :
    (x.setWidth 32).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hx]

theorem list_getElem_congr {α : Type} {xs : List α} {i j : Nat}
    (h : i = j) (hi : i < xs.length) (hj : j < xs.length) : xs[i]'hi = xs[j]'hj := by
  subst h; rfl

theorem cpopNatRec_zero_iff (w : BitVec 64) :
    ∀ k acc, w.cpopNatRec k acc = 0 ↔ acc = 0 ∧ ∀ i < k, w.getLsbD i = false
  | 0, acc => by
    simp [BitVec.cpopNatRec]
  | k + 1, acc => by
    change w.cpopNatRec k (acc + (w.getLsbD k).toNat) = 0 ↔
      acc = 0 ∧ ∀ i < k + 1, w.getLsbD i = false
    rw [cpopNatRec_zero_iff w k (acc + (w.getLsbD k).toNat)]
    constructor
    · rintro ⟨hadd, hlt⟩
      have hacc : acc = 0 := by omega
      have hbit0 : (w.getLsbD k).toNat = 0 := by omega
      have hkf : w.getLsbD k = false := by cases hb : w.getLsbD k <;> simp [hb] at hbit0 ⊢
      refine ⟨hacc, fun i hi => ?_⟩
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with h | rfl
      · exact hlt i h
      · exact hkf
    · rintro ⟨rfl, hall⟩
      have hkf : w.getLsbD k = false := hall k (Nat.lt_succ_self k)
      exact ⟨by simp [hkf], fun i hi => hall i (Nat.lt_trans hi (Nat.lt_succ_self k))⟩

theorem cpopNatRec_le (w : BitVec 64) :
    ∀ k acc, w.cpopNatRec k acc ≤ acc + k
  | 0, acc => by simp [BitVec.cpopNatRec]
  | k + 1, acc => by
    change w.cpopNatRec k (acc + (w.getLsbD k).toNat) ≤ acc + (k + 1)
    have ih := cpopNatRec_le w k (acc + (w.getLsbD k).toNat)
    have hb : (w.getLsbD k).toNat ≤ 1 := by cases w.getLsbD k <;> decide
    omega

theorem cpop64_toNat_le (w : BitVec 64) : w.cpop.toNat ≤ 64 := by
  rw [BitVec.toNat_cpop]
  have h := cpopNatRec_le w 64 0
  omega

theorem cpop64_eq_zero_iff (w : BitVec 64) : w.cpop = 0#64 ↔ w = 0#64 := by
  constructor
  · intro h
    have ht : w.cpop.toNat = 0 := by rw [h]; rfl
    rw [BitVec.toNat_cpop] at ht
    have hbits := ((cpopNatRec_zero_iff w 64 0).mp ht).2
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simpa using hbits i hi
  · intro h; subst h; decide

theorem maskParity3_eq_cpop {m : Nat} (hm : m < 8) :
    maskParity 3 m = (((BitVec.ofNat 64 m).cpop &&& 1#64) != 0#64) := by
  have hc : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem maskParity4_eq_cpop {m : Nat} (hm : m < 16) :
    maskParity 4 m = (((BitVec.ofNat 64 m).cpop &&& 1#64) != 0#64) := by
  have hc : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨
      m = 8 ∨ m = 9 ∨ m = 10 ∨ m = 11 ∨ m = 12 ∨ m = 13 ∨ m = 14 ∨ m = 15 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem fullLitMarksClear_of_eq {c : FullCfg} {s s' : FullState}
    (h : FullLitMarksClear c s) (h1 : s'.core.mrk = s.core.mrk)
    (h2 : s'.core.lit_mark = s.core.lit_mark) : FullLitMarksClear c s' :=
  ⟨fun v hv => by rw [h1]; exact h.1 v hv, fun l hl => by rw [h2]; exact h.2 l hl⟩

theorem fullArenaVarsNodup_of_eq {s s' : FullState} (h : FullArenaVarsNodup s)
    (h1 : s'.core.arena = s.core.arena) (h2 : s'.core.arena_len = s.core.arena_len) :
    FullArenaVarsNodup s' := by
  unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseRefsCore
    fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
    fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore at h ⊢
  rw [h1, h2]; exact h

theorem fullWitnessInv_with_tmp {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (tmp' : List (BitVec 32)) :
    FullWitnessInv c F0 F_cur { k with tmp := tmp' } :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }

theorem fullWitnessInv_with_inconsistent {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k)
    (inc' : BitVec 64) (hu : inc' ≠ 0#64 → (cnfOfClauses F_cur).Unsat) :
    FullWitnessInv c F0 F_cur { k with inconsistent := inc' } :=
  { hw with
    inconsistent_sound := hu
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }

theorem fullSparseInvW_upd_scratch_buf {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (h : FullSparseInvW c F0 F_cur s)
    {scr' : List (BitVec 32)} (hs : scr'.length = s.scratch.scratch_buf.length) :
    FullSparseInvW c F0 F_cur { s with scratch := { s.scratch with scratch_buf := scr' } } :=
  let st := fullState_upd_scratch_buf_step h.1 hs
  fullSparseInvW_of_core_eq h st.1 st.2.1 st.2.2.1

theorem fullSparseInvW_upd_work_stk1 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (h : FullSparseInvW c F0 F_cur s)
    {ws1' : List (BitVec 32)} (hw1 : ws1'.length = s.scratch.work_stk1.length) :
    FullSparseInvW c F0 F_cur { s with scratch := { s.scratch with work_stk1 := ws1' } } :=
  let st := fullState_upd_work_stk1_step h.1 hw1
  fullSparseInvW_of_core_eq h st.1 st.2.1 st.2.2.1

theorem fullSparseInvW_upd_work_stk2 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (h : FullSparseInvW c F0 F_cur s)
    {ws2' : List (BitVec 32)} (hw2 : ws2'.length = s.scratch.work_stk2.length) :
    FullSparseInvW c F0 F_cur { s with scratch := { s.scratch with work_stk2 := ws2' } } :=
  let st := fullState_upd_work_stk2_step h.1 hw2
  fullSparseInvW_of_core_eq h st.1 st.2.1 st.2.2.1

theorem fullSparseInvW_upd_tarjan_reach {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (h : FullSparseInvW c F0 F_cur s)
    {tr' : List (BitVec 32)} (htr : tr'.length = s.scratch.tarjan_reach.length) :
    FullSparseInvW c F0 F_cur { s with scratch := { s.scratch with tarjan_reach := tr' } } := by
  let sc' : FullScratch := { s.scratch with tarjan_reach := tr' }
  have hsc : sc'.LengthsOk c := fullScratch_lengthsOk_of_arr_len h.1.2
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl htr rfl rfl rfl rfl rfl rfl rfl rfl
  exact fullSparseInvW_of_core_eq h ⟨h.1.1, hsc⟩ rfl ⟨rfl, rfl⟩

theorem fullSparseInvW_upd_wsort {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (h : FullSparseInvW c F0 F_cur s)
    {ws' : List (BitVec 32)} (hw : ws'.length = s.scratch.wsort.length) :
    FullSparseInvW c F0 F_cur { s with scratch := { s.scratch with wsort := ws' } } :=
  let st := fullState_upd_wsort_step h.1 hw
  fullSparseInvW_of_core_eq h st.1 st.2.1 st.2.2.1.1

theorem fullSparseInvW_upd_tmp {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (h : FullSparseInvW c F0 F_cur s)
    {tmp' : List (BitVec 32)} (ht : tmp'.length = s.core.tmp.length) :
    FullSparseInvW c F0 F_cur { s with core := { s.core with tmp := tmp' } } := by
  have hcok : ({ s.core with tmp := tmp' } : FullCoreState).LengthsOk c :=
    { h.1.core_ok with tmp_len_arr := ht.trans h.1.core_ok.tmp_len_arr }
  refine ⟨⟨hcok, h.1.2⟩, fullWitnessInv_with_tmp h.2.1 tmp',
    fullLitMarksClear_of_eq h.2.2.1 rfl rfl,
    fullArenaVarsNodup_of_eq h.2.2.2.1 rfl rfl, ?_, h.2.2.2.2.2⟩
  exact h.2.2.2.2.1.of_pres ⟨rfl, rfl⟩ fun _ hr => hr

theorem fullSparseInvW_upd_oom {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (h : FullSparseInvW c F0 F_cur s)
    (oom' : BitVec 64) :
    FullSparseInvW c F0 F_cur { s with core := { s.core with oom := oom' } } := by
  have hcok : ({ s.core with oom := oom' } : FullCoreState).LengthsOk c :=
    { h.1.core_ok with vals_len := h.1.core_ok.vals_len }
  refine ⟨⟨hcok, h.1.2⟩, fullWitnessInv_with_oom h.2.1 oom',
    fullLitMarksClear_of_eq h.2.2.1 rfl rfl,
    fullArenaVarsNodup_of_eq h.2.2.2.1 rfl rfl, ?_, h.2.2.2.2.2⟩
  exact h.2.2.2.2.1.of_pres ⟨rfl, rfl⟩ fun _ hr => hr

theorem fullSparseInvW_upd_inc {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (h : FullSparseInvW c F0 F_cur s)
    (inc' : BitVec 64) (hu : inc' ≠ 0#64 → (cnfOfClauses F_cur).Unsat) :
    FullSparseInvW c F0 F_cur { s with core := { s.core with inconsistent := inc' } } := by
  have hcok : ({ s.core with inconsistent := inc' } : FullCoreState).LengthsOk c :=
    { h.1.core_ok with vals_len := h.1.core_ok.vals_len }
  refine ⟨⟨hcok, h.1.2⟩, fullWitnessInv_with_inconsistent h.2.1 inc' hu,
    fullLitMarksClear_of_eq h.2.2.1 rfl rfl,
    fullArenaVarsNodup_of_eq h.2.2.2.1 rfl rfl, ?_, h.2.2.2.2.2⟩
  exact h.2.2.2.2.1.of_pres ⟨rfl, rfl⟩ fun _ hr => hr

theorem unsat_of_sparseW_inconsistent {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (h : FullSparseInvW c F0 F_cur s)
    (hu : (cnfOfClauses F_cur).Unsat) : F0.Unsat :=
  h.2.1.ext_sound.2 hu

@[expose] def FullTmpScrRest (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  (array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
   array (t := i32) c.pReason s.core.rsns ⋆ array (t := i32) c.pTrail s.core.trl ⋆
   array (t := i32) c.pTrailPos s.core.trail_pos ⋆ array (t := i32) c.pMinClr s.core.min_clr) ⋆
  (array (t := i32) c.pDelayed s.scratch.delayed ⋆ array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
   array (t := i32) c.pExtendStk s.scratch.extend_stk) ⋆
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
  FullCoreByteArrs c s.core ⋆ FullCoreU32B c s.core ⋆ FullCoreDynArrs c s.core ⋆
  FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆
  FullScrWksArrs c s.scratch ⋆ FullScrMetaArrs c s.scratch ⋆ c.pad

theorem focus_full_tmp_scr {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) :
    (array (t := i32) c.pTmp s.core.tmp ⋆
      (array (t := i32) c.pScratchBuf s.scratch.scratch_buf ⋆ (FullTmpScrRest c s ⋆ R))) m := by
  unfold FullMem FullCoreArrays FullCoreU32A FullScratchArrays FullScrDynArrs at hm
  unfold FullTmpScrRest
  ecancel

theorem unfocus_full_tmp_scr {c : FullCfg} {s : FullState}
    {tmp' scr' : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (array (t := i32) c.pTmp tmp' ⋆
      (array (t := i32) c.pScratchBuf scr' ⋆ (FullTmpScrRest c s ⋆ R))) m) :
    (FullMem c { s with
      core := { s.core with tmp := tmp' }
      scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m := by
  change (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
      s.core.d_cur s.core.d_val ⋆
    array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
    (FullCoreByteArrs c s.core ⋆
      (array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
       array (t := i32) c.pReason s.core.rsns ⋆ array (t := i32) c.pTrail s.core.trl ⋆
       array (t := i32) c.pTrailPos s.core.trail_pos ⋆ array (t := i32) c.pTmp tmp' ⋆
       array (t := i32) c.pMinClr s.core.min_clr) ⋆
      FullCoreU32B c s.core ⋆ FullCoreDynArrs c s.core) ⋆
    (FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆ FullScrWksArrs c s.scratch ⋆
      FullScrMetaArrs c s.scratch ⋆
      (array (t := i32) c.pDelayed s.scratch.delayed ⋆
       array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
       array (t := i32) c.pExtendStk s.scratch.extend_stk ⋆
       array (t := i32) c.pScratchBuf scr')) ⋆
    c.pad ⋆ R) m
  unfold FullTmpScrRest at hm
  ecancel

@[expose] def FullScrBufRest (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  (array (t := i32) c.pDelayed s.scratch.delayed ⋆ array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
   array (t := i32) c.pExtendStk s.scratch.extend_stk) ⋆
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆ FullCoreArrays c s.core ⋆
  FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆
  FullScrWksArrs c s.scratch ⋆ FullScrMetaArrs c s.scratch ⋆ c.pad

theorem focus_full_scr_buf {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) :
    (array (t := i32) c.pScratchBuf s.scratch.scratch_buf ⋆ (FullScrBufRest c s ⋆ R)) m := by
  unfold FullMem FullScratchArrays FullScrDynArrs at hm; unfold FullScrBufRest; ecancel

theorem unfocus_full_scr_buf {c : FullCfg} {s : FullState} {scr' : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (array (t := i32) c.pScratchBuf scr' ⋆ (FullScrBufRest c s ⋆ R)) m) :
    (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m := by
  change (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
      s.core.d_cur s.core.d_val ⋆
    array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆ FullCoreArrays c s.core ⋆
    (FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆ FullScrWksArrs c s.scratch ⋆
      FullScrMetaArrs c s.scratch ⋆
      (array (t := i32) c.pDelayed s.scratch.delayed ⋆
       array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
       array (t := i32) c.pExtendStk s.scratch.extend_stk ⋆
       array (t := i32) c.pScratchBuf scr')) ⋆
    c.pad ⋆ R) m
  unfold FullScrBufRest at hm; ecancel

@[expose] def FullTmpOnlyRest (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  (array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
   array (t := i32) c.pReason s.core.rsns ⋆ array (t := i32) c.pTrail s.core.trl ⋆
   array (t := i32) c.pTrailPos s.core.trail_pos ⋆ array (t := i32) c.pMinClr s.core.min_clr) ⋆
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
  FullCoreByteArrs c s.core ⋆ FullCoreU32B c s.core ⋆ FullCoreDynArrs c s.core ⋆
  FullScratchArrays c s.scratch ⋆ c.pad

theorem focus_full_tmp_only {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) :
    (array (t := i32) c.pTmp s.core.tmp ⋆ (FullTmpOnlyRest c s ⋆ R)) m := by
  unfold FullMem FullCoreArrays FullCoreU32A at hm; unfold FullTmpOnlyRest; ecancel

theorem unfocus_full_tmp_only {c : FullCfg} {s : FullState} {tmp' : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (array (t := i32) c.pTmp tmp' ⋆ (FullTmpOnlyRest c s ⋆ R)) m) :
    (FullMem c { s with core := { s.core with tmp := tmp' } } ⋆ R) m := by
  change (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
      s.core.d_cur s.core.d_val ⋆
    array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
    (FullCoreByteArrs c s.core ⋆
      (array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
       array (t := i32) c.pReason s.core.rsns ⋆ array (t := i32) c.pTrail s.core.trl ⋆
       array (t := i32) c.pTrailPos s.core.trail_pos ⋆ array (t := i32) c.pTmp tmp' ⋆
       array (t := i32) c.pMinClr s.core.min_clr) ⋆
      FullCoreU32B c s.core ⋆ FullCoreDynArrs c s.core) ⋆
    FullScratchArrays c s.scratch ⋆ c.pad ⋆ R) m
  unfold FullTmpOnlyRest at hm; ecancel

@[expose] def FullParRest (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  (array (t := i32) c.pWsort s.scratch.wsort ⋆
   array (t := i32) c.pWorkStk2 s.scratch.work_stk2 ⋆
   array (t := i32) c.pTarjanMark s.scratch.tarjan_mark ⋆
   array (t := i32) c.pTarjanReach s.scratch.tarjan_reach) ⋆
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆ FullCoreArrays c s.core ⋆
  FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆
  FullScrMetaArrs c s.scratch ⋆ FullScrDynArrs c s.scratch ⋆ c.pad

theorem focus_full_par {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) :
    (array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆ (FullParRest c s ⋆ R)) m := by
  unfold FullMem FullScratchArrays FullScrWksArrs at hm; unfold FullParRest; ecancel

theorem unfocus_full_par {c : FullCfg} {s : FullState} {ws1' : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (array (t := i32) c.pWorkStk1 ws1' ⋆ (FullParRest c s ⋆ R)) m) :
    (FullMem c { s with scratch := { s.scratch with work_stk1 := ws1' } } ⋆ R) m := by
  change (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
      s.core.d_cur s.core.d_val ⋆
    array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆ FullCoreArrays c s.core ⋆
    (FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆
      (array (t := i32) c.pWsort s.scratch.wsort ⋆
       array (t := i32) c.pWorkStk1 ws1' ⋆
       array (t := i32) c.pWorkStk2 s.scratch.work_stk2 ⋆
       array (t := i32) c.pTarjanMark s.scratch.tarjan_mark ⋆
       array (t := i32) c.pTarjanReach s.scratch.tarjan_reach) ⋆
      FullScrMetaArrs c s.scratch ⋆ FullScrDynArrs c s.scratch) ⋆
    c.pad ⋆ R) m
  unfold FullParRest at hm; ecancel

/-! ## 2. Pure $\mathbb{F}_2$ Pool, Hash Table, Matrix & List Helpers (`private`) -/

theorem perm_swap_take {α : Type} {xs : List α} {i j n : Nat}
    (hi : i < j) (hj : j < n) (hn : n ≤ xs.length) :
    ((xs.set i (xs[j]'(by omega))).set j (xs[i]'(by omega))).take n |>.Perm (xs.take n) := by
  have ha : ((xs.set i xs[j]).set j xs[i]).take n =
      (((xs.take n).set i ((xs.take n)[j]'(by rw [List.length_take]; omega))).set j
        ((xs.take n)[i]'(by rw [List.length_take]; omega))) := by
    apply List.ext_getElem
    · simp [List.length_take]
    · intro k hk1 _
      rw [List.length_take, List.length_set, List.length_set, Nat.min_eq_left hn] at hk1
      by_cases hkj : k = j
      · simp only [List.getElem_take, List.getElem_set, hkj, ↓reduceIte]
      · by_cases hki : k = i
        · simp only [List.getElem_take, List.getElem_set, hki, ↓reduceIte]
        · simp only [List.getElem_take, List.getElem_set]
  rw [ha]
  exact List.set_set_perm (by rw [List.length_take]; omega) (by rw [List.length_take]; omega)

theorem strictSorted_of_adj {vs : List Nat}
    (hadj : ∀ p, p + 1 < vs.length → vs[p]! < vs[p + 1]!) : List.Pairwise (· < ·) vs := by
  have hlt : ∀ i j, i < j → j < vs.length → vs[i]! < vs[j]! := by
    intro i j hij hj
    induction hij with
    | refl => exact hadj i hj
    | step _ ih =>
      rename_i m hm
      exact Nat.lt_trans (ih (by omega)) (hadj m hj)
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  have hg := hlt i j hij hj
  simpa [hi, hj] using hg

theorem strictSorted_lt_of_take {xs : List (BitVec 32)} {k : Nat}
    (hk : k ≤ xs.length)
    (hs : List.Pairwise (· < ·) ((xs.take k).map fun x => x.toNat / 2)) :
    ∀ i j, i < j → j < k →
      (xs[i]?.getD 0#32).toNat / 2 < (xs[j]?.getD 0#32).toNat / 2 := by
  rw [List.pairwise_iff_getElem] at hs
  intro i j hij hjk
  have hl : ((xs.take k).map fun x => x.toNat / 2).length = k := by
    rw [List.length_map, List.length_take, Nat.min_eq_left hk]
  have h := hs i j (by omega) (by omega) hij
  simp only [List.getElem_map, List.getElem_take] at h
  rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)]
  exact h

/-- Hash-table invariant (`ht_cap` 7-word slots at `scr[0 .. 7 * ht_cap)`). -/
@[expose] def XorHtInv (F : CNF Nat) (cv ht_cap : Nat) (scr : List (BitVec 32)) : Prop :=
  ∀ s < ht_cap,
    let sb := s * 7
    let sk := (scr[sb]?.getD 0#32).toNat
    sk = 0 ∨
      (3 ≤ sk ∧ sk ≤ 5 ∧
       let vs := (List.range sk).map fun i => (scr[sb + 2 + i]?.getD 0#32).toNat
       List.Pairwise (· < ·) vs ∧ (∀ v ∈ vs, v < cv) ∧
       let seen := scr[sb + 1]?.getD 0#32
       ∀ m < 2 ^ sk, seen.getLsbD m = true → F.EntailsClause (cnfClause (xorMaskClause vs m)))

/-- Pool invariant over `scr[p .. eq_end)` with `clen = 0` dead slots allowed. -/
inductive XorEqPoolOk (F : CNF Nat) (cv : Nat) (scr : List (BitVec 32)) (eq_end : Nat) :
    Nat → Prop where
  | done : XorEqPoolOk F cv scr eq_end eq_end
  | step {p : Nat} {hdr : BitVec 32} {stride clen : Nat} :
      p < eq_end →
      scr[p]? = some hdr →
      stride = ((hdr >>> 16#32) &&& 0x7FFF#32).toNat →
      clen = (hdr &&& 0xFFFF#32).toNat →
      p + 1 + stride ≤ eq_end →
      (clen = 0 ∨
        (0 < clen ∧ clen ≤ stride ∧
         let vs := (List.range clen).map fun i => (scr[p + 1 + i]?.getD 0#32).toNat
         List.Pairwise (· < ·) vs ∧ (∀ v ∈ vs, v < cv) ∧
         XorVarsSound F vs ((hdr >>> 31#32) != 0#32))) →
      XorEqPoolOk F cv scr eq_end (p + 1 + stride) →
      XorEqPoolOk F cv scr eq_end p

theorem xorEqPoolOk_start_le {F : CNF Nat} {cv : Nat} {scr : List (BitVec 32)}
    {eq_end p : Nat} (h : XorEqPoolOk F cv scr eq_end p) : p ≤ eq_end := by
  cases h with
  | done => exact Nat.le_refl _
  | step hp => exact Nat.le_of_lt hp

theorem xorEqPoolOk_congr {F : CNF Nat} {cv : Nat} {scr1 scr2 : List (BitVec 32)}
    {eq_end p : Nat} (h : XorEqPoolOk F cv scr1 eq_end p)
    (heq : ∀ i, p ≤ i → i < eq_end → scr2[i]? = scr1[i]?) :
    XorEqPoolOk F cv scr2 eq_end p := by
  induction h with
  | done => exact .done
  | @step p hdr stride clen hp hhdr hst hcl hbd hbody hrest ih =>
    refine .step hp (by rw [heq _ (Nat.le_refl _) hp, hhdr]) hst hcl hbd ?_
      (ih fun i hi1 hi2 => heq i (by omega) hi2)
    rcases hbody with rfl | ⟨hpos, hle, hss, hlt, hsnd⟩
    · exact Or.inl rfl
    · refine Or.inr ⟨hpos, hle, ?_⟩
      have hvs : (List.range clen).map (fun i => (scr2[p + 1 + i]?.getD 0#32).toNat) =
          (List.range clen).map (fun i => (scr1[p + 1 + i]?.getD 0#32).toNat) := by
        refine List.map_congr_left fun i hi => ?_
        have him : i < clen := List.mem_range.mp hi
        rw [heq (p + 1 + i) (by omega) (by omega)]
      rw [hvs]
      exact ⟨hss, hlt, hsnd⟩

/-- Block header starts along `scr[p .. eq_end)`. -/
@[expose] def poolStarts (scr : List (BitVec 32)) (eq_end p : Nat) : Nat → List Nat
  | 0 => []
  | fuel + 1 =>
    if p < eq_end then
      let st := (((scr[p]?.getD 0#32) >>> 16#32) &&& 0x7FFF#32).toNat
      p :: poolStarts scr eq_end (p + 1 + st) fuel
    else []

theorem poolStarts_ge {scr : List (BitVec 32)} {eq_end : Nat} :
    ∀ {fuel p q : Nat}, q ∈ poolStarts scr eq_end p fuel → p ≤ q
  | 0, _, _, h => nomatch h
  | fuel + 1, p, q, h => by
    unfold poolStarts at h
    split at h
    · rcases List.mem_cons.mp h with rfl | hrest
      · exact Nat.le_refl _
      · have ih := poolStarts_ge hrest; omega
    · exact nomatch h

theorem poolStarts_step_iff {scr : List (BitVec 32)} {eq_end fuel p q : Nat}
    (hp : p < eq_end) :
    q ∈ poolStarts scr eq_end p (fuel + 1) ↔
      q = p ∨
        (p + 1 + (((scr[p]?.getD 0#32) >>> 16#32) &&& 0x7FFF#32).toNat ≤ q ∧
         q ∈ poolStarts scr eq_end
           (p + 1 + (((scr[p]?.getD 0#32) >>> 16#32) &&& 0x7FFF#32).toNat) fuel) := by
  simp only [poolStarts, hp, ↓reduceIte, List.mem_cons]
  constructor
  · rintro (rfl | hr)
    · exact Or.inl rfl
    · exact Or.inr ⟨poolStarts_ge hr, hr⟩
  · rintro (rfl | ⟨_, hr⟩)
    · exact Or.inl rfl
    · exact Or.inr hr

theorem poolStarts_congr {scr1 scr2 : List (BitVec 32)} {eq_end : Nat} :
    ∀ {fuel p : Nat},
      (∀ i, p ≤ i → i < eq_end →
        (((scr2[i]?.getD 0#32) >>> 16#32) &&& 0x7FFF#32) =
        (((scr1[i]?.getD 0#32) >>> 16#32) &&& 0x7FFF#32)) →
      poolStarts scr2 eq_end p fuel = poolStarts scr1 eq_end p fuel
  | 0, _, _ => rfl
  | fuel + 1, p, heq => by
    unfold poolStarts
    split
    · rename_i hp
      have hst := heq p (Nat.le_refl _) hp
      dsimp only
      rw [hst]
      congr 1
      exact poolStarts_congr fun i hi1 hi2 => heq i (by omega) hi2
    · rfl

theorem xorEqPoolOk_zero_at {F : CNF Nat} {cv : Nat} {scr : List (BitVec 32)}
    {eq_end p fuel q : Nat} (h : XorEqPoolOk F cv scr eq_end p)
    (hq : q ∈ poolStarts scr eq_end p fuel)
    (hscr : eq_end ≤ scr.length) :
    XorEqPoolOk F cv (scr.set q (scr[q]?.getD 0#32 &&& 0x7FFF0000#32)) eq_end p := by
  induction h generalizing fuel with
  | done =>
    cases fuel with
    | zero => exact .done
    | succ f =>
      unfold poolStarts at hq; simp at hq
  | step =>
    rename_i p0 hdr0 st0 cl0 hp hhdr hst hcl hbd hbody hrest ih
    let wq := scr[q]?.getD 0#32 &&& 0x7FFF0000#32
    cases fuel with
    | zero => exact nomatch hq
    | succ f =>
      have hst' : (((scr[p0]?.getD 0#32) >>> 16#32) &&& 0x7FFF#32).toNat = st0 := by
        simp [hhdr, hst]
      rw [poolStarts_step_iff hp, hst'] at hq
      rcases hq with rfl | ⟨hle, hrest_q⟩
      · have hq_len : q < scr.length := by omega
        have hne : ∀ i, q + 1 + st0 ≤ i → (scr.set q wq)[i]? = scr[i]? := fun i hi =>
          List.getElem?_set_ne (by omega)
        have hwq_st : ((wq >>> 16#32) &&& 0x7FFF#32).toNat = st0 := by
          have hwq_eq : wq = hdr0 &&& 0x7FFF0000#32 := by simp [wq, hhdr]
          have hsh : ((hdr0 &&& 0x7FFF0000#32) >>> 16#32 &&& 0x7FFF#32) =
              ((hdr0 >>> 16#32) &&& 0x7FFF#32) := by
            have hand_sh : ∀ (a b : BitVec 32) (k : Nat),
                (a &&& b) >>> k = (a >>> k) &&& (b >>> k) := fun a b k => by
              apply BitVec.eq_of_getLsbD_eq; intro i _
              simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight]
            rw [show ((hdr0 &&& 0x7FFF0000#32) >>> 16#32) =
                (hdr0 &&& 0x7FFF0000#32) >>> 16 from rfl, hand_sh]
            change ((hdr0 >>> 16#32) &&& 0x7FFF#32) &&& 0x7FFF#32 = _
            rw [BitVec.and_assoc, show (0x7FFF#32 &&& 0x7FFF#32 : BitVec 32) = 0x7FFF#32 from rfl]
          rw [hwq_eq, hsh, hst]
        have hwq_cl : (wq &&& 0xFFFF#32).toNat = 0 := by
          have hwq_eq : wq = hdr0 &&& 0x7FFF0000#32 := by simp [wq, hhdr]
          rw [hwq_eq, BitVec.and_assoc,
            show (0x7FFF0000#32 &&& 0xFFFF#32 : BitVec 32) = 0#32 from rfl,
            BitVec.and_zero]; rfl
        refine .step hp (List.getElem?_set_self hq_len) hwq_st.symm hwq_cl.symm hbd (Or.inl rfl)
          (xorEqPoolOk_congr hrest fun i hi1 _ => hne i hi1)
      · refine .step hp (by rw [List.getElem?_set_ne (by omega), hhdr]) hst hcl hbd ?_
          (ih hrest_q)
        rcases hbody with rfl | ⟨hpos, hle_c, hss, hlt, hsnd⟩
        · exact Or.inl rfl
        · refine Or.inr ⟨hpos, hle_c, ?_⟩
          have hvs : (List.range cl0).map
              (fun i => ((scr.set q wq)[p0 + 1 + i]?.getD 0#32).toNat) =
              (List.range cl0).map (fun i => (scr[p0 + 1 + i]?.getD 0#32).toNat) := by
            refine List.map_congr_left fun i hi => ?_
            have him : i < cl0 := List.mem_range.mp hi
            rw [List.getElem?_set_ne (by omega)]
          rw [hvs]; exact ⟨hss, hlt, hsnd⟩

theorem xorEqPoolOk_append {F : CNF Nat} {cv : Nat} {scr : List (BitVec 32)}
    {eq_end clen : Nat} {hdr : BitVec 32}
    (hp : XorEqPoolOk F cv scr eq_end 0)
    (_heq_end : eq_end + 1 + clen ≤ scr.length)
    (hhdr : scr[eq_end]? = some hdr)
    (hst : ((hdr >>> 16#32) &&& 0x7FFF#32).toNat = clen)
    (hcl : (hdr &&& 0xFFFF#32).toNat = clen)
    (hpos : 0 < clen)
    (hss : List.Pairwise (· < ·)
      ((List.range clen).map fun i => (scr[eq_end + 1 + i]?.getD 0#32).toNat))
    (hlt : ∀ v ∈ (List.range clen).map (fun i => (scr[eq_end + 1 + i]?.getD 0#32).toNat), v < cv)
    (hsnd : XorVarsSound F
      ((List.range clen).map fun i => (scr[eq_end + 1 + i]?.getD 0#32).toNat)
      ((hdr >>> 31#32) != 0#32)) :
    XorEqPoolOk F cv scr (eq_end + 1 + clen) 0 := by
  have helper : ∀ p, XorEqPoolOk F cv scr eq_end p →
      XorEqPoolOk F cv scr (eq_end + 1 + clen) p := by
    intro p hx
    induction hx with
    | done =>
      exact .step (by omega) hhdr hst.symm hcl.symm (by omega)
        (Or.inr ⟨hpos, Nat.le_refl _, hss, hlt, hsnd⟩) .done
    | step hp0 hhdr0 hst0 hcl0 hbd0 hbody0 hrest0 ih =>
      exact .step (by omega) hhdr0 hst0 hcl0 (by omega) hbody0 ih
  exact helper 0 hp

@[expose] def XorMatOk (F : CNF Nat) (c2v scr : List (BitVec 32))
    (mat nrows ncols : Nat) : Prop :=
  let row_u32s := 2 * ((ncols + 64) / 64)
  ∀ r < nrows, XorPackedRowSound F c2v scr (mat + r * row_u32s) ncols

/-! ## 3. Leaf & Utility `Func.wp` Contracts (`full_xor_sort5` .. `full_xor_set_bit`) -/

@[expose] def fullXorSort5Spec : Spec [i64, i32, i32] [.bool] := fun (tmp_ptr, k, cv, ()) m Q _ =>
  ∃ (tmp : List (BitVec 32)) (R : Mem 64 → Prop),
    k.toNat ≤ tmp.length ∧ tmp.length < 2 ^ 31 ∧ cv.toNat < 2 ^ 31 ∧
    (array (t := i32) tmp_ptr tmp ⋆ R) m ∧
    ∀ (ok : Bool) (tmp' : List (BitVec 32)) (m' : Mem 64),
      tmp'.length = tmp.length →
      (tmp'.take k.toNat).Perm (tmp.take k.toNat) →
      (∀ i, k.toNat ≤ i → tmp'[i]? = tmp[i]?) →
      (ok = true →
        (∀ i < k.toNat, (tmp'[i]?.getD 0#32).toNat / 2 < cv.toNat) ∧
        List.Pairwise (· < ·) ((tmp'.take k.toNat).map fun x => x.toNat / 2)) →
      (array (t := i32) tmp_ptr tmp' ⋆ R) m' → Q (ok, ()) m'

@[expose] def fullXorParityMaskSpec : Spec [i32, .bool] [i32] := fun (k, odd_p, ()) m Q _ =>
  Q (parityMask k.toNat odd_p, ()) m

@[expose] def fullXorHtInsertSpec : Spec [i64, i64, i64, i64, i32] [i64] :=
  fun (scr_ptr, tmp_ptr, ht_cap, _used, k, ()) m Q _ =>
    ∃ (F : CNF Nat) (cv : Nat) (scr tmp : List (BitVec 32)) (R : Mem 64 → Prop),
      7 * ht_cap.toNat ≤ scr.length ∧ scr.length < 2 ^ 32 ∧
      k.toNat ≤ tmp.length ∧ tmp.length < 2 ^ 32 ∧
      (3 ≤ k.toNat ∧ k.toNat ≤ 5) ∧
      (∀ i < k.toNat, (tmp[i]?.getD 0#32).toNat / 2 < cv) ∧
      List.Pairwise (· < ·) ((tmp.take k.toNat).map fun x => x.toNat / 2) ∧
      F.EntailsClause (cnfClause ((tmp.take k.toNat).map BitVec.toNat)) ∧
      XorHtInv F cv ht_cap.toNat scr ∧
      (array (t := i32) scr_ptr scr ⋆ array (t := i32) tmp_ptr tmp ⋆ R) m ∧
      ∀ (used' : BitVec 64) (scr' : List (BitVec 32)) (m' : Mem 64),
        scr'.length = scr.length →
        (∀ i, 7 * ht_cap.toNat ≤ i → scr'[i]? = scr[i]?) →
        XorHtInv F cv ht_cap.toNat scr' →
        (array (t := i32) scr_ptr scr' ⋆ array (t := i32) tmp_ptr tmp ⋆ R) m' →
        Q (used', ()) m'

@[expose] def ufRoot (par : List (BitVec 32)) (x : Nat) : Nat → Nat
  | 0 => x
  | fuel + 1 =>
    let px := (par[x]?.getD 0#32).toNat
    if x ≤ px then x else ufRoot par px fuel

theorem ufRoot_eq_of_self {par : List (BitVec 32)} {x fuel : Nat}
    (hx : x ≤ (par[x]?.getD 0#32).toNat) : ufRoot par x (fuel + 1) = x := by
  simp [ufRoot, hx]

theorem ufRoot_lt {par : List (BitVec 32)} {x cv fuel : Nat} (hx : x < cv)
    (hord : ∀ i < cv, (par[i]?.getD 0#32).toNat ≤ i) : ufRoot par x fuel < cv := by
  induction fuel generalizing x with
  | zero => exact hx
  | succ f ih =>
    dsimp only [ufRoot]
    split
    · exact hx
    · exact ih (by have := hord x hx; omega)

theorem ufRoot_idem_of_ord {par : List (BitVec 32)} {cv : Nat}
    (hord : ∀ i < cv, (par[i]?.getD 0#32).toNat ≤ i) :
    ∀ {x f1 f2 : Nat}, x < f1 → x < f2 → x < cv →
      ufRoot par x f1 = ufRoot par x f2
  | x, 0, _, h1, _, _ => absurd h1 (Nat.not_lt_zero _)
  | x, _, 0, _, h2, _ => absurd h2 (Nat.not_lt_zero _)
  | x, f1 + 1, f2 + 1, h1, h2, hcv => by
    dsimp only [ufRoot]
    split
    · rfl
    · rename_i hlt
      have hpx : (par[x]?.getD 0#32).toNat < x := by
        have := hord x hcv; omega
      exact ufRoot_idem_of_ord hord (by omega) (by omega) (by omega)

theorem ufRoot_set_grandparent {par : List (BitVec 32)} {x cv fuel : Nat}
    (hord : ∀ i < cv, (par[i]?.getD 0#32).toNat ≤ i)
    (hcv_len : cv ≤ par.length)
    (hx : x < cv) (hpx_lt : (par[x]?.getD 0#32).toNat < x) :
    let px := (par[x]?.getD 0#32).toNat
    let ppx := par[px]?.getD 0#32
    let par' := par.set x ppx
    (∀ i < cv, (par'[i]?.getD 0#32).toNat ≤ i) ∧
    ∀ v < cv, v < fuel → ufRoot par' v fuel = ufRoot par v fuel := by
  intro px ppx par'
  have hpx_cv : px < cv := by omega
  have hx_len : x < par.length := by omega
  have hppx_le : ppx.toNat ≤ px := hord px hpx_cv
  have hord' : ∀ i < cv, (par'[i]?.getD 0#32).toNat ≤ i := by
    intro i hi
    by_cases hix : i = x
    · subst hix
      simp only [par', List.getElem?_set_self hx_len, Option.getD_some]; omega
    · rw [show par'[i]? = par[i]? from List.getElem?_set_ne (Ne.symm hix)]; exact hord i hi
  refine ⟨hord', fun v hv hvf => ?_⟩
  induction fuel generalizing v with
  | zero => exact absurd hvf (Nat.not_lt_zero _)
  | succ f ih =>
    dsimp only [ufRoot]
    by_cases hvx : v = x
    · subst hvx
      have hv_not : ¬ (v ≤ ppx.toNat) := by omega
      have hv_not0 : ¬ (v ≤ (par[v]?.getD 0#32).toNat) := by omega
      simp only [par', List.getElem?_set_self hx_len, Option.getD_some, hv_not, ↓reduceIte,
        hv_not0]
      change ufRoot par' ppx.toNat f = ufRoot par px f
      have hppx_eq : ufRoot par' ppx.toNat f = ufRoot par ppx.toNat f :=
        ih ppx.toNat (by omega) (by omega)
      rw [hppx_eq]
      by_cases hself : px ≤ ppx.toNat
      · have heq : ppx.toNat = px := by omega
        rw [heq]
      · cases f with
        | zero => omega
        | succ f' =>
          have hnself : ¬ (px ≤ (par[px]?.getD 0#32).toNat) := by simpa [ppx] using hself
          have hstep : ufRoot par px (f' + 1) = ufRoot par ppx.toNat f' := by
            simp [ufRoot, ppx, hnself]
          rw [hstep]
          exact ufRoot_idem_of_ord hord (by omega) (by omega) (by omega)
    · have heq : par'[v]? = par[v]? := List.getElem?_set_ne (Ne.symm hvx)
      rw [heq]
      split
      · rfl
      · exact ih _ (by have := hord v hv; omega) (by omega)

theorem ufRoot_le {par : List (BitVec 32)} {cv : Nat}
    (hord : ∀ i < cv, (par[i]?.getD 0#32).toNat ≤ i) :
    ∀ {x fuel : Nat}, x < cv → ufRoot par x fuel ≤ x
  | _, 0, _ => Nat.le_refl _
  | x, fuel + 1, hx => by
    dsimp only [ufRoot]
    split
    · exact Nat.le_refl _
    · have hpx : (par[x]?.getD 0#32).toNat < x := by have := hord x hx; omega
      exact Nat.le_trans (ufRoot_le hord (by omega)) (Nat.le_of_lt hpx)

theorem ufRoot_is_root {par : List (BitVec 32)} {cv : Nat}
    (hord : ∀ i < cv, (par[i]?.getD 0#32).toNat ≤ i) :
    ∀ {x fuel : Nat}, x < fuel → x < cv →
      (par[ufRoot par x fuel]?.getD 0#32).toNat = ufRoot par x fuel
  | _, 0, hf, _ => absurd hf (Nat.not_lt_zero _)
  | x, fuel + 1, hf, hx => by
    dsimp only [ufRoot]
    split
    · rename_i hge; have := hord x hx; omega
    · rename_i hlt
      have hpx : (par[x]?.getD 0#32).toNat < x := by have := hord x hx; omega
      exact ufRoot_is_root hord (by omega) (by omega)

@[expose] def fullXorUfFindSpec : Spec [i64, i32, i64] [i32] := fun (par_ptr, x, cv, ()) m Q _ =>
  ∃ (par : List (BitVec 32)) (R : Mem 64 → Prop),
    cv.toNat ≤ par.length ∧ par.length < 2 ^ 31 ∧ x.toNat < cv.toNat ∧
    (∀ i < cv.toNat, (par[i]?.getD 0#32).toNat ≤ i) ∧
    (array (t := i32) par_ptr par ⋆ R) m ∧
    ∀ (r : BitVec 32) (par' : List (BitVec 32)) (m' : Mem 64),
      par'.length = par.length → r.toNat = ufRoot par x.toNat cv.toNat → r.toNat < cv.toNat →
      (∀ i < cv.toNat, (par'[i]?.getD 0#32).toNat ≤ i) →
      (∀ i < cv.toNat, ufRoot par' i cv.toNat = ufRoot par i cv.toNat) →
      (∀ i < cv.toNat, (par[i]?.getD 0#32).toNat = ufRoot par i cv.toNat → par'[i]? = par[i]?) →
      (∀ i, cv.toNat ≤ i → par'[i]? = par[i]?) →
      (array (t := i32) par_ptr par' ⋆ R) m' → Q (r, ()) m'

@[expose] def fullXorReadU64Spec : Spec [i64, i64] [i64] := fun (scr_ptr, idx, ()) m Q _ =>
  ∃ (scr : List (BitVec 32)) (R : Mem 64 → Prop),
    idx.toNat + 1 < scr.length ∧ scr.length < 2 ^ 32 ∧
    (array (t := i32) scr_ptr scr ⋆ R) m ∧
    Q (rowU64 scr idx.toNat 0, ()) m

@[expose] def fullXorWriteU64Spec : Spec [i64, i64, i64] [] := fun (scr_ptr, idx, val, ()) m Q _ =>
  ∃ (scr : List (BitVec 32)) (R : Mem 64 → Prop),
    idx.toNat + 1 < scr.length ∧ scr.length < 2 ^ 32 ∧
    (array (t := i32) scr_ptr scr ⋆ R) m ∧
    ∀ (scr' : List (BitVec 32)) (m' : Mem 64),
      scr'.length = scr.length →
      rowU64 scr' idx.toNat 0 = val →
      (∀ i, i ≠ idx.toNat → i ≠ idx.toNat + 1 → scr'[i]? = scr[i]?) →
      (array (t := i32) scr_ptr scr' ⋆ R) m' → Q () m'

@[expose] def fullXorSwapRowsSpec : Spec [i64, i64, i64, i64, i64] [] :=
  fun (scr_ptr, mat, r1, r2, row_u32s, ()) m Q _ =>
    ∃ (scr : List (BitVec 32)) (nrows : Nat) (R : Mem 64 → Prop),
      mat.toNat + nrows * row_u32s.toNat ≤ scr.length ∧ scr.length < 2 ^ 32 ∧
      r1.toNat < nrows ∧ r2.toNat < nrows ∧
      (array (t := i32) scr_ptr scr ⋆ R) m ∧
      ∀ (scr' : List (BitVec 32)) (m' : Mem 64),
        scr'.length = scr.length →
        (∀ idx, idx < mat.toNat ∨ mat.toNat + nrows * row_u32s.toNat ≤ idx →
          scr'[idx]? = scr[idx]?) →
        (∀ r < nrows, ∀ i < row_u32s.toNat,
          scr'[mat.toNat + r * row_u32s.toNat + i]? =
            scr[mat.toNat +
              (if r = r1.toNat then r2.toNat else if r = r2.toNat then r1.toNat else r) *
                row_u32s.toNat + i]?) →
        (array (t := i32) scr_ptr scr' ⋆ R) m' → Q () m'

@[expose] def fullXorXorRowsSpec : Spec [i64, i64, i64, i64, i64] [] :=
  fun (scr_ptr, mat, dst_r, src_r, words64, ()) m Q _ =>
    ∃ (scr : List (BitVec 32)) (nrows : Nat) (R : Mem 64 → Prop),
      let row_u32s := 2 * words64.toNat
      mat.toNat + nrows * row_u32s ≤ scr.length ∧ scr.length < 2 ^ 32 ∧
      dst_r.toNat < nrows ∧ src_r.toNat < nrows ∧ dst_r ≠ src_r ∧
      (array (t := i32) scr_ptr scr ⋆ R) m ∧
      ∀ (scr' : List (BitVec 32)) (m' : Mem 64),
        scr'.length = scr.length →
        (∀ idx, idx < mat.toNat ∨ mat.toNat + nrows * row_u32s ≤ idx →
          scr'[idx]? = scr[idx]?) →
        (∀ r < nrows, r ≠ dst_r.toNat → ∀ i < row_u32s,
          scr'[mat.toNat + r * row_u32s + i]? = scr[mat.toNat + r * row_u32s + i]?) →
        (∀ w < words64.toNat,
          rowU64 scr' (mat.toNat + dst_r.toNat * row_u32s) w =
            rowU64 scr (mat.toNat + dst_r.toNat * row_u32s) w ^^^
            rowU64 scr (mat.toNat + src_r.toNat * row_u32s) w) →
        (array (t := i32) scr_ptr scr' ⋆ R) m' → Q () m'

@[expose] def fullXorSetBitSpec : Spec [i64, i64, i64] [] := fun (scr_ptr, rbase, c, ()) m Q _ =>
  ∃ (scr : List (BitVec 32)) (ncols : Nat) (R : Mem 64 → Prop),
    c.toNat ≤ ncols ∧
    rbase.toNat + 2 * ((ncols + 64) / 64) ≤ scr.length ∧ scr.length < 2 ^ 32 ∧
    (array (t := i32) scr_ptr scr ⋆ R) m ∧
    ∀ (scr' : List (BitVec 32)) (m' : Mem 64),
      scr'.length = scr.length →
      (∀ idx, idx < rbase.toNat ∨ rbase.toNat + 2 * ((ncols + 64) / 64) ≤ idx →
        scr'[idx]? = scr[idx]?) →
      (∀ c' ≤ ncols, rowBit scr' rbase.toNat c' =
        if c' = c.toNat then true else rowBit scr rbase.toNat c') →
      (array (t := i32) scr_ptr scr' ⋆ R) m' → Q () m'

theorem full_xor_parity_mask_wp (Γ : Env) :
    ∀ a m Q X, fullXorParityMaskSpec a m Q X →
      Func.wp Γ full_xor_parity_mask_body a m Q X := by
  rintro ⟨k, odd_p, ⟨⟩⟩ m Q X hQ
  unfold full_xor_parity_mask_body
  unfold fullXorParityMaskSpec parityMask at hQ
  dsimp only [Func.wp]
  by_cases hk3 : k.toNat = 3
  · have hk3' : k = 3#32 := BitVec.eq_of_toNat_eq hk3
    subst hk3'
    cases odd_p <;> c0_hsteps <;>
      (simp only [Bool.false_eq_true, Bool.true_eq_false] at *; try contradiction) <;>
        simpa using hQ
  · by_cases hk4 : k.toNat = 4
    · have hk4' : k = 4#32 := BitVec.eq_of_toNat_eq hk4
      subst hk4'
      cases odd_p <;> c0_hsteps <;>
        (simp only [Bool.false_eq_true, Bool.true_eq_false] at *; try contradiction) <;>
          simpa using hQ
    · by_cases hk5 : k.toNat = 5
      · have hk5' : k = 5#32 := BitVec.eq_of_toNat_eq hk5
        subst hk5'
        cases odd_p <;> c0_hsteps <;>
          (simp only [Bool.false_eq_true, Bool.true_eq_false] at *; try contradiction) <;>
            simpa using hQ
      · c0_hsplit
        · exfalso; bv_omega
        · c0_hsplit
          · exfalso; bv_omega
          · c0_hsplit
            · exfalso; bv_omega
            · c0_hsteps; simpa [hk3, hk4, hk5] using hQ

theorem full_xor_read_u64_wp (Γ : Env) :
    ∀ a m Q X, fullXorReadU64Spec a m Q X →
      Func.wp Γ full_xor_read_u64_body a m Q X := by
  rintro ⟨scr_ptr, idx, ⟨⟩⟩ m Q X ⟨scr, R, hbd, hscr32, hm, hQ⟩
  unfold full_xor_read_u64_body
  have h1 : idx.toNat < scr.length := by omega
  have hidx1 : (idx + 1#64).toNat = idx.toNat + 1 := by bv_omega
  have h2 : (idx + 1#64).toNat < scr.length := by omega
  dsimp only [Func.wp]
  c0_hsteps
  have hget2 : scr[(idx + 1#64).toNat]'h2 = scr[idx.toNat + 1]'(by omega) := by
    have hs := congrArg (scr[·]?) hidx1
    rw [List.getElem?_eq_getElem h2, List.getElem?_eq_getElem (by omega)] at hs
    exact Option.some.inj hs
  have heq : (scr[idx.toNat]'h1).setWidth 64 |||
      (scr[(idx + 1#64).toNat]'h2).setWidth 64 <<< 32 = rowU64 scr idx.toNat 0 := by
    unfold rowU64
    rw [Nat.mul_zero, Nat.add_zero, List.getElem?_eq_getElem h1, hget2,
      List.getElem?_eq_getElem (by omega), Option.getD_some, Option.getD_some]
  change Q ((scr[idx.toNat]'h1).setWidth 64 |||
      (scr[(idx + 1#64).toNat]'h2).setWidth 64 <<< 32, ()) m
  rw [heq]
  exact hQ

theorem full_xor_write_u64_wp (Γ : Env) :
    ∀ a m Q X, fullXorWriteU64Spec a m Q X →
      Func.wp Γ full_xor_write_u64_body a m Q X := by
  rintro ⟨scr_ptr, idx, val, ⟨⟩⟩ m Q X ⟨scr, R, hbd, hscr32, hm, hQ⟩
  unfold full_xor_write_u64_body
  have h1 : idx.toNat < scr.length := by omega
  have h2 : (idx + 1#64).toNat < scr.length := by bv_omega
  have hidx1 : (idx + 1#64).toNat = idx.toNat + 1 := by bv_omega
  dsimp only [Func.wp]
  c0_hsteps
  refine hQ
    ((scr.set idx.toNat ((val &&& 0xFFFFFFFF#64).setWidth 32)).set (idx.toNat + 1)
      ((val >>> 32#64).setWidth 32))
    m (by simp) ?_ (fun i hi1 hi2 => ?_) ?_
  · unfold rowU64
    simp only [Nat.mul_zero, Nat.add_zero]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_self h1,
      List.getElem?_set_self (by simp; omega)]
    dsimp only [Option.getD]
    apply BitVec.eq_of_getLsbD_eq
    intro b hb
    rw [rowU64_lo_hi]
    split
    · rename_i hlt32
      have hmask : (0xFFFFFFFF#64 : BitVec 64).getLsbD b = true := by
        revert b hlt32; decide
      simp only [BitVec.getLsbD_setWidth, decide_eq_true hlt32, Bool.true_and, BitVec.getLsbD_and,
        hmask, Bool.and_true]
    · rename_i hge32
      have hsub : b - 32 < 32 := by omega
      simp only [BitVec.getLsbD_setWidth, decide_eq_true hsub, Bool.true_and]
      change (val >>> 32).getLsbD (b - 32) = val.getLsbD b
      rw [BitVec.getLsbD_ushiftRight, show 32 + (b - 32) = b by omega]
  · rw [List.getElem?_set_ne (Ne.symm hi2), List.getElem?_set_ne (Ne.symm hi1)]
  · simpa [hidx1] using hm

theorem full_xor_swap_rows_wp (Γ : Env) :
    ∀ a m Q X, fullXorSwapRowsSpec a m Q X →
      Func.wp Γ full_xor_swap_rows_body a m Q X := by
  rintro ⟨scr_ptr, mat, r1, r2, row_u32s, ⟨⟩⟩ m0 Q X
    ⟨scr, nrows, R, hbd, hscr32, hr1, hr2, hm0, hQ⟩
  unfold full_xor_swap_rows_body
  let b1 := mat.toNat + r1.toNat * row_u32s.toNat
  let b2 := mat.toNat + r2.toNat * row_u32s.toNat
  have hnr1 : r1.toNat * row_u32s.toNat + row_u32s.toNat ≤ nrows * row_u32s.toNat := by
    have := Nat.mul_le_mul_right row_u32s.toNat (Nat.succ_le_of_lt hr1)
    simpa [Nat.succ_mul] using this
  have hnr2 : r2.toNat * row_u32s.toNat + row_u32s.toNat ≤ nrows * row_u32s.toNat := by
    have := Nat.mul_le_mul_right row_u32s.toNat (Nat.succ_le_of_lt hr2)
    simpa [Nat.succ_mul] using this
  have hb1_bv : (mat + r1 * row_u32s).toNat = b1 := by
    have hmul : r1.toNat * row_u32s.toNat < 2 ^ 32 := by omega
    bv_omega
  have hb2_bv : (mat + r2 * row_u32s).toNat = b2 := by
    have hmul : r2.toNat * row_u32s.toNat < 2 ^ 32 := by omega
    bv_omega
  c0_to_group
  refine wp_loop_inv
    (fun (i, ()) mi => ∃ scri : List (BitVec 32),
      scri.length = scr.length ∧ i.toNat ≤ row_u32s.toNat ∧
      (∀ k < i.toNat, scri[b1 + k]? = scr[b2 + k]? ∧ scri[b2 + k]? = scr[b1 + k]?) ∧
      (∀ k, i.toNat ≤ k → k < row_u32s.toNat →
        scri[b1 + k]? = scr[b1 + k]? ∧ scri[b2 + k]? = scr[b2 + k]?) ∧
      (∀ idx, idx < mat.toNat ∨ mat.toNat + nrows * row_u32s.toNat ≤ idx →
        scri[idx]? = scr[idx]?) ∧
      (∀ r < nrows, r ≠ r1.toNat → r ≠ r2.toNat → ∀ k < row_u32s.toNat,
        scri[mat.toNat + r * row_u32s.toNat + k]? = scr[mat.toNat + r * row_u32s.toNat + k]?) ∧
      (array (t := i32) scr_ptr scri ⋆ R) mi)
    (fun (i, ()) _ => row_u32s.toNat - i.toNat)
    (fun J hJ => by
      c0_to_group
      exact hJ (0#64, ()) m0 ⟨scr, rfl, Nat.zero_le _, fun _ hk => absurd hk (Nat.not_lt_zero _),
        fun _ _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl, fun _ _ _ _ _ _ => rfl, hm0⟩)
    (fun J (i, ()) mi ⟨scri, hlen_i, hi_le, hsw_i, hrem_i, hout_i, hoth_i, hmi⟩ ih => ?_)
  c0_split
  · have hi_lt : i.toNat < row_u32s.toNat := by bv_omega
    have hidx1 : (mat + r1 * row_u32s + i).toNat = b1 + i.toNat := by
      have hmul : r1.toNat * row_u32s.toNat < 2 ^ 32 := by omega
      bv_omega
    have hidx2 : (mat + r2 * row_u32s + i).toNat = b2 + i.toNat := by
      have hmul : r2.toNat * row_u32s.toNat < 2 ^ 32 := by omega
      bv_omega
    have hi1_len : (mat + r1 * row_u32s + i).toNat < scri.length := by omega
    have hi2_len : (mat + r2 * row_u32s + i).toNat < scri.length := by omega
    c0_to_group
    have hi1_succ : (i + 1#64).toNat = i.toNat + 1 := by bv_omega
    let v1 := scri[(mat + r1 * row_u32s + i).toNat]'hi1_len
    let v2 := scri[(mat + r2 * row_u32s + i).toNat]'hi2_len
    let scri' := (scri.set (b1 + i.toNat) v2).set (b2 + i.toNat) v1
    have hv1_eq : v1 = scr[b1 + i.toNat]'(by omega) := by
      have hg := (hrem_i i.toNat (Nat.le_refl _) hi_lt).1
      have hs := congrArg (scri[·]?) hidx1
      rw [List.getElem?_eq_getElem hi1_len] at hs
      rw [← hs, List.getElem?_eq_getElem (by omega)] at hg
      exact Option.some.inj hg
    have hv2_eq : v2 = scr[b2 + i.toNat]'(by omega) := by
      have hg := (hrem_i i.toNat (Nat.le_refl _) hi_lt).2
      have hs := congrArg (scri[·]?) hidx2
      rw [List.getElem?_eq_getElem hi2_len] at hs
      rw [← hs, List.getElem?_eq_getElem (by omega)] at hg
      exact Option.some.inj hg
    have hmi' : (array (t := i32) scr_ptr scri' ⋆ R) m := by
      simpa [scri', v1, v2, hidx1, hidx2] using hm
    refine ih (i + 1#64, ()) m (by dsimp only; omega)
      ⟨scri', by simp [scri', hlen_i], by omega, ?_, ?_, ?_, ?_, hmi'⟩
    · intro k hk
      rw [hi1_succ] at hk
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with hkl | rfl
      · have hk_ne : k ≠ i.toNat := by omega
        by_cases h12 : r1.toNat = r2.toNat
        · have hb12 : b1 = b2 := by simp [b1, b2, h12]
          simp only [scri', hb12]
          rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
          simpa [hb12] using hsw_i k hkl
        · have hdisj : b1 + row_u32s.toNat ≤ b2 ∨ b2 + row_u32s.toNat ≤ b1 := by
            rcases Nat.lt_or_gt_of_ne h12 with hlt | hgt
            · left; have := Nat.mul_le_mul_right row_u32s.toNat (Nat.succ_le_of_lt hlt)
              simp only [Nat.succ_mul] at this; dsimp [b1, b2]; omega
            · right; have := Nat.mul_le_mul_right row_u32s.toNat (Nat.succ_le_of_lt hgt)
              simp only [Nat.succ_mul] at this; dsimp [b1, b2]; omega
          refine ⟨?_, ?_⟩
          · simp only [scri']
            rw [List.getElem?_set_ne (by rcases hdisj with d | d <;> omega),
              List.getElem?_set_ne (by omega)]
            exact (hsw_i k hkl).1
          · simp only [scri']
            rw [List.getElem?_set_ne (by omega),
              List.getElem?_set_ne (by rcases hdisj with d | d <;> omega)]
            exact (hsw_i k hkl).2
      · by_cases h12 : r1.toNat = r2.toNat
        · have hb12 : b1 = b2 := by simp [b1, b2, h12]
          simp only [scri', hb12, v1, hv1_eq]
          rw [List.getElem?_set_self (by simp; omega)]
          exact ⟨by rw [List.getElem?_eq_getElem (by omega)],
            by rw [List.getElem?_eq_getElem (by omega)]⟩
        · have hne_bi : b2 + i.toNat ≠ b1 + i.toNat := by
            rcases Nat.lt_or_gt_of_ne h12 with hlt | hgt
            · have := Nat.mul_le_mul_right row_u32s.toNat (Nat.succ_le_of_lt hlt)
              simp only [Nat.succ_mul] at this; dsimp [b1, b2]; omega
            · have := Nat.mul_le_mul_right row_u32s.toNat (Nat.succ_le_of_lt hgt)
              simp only [Nat.succ_mul] at this; dsimp [b1, b2]; omega
          refine ⟨?_, ?_⟩
          · simp only [scri', v2, hv2_eq]
            rw [List.getElem?_set_ne hne_bi, List.getElem?_set_self (by simp [hlen_i]; omega),
              List.getElem?_eq_getElem (by omega)]
          · simp only [scri', v1, hv1_eq]
            rw [List.getElem?_set_self (by simp [hlen_i]; omega),
              List.getElem?_eq_getElem (by omega)]
    · intro k hk1 hk2
      rw [hi1_succ] at hk1
      have hne1 : b1 + k ≠ b1 + i.toNat := by omega
      have hne2 : b2 + k ≠ b2 + i.toNat := by omega
      by_cases h12 : r1.toNat = r2.toNat
      · have hb12 : b1 = b2 := by simp [b1, b2, h12]
        simp only [scri', hb12]
        rw [List.getElem?_set_ne hne2.symm, List.getElem?_set_ne hne2.symm]
        simpa [hb12] using hrem_i k (by omega) hk2
      · have hdisj : b1 + row_u32s.toNat ≤ b2 ∨ b2 + row_u32s.toNat ≤ b1 := by
          rcases Nat.lt_or_gt_of_ne h12 with hlt | hgt
          · left; have := Nat.mul_le_mul_right row_u32s.toNat (Nat.succ_le_of_lt hlt)
            simp only [Nat.succ_mul] at this; dsimp [b1, b2]; omega
          · right; have := Nat.mul_le_mul_right row_u32s.toNat (Nat.succ_le_of_lt hgt)
            simp only [Nat.succ_mul] at this; dsimp [b1, b2]; omega
        refine ⟨?_, ?_⟩
        · simp only [scri']
          rw [List.getElem?_set_ne (by rcases hdisj with d | d <;> omega),
            List.getElem?_set_ne hne1.symm]
          exact (hrem_i k (by omega) hk2).1
        · simp only [scri']
          rw [List.getElem?_set_ne hne2.symm,
            List.getElem?_set_ne (by rcases hdisj with d | d <;> omega)]
          exact (hrem_i k (by omega) hk2).2
    · intro idx hidx
      simp only [scri']
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      exact hout_i idx hidx
    · intro r hr hne1 hne2 k hk
      have hdisj1 : mat.toNat + r * row_u32s.toNat + k ≠ b1 + i.toNat := by
        rcases Nat.lt_or_gt_of_ne hne1 with hlt | hgt
        · have := Nat.mul_le_mul_right row_u32s.toNat (Nat.succ_le_of_lt hlt)
          simp only [Nat.succ_mul] at this; dsimp [b1]; omega
        · have := Nat.mul_le_mul_right row_u32s.toNat (Nat.succ_le_of_lt hgt)
          simp only [Nat.succ_mul] at this; dsimp [b1]; omega
      have hdisj2 : mat.toNat + r * row_u32s.toNat + k ≠ b2 + i.toNat := by
        rcases Nat.lt_or_gt_of_ne hne2 with hlt | hgt
        · have := Nat.mul_le_mul_right row_u32s.toNat (Nat.succ_le_of_lt hlt)
          simp only [Nat.succ_mul] at this; dsimp [b2]; omega
        · have := Nat.mul_le_mul_right row_u32s.toNat (Nat.succ_le_of_lt hgt)
          simp only [Nat.succ_mul] at this; dsimp [b2]; omega
      simp only [scri']
      rw [List.getElem?_set_ne hdisj2.symm, List.getElem?_set_ne hdisj1.symm]
      exact hoth_i r hr hne1 hne2 k hk
  · have hi_eq : i.toNat = row_u32s.toNat := by bv_omega
    c0_to_group
    refine hQ scri mi hlen_i hout_i (fun r hr k hk => ?_) hmi
    by_cases h1 : r = r1.toNat
    · subst h1; simp only [↓reduceIte]; exact (hsw_i k (by omega)).1
    · by_cases h2 : r = r2.toNat
      · subst h2; simp only [h1, ↓reduceIte]; exact (hsw_i k (by omega)).2
      · simp only [h1, h2, ↓reduceIte]; exact hoth_i r hr h1 h2 k hk

theorem full_xor_xor_rows_wp (Γ : Env)
    (hRead : ∀ a m Q X, fullXorReadU64Spec a m Q X → Γ "full_xor_read_u64" [i64, i64] [i64] a m Q X)
    (hWrite : ∀ a m Q X, fullXorWriteU64Spec a m Q X →
      Γ "full_xor_write_u64" [i64, i64, i64] [] a m Q X) :
    ∀ a m Q X, fullXorXorRowsSpec a m Q X →
      Func.wp Γ full_xor_xor_rows_body a m Q X := by
  rintro ⟨scr_ptr, mat, dst_r, src_r, words64, ⟨⟩⟩ m0 Q X
    ⟨scr, nrows, R, hbd, hscr32, hdst, hsrc, hne, hm0, hQ⟩
  unfold full_xor_xor_rows_body
  let row_u32s := 2 * words64.toNat
  let bd := mat.toNat + dst_r.toNat * row_u32s
  let bs := mat.toNat + src_r.toNat * row_u32s
  have hru_le : row_u32s ≤ nrows * row_u32s := Nat.le_mul_of_pos_left _ (by omega)
  have hmat_end : mat.toNat + nrows * row_u32s ≤ scr.length := by
    dsimp [row_u32s]; exact hbd
  have hru_lt32 : row_u32s < 2 ^ 32 := by omega
  have hw64_lt32 : words64.toNat < 2 ^ 31 := by dsimp [row_u32s] at hru_lt32; omega
  have hru_bv : (words64 <<< (1 : Nat)).toNat = row_u32s := by
    dsimp [row_u32s]; rw [BitVec.toNat_shiftLeft]
    simp only [Nat.shiftLeft_eq, Nat.pow_one,
      Nat.mod_eq_of_lt (by omega : words64.toNat * 2 < 2 ^ 64)]
    exact Nat.mul_comm _ _
  have hbd_end : bd + row_u32s ≤ mat.toNat + nrows * row_u32s := by
    have := Nat.mul_le_mul_right row_u32s (Nat.succ_le_of_lt hdst)
    simp only [Nat.succ_mul] at this; dsimp [bd]; omega
  have hbs_end : bs + row_u32s ≤ mat.toNat + nrows * row_u32s := by
    have := Nat.mul_le_mul_right row_u32s (Nat.succ_le_of_lt hsrc)
    simp only [Nat.succ_mul] at this; dsimp [bs]; omega
  have hdisj : bd + row_u32s ≤ bs ∨ bs + row_u32s ≤ bd := by
    have hne_n : dst_r.toNat ≠ src_r.toNat := fun h => hne (BitVec.eq_of_toNat_eq h)
    rcases Nat.lt_or_gt_of_ne hne_n with hlt | hgt
    · left; have := Nat.mul_le_mul_right row_u32s (Nat.succ_le_of_lt hlt)
      simp only [Nat.succ_mul] at this; dsimp [bd, bs]; omega
    · right; have := Nat.mul_le_mul_right row_u32s (Nat.succ_le_of_lt hgt)
      simp only [Nat.succ_mul] at this; dsimp [bd, bs]; omega
  c0_to_group
  refine wp_loop_inv
    (fun (w, ()) mw => ∃ scrw : List (BitVec 32),
      scrw.length = scr.length ∧ w.toNat ≤ words64.toNat ∧
      (∀ idx, idx < bd ∨ bd + 2 * w.toNat ≤ idx → scrw[idx]? = scr[idx]?) ∧
      (∀ w' < w.toNat, rowU64 scrw bd w' = rowU64 scr bd w' ^^^ rowU64 scr bs w') ∧
      (array (t := i32) scr_ptr scrw ⋆ R) mw)
    (fun (w, ()) _ => words64.toNat - w.toNat)
    (fun J hJ => by
      c0_to_group
      exact hJ (0#64, ()) m0 ⟨scr, rfl, Nat.zero_le _, fun _ _ => rfl,
        fun _ hw => absurd hw (Nat.not_lt_zero _), hm0⟩)
    (fun J (w, ()) mw ⟨scrw, hlen_w, hw_le, hframe_w, hxor_w, hmw⟩ ih => ?_)
  c0_split
  · have hw_lt : w.toNat < words64.toNat := by bv_omega
    have hbd_mul : dst_r.toNat * row_u32s < 2 ^ 32 := by omega
    have hbs_mul : src_r.toNat * row_u32s < 2 ^ 32 := by omega
    have hwsh : (w <<< (1 : Nat)).toNat = 2 * w.toNat := by
      rw [BitVec.toNat_shiftLeft]
      simp only [Nat.shiftLeft_eq, Nat.pow_one,
        Nat.mod_eq_of_lt (by omega : w.toNat * 2 < 2 ^ 64)]
      exact Nat.mul_comm _ _
    have hidx_d : (mat + dst_r * (words64 <<< (1 : Nat)) + (w <<< (1 : Nat))).toNat =
        bd + 2 * w.toNat := by
      have hbd_eq : mat.toNat + dst_r.toNat * row_u32s = bd := rfl
      rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_mul, hru_bv, hwsh,
        Nat.mod_eq_of_lt (by omega : dst_r.toNat * row_u32s < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega), hbd_eq, Nat.mod_eq_of_lt (by omega)]
    have hidx_s : (mat + src_r * (words64 <<< (1 : Nat)) + (w <<< (1 : Nat))).toNat =
        bs + 2 * w.toNat := by
      have hbs_eq : mat.toNat + src_r.toNat * row_u32s = bs := rfl
      rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_mul, hru_bv, hwsh,
        Nat.mod_eq_of_lt (by omega : src_r.toNat * row_u32s < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega), hbs_eq, Nat.mod_eq_of_lt (by omega)]
    c0_hstraight
    c0_call hRead
    refine ⟨scrw, R, by rw [hidx_d]; omega, by omega, hmw, ?_⟩
    c0_call hRead
    refine ⟨scrw, R, by rw [hidx_s]; omega, by omega, hmw, ?_⟩
    c0_call hWrite
    refine ⟨scrw, R, by rw [hidx_d]; omega, by omega, hmw,
      fun scrw' mw' hlen' hrow' hoth' hmw' => ?_⟩
    c0_hstraight
    have hw_succ : (w + 1#64).toNat = w.toNat + 1 := by bv_omega
    have hvd_eq : rowU64 scrw (mat + dst_r * (words64 <<< (1 : Nat)) + (w <<< (1 : Nat))).toNat 0 =
        rowU64 scr bd w.toNat := by
      rw [hidx_d]; unfold rowU64
      rw [Nat.mul_zero, Nat.add_zero, hframe_w (bd + 2 * w.toNat) (Or.inr (by omega)),
        hframe_w (bd + 2 * w.toNat + 1) (Or.inr (by omega))]
    have hvs_eq : rowU64 scrw (mat + src_r * (words64 <<< (1 : Nat)) + (w <<< (1 : Nat))).toNat 0 =
        rowU64 scr bs w.toNat := by
      rw [hidx_s]; unfold rowU64
      rw [Nat.mul_zero, Nat.add_zero,
        hframe_w (bs + 2 * w.toNat) (by rcases hdisj with d | d <;> omega),
        hframe_w (bs + 2 * w.toNat + 1) (by rcases hdisj with d | d <;> omega)]
    refine ih (w + 1#64, ()) mw' (by dsimp only; rw [hw_succ]; omega)
      ⟨scrw', hlen'.trans hlen_w, by rw [hw_succ]; omega, ?_, ?_, hmw'⟩
    · intro idx hidx
      rw [hoth' idx (by rw [hidx_d]; omega) (by rw [hidx_d]; omega)]
      exact hframe_w idx (hidx.elim Or.inl (fun h => Or.inr (by omega)))
    · intro w' hw'
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp (hw_succ ▸ hw')) with hwl | rfl
      · unfold rowU64
        rw [hoth' (bd + 2 * w') (by rw [hidx_d]; omega) (by rw [hidx_d]; omega),
          hoth' (bd + 2 * w' + 1) (by rw [hidx_d]; omega) (by rw [hidx_d]; omega)]
        exact hxor_w w' hwl
      · unfold rowU64 at hrow' hvd_eq hvs_eq ⊢
        rw [Nat.mul_zero, Nat.add_zero, hidx_d, hidx_s] at hrow'
        simp only [Nat.add_zero] at hrow'
        rw [Nat.mul_zero, Nat.add_zero, hidx_d] at hvd_eq
        rw [Nat.mul_zero, Nat.add_zero, hidx_s] at hvs_eq
        rw [hrow', hvd_eq, hvs_eq]
  · have hw_eq : w.toNat = words64.toNat := by bv_omega
    have h2w : 2 * w.toNat = row_u32s := by rw [hw_eq]
    have hbd2 : bd + 2 * w.toNat = bd + row_u32s := by rw [h2w]
    c0_hstraight
    refine hQ scrw mw hlen_w (fun idx hidx => hframe_w idx ?_)
      (fun r hr hnr i hi => hframe_w (mat.toNat + r * row_u32s + i) ?_)
      (fun w' hw' => hxor_w w' (by omega)) hmw
    · rw [hbd2]
      rcases hidx with h | h
      · exact Or.inl (Nat.lt_of_lt_of_le h (Nat.le_add_right _ _))
      · exact Or.inr (Nat.le_trans hbd_end h)
    · rw [hbd2]
      rcases Nat.lt_or_gt_of_ne hnr with hlt | hgt
      · left; have := Nat.mul_le_mul_right row_u32s (Nat.succ_le_of_lt hlt)
        simp only [Nat.succ_mul] at this; dsimp [bd]; omega
      · right; have := Nat.mul_le_mul_right row_u32s (Nat.succ_le_of_lt hgt)
        simp only [Nat.succ_mul] at this; dsimp [bd]; omega

theorem full_xor_set_bit_wp (Γ : Env)
    (hRead : ∀ a m Q X, fullXorReadU64Spec a m Q X → Γ "full_xor_read_u64" [i64, i64] [i64] a m Q X)
    (hWrite : ∀ a m Q X, fullXorWriteU64Spec a m Q X →
      Γ "full_xor_write_u64" [i64, i64, i64] [] a m Q X) :
    ∀ a m Q X, fullXorSetBitSpec a m Q X →
      Func.wp Γ full_xor_set_bit_body a m Q X := by
  rintro ⟨scr_ptr, rbase, c, ⟨⟩⟩ m0 Q X ⟨scr, ncols, R, hc, hbd, hscr32, hm0, hQ⟩
  unfold full_xor_set_bit_body
  have hw_lt : c.toNat / 64 < (ncols + 64) / 64 := by omega
  have hsh_lt : (c >>> (6 : Nat)).toNat = c.toNat / 64 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hsh2_lt : ((c >>> (6 : Nat)) <<< (1 : Nat)).toNat = 2 * (c.toNat / 64) := by
    rw [BitVec.toNat_shiftLeft, hsh_lt]
    simp only [Nat.shiftLeft_eq, Nat.pow_one,
      Nat.mod_eq_of_lt (by omega : c.toNat / 64 * 2 < 2 ^ 64)]
    exact Nat.mul_comm _ _
  have hidx_nat : (rbase + ((c >>> (6 : Nat)) <<< (1 : Nat))).toNat =
      rbase.toNat + 2 * (c.toNat / 64) := by
    rw [BitVec.toNat_add, hsh2_lt, Nat.mod_eq_of_lt (by omega)]
  c0_hstraight
  c0_call hRead
  refine ⟨scr, R, by rw [hidx_nat]; omega, hscr32, hm0, ?_⟩
  c0_call hWrite
  refine ⟨scr, R, by rw [hidx_nat]; omega, hscr32, hm0, fun scr' m' hlen' hrow' hoth' hm' => ?_⟩
  c0_hstraight
  refine hQ scr' m' hlen'
    (fun idx hidx => hoth' idx (by rw [hidx_nat]; omega) (by rw [hidx_nat]; omega))
    (fun c' hc' => ?_) hm'
  unfold rowBit
  by_cases hw_eq : c' / 64 = c.toNat / 64
  · rw [hw_eq]
    have hcb : (c &&& BitVec.ofNat 64 63).toNat = c.toNat % 64 := by
      rw [BitVec.toNat_and]
      apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.testBit_and, show (BitVec.ofNat 64 63).toNat = 63 from rfl]
      have h64 : (c.toNat % 64).testBit i = (c.toNat % 2 ^ 6).testBit i := rfl
      rw [h64, Nat.testBit_mod_two_pow]
      by_cases hi : i < 6
      · have h63 : (63 : Nat).testBit i = true := by
          rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with
            rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        simp [hi, h63]
      · have hpow : 64 ≤ 2 ^ i := by
          simpa using Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 6 ≤ i)
        have h63f : (63 : Nat).testBit i = false := by
          simp [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (by omega : 63 < 2 ^ i)]
        simp [hi, h63f]
    have hmod_mod : (c.toNat % 64) % 64 = c.toNat % 64 :=
      Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))
    have heq_w : rowU64 scr' rbase.toNat (c.toNat / 64) =
        rowU64 scr rbase.toNat (c.toNat / 64) ||| (1#64 <<< (c.toNat % 64)) := by
      unfold rowU64 at hrow' ⊢
      rw [Nat.mul_zero, Nat.add_zero, hidx_nat] at hrow'
      change BitVec.setWidth 64 (scr'[rbase.toNat + 2 * (c.toNat / 64)]?.getD 0#32) |||
          BitVec.setWidth 64 (scr'[rbase.toNat + 2 * (c.toNat / 64) + 1]?.getD 0#32)
            <<< (32 : Nat) =
        BitVec.setWidth 64 (scr[rbase.toNat + 2 * (c.toNat / 64)]?.getD 0#32) |||
            BitVec.setWidth 64 (scr[rbase.toNat + 2 * (c.toNat / 64) + 1]?.getD 0#32)
              <<< (32 : Nat) |||
          1#64 <<< ((c &&& BitVec.ofNat 64 63).toNat % 64) at hrow'
      rw [hcb, hmod_mod] at hrow'
      exact hrow'
    rw [heq_w, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
    have hb_lt : c' % 64 < 64 := Nat.mod_lt _ (by decide)
    by_cases hcc : c' = c.toNat
    · subst hcc
      simp [hb_lt, Nat.lt_irrefl, Nat.sub_self]
    · by_cases hlt : c' % 64 < c.toNat % 64
      · simp [hlt, hcc]
      · have hpos : c' % 64 - c.toNat % 64 ≠ 0 := by omega
        simp [hlt, hb_lt, BitVec.getLsbD_one, hpos, hcc]
  · have hcc : c' ≠ c.toNat := by intro h; subst h; exact hw_eq rfl
    have heq_w : rowU64 scr' rbase.toNat (c' / 64) = rowU64 scr rbase.toNat (c' / 64) := by
      unfold rowU64
      rw [hoth' (rbase.toNat + 2 * (c' / 64)) (by rw [hidx_nat]; omega) (by rw [hidx_nat]; omega),
        hoth' (rbase.toNat + 2 * (c' / 64) + 1) (by rw [hidx_nat]; omega) (by rw [hidx_nat]; omega)]
    simp [hcc, heq_w]

theorem full_xor_uf_find_wp (Γ : Env) :
    ∀ a m Q X, fullXorUfFindSpec a m Q X →
      Func.wp Γ full_xor_uf_find_body a m Q X := by
  rintro ⟨par_ptr, x0, cv, ⟨⟩⟩ m0 Q X ⟨par, R, hpar_len, hpar31, hx0, hord0, hm0, hQ⟩
  unfold full_xor_uf_find_body
  c0_hstraight
  refine wp_loop_inv
    (fun (x, step, ()) ms => ∃ pars : List (BitVec 32),
      pars.length = par.length ∧ x.toNat < cv.toNat ∧ x.toNat + step.toNat < cv.toNat ∧
      (∀ i < cv.toNat, (pars[i]?.getD 0#32).toNat ≤ i) ∧
      ufRoot pars x.toNat cv.toNat = ufRoot par x0.toNat cv.toNat ∧
      (∀ i < cv.toNat, ufRoot pars i cv.toNat = ufRoot par i cv.toNat) ∧
      (∀ i < cv.toNat, (par[i]?.getD 0#32).toNat = ufRoot par i cv.toNat → pars[i]? = par[i]?) ∧
      (∀ i, cv.toNat ≤ i → pars[i]? = par[i]?) ∧
      (array (t := i32) par_ptr pars ⋆ R) ms)
    (fun (_, step, ()) _ => cv.toNat - step.toNat)
    (fun J hJ => by
      c0_hstraight
      exact hJ (x0, 0#64, ()) m0 ⟨par, rfl, hx0, by simpa using hx0, hord0, rfl,
        fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl, hm0⟩)
    (fun J (x, step, ()) ms
        ⟨pars, hlen_s, hx_lt, hxstep, hord_s, hrt_x, hrt_all, hflat_s, hsuf_s, hms⟩ ih => ?_)
  c0_hsplit
  · c0_hstraight
    c0_hsplit
    · have hlt : step.toNat < cv.toNat ∧ x.toNat < cv.toNat := by bv_omega
      have hx_len : x.toNat < pars.length := by omega
      have hxz : (x.setWidth 64).toNat = x.toNat := bv_zext32_toNat x
      c0_hstraight!
      let px := pars[x.toNat]'hx_len
      have hpx_ord : px.toNat ≤ x.toNat := by
        have h := hord_s x.toNat hlt.2
        rwa [List.getElem?_eq_getElem hx_len, Option.getD_some] at h
      c0_hsplit
      · have hpx_eq : px.toNat = x.toNat := by bv_omega
        have hx_rt : ufRoot pars x.toNat cv.toNat = x.toNat := by
          cases hcv : cv.toNat with
          | zero => omega
          | succ f =>
            apply ufRoot_eq_of_self
            rw [List.getElem?_eq_getElem hx_len, Option.getD_some]; exact Nat.le_of_eq hpx_eq.symm
        c0_hstraight
        exact hQ x pars ms hlen_s (by rw [← hrt_x, hx_rt]) hlt.2 hord_s hrt_all hflat_s hsuf_s
          (by simpa [hxz] using hms)
      · c0_hsplit
        · exfalso; dsimp [px] at hpx_ord
          have hc_ge : cv.toNat ≤ (pars[x.toNat]'hx_len).toNat := by assumption
          exact absurd (Nat.le_trans hc_ge hpx_ord) (Nat.not_le_of_lt hx_lt)
        · -- px < x
          have hne_self : ¬ (pars[x.toNat]'hx_len) = x := by assumption
          have hpx_lt : px.toNat < x.toNat :=
            Classical.byContradiction fun hle =>
              hne_self (BitVec.eq_of_toNat_eq (Nat.le_antisymm hpx_ord (Nat.not_lt.mp hle)))
          have hpx_len : px.toNat < pars.length := by omega
          have hpxz : (px.setWidth 64).toNat = px.toNat := bv_zext32_toNat px
          have hpxz_len : (px.setWidth 64).toNat < pars.length := by rw [hpxz]; exact hpx_len
          c0_hstraight
          let ppx := pars[px.toNat]'hpx_len
          have hppx_ord : ppx.toNat ≤ px.toNat := by
            have h := hord_s px.toNat (by omega)
            rwa [List.getElem?_eq_getElem hpx_len, Option.getD_some] at h
          have hstep_sg := ufRoot_set_grandparent (par := pars) (x := x.toNat) (cv := cv.toNat)
            (fuel := cv.toNat) hord_s (by omega) hlt.2
            (by rw [List.getElem?_eq_getElem hx_len, Option.getD_some]; exact hpx_lt)
          have hpx_eq_g : (pars[x.toNat]?.getD 0#32).toNat = px.toNat := by
            rw [List.getElem?_eq_getElem hx_len, Option.getD_some]
          dsimp only at hstep_sg
          rw [hpx_eq_g] at hstep_sg
          have hpx_get : pars[px.toNat]?.getD 0#32 = ppx := by
            rw [List.getElem?_eq_getElem hpx_len, Option.getD_some]
          have hpars_eq : pars.set x.toNat ppx = pars.set x.toNat (pars[px.toNat]?.getD 0#32) := by
            rw [hpx_get]
          have hrt_px : ufRoot (pars.set x.toNat ppx) px.toNat cv.toNat =
              ufRoot par x0.toNat cv.toNat := by
            rw [hpars_eq, hstep_sg.2 px.toNat (by omega) (by omega), ← hrt_x]
            cases hcv : cv.toNat with
            | zero => omega
            | succ f =>
              have hx_f : x.toNat ≤ f := by rw [hcv] at hx_lt; omega
              have hpx_f : px.toNat < f := Nat.lt_of_lt_of_le hpx_lt hx_f
              have hstep_r : ufRoot pars x.toNat (f + 1) = ufRoot pars px.toNat f := by
                conv => lhs; unfold ufRoot; dsimp only
                rw [hpx_eq_g]
                split
                · omega
                · rfl
              rw [hstep_r]
              exact ufRoot_idem_of_ord hord_s (Nat.lt_succ_of_lt hpx_f) hpx_f
                (Nat.lt_trans hpx_lt hx_lt)
          refine wp_join0
            (fun mk => (array (t := i32) par_ptr (pars.set x.toNat ppx) ⋆ R) mk)
            ?_ ?_
          · rintro K mk hmk
            c0_hstraight
            exact ih (px, step + 1#64, ()) mk (by dsimp only; bv_omega)
              ⟨pars.set x.toNat ppx, by simp [hlen_s], Nat.lt_trans hpx_lt hx_lt, by bv_omega,
               by rw [hpars_eq]; exact hstep_sg.1, hrt_px,
               fun i hi => by
                 rw [hpars_eq, hstep_sg.2 i hi (by omega)]
                 exact hrt_all i hi,
               fun i hi hfl => by
                 by_cases hix : i = x.toNat
                 · subst hix
                   have hpeq := hflat_s x.toNat hi hfl
                   have hpx_rt : px.toNat = ufRoot pars x.toNat cv.toNat := by
                     rw [hrt_all x.toNat hi, ← hfl, ← hpeq, List.getElem?_eq_getElem hx_len,
                       Option.getD_some]
                   have hrt_fix := ufRoot_is_root hord_s hi hi
                   rw [← hpx_rt, List.getElem?_eq_getElem hpx_len, Option.getD_some] at hrt_fix
                   have hppx_eq : ppx = px := BitVec.eq_of_toNat_eq hrt_fix
                   rw [hppx_eq, List.getElem?_set_self hx_len, ← List.getElem?_eq_getElem hx_len,
                     hpeq]
                 · rw [List.getElem?_set_ne (Ne.symm hix)]; exact hflat_s i hi hfl,
               fun i hi => by
                 rw [List.getElem?_set_ne (by omega)]
                 exact hsuf_s i hi,
               hmk⟩
          · intro K hK
            c0_hsplit
            · have hxz_len : (x.setWidth 64).toNat < pars.length := by rw [hxz]; exact hx_len
              c0_hstraight
              have h_eq1 : pars[(BitVec.setWidth 64 x).toNat]'hxz_len = px := by
                change (some (pars[(BitVec.setWidth 64 x).toNat]'hxz_len)).getD 0#32 = pars[x.toNat]
                rw [← List.getElem?_eq_getElem hxz_len, hxz, List.getElem?_eq_getElem hx_len]; rfl
              have h_eq2 :
                  pars[(BitVec.setWidth 64 (pars[(BitVec.setWidth 64 x).toNat]'hxz_len)).toNat]'
                  (by rw [h_eq1]; exact hpxz_len) = ppx := by
                change (some _).getD 0#32 = ppx
                rw [← List.getElem?_eq_getElem, h_eq1, hpxz, hpx_get]
              have h_set_eq : pars.set (BitVec.setWidth 64 x).toNat
                  (pars[(BitVec.setWidth 64 (pars[(BitVec.setWidth 64 x).toNat]'hxz_len)).toNat]'
                    (by rw [h_eq1]; exact hpxz_len)) = pars.set x.toNat ppx := by
                rw [h_eq2, hxz]
              exact hK m ((congrArg (fun l => (array (t := i32) par_ptr l ⋆ R) m) h_set_eq).mp hm)
            · exfalso
              have hc_not :
                  ¬ (pars[(px.setWidth 64).toNat]'hpxz_len).toNat < cv.toNat := by
                assumption
              have hlt_cv : (pars[(px.setWidth 64).toNat]'hpxz_len).toNat < cv.toNat := by
                have h_eq : pars[(px.setWidth 64).toNat]'hpxz_len = ppx := by
                  change (some (pars[(px.setWidth 64).toNat]'hpxz_len)).getD 0#32 = ppx
                  rw [← List.getElem?_eq_getElem hpxz_len, hpxz, hpx_get]
                rw [h_eq]
                exact Nat.lt_of_le_of_lt hppx_ord (Nat.lt_trans hpx_lt hx_lt)
              exact hc_not hlt_cv
    · exfalso; omega
  · exfalso; omega


theorem full_xor_sort5_wp (Γ : Env) :
    ∀ a m Q X, fullXorSort5Spec a m Q X →
      Func.wp Γ full_xor_sort5_body a m Q X := by
  rintro ⟨tmp_ptr, k, cv, ⟨⟩⟩ m0 Q X ⟨tmp, R, hk_len, htmp31, hcv31, hm0, hQ⟩
  have hlen32 : tmp.length < 2 ^ 32 := by omega
  -- Loop 1: check `(tmp[i] >> 1u) < cv`
  c0_hstraight
  refine wp_loop_inv
    (fun (i, ()) mi =>
      i.toNat ≤ k.toNat ∧
      (∀ t < i.toNat, (tmp[t]?.getD 0#32).toNat / 2 < cv.toNat) ∧
      (array (t := i32) tmp_ptr tmp ⋆ R) mi)
    (fun (i, ()) _ => k.toNat - i.toNat)
    (fun J hJ => by
      c0_hstraight
      exact hJ (0#32, ()) m0 ⟨Nat.zero_le _, fun _ ht => absurd ht (Nat.not_lt_zero _), hm0⟩)
    (fun J (i, ()) mi ⟨hi_le, hok_i, hmi⟩ ih => ?_)
  c0_hsplit
  · have hi_lt : i.toNat < k.toNat := by bv_omega
    have hi_len : i.toNat < tmp.length := by omega
    have hiz : (i.setWidth 64).toNat = i.toNat := bv_zext32_toNat i
    c0_hsplit
    · c0_hstraight
      exact hQ false tmp mi (by rfl) (.refl _) (fun _ _ => rfl) (fun h => nomatch h) hmi
    · have hlt_i : (tmp[i.toNat]?.getD 0#32).toNat / 2 < cv.toNat := by
        simp only [List.getElem?_eq_getElem hi_len, Option.getD_some]
        simp only [Nat.pow_one] at *
        bv_omega
      have hi1 : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
      c0_hstraight
      refine ih (i + 1#32, ()) mi (by dsimp only; omega) ⟨by omega, fun t ht => ?_, hmi⟩
      rw [hi1] at ht
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp ht) with htl | rfl
      · exact hok_i t htl
      · exact hlt_i
  · have hi_eq : i.toNat = k.toNat := by bv_omega
    have hcv_all : ∀ t < k.toNat, (tmp[t]?.getD 0#32).toNat / 2 < cv.toNat := by
      intro t ht; exact hok_i t (by omega)
    -- Loop 2: bubble-sort permutation over `tmp[0 .. k)`
    c0_hstraight
    refine wp_loop_inv
      (fun (i2, ()) m2 => ∃ tmp2 : List (BitVec 32),
        tmp2.length = tmp.length ∧ i2.toNat ≤ k.toNat ∧
        (tmp2.take k.toNat).Perm (tmp.take k.toNat) ∧
        (∀ t, k.toNat ≤ t → tmp2[t]? = tmp[t]?) ∧
        (array (t := i32) tmp_ptr tmp2 ⋆ R) m2)
      (fun (i2, ()) _ => k.toNat - i2.toNat)
      (fun J2 hJ2 => by
        c0_hstraight
        exact hJ2 (0#32, ()) mi ⟨tmp, rfl, Nat.zero_le _, .refl _, fun _ _ => rfl, hmi⟩)
      (fun J2 (i2, ()) m2 ⟨tmp2, hlen2, hi2_le, hperm2, hfr2, hm2⟩ ih2 => ?_)
    c0_hsplit
    · have hi2_lt : i2.toNat < k.toNat := by bv_omega
      have hi2_succ : (i2 + 1#32).toNat = i2.toNat + 1 := by bv_omega
      c0_hstraight
      refine wp_loop_inv
        (fun (j, ()) mj => ∃ tmpj : List (BitVec 32),
          tmpj.length = tmp.length ∧ i2.toNat < j.toNat ∧ j.toNat ≤ k.toNat ∧
          (tmpj.take k.toNat).Perm (tmp.take k.toNat) ∧
          (∀ t, k.toNat ≤ t → tmpj[t]? = tmp[t]?) ∧
          (array (t := i32) tmp_ptr tmpj ⋆ R) mj)
        (fun (j, ()) _ => k.toNat - j.toNat)
        (fun Jj hJj => by
          c0_hstraight
          exact hJj (i2 + 1#32, ()) m2 ⟨tmp2, hlen2, by omega, by omega, hperm2, hfr2, hm2⟩)
        (fun Jj (j, ()) mj ⟨tmpj, hlenj, hij_lt, hj_le, hpermj, hfrj, hmj⟩ ihj => ?_)
      c0_hsplit
      · have hj_lt : j.toNat < k.toNat := by bv_omega
        have hi2_lenj : i2.toNat < tmpj.length := by omega
        have hj_lenj : j.toNat < tmpj.length := by omega
        have hi2z : (i2.setWidth 64).toNat = i2.toNat := bv_zext32_toNat i2
        have hjz : (j.setWidth 64).toNat = j.toNat := bv_zext32_toNat j
        have hj1 : (j + 1#32).toNat = j.toNat + 1 := by bv_omega
        c0_hstraight
        refine wp_join0
          (fun mk => ∃ tmpk : List (BitVec 32),
            tmpk.length = tmp.length ∧
            (tmpk.take k.toNat).Perm (tmp.take k.toNat) ∧
            (∀ t, k.toNat ≤ t → tmpk[t]? = tmp[t]?) ∧
            (array (t := i32) tmp_ptr tmpk ⋆ R) mk)
          ?_ ?_
        · rintro K mk ⟨tmpk, hlenk, hpermk, hfrk, hmk⟩
          c0_hstraight
          exact ihj (j + 1#32, ()) mk (by dsimp only; omega)
            ⟨tmpk, hlenk, by omega, by omega, hpermk, hfrk, hmk⟩
        · intro K hK
          c0_hsplit
          · c0_hstraight
            let a := tmpj[i2.toNat]'hi2_lenj
            let b := tmpj[j.toNat]'hj_lenj
            let tmpj' := (tmpj.set i2.toNat b).set j.toNat a
            have hperm' : (tmpj'.take k.toNat).Perm (tmp.take k.toNat) :=
              (perm_swap_take hij_lt hj_lt (by omega)).trans hpermj
            have hfr' : ∀ t, k.toNat ≤ t → tmpj'[t]? = tmp[t]? := fun t ht => by
              simp only [tmpj']
              rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
              exact hfrj t ht
            exact hK m ⟨tmpj', by simp [tmpj', hlenj], hperm', hfr',
              by simpa [tmpj', a, b, hi2z, hjz] using hm⟩
          · c0_hstraight
            exact hK mj ⟨tmpj, hlenj, hpermj, hfrj, hmj⟩
      · have hj_eq : j.toNat = k.toNat := by bv_omega
        c0_hstraight
        exact ih2 (i2 + 1#32, ()) mj (by dsimp only; omega)
          ⟨tmpj, hlenj, by omega, hpermj, hfrj, hmj⟩
    · -- Loop 3: verify adjacent `<` over `tmp2[0 .. k)`
      have hi2_eq : i2.toNat = k.toNat := by bv_omega
      have hcv2 : ∀ t < k.toNat, (tmp2[t]?.getD 0#32).toNat / 2 < cv.toNat := by
        intro t ht
        have hmem : tmp2[t]'(by omega) ∈ tmp2.take k.toNat := by
          have hmt :
              tmp2[t]'(by omega) =
                (tmp2.take k.toNat)[t]'(by rw [List.length_take]; omega) := by
            simp [List.getElem_take]
          rw [hmt]; exact List.getElem_mem _
        have hmem0 : tmp2[t]'(by omega) ∈ tmp.take k.toNat := (hperm2.mem_iff).mp hmem
        rcases List.getElem_of_mem hmem0 with ⟨s, hs, hseq⟩
        rw [List.length_take, Nat.min_eq_left hk_len] at hs
        rw [List.getElem_take] at hseq
        have hc := hcv_all s hs
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hc ⊢
        rw [← hseq]; exact hc
      c0_hstraight
      refine wp_loop_inv
        (fun (p, ()) mp =>
          p.toNat ≤ k.toNat ∧
          (∀ q, q < p.toNat → q + 1 < k.toNat →
            (tmp2[q]?.getD 0#32).toNat / 2 < (tmp2[q + 1]?.getD 0#32).toNat / 2) ∧
          (array (t := i32) tmp_ptr tmp2 ⋆ R) mp)
        (fun (p, ()) _ => k.toNat - p.toNat)
        (fun J3 hJ3 => by
          c0_hstraight
          exact hJ3 (0#32, ()) m2 ⟨Nat.zero_le _, fun _ h => absurd h (Nat.not_lt_zero _), hm2⟩)
        (fun J3 (p, ()) mp ⟨hp_le, hadj_p, hmp⟩ ih3 => ?_)
      c0_hsplit
      · have hp1_bv : (p + 1#32).toNat = p.toNat + 1 := by bv_omega
        have hp_lt : p.toNat + 1 < k.toNat := by bv_omega
        have hp_len : p.toNat < tmp2.length := by omega
        have hp1_len : p.toNat + 1 < tmp2.length := by omega
        have hpz : (p.setWidth 64).toNat = p.toNat := bv_zext32_toNat p
        have hp1z : ((p + 1#32).setWidth 64).toNat = p.toNat + 1 := by
          rw [bv_zext32_toNat, hp1_bv]
        c0_hsplit
        · c0_hstraight
          exact hQ false tmp2 mp hlen2 hperm2 hfr2 (fun h => nomatch h) hmp
        · have hadj_now : (tmp2[p.toNat]?.getD 0#32).toNat / 2 <
              (tmp2[p.toNat + 1]?.getD 0#32).toNat / 2 := by
            have hp1_mod : (p.toNat + 1) % 2 ^ 32 = p.toNat + 1 := Nat.mod_eq_of_lt (by omega)
            simp only [List.getElem?_eq_getElem hp_len, List.getElem?_eq_getElem hp1_len,
              Option.getD_some]
            simp only [Nat.pow_one, hp1_mod] at *
            bv_omega
          c0_hstraight
          refine ih3 (p + 1#32, ()) mp (by dsimp only; omega) ⟨by omega, fun q hq1 hq2 => ?_, hmp⟩
          rw [hp1_bv] at hq1
          rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hq1) with hql | rfl
          · exact hadj_p q hql hq2
          · exact hadj_now
      · have hp_ge : k.toNat ≤ p.toNat + 1 := by bv_omega
        c0_hstraight
        refine hQ true tmp2 mp hlen2 hperm2 hfr2 (fun _ => ⟨hcv2, ?_⟩) hmp
        apply strictSorted_of_adj
        intro q hq
        rw [List.length_map, List.length_take, Nat.min_eq_left (by omega)] at hq
        have hlt := hadj_p q (by omega) hq
        rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega),
          Option.getD_some, Option.getD_some] at hlt
        simp only [List.getElem!_eq_getElem?_getD, List.getElem?_map, List.getElem?_take]
        rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)]
        simpa [show q < k.toNat by omega, hq] using hlt


/-! ## 4. Shared Arena, Witness, Pool & Chain-Framing Helpers -/

theorem fullSparseInvW_upd_probing {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (h : FullSparseInvW c F0 F_cur s)
    (p' : BitVec 64) :
    FullSparseInvW c F0 F_cur { s with core := { s.core with probing := p' } } := by
  have hcok : ({ s.core with probing := p' } : FullCoreState).LengthsOk c :=
    { h.1.core_ok with vals_len := h.1.core_ok.vals_len }
  have hw' : FullWitnessInv c F0 F_cur { s.core with probing := p' } :=
    { h.2.1 with
      arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
      watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }
  refine ⟨⟨hcok, h.1.2⟩, hw', fullLitMarksClear_of_eq h.2.2.1 rfl rfl,
    fullArenaVarsNodup_of_eq h.2.2.2.1 rfl rfl, ?_, h.2.2.2.2.2⟩
  exact h.2.2.2.2.1.of_pres ⟨rfl, rfl⟩ fun _ hr => hr

theorem fullSparseInvW_to_sparseInv {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (h : FullSparseInvW c F0 F_cur s) :
    FullSparseInv c F0 s :=
  ⟨⟨h.1, ⟨F_cur, h.2.1⟩⟩, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem xorVarsSound_both_unsat {F : CNF Nat} {vs : List Nat}
    (h0 : XorVarsSound F vs false) (h1 : XorVarsSound F vs true) : F.Unsat :=
  fun α => Bool.eq_false_iff.mpr fun hα => Bool.noConfusion ((h0 α hα).symm.trans (h1 α hα))

theorem xorVarsSound_nil_true_unsat {F : CNF Nat}
    (h : XorVarsSound F [] true) : F.Unsat :=
  fun α => Bool.eq_false_iff.mpr fun hα => by
    have hv := h α hα; simp [xorEvalVars_nil] at hv

theorem entailsClause_perm {F : CNF Nat} {xs ys : List Nat} (hp : xs.Perm ys)
    (h : F.EntailsClause (cnfClause xs)) : F.EntailsClause (cnfClause ys) :=
  Std.Sat.CNF.entails_clause_def.mpr fun α hα =>
    (sat_cnfClause_congr fun _x => hp.mem_iff).mp ((Std.Sat.CNF.entails_clause_def.mp h) α hα)

theorem list_take_succ_set {α : Type} {xs : List α} {k : Nat} {v : α}
    (hk : k < xs.length) :
    (xs.set k v).take (k + 1) = xs.take k ++ [v] := by
  induction xs generalizing k with
  | nil => simp at hk
  | cons x xs ih =>
    cases k with
    | zero => simp
    | succ k =>
      simp only [List.length_cons] at hk
      rw [List.set_cons_succ, List.take_succ_cons, ih (Nat.lt_of_succ_lt_succ hk)]
      rfl

theorem list_take_succ_of_lt {α : Type} {xs : List α} {k : Nat} (hk : k < xs.length) :
    xs.take (k + 1) = xs.take k ++ [xs[k]] := by
  induction xs generalizing k with
  | nil => simp at hk
  | cons x xs ih =>
    cases k with
    | zero => simp
    | succ k =>
      simp only [List.length_cons] at hk
      rw [List.take_succ_cons, ih (Nat.lt_of_succ_lt_succ hk)]
      rfl

theorem fullWitnessInv_vals_falsified_entails {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k)
    (hl0 : k.cur_level = 0) {clits kept : List Nat}
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause clits))
    (hsub : ∀ l ∈ clits, l ∈ kept ∨ (l < 2 * k.cur_vars ∧ k.vals[l]?.getD 0#8 = 255#8)) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause kept) :=
  Std.Sat.CNF.entails_clause_def.mpr fun α hα => by
  obtain ⟨l, hl_mem, hl_sat⟩ :=
    (clause_sat_cnfClause_iff α clits).mp ((Std.Sat.CNF.entails_clause_def.mp hent) α hα)
  rcases hsub l hl_mem with hk | ⟨hl_lt, hv⟩
  · exact (clause_sat_cnfClause_iff α kept).mpr ⟨l, hk, hl_sat⟩
  · obtain ⟨i, hi_lt, hi_trl⟩ := (hw.vals_false_iff l hl_lt).mp hv
    have hlvl0 : (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
      have := hw.lvl_le i hi_lt; omega
    have hu := (Std.Sat.CNF.entails_clause_def.mp (hw.level0_sound i hi_lt hlvl0)) α hα
    rw [hi_trl] at hu
    have hneg := (sat_cnfClause_singleton α (l ^^^ 1)).mp hu
    have hvv : (l ^^^ 1) / 2 = l / 2 := by
      rw [FullM6ProofUtil.nat_xor1_eq]; split <;> omega
    have hss : (l ^^^ 1) % 2 = 1 - l % 2 := FullM6ProofUtil.nat_xor1_mod2 l
    simp only [litVar, litSign, hvv, hss] at hneg hl_sat
    rcases Nat.mod_two_eq_zero_or_one l with hm | hm <;> simp_all

theorem fullArenaScanRefs_next {ar : List (BitVec 32)} {alen : Nat} :
    ∀ {fuel pos r : Nat},
      alen - pos ≤ fuel →
      (∀ x ∈ fullArenaScanRefs ar alen pos fuel, x + 6 ≤ fullArenaNextOff ar alen x) →
      r ∈ fullArenaScanRefs ar alen pos fuel →
      fullArenaNextOff ar alen r + 3 ≤ alen →
      fullArenaNextOff ar alen r ∈ fullArenaScanRefs ar alen pos fuel
  | 0, _, _, _, _, hr, _ => nomatch hr
  | fuel + 1, pos, r, hfl, hwf, hr, hbd => by
    rw [fullArenaScanRefs.eq_2] at hr ⊢
    split at hr
    · next hp =>
      simp only [hp, ↓reduceIte, List.mem_cons] at hr ⊢
      have hpos_step : pos + 6 ≤ fullArenaNextOff ar alen pos :=
        hwf pos (by rw [fullArenaScanRefs.eq_2]; simp [hp])
      rcases hr with heq_r | hr_tail
      · subst heq_r
        right
        have hfl' : alen - fullArenaNextOff ar alen r ≤ fuel := by omega
        have hpos_nz : fuel ≠ 0 := by omega
        obtain ⟨f', hf'⟩ := Nat.exists_eq_succ_of_ne_zero hpos_nz
        rw [hf', fullArenaScanRefs.eq_2]
        simp [hbd]
      · right
        exact fullArenaScanRefs_next (by omega)
          (fun x hx => hwf x (by rw [fullArenaScanRefs.eq_2]; simp [hp, hx])) hr_tail hbd
    · exact nomatch hr

theorem fullArena_start_mem {c : FullCfg} {F_cur : List (List Nat)} {k : FullCoreState}
    (ha : FullArenaClausesInv c F_cur k) :
    0 = k.arena_len ∨ 0 ∈ fullArenaClauseRefsCore k := by
  rcases ha.len_ok with h0 | h3
  · exact Or.inl h0.symm
  · right
    obtain ⟨f', hf⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k.arena_len ≠ 0)
    have h3' : 0 + 3 ≤ f'.succ := by omega
    unfold fullArenaClauseRefsCore
    rw [hf, fullArenaScanRefs.eq_2]
    simp [h3']

theorem fullArenaClauseRefs_next {c : FullCfg} {F_cur : List (List Nat)}
    {k : FullCoreState} (ha : FullArenaClausesInv c F_cur k)
    {r : Nat} (hr : r ∈ fullArenaClauseRefsCore k) :
    fullArenaNextOff k.arena k.arena_len r = k.arena_len ∨
      fullArenaNextOff k.arena k.arena_len r ∈ fullArenaClauseRefsCore k := by
  have hwf_r := ha.refs_wf r hr
  rcases hwf_r.2.2.2.2 with heq | hbd
  · exact Or.inl heq
  · right
    refine fullArenaScanRefs_next (Nat.sub_le _ _) (fun x hx => ?_) hr hbd
    have hwx := ha.refs_wf x hx
    omega

theorem poolStarts_extend {F : CNF Nat} {cv : Nat} {scr1 scr2 : List (BitVec 32)}
    {eq_end1 eq_end2 fuel p : Nat} (hle : eq_end1 ≤ eq_end2)
    (hp_lt : p < eq_end1)
    (heq : ∀ i < eq_end1,
      (((scr2[i]?.getD 0#32) >>> 16#32) &&& 0x7FFF#32) =
      (((scr1[i]?.getD 0#32) >>> 16#32) &&& 0x7FFF#32))
    (_hpool : XorEqPoolOk F cv scr1 eq_end1 0)
    (hm : p ∈ poolStarts scr1 eq_end1 0 fuel) :
    p ∈ poolStarts scr2 eq_end2 0 fuel := by
  have hgen : ∀ k q, q < eq_end1 →
      (∀ i, q ≤ i → i < eq_end1 →
        (((scr2[i]?.getD 0#32) >>> 16#32) &&& 0x7FFF#32) =
        (((scr1[i]?.getD 0#32) >>> 16#32) &&& 0x7FFF#32)) →
      p ∈ poolStarts scr1 eq_end1 q k →
      p ∈ poolStarts scr2 eq_end2 q k := by
    intro k
    induction k with
    | zero => intro q _ _ h; exact nomatch h
    | succ k ih =>
      intro q hq heqi hm1
      rw [poolStarts] at hm1 ⊢
      have hq2 : q < eq_end2 := by omega
      simp only [hq, hq2, ↓reduceIte, List.mem_cons] at hm1 ⊢
      rcases hm1 with rfl | hm2
      · exact Or.inl rfl
      · right
        have hst : (((scr2[q]?.getD 0#32) >>> 16#32) &&& 0x7FFF#32) =
            (((scr1[q]?.getD 0#32) >>> 16#32) &&& 0x7FFF#32) :=
          heqi q (Nat.le_refl _) hq
        rw [hst]
        have hge := poolStarts_ge hm2
        exact ih _ (by omega) (fun i hi1 hi2 => heqi i (by omega) hi2) hm2
  by_cases h0 : 0 < eq_end1
  · exact hgen fuel 0 h0 (fun i _ hi => heq i hi) hm
  · omega

@[expose] def FullChainRest (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  (array (t := i32) c.pWsort s.scratch.wsort ⋆
   array (t := i32) c.pTarjanMark s.scratch.tarjan_mark ⋆
   array (t := i32) c.pDelayed s.scratch.delayed ⋆
   array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
   array (t := i32) c.pExtendStk s.scratch.extend_stk) ⋆
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆ FullCoreArrays c s.core ⋆
  FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆ FullScrMetaArrs c s.scratch ⋆ c.pad

theorem focus_full_chain {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) :
    (array (t := i32) c.pScratchBuf s.scratch.scratch_buf ⋆
      array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆
      array (t := i32) c.pWorkStk2 s.scratch.work_stk2 ⋆
      array (t := i32) c.pTarjanReach s.scratch.tarjan_reach ⋆
      (FullChainRest c s ⋆ R)) m := by
  unfold FullMem FullScratchArrays FullScrWksArrs FullScrDynArrs at hm
  unfold FullChainRest
  ecancel

theorem unfocus_full_chain {c : FullCfg} {s : FullState}
    {scr' ws1' ws2' tr' : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (array (t := i32) c.pScratchBuf scr' ⋆
      array (t := i32) c.pWorkStk1 ws1' ⋆
      array (t := i32) c.pWorkStk2 ws2' ⋆
      array (t := i32) c.pTarjanReach tr' ⋆
      (FullChainRest c s ⋆ R)) m) :
    (FullMem c { s with scratch :=
      { s.scratch with
        scratch_buf := scr', work_stk1 := ws1',
        work_stk2 := ws2', tarjan_reach := tr' } } ⋆ R) m := by
  change (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
      s.core.d_cur s.core.d_val ⋆
    array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆ FullCoreArrays c s.core ⋆
    (FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆
      (array (t := i32) c.pWsort s.scratch.wsort ⋆
       array (t := i32) c.pWorkStk1 ws1' ⋆
       array (t := i32) c.pWorkStk2 ws2' ⋆
       array (t := i32) c.pTarjanMark s.scratch.tarjan_mark ⋆
       array (t := i32) c.pTarjanReach tr') ⋆
      FullScrMetaArrs c s.scratch ⋆
      (array (t := i32) c.pDelayed s.scratch.delayed ⋆
       array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
       array (t := i32) c.pExtendStk s.scratch.extend_stk ⋆
       array (t := i32) c.pScratchBuf scr')) ⋆
    c.pad ⋆ R) m
  unfold FullChainRest at hm
  ecancel


theorem dimacsBound_val : LeanQbe.T.Examples.LratBytes.dimacsBound = 268435456 := rfl

end LeanQbe.T.Examples.Kissat.FullM8XorGauss
