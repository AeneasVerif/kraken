module

public import LeanQbe.T.Examples.Kissat.FullM5CongFixProof1
public import LeanQbe.T.Examples.Kissat.FullM6CongSubstProof1b
public import LeanQbe.T.Examples.Kissat.FullDefSweepLemmas
public import LeanQbe.T.Examples.Kissat.FullM7CongIte
import Kraken.Mem
import Kraken.Separation

/-!
# Formal Verification of `FullM7CongIte` (`O(deg log deg)` Conditional-Equivalence ITE Extraction)

Proves memory safety, overflow safety, functional correctness, and `GateSeqOk32` ITE gate
soundness for all 7 functions in `FullM7CongIte` (`m7CongIteModule`):
1. `full_cong_u64_sift_m7` / `full_cong_u64_sort_m7` — in-place `O(n log n)` `u64` heapsort.
2. `full_cong_bsearch_u64_m7` — sorted `u64` binary search on `[lo, hi)`.
3. `full_cong_copy_condbin_m7` — ternary watch scan (`sz == 3`, 3 unassigned lits, distinct vars),
   sorted + deduped `CondBinElemOk`.
4. `full_cong_extract_condeq_m7` — sorted opposite-polarity conditional equivalence extraction
   (`CondEqElemOk`).
5. `full_cong_merge_condeq_m7` — two-pointer conditional-equivalence merge emitting sound 5-word
   ITE gate records `(y, (2<<28)|3, c, t, e)` into `scratch_buf` (`GateSeqOk32`).
6. `full_cong_extract_ite_all_m7` — outer variable driver preserving `FullDenseInv` and
   appending `GateSeqOk32` records from `g_len` to `g_len'`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7CongIte

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM5CongFix
open LeanQbe.T.Examples.Kissat.FullM6CongSubst (M6GateAt M6GateSeqOk m6GateSeqOk_append)
open LeanQbe.T.Examples.Kissat.Full.FullCongHelpers
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Full.FullCongTactics
open Kraken.Bedrock2.Test

/-! ## 1. `BitVec` Helpers, `FullMemNoWks3`, and Local `array64` Framing -/

theorem bv64_mul8_eq {i : BitVec 64} :
    i * 8 = BitVec.ofNat 64 (8 * i.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, Nat.mul_comm]

theorem bv64_mul4_eq {i : BitVec 64} :
    i * 4 = BitVec.ofNat 64 (4 * i.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, Nat.mul_comm]

theorem c0_load_arr64 {a : BitVec 64} {xs : List (BitVec 64)} {i : BitVec 64}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : i.toNat < xs.length) (hm : (array64 a xs ⋆ R) m) :
    loadVal m i64 (a + i * 8) = some xs[i.toNat] := by
  rw [bv64_mul8_eq]; exact loadVal_array64 hi hm

theorem c0_load_arr64_0 {a : BitVec 64} {xs : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64} (h0 : 0 < xs.length) (hm : (array64 a xs ⋆ R) m) :
    loadVal m i64 (a + 0) = some xs[0] := by
  simpa using loadVal_array64 (i := 0) h0 hm

theorem c0_load_arr64_zext0 {a : BitVec 64} {xs : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64} (h0 : 0 < xs.length) (hm : (array64 a xs ⋆ R) m) :
    loadVal m i64 (a + (0#32).signExtend 64 * 8) = some xs[0] := by
  simpa using loadVal_array64 (i := 0) h0 hm

theorem c0_store_arr64 {a : BitVec 64} {xs : List (BitVec 64)} {i : BitVec 64}
    (v : BitVec 64) {R : Mem 64 → Prop} {m : Mem 64} (hi : i.toNat < xs.length)
    (hm : (array64 a xs ⋆ R) m) :
    storeOk m i64 (a + i * 8) ∧
      (array64 a (xs.set i.toNat v) ⋆ R) (storeMem m i64 (a + i * 8) v) := by
  rw [bv64_mul8_eq]; exact store_array64 v hi hm

theorem c0_store_arr64_0 {a : BitVec 64} {xs : List (BitVec 64)}
    (v : BitVec 64) {R : Mem 64 → Prop} {m : Mem 64} (h0 : 0 < xs.length)
    (hm : (array64 a xs ⋆ R) m) :
    storeOk m i64 (a + 0) ∧
      (array64 a (xs.set 0 v) ⋆ R) (storeMem m i64 (a + 0) v) := by
  simpa using store_array64 v (i := 0) h0 hm

theorem c0_store_arr64_zext0 {a : BitVec 64} {xs : List (BitVec 64)}
    (v : BitVec 64) {R : Mem 64 → Prop} {m : Mem 64} (h0 : 0 < xs.length)
    (hm : (array64 a xs ⋆ R) m) :
    storeOk m i64 (a + (0#32).signExtend 64 * 8) ∧
      (array64 a (xs.set 0 v) ⋆ R) (storeMem m i64 (a + (0#32).signExtend 64 * 8) v) := by
  simpa using store_array64 v (i := 0) h0 hm

attribute [local c0_load] c0_load_arr64 c0_load_arr64_0 c0_load_arr64_zext0
attribute [local c0_store] c0_store_arr64 c0_store_arr64_0 c0_store_arr64_zext0

def FullScrWksArrsNo3 (c : FullCfg) (sc : FullScratch) : Mem 64 → Prop :=
  array (t := i32) c.pTarjanMark sc.tarjan_mark ⋆
  array (t := i32) c.pTarjanReach sc.tarjan_reach

def FullScratchArraysNo3 (c : FullCfg) (sc : FullScratch) : Mem 64 → Prop :=
  FullScrByteArrs c sc ⋆ FullScrU32A c sc ⋆ FullScrWksArrsNo3 c sc ⋆
    FullScrMetaArrs c sc ⋆ FullScrDynArrs c sc

def FullMemNoWks3 (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
  FullCoreArrays c s.core ⋆ FullScratchArraysNo3 c s.scratch ⋆ c.pad

def FullNoWks3ScrBufRest (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
  FullCoreArrays c s.core ⋆
  (FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆ FullScrWksArrsNo3 c s.scratch ⋆
   FullScrMetaArrs c s.scratch ⋆
   array (t := i32) c.pDelayed s.scratch.delayed ⋆
   array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
   array (t := i32) c.pExtendStk s.scratch.extend_stk) ⋆ c.pad

theorem fullNoWks3_scrBuf_rest_irrel (c : FullCfg) (s : FullState)
    (scr' : List (BitVec 32)) :
    FullNoWks3ScrBufRest c { s with scratch := { s.scratch with scratch_buf := scr' } } =
      FullNoWks3ScrBufRest c s := by
  unfold FullNoWks3ScrBufRest Full.hdrTailWords Full.hdrTailWords0 Full.hdrTailWords1
    Full.hdrTailWords2 Full.hdrTailWords3 FullScrByteArrs FullScrU32A FullScrWksArrsNo3
    FullScrMetaArrs
  rfl

theorem focus_noWks3_scratch_buf {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hm : (FullMemNoWks3 c s ⋆ R) m) :
    (array (t := i32) c.pScratchBuf s.scratch.scratch_buf ⋆
      (FullNoWks3ScrBufRest c s ⋆ R)) m := by
  unfold FullMemNoWks3 FullScratchArraysNo3 FullScrDynArrs at hm
  unfold FullNoWks3ScrBufRest
  ecancel

theorem fullNoWks3_all_eq (c : FullCfg) (s : FullState) (scr' : List (BitVec 32)) :
    FullMemNoWks3 c { s with scratch := { s.scratch with scratch_buf := scr' } } =
      (array (t := i32) c.pScratchBuf scr' ⋆ FullNoWks3ScrBufRest c s) := by
  rw [← fullNoWks3_scrBuf_rest_irrel c s scr']
  unfold FullMemNoWks3 FullScratchArraysNo3 FullScrDynArrs FullNoWks3ScrBufRest
  ac_rfl

theorem unfocus_noWks3_scratch_buf {c : FullCfg} {s : FullState}
    {scr' : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (array (t := i32) c.pScratchBuf scr' ⋆ (FullNoWks3ScrBufRest c s ⋆ R)) m) :
    (FullMemNoWks3 c { s with scratch := { s.scratch with scratch_buf := scr' } } ⋆ R) m := by
  rw [fullNoWks3_all_eq]; exact sep_ac hm

theorem reg_to_arr64_sep {c : FullCfg} {a : BitVec 64} {xs32 : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64} (hlen : xs32.length = 2 * c.max_vars)
    (hm : (array (t := i32) a xs32 ⋆ R) m) :
    ∃ ys : List (BitVec 64), ys.length = c.max_vars ∧ (array64 a ys ⋆ R) m := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hlen_w : 4 * (2 * c.max_vars) = 8 * c.max_vars := by omega
  have hr : (region a (8 * c.max_vars) ⋆ R) m :=
    LeanQbe.T.sep_mono (fun _ h => by
      have hr0 := array_to_region (t := i32) (by simp [Ty.bytes, Ty.size, i32, hlen]; omega) h
      simpa [Ty.bytes, Ty.size, i32, hlen, hlen_w] using hr0) hm
  have ha : ((fun f => ∃ ys, ys.length = c.max_vars ∧ array64 a ys f) ⋆ R) m :=
    LeanQbe.T.sep_mono (fun _ hf => region_to_array64 c.max_vars (by omega) hf) hr
  obtain ⟨ys, hys⟩ := LeanQbe.T.sep_ex_l.mp ha
  exact ⟨ys, LeanQbe.T.sep_pure_l.mp hys⟩

theorem arr64_to_u32_sep {c : FullCfg} {a : BitVec 64} {ys : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64} (hlen : ys.length = c.max_vars)
    (hm : (array64 a ys ⋆ R) m) :
    ∃ xs32 : List (BitVec 32), xs32.length = 2 * c.max_vars ∧
      (array (t := i32) a xs32 ⋆ R) m := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hlen_w : 4 * (2 * c.max_vars) = 8 * c.max_vars := by omega
  have hr : (region a (4 * (2 * c.max_vars)) ⋆ R) m :=
    LeanQbe.T.sep_mono (fun _ hf => by
      rw [array64_eq_array] at hf
      have hr0 := array_to_region (t := i64) (by simp [Ty.bytes, Ty.size, i64, hlen]; omega) hf
      simpa [Ty.bytes, Ty.size, i64, hlen, hlen_w] using hr0) hm
  have ha : ((fun f => ∃ xs32, xs32.length = 2 * c.max_vars ∧
      array (t := i32) a xs32 f) ⋆ R) m :=
    LeanQbe.T.sep_mono (fun _ hf => region_to_array_i32 (2 * c.max_vars) (by omega) hf) hr
  obtain ⟨xs32, hxs⟩ := LeanQbe.T.sep_ex_l.mp ha
  exact ⟨xs32, LeanQbe.T.sep_pure_l.mp hxs⟩

theorem focus_full_wks3_u64 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hl : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m) :
    ∃ ws64 s1 s2 : List (BitVec 64),
      ws64.length = c.max_vars ∧ s1.length = c.max_vars ∧ s2.length = c.max_vars ∧
      (FullMemNoWks3 c s ⋆ array64 c.pWsort ws64 ⋆ array64 c.pWorkStk1 s1 ⋆
        array64 c.pWorkStk2 s2 ⋆ R) m := by
  have hsl := hl.scratch_ok
  have hm1 : (array (t := i32) c.pWsort s.scratch.wsort ⋆
      (array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆
        (array (t := i32) c.pWorkStk2 s.scratch.work_stk2 ⋆
          (FullMemNoWks3 c s ⋆ R)))) m := by
    unfold FullMem FullScratchArrays FullScrWksArrs at hm
    unfold FullMemNoWks3 FullScratchArraysNo3 FullScrWksArrsNo3
    ecancel
  obtain ⟨ws64, hwsl, hws⟩ := reg_to_arr64_sep hsl.wsort_len hm1
  obtain ⟨s1, hs1l, hs1⟩ := reg_to_arr64_sep hsl.work_stk1_len (by ecancel :
    (array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆
      (array64 c.pWsort ws64 ⋆
        (array (t := i32) c.pWorkStk2 s.scratch.work_stk2 ⋆ (FullMemNoWks3 c s ⋆ R)))) m)
  obtain ⟨s2, hs2l, hs2⟩ := reg_to_arr64_sep hsl.work_stk2_len (by ecancel :
    (array (t := i32) c.pWorkStk2 s.scratch.work_stk2 ⋆
      (array64 c.pWsort ws64 ⋆ array64 c.pWorkStk1 s1 ⋆ (FullMemNoWks3 c s ⋆ R))) m)
  exact ⟨ws64, s1, s2, hwsl, hs1l, hs2l, by ecancel⟩

theorem unfocus_full_wks3_u64 {c : FullCfg} {s : FullState} {ws64 s1 s2 : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hws : ws64.length = c.max_vars) (hs1 : s1.length = c.max_vars) (hs2 : s2.length = c.max_vars)
    (hm : (FullMemNoWks3 c s ⋆ array64 c.pWsort ws64 ⋆ array64 c.pWorkStk1 s1 ⋆
      array64 c.pWorkStk2 s2 ⋆ R) m) :
    ∃ ws32 k1 k2 : List (BitVec 32),
      ws32.length = 2 * c.max_vars ∧ k1.length = 2 * c.max_vars ∧ k2.length = 2 * c.max_vars ∧
      (FullMem c { s with scratch :=
        { s.scratch with wsort := ws32, work_stk1 := k1, work_stk2 := k2 } } ⋆ R) m := by
  obtain ⟨ws32, hws32l, hws32⟩ := arr64_to_u32_sep hws (by ecancel :
    (array64 c.pWsort ws64 ⋆
      (array64 c.pWorkStk1 s1 ⋆ array64 c.pWorkStk2 s2 ⋆ (FullMemNoWks3 c s ⋆ R))) m)
  obtain ⟨k1, hk1l, hk1⟩ := arr64_to_u32_sep hs1 (by ecancel :
    (array64 c.pWorkStk1 s1 ⋆
      (array (t := i32) c.pWsort ws32 ⋆ array64 c.pWorkStk2 s2 ⋆ (FullMemNoWks3 c s ⋆ R))) m)
  obtain ⟨k2, hk2l, hk2⟩ := arr64_to_u32_sep hs2 (by ecancel :
    (array64 c.pWorkStk2 s2 ⋆
      (array (t := i32) c.pWsort ws32 ⋆ array (t := i32) c.pWorkStk1 k1 ⋆
        (FullMemNoWks3 c s ⋆ R))) m)
  have hirr : FullMemNoWks3 c { s with scratch :=
      { s.scratch with wsort := ws32, work_stk1 := k1, work_stk2 := k2 } } =
      FullMemNoWks3 c s := by
    unfold FullMemNoWks3 Full.hdrTailWords Full.hdrTailWords0 Full.hdrTailWords1
      Full.hdrTailWords2 Full.hdrTailWords3 FullScratchArraysNo3 FullScrByteArrs FullScrU32A
      FullScrWksArrsNo3 FullScrMetaArrs FullScrDynArrs
    rfl
  refine ⟨ws32, k1, k2, hws32l, hk1l, hk2l, ?_⟩
  have hmem : FullMem c { s with scratch :=
      { s.scratch with wsort := ws32, work_stk1 := k1, work_stk2 := k2 } } =
      (array (t := i32) c.pWorkStk2 k2 ⋆
        (array (t := i32) c.pWsort ws32 ⋆ array (t := i32) c.pWorkStk1 k1 ⋆
          FullMemNoWks3 c s)) := by
    rw [← hirr]
    unfold FullMem FullScratchArrays FullScrWksArrs FullMemNoWks3 FullScratchArraysNo3
      FullScrWksArrsNo3
    ac_rfl
  rw [hmem]
  exact sep_ac hk2

theorem load_noWks3_hdr {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (i : Nat) (hi : i < 140) (hm : (FullMemNoWks3 c s ⋆ R) m) :
    loadVal m i64 (c.hdr + BitVec.ofNat 64 (32 + 8 * i)) =
      some ((Full.hdrTailWords c s)[i]'(by simp [hi])) := by
  have h1 : (array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
       FullCoreArrays c s.core ⋆ FullScratchArraysNo3 c s.scratch ⋆ c.pad ⋆ R)) m := by
    unfold FullMemNoWks3 at hm; ecancel
  have hi' : i < (Full.hdrTailWords c s).length := by simp [hi]
  have hld := loadVal_array64 hi' h1
  rwa [show c.hdr + (32 : BitVec 64) + BitVec.ofNat 64 (8 * i) =
    c.hdr + BitVec.ofNat 64 (32 + 8 * i) from ptr_add_ofNat c.hdr 32 (8 * i)] at hld

theorem load_noWks3_arena_len {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hm : (FullMemNoWks3 c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 48) = some (BitVec.ofNat 64 s.core.arena_len) :=
  load_noWks3_hdr 2 (by decide) hm

theorem load_noWks3_vals_ptr {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hm : (FullMemNoWks3 c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 64) = some c.pVals :=
  load_noWks3_hdr 4 (by decide) hm

theorem load_noWks3_wvec_ptr {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hm : (FullMemNoWks3 c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 104) = some c.pWvec :=
  load_noWks3_hdr 9 (by decide) hm

theorem load_noWks3_arena_ptr {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hm : (FullMemNoWks3 c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 112) = some c.pArena :=
  load_noWks3_hdr 10 (by decide) hm

theorem load_noWks3_wstk_ptr {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hm : (FullMemNoWks3 c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 120) = some c.pWstk :=
  load_noWks3_hdr 11 (by decide) hm

theorem load_noWks3_flags_ptr {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hm : (FullMemNoWks3 c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 800) = some c.pFlags :=
  load_noWks3_hdr 96 (by decide) hm

theorem load_noWks3_work_stk1_ptr {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hm : (FullMemNoWks3 c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 848) = some c.pWorkStk1 :=
  load_noWks3_hdr 102 (by decide) hm

theorem load_noWks3_work_stk2_ptr {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hm : (FullMemNoWks3 c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 856) = some c.pWorkStk2 :=
  load_noWks3_hdr 103 (by decide) hm

theorem load_noWks3_scratch_buf_ptr {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hm : (FullMemNoWks3 c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 920) = some c.pScratchBuf :=
  load_noWks3_hdr 111 (by decide) hm

theorem load_noWks3_scratch_cap {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hm : (FullMemNoWks3 c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 928) = some (BitVec.ofNat 64 c.scratch_cap) :=
  load_noWks3_hdr 112 (by decide) hm

theorem c0_load_noWks3_vals {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {i : BitVec 64} (hi : i.toNat < s.core.vals.length)
    (hm : (FullMemNoWks3 c s ⋆ R) m) :
    loadVal m i8 (c.pVals + i) = some s.core.vals[i.toNat] := by
  have h1 : (array (t := i8) c.pVals s.core.vals ⋆
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
       array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
       array (t := i8) c.pLitMark s.core.lit_mark ⋆ array (t := i8) c.pMark s.core.mrk ⋆
       FullCoreU32A c s.core ⋆ FullCoreU32B c s.core ⋆ FullCoreDynArrs c s.core ⋆
       FullScratchArraysNo3 c s.scratch ⋆ c.pad ⋆ R)) m := by
    unfold FullMemNoWks3 FullCoreArrays FullCoreByteArrs at hm; ecancel
  have hld := loadVal_array (t := i8) (i := i.toNat) (by decide) hi h1
  simpa [Ty.bytes, Ty.size, i8] using hld

theorem c0_load_noWks3_flags {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {i : BitVec 64} (hi : i.toNat < s.core.flags.length)
    (hm : (FullMemNoWks3 c s ⋆ R) m) :
    loadVal m i32 (c.pFlags + i * 4) = some s.core.flags[i.toNat] := by
  have h1 : (array (t := i32) c.pFlags s.core.flags ⋆
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
       array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆ FullCoreByteArrs c s.core ⋆
       array (t := i32) c.pLevel s.core.lvl ⋆ array (t := i32) c.pReason s.core.rsns ⋆
       array (t := i32) c.pTrail s.core.trl ⋆ array (t := i32) c.pTrailPos s.core.trail_pos ⋆
       array (t := i32) c.pTmp s.core.tmp ⋆ array (t := i32) c.pMinClr s.core.min_clr ⋆
       FullCoreU32B c s.core ⋆ FullCoreDynArrs c s.core ⋆
       FullScratchArraysNo3 c s.scratch ⋆ c.pad ⋆ R)) m := by
    unfold FullMemNoWks3 FullCoreArrays FullCoreU32A at hm; ecancel
  rw [bv64_mul4_eq]
  simpa [Ty.bytes, Ty.size, i32] using
    loadVal_array (t := i32) (i := i.toNat) (by decide) hi h1

theorem c0_load_noWks3_wvec {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {i : BitVec 64} (hi : i.toNat < s.core.wvec.length)
    (hm : (FullMemNoWks3 c s ⋆ R) m) :
    loadVal m i32 (c.pWvec + i * 4) = some s.core.wvec[i.toNat] := by
  have h1 : (array (t := i32) c.pWvec s.core.wvec ⋆
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
       array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆ FullCoreByteArrs c s.core ⋆
       FullCoreU32A c s.core ⋆ array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
       array (t := i32) c.pFrameDec s.core.frame_dec ⋆ array (t := i32) c.pRepr s.core.repr ⋆
       array (t := i32) c.pMinStk s.core.min_stk ⋆ FullCoreDynArrs c s.core ⋆
       FullScratchArraysNo3 c s.scratch ⋆ c.pad ⋆ R)) m := by
    unfold FullMemNoWks3 FullCoreArrays FullCoreU32B at hm; ecancel
  rw [bv64_mul4_eq]
  simpa [Ty.bytes, Ty.size, i32] using
    loadVal_array (t := i32) (i := i.toNat) (by decide) hi h1

theorem c0_load_noWks3_wstk {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {i : BitVec 64} (hi : i.toNat < s.core.wstk.length)
    (hm : (FullMemNoWks3 c s ⋆ R) m) :
    loadVal m i32 (c.pWstk + i * 4) = some s.core.wstk[i.toNat] := by
  have h1 : (array (t := i32) c.pWstk s.core.wstk ⋆
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
       array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆ FullCoreByteArrs c s.core ⋆
       FullCoreU32A c s.core ⋆ FullCoreU32B c s.core ⋆ array (t := i32) c.pArena s.core.arena ⋆
       FullScratchArraysNo3 c s.scratch ⋆ c.pad ⋆ R)) m := by
    unfold FullMemNoWks3 FullCoreArrays FullCoreDynArrs at hm; ecancel
  rw [bv64_mul4_eq]
  simpa [Ty.bytes, Ty.size, i32] using
    loadVal_array (t := i32) (i := i.toNat) (by decide) hi h1

theorem c0_load_noWks3_arena {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {i : BitVec 64} (hi : i.toNat < s.core.arena.length)
    (hm : (FullMemNoWks3 c s ⋆ R) m) :
    loadVal m i32 (c.pArena + i * 4) = some s.core.arena[i.toNat] := by
  have h1 : (array (t := i32) c.pArena s.core.arena ⋆
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
       array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆ FullCoreByteArrs c s.core ⋆
       FullCoreU32A c s.core ⋆ FullCoreU32B c s.core ⋆ array (t := i32) c.pWstk s.core.wstk ⋆
       FullScratchArraysNo3 c s.scratch ⋆ c.pad ⋆ R)) m := by
    unfold FullMemNoWks3 FullCoreArrays FullCoreDynArrs at hm; ecancel
  rw [bv64_mul4_eq]
  simpa [Ty.bytes, Ty.size, i32] using
    loadVal_array (t := i32) (i := i.toNat) (by decide) hi h1

theorem c0_store_noWks3_scratch_buf {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {i : BitVec 64} (v : BitVec 32)
    (hi : i.toNat < s.scratch.scratch_buf.length) (hm : (FullMemNoWks3 c s ⋆ R) m) :
    storeOk m i32 (c.pScratchBuf + i * 4) ∧
      (FullMemNoWks3 c { s with scratch :=
        { s.scratch with scratch_buf := s.scratch.scratch_buf.set i.toNat v } } ⋆ R)
        (storeMem m i32 (c.pScratchBuf + i * 4) v) := by
  have hfs := focus_noWks3_scratch_buf hm
  rw [bv64_mul4_eq]
  obtain ⟨hok, hst⟩ := store_array (t := i32) (i := i.toNat) v (by decide) hi hfs
  exact ⟨by simpa [Ty.bytes, Ty.size, i32] using hok,
    unfocus_noWks3_scratch_buf (by simpa [Ty.bytes, Ty.size, i32] using hst)⟩

attribute [local c0_load] load_noWks3_arena_len load_noWks3_vals_ptr load_noWks3_wvec_ptr
  load_noWks3_arena_ptr load_noWks3_wstk_ptr load_noWks3_flags_ptr
  load_noWks3_work_stk1_ptr load_noWks3_work_stk2_ptr
  load_noWks3_scratch_buf_ptr load_noWks3_scratch_cap
  c0_load_noWks3_vals c0_load_noWks3_flags c0_load_noWks3_wvec
  c0_load_noWks3_wstk c0_load_noWks3_arena
attribute [local c0_store] c0_store_noWks3_scratch_buf

/-! ## 2. Heap, Sortedness, `CondBinElemOk`, `CondEqElemOk`, and `GateAt32` Lemmas -/

def MaxHeapAt (xs : List (BitVec 64)) (hi j : Nat) : Prop :=
  (2 * j + 1 < hi → xs[2 * j + 1]?.getD 0#64 ≤ xs[j]?.getD 0#64) ∧
  (2 * j + 2 < hi → xs[2 * j + 2]?.getD 0#64 ≤ xs[j]?.getD 0#64)

def MaxHeapRange (xs : List (BitVec 64)) (lo hi : Nat) : Prop :=
  ∀ j, lo ≤ j → j < hi → MaxHeapAt xs hi j

def SortedRange64 (xs : List (BitVec 64)) (lo hi : Nat) : Prop :=
  ∀ i j, lo ≤ i → i ≤ j → j < hi → xs[i]?.getD 0#64 ≤ xs[j]?.getD 0#64

def CondBinElemOk (F_cur : List (List Nat)) (cur_vars lit : Nat) (w : BitVec 64) : Prop :=
  let a := (w >>> 32).toNat
  let b := (w &&& 0xFFFFFFFF#64).toNat
  a < 2 * cur_vars ∧ b < 2 * cur_vars ∧
  a / 2 ≠ b / 2 ∧ a / 2 ≠ lit / 2 ∧ b / 2 ≠ lit / 2 ∧
  (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, a, b])

def CondEqElemOk (F_cur : List (List Nat)) (cur_vars lit : Nat) (w : BitVec 64) : Prop :=
  let lhs := (w >>> 32).toNat
  let rhs := (w &&& 0xFFFFFFFF#64).toNat
  lhs < 2 * cur_vars ∧ rhs < 2 * cur_vars ∧
  lhs / 2 ≠ rhs / 2 ∧ lhs / 2 ≠ lit / 2 ∧ rhs / 2 ≠ lit / 2 ∧
  (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, lhs, litNeg rhs]) ∧
  (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, litNeg lhs, rhs])

theorem packU64_hi (a b : BitVec 32) :
    (((a.setWidth 64 <<< 32#64) ||| b.setWidth 64) >>> 32).toNat = a.toNat := by
  have h : ((a.setWidth 64 <<< 32#64) ||| b.setWidth 64) >>> 32 = a.setWidth 64 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    by_cases h32 : i < 32
    · simp [show 32 + i < 64 by omega, show ¬ (32 + i < 32) by omega, h32, hi]
    · have ha : a.getLsbD i = false := BitVec.getLsbD_of_ge (x := a) (i := i) (by omega)
      simp [show ¬ (32 + i < 64) by omega, hi, ha]
  rw [h, bv_zext32_toNat]

theorem packU64_lo (a b : BitVec 32) :
    (((a.setWidth 64 <<< 32#64) ||| b.setWidth 64) &&& 0xFFFFFFFF#64).toNat = b.toNat := by
  have h : ((a.setWidth 64 <<< 32#64) ||| b.setWidth 64) &&& 0xFFFFFFFF#64 = b.setWidth 64 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    have hm : (0xFFFFFFFF#64 : BitVec 64)[i] = decide (i < 32) := by
      rw [BitVec.getElem_eq_testBit_toNat, show (0xFFFFFFFF#64 : BitVec 64).toNat = 2 ^ 32 - 1
        from rfl]
      exact Nat.testBit_two_pow_sub_one 32 i
    by_cases h32 : i < 32
    · simp [hm, h32, hi]
    · have hb : b.getLsbD i = false := BitVec.getLsbD_of_ge (x := b) (i := i) (by omega)
      simp [hm, h32, hi, hb]
  rw [h, bv_zext32_toNat]

theorem u64_trunc32_hi_eq (w : BitVec 64) :
    ((w >>> 32#64).setWidth 32).toNat = (w >>> 32).toNat := by
  have h1 : (w >>> 32#64).setWidth 32 = ((w >>> 32).setWidth 32) := rfl
  rw [h1, BitVec.toNat_setWidth]
  have hlt : (w >>> 32).toNat < 2 ^ 32 := by bv_omega
  exact Nat.mod_eq_of_lt hlt

theorem u64_trunc32_lo_eq (w : BitVec 64) :
    (w.setWidth 32).toNat = (w &&& 0xFFFFFFFF#64).toNat := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_and, show (0xFFFFFFFF#64 : BitVec 64).toNat = 2 ^ 32 - 1
    from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem bv32_lit_div2_xor1 (x : BitVec 32) :
    (x ^^^ 1#32).toNat / 2 = x.toNat / 2 := by
  have hx : (1#32 : BitVec 32) = 1 := rfl
  rw [hx, bv32_xor1_litNeg]
  simpa [litVar] using litVar_litNeg x.toNat

theorem bv32_lit_xor1_even_or {x : BitVec 32} (hx : x &&& 1#32 = 0#32) :
    x ||| 1#32 = x ^^^ 1#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i _
  have h0 : x.getLsbD 0 = false := by
    have hg := congrArg (fun v : BitVec 32 => v.getLsbD 0) hx
    simpa [BitVec.getLsbD_and] using hg
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_xor]
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · simp; exact h0
  · simp [show i ≠ 0 by omega]

theorem evalLitVal_eq_true (α : Nat → Bool) (l : Nat) :
    evalLitVal α l = true ↔ α (litVar l) = !litSign l := by
  unfold evalLitVal; cases α (litVar l) <;> cases litSign l <;> simp

theorem condEq_to_iteGateDef {F_cur : List (List Nat)} {cur_vars c : Nat}
    {w1 w2 : BitVec 64}
    (hw1 : CondEqElemOk F_cur cur_vars (litNeg c) w1)
    (hw2 : CondEqElemOk F_cur cur_vars c w2)
    (hsame : (w1 >>> 32).toNat = (w2 >>> 32).toNat) :
    IteGateDef (cnfOfClauses F_cur) (w1 >>> 32).toNat c
      (w1 &&& 0xFFFFFFFF#64).toNat (w2 &&& 0xFFFFFFFF#64).toNat := by
  refine iteGateDef_of_eval_eq fun α hα => ?_
  have hc1 := CNF.entails_clause_def.mp hw1.2.2.2.2.2.1 α hα
  have hc2 := CNF.entails_clause_def.mp hw1.2.2.2.2.2.2 α hα
  have hd1 := CNF.entails_clause_def.mp hw2.2.2.2.2.2.1 α hα
  have hd2 := CNF.entails_clause_def.mp hw2.2.2.2.2.2.2 α hα
  rw [clause_sat_cnfClause_iff] at hc1 hc2 hd1 hd2
  simp only [List.mem_cons, List.not_mem_nil, or_false, ← evalLitVal_eq_true] at hc1 hc2 hd1 hd2
  cases hcc : evalLitVal α c
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rcases hd1 with ⟨l, rfl | rfl | rfl, hs⟩ <;> rcases hd2 with ⟨l', rfl | rfl | rfl, hs'⟩
    all_goals try (simp [hcc] at hs; try cases hs)
    all_goals try (simp [hcc] at hs'; try cases hs')
    all_goals rw [hsame] at *
    all_goals try simp only [evalLitVal_litNeg] at hs hs'
    all_goals cases hy : evalLitVal α (w2 >>> 32).toNat <;>
      cases he : evalLitVal α (w2 &&& 0xFFFFFFFF#64).toNat <;> simp_all
  · simp only [↓reduceIte]
    rcases hc1 with ⟨l, rfl | rfl | rfl, hs⟩ <;> rcases hc2 with ⟨l', rfl | rfl | rfl, hs'⟩
    all_goals try (simp [evalLitVal_litNeg, hcc] at hs; try cases hs)
    all_goals try (simp [evalLitVal_litNeg, hcc] at hs'; try cases hs')
    all_goals try simp only [evalLitVal_litNeg] at hs hs'
    all_goals cases hy : evalLitVal α (w1 >>> 32).toNat <;>
      cases ht : evalLitVal α (w1 &&& 0xFFFFFFFF#64).toNat <;> simp_all

theorem gateAt32_ite_append {F_cur : List (List Nat)} {cur_vars : Nat}
    {scr0 scr1 : List (BitVec 32)} {g_len : Nat} {y c t e : BitVec 32}
    (hcv : 3 ≤ cur_vars)
    (hy : y.toNat < 2 * cur_vars) (hc : c.toNat < 2 * cur_vars)
    (ht : t.toNat < 2 * cur_vars) (he : e.toNat < 2 * cur_vars)
    (hite : IteGateDef (cnfOfClauses F_cur) y.toNat c.toNat t.toNat e.toNat)
    (hlen0 : g_len + 5 ≤ scr0.length)
    (hscr1 : scr1 = ((((scr0.set g_len y).set (g_len + 1)
      ((2#32 <<< 28#32) ||| 3#32)).set (g_len + 2) c).set (g_len + 3) t).set (g_len + 4) e)
    (hseq0 : GateSeqOk32 F_cur cur_vars scr0 g_len 0) :
    scr1.length = scr0.length ∧
    (∀ idx < g_len, scr1[idx]? = scr0[idx]?) ∧
    GateSeqOk32 F_cur cur_vars scr1 (g_len + 5) 0 := by
  have hlen1 : scr1.length = scr0.length := by
    subst scr1; simp only [List.length_set]
  have hpref : ∀ idx < g_len, scr1[idx]? = scr0[idx]? := by
    intro idx hidx; subst scr1
    repeat rw [List.getElem?_set_ne (by omega)]
  have hg0 : scr1[g_len]? = some y := by
    subst scr1
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_self (by omega)]
  have hmword : scr1[g_len + 1]? = some ((2#32 <<< 28#32) ||| 3#32) := by
    subst scr1
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp; omega)]
  have hg2 : scr1[g_len + 2]? = some c := by
    subst scr1
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_self (by simp; omega)]
  have hg3 : scr1[g_len + 3]? = some t := by
    subst scr1
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp; omega)]
  have hg4 : scr1[g_len + 4]? = some e := by
    subst scr1
    rw [List.getElem?_set_self (by simp; omega)]
  have htag : (((2#32 <<< 28#32) ||| 3#32) >>> 28).toNat = 2 := by decide
  have har : (((2#32 <<< 28#32) ||| 3#32) &&& 255#32).toNat = 3 := by decide
  have hgat : GateAt32 F_cur cur_vars scr1 (g_len + 5) g_len := by
    refine ⟨y, (2#32 <<< 28#32) ||| 3#32, hg0, hmword, hy, ?_⟩
    dsimp only; rw [htag, har]
    refine ⟨Nat.le_refl _, hcv, by decide, fun k hk => ?_, Or.inr (Or.inr ⟨rfl, rfl, ?_⟩)⟩
    · rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
      · exact ⟨c, hg2, hc⟩
      · exact ⟨t, hg3, ht⟩
      · exact ⟨e, hg4, he⟩
    · simpa [hg2, hg3, hg4] using hite
  have hnew : GateSeqOk32 F_cur cur_vars scr1 (g_len + 5) g_len := by
    refine GateSeqOk32.step hgat ?_
    rw [hmword, Option.getD_some, show (((2#32 <<< 28#32) ||| 3#32) &&& 255#32).toNat = 3 from har]
    exact GateSeqOk32.done
  exact ⟨hlen1, hpref, gateSeqOk32_append (by omega) hpref hnew hseq0⟩

theorem maxHeap_le_root {xs : List (BitVec 64)} {hi : Nat}
    (hmh : MaxHeapRange xs 0 hi) :
    ∀ j < hi, xs[j]?.getD 0#64 ≤ xs[0]?.getD 0#64 := by
  intro j
  induction j using Nat.strongRecOn with
  | ind j ih =>
    intro hj
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · exact BitVec.le_refl _
    · let p := (j - 1) / 2
      have hp_lt : p < j := by omega
      have hmp := hmh p (Nat.zero_le _) (by omega)
      dsimp only [MaxHeapAt] at hmp
      have hpc : xs[j]?.getD 0#64 ≤ xs[p]?.getD 0#64 := by
        rcases (by omega : j = 2 * p + 1 ∨ j = 2 * p + 2) with hj1 | hj2
        · rw [← hj1] at hmp; exact hmp.1 hj
        · rw [← hj2] at hmp; exact hmp.2 hj
      exact BitVec.le_trans hpc (ih p hp_lt (by omega))

theorem condBin_of_perm3 {F_cur : List (List Nat)} {cur_vars : Nat}
    {lit a b : BitVec 32} {l0 l1 l2 : Nat}
    (hcl : (cnfOfClauses F_cur).EntailsClause (cnfClause [l0, l1, l2]))
    (hperm : (lit.toNat = l0 ∧ a.toNat = l1 ∧ b.toNat = l2) ∨
             (lit.toNat = l1 ∧ a.toNat = l0 ∧ b.toNat = l2) ∨
             (lit.toNat = l2 ∧ a.toNat = l0 ∧ b.toNat = l1))
    (ha : a.toNat < 2 * cur_vars) (hb : b.toNat < 2 * cur_vars)
    (h1 : a.toNat / 2 ≠ b.toNat / 2) (h2 : a.toNat / 2 ≠ lit.toNat / 2)
    (h3 : b.toNat / 2 ≠ lit.toNat / 2) :
    CondBinElemOk F_cur cur_vars lit.toNat
      (((if b.ult a then b else a).setWidth 64 <<< 32#64) |||
        (if b.ult a then a else b).setWidth 64) := by
  have hent_ab : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat, a.toNat, b.toNat]) := by
    rw [CNF.entails_clause_def] at hcl ⊢
    intro α hα
    obtain ⟨q, hq, hs⟩ := (clause_sat_cnfClause_iff α [l0, l1, l2]).mp (hcl α hα)
    rw [clause_sat_cnfClause_iff]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
    rcases hperm with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases hq with rfl | rfl | rfl <;> exact ⟨_, by simp_all, hs⟩
  have hent_swap :
      (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat, b.toNat, a.toNat]) := by
    rw [CNF.entails_clause_def] at hent_ab ⊢
    intro α hα
    obtain ⟨q, hq, hs⟩ :=
      (clause_sat_cnfClause_iff α [lit.toNat, a.toNat, b.toNat]).mp (hent_ab α hα)
    rw [clause_sat_cnfClause_iff]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
    rcases hq with rfl | rfl | rfl <;> exact ⟨_, by simp_all, hs⟩
  by_cases hult : b.ult a = true
  · simp only [hult, ↓reduceIte]
    unfold CondBinElemOk; rw [packU64_hi, packU64_lo]
    exact ⟨hb, ha, Ne.symm h1, h3, h2, hent_swap⟩
  · simp only [hult, Bool.false_eq_true, ↓reduceIte]
    unfold CondBinElemOk; rw [packU64_hi, packU64_lo]
    exact ⟨ha, hb, h1, h2, h3, hent_ab⟩

/-! ## 3. Specifications & `Func.wp` Proofs for Heapsort, Bsearch & CopyCondbin -/

def m7U64SiftSpec : Spec [i64, i64, i64] [] := fun (a, start, n, ()) m Q _ =>
  ∃ (xs : List (BitVec 64)) (R : Mem 64 → Prop),
    start.toNat ≤ n.toNat ∧ n.toNat ≤ xs.length ∧ xs.length < 2 ^ 61 ∧
    MaxHeapRange xs (start.toNat + 1) n.toNat ∧
    (array64 a xs ⋆ R) m ∧
    ∀ (xs' : List (BitVec 64)) m',
      xs'.length = xs.length →
      (∀ k, n.toNat ≤ k → k < xs.length → xs'[k]? = xs[k]?) →
      (∀ k < n.toNat, ∃ j < n.toNat, xs'[k]? = xs[j]?) →
      MaxHeapRange xs' start.toNat n.toNat →
      (array64 a xs' ⋆ R) m' →
      Q () m'

def m7U64SortSpec : Spec [i64, i64] [] := fun (a, n, ()) m Q _ =>
  ∃ (xs : List (BitVec 64)) (R : Mem 64 → Prop),
    n.toNat ≤ xs.length ∧ xs.length < 2 ^ 61 ∧
    (array64 a xs ⋆ R) m ∧
    ∀ (xs' : List (BitVec 64)) m',
      xs'.length = xs.length →
      (∀ k, n.toNat ≤ k → k < xs.length → xs'[k]? = xs[k]?) →
      (∀ k < n.toNat, ∃ j < n.toNat, xs'[k]? = xs[j]?) →
      SortedRange64 xs' 0 n.toNat →
      (array64 a xs' ⋆ R) m' →
      Q () m'

def m7BsearchU64Spec : Spec [i64, i64, i64, i64] [.bool] := fun (a, lo, hi, key, ()) m Q _ =>
  ∃ (xs : List (BitVec 64)) (R : Mem 64 → Prop),
    lo.toNat ≤ hi.toNat ∧ hi.toNat ≤ xs.length ∧ xs.length < 2 ^ 61 ∧
    SortedRange64 xs lo.toNat hi.toNat ∧
    (array64 a xs ⋆ R) m ∧
    ∀ r : Bool,
      (r = true ↔ ∃ idx, lo.toNat ≤ idx ∧ idx < hi.toNat ∧ xs[idx]? = some key) →
      Q (r, ()) m

def m7CopyCondbinSpec : Spec [i64, i32, i64, i64] [i64] := fun (h, lit, out, cap, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : Std.Sat.CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (out0 : List (BitVec 64)) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ s.core.dense_mode ≠ 0#64 ∧
    lit.toNat < 2 * s.core.cur_vars ∧
    out0.length = cap.toNat ∧ cap.toNat < 2 ^ 61 ∧
    (FullMemNoWks3 c s ⋆ array64 out out0 ⋆ R) m ∧
    ∀ (cnt : BitVec 64) (out' : List (BitVec 64)) m',
      out'.length = cap.toNat →
      cnt.toNat ≤ cap.toNat →
      SortedRange64 out' 0 cnt.toNat →
      (∀ k < cnt.toNat, CondBinElemOk F_cur s.core.cur_vars lit.toNat (out'[k]?.getD 0#64)) →
      (FullMemNoWks3 c s ⋆ array64 out out' ⋆ R) m' →
      Q (cnt, ()) m'

theorem full_cong_u64_sift_m7_wp (Γ : Env) :
    ∀ args m Q X, m7U64SiftSpec args m Q X →
      Func.wp Γ full_cong_u64_sift_m7_body args m Q X := by
  rintro ⟨a, start, n, ⟨⟩⟩ m0 Q X
    ⟨xs0, R, hst_le, hn_le, hlen_bd, hmh0, hm0, hQ⟩
  unfold Func.wp full_cong_u64_sift_m7_body
  fc_to_group
  refine wp_unroll_group fun Jret hJret => ?_
  have hret_ok : ∀ (xs : List (BitVec 64)) (ml : Mem 64) (_x : BitVec 64),
      xs.length = xs0.length →
      (∀ k, n.toNat ≤ k → k < xs.length → xs[k]? = xs0[k]?) →
      (∀ k < n.toNat, ∃ j < n.toNat, xs[k]? = xs0[j]?) →
      MaxHeapRange xs start.toNat n.toNat →
      (array64 a xs ⋆ R) ml →
      Jret (_x, ()) ml := by
    intro xs ml _x hl hk hsub hmh hm
    exact hJret (_x, ()) ml (by
      c0_steps
      exact hQ xs ml hl (fun k hk1 hk2 => hk k hk1 (hl.symm ▸ hk2)) hsub hmh hm)
  fc_to_group
  refine wp_loop_inv
    (fun (root, ()) ml => ∃ xs : List (BitVec 64),
      start.toNat ≤ root.toNat ∧ root.toNat ≤ n.toNat ∧
      xs.length = xs0.length ∧
      (∀ k, n.toNat ≤ k → k < xs.length → xs[k]? = xs0[k]?) ∧
      (∀ k < n.toNat, ∃ j < n.toNat, xs[k]? = xs0[j]?) ∧
      (∀ j, start.toNat ≤ j → j < n.toNat → j ≠ root.toNat → MaxHeapAt xs n.toNat j) ∧
      (start.toNat < root.toNat →
        let p := (root.toNat - 1) / 2
        (2 * root.toNat + 1 < n.toNat → xs[2 * root.toNat + 1]?.getD 0#64 ≤ xs[p]?.getD 0#64) ∧
        (2 * root.toNat + 2 < n.toNat → xs[2 * root.toNat + 2]?.getD 0#64 ≤ xs[p]?.getD 0#64)) ∧
      (array64 a xs ⋆ R) ml)
    (fun (root, ()) _ => n.toNat - root.toNat)
    (fun J hJ => by
      fc_to_group
      refine hJ (start, ()) m0 ⟨xs0, Nat.le_refl _, hst_le, rfl, fun _ _ _ => rfl,
        fun k hk => ⟨k, hk, rfl⟩, fun j hj1 hj2 hjne => hmh0 j (by omega) hj2,
        fun h => absurd h (Nat.lt_irrefl _), hm0⟩)
    (fun J (root, ()) ml ⟨xs, hsr, hrn, hxl, htail, hsub, hmh_ex, hpar, hml⟩ ih => ?_)
  fc_split_fast
  · have hr_lt : root.toNat < n.toNat := by
      simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
    have hleft_n : (root * 2 + 1).toNat = 2 * root.toNat + 1 := by bv_omega
    fc_split_fast
    · have hc_ge : n.toNat ≤ 2 * root.toNat + 1 := by
        simp only [BitVec.ule, decide_eq_true_eq] at hc; bv_omega
      refine hret_ok xs ml root hxl htail hsub (fun j hj1 hj2 => ?_) hml
      by_cases hjr : j = root.toNat
      · subst hjr; exact ⟨fun h => by omega, fun h => by omega⟩
      · exact hmh_ex j hj1 hj2 hjr
    · have hleft_lt : 2 * root.toNat + 1 < n.toNat := by
        simp only [BitVec.ule, decide_eq_false_iff_not] at hc
        change ¬ (n.toNat ≤ (root * 2 + 1).toNat) at hc; rw [hleft_n] at hc; omega
      have hleft_arr : (root * 2 + 1).toNat < xs.length := by omega
      have hroot_arr : root.toNat < xs.length := by omega
      fc_to_group
      refine wp_join_group (ts := [i64])
        (fun (best, ()) mb => mb = ml ∧
          (best.toNat = root.toNat ∨ best.toNat = 2 * root.toNat + 1) ∧
          xs[root.toNat]?.getD 0#64 ≤ xs[best.toNat]?.getD 0#64 ∧
          xs[2 * root.toNat + 1]?.getD 0#64 ≤ xs[best.toNat]?.getD 0#64)
        (fun _ ⟨best, ⟨⟩⟩ mb ⟨hmb, hbest_eq, hbr, hbl⟩ => ?_)
        (fun Jb hJb => ?_)
      · subst mb
        have hright_n : (root * 2 + 1 + 1).toNat = 2 * root.toNat + 2 := by bv_omega
        have hbest_arr : best.toNat < xs.length := by rcases hbest_eq with h | h <;> omega
        fc_to_group
        refine wp_join_group (ts := [i64])
          (fun (best2, ()) mb2 => mb2 = ml ∧
            (best2.toNat = root.toNat ∨ best2.toNat = 2 * root.toNat + 1 ∨
              best2.toNat = 2 * root.toNat + 2) ∧
            best2.toNat < n.toNat ∧
            xs[root.toNat]?.getD 0#64 ≤ xs[best2.toNat]?.getD 0#64 ∧
            xs[2 * root.toNat + 1]?.getD 0#64 ≤ xs[best2.toNat]?.getD 0#64 ∧
            (2 * root.toNat + 2 < n.toNat →
              xs[2 * root.toNat + 2]?.getD 0#64 ≤ xs[best2.toNat]?.getD 0#64))
          (fun _ ⟨best2, ⟨⟩⟩ mb2 ⟨hmb2, hbest2_eq, hb2n, hb2r, hb2l, hb2ri⟩ => ?_)
          (fun Jb2 hJb2 => ?_)
        · subst mb2
          fc_split_fast
          · have hb2_eq : best2.toNat = root.toNat := congrArg BitVec.toNat (beq_iff_eq.mp hc)
            refine hret_ok xs ml root hxl htail hsub (fun j hj1 hj2 => ?_) hml
            by_cases hjr : j = root.toNat
            · subst hjr; rw [hb2_eq] at hb2l hb2ri; exact ⟨fun _ => hb2l, hb2ri⟩
            · exact hmh_ex j hj1 hj2 hjr
          · have hb2_ne : best2.toNat ≠ root.toNat := by
              intro h; exact (beq_eq_false_iff_ne.mp hc) (BitVec.eq_of_toNat_eq h)
            have hchild_ge : root.toNat < best2.toNat := by
              rcases hbest2_eq with h | h | h <;> omega
            have hbest2_arr : best2.toNat < xs.length := by omega
            fc_steps
            let v_root := xs[root.toNat]'hroot_arr
            let v_best := xs[best2.toNat]'hbest2_arr
            have hv_r_eq : xs[root.toNat]?.getD 0#64 = v_root := by
              rw [List.getElem?_eq_getElem hroot_arr, Option.getD_some]
            have hv_b_eq : xs[best2.toNat]?.getD 0#64 = v_best := by
              rw [List.getElem?_eq_getElem hbest2_arr, Option.getD_some]
            let xs1 := xs.set root.toNat v_best
            let xs2 := xs1.set best2.toNat v_root
            have hxs2_len : xs2.length = xs0.length := by simp [xs2, xs1, hxl]
            have hxs2_tail : ∀ k, n.toNat ≤ k → k < xs2.length → xs2[k]? = xs0[k]? := by
              intro k hk1 hk2
              dsimp [xs2, xs1]
              rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
              exact htail k hk1 (by omega)
            have hxs2_sub : ∀ k < n.toNat, ∃ j < n.toNat, xs2[k]? = xs0[j]? := by
              intro k hk
              by_cases hkb : k = best2.toNat
              · subst hkb; dsimp [xs2, xs1]
                rw [List.getElem?_set_self (by simp; omega)]
                simpa [List.getElem?_eq_getElem hroot_arr] using hsub root.toNat hr_lt
              · by_cases hkr : k = root.toNat
                · subst hkr; dsimp [xs2, xs1]
                  rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega)]
                  simpa [List.getElem?_eq_getElem hbest2_arr] using hsub best2.toNat hb2n
                · dsimp [xs2, xs1]
                  rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
                  exact hsub k hk
            have hxs2_get_root : xs2[root.toNat]? = some v_best := by
              dsimp [xs2, xs1]
              rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega)]
            have hxs2_get_best : xs2[best2.toNat]? = some v_root := by
              dsimp [xs2, xs1]; rw [List.getElem?_set_self (by simp; omega)]
            have hxs2_get_other : ∀ k, k ≠ root.toNat → k ≠ best2.toNat → xs2[k]? = xs[k]? := by
              intro k hk1 hk2; dsimp [xs2, xs1]
              rw [List.getElem?_set_ne (Ne.symm hk2), List.getElem?_set_ne (Ne.symm hk1)]
            refine ih (best2, ()) m (by dsimp only; omega)
              ⟨xs2, by omega, by omega, hxs2_len, hxs2_tail, hxs2_sub, ?_, ?_, hm⟩
            · intro j hj1 hj2 hjne
              by_cases hjr : j = root.toNat
              · subst hjr
                refine ⟨fun h1 => ?_, fun h2 => ?_⟩
                · rw [hxs2_get_root, Option.getD_some]
                  by_cases h1b : 2 * root.toNat + 1 = best2.toNat
                  · rw [h1b, hxs2_get_best, Option.getD_some]
                    simpa [hv_r_eq, hv_b_eq] using hb2r
                  · rw [hxs2_get_other _ (by omega) h1b]
                    simpa [hv_b_eq] using hb2l
                · rw [hxs2_get_root, Option.getD_some]
                  by_cases h2b : 2 * root.toNat + 2 = best2.toNat
                  · rw [h2b, hxs2_get_best, Option.getD_some]
                    simpa [hv_r_eq, hv_b_eq] using hb2r
                  · rw [hxs2_get_other _ (by omega) h2b]
                    simpa [hv_b_eq] using hb2ri h2
              · have hmhj := hmh_ex j hj1 hj2 hjr
                by_cases hjp : j = (best2.toNat - 1) / 2
                · have : j = root.toNat := by rcases hbest2_eq with h | h | h <;> omega
                  exact absurd this hjr
                · have hne1 : 2 * j + 1 ≠ best2.toNat := by
                    rcases hbest2_eq with h | h | h
                    · exact absurd h hb2_ne
                    · omega
                    · omega
                  have hne2 : 2 * j + 2 ≠ best2.toNat := by
                    rcases hbest2_eq with h | h | h
                    · exact absurd h hb2_ne
                    · omega
                    · omega
                  by_cases hjr_p : start.toNat < root.toNat ∧ j = (root.toNat - 1) / 2
                  · obtain ⟨hsr_lt, rfl⟩ := hjr_p
                    have hp_ok := hpar hsr_lt
                    dsimp only [MaxHeapAt]
                    rw [hxs2_get_other _ hjr hjne]
                    refine ⟨fun h1 => ?_, fun h2 => ?_⟩
                    · by_cases h1r : 2 * ((root.toNat - 1) / 2) + 1 = root.toNat
                      · rw [h1r, hxs2_get_root, Option.getD_some]
                        rcases hbest2_eq with h | h | h
                        · exact absurd h hb2_ne
                        · rw [← hv_b_eq, h]; exact hp_ok.1 (by omega)
                        · rw [← hv_b_eq, h]; exact hp_ok.2 (by omega)
                      · rw [hxs2_get_other _ h1r hne1]; exact hmhj.1 h1
                    · by_cases h2r : 2 * ((root.toNat - 1) / 2) + 2 = root.toNat
                      · rw [h2r, hxs2_get_root, Option.getD_some]
                        rcases hbest2_eq with h | h | h
                        · exact absurd h hb2_ne
                        · rw [← hv_b_eq, h]; exact hp_ok.1 (by omega)
                        · rw [← hv_b_eq, h]; exact hp_ok.2 (by omega)
                      · rw [hxs2_get_other _ h2r hne2]; exact hmhj.2 h2
                  · by_cases hj_par : j = (root.toNat - 1) / 2
                    · have hle : ¬ start.toNat < root.toNat := fun hs => hjr_p ⟨hs, hj_par⟩
                      omega
                    · have : 2 * j + 1 ≠ root.toNat ∧ 2 * j + 2 ≠ root.toNat := by omega
                      dsimp only [MaxHeapAt]
                      rw [hxs2_get_other _ hjr hjne]
                      refine ⟨fun h1 => ?_, fun h2 => ?_⟩
                      · rw [hxs2_get_other _ this.1 hne1]; exact hmhj.1 h1
                      · rw [hxs2_get_other _ this.2 hne2]; exact hmhj.2 h2
            · intro _; refine ⟨fun hc1 => ?_, fun hc2 => ?_⟩
              · have hp_eq : (best2.toNat - 1) / 2 = root.toNat := by
                  rcases hbest2_eq with h | h | h <;> omega
                rw [hp_eq, hxs2_get_root, Option.getD_some]
                have hmb := hmh_ex best2.toNat (by omega) hb2n hb2_ne
                have hne1 : 2 * best2.toNat + 1 ≠ root.toNat := by omega
                have hne2 : 2 * best2.toNat + 1 ≠ best2.toNat := by omega
                rw [hxs2_get_other _ hne1 hne2]
                simpa [hv_b_eq] using hmb.1 hc1
              · have hp_eq : (best2.toNat - 1) / 2 = root.toNat := by
                  rcases hbest2_eq with h | h | h <;> omega
                rw [hp_eq, hxs2_get_root, Option.getD_some]
                have hmb := hmh_ex best2.toNat (by omega) hb2n hb2_ne
                have hne1 : 2 * best2.toNat + 2 ≠ root.toNat := by omega
                have hne2 : 2 * best2.toNat + 2 ≠ best2.toNat := by omega
                rw [hxs2_get_other _ hne1 hne2]
                simpa [hv_b_eq] using hmb.2 hc2
        · fc_split_fast
          · have hri_lt : 2 * root.toNat + 2 < n.toNat := by
              rw [← hright_n]; simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
            have hri_arr : (root * 2 + 1 + 1).toNat < xs.length := by omega
            fc_split_fast
            · have hult_b : xs[best.toNat]?.getD 0#64 < xs[2 * root.toNat + 2]?.getD 0#64 := by
                rw [List.getElem?_eq_getElem hbest_arr,
                  List.getElem?_eq_getElem (by rw [← hright_n]; exact hri_arr),
                  Option.getD_some, Option.getD_some]
                simp only [BitVec.ult, decide_eq_true_eq, hright_n] at hc
                exact BitVec.lt_def.mpr hc
              exact hJb2 (root * 2 + 1 + 1, ()) ml
                ⟨rfl, Or.inr (Or.inr hright_n), by omega,
                 BitVec.le_trans hbr (BitVec.le_of_lt (by rw [hright_n]; exact hult_b)),
                 BitVec.le_trans hbl (BitVec.le_of_lt (by rw [hright_n]; exact hult_b)),
                 fun _ => by rw [hright_n]; exact BitVec.le_refl _⟩
            · have hle_ri : xs[2 * root.toNat + 2]?.getD 0#64 ≤ xs[best.toNat]?.getD 0#64 := by
                rw [List.getElem?_eq_getElem hbest_arr,
                  List.getElem?_eq_getElem (by rw [← hright_n]; exact hri_arr),
                  Option.getD_some, Option.getD_some]
                simp only [BitVec.ult, decide_eq_false_iff_not, not_lt, hright_n] at hc
                exact BitVec.le_def.mpr hc
              exact hJb2 (best, ()) ml
                ⟨rfl, by rcases hbest_eq with h | h; exact Or.inl h; exact Or.inr (Or.inl h),
                 by rcases hbest_eq with h | h <;> omega, hbr, hbl, fun _ => hle_ri⟩
          · have hno_ri : ¬ 2 * root.toNat + 2 < n.toNat := by
              rw [← hright_n]; simp only [BitVec.ult, decide_eq_false_iff_not] at hc; exact hc
            exact hJb2 (best, ()) ml
              ⟨rfl, by rcases hbest_eq with h | h; exact Or.inl h; exact Or.inr (Or.inl h),
               by rcases hbest_eq with h | h <;> omega, hbr, hbl, fun h => absurd h hno_ri⟩
      · fc_split_fast
        · have hult_l : xs[root.toNat]?.getD 0#64 < xs[2 * root.toNat + 1]?.getD 0#64 := by
            rw [List.getElem?_eq_getElem hroot_arr,
              List.getElem?_eq_getElem (by rw [← hleft_n]; exact hleft_arr),
              Option.getD_some, Option.getD_some]
            simp only [BitVec.ult, decide_eq_true_eq, hleft_n] at hc
            exact BitVec.lt_def.mpr hc
          exact hJb (root * 2 + 1, ()) ml
            ⟨rfl, Or.inr hleft_n, by rw [hleft_n]; exact BitVec.le_of_lt hult_l,
             by rw [hleft_n]; exact BitVec.le_refl _⟩
        · have hle_l : xs[2 * root.toNat + 1]?.getD 0#64 ≤ xs[root.toNat]?.getD 0#64 := by
            rw [List.getElem?_eq_getElem hroot_arr,
              List.getElem?_eq_getElem (by rw [← hleft_n]; exact hleft_arr),
              Option.getD_some, Option.getD_some]
            simp only [BitVec.ult, decide_eq_false_iff_not, not_lt, hleft_n] at hc
            exact BitVec.le_def.mpr hc
          exact hJb (root, ()) ml
            ⟨rfl, Or.inl rfl, BitVec.le_refl _, hle_l⟩
  · have hr_ge : root.toNat ≥ n.toNat := by
      simp only [BitVec.ult, decide_eq_false_iff_not] at hc; omega
    have hre : root.toNat = n.toNat := by omega
    refine hret_ok xs ml root hxl htail hsub (fun j hj1 hj2 => ?_) hml
    exact hmh_ex j hj1 hj2 (by omega)

theorem bv64_ushiftRight1_toNat (x : BitVec 64) :
    (x >>> (1 : Nat)).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem bv64_shl1_toNat (x : BitVec 64) :
    (x <<< (1 : Nat)).toNat = (2 * x.toNat) % 2 ^ 64 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]

theorem full_cong_u64_sort_m7_wp (Γ : Env)
    (hSift : ∀ a m Q X, m7U64SiftSpec a m Q X →
      Γ "full_cong_u64_sift_m7" [i64, i64, i64] [] a m Q X) :
    ∀ args m Q X, m7U64SortSpec args m Q X →
      Func.wp Γ full_cong_u64_sort_m7_body args m Q X := by
  rintro ⟨a, n, ⟨⟩⟩ m0 Q X ⟨xs0, R, hn_le, hlen_bd, hm0, hQ⟩
  fc_split_fast
  · have hn1 : n.toNat ≤ 1 := by
      simp only [BitVec.ule, decide_eq_true_eq] at hc; exact hc
    fc_steps
    refine hQ xs0 m0 rfl (fun k _ _ => rfl) (fun k hk => ⟨k, hk, rfl⟩) ?_ hm0
    intro i j hi hij hj
    have : i = j := by omega
    subst this; exact BitVec.le_refl _
  · have hn_gt1 : 1 < n.toNat := by
      simp only [BitVec.ule, decide_eq_false_iff_not, not_le] at hc; exact hc
    fc_to_group
    refine wp_loop_inv (ts := [i64])
      (fun (i, ()) ml => ∃ xs : List (BitVec 64),
        i.toNat ≤ n.toNat / 2 ∧ xs.length = xs0.length ∧
        (∀ k, n.toNat ≤ k → k < xs.length → xs[k]? = xs0[k]?) ∧
        (∀ k < n.toNat, ∃ j < n.toNat, xs[k]? = xs0[j]?) ∧
        MaxHeapRange xs i.toNat n.toNat ∧ (array64 a xs ⋆ R) ml)
      (fun (i, ()) _ => i.toNat)
      (fun J1 hJ1 => by
        fc_steps
        refine hJ1 (n >>> (1 : Nat), ()) m0 ⟨xs0, ?_, rfl, fun _ _ _ => rfl,
          fun k hk => ⟨k, hk, rfl⟩, fun j hj1 hj2 => ?_, hm0⟩
        · rw [bv64_ushiftRight1_toNat]; exact Nat.le_refl _
        · rw [bv64_ushiftRight1_toNat] at hj1
          exact ⟨fun h => by omega, fun h => by omega⟩)
      (fun J1 ⟨i, ⟨⟩⟩ ml ⟨xs, hi_le, hxl, htail, hsub, hmh, hml⟩ ih1 => ?_)
    fc_split_fast
    · have hi_pos : 0 < i.toNat := by
        simp only [BitVec.ult, decide_eq_true_eq] at hc; bv_omega
      have hip_n : (i - 1#64).toNat = i.toNat - 1 := by bv_omega
      fc_steps
      refine wp_call_of_spec _ _ (hSift (a, i - 1#64, n, ()) ml _ X
        ⟨xs, R, by omega, by omega, by omega, ?_, hml, fun xs' m' hxl' htail' hsub' hmh' hm' => ?_⟩)
      · simpa [hip_n, Nat.sub_add_cancel hi_pos] using hmh
      · fc_steps
        refine ih1 (i - 1#64, ()) m' (by dsimp only; omega)
          ⟨xs', by omega, by omega, fun k hk1 hk2 => ?_, fun k hk => ?_, hmh', hm'⟩
        · rw [htail' k hk1 (by omega), htail k hk1 (by omega)]
        · obtain ⟨j, hj, hget⟩ := hsub' k hk
          obtain ⟨j0, hj0, hget0⟩ := hsub j hj
          exact ⟨j0, hj0, hget.trans hget0⟩
    · have hi0 : i.toNat = 0 := by
        simp only [BitVec.ult, decide_eq_false_iff_not, not_lt] at hc; bv_omega
      have hmh0 : MaxHeapRange xs 0 n.toNat := hi0 ▸ hmh
      fc_to_group
      refine wp_loop_inv (ts := [i64])
        (fun (k, ()) mk => ∃ xs' : List (BitVec 64),
          k.toNat < n.toNat ∧ xs'.length = xs0.length ∧
          (∀ p, n.toNat ≤ p → p < xs'.length → xs'[p]? = xs0[p]?) ∧
          (∀ p < n.toNat, ∃ j < n.toNat, xs'[p]? = xs0[j]?) ∧
          MaxHeapRange xs' 0 (k.toNat + 1) ∧
          SortedRange64 xs' (k.toNat + 1) n.toNat ∧
          (∀ x y, x ≤ k.toNat → k.toNat < y → y < n.toNat →
            xs'[x]?.getD 0#64 ≤ xs'[y]?.getD 0#64) ∧
          (array64 a xs' ⋆ R) mk)
        (fun (k, ()) _ => k.toNat)
        (fun J2 hJ2 => by
          fc_steps
          have hnm1 : (n - 1#64).toNat = n.toNat - 1 := by bv_omega
          refine hJ2 (n - 1#64, ()) ml ⟨xs, by omega, hxl, htail, hsub, ?_, ?_, ?_, hml⟩
          · rw [hnm1, Nat.sub_add_cancel (by omega)]; exact hmh0
          · intro p q hp hpq hq; rw [hnm1, Nat.sub_add_cancel (by omega)] at hp; omega
          · intro x y _ hy1 hy2; rw [hnm1] at hy1; omega)
        (fun J2 ⟨k, ⟨⟩⟩ mk ⟨xs', hk_lt, hxl', htail', hsub', hmh', hsort', hpart', hmk⟩ ih2 => ?_)
      fc_split_fast
      · have hk_pos : 0 < k.toNat := by
          simp only [BitVec.ult, decide_eq_true_eq] at hc; bv_omega
        have hk_arr : k.toNat < xs'.length := by omega
        have h0_arr : 0 < xs'.length := by omega
        have hkp_n : (k - 1#64).toNat = k.toNat - 1 := by bv_omega
        fc_steps
        let v_k := xs'[k.toNat]'hk_arr
        let v_0 := xs'[0]'h0_arr
        let xs1 := (xs'.set k.toNat v_0).set 0 v_k
        have hxs1_len : xs1.length = xs0.length := by simp [xs1, hxl']
        have hxs1_tail : ∀ p, n.toNat ≤ p → p < xs1.length → xs1[p]? = xs0[p]? := by
          intro p hp1 hp2; dsimp [xs1]
          rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
          exact htail' p hp1 (by omega)
        have hxs1_sub : ∀ p < n.toNat, ∃ j < n.toNat, xs1[p]? = xs0[j]? := by
          intro p hp
          by_cases hp0 : p = 0
          · subst hp0; dsimp [xs1]; rw [List.getElem?_set_self (by simp; omega)]
            simpa [List.getElem?_eq_getElem hk_arr] using hsub' k.toNat hk_lt
          · by_cases hpk : p = k.toNat
            · subst hpk; dsimp [xs1]
              rw [List.getElem?_set_ne (Ne.symm hp0), List.getElem?_set_self (by omega)]
              simpa [List.getElem?_eq_getElem h0_arr] using hsub' 0 (by omega)
            · dsimp [xs1]
              rw [List.getElem?_set_ne (Ne.symm hp0), List.getElem?_set_ne (Ne.symm hpk)]
              exact hsub' p hp
        have hxs1_0 : xs1[0]? = some v_k := by
          dsimp [xs1]; rw [List.getElem?_set_self (by simp; omega)]
        have hxs1_k : xs1[k.toNat]? = some v_0 := by
          dsimp [xs1]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega)]
        have hxs1_other : ∀ p, p ≠ 0 → p ≠ k.toNat → xs1[p]? = xs'[p]? := by
          intro p hp0 hpk; dsimp [xs1]
          rw [List.getElem?_set_ne (Ne.symm hp0), List.getElem?_set_ne (Ne.symm hpk)]
        have hmh1 : MaxHeapRange xs1 1 k.toNat := by
          intro j hj1 hj2; dsimp only [MaxHeapAt]
          have hmj := hmh' j (by omega) (by omega)
          dsimp only [MaxHeapAt] at hmj
          rw [hxs1_other j (by omega) (by omega)]
          refine ⟨fun h1 => ?_, fun h2 => ?_⟩
          · rw [hxs1_other _ (by omega) (by omega)]; exact hmj.1 (by omega)
          · rw [hxs1_other _ (by omega) (by omega)]; exact hmj.2 (by omega)
        have hmax0 : ∀ j < k.toNat + 1, xs'[j]?.getD 0#64 ≤ v_0 := by
          intro j hj
          have hm0' := maxHeap_le_root hmh' j hj
          rwa [List.getElem?_eq_getElem h0_arr, Option.getD_some] at hm0'
        refine wp_call_of_spec _ _ (hSift (a, 0#64, k, ()) m _ X
          ⟨xs1, R, by bv_omega, by omega, by omega, hmh1, hm,
            fun xs2 m2 hxl2 htail2 hsub2 hmh2 hm2 => ?_⟩)
        fc_steps
        have hxs2_k : xs2[k.toNat]? = some v_0 := by
          rw [htail2 k.toNat (Nat.le_refl _) (by omega), hxs1_k]
        have hxs2_tail_n : ∀ p, n.toNat ≤ p → p < xs2.length → xs2[p]? = xs0[p]? := by
          intro p hp1 hp2
          rw [htail2 p (by omega) (by omega), hxs1_tail p hp1 (by omega)]
        have hxs2_sub_n : ∀ p < n.toNat, ∃ j < n.toNat, xs2[p]? = xs0[j]? := by
          intro p hp
          by_cases hpk : p < k.toNat
          · obtain ⟨j, hj, hget⟩ := hsub2 p hpk
            obtain ⟨j0, hj0, hget0⟩ := hxs1_sub j (by omega)
            exact ⟨j0, hj0, hget.trans hget0⟩
          · rw [htail2 p (by omega) (by omega)]
            exact hxs1_sub p hp
        have hxs2_le_v0 : ∀ p ≤ k.toNat, xs2[p]?.getD 0#64 ≤ v_0 := by
          intro p hp
          by_cases hpk : p = k.toNat
          · subst hpk; rw [hxs2_k, Option.getD_some]; exact BitVec.le_refl _
          · obtain ⟨j, hj, hget⟩ := hsub2 p (by omega)
            rw [hget]
            by_cases hj0 : j = 0
            · subst hj0; rw [hxs1_0, Option.getD_some]
              simpa [v_k, List.getElem?_eq_getElem hk_arr, Option.getD_some] using hmax0 k.toNat
                (by omega)
            · rw [hxs1_other j hj0 (by omega)]; exact hmax0 j (by omega)
        have hxs2_ge_k : ∀ q, k.toNat ≤ q → q < n.toNat → v_0 ≤ xs2[q]?.getD 0#64 := by
          intro q hq1 hq2
          by_cases hqk : q = k.toNat
          · subst hqk; rw [hxs2_k, Option.getD_some]; exact BitVec.le_refl _
          · rw [htail2 q (by omega) (by omega), hxs1_other q (by omega) (by omega)]
            have hp0 := hpart' 0 q (Nat.zero_le _) (by omega) hq2
            rwa [List.getElem?_eq_getElem h0_arr, Option.getD_some] at hp0
        refine ih2 (k - 1#64, ()) m2 (by dsimp only; omega)
          ⟨xs2, by omega, by omega, hxs2_tail_n, hxs2_sub_n, ?_, ?_, ?_, hm2⟩
        · rwa [hkp_n, Nat.sub_add_cancel hk_pos]
        · intro x y hx hxy hy; rw [hkp_n, Nat.sub_add_cancel hk_pos] at hx
          by_cases hxk : x = k.toNat
          · subst hxk; rw [hxs2_k, Option.getD_some]; exact hxs2_ge_k y hxy hy
          · rw [htail2 x (by omega) (by omega), htail2 y (by omega) (by omega),
              hxs1_other x (by omega) (by omega), hxs1_other y (by omega) (by omega)]
            exact hsort' x y (by omega) hxy hy
        · intro x y hx hy1 hy2; rw [hkp_n] at hx hy1
          exact BitVec.le_trans (hxs2_le_v0 x (by omega)) (hxs2_ge_k y (by omega) hy2)
      · have hk0 : k.toNat = 0 := by
          simp only [BitVec.ult, decide_eq_false_iff_not, not_lt] at hc; bv_omega
        fc_steps
        refine hQ xs' mk hxl' (fun p hp1 hp2 => htail' p hp1 (by omega)) hsub'
          (fun x y hx hxy hy => ?_) hmk
        rcases Nat.eq_zero_or_pos x with rfl | hx_pos
        · rcases Nat.eq_zero_or_pos y with rfl | hy_pos
          · exact BitVec.le_refl _
          · exact hpart' 0 y (Nat.zero_le _) (by omega) hy
        · exact hsort' x y (by omega) hxy hy

theorem full_cong_bsearch_u64_m7_wp (Γ : Env) :
    ∀ args m Q X, m7BsearchU64Spec args m Q X →
      Func.wp Γ full_cong_bsearch_u64_m7_body args m Q X := by
  rintro ⟨a, lo, hi, key, ⟨⟩⟩ m0 Q X ⟨xs, R, hlh0, hhi0, hlen_bd, hsort, hm0, hQ⟩
  fc_to_group
  refine wp_loop_inv (ts := [i64, i64])
    (fun (lo_v, hi_v, ()) ml => ml = m0 ∧
      lo.toNat ≤ lo_v.toNat ∧ lo_v.toNat ≤ hi_v.toNat ∧ hi_v.toNat ≤ hi.toNat ∧
      ((∃ idx, lo.toNat ≤ idx ∧ idx < hi.toNat ∧ xs[idx]? = some key) ↔
        (∃ idx, lo_v.toNat ≤ idx ∧ idx < hi_v.toNat ∧ xs[idx]? = some key)))
    (fun (lo_v, hi_v, ()) _ => hi_v.toNat - lo_v.toNat)
    (fun J hJ => by
      fc_steps; exact hJ (lo, hi, ()) m0 ⟨rfl, Nat.le_refl _, hlh0, Nat.le_refl _, Iff.rfl⟩)
    (fun J ⟨lo_v, hi_v, ⟨⟩⟩ ml ⟨hml, hlo_l, hlo_h, hhi_h, heqv⟩ ih => ?_)
  subst ml
  fc_split_fast
  · have hlt : lo_v.toNat < hi_v.toNat := by
      simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
    let mid := lo_v + ((hi_v - lo_v) >>> (1 : Nat))
    have hdiff : (hi_v - lo_v).toNat = hi_v.toNat - lo_v.toNat := by bv_omega
    have hshr : ((hi_v - lo_v) >>> (1 : Nat)).toNat = (hi_v.toNat - lo_v.toNat) / 2 := by
      rw [bv64_ushiftRight1_toNat, hdiff]
    have hmid_n : mid.toNat = lo_v.toNat + (hi_v.toNat - lo_v.toNat) / 2 := by
      rw [show mid = lo_v + ((hi_v - lo_v) >>> (1 : Nat)) from rfl,
        BitVec.toNat_add, hshr, Nat.mod_eq_of_lt]; omega
    have hmid_lo : lo_v.toNat ≤ mid.toNat := by omega
    have hmid_lt : mid.toNat < hi_v.toNat := by omega
    have hmid_arr : mid.toNat < xs.length := by omega
    fc_steps
    fc_split_fast
    · have hval_eq : xs[mid.toNat]'hmid_arr = key := hc
      fc_steps
      refine hQ true ⟨fun _ => heqv.mpr ⟨mid.toNat, hmid_lo, hmid_lt, ?_⟩, fun _ => rfl⟩
      rw [List.getElem?_eq_getElem hmid_arr, hval_eq]
    · have hval_lt : xs[mid.toNat]'hmid_arr < key := BitVec.lt_def.mpr hc
      have hmp1_n : (mid + 1#64).toNat = mid.toNat + 1 := by bv_omega
      refine ih (mid + 1#64, hi_v, ()) m0 (by dsimp only; omega)
        ⟨rfl, by omega, by omega, hhi_h, ?_⟩
      rw [heqv]
      refine ⟨fun ⟨idx, h1, h2, hget⟩ => ?_, fun ⟨idx, h1, h2, hget⟩ => ⟨idx, by omega, h2, hget⟩⟩
      refine ⟨idx, ?_, h2, hget⟩
      exact Classical.byContradiction fun hle => by
        have hidx_le : idx ≤ mid.toNat := by omega
        have hs := hsort idx mid.toNat (by omega) hidx_le (by omega)
        rw [hget, List.getElem?_eq_getElem hmid_arr, Option.getD_some, Option.getD_some] at hs
        exact absurd hs (not_le_of_gt hval_lt)
    · have hval_ne : xs[mid.toNat]'hmid_arr ≠ key := ‹_›
      have hkey_lt : key < xs[mid.toNat]'hmid_arr := BitVec.lt_def.mpr
        (Nat.lt_of_le_of_ne (Nat.le_of_not_lt hc) fun h =>
          hval_ne (BitVec.eq_of_toNat_eq h.symm))
      refine ih (lo_v, mid, ()) m0 (by dsimp only; omega)
        ⟨rfl, hlo_l, hmid_lo, by omega, ?_⟩
      rw [heqv]
      refine ⟨fun ⟨idx, h1, h2, hget⟩ => ?_, fun ⟨idx, h1, h2, hget⟩ => ⟨idx, h1, by omega, hget⟩⟩
      refine ⟨idx, h1, ?_, hget⟩
      exact Classical.byContradiction fun hge => by
        have hidx_ge : mid.toNat ≤ idx := by omega
        have hs := hsort mid.toNat idx (by omega) hidx_ge (by omega)
        rw [hget, List.getElem?_eq_getElem hmid_arr, Option.getD_some, Option.getD_some] at hs
        exact absurd hs (not_le_of_gt hkey_lt)
  · have hge : hi_v.toNat ≤ lo_v.toNat := by
      simp only [BitVec.ult, decide_eq_false_iff_not, not_lt] at hc; exact hc
    fc_steps
    refine hQ false ⟨(fun h => by cases h), fun h => ?_⟩
    rw [heqv] at h
    obtain ⟨idx, h1, h2, _⟩ := h
    omega

theorem bv32_ushiftRight1_toNat (x : BitVec 32) :
    (x >>> (1 : Nat)).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem bv32_ushiftRight_imm1_toNat (x : BitVec 32) :
    (x >>> (1#32 : BitVec 32).toNat).toNat = x.toNat / 2 :=
  bv32_ushiftRight1_toNat x

theorem packU64_eq_lt_rhs {a b : BitVec 32} (hlt : b.ult a = true) :
    ((b.setWidth 64 <<< (32 : Nat)) ||| a.setWidth 64) =
      ((if b.ult a then b else a).setWidth 64 <<< 32#64) |||
        (if b.ult a then a else b).setWidth 64 := by
  simp [hlt]

theorem packU64_eq_ge_rhs {a b : BitVec 32} (hle : b.ult a = false) :
    ((a.setWidth 64 <<< (32 : Nat)) ||| b.setWidth 64) =
      ((if b.ult a then b else a).setWidth 64 <<< 32#64) |||
        (if b.ult a then a else b).setWidth 64 := by
  simp [hle]

theorem dense_slice_pop_step {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p rem : Nat} (h : DenseWatchSliceOk F_cur k lit p rem) (hpos : 0 < rem) :
    ∃ w0 : BitVec 32, k.wstk[p]? = some w0 ∧
      ((w0 &&& 0x80000000#32 ≠ 0#32 ∧ DenseWatchSliceOk F_cur k lit (p + 1) (rem - 1)) ∨
       (w0 &&& 0x80000000#32 = 0#32 ∧ 1 < rem ∧ ∃ cr : BitVec 32,
         k.wstk[p + 1]? = some cr ∧ cr.toNat ∈ fullArenaClauseRefsCore k ∧
         DenseWatchSliceOk F_cur k lit (p + 2) (rem - 2))) := by
  cases h with
  | empty => cases hpos
  | bin hw0 hfl _ _ _ hrest =>
    exact ⟨_, hw0, Or.inl ⟨hfl, by simpa using hrest⟩⟩
  | occ hw0 hcr hfl _ _ href hrest =>
    exact ⟨_, hw0, Or.inr ⟨hfl, by omega, _, hcr, href, by simpa using hrest⟩⟩

private theorem m7_wp_add_vi {rs : List Ty} {Γ : Env} {Q : Post rs} {X : XPost} {m : Mem 64}
    (a n : BitVec 64) (k : Tup Val [i64] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (.mk (.add i64) (.var a, .imm n, ())) k) m =
      wp Γ Q X (k (a + n, ())) m := by
  rw [wp_let_add_eq]; simp [Ty.hasFloat, lift2]

private theorem m7_wp_add_vv {rs : List Ty} {Γ : Env} {Q : Post rs} {X : XPost} {m : Mem 64}
    (a b : BitVec 64) (k : Tup Val [i64] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (.mk (.add i64) (.var a, .var b, ())) k) m =
      wp Γ Q X (k (a + b, ())) m := by
  rw [wp_let_add_eq]; simp [Ty.hasFloat, lift2]

private theorem m7_wp_mul_vi {rs : List Ty} {Γ : Env} {Q : Post rs} {X : XPost} {m : Mem 64}
    (a n : BitVec 64) (k : Tup Val [i64] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (.mk (.mul i64) (.var a, .imm n, ())) k) m =
      wp Γ Q X (k (a * n, ())) m := by
  rw [wp_let_mul_eq]; simp [Ty.hasFloat, lift2]

private theorem m7_wp_shl1_v {rs : List Ty} {Γ : Env} {Q : Post rs} {X : XPost} {m : Mem 64}
    (a : BitVec 64) (k : Tup Val [i64] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (.mk (.shl i64) (.var a, .imm 1, ())) k) m =
      wp Γ Q X (k (a <<< (1 : Nat), ())) m := by
  rw [wp_let_shl_eq]; simp [Ty.hasFloat, lift2]

private theorem m7_wp_zext_v {rs : List Ty} {Γ : Env} {Q : Post rs} {X : XPost} {m : Mem 64}
    (a : BitVec 32) (k : Tup Val [i64] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (.mk (.zext 32 64) (.var a, ())) k) m =
      wp Γ Q X (k (a.setWidth 64, ())) m := by
  rw [wp_let_zext_eq]; simp

theorem full_cong_copy_condbin_m7_wp (Γ : Env)
    (hSort : ∀ a m Q X, m7U64SortSpec a m Q X →
      Γ "full_cong_u64_sort_m7" [i64, i64] [] a m Q X) :
    ∀ args m Q X, m7CopyCondbinSpec args m Q X →
      Func.wp Γ full_cong_copy_condbin_m7_body args m Q X := by
  rintro ⟨h, lit, out, cap, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s, out0, R, rfl, hlen, hw, hdm, hlit_lt, hout_len, hcap_bd, hm0, hQ⟩
  have hmx := c.hmaxv; have hwc := c.hwcap; have hac := c.harena
  unfold dimacsBound at hmx hwc hac
  have hcl := hlen.core_ok
  have hcv_le := hcl.cur_vars_le; have hwvl := hcl.wvec_len
  have hwsl := hcl.wstk_len_arr; have hwle := hcl.wlen_le
  have harl := hcl.arena_len_arr; have hale := hcl.arena_len_le
  have hvl := hcl.vals_len
  have hw_bd := hw.watches.bounds lit.toNat hlit_lt
  have hshl : (lit.setWidth 64 <<< (1 : Nat)).toNat = 2 * lit.toNat := by
    rw [bv64_shl1_toNat, bv_zext32_toNat]; omega
  have hshl1 : (lit.setWidth 64 <<< (1 : Nat) + 1#64).toNat = 2 * lit.toNat + 1 := by
    rw [BitVec.toNat_add, hshl]; show (2 * lit.toNat + 1) % 2 ^ 64 = 2 * lit.toNat + 1; omega
  have hw0_arr : (lit.setWidth 64 <<< (1 : Nat)).toNat < s.core.wvec.length := by omega
  have hw1_arr : (lit.setWidth 64 <<< (1 : Nat) + 1#64).toNat < s.core.wvec.length := by omega
  have hslice0 : DenseWatchSliceOk F_cur s.core lit.toNat (fullWatchOffCore s.core lit.toNat)
      (fullWatchSizeCore s.core lit.toNat) := by
    have hwat := hw.watches; unfold ModeWatchesInv at hwat
    rw [ite_eq_right hdm] at hwat
    exact hwat.slices lit.toNat hlit_lt
  have hm0' : (FullMemNoWks3 c s ⋆ (array64 out out0 ⋆ R)) m0 := sep_ac hm0
  unfold Func.wp full_cong_copy_condbin_m7_body
  dsimp only
  rw [m7_wp_add_vi]; dsimp only; refine wp_load_of (load_noWks3_wvec_ptr hm0') ?_
  rw [m7_wp_add_vi]; dsimp only; refine wp_load_of (load_noWks3_wstk_ptr hm0') ?_
  rw [m7_wp_add_vi]; dsimp only; refine wp_load_of (load_noWks3_arena_ptr hm0') ?_
  rw [m7_wp_add_vi]; dsimp only; refine wp_load_of (load_noWks3_vals_ptr hm0') ?_
  rw [m7_wp_add_vi]; dsimp only; refine wp_load_of (load_noWks3_arena_len hm0') ?_
  rw [m7_wp_zext_v]; dsimp only; rw [m7_wp_shl1_v]; dsimp only
  rw [m7_wp_mul_vi]; dsimp only; rw [m7_wp_add_vv]; dsimp only
  refine wp_load_of (c0_load_noWks3_wvec hw0_arr hm0') ?_
  rw [m7_wp_zext_v]; dsimp only; rw [m7_wp_add_vi]; dsimp only
  rw [m7_wp_mul_vi]; dsimp only; rw [m7_wp_add_vv]; dsimp only
  refine wp_load_of (c0_load_noWks3_wvec hw1_arr hm0') ?_
  rw [m7_wp_zext_v]; dsimp only; rw [m7_wp_add_vv]; dsimp only
  generalize hoff_v :
    (s.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'hw0_arr).setWidth 64 = off
  generalize hwsz_v :
    (s.core.wvec[(lit.setWidth 64 <<< (1 : Nat) + 1#64).toNat]'hw1_arr).setWidth 64 = wsz
  have hoff_n : off.toNat = fullWatchOffCore s.core lit.toNat := by
    rw [← hoff_v, bv_zext32_toNat]; unfold fullWatchOffCore
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact congrArg BitVec.toNat (list_getElem_congr hshl hw0_arr (by omega))
  have hwsz_n : wsz.toNat = fullWatchSizeCore s.core lit.toNat := by
    rw [← hwsz_v, bv_zext32_toNat]; unfold fullWatchSizeCore
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact congrArg BitVec.toNat (list_getElem_congr hshl1 hw1_arr (by omega))
  have hend_n : (off + wsz).toNat = off.toNat + wsz.toNat := by bv_omega
  refine wp_join_group (ts := [i64, i64])
    (fun (_p, cnt, ()) ml => ∃ out1 : List (BitVec 64),
      out1.length = cap.toNat ∧ cnt.toNat ≤ cap.toNat ∧
      (∀ k < cnt.toNat,
        CondBinElemOk F_cur s.core.cur_vars lit.toNat (out1[k]?.getD 0#64)) ∧
      (FullMemNoWks3 c s ⋆ array64 out out1 ⋆ R) ml)
    (fun _ ⟨_p, cnt, ⟨⟩⟩ ml ⟨out1, hout1_len, hcnt_le, hcb1, hml⟩ => ?_)
    (fun J0 hJ0 => ?_)
  · -- Post watch-scan: if cnt ≤ 1 return cnt; else sort & dedup
    fc_split_fast
    · have hcnt1 : cnt.toNat ≤ 1 := by
        simp only [BitVec.ule, decide_eq_true_eq] at hc; exact hc
      fc_steps
      refine hQ cnt out1 ml hout1_len hcnt_le (fun i j hi hij hj => ?_) hcb1 hml
      have : i = j := by omega
      subst this; exact BitVec.le_refl _
    · have hcnt_gt1 : 1 < cnt.toNat := by
        simp only [BitVec.ule, decide_eq_false_iff_not, not_le] at hc; exact hc
      have hm_s0 : (array64 out out1 ⋆ (FullMemNoWks3 c s ⋆ R)) ml := sep_ac hml
      refine wp_call_of_spec _ _ (hSort (out, cnt, ()) ml _ X
        ⟨out1, FullMemNoWks3 c s ⋆ R, by omega, by omega, hm_s0,
          fun out_s m_s hos_len hos_tail hos_sub hos_sort hm_s => ?_⟩)
      have hos_cb : ∀ k < cnt.toNat,
          CondBinElemOk F_cur s.core.cur_vars lit.toNat (out_s[k]?.getD 0#64) := by
        intro k hk
        obtain ⟨j, hj, hget⟩ := hos_sub k hk
        have hok := hcb1 j hj
        rwa [← hget] at hok
      fc_to_group
      refine wp_loop_inv (ts := [i64, i64])
        (fun (u, i, ()) md => ∃ out_d : List (BitVec 64),
          1 ≤ u.toNat ∧ u.toNat ≤ i.toNat ∧ i.toNat ≤ cnt.toNat ∧
          out_d.length = cap.toNat ∧
          (∀ k, i.toNat ≤ k → k < cnt.toNat → out_d[k]? = out_s[k]?) ∧
          (∀ k < u.toNat, ∃ j < i.toNat, out_d[k]? = out_s[j]?) ∧
          SortedRange64 out_d 0 u.toNat ∧
          (array64 out out_d ⋆ (FullMemNoWks3 c s ⋆ R)) md)
        (fun (_, i, ()) _ => cnt.toNat - i.toNat)
        (fun Jd hJd => by
          fc_steps
          refine hJd (1#64, 1#64, ()) m_s ⟨out_s, Nat.le_refl _, by bv_omega, by bv_omega,
            by omega, fun _ _ _ => rfl, fun k hk => ⟨k, hk, rfl⟩,
            fun i j hi hij hj => by
              have : i = j := (by bv_omega)
              subst this; exact BitVec.le_refl _,
            hm_s⟩)
        (fun Jd ⟨u, i, ⟨⟩⟩ md ⟨out_d, hu1, hui, hic, hod_len, htail_d, hsub_d, hsort_d, hmd⟩ ihd =>
          ?_)
      fc_split_fast
      · have hi_lt : i.toNat < cnt.toNat := by
          simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
        have hum1_n : (u - 1#64).toNat = u.toNat - 1 := by bv_omega
        have hi_arr : i.toNat < out_d.length := by omega
        have hum1_arr : (u - 1#64).toNat < out_d.length := by omega
        have hu_arr : u.toNat < out_d.length := by omega
        have hip1_n : (i + 1#64).toNat = i.toNat + 1 := by bv_omega
        fc_to_group
        refine wp_join_group (ts := [i64])
          (fun (u2, ()) md2 => ∃ out_d2 : List (BitVec 64),
            1 ≤ u2.toNat ∧ u2.toNat ≤ i.toNat + 1 ∧ out_d2.length = cap.toNat ∧
            (∀ k, i.toNat + 1 ≤ k → k < cnt.toNat → out_d2[k]? = out_s[k]?) ∧
            (∀ k < u2.toNat, ∃ j < i.toNat + 1, out_d2[k]? = out_s[j]?) ∧
            SortedRange64 out_d2 0 u2.toNat ∧
            (array64 out out_d2 ⋆ (FullMemNoWks3 c s ⋆ R)) md2)
          (fun _ ⟨u2, ⟨⟩⟩ md2 ⟨out_d2, hu2_1, hu2_le, hod2_len, ht2, hs2, hso2, hmd2⟩ => by
            fc_steps
            exact ihd (u2, i + 1#64, ()) md2 (by dsimp only; omega)
              ⟨out_d2, hu2_1, by omega, by omega, hod2_len, fun k hk1 hk2 => ht2 k (by omega) hk2,
                fun k hk => by obtain ⟨j, hj, hg⟩ := hs2 k hk; exact ⟨j, by omega, hg⟩,
                hso2, hmd2⟩)
          (fun Jd2 hJd2 => ?_)
        fc_split_fast
        · have hne_d : out_d[i.toNat]'hi_arr ≠ out_d[(u - 1#64).toNat]'hum1_arr :=
            bne_iff_ne.mp hc
          have hup1_n : (u + 1#64).toNat = u.toNat + 1 := by bv_omega
          fc_steps
          let vi := out_d[i.toNat]'hi_arr
          let out_d2 := out_d.set u.toNat vi
          have hod2_len : out_d2.length = cap.toNat := by simp [out_d2, hod_len]
          have hvi_eq : out_s[i.toNat]? = some vi := by
            rw [← htail_d i.toNat (Nat.le_refl _) hi_lt, List.getElem?_eq_getElem hi_arr]
          have hle_prev : out_d[(u - 1#64).toNat]?.getD 0#64 ≤ vi := by
            obtain ⟨j0, hj0, hget0⟩ := hsub_d (u.toNat - 1) (by omega)
            have hget0' : out_d[(u - 1#64).toNat]? = out_s[j0]? := by
              rw [hum1_n]; exact hget0
            have hs0 := hos_sort j0 i.toNat (Nat.zero_le _) (by omega) hi_lt
            rw [← hget0', hvi_eq, Option.getD_some] at hs0
            exact hs0
          refine hJd2 (u + 1#64, ()) m ⟨out_d2, by omega, by omega, hod2_len, ?_, ?_, ?_, hm⟩
          · intro k hk1 hk2
            dsimp [out_d2]
            rw [List.getElem?_set_ne (by omega)]
            exact htail_d k (by omega) hk2
          · intro k hk; rw [hup1_n] at hk
            by_cases hku : k = u.toNat
            · subst hku; dsimp [out_d2]; rw [List.getElem?_set_self (by omega)]
              exact ⟨i.toNat, by omega, hvi_eq.symm⟩
            · dsimp [out_d2]; rw [List.getElem?_set_ne (Ne.symm hku)]
              obtain ⟨j, hj, hget⟩ := hsub_d k (by omega)
              exact ⟨j, by omega, hget⟩
          · intro x y hx hxy hy; rw [hup1_n] at hy
            by_cases hyu : y = u.toNat
            · subst hyu; dsimp [out_d2]; rw [List.getElem?_set_self (by omega), Option.getD_some]
              by_cases hxu : x = u.toNat
              · subst hxu; rw [List.getElem?_set_self (by omega), Option.getD_some]
                exact BitVec.le_refl _
              · rw [List.getElem?_set_ne (Ne.symm hxu)]
                have hsd := hsort_d x (u.toNat - 1) hx (by omega) (by omega)
                rw [← hum1_n] at hsd
                exact BitVec.le_trans hsd hle_prev
            · dsimp [out_d2]
              rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (Ne.symm hyu)]
              exact hsort_d x y hx hxy (by omega)
        · fc_steps
          refine hJd2 (u, ()) md ⟨out_d, hu1, by omega, hod_len,
            fun k hk1 hk2 => htail_d k (by omega) hk2,
            fun k hk => by obtain ⟨j, hj, hg⟩ := hsub_d k hk; exact ⟨j, by omega, hg⟩,
            hsort_d, hmd⟩
      · have hi_ge : cnt.toNat ≤ i.toNat := by
          simp only [BitVec.ult, decide_eq_false_iff_not, not_lt] at hc; exact hc
        fc_steps
        refine hQ u out_d md hod_len (by omega) hsort_d (fun k hk => ?_) (sep_ac hmd)
        obtain ⟨j, hj, hget⟩ := hsub_d k hk
        have hok := hos_cb j (by omega)
        rwa [← hget] at hok
  · -- Watch scan loop (@L1)
    fc_to_group
    refine wp_loop_inv (ts := [i64, i64])
      (fun (p, cnt, ()) ml => ∃ out1 : List (BitVec 64),
        out1.length = cap.toNat ∧ cnt.toNat ≤ cap.toNat ∧
        p.toNat ≤ (off + wsz).toNat ∧
        DenseWatchSliceOk F_cur s.core lit.toNat p.toNat ((off + wsz).toNat - p.toNat) ∧
        (∀ k < cnt.toNat,
          CondBinElemOk F_cur s.core.cur_vars lit.toNat (out1[k]?.getD 0#64)) ∧
        (FullMemNoWks3 c s ⋆ array64 out out1 ⋆ R) ml)
      (fun (p, _, ()) _ => (off + wsz).toNat - p.toNat)
      (fun J1 hJ1 => by
        fc_steps
        refine hJ1 (off, 0#64, ()) m0 ⟨out0, hout_len, Nat.zero_le _, by bv_omega, ?_,
          fun k hk => by simp at hk, hm0⟩
        simpa [hoff_n, hwsz_n, hend_n, Nat.add_sub_cancel_left] using hslice0)
      (fun J1 ⟨p, cnt, ⟨⟩⟩ ml ⟨out1, hout1_len, hcnt_le, hp_le, hslice, hcb1, hml⟩ ih1 => ?_)
    fc_split_fast
    · have hp_lt : p.toNat < (off + wsz).toNat := by
        simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
      have hp_w : p.toNat < s.core.wstk.length := by omega
      obtain ⟨w0, hw0_get, hcase⟩ := dense_slice_pop_step hslice (by omega)
      have hw0_eq : s.core.wstk[p.toNat]'hp_w = w0 := by
        rw [List.getElem?_eq_getElem hp_w] at hw0_get; exact Option.some.inj hw0_get
      have hp1_n : (p + 1#64).toNat = p.toNat + 1 := by bv_omega
      c0_steps
      fc_to_group
      refine wp_join_group (ts := [i64, i64])
        (fun (pn, cn, ()) mn => ∃ outn : List (BitVec 64),
          outn.length = cap.toNat ∧ cn.toNat ≤ cap.toNat ∧
          p.toNat < pn.toNat ∧ pn.toNat ≤ (off + wsz).toNat ∧
          DenseWatchSliceOk F_cur s.core lit.toNat pn.toNat ((off + wsz).toNat - pn.toNat) ∧
          (∀ k < cn.toNat,
            CondBinElemOk F_cur s.core.cur_vars lit.toNat (outn[k]?.getD 0#64)) ∧
          (FullMemNoWks3 c s ⋆ array64 out outn ⋆ R) mn)
        (fun _ ⟨pn, cn, ⟨⟩⟩ mn ⟨outn, hon_len, hcn_le, hinc, hpn_le, hsln, hcbn, hmn⟩ => by
          fc_steps
          exact ih1 (pn, cn, ()) mn (by dsimp only; omega)
            ⟨outn, hon_len, hcn_le, hpn_le, hsln, hcbn, hmn⟩)
        (fun J2 hJ2 => ?_)
      fc_split_fast
      · rcases hcase with ⟨_, hrest⟩ | ⟨hf0, _⟩
        · fc_steps
          exact hJ2 (p + 1#64, cnt, ()) ml ⟨out1, hout1_len, hcnt_le, by omega, by omega,
            by simpa [hp1_n, Nat.sub_sub] using hrest, hcb1, hml⟩
        · exfalso; rw [hw0_eq] at hc; exact absurd hf0 (bne_iff_ne.mp hc)
      · rcases hcase with ⟨hf1, _⟩ | ⟨_, hrem2, cr, hcr_get, hcr_ref, hrest2⟩
        · exfalso; rw [hw0_eq] at hc; exact hf1 (by simpa using hc)
        · fc_split_fast
          · have hge_end : (off + wsz).toNat ≤ (p + 1#64).toNat := by
              simp only [BitVec.ule, decide_eq_true_eq] at hc; exact hc
            omega
          · have hp1_lt : p.toNat + 1 < (off + wsz).toNat := by omega
            have hp1_w : (p + 1#64).toNat < s.core.wstk.length := by omega
            have hp2_n : (p + 2#64).toNat = p.toNat + 2 := by bv_omega
            let crw := s.core.wstk[(p + 1#64).toNat]'hp1_w
            have hp1_bv : (p + 1).toNat = (p + 1#64).toNat := by bv_omega
            have hcr_c0 : ∀ (hwk : (p + 1).toNat < s.core.wstk.length),
                s.core.wstk[(p + 1).toNat]'hwk = crw := fun hwk =>
              list_getElem_congr hp1_bv hwk hp1_w
            have hcr_eq : crw = cr := by
              rw [show crw = s.core.wstk[p.toNat + 1]'(by omega) from
                list_getElem_congr hp1_n hp1_w (by omega)]
              rw [List.getElem?_eq_getElem (by omega)] at hcr_get
              exact Option.some.inj hcr_get
            have hcr_ref' : crw.toNat ∈ fullArenaClauseRefsCore s.core := hcr_eq.symm ▸ hcr_ref
            have hslice2 : DenseWatchSliceOk F_cur s.core lit.toNat (p + 2#64).toNat
                ((off + wsz).toNat - (p + 2#64).toNat) := by
              simpa [hp2_n, Nat.sub_sub] using hrest2
            let StepOut (cn : BitVec 64) (mn : Mem 64) : Prop := ∃ outn : List (BitVec 64),
              outn.length = cap.toNat ∧ cn.toNat ≤ cap.toNat ∧
              (∀ k < cn.toNat,
                CondBinElemOk F_cur s.core.cur_vars lit.toNat (outn[k]?.getD 0#64)) ∧
              (FullMemNoWks3 c s ⋆ array64 out outn ⋆ R) mn
            c0_steps
            fc_to_group
            refine wp_join_group (ts := [i64]) (fun (cn, ()) mn => StepOut cn mn)
              (fun _ ⟨cn, ⟨⟩⟩ mn ⟨outn, hon_len, hcn_le, hcbn, hmn⟩ => by
                fc_steps
                exact hJ2 (p + 2#64, cn, ()) mn
                  ⟨outn, hon_len, hcn_le, by omega, by omega, hslice2, hcbn, hmn⟩)
              (fun J3 hJ3 => ?_)
            fc_split_fast
            · have hcr5_lt : crw.toNat + 5 < s.core.arena_len := by
                simp only [BitVec.ult, decide_eq_true_eq] at hc
                have hpk : (p + 1).toNat < s.core.wstk.length := by rw [hp1_bv]; exact hp1_w
                have hc' : (crw.setWidth 64 + 5).toNat < s.core.arena_len := by
                  have hlt := Nat.lt_of_lt_of_le hc
                    (by rw [BitVec.toNat_ofNat]; exact Nat.mod_le _ _)
                  rw [hcr_c0 hpk] at hlt; exact hlt
                rw [BitVec.toNat_add, bv_zext32_toNat] at hc'
                bv_omega
              have hwf_cr := hw.arena.refs_wf crw.toNat hcr_ref'
              have har_bd0 : (crw.setWidth 64).toNat < s.core.arena.length := by
                rw [bv_zext32_toNat]; omega
              have har_bd2 : (crw.setWidth 64 + 2#64).toNat < s.core.arena.length := by
                rw [BitVec.toNat_add, bv_zext32_toNat]; bv_omega
              have har_bd3 : (crw.setWidth 64 + 3#64).toNat < s.core.arena.length := by
                rw [BitVec.toNat_add, bv_zext32_toNat]; bv_omega
              have har_bd4 : (crw.setWidth 64 + 4#64).toNat < s.core.arena.length := by
                rw [BitVec.toNat_add, bv_zext32_toNat]; bv_omega
              have har_bd5 : (crw.setWidth 64 + 5#64).toNat < s.core.arena.length := by
                rw [BitVec.toNat_add, bv_zext32_toNat]; bv_omega
              have har_bd3_c0 :
                  (BitVec.setWidth 64 (s.core.wstk[(p + 1).toNat]'(by rw [hp1_bv]; exact hp1_w)) +
                    (3 : BitVec 64)).toNat < s.core.arena.length := by
                rw [BitVec.toNat_add, bv_zext32_toNat,
                  congrArg BitVec.toNat (hcr_c0 (by rw [hp1_bv]; exact hp1_w))]; bv_omega
              have har_bd4_c0 :
                  (BitVec.setWidth 64 (s.core.wstk[(p + 1).toNat]'(by rw [hp1_bv]; exact hp1_w)) +
                    (4 : BitVec 64)).toNat < s.core.arena.length := by
                rw [BitVec.toNat_add, bv_zext32_toNat,
                  congrArg BitVec.toNat (hcr_c0 (by rw [hp1_bv]; exact hp1_w))]; bv_omega
              have har_bd5_c0 :
                  (BitVec.setWidth 64 (s.core.wstk[(p + 1).toNat]'(by rw [hp1_bv]; exact hp1_w)) +
                    (5 : BitVec 64)).toNat < s.core.arena.length := by
                rw [BitVec.toNat_add, bv_zext32_toNat,
                  congrArg BitVec.toNat (hcr_c0 (by rw [hp1_bv]; exact hp1_w))]; bv_omega
              c0_steps
              fc_to_group
              refine wp_join_group (ts := [i64]) (fun (cn, ()) mn => StepOut cn mn)
                (fun _ ⟨cn, ⟨⟩⟩ mn hstep => by fc_steps; exact hJ3 (cn, ()) mn hstep)
                (fun J4 hJ4 => ?_)
              fc_split_fast
              · have hhdr_eq : s.core.arena[(crw.setWidth 64).toNat]'har_bd0 =
                    Full.fullArenaHdrCore s.core crw.toNat := by
                  unfold fullArenaHdrCore
                  rw [List.getElem?_eq_getElem (by rw [bv_zext32_toNat] at har_bd0; exact har_bd0),
                    Option.getD_some]
                  exact list_getElem_congr (bv_zext32_toNat crw) har_bd0 (by omega)
                have hng : fullArenaClauseGarbCore s.core crw.toNat = false := by
                  unfold fullArenaClauseGarbCore
                  rw [← hhdr_eq]
                  have hhdr0 : (s.core.arena[(crw.setWidth 64).toNat]'har_bd0 &&& 0x00480000#32) =
                      0#32 := by
                    have h0 := beq_iff_eq.mp hc
                    have hmask : (524288 ||| 4194304 : BitVec 32) = 0x00480000#32 := by decide
                    rw [hmask] at h0
                    rwa [← list_getElem_congr (by simp only [bv_zext32_toNat]) har_bd0 _]
                  exact garb_false_of_and_480000 hhdr0
                refine wp_jnz_of (fun hc => ?_) (fun hc => ?_)
                · dsimp only [Arg.val] at hc
                  have hsz3 : fullArenaClauseSizeCore s.core crw.toNat = 3 := by
                    have h0 := beq_iff_eq.mp (show (_ == 3#32) = true from hc)
                    have hs0 : s.core.arena[(crw.setWidth 64 + 2#64).toNat]'har_bd2 = 3#32 := by
                      rwa [← list_getElem_congr (by
                        simp only [BitVec.toNat_add, bv_zext32_toNat]) har_bd2 _]
                    unfold fullArenaClauseSizeCore
                    have hidx2 : (crw.setWidth 64 + 2#64).toNat = crw.toNat + 2 := by
                      rw [BitVec.toNat_add, bv_zext32_toNat]; bv_omega
                    have hs1 : s.core.arena[crw.toNat + 2]? = some 3#32 := by
                      rw [List.getElem?_eq_getElem (by omega)]; congr 1
                      exact (list_getElem_congr hidx2 har_bd2 (by omega)).symm.trans hs0
                    simp [hs1]
                  have hent3 := hw.arena.entails crw.toNat hcr_ref' hng
                  have hlits3 := arena_clause3_lits hsz3 (by omega)
                  let l0 := s.core.arena[(crw.setWidth 64 + 3#64).toNat]'har_bd3
                  let l1 := s.core.arena[(crw.setWidth 64 + 4#64).toNat]'har_bd4
                  let l2 := s.core.arena[(crw.setWidth 64 + 5#64).toNat]'har_bd5
                  have hl0_eq : l0 = s.core.arena[crw.toNat + 3]'(by omega) :=
                    list_getElem_congr (by rw [BitVec.toNat_add, bv_zext32_toNat]; bv_omega)
                      har_bd3 (by omega)
                  have hl1_eq : l1 = s.core.arena[crw.toNat + 4]'(by omega) :=
                    list_getElem_congr (by rw [BitVec.toNat_add, bv_zext32_toNat]; bv_omega)
                      har_bd4 (by omega)
                  have hl2_eq : l2 = s.core.arena[crw.toNat + 5]'(by omega) :=
                    list_getElem_congr (by rw [BitVec.toNat_add, bv_zext32_toNat]; bv_omega)
                      har_bd5 (by omega)
                  have hcr_any : ∀ (hwk : (p + 1).toNat < s.core.wstk.length),
                      (s.core.wstk[(p + 1).toNat]'hwk).toNat = crw.toNat := fun hwk =>
                    congrArg BitVec.toNat (hcr_c0 hwk)
                  have hl0_lt : l0.toNat < 2 * s.core.cur_vars :=
                    hw.arena.lits_lt crw.toNat hcr_ref' hng l0.toNat (by rw [hlits3, hl0_eq]; simp)
                  have hl1_lt : l1.toNat < 2 * s.core.cur_vars :=
                    hw.arena.lits_lt crw.toNat hcr_ref' hng l1.toNat (by rw [hlits3, hl1_eq]; simp)
                  have hl2_lt : l2.toNat < 2 * s.core.cur_vars :=
                    hw.arena.lits_lt crw.toNat hcr_ref' hng l2.toNat (by rw [hlits3, hl2_eq]; simp)
                  have hl0_bd : (l0.setWidth 64).toNat < s.core.vals.length := by
                    rw [bv_zext32_toNat]; omega
                  have hl1_bd : (l1.setWidth 64).toNat < s.core.vals.length := by
                    rw [bv_zext32_toNat]; omega
                  have hl2_bd : (l2.setWidth 64).toNat < s.core.vals.length := by
                    rw [bv_zext32_toNat]; omega
                  c0_steps
                  fc_to_group
                  refine wp_join_group (ts := [i64]) (fun (cn, ()) mn => StepOut cn mn)
                    (fun _ ⟨cn, ⟨⟩⟩ mn hstep => by fc_steps; exact hJ4 (cn, ()) mn hstep)
                    (fun J5 hJ5 => ?_)
                  fc_split_fast
                  · fc_split_fast
                    · fc_split_fast
                      · let CandRes (a b : BitVec 32) (ok : Bool) (mc : Mem 64) : Prop :=
                          mc = ml ∧ (ok = true →
                            ((lit.toNat = l0.toNat ∧ a.toNat = l1.toNat ∧ b.toNat = l2.toNat) ∨
                             (lit.toNat = l1.toNat ∧ a.toNat = l0.toNat ∧ b.toNat = l2.toNat) ∨
                             (lit.toNat = l2.toNat ∧ a.toNat = l0.toNat ∧ b.toNat = l1.toNat)) ∧
                            a.toNat < 2 * s.core.cur_vars ∧ b.toNat < 2 * s.core.cur_vars)
                        fc_to_group
                        refine wp_join_group (ts := [i32, i32, .bool])
                          (fun (a, b, ok, ()) mc => CandRes a b ok mc)
                          (fun _ ⟨a, b, ok, ⟨⟩⟩ mc hcand => ?_)
                          (fun J6 hJ6 => ?_)
                        · obtain ⟨hmc, hok⟩ := hcand
                          subst mc
                          fc_split_fast
                          · obtain ⟨hperm, ha_lt, hb_lt⟩ := hok (by simpa using hc)
                            fc_split_fast
                            · have h1 : a.toNat / 2 ≠ b.toNat / 2 := by
                                rw [← bv32_ushiftRight_imm1_toNat a,
                                  ← bv32_ushiftRight_imm1_toNat b]
                                exact fun heq => bne_iff_ne.mp hc (BitVec.eq_of_toNat_eq heq)
                              fc_split_fast
                              · have h2 : a.toNat / 2 ≠ lit.toNat / 2 := by
                                  rw [← bv32_ushiftRight_imm1_toNat a,
                                    ← bv32_ushiftRight_imm1_toNat lit]
                                  exact fun heq => bne_iff_ne.mp hc (BitVec.eq_of_toNat_eq heq)
                                fc_split_fast
                                · have h3 : b.toNat / 2 ≠ lit.toNat / 2 := by
                                    rw [← bv32_ushiftRight_imm1_toNat b,
                                      ← bv32_ushiftRight_imm1_toNat lit]
                                    exact fun heq => bne_iff_ne.mp hc (BitVec.eq_of_toNat_eq heq)
                                  fc_split_fast
                                  · fc_steps
                                    refine hQ 0#64 out1 ml hout1_len (Nat.zero_le _)
                                      (fun i j hi hij hj => by simp at hj)
                                      (fun k hk => by simp at hk) hml
                                  · have hcnt_lt_cap : cnt.toNat < cap.toNat := by
                                      simp only [BitVec.ule, decide_eq_false_iff_not, not_le] at hc
                                      exact hc
                                    have hcnt_arr : cnt.toNat < out1.length := by omega
                                    have hcp1_n : (cnt + 1#64).toNat = cnt.toNat + 1 := by bv_omega
                                    fc_to_group
                                    refine wp_join_group (ts := [i32, i32])
                                      (fun (mn, mx, ()) mt => mt = ml ∧
                                        ((mn.setWidth 64 <<< (32 : Nat)) ||| mx.setWidth 64) =
                                          (((if b.ult a then b else a).setWidth 64 <<< 32#64) |||
                                            (if b.ult a then a else b).setWidth 64))
                                      (fun _ ⟨mn, mx, ⟨⟩⟩ mt ⟨hmt, hpack⟩ => ?_)
                                      (fun J10 hJ10 => ?_)
                                    · subst mt
                                      have hml' :
                                          (array64 out out1 ⋆ (FullMemNoWks3 c s ⋆ R)) ml :=
                                        sep_ac hml
                                      have sep_swap12 : ∀ {P Q S : Mem 64 → Prop} {mx : Mem 64},
                                          (P ⋆ (Q ⋆ S)) mx → (Q ⋆ P ⋆ S) mx := fun {P Q S mx} h =>
                                        sep_ac h
                                      fc_steps
                                      let packed :=
                                        ((mn.setWidth 64 <<< (32 : Nat)) ||| mx.setWidth 64)
                                      let out2 := out1.set cnt.toNat packed
                                      have hm2 :
                                          (FullMemNoWks3 c s ⋆ array64 out out2 ⋆ R) m :=
                                        sep_swap12 hm
                                      have hcb_new :
                                          CondBinElemOk F_cur s.core.cur_vars lit.toNat packed := by
                                        dsimp [packed]; rw [hpack]
                                        exact condBin_of_perm3
                                          (by rw [hlits3, ← hl0_eq, ← hl1_eq, ← hl2_eq] at hent3
                                              exact hent3)
                                          hperm ha_lt hb_lt h1 h2 h3
                                      refine hJ5 (cnt + 1#64, ()) m
                                        ⟨out2, by simp [out2, hout1_len], by omega,
                                          fun k hk => ?_, hm2⟩
                                      rw [hcp1_n] at hk
                                      by_cases hk_last : k = cnt.toNat
                                      · subst hk_last; dsimp [out2]
                                        rw [List.getElem?_set_self hcnt_arr, Option.getD_some]
                                        exact hcb_new
                                      · dsimp [out2]; rw [List.getElem?_set_ne (Ne.symm hk_last)]
                                        exact hcb1 k (by omega)
                                    · fc_split_fast
                                      · exact hJ10 (b, a, ()) ml ⟨rfl, packU64_eq_lt_rhs hc⟩
                                      · exact hJ10 (a, b, ()) ml ⟨rfl, packU64_eq_ge_rhs hc⟩
                                · fc_steps
                                  exact hJ5 (cnt, ()) ml ⟨out1, hout1_len, hcnt_le, hcb1, hml⟩
                              · fc_steps
                                exact hJ5 (cnt, ()) ml ⟨out1, hout1_len, hcnt_le, hcb1, hml⟩
                            · fc_steps; exact hJ5 (cnt, ()) ml ⟨out1, hout1_len, hcnt_le, hcb1, hml⟩
                          · fc_steps; exact hJ5 (cnt, ()) ml ⟨out1, hout1_len, hcnt_le, hcb1, hml⟩
                        · fc_split_fast
                          · have hceq : lit.toNat = l0.toNat := by
                              have h := (beq_iff_eq.mp hc).symm
                              rw [h, hl0_eq]
                              exact congrArg BitVec.toNat (list_getElem_congr
                                (by rw [BitVec.toNat_add, bv_zext32_toNat, hcr_any]; bv_omega)
                                _ (by omega))
                            fc_steps
                            exact hJ6 (l1, l2, true, ()) ml ⟨rfl, fun _ =>
                              ⟨Or.inl ⟨hceq, rfl, rfl⟩, hl1_lt, hl2_lt⟩⟩
                          · fc_to_group
                            refine wp_join_group (ts := [i32, i32, .bool])
                              (fun (a, b, ok, ()) mc => CandRes a b ok mc)
                              (fun _ ⟨a, b, ok, ⟨⟩⟩ mc hcand => by
                                fc_steps; exact hJ6 (a, b, ok, ()) mc hcand)
                              (fun J7 hJ7 => ?_)
                            fc_split_fast
                            · have hceq : lit.toNat = l1.toNat := by
                                have h := (beq_iff_eq.mp hc).symm
                                rw [h, hl1_eq]
                                exact congrArg BitVec.toNat (list_getElem_congr
                                  (by rw [BitVec.toNat_add, bv_zext32_toNat, hcr_any]; bv_omega)
                                  _ (by omega))
                              fc_steps
                              exact hJ7 (l0, l2, true, ()) ml ⟨rfl, fun _ =>
                                ⟨Or.inr (Or.inl ⟨hceq, rfl, rfl⟩), hl0_lt, hl2_lt⟩⟩
                            · fc_to_group
                              refine wp_join_group (ts := [i32, i32, .bool])
                                (fun (a, b, ok, ()) mc => CandRes a b ok mc)
                                (fun _ ⟨a, b, ok, ⟨⟩⟩ mc hcand => by
                                  fc_steps; exact hJ7 (a, b, ok, ()) mc hcand)
                                (fun J8 hJ8 => ?_)
                              fc_split_fast
                              · have hceq : lit.toNat = l2.toNat := by
                                  have h := (beq_iff_eq.mp hc).symm
                                  rw [h, hl2_eq]
                                  exact congrArg BitVec.toNat (list_getElem_congr
                                    (by rw [BitVec.toNat_add, bv_zext32_toNat, hcr_any]; bv_omega)
                                    _ (by omega))
                                fc_steps
                                exact hJ8 (l0, l1, true, ()) ml ⟨rfl, fun _ =>
                                  ⟨Or.inr (Or.inr ⟨hceq, rfl, rfl⟩), hl0_lt, hl1_lt⟩⟩
                              · fc_steps
                                exact hJ8 (0#32, 0#32, false, ()) ml ⟨rfl, fun h => by cases h⟩
                      · fc_steps; exact hJ5 (cnt, ()) ml ⟨out1, hout1_len, hcnt_le, hcb1, hml⟩
                    · fc_steps; exact hJ5 (cnt, ()) ml ⟨out1, hout1_len, hcnt_le, hcb1, hml⟩
                  · fc_steps; exact hJ5 (cnt, ()) ml ⟨out1, hout1_len, hcnt_le, hcb1, hml⟩
                · fc_steps; exact hJ4 (cnt, ()) ml ⟨out1, hout1_len, hcnt_le, hcb1, hml⟩
              · fc_steps; exact hJ4 (cnt, ()) ml ⟨out1, hout1_len, hcnt_le, hcb1, hml⟩
            · fc_steps; exact hJ3 (cnt, ()) ml ⟨out1, hout1_len, hcnt_le, hcb1, hml⟩
    · have hp_ge : (off + wsz).toNat ≤ p.toNat := by
        simp only [BitVec.ult, decide_eq_false_iff_not, not_lt] at hc; exact hc
      fc_steps
      exact hJ0 (p, cnt, ()) ml ⟨out1, hout1_len, hcnt_le, hcb1, hml⟩


/-! ## 3b. Cross-Module Spec Constructors & Shared Gate-Soundness Lemmas -/

theorem sortedRange64_sub {xs : List (BitVec 64)} {lo1 hi1 lo2 hi2 : Nat}
    (hs : SortedRange64 xs lo1 hi1) (hlo : lo1 ≤ lo2) (hhi : hi2 ≤ hi1) :
    SortedRange64 xs lo2 hi2 :=
  fun i j hi hij hj => hs i j (by omega) hij (by omega)

theorem m7U64SortSpec_mk {a n m Q X} (xs : List (BitVec 64)) (R : Mem 64 → Prop)
    (h1 : n.toNat ≤ xs.length) (h2 : xs.length < 2 ^ 61) (h3 : (array64 a xs ⋆ R) m)
    (hQ : ∀ xs' m', xs'.length = xs.length →
      (∀ k, n.toNat ≤ k → k < xs.length → xs'[k]? = xs[k]?) →
      (∀ k < n.toNat, ∃ j < n.toNat, xs'[k]? = xs[j]?) →
      SortedRange64 xs' 0 n.toNat → (array64 a xs' ⋆ R) m' → Q () m') :
    m7U64SortSpec (a, n, ()) m Q X :=
  ⟨xs, R, h1, h2, h3, hQ⟩

theorem m7BsearchU64Spec_mk {a lo hi key m Q X} (xs : List (BitVec 64)) (R : Mem 64 → Prop)
    (h1 : lo.toNat ≤ hi.toNat) (h2 : hi.toNat ≤ xs.length) (h3 : xs.length < 2 ^ 61)
    (h4 : SortedRange64 xs lo.toNat hi.toNat) (h5 : (array64 a xs ⋆ R) m)
    (hQ : ∀ r : Bool,
      (r = true ↔ ∃ idx, lo.toNat ≤ idx ∧ idx < hi.toNat ∧ xs[idx]? = some key) →
      Q (r, ()) m) :
    m7BsearchU64Spec (a, lo, hi, key, ()) m Q X :=
  ⟨xs, R, h1, h2, h3, h4, h5, hQ⟩

theorem m7CopyCondbinSpec_mk {c F0 F_cur s out cap m Q X} {lit : BitVec 32}
    (out0 : List (BitVec 64)) (R : Mem 64 → Prop)
    (h1 : s.LengthsOk c) (h2 : FullWitnessInv c F0 F_cur s.core)
    (h3 : s.core.dense_mode ≠ 0#64) (h4 : lit.toNat < 2 * s.core.cur_vars)
    (h5 : out0.length = cap.toNat) (h6 : cap.toNat < 2 ^ 61)
    (h7 : (FullMemNoWks3 c s ⋆ array64 out out0 ⋆ R) m)
    (hQ : ∀ cnt out' m', out'.length = cap.toNat → cnt.toNat ≤ cap.toNat →
      SortedRange64 out' 0 cnt.toNat →
      (∀ k < cnt.toNat, CondBinElemOk F_cur s.core.cur_vars lit.toNat (out'[k]?.getD 0#64)) →
      (FullMemNoWks3 c s ⋆ array64 out out' ⋆ R) m' → Q (cnt, ()) m') :
    m7CopyCondbinSpec (c.hdr, lit, out, cap, ()) m Q X :=
  ⟨c, F0, F_cur, s, out0, R, rfl, h1, h2, h3, h4, h5, h6, h7, hQ⟩

theorem bv32_lit_xor1_even_or' {x : BitVec 32} (hx : x &&& 1#32 = 0#32) :
    x ||| 1#32 = x ^^^ 1#32 :=
  bv32_lit_xor1_even_or hx

theorem bv32_litNeg_double (x : BitVec 32) : (x ^^^ 1#32) ^^^ 1#32 = x := by
  rw [BitVec.xor_assoc]; simp

theorem condEq_pack_of_condBin {F_cur : List (List Nat)} {cur_vars lit : Nat}
    {a vb nvb : BitVec 32}
    (hcl1 : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, a.toNat, vb.toNat]))
    (hcl2 : (cnfOfClauses F_cur).EntailsClause
      (cnfClause [lit, litNeg a.toNat, litNeg vb.toNat]))
    (hnvb : nvb = vb ^^^ 1#32)
    (ha : a.toNat < 2 * cur_vars) (hb : vb.toNat < 2 * cur_vars)
    (h1 : a.toNat / 2 ≠ vb.toNat / 2) (h2 : a.toNat / 2 ≠ lit / 2)
    (h3 : vb.toNat / 2 ≠ lit / 2) :
    CondEqElemOk F_cur cur_vars lit ((a.setWidth 64 <<< 32#64) ||| nvb.setWidth 64) ∧
    CondEqElemOk F_cur cur_vars lit
      ((vb.setWidth 64 <<< 32#64) ||| (a ^^^ 1#32).setWidth 64) ∧
    CondEqElemOk F_cur cur_vars lit ((nvb.setWidth 64 <<< 32#64) ||| a.setWidth 64) := by
  have hna_n : (a ^^^ 1#32).toNat = litNeg a.toNat := bv32_xor1_eq_litNeg a
  have hnvb_n : nvb.toNat = litNeg vb.toNat := by rw [hnvb]; exact bv32_xor1_eq_litNeg vb
  have hna_lt : (a ^^^ 1#32).toNat < 2 * cur_vars := by
    rw [hna_n]; exact litNeg_lt_two_mul ha
  have hnvb_lt : nvb.toNat < 2 * cur_vars := by
    rw [hnvb_n]; exact litNeg_lt_two_mul hb
  have hna_div : (a ^^^ 1#32).toNat / 2 = a.toNat / 2 := bv32_lit_div2_xor1 a
  have hnvb_div : nvb.toNat / 2 = vb.toNat / 2 := by rw [hnvb]; exact bv32_lit_div2_xor1 vb
  have hna_div2 : litNeg a.toNat / 2 = a.toNat / 2 := by rw [← hna_n]; exact hna_div
  have hnvb_div2 : litNeg vb.toNat / 2 = vb.toNat / 2 := by rw [← hnvb_n]; exact hnvb_div
  have hp1 : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, vb.toNat, a.toNat]) :=
    entails_perm_clause (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl <;> simp) hcl1
  have hp2 : (cnfOfClauses F_cur).EntailsClause
      (cnfClause [lit, litNeg vb.toNat, litNeg a.toNat]) :=
    entails_perm_clause (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl <;> simp) hcl2
  refine ⟨?_, ?_, ?_⟩
  · unfold CondEqElemOk; dsimp only; rw [packU64_hi, packU64_lo, hnvb_n, litNeg_litNeg]
    exact ⟨ha, by rwa [← hnvb_n], by rw [hnvb_div2]; exact h1, h2,
      by rw [hnvb_div2]; exact h3, hcl1, hcl2⟩
  · unfold CondEqElemOk; dsimp only; rw [packU64_hi, packU64_lo, hna_n, litNeg_litNeg]
    exact ⟨hb, by rwa [← hna_n], by rw [hna_div2]; exact Ne.symm h1, h3,
      by rw [hna_div2]; exact h2, hp1, hp2⟩
  · unfold CondEqElemOk; dsimp only; rw [packU64_hi, packU64_lo, hnvb_n, litNeg_litNeg]
    exact ⟨by rwa [← hnvb_n], ha, by rw [hnvb_div2]; exact Ne.symm h1,
      by rw [hnvb_div2]; exact h3, h2, hp2, hp1⟩

theorem condEq_of_condBin_hi_lo {F_cur : List (List Nat)} {cur_vars lit : Nat}
    {w1 w2 : BitVec 64} {a vb : BitVec 32}
    (h1 : CondBinElemOk F_cur cur_vars lit w1) (h2 : CondBinElemOk F_cur cur_vars lit w2)
    (ha1 : (w1 >>> 32).toNat = a.toNat) (hb1 : (w1 &&& 0xFFFFFFFF#64).toNat = vb.toNat)
    (ha2 : (w2 >>> 32).toNat = litNeg a.toNat)
    (hb2 : (w2 &&& 0xFFFFFFFF#64).toNat = litNeg vb.toNat) :
    CondEqElemOk F_cur cur_vars lit
      ((a.setWidth 64 <<< 32#64) ||| (vb ^^^ 1#32).setWidth 64) ∧
    CondEqElemOk F_cur cur_vars lit
      ((vb.setWidth 64 <<< 32#64) ||| (a ^^^ 1#32).setWidth 64) ∧
    CondEqElemOk F_cur cur_vars lit
      (((vb ^^^ 1#32).setWidth 64 <<< 32#64) ||| a.setWidth 64) := by
  unfold CondBinElemOk at h1 h2
  rw [ha1, hb1] at h1; rw [ha2, hb2] at h2
  exact condEq_pack_of_condBin h1.2.2.2.2.2 h2.2.2.2.2.2 rfl h1.1 h1.2.1
    h1.2.2.1 h1.2.2.2.1 h1.2.2.2.2.1


theorem merge_condeq_gate_ok {F_cur : List (List Nat)} {cur_vars : Nat}
    {scr scr1 : List (BitVec 32)} {g_len cond : Nat} {pv nv : BitVec 64}
    {y t e yy tt ee : BitVec 32}
    (hcv : 3 ≤ cur_vars) (hcond : cond < 2 * cur_vars)
    (hw1 : CondEqElemOk F_cur cur_vars (litNeg cond) pv)
    (hw2 : CondEqElemOk F_cur cur_vars cond nv)
    (hy : y = (pv >>> (32 : Nat)).setWidth 32)
    (ht : t = pv.setWidth 32) (he : e = nv.setWidth 32)
    (hsame : (nv >>> (32 : Nat)).setWidth 32 = y)
    (hflip : ((t &&& 1#32 = 0#32 → yy = y ∧ tt = t ∧ ee = e) ∧
              (t &&& 1#32 ≠ 0#32 → yy = y ^^^ 1#32 ∧ tt = t ^^^ 1#32 ∧ ee = e ^^^ 1#32)))
    (hc_bd : cond < 2 ^ 32)
    (hlen0 : g_len + 5 ≤ scr.length)
    (hscr1 : scr1 = ((((scr.set g_len yy).set (g_len + 1)
      ((2#32 <<< 28#32) ||| 3#32)).set (g_len + 2) (BitVec.ofNat 32 cond)).set
      (g_len + 3) tt).set (g_len + 4) ee)
    (hseq0 : GateSeqOk32 F_cur cur_vars scr g_len 0) :
    scr1.length = scr.length ∧
    (∀ idx < g_len, scr1[idx]? = scr[idx]?) ∧
    GateSeqOk32 F_cur cur_vars scr1 (g_len + 5) 0 := by
  have hy_n : (pv >>> 32).toNat = y.toNat := by rw [hy]; exact (u64_trunc32_hi_eq pv).symm
  have ht_n : (pv &&& 0xFFFFFFFF#64).toNat = t.toNat := by
    rw [ht]; exact (u64_trunc32_lo_eq pv).symm
  have he_n : (nv &&& 0xFFFFFFFF#64).toNat = e.toNat := by
    rw [he]; exact (u64_trunc32_lo_eq nv).symm
  have hsame_n : (pv >>> 32).toNat = (nv >>> 32).toNat := by
    rw [hy_n, ← hsame]
    change (BitVec.setWidth 32 (nv >>> 32)).toNat = (nv >>> 32).toNat
    bv_omega
  have hite := condEq_to_iteGateDef hw1 hw2 hsame_n
  rw [hy_n, ht_n, he_n] at hite
  have hy_lt : y.toNat < 2 * cur_vars := by rw [← hy_n]; exact hw1.1
  have ht_lt : t.toNat < 2 * cur_vars := by rw [← ht_n]; exact hw1.2.1
  have he_lt : e.toNat < 2 * cur_vars := by rw [← he_n]; exact hw2.2.1
  have hc32 : (BitVec.ofNat 32 cond).toNat = cond := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hc_bd
  by_cases hpar : t &&& 1#32 = 0#32
  · obtain ⟨rfl, rfl, rfl⟩ := hflip.1 hpar
    exact gateAt32_ite_append hcv hy_lt (by rw [hc32]; exact hcond) ht_lt he_lt
      (by rw [hc32]; exact hite) hlen0 hscr1 hseq0
  · obtain ⟨rfl, rfl, rfl⟩ := hflip.2 hpar
    have hyy_lt : (y ^^^ 1#32).toNat < 2 * cur_vars := by
      rw [bv32_xor1_eq_litNeg]; exact litNeg_lt_two_mul hy_lt
    have htt_lt : (t ^^^ 1#32).toNat < 2 * cur_vars := by
      rw [bv32_xor1_eq_litNeg]; exact litNeg_lt_two_mul ht_lt
    have hee_lt : (e ^^^ 1#32).toNat < 2 * cur_vars := by
      rw [bv32_xor1_eq_litNeg]; exact litNeg_lt_two_mul he_lt
    have hite' : IteGateDef (cnfOfClauses F_cur)
        (y ^^^ 1#32).toNat cond (t ^^^ 1#32).toNat (e ^^^ 1#32).toNat := by
      simp only [bv32_xor1_eq_litNeg]
      exact iteGateDef_flip_out hite
    exact gateAt32_ite_append hcv hyy_lt (by rw [hc32]; exact hcond) htt_lt hee_lt
      (by rw [hc32]; exact hite') hlen0 hscr1 hseq0

theorem m6GateAt_ite_append {F_cur : List (List Nat)} {cur_vars : Nat}
    {scr0 scr1 : List (BitVec 32)} {g_len : Nat} {y c t e : BitVec 32}
    (hcv : 3 ≤ cur_vars)
    (hy : y.toNat < 2 * cur_vars) (hc : c.toNat < 2 * cur_vars)
    (ht : t.toNat < 2 * cur_vars) (he : e.toNat < 2 * cur_vars)
    (hite : IteGateDef (cnfOfClauses F_cur) y.toNat c.toNat t.toNat e.toNat)
    (hlen0 : g_len + 5 ≤ scr0.length)
    (hscr1 : scr1 = ((((scr0.set g_len y).set (g_len + 1)
      ((2#32 <<< 28#32) ||| 3#32)).set (g_len + 2) c).set (g_len + 3) t).set (g_len + 4) e)
    (hseq0 : M6GateSeqOk F_cur cur_vars scr0 g_len 0) :
    scr1.length = scr0.length ∧
    (∀ idx < g_len, scr1[idx]? = scr0[idx]?) ∧
    M6GateSeqOk F_cur cur_vars scr1 (g_len + 5) 0 := by
  have hlen1 : scr1.length = scr0.length := by subst scr1; simp only [List.length_set]
  have hpref : ∀ idx < g_len, scr1[idx]? = scr0[idx]? := by
    intro idx hidx; subst scr1
    repeat rw [List.getElem?_set_ne (by omega)]
  have hg0 : scr1[g_len]? = some y := by
    subst scr1
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_self (by omega)]
  have hmword : scr1[g_len + 1]? = some ((2#32 <<< 28#32) ||| 3#32) := by
    subst scr1
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp; omega)]
  have hg2 : scr1[g_len + 2]? = some c := by
    subst scr1
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_self (by simp; omega)]
  have hg3 : scr1[g_len + 3]? = some t := by
    subst scr1
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp; omega)]
  have hg4 : scr1[g_len + 4]? = some e := by
    subst scr1; rw [List.getElem?_set_self (by simp; omega)]
  have htag : (((2#32 <<< 28#32) ||| 3#32) >>> 28).toNat = 2 := by decide
  have har : (((2#32 <<< 28#32) ||| 3#32) &&& 255#32).toNat = 3 := by decide
  have hgat : M6GateAt F_cur cur_vars scr1 (g_len + 5) g_len := by
    refine ⟨y, (2#32 <<< 28#32) ||| 3#32, hg0, hmword, hy, ?_⟩
    dsimp only; rw [htag, har]
    refine ⟨Nat.le_refl _, hcv, by decide, fun k hk => ?_, Or.inr (Or.inr ⟨rfl, rfl, ?_⟩)⟩
    · rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
      · exact ⟨c, hg2, hc⟩
      · exact ⟨t, hg3, ht⟩
      · exact ⟨e, hg4, he⟩
    · simpa [hg2, hg3, hg4] using hite
  have hnew : M6GateSeqOk F_cur cur_vars scr1 (g_len + 5) g_len := by
    refine M6GateSeqOk.step hgat ?_
    rw [hmword, Option.getD_some,
      show (((2#32 <<< 28#32) ||| 3#32) &&& 255#32).toNat = 3 from har]
    exact M6GateSeqOk.done
  exact ⟨hlen1, hpref, m6GateSeqOk_append (by omega) hpref hnew hseq0⟩

theorem merge_condeq_m6gate_ok {F_cur : List (List Nat)} {cur_vars : Nat}
    {scr scr1 : List (BitVec 32)} {g_len cond : Nat} {pv nv : BitVec 64}
    {y t e yy tt ee : BitVec 32}
    (hcv : 3 ≤ cur_vars) (hcond : cond < 2 * cur_vars)
    (hw1 : CondEqElemOk F_cur cur_vars (litNeg cond) pv)
    (hw2 : CondEqElemOk F_cur cur_vars cond nv)
    (hy : y = (pv >>> (32 : Nat)).setWidth 32)
    (ht : t = pv.setWidth 32) (he : e = nv.setWidth 32)
    (hsame : (nv >>> (32 : Nat)).setWidth 32 = y)
    (hflip : ((t &&& 1#32 = 0#32 → yy = y ∧ tt = t ∧ ee = e) ∧
              (t &&& 1#32 ≠ 0#32 → yy = y ^^^ 1#32 ∧ tt = t ^^^ 1#32 ∧ ee = e ^^^ 1#32)))
    (hc_bd : cond < 2 ^ 32) (hlen0 : g_len + 5 ≤ scr.length)
    (hscr1 : scr1 = ((((scr.set g_len yy).set (g_len + 1)
      ((2#32 <<< 28#32) ||| 3#32)).set (g_len + 2) (BitVec.ofNat 32 cond)).set
      (g_len + 3) tt).set (g_len + 4) ee)
    (hseq0 : M6GateSeqOk F_cur cur_vars scr g_len 0) :
    scr1.length = scr.length ∧ (∀ idx < g_len, scr1[idx]? = scr[idx]?) ∧
    M6GateSeqOk F_cur cur_vars scr1 (g_len + 5) 0 := by
  have hy_n : (pv >>> 32).toNat = y.toNat := by rw [hy]; exact (u64_trunc32_hi_eq pv).symm
  have ht_n : (pv &&& 0xFFFFFFFF#64).toNat = t.toNat := by
    rw [ht]; exact (u64_trunc32_lo_eq pv).symm
  have he_n : (nv &&& 0xFFFFFFFF#64).toNat = e.toNat := by
    rw [he]; exact (u64_trunc32_lo_eq nv).symm
  have hsame_n : (pv >>> 32).toNat = (nv >>> 32).toNat := by
    rw [hy_n, ← hsame]
    change (BitVec.setWidth 32 (nv >>> 32)).toNat = (nv >>> 32).toNat; bv_omega
  have hite := condEq_to_iteGateDef hw1 hw2 hsame_n
  rw [hy_n, ht_n, he_n] at hite
  have hy_lt : y.toNat < 2 * cur_vars := by rw [← hy_n]; exact hw1.1
  have ht_lt : t.toNat < 2 * cur_vars := by rw [← ht_n]; exact hw1.2.1
  have he_lt : e.toNat < 2 * cur_vars := by rw [← he_n]; exact hw2.2.1
  have hc32 : (BitVec.ofNat 32 cond).toNat = cond := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hc_bd
  by_cases hpar : t &&& 1#32 = 0#32
  · obtain ⟨rfl, rfl, rfl⟩ := hflip.1 hpar
    exact m6GateAt_ite_append hcv hy_lt (by rw [hc32]; exact hcond) ht_lt he_lt
      (by rw [hc32]; exact hite) hlen0 hscr1 hseq0
  · obtain ⟨rfl, rfl, rfl⟩ := hflip.2 hpar
    have hyy_lt : (y ^^^ 1#32).toNat < 2 * cur_vars := by
      rw [bv32_xor1_eq_litNeg]; exact litNeg_lt_two_mul hy_lt
    have htt_lt : (t ^^^ 1#32).toNat < 2 * cur_vars := by
      rw [bv32_xor1_eq_litNeg]; exact litNeg_lt_two_mul ht_lt
    have hee_lt : (e ^^^ 1#32).toNat < 2 * cur_vars := by
      rw [bv32_xor1_eq_litNeg]; exact litNeg_lt_two_mul he_lt
    have hite' : IteGateDef (cnfOfClauses F_cur)
        (y ^^^ 1#32).toNat cond (t ^^^ 1#32).toNat (e ^^^ 1#32).toNat := by
      simp only [bv32_xor1_eq_litNeg]; exact iteGateDef_flip_out hite
    exact m6GateAt_ite_append hcv hyy_lt (by rw [hc32]; exact hcond) htt_lt hee_lt
      (by rw [hc32]; exact hite') hlen0 hscr1 hseq0

theorem m7U64SiftSpec_noExit {xs m Q X X'} :
    m7U64SiftSpec xs m Q X → m7U64SiftSpec xs m Q X' := fun h => h

theorem m7U64SortSpec_noExit {xs m Q X X'} :
    m7U64SortSpec xs m Q X → m7U64SortSpec xs m Q X' := fun h => h

theorem m7BsearchU64Spec_noExit {xs m Q X X'} :
    m7BsearchU64Spec xs m Q X → m7BsearchU64Spec xs m Q X' := fun h => h

theorem m7CopyCondbinSpec_noExit {xs m Q X X'} :
    m7CopyCondbinSpec xs m Q X → m7CopyCondbinSpec xs m Q X' := fun h => h

theorem bv64_shl1_bv_toNat (x : BitVec 64) :
    (x <<< (1 : BitVec 64)).toNat = (2 * x.toNat) % 2 ^ 64 := by
  change (x <<< 1).toNat = _; exact bv64_shl1_toNat x

theorem bv64_lit0_toNat {v : BitVec 64} (hv : v.toNat < 2 ^ 30) :
    ((v <<< (1 : BitVec 64)).setWidth 32).toNat = 2 * v.toNat := by
  rw [BitVec.toNat_setWidth, bv64_shl1_bv_toNat]; omega

theorem bv64_lit0_even (v : BitVec 64) :
    ((v <<< (1 : BitVec 64)).setWidth 32) &&& 1#32 = 0#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i _
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · simp
  · simp [BitVec.getLsbD_and, show i ≠ 0 by omega]

theorem bv64_lit0_xor1 (v : BitVec 64) :
    ((v <<< (1 : BitVec 64)).setWidth 32) ^^^ 1#32 =
      ((v <<< (1 : BitVec 64)).setWidth 32) ||| 1#32 :=
  (bv32_lit_xor1_even_or (bv64_lit0_even v)).symm

theorem bv64_lit1_xor1 (v : BitVec 64) :
    (((v <<< (1 : BitVec 64)).setWidth 32) ||| 1#32) ^^^ 1#32 =
      (v <<< (1 : BitVec 64)).setWidth 32 := by
  rw [← bv64_lit0_xor1, bv32_litNeg_double]

theorem bv64_lit1_toNat {v : BitVec 64} (hv : v.toNat < 2 ^ 30) :
    (((v <<< (1 : BitVec 64)).setWidth 32) ||| 1#32).toNat = 2 * v.toNat + 1 := by
  rw [← bv64_lit0_xor1, bv32_xor1_eq_litNeg, bv64_lit0_toNat hv]
  unfold litNeg
  change (2 * v.toNat) ^^^ 1 = 2 * v.toNat + 1
  apply Nat.eq_of_testBit_eq; intro i
  rcases i with _ | j
  · simp [Nat.testBit_zero]
  · rw [Nat.testBit_xor]
    simp [Nat.testBit_succ, show 2 * v.toNat / 2 = v.toNat by omega,
      show (2 * v.toNat + 1) / 2 = v.toNat by omega]

theorem bv32_zext64_shl1_add1_toNat {l : BitVec 32} (hl : l.toNat < 2 ^ 31) :
    ((l.setWidth 64 <<< (1 : BitVec 64)) + 1#64).toNat = 2 * l.toNat + 1 := by
  rw [BitVec.toNat_add, bv64_shl1_bv_toNat, bv_zext32_toNat]
  have : (1#64 : BitVec 64).toNat = 1 := rfl
  omega

end LeanQbe.T.Examples.Kissat.FullM7CongIte

end
