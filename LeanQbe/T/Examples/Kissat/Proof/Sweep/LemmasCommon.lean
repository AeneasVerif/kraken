/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Kitten.LemmasBtAdd
public import LeanQbe.T.Examples.Kissat.Proof.Kitten.Tactics
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
public import LeanQbe.T.Examples.Kissat.Proof.Sweep.Spec
public import LeanQbe.T.Logic.C0HeadStep
public import LeanQbe.T.Logic.C0Step
public import LeanQbe.T.Logic.ControlComb
public import LeanQbe.T.Logic.ProofKit

/-!
# Shared Sweep Tactics, Dynamic Memory Rules, & Preservation Lemmas (`Proof.Sweep.LemmasCommon`)

Zero legacy `Full*` imports; zero `@[expose]` on theorems, lemmas, or sections.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Sweep

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Kitten
open LeanQbe.T.Examples.Kissat.Proof.Kitten.Spec
open LeanQbe.T.Examples.Kissat.Proof.Sweep.Spec

open K6MemATactics K6PtrTactics

/-! ## 1. Strictly Scoped `FullMem`, PHT, & Dynamic `K6` Memory Tactics -/

namespace M6SweepTactics

open FullArenaTactics
open scoped FullArenaTactics

attribute [scoped bv_c0 high] bv_c0_zext32_64
attribute [scoped bv_c0] bv32_lshr_1 bv32_and_1 bv32_xor_1 List.length_set Bool.false_eq_true
attribute [scoped bv_c0] k6_bv32_zero k6_bv32_one k6_bv32_two k6_mv32_toNat

@[scoped bv_c0] theorem m6_fullState_core (k : FullCoreState) (sc : FullScratch) :
    ({ core := k, scratch := sc } : FullState).core = k := rfl

@[scoped bv_c0] theorem m6_fullState_scratch (k : FullCoreState) (sc : FullScratch) :
    ({ core := k, scratch := sc } : FullState).scratch = sc := rfl

@[scoped bv_c0] theorem m6_bv64_and_1023 (x : BitVec 64) :
    (x &&& BitVec.ofNat 64 1023).toNat = x.toNat % 1024 := by
  rw [BitVec.toNat_and, show (BitVec.ofNat 64 1023).toNat = 1023 from rfl]
  exact Nat.and_two_pow_sub_one_eq_mod x.toNat 10

@[scoped bv_c0] theorem m6_bv32_shl1_nat (x : BitVec 32) :
    (x <<< (1 : Nat)).toNat = (2 * x.toNat) % 2 ^ 32 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]

@[scoped bv_c0] theorem m6_bv32_shl1_mod32 (x : BitVec 32) :
    x <<< ((1#32 : BitVec 32).toNat % 32) = x <<< (1 : Nat) := rfl

@[scoped bv_c0] theorem m6_bv64_shl1_bv (x : BitVec 32) :
    (x.setWidth 64 <<< (1 : Nat)).toNat = 2 * x.toNat := by
  have hx := x.isLt
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (by omega : x.toNat * 2 < 2 ^ 64)]; omega

@[scoped bv_c0] theorem m6_bv64_shl1_add1_bv (x : BitVec 32) :
    ((x.setWidth 64 <<< (1 : Nat)) + 1#64).toNat = 2 * x.toNat + 1 := by
  have hx := x.isLt
  rw [BitVec.toNat_add, m6_bv64_shl1_bv, show (1#64).toNat = 1 from rfl,
    Nat.mod_eq_of_lt (by omega : 2 * x.toNat + 1 < 2 ^ 64)]

@[scoped c0_load] theorem load_m6_tmp0 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hi : 0 < s.core.tmp.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 c.pTmp = some s.core.tmp[0] := by
  simpa using load_full_tmp (i := 0) hi hm

@[scoped c0_store] theorem store_m6_tmp0 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (v : BitVec 32) (hi : 0 < s.core.tmp.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 c.pTmp ∧
      (FullMem c { s with core := { s.core with tmp := s.core.tmp.set 0 v } } ⋆ R)
        (storeMem m i32 c.pTmp v) := by
  simpa using store_full_tmp (i := 0) v hi hm

@[scoped c0_store] theorem store_m6_tmp1 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (v : BitVec 32) (hi : 1 < s.core.tmp.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pTmp + 4) ∧
      (FullMem c { s with core := { s.core with tmp := s.core.tmp.set 1 v } } ⋆ R)
        (storeMem m i32 (c.pTmp + 4) v) := by
  simpa using store_full_tmp (i := 1) v hi hm

@[scoped c0_load] theorem load_m6_ws1_0 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hi : 0 < s.scratch.work_stk1.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 c.pWorkStk1 = some s.scratch.work_stk1[0] := by
  simpa using load_full_work_stk1 (i := 0) hi hm

@[scoped c0_store] theorem store_m6_ws1_0 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (v : BitVec 32) (hi : 0 < s.scratch.work_stk1.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 c.pWorkStk1 ∧
      (FullMem c { s with scratch := { s.scratch with
        work_stk1 := s.scratch.work_stk1.set 0 v } } ⋆ R)
        (storeMem m i32 c.pWorkStk1 v) := by
  simpa using store_full_work_stk1 (i := 0) v hi hm

scoped macro "m6_steps" : tactic =>
  `(tactic| (
      (try change Func.wp _ _ _ _ _ _); (try change wp _ _ _ _ _)
      c0_hsteps!))

scoped macro "m6_split" : tactic =>
  `(tactic| (
      (try change Func.wp _ _ _ _ _ _); (try change wp _ _ _ _ _)
      c0_hsplit))

scoped macro "m6_to_group" : tactic =>
  `(tactic| (
      (try change Func.wp _ _ _ _ _ _); (try change wp _ _ _ _ _)
      c0_hsteps_nogrp))

scoped macro "m6_csteps!" : tactic =>
  `(tactic| (
      (try change Func.wp _ _ _ _ _ _); (try change wp _ _ _ _ _)
      c0_steps!))

scoped macro "m6_call " h:ident : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

end M6SweepTactics

open FullArenaTactics
open scoped FullArenaTactics M6SweepTactics

namespace FullK6DynMem

@[scoped c0_load] theorem load_m6_full_kvals {c : FullCfg} {L : K6Layout} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {idx : BitVec 32}
    (hL : L.scrLen = c.scratch_cap) (hscr : s.scratch.scratch_buf.length = c.scratch_cap)
    (hi : idx.toNat < 2 * L.maxV) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 ((L.kPtr c.pScratchBuf + BitVec.ofNat 64 (4 * L.oVals)) +
        idx.setWidth 64 * 4) =
      some (s.scratch.scratch_buf[L.k6Base + L.oVals + idx.toNat]'(by
        have := L.hmaxV; have := L.hacap
        rw [hscr, ← hL]; unfold K6Layout.scrLen K6Layout.k6Fixed K6Layout.oVals; omega)) := by
  have hlt : idx.toNat < 2 ^ 28 := by have := L.hmaxV; omega
  have hptr : (L.kPtr c.pScratchBuf + BitVec.ofNat 64 (4 * L.oVals)) + idx.setWidth 64 * 4 =
      c.pScratchBuf + BitVec.ofNat 64 (4 * (L.k6Base + L.oVals + idx.toNat)) := by
    rw [show idx.setWidth 64 = BitVec.ofNat 64 idx.toNat from by apply BitVec.eq_of_toNat_eq; simp,
      k6_ptr_nat_mul4 _ idx.toNat hlt, K6Layout.kPtr, BitVec.add_assoc, BitVec.add_assoc,
      ← BitVec.ofNat_add, ← BitVec.ofNat_add]
    congr 2; unfold K6Layout.k6Base K6Layout.oVals; omega
  rw [hptr]; exact load_full_scratch_buf _ hm

@[scoped c0_load] theorem load_m6_full_kvals_dyn {c : FullCfg} {L : K6Layout} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {idx : BitVec 32}
    (hL : L.scrLen = c.scratch_cap) (hscr : s.scratch.scratch_buf.length = c.scratch_cap)
    (hi : idx.toNat < 2 * L.maxV) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 ((L.kPtr c.pScratchBuf +
        ((32 : BitVec 32) + (10 : BitVec 32) * L.mv32).setWidth 64 * 4) +
        idx.setWidth 64 * 4) =
      some (s.scratch.scratch_buf[L.k6Base + L.oVals + idx.toNat]'(by
        have := L.hmaxV; have := L.hacap
        rw [hscr, ← hL]; unfold K6Layout.scrLen K6Layout.k6Fixed K6Layout.oVals; omega)) := by
  rw [k6_ptr_vals L (L.kPtr c.pScratchBuf)]; exact load_m6_full_kvals hL hscr hi hm

@[scoped c0_load] theorem load_m6_full_k6_hdr {c : FullCfg} {L : K6Layout} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {idx : Nat}
    (hL : L.scrLen = c.scratch_cap) (hscr : s.scratch.scratch_buf.length = c.scratch_cap)
    (hidx : idx < 32) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 (L.kPtr c.pScratchBuf + BitVec.ofNat 64 idx * 4) =
      some (s.scratch.scratch_buf[L.k6Base + idx]'(by
        have := L.hmaxV; have := L.hacap
        rw [hscr, ← hL]; unfold K6Layout.scrLen K6Layout.k6Fixed; omega)) := by
  have hptr : L.kPtr c.pScratchBuf + BitVec.ofNat 64 idx * 4 =
      c.pScratchBuf + BitVec.ofNat 64 (4 * (L.k6Base + idx)) := by
    have := L.hmaxV
    rw [K6Layout.kPtr, k6_ptr_nat_mul4 _ idx (by omega), BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2; unfold K6Layout.k6Base; omega
  rw [hptr]; exact load_full_scratch_buf _ hm

@[scoped c0_store] theorem store_m6_full_k6_hdr {c : FullCfg} {L : K6Layout} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) {idx : Nat}
    (hL : L.scrLen = c.scratch_cap) (hscr : s.scratch.scratch_buf.length = c.scratch_cap)
    (hidx : idx < 32) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (L.kPtr c.pScratchBuf + BitVec.ofNat 64 idx * 4) ∧
      (FullMem c { s with scratch := { s.scratch with
        scratch_buf := s.scratch.scratch_buf.set (L.k6Base + idx) v } } ⋆ R)
        (storeMem m i32 (L.kPtr c.pScratchBuf + BitVec.ofNat 64 idx * 4) v) := by
  have hptr : L.kPtr c.pScratchBuf + BitVec.ofNat 64 idx * 4 =
      c.pScratchBuf + BitVec.ofNat 64 (4 * (L.k6Base + idx)) := by
    have := L.hmaxV
    rw [K6Layout.kPtr, k6_ptr_nat_mul4 _ idx (by omega), BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2; unfold K6Layout.k6Base; omega
  rw [hptr]
  exact store_full_scratch_buf v (by
    have := L.hmaxV; have := L.hacap
    rw [hscr, ← hL]; unfold K6Layout.scrLen K6Layout.k6Fixed; omega) hm

@[scoped c0_load] theorem load_m6_full_kassump {c : FullCfg} {L : K6Layout} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {idx : BitVec 32}
    (hL : L.scrLen = c.scratch_cap) (hscr : s.scratch.scratch_buf.length = c.scratch_cap)
    (hi : idx.toNat < L.maxV) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 ((L.kPtr c.pScratchBuf + BitVec.ofNat 64 (4 * L.oAssump)) +
        idx.setWidth 64 * 4) =
      some (s.scratch.scratch_buf[L.k6Base + L.oAssump + idx.toNat]'(by
        have := L.hmaxV; have := L.hacap
        rw [hscr, ← hL]; unfold K6Layout.scrLen K6Layout.k6Fixed K6Layout.oAssump; omega)) := by
  have hlt : idx.toNat < 2 ^ 28 := by have := L.hmaxV; omega
  have hptr : (L.kPtr c.pScratchBuf + BitVec.ofNat 64 (4 * L.oAssump)) + idx.setWidth 64 * 4 =
      c.pScratchBuf + BitVec.ofNat 64 (4 * (L.k6Base + L.oAssump + idx.toNat)) := by
    rw [show idx.setWidth 64 = BitVec.ofNat 64 idx.toNat from by apply BitVec.eq_of_toNat_eq; simp,
      k6_ptr_nat_mul4 _ idx.toNat hlt, K6Layout.kPtr, BitVec.add_assoc, BitVec.add_assoc,
      ← BitVec.ofNat_add, ← BitVec.ofNat_add]
    congr 2; unfold K6Layout.k6Base K6Layout.oAssump; omega
  rw [hptr]; exact load_full_scratch_buf _ hm

end FullK6DynMem

namespace M6PhtMem

private theorem pht_ptr_add (p : BitVec 64) {base : Nat} (_hb : base < 2 ^ 28)
    {idx : BitVec 32} (hi : idx.toNat < 2 ^ 28) :
    (p + BitVec.ofNat 64 (4 * base)) + idx.setWidth 64 * 4 =
      p + BitVec.ofNat 64 (4 * (base + idx.toNat)) := by
  rw [show idx.setWidth 64 = BitVec.ofNat 64 idx.toNat from by apply BitVec.eq_of_toNat_eq; simp,
    k6_ptr_nat_mul4 _ idx.toNat hi, BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 2; omega

private theorem pht_base_mul4 (p : BitVec 64) {base : Nat} (hb : base < 2 ^ 28) :
    p + BitVec.ofNat 64 base * 4 = p + BitVec.ofNat 64 (4 * base) := by
  rw [k6_ptr_nat_mul4 p base hb]

private theorem pht_merged_ptr (L : K6Layout) (p : BitVec 64) :
    p + ((1280 : BitVec 32) + L.mv32).setWidth 64 * 4 =
      p + BitVec.ofNat 64 (4 * L.phtMerged) := by
  have := L.hmaxV
  congr 1; apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_add, k6_mv32_toNat,
    BitVec.toNat_ofNat]
  unfold K6Layout.phtMerged
  rw [show (1280 : BitVec 32).toNat = 1280 from rfl,
    show (4 : BitVec 64).toNat = 4 from rfl,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

@[scoped c0_load] theorem load_pht_head {c : FullCfg} {L : K6Layout} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {idx : BitVec 32}
    (hL : L.scrLen = c.scratch_cap) (hscr : s.scratch.scratch_buf.length = c.scratch_cap)
    (hi : idx.toNat < k6PhtSz) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 ((c.pScratchBuf + BitVec.ofNat 64 (4 * k6PhtHead)) + idx.setWidth 64 * 4) =
      some (s.scratch.scratch_buf[k6PhtHead + idx.toNat]'(by
        have := L.hmaxV; have := L.hacap
        rw [hscr, ← hL]
        unfold K6Layout.scrLen K6Layout.k6Base k6PhtHead k6PhtSz at *; omega)) := by
  rw [pht_ptr_add c.pScratchBuf (by unfold k6PhtHead; decide)
    (by unfold k6PhtSz at hi; omega)]
  exact load_full_scratch_buf _ hm

@[scoped c0_load] theorem load_pht_head_ofnat {c : FullCfg} {L : K6Layout} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {idx : BitVec 32}
    (hL : L.scrLen = c.scratch_cap) (hscr : s.scratch.scratch_buf.length = c.scratch_cap)
    (hi : idx.toNat < k6PhtSz) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 ((c.pScratchBuf + (256 : BitVec 64) * 4) + idx.setWidth 64 * 4) =
      some (s.scratch.scratch_buf[k6PhtHead + idx.toNat]'(by
        have := L.hmaxV; have := L.hacap
        rw [hscr, ← hL]
        unfold K6Layout.scrLen K6Layout.k6Base k6PhtHead k6PhtSz at *; omega)) := by
  rw [show (256 : BitVec 64) = BitVec.ofNat 64 k6PhtHead from rfl,
    pht_base_mul4 c.pScratchBuf (by unfold k6PhtHead; decide)]
  exact load_pht_head hL hscr hi hm

@[scoped c0_load] theorem load_pht_head_64 {c : FullCfg} {L : K6Layout} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {idx : BitVec 32}
    (hL : L.scrLen = c.scratch_cap) (hscr : s.scratch.scratch_buf.length = c.scratch_cap)
    (hi : idx.toNat < k6PhtSz) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 ((c.pScratchBuf + (256#64 : BitVec 64) * 4) + idx.setWidth 64 * 4) =
      some (s.scratch.scratch_buf[k6PhtHead + idx.toNat]'(by
        have := L.hmaxV; have := L.hacap
        rw [hscr, ← hL]; unfold K6Layout.scrLen K6Layout.k6Base k6PhtHead k6PhtSz at *; omega)) :=
  load_pht_head_ofnat hL hscr hi hm

@[scoped c0_store] theorem store_pht_head {c : FullCfg} {L : K6Layout} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) {idx : BitVec 32}
    (hL : L.scrLen = c.scratch_cap) (hscr : s.scratch.scratch_buf.length = c.scratch_cap)
    (hi : idx.toNat < k6PhtSz) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 ((c.pScratchBuf + BitVec.ofNat 64 (4 * k6PhtHead)) + idx.setWidth 64 * 4) ∧
      (FullMem c { s with scratch := { s.scratch with
        scratch_buf := s.scratch.scratch_buf.set (k6PhtHead + idx.toNat) v } } ⋆ R)
        (storeMem m i32
          ((c.pScratchBuf + BitVec.ofNat 64 (4 * k6PhtHead)) + idx.setWidth 64 * 4) v) := by
  rw [pht_ptr_add c.pScratchBuf (by unfold k6PhtHead; decide)
    (by unfold k6PhtSz at hi; omega)]
  exact store_full_scratch_buf v (by
    have := L.hmaxV; have := L.hacap
    rw [hscr, ← hL]; unfold K6Layout.scrLen K6Layout.k6Base k6PhtHead k6PhtSz at *; omega) hm

@[scoped c0_store] theorem store_pht_head_ofnat {c : FullCfg} {L : K6Layout} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) {idx : BitVec 32}
    (hL : L.scrLen = c.scratch_cap) (hscr : s.scratch.scratch_buf.length = c.scratch_cap)
    (hi : idx.toNat < k6PhtSz) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 ((c.pScratchBuf + (256 : BitVec 64) * 4) + idx.setWidth 64 * 4) ∧
      (FullMem c { s with scratch := { s.scratch with
        scratch_buf := s.scratch.scratch_buf.set (k6PhtHead + idx.toNat) v } } ⋆ R)
        (storeMem m i32 ((c.pScratchBuf + (256 : BitVec 64) * 4) + idx.setWidth 64 * 4) v) := by
  rw [show (256 : BitVec 64) = BitVec.ofNat 64 k6PhtHead from rfl,
    pht_base_mul4 c.pScratchBuf (by unfold k6PhtHead; decide)]
  exact store_pht_head v hL hscr hi hm

@[scoped c0_store] theorem store_pht_head_64 {c : FullCfg} {L : K6Layout} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) {idx : BitVec 32}
    (hL : L.scrLen = c.scratch_cap) (hscr : s.scratch.scratch_buf.length = c.scratch_cap)
    (hi : idx.toNat < k6PhtSz) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 ((c.pScratchBuf + (256#64 : BitVec 64) * 4) + idx.setWidth 64 * 4) ∧
      (FullMem c { s with scratch := { s.scratch with
        scratch_buf := s.scratch.scratch_buf.set (k6PhtHead + idx.toNat) v } } ⋆ R)
        (storeMem m i32
          ((c.pScratchBuf + (256#64 : BitVec 64) * 4) + idx.setWidth 64 * 4) v) :=
  store_pht_head_ofnat v hL hscr hi hm

@[scoped c0_load] theorem load_pht_next {c : FullCfg} {L : K6Layout} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {idx : BitVec 32}
    (hL : L.scrLen = c.scratch_cap) (hscr : s.scratch.scratch_buf.length = c.scratch_cap)
    (hi : idx.toNat < L.maxV) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 ((c.pScratchBuf + BitVec.ofNat 64 (4 * k6PhtNext)) + idx.setWidth 64 * 4) =
      some (s.scratch.scratch_buf[k6PhtNext + idx.toNat]'(by
        have := L.hmaxV; have := L.hacap
        rw [hscr, ← hL]; unfold K6Layout.scrLen K6Layout.k6Base k6PhtNext; omega)) := by
  have := L.hmaxV
  rw [pht_ptr_add c.pScratchBuf (by unfold k6PhtNext; decide) (by omega)]
  exact load_full_scratch_buf _ hm

@[scoped c0_load] theorem load_pht_next_32 {c : FullCfg} {L : K6Layout} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {idx : BitVec 32}
    (hL : L.scrLen = c.scratch_cap) (hscr : s.scratch.scratch_buf.length = c.scratch_cap)
    (hi : idx.toNat < L.maxV) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32
        ((c.pScratchBuf + ((1280 : BitVec 32).setWidth 64) * 4) + idx.setWidth 64 * 4) =
      some (s.scratch.scratch_buf[k6PhtNext + idx.toNat]'(by
        have := L.hmaxV; have := L.hacap
        rw [hscr, ← hL]; unfold K6Layout.scrLen K6Layout.k6Base k6PhtNext; omega)) := by
  change loadVal m i32 ((c.pScratchBuf + BitVec.ofNat 64 (4 * k6PhtNext)) +
    idx.setWidth 64 * 4) = _
  exact load_pht_next hL hscr hi hm

@[scoped c0_load] theorem load_pht_next_bv32 {c : FullCfg} {L : K6Layout} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {idx : BitVec 32}
    (hL : L.scrLen = c.scratch_cap) (hscr : s.scratch.scratch_buf.length = c.scratch_cap)
    (hi : idx.toNat < L.maxV) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 ((c.pScratchBuf + (1280#32).setWidth 64 * 4) + idx.setWidth 64 * 4) =
      some (s.scratch.scratch_buf[k6PhtNext + idx.toNat]'(by
        have := L.hmaxV; have := L.hacap
        rw [hscr, ← hL]; unfold K6Layout.scrLen K6Layout.k6Base k6PhtNext; omega)) :=
  load_pht_next_32 hL hscr hi hm

@[scoped c0_load] theorem load_pht_next_ofnat {c : FullCfg} {L : K6Layout} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {idx : BitVec 32}
    (hL : L.scrLen = c.scratch_cap) (hscr : s.scratch.scratch_buf.length = c.scratch_cap)
    (hi : idx.toNat < L.maxV) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 ((c.pScratchBuf + (1280 : BitVec 64) * 4) + idx.setWidth 64 * 4) =
      some (s.scratch.scratch_buf[k6PhtNext + idx.toNat]'(by
        have := L.hmaxV; have := L.hacap
        rw [hscr, ← hL]; unfold K6Layout.scrLen K6Layout.k6Base k6PhtNext; omega)) :=
  load_pht_next_32 hL hscr hi hm

@[scoped c0_load] theorem load_pht_next_64 {c : FullCfg} {L : K6Layout} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {idx : BitVec 32}
    (hL : L.scrLen = c.scratch_cap) (hscr : s.scratch.scratch_buf.length = c.scratch_cap)
    (hi : idx.toNat < L.maxV) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 ((c.pScratchBuf + (1280#64 : BitVec 64) * 4) + idx.setWidth 64 * 4) =
      some (s.scratch.scratch_buf[k6PhtNext + idx.toNat]'(by
        have := L.hmaxV; have := L.hacap
        rw [hscr, ← hL]; unfold K6Layout.scrLen K6Layout.k6Base k6PhtNext; omega)) :=
  load_pht_next_32 hL hscr hi hm

@[scoped c0_store] theorem store_pht_next {c : FullCfg} {L : K6Layout} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) {idx : BitVec 32}
    (hL : L.scrLen = c.scratch_cap) (hscr : s.scratch.scratch_buf.length = c.scratch_cap)
    (hi : idx.toNat < L.maxV) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 ((c.pScratchBuf + BitVec.ofNat 64 (4 * k6PhtNext)) + idx.setWidth 64 * 4) ∧
      (FullMem c { s with scratch := { s.scratch with
        scratch_buf := s.scratch.scratch_buf.set (k6PhtNext + idx.toNat) v } } ⋆ R)
        (storeMem m i32
          ((c.pScratchBuf + BitVec.ofNat 64 (4 * k6PhtNext)) + idx.setWidth 64 * 4) v) := by
  have := L.hmaxV
  rw [pht_ptr_add c.pScratchBuf (by unfold k6PhtNext; decide) (by omega)]
  exact store_full_scratch_buf v (by
    have := L.hmaxV; have := L.hacap
    rw [hscr, ← hL]; unfold K6Layout.scrLen K6Layout.k6Base k6PhtNext; omega) hm

@[scoped c0_store] theorem store_pht_next_32 {c : FullCfg} {L : K6Layout} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) {idx : BitVec 32}
    (hL : L.scrLen = c.scratch_cap) (hscr : s.scratch.scratch_buf.length = c.scratch_cap)
    (hi : idx.toNat < L.maxV) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32
        ((c.pScratchBuf + ((1280 : BitVec 32).setWidth 64) * 4) + idx.setWidth 64 * 4) ∧
      (FullMem c { s with scratch := { s.scratch with
        scratch_buf := s.scratch.scratch_buf.set (k6PhtNext + idx.toNat) v } } ⋆ R)
        (storeMem m i32
          ((c.pScratchBuf + ((1280 : BitVec 32).setWidth 64) * 4) +
            idx.setWidth 64 * 4) v) := by
  change storeOk m i32 ((c.pScratchBuf + BitVec.ofNat 64 (4 * k6PhtNext)) +
    idx.setWidth 64 * 4) ∧ _
  exact store_pht_next v hL hscr hi hm

@[scoped c0_store] theorem store_pht_next_bv32 {c : FullCfg} {L : K6Layout} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) {idx : BitVec 32}
    (hL : L.scrLen = c.scratch_cap) (hscr : s.scratch.scratch_buf.length = c.scratch_cap)
    (hi : idx.toNat < L.maxV) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 ((c.pScratchBuf + (1280#32).setWidth 64 * 4) + idx.setWidth 64 * 4) ∧
      (FullMem c { s with scratch := { s.scratch with
        scratch_buf := s.scratch.scratch_buf.set (k6PhtNext + idx.toNat) v } } ⋆ R)
        (storeMem m i32
          ((c.pScratchBuf + (1280#32).setWidth 64 * 4) + idx.setWidth 64 * 4) v) :=
  store_pht_next_32 v hL hscr hi hm

@[scoped c0_store] theorem store_pht_next_ofnat {c : FullCfg} {L : K6Layout} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) {idx : BitVec 32}
    (hL : L.scrLen = c.scratch_cap) (hscr : s.scratch.scratch_buf.length = c.scratch_cap)
    (hi : idx.toNat < L.maxV) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 ((c.pScratchBuf + (1280 : BitVec 64) * 4) + idx.setWidth 64 * 4) ∧
      (FullMem c { s with scratch := { s.scratch with
        scratch_buf := s.scratch.scratch_buf.set (k6PhtNext + idx.toNat) v } } ⋆ R)
        (storeMem m i32
          ((c.pScratchBuf + (1280 : BitVec 64) * 4) + idx.setWidth 64 * 4) v) :=
  store_pht_next_32 v hL hscr hi hm

@[scoped c0_store] theorem store_pht_next_64 {c : FullCfg} {L : K6Layout} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) {idx : BitVec 32}
    (hL : L.scrLen = c.scratch_cap) (hscr : s.scratch.scratch_buf.length = c.scratch_cap)
    (hi : idx.toNat < L.maxV) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 ((c.pScratchBuf + (1280#64 : BitVec 64) * 4) + idx.setWidth 64 * 4) ∧
      (FullMem c { s with scratch := { s.scratch with
        scratch_buf := s.scratch.scratch_buf.set (k6PhtNext + idx.toNat) v } } ⋆ R)
        (storeMem m i32
          ((c.pScratchBuf + (1280#64 : BitVec 64) * 4) + idx.setWidth 64 * 4) v) :=
  store_pht_next_32 v hL hscr hi hm

@[scoped c0_load] theorem load_pht_merged {c : FullCfg} {L : K6Layout} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {idx : BitVec 32}
    (hL : L.scrLen = c.scratch_cap) (hscr : s.scratch.scratch_buf.length = c.scratch_cap)
    (hi : idx.toNat < L.maxV) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 ((c.pScratchBuf + BitVec.ofNat 64 (4 * L.phtMerged)) + idx.setWidth 64 * 4) =
      some (s.scratch.scratch_buf[L.phtMerged + idx.toNat]'(by
        have := L.hmaxV; have := L.hacap
        rw [hscr, ← hL]; unfold K6Layout.scrLen K6Layout.k6Base K6Layout.phtMerged; omega)) := by
  have := L.hmaxV
  rw [pht_ptr_add c.pScratchBuf (by unfold K6Layout.phtMerged; omega) (by omega)]
  exact load_full_scratch_buf _ hm

@[scoped c0_load] theorem load_pht_merged_32 {c : FullCfg} {L : K6Layout} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {idx : BitVec 32}
    (hL : L.scrLen = c.scratch_cap) (hscr : s.scratch.scratch_buf.length = c.scratch_cap)
    (hi : idx.toNat < L.maxV) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32
        ((c.pScratchBuf + ((1280 : BitVec 32) + L.mv32).setWidth 64 * 4) +
          idx.setWidth 64 * 4) =
      some (s.scratch.scratch_buf[L.phtMerged + idx.toNat]'(by
        have := L.hmaxV; have := L.hacap
        rw [hscr, ← hL]; unfold K6Layout.scrLen K6Layout.k6Base K6Layout.phtMerged; omega)) := by
  rw [pht_merged_ptr]; exact load_pht_merged hL hscr hi hm

@[scoped c0_load] theorem load_pht_merged_bv32 {c : FullCfg} {L : K6Layout} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {idx : BitVec 32}
    (hL : L.scrLen = c.scratch_cap) (hscr : s.scratch.scratch_buf.length = c.scratch_cap)
    (hi : idx.toNat < L.maxV) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32
        ((c.pScratchBuf + (1280#32 + L.mv32).setWidth 64 * 4) + idx.setWidth 64 * 4) =
      some (s.scratch.scratch_buf[L.phtMerged + idx.toNat]'(by
        have := L.hmaxV; have := L.hacap
        rw [hscr, ← hL]; unfold K6Layout.scrLen K6Layout.k6Base K6Layout.phtMerged; omega)) :=
  load_pht_merged_32 hL hscr hi hm

@[scoped c0_store] theorem store_pht_merged {c : FullCfg} {L : K6Layout} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) {idx : BitVec 32}
    (hL : L.scrLen = c.scratch_cap) (hscr : s.scratch.scratch_buf.length = c.scratch_cap)
    (hi : idx.toNat < L.maxV) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 ((c.pScratchBuf + BitVec.ofNat 64 (4 * L.phtMerged)) + idx.setWidth 64 * 4) ∧
      (FullMem c { s with scratch := { s.scratch with
        scratch_buf := s.scratch.scratch_buf.set (L.phtMerged + idx.toNat) v } } ⋆ R)
        (storeMem m i32
          ((c.pScratchBuf + BitVec.ofNat 64 (4 * L.phtMerged)) + idx.setWidth 64 * 4) v) := by
  have := L.hmaxV
  rw [pht_ptr_add c.pScratchBuf (by unfold K6Layout.phtMerged; omega) (by omega)]
  exact store_full_scratch_buf v (by
    have := L.hmaxV; have := L.hacap
    rw [hscr, ← hL]; unfold K6Layout.scrLen K6Layout.k6Base K6Layout.phtMerged; omega) hm

@[scoped c0_store] theorem store_pht_merged_32 {c : FullCfg} {L : K6Layout} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) {idx : BitVec 32}
    (hL : L.scrLen = c.scratch_cap) (hscr : s.scratch.scratch_buf.length = c.scratch_cap)
    (hi : idx.toNat < L.maxV) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32
        ((c.pScratchBuf + ((1280 : BitVec 32) + L.mv32).setWidth 64 * 4) +
          idx.setWidth 64 * 4) ∧
      (FullMem c { s with scratch := { s.scratch with
        scratch_buf := s.scratch.scratch_buf.set (L.phtMerged + idx.toNat) v } } ⋆ R)
        (storeMem m i32
          ((c.pScratchBuf + ((1280 : BitVec 32) + L.mv32).setWidth 64 * 4) +
            idx.setWidth 64 * 4) v) := by
  rw [pht_merged_ptr]; exact store_pht_merged v hL hscr hi hm

@[scoped c0_store] theorem store_pht_merged_bv32 {c : FullCfg} {L : K6Layout} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) {idx : BitVec 32}
    (hL : L.scrLen = c.scratch_cap) (hscr : s.scratch.scratch_buf.length = c.scratch_cap)
    (hi : idx.toNat < L.maxV) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32
        ((c.pScratchBuf + (1280#32 + L.mv32).setWidth 64 * 4) + idx.setWidth 64 * 4) ∧
      (FullMem c { s with scratch := { s.scratch with
        scratch_buf := s.scratch.scratch_buf.set (L.phtMerged + idx.toNat) v } } ⋆ R)
        (storeMem m i32
          ((c.pScratchBuf + (1280#32 + L.mv32).setWidth 64 * 4) + idx.setWidth 64 * 4) v) :=
  store_pht_merged_32 v hL hscr hi hm

end M6PhtMem

namespace M6ElsBv

@[scoped bv_c0] theorem m6_els_bv8_eq0 (v : BitVec 8) :
    (v.signExtend 32 == 0#32) = (v == 0#8) := by
  revert v; decide

@[scoped bv_c0] theorem m6_els_bv64_shl1_bv (v : BitVec 64) :
    (v <<< 1#64).toNat = 2 * v.toNat % 2 ^ 64 := by
  rw [show (v <<< 1#64) = v <<< (1 : Nat) from rfl, BitVec.toNat_shiftLeft,
    Nat.shiftLeft_eq, Nat.mul_comm]

end M6ElsBv

/-! ## 2. Callee Wrappers & `K6State` / `FullMem` Slab Helpers -/

theorem m6_call_max_v {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hMaxV : Γ.Has "full_m6_max_v" m6MaxVSpec)
    {c : FullCfg} {m : Mem 64} {k : Tup Val [i64] → Expr Val Cont rs}
    (hcap : c.scratch_cap < 2 ^ 64)
    (hk : wp Γ Q X (k (BitVec.ofNat 64 (k6MaxV c.scratch_cap), ())) m) :
    wp Γ Q X (.call (as := [i64]) (bs := [i64]) "full_m6_max_v"
      (Arg.var (BitVec.ofNat 64 c.scratch_cap), ()) k) m :=
  k6_maxV_call_step hMaxV hcap hk

theorem m6_join_k6_ofSlab {c : FullCfg} {L : K6Layout} {s : FullState} {ks' : K6State}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hL : L.scrLen = c.scratch_cap) (hs : s.scratch.scratch_buf.length = c.scratch_cap)
    (hsh : ks'.ShapesOk L)
    (hm : (K6MemA L (L.kPtr c.pScratchBuf) ks' ⋆ (FullK6Frame c L s ⋆ R)) m) :
    let scr' := s.scratch.scratch_buf.take L.k6Base ++ ks'.toSlab
    let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
    scr'.length = c.scratch_cap ∧
    (∀ i < L.k6Base, scr'[i]? = s.scratch.scratch_buf[i]?) ∧
    k6StateOfScratch L scr' = ks' ∧ (FullMem c s' ⋆ R) m := by
  intro scr' s'
  have hmL := L.hmaxV; have hac := L.hacap
  have hkb_le : L.k6Base ≤ s.scratch.scratch_buf.length := by
    rw [hs, ← hL]; unfold K6Layout.scrLen K6Layout.k6Base; omega
  have htk : (s.scratch.scratch_buf.take L.k6Base).length = L.k6Base :=
    List.length_take_of_le hkb_le
  have hsl : scr'.length = c.scratch_cap := by
    dsimp only [scr']
    rw [List.length_append, htk, ks'.toSlab_length hsh, ← hL]
    unfold K6Layout.scrLen; omega
  have hpre : ∀ i < L.k6Base, scr'[i]? = s.scratch.scratch_buf[i]? := fun i hi => by
    dsimp only [scr']
    rw [List.getElem?_append_left (by rw [htk]; exact hi), List.getElem?_take_of_lt hi]
  have hof : k6StateOfScratch L scr' = ks' := by
    unfold k6StateOfScratch; dsimp only [scr']
    rw [k6_slab_drop_exact _ _ htk]; exact K6State.ofSlab_toSlab hsh
  obtain ⟨_, hkm⟩ := k6MemA_to_mem hm
  exact ⟨hsl, hpre, hof, fullMem_join_k6 hkb_le hsh (sep_ac hkm)⟩

theorem m6_k6Ptr_eq {c : FullCfg} {L : K6Layout} (hLmv : L.maxV = k6MaxV c.scratch_cap)
    (hmv_lt : k6MaxV c.scratch_cap < 2 ^ 30) :
    c.pScratchBuf + ((1280 : BitVec 32) +
        ((BitVec.ofNat 64 (k6MaxV c.scratch_cap)).setWidth 32 <<< (1 : Nat))).setWidth 64 * 4 =
      L.kPtr c.pScratchBuf := by
  have hmv_eq : (BitVec.ofNat 64 (k6MaxV c.scratch_cap)).setWidth 32 = L.mv32 := by
    apply BitVec.eq_of_toNat_eq
    simp only [k6_mv32_toNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [← hLmv]; omega
  rw [hmv_eq]; exact k6_ptr_base L c.pScratchBuf

theorem m6_k6Layout_congr {cap1 cap2 : Nat} (heq : cap1 = cap2)
    (h1 : k6MinScr ≤ cap1) (hl1 : cap1 < dimacsBound)
    (h2 : k6MinScr ≤ cap2) (hl2 : cap2 < dimacsBound) :
    k6LayoutOfCap cap1 h1 hl1 = k6LayoutOfCap cap2 h2 hl2 := by
  subst heq; exact K6Layout.eq_of_scrLen_maxV rfl rfl

/-! ## 3. Pure BitVec, List, XOR, & Semantic Entailment Helpers -/

theorem m6_bv32_add1 {x : BitVec 32} (h : x.toNat < 2 ^ 31) :
    (x + 1#32).toNat = x.toNat + 1 := by bv_omega

theorem m6_bv64_add1 {x : BitVec 64} (h : x.toNat < 2 ^ 63) :
    (x + 1#64).toNat = x.toNat + 1 := by bv_omega

theorem m6_bv32_shr1_toNat (x : BitVec 32) : (x >>> (1 : Nat)).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem m6_bv32_and1_toNat (x : BitVec 32) : (x &&& 1#32).toNat = x.toNat % 2 := by
  rw [BitVec.toNat_and, show (1#32).toNat = 1 from rfl]
  simp [Nat.and_two_pow_sub_one_eq_mod x.toNat 1]

theorem m6_bv32_shl1_lt {v : BitVec 32} (hv : v.toNat < 2 ^ 31) :
    (v <<< (1 : Nat)).toNat = 2 * v.toNat := by bv_omega

theorem m6_bv32_shl1_or_pol (v pol : BitVec 32) (hv : v.toNat < 2 ^ 31) (hp : pol.toNat < 2) :
    ((v <<< (1 : Nat)) ||| pol).toNat = 2 * v.toNat + pol.toNat := by
  have h1 : (v <<< (1 : Nat)).toNat = 2 * v.toNat := m6_bv32_shl1_lt hv
  rcases (by omega : pol.toNat = 0 ∨ pol.toNat = 1) with h0 | h1p
  · have hp0 : pol = 0#32 := BitVec.eq_of_toNat_eq h0
    rw [hp0, BitVec.or_zero, h1, show (0#32).toNat = 0 from rfl]; omega
  · have hp1 : pol = 1#32 := BitVec.eq_of_toNat_eq h1p
    rw [hp1, BitVec.toNat_or, h1, show (1#32).toNat = 1 from rfl]
    apply Nat.eq_of_testBit_eq; intro i; cases i with
    | zero => simp [Nat.testBit_zero]
    | succ j =>
      rw [Nat.testBit_or, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ,
        show (1 : Nat) / 2 = 0 from rfl, show (2 * v.toNat) / 2 = v.toNat by omega,
        show (2 * v.toNat + 1) / 2 = v.toNat by omega, Nat.zero_testBit, Bool.or_false]

theorem m6_bv32_shl1_or_and1 (t l : BitVec 32) (ht : t.toNat < 2 ^ 31) :
    ((t <<< (1 : Nat)) ||| (l &&& 1#32)).toNat = 2 * t.toNat + l.toNat % 2 := by
  have h1 : (l &&& 1#32).toNat < 2 := by rw [m6_bv32_and1_toNat]; omega
  simpa [m6_bv32_and1_toNat] using m6_bv32_shl1_or_pol t (l &&& 1#32) ht h1

theorem m6_bv32_add1_sub1_eq (x : BitVec 32) : x + 1#32 - 1#32 = x := by bv_omega

theorem m6_bv32_ofNat_add1 (x : BitVec 32) :
    BitVec.ofNat 32 (x.toNat + 1) = x + 1#32 := by bv_omega

theorem m6_bv64_shl1 (x : BitVec 32) :
    (x.setWidth 64 <<< (1 : Nat)).toNat = 2 * x.toNat :=
  M6SweepTactics.m6_bv64_shl1_bv x

theorem m6_bv64_shl1_add1 (x : BitVec 32) :
    ((x.setWidth 64 <<< (1 : Nat)) + 1#64).toNat = 2 * x.toNat + 1 :=
  M6SweepTactics.m6_bv64_shl1_add1_bv x

theorem m6_pol_01 (pa pc : BitVec 32) :
    let pol := (pa &&& 1#32) ^^^ (pc &&& 1#32)
    pol = 0#32 ∨ pol = 1#32 := by
  intro pol
  have h1 : ∀ x : BitVec 32, (x &&& 1#32) = 0#32 ∨ (x &&& 1#32) = 1#32 := fun x => by
    have ht : (x &&& 1#32).toNat < 2 := by rw [m6_bv32_and1_toNat]; omega
    rcases (by omega : (x &&& 1#32).toNat = 0 ∨ (x &&& 1#32).toNat = 1) with h0 | h1
    · exact Or.inl (BitVec.eq_of_toNat_eq h0)
    · exact Or.inr (BitVec.eq_of_toNat_eq h1)
  rcases h1 pa with ha | ha <;> rcases h1 pc with hc | hc <;> simp [pol, ha, hc]

theorem m6_getElem_eq_getD {α : Type} (xs : List α) {i : Nat}
    (h : i < xs.length) (d : α) : xs[i]'h = xs[i]?.getD d := by
  rw [List.getElem?_eq_getElem h, Option.getD_some]

theorem m6_list_getElem_congr {α : Type} {xs : List α} {i j : Nat}
    (hij : i = j) (hi : i < xs.length) (hj : j < xs.length) :
    xs[i]'hi = xs[j]'hj := by subst hij; rfl

theorem m6_list_drop_set_lt {α : Type _} (xs : List α) {k i : Nat} (v : α) (hik : i < k) :
    (xs.set i v).drop k = xs.drop k := by
  apply List.ext_getElem
  · simp
  · intro j _ _; simp only [List.getElem_drop]; rw [List.getElem_set_ne (by omega)]

theorem m6_list_drop_set_ge {α : Type _} (xs : List α) {k i : Nat} (v : α) (hki : k ≤ i) :
    (xs.set i v).drop k = (xs.drop k).set (i - k) v := by
  apply List.ext_getElem
  · simp
  · intro j _ _
    simp only [List.getElem_drop]
    by_cases hji : j = i - k
    · subst hji; simp only [show k + (i - k) = i by omega, List.getElem_set_self]
    · rw [List.getElem_set_ne (by omega), List.getElem_set_ne (Ne.symm hji), List.getElem_drop]

theorem m6_list_take_set_lt {α : Type _} (xs : List α) {n i : Nat} (v : α) (hin : i < n) :
    (xs.set i v).take n = (xs.take n).set i v := by
  apply List.ext_getElem
  · simp
  · intro j _ _
    by_cases hji : j = i
    · subst hji; rw [List.getElem_take, List.getElem_set_self, List.getElem_set_self]
    · rw [List.getElem_take, List.getElem_set_ne (Ne.symm hji),
        List.getElem_set_ne (Ne.symm hji), List.getElem_take]

theorem m6_list_take_set_ge {α : Type _} (xs : List α) {n i : Nat} (v : α) (hni : n ≤ i) :
    (xs.set i v).take n = xs.take n := by
  apply List.ext_getElem
  · simp
  · intro j hj1 _
    have hj : j < n := by simp at hj1; omega
    simp only [List.getElem_take]; rw [List.getElem_set_ne (by omega)]

theorem m6_inj_lt_of_missing (f : Nat → Nat) {n m x : Nat}
    (hinj : ∀ i j, i < n → j < n → f i = f j → i = j)
    (hlt : ∀ i < n, f i < m) (hx : x < m) (hmiss : ∀ i < n, f i ≠ x) : n < m := by
  let xs := (List.range n).map f
  have hnd : xs.Nodup := List.pairwise_iff_getElem.mpr fun i j hi hj hij => by
    simp only [xs, List.length_map, List.length_range] at hi hj
    simp only [xs, List.getElem_map, List.getElem_range]
    exact fun heq => Nat.ne_of_lt hij (hinj i j hi hj heq)
  have hnot : x ∉ xs := by
    intro hm; obtain ⟨i, hi, heq⟩ := List.mem_map.mp hm
    rw [List.mem_range] at hi; exact hmiss i hi heq
  have hle := k6_nodup_subset_length (List.nodup_cons.mpr ⟨hnot, hnd⟩) fun y hy => by
    rcases List.mem_cons.mp hy with rfl | hy'
    · exact hx
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy'
      rw [List.mem_range] at hi; exact hlt i hi
  simp only [xs, List.length_cons, List.length_map, List.length_range] at hle
  omega

theorem m6_nat_xor1_cases (x : Nat) : x ^^^ 1 = if x % 2 = 0 then x + 1 else x - 1 :=
  nat_xor1_eq x

theorem m6_nat_xor1_even (k : Nat) : (2 * k) ^^^ 1 = 2 * k + 1 := by
  rw [nat_xor1_eq, Nat.mul_mod_right]; rfl

theorem m6_nat_xor1_odd (k : Nat) : (2 * k + 1) ^^^ 1 = 2 * k := by
  rw [nat_xor1_eq]; split <;> omega

theorem m6_nat_xor1_lt {x N : Nat} (hx : x < 2 * N) : x ^^^ 1 < 2 * N :=
  nat_xor1_lt hx

theorem m6_xor1_div2 (x : Nat) : (x ^^^ 1) / 2 = x / 2 := litVar_litNeg x

theorem m6_xor1_xor1 (x : Nat) : (x ^^^ 1) ^^^ 1 = x := litNeg_litNeg x

theorem m6_pack_nv_nc (nv nc : BitVec 32) (hnv : nv.toNat ≤ 8192) (hnc : nc.toNat ≤ 24576) :
    let r := nv.setWidth 64 ||| (nc.setWidth 64 <<< (16 : Nat))
    (r &&& 0xFFFF#64).toNat = nv.toNat ∧
    (r >>> (16 : Nat)).toNat = nc.toNat ∧
    r.toNat = nv.toNat + nc.toNat * 2 ^ 16 := by
  intro r
  have hlt16 : ∀ {x : Nat}, x < 2 ^ 16 → ∀ j, 16 ≤ j → x.testBit j = false := fun hx j hj =>
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) hj))
  have hmask : ∀ j, Nat.testBit 65535 j = decide (j < 16) := fun j => by
    rw [show (65535 : Nat) = 2 ^ 16 - 1 from rfl, Nat.testBit_two_pow_sub_one]
  have h1 : (r &&& 0xFFFF#64) = nv.setWidth 64 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [r, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_setWidth, BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and, hmask]
    by_cases h16 : i < 16
    · have h32 : i < 32 := by omega
      simp [h16, h32]
    · simp only [h16, decide_false, Bool.and_false]
      rw [BitVec.getLsbD]; exact (hlt16 (by omega : nv.toNat < 2 ^ 16) i (by omega)).symm
  have h2 : (r >>> (16 : Nat)) = nc.setWidth 64 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [r, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_setWidth]
    by_cases h64 : 16 + i < 64
    · simp only [h64, decide_true, Bool.true_and, show 16 + i - 16 = i by omega]
      rw [BitVec.getLsbD, hlt16 (by omega : nv.toNat < 2 ^ 16) (16 + i) (by omega), Bool.false_or]
      by_cases hi32 : i < 32
      · simp [hi, hi32]
      · have hf := hlt16 (by omega : nc.toNat < 2 ^ 16) i (by omega)
        simp [BitVec.getLsbD, hf]
    · have hf := hlt16 (by omega : nc.toNat < 2 ^ 16) i (by omega)
      simp [h64, BitVec.getLsbD, hf]
  have hr_sum_bv : r = BitVec.ofNat 64 (nv.toNat + nc.toNat * 2 ^ 16) := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [r, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and]
    change _ = Nat.testBit (nv.toNat + nc.toNat * 2 ^ 16) i
    rw [show nv.toNat + nc.toNat * 2 ^ 16 = 2 ^ 16 * nc.toNat + nv.toNat by omega,
      Nat.testBit_two_pow_mul_add _ (by omega : nv.toNat < 2 ^ 16)]
    by_cases h16 : i < 16
    · simp [h16, BitVec.getLsbD]
    · have hge : 16 ≤ i := by omega
      have hsub : i - 16 < 64 := by omega
      have hfn := hlt16 (by omega : nv.toNat < 2 ^ 16) i hge
      rw [BitVec.getLsbD, hfn, Bool.false_or]
      simp only [h16, hsub, decide_false, decide_true, Bool.not_false, Bool.true_and]
      by_cases h32 : i - 16 < 32
      · simp [BitVec.getLsbD]
      · have hfc := hlt16 (by omega : nc.toNat < 2 ^ 16) (i - 16) (by omega)
        simp [BitVec.getLsbD, hfc]
  refine ⟨by rw [h1, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)],
    by rw [h2, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)],
    by rw [hr_sum_bv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]⟩

/-! ## 4. Cone Lifting, Trail, & Semantic Entailment Helpers -/

@[expose] def m6ConeLift (cone_v : List (BitVec 32)) (l : Nat) : Nat :=
  (cone_v[l / 2]?.getD 0#32).toNat * 2 + l % 2

theorem coneLift_of_tmk_pair {cone_v : List (BitVec 32)} {idx v l : Nat}
    (hw : (cone_v[idx]?.getD 0#32).toNat = v) (hl : l / 2 = v) :
    m6ConeLift cone_v (2 * idx + l % 2) = l := by
  unfold m6ConeLift
  rw [show (2 * idx + l % 2) / 2 = idx by omega,
    show (2 * idx + l % 2) % 2 = l % 2 by omega, hw]
  omega

theorem coneLift_sat_iff {cone_v : List (BitVec 32)} {α : Nat → Bool} {l : Nat} :
    (cnfClause [l]).Sat (fun i => α (cone_v[i]?.getD 0#32).toNat) ↔
      (cnfClause [m6ConeLift cone_v l]).Sat α := by
  simp only [sat_cnfClause_singleton, m6ConeLift, litVar, litSign]
  have hd : ((cone_v[l / 2]?.getD 0#32).toNat * 2 + l % 2) / 2 =
      (cone_v[l / 2]?.getD 0#32).toNat := by omega
  have hm : ((cone_v[l / 2]?.getD 0#32).toNat * 2 + l % 2) % 2 = l % 2 := by omega
  rw [hd, hm]

theorem semEntails_coneModelSet_of_entails {F_cur : List (List Nat)}
    {ws1 : List (BitVec 32)} {nv : Nat} {lits : List Nat}
    (hlts : ∀ l ∈ lits, l < 2 * nv)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause (lits.map (m6ConeLift ws1)))) :
    SemEntails (ConeModelSet F_cur ws1 nv) lits := by
  intro β ⟨α, hα, hβ⟩
  have hsat := (CNF.entails_clause_def.mp hent) α hα
  rw [clause_sat_cnfClause_iff] at hsat ⊢
  obtain ⟨gl, hgl_m, hgl_s⟩ := hsat
  obtain ⟨l, hl_m, rfl⟩ := List.mem_map.mp hgl_m
  refine ⟨l, hl_m, ?_⟩
  have hl_lt := hlts l hl_m
  have hvar : litVar (m6ConeLift ws1 l) = (ws1[l / 2]?.getD 0#32).toNat := by
    unfold litVar m6ConeLift; omega
  have hsign : litSign (m6ConeLift ws1 l) = litSign l := by
    unfold litSign m6ConeLift; simp [Nat.add_mod]
  rw [hvar, hsign] at hgl_s
  rw [show litVar l = l / 2 from rfl, hβ (l / 2) (by omega)]
  exact hgl_s

theorem coneModelSet_mono_nv {F_cur : List (List Nat)} {ws1 ws1' : List (BitVec 32)}
    {n1 n2 : Nat} (hle : n1 ≤ n2) (heq : ∀ i < n1, ws1'[i]? = ws1[i]?)
    {β : Nat → Bool} (h : ConeModelSet F_cur ws1' n2 β) :
    ConeModelSet F_cur ws1 n1 β := by
  obtain ⟨α, hα, hβ⟩ := h
  refine ⟨α, hα, fun i hi => ?_⟩
  have h1 := hβ i (by omega); rwa [heq i hi] at h1

theorem m6_lvl0_false_not_sat {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hcl0 : k.cur_level = 0)
    {l : Nat} (hlt : l < 2 * k.cur_vars) (hfalse : k.vals[l]?.getD 0#8 = 0xFF#8)
    {α : Nat → Bool} (hα : (cnfOfClauses F_cur).Sat α) : ¬ (cnfClause [l]).Sat α := by
  obtain ⟨idx, hidx, htrl⟩ := (hw.vals_false_iff l hlt).mp hfalse
  have hlvl0 : (k.lvl[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
    have := hw.lvl_le idx hidx; omega
  have hent := hw.level0_sound idx hidx hlvl0
  rw [htrl, CNF.entails_clause_def] at hent
  have hneg : (cnfClause [litNeg l]).Sat α := hent α hα
  simp only [sat_cnfClause_singleton, litVar_litNeg, litSign_litNeg] at hneg ⊢
  intro hsat; rw [hsat] at hneg; cases hb : litSign l <;> simp [hb] at hneg

theorem m6_lvl0_false_entails {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hcl0 : k.cur_level = 0)
    {l : Nat} (hlt : l < 2 * k.cur_vars) (hf : k.vals[l]?.getD 0#8 = 0xFF#8) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [l ^^^ 1]) := by
  obtain ⟨i, hi, htrl⟩ := (hw.vals_false_iff l hlt).mp hf
  have hl0 : (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
    have := hw.lvl_le i hi; omega
  have hent := hw.level0_sound i hi hl0; rwa [htrl] at hent

theorem m6_lvl0_true_entails {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hcl0 : k.cur_level = 0)
    {l : Nat} (hlt : l < 2 * k.cur_vars) (ht : k.vals[l]?.getD 0#8 = 1#8) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [l]) := by
  obtain ⟨i, hi, htrl⟩ := (hw.vals_true_iff l hlt).mp ht
  have hl0 : (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
    have := hw.lvl_le i hi; omega
  have hent := hw.level0_sound i hi hl0; rwa [htrl] at hent

theorem m6_litEquiv_neg {f : CNF Nat} {a b : Nat} (h : LitEquiv f a b) :
    LitEquiv f (a ^^^ 1) (b ^^^ 1) := by
  constructor
  · have h1 := h.2
    rw [CNF.entails_clause_def] at h1 ⊢; intro α hα
    have h2 := (clauseEvalVal_iff α _).mpr (h1 α hα)
    rw [← clauseEvalVal_iff]
    simp only [clauseEvalVal, List.any_cons, List.any_nil, Bool.or_false,
      show a ^^^ 1 = litNeg a from rfl, show b ^^^ 1 = litNeg b from rfl,
      litNeg_litNeg] at h2 ⊢
    simpa [Bool.or_comm] using h2
  · have h1 := h.1
    rw [CNF.entails_clause_def] at h1 ⊢; intro α hα
    have h2 := (clauseEvalVal_iff α _).mpr (h1 α hα)
    rw [← clauseEvalVal_iff]
    simp only [clauseEvalVal, List.any_cons, List.any_nil, Bool.or_false,
      show a ^^^ 1 = litNeg a from rfl, show b ^^^ 1 = litNeg b from rfl,
      litNeg_litNeg] at h2 ⊢
    simpa [Bool.or_comm] using h2

theorem m6_litEquiv_unsat_contra {f : CNF Nat} {a b : Nat}
    (heq : LitEquiv f a b) (ha : f.EntailsClause (cnfClause [a]))
    (hb : f.EntailsClause (cnfClause [b ^^^ 1])) : f.Unsat := by
  rw [CNF.unsat_iff_not_sat]; intro β hβ
  have h1 := litEquiv_eval hβ heq
  have h2 := (clauseEvalVal_iff β _).mpr (CNF.entails_clause_def.mp ha β hβ)
  have h3 := (clauseEvalVal_iff β _).mpr (CNF.entails_clause_def.mp hb β hβ)
  simp only [clauseEvalVal, List.any_cons, List.any_nil, Bool.or_false,
    show b ^^^ 1 = litNeg b from rfl, evalLitVal_litNeg] at h2 h3
  rw [h1] at h2; rw [h2] at h3; cases h3

theorem m6_entails_bin_subst {f : CNF Nat} {a b a' b' : Nat}
    (ha : LitEquiv f a a') (hb : LitEquiv f b b')
    (hc : f.EntailsClause (cnfClause [a, b])) :
    f.EntailsClause (cnfClause [a', b']) := by
  rw [CNF.entails_clause_def] at hc ⊢; intro α hα
  have h1 := (clauseEvalVal_iff α _).mpr (hc α hα)
  rw [← clauseEvalVal_iff]
  simp only [clauseEvalVal, List.any_cons, List.any_nil, Bool.or_false] at h1 ⊢
  rw [← litEquiv_eval hα ha, ← litEquiv_eval hα hb]; exact h1

theorem m6_entails_unit_of_dup {f : CNF Nat} {a : Nat}
    (hc : f.EntailsClause (cnfClause [a, a])) : f.EntailsClause (cnfClause [a]) := by
  rw [CNF.entails_clause_def] at hc ⊢; intro α hα
  have h1 := (clauseEvalVal_iff α _).mpr (hc α hα)
  rw [← clauseEvalVal_iff]
  simp only [clauseEvalVal, List.any_cons, List.any_nil, Bool.or_false] at h1 ⊢
  simpa using h1

theorem m6_unsat_of_nil_entails {f : CNF Nat} (h : f.EntailsClause (cnfClause [])) :
    f.Unsat := by
  rw [CNF.unsat_iff_not_sat]; intro α hα
  have := (clauseEvalVal_iff α _).mpr (CNF.entails_clause_def.mp h α hα)
  simp [clauseEvalVal] at this

/-! ## 5. `K6Inv`, `K6TailEq`, `FullDenseInvW`, & Watch/EqBuf/Repr Helpers -/

theorem m6_trl_end_le_of_bdd {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State} {nv : Nat}
    (hinv : K6Inv L P ks) (htrl_bdd : ∀ l ∈ k6TrailLits ks, l < 2 * nv) :
    ks.trl_end.toNat ≤ nv := by
  have hm := L.hmaxV
  have hte_le := hinv.assign.trl_end_le
  have hnv := hinv.clauses.nv_le
  have hte_len : ks.trl_end.toNat ≤ ks.trl.length := by rw [hinv.shapes.trl_len]; omega
  have hle := k6_nodup_subset_length (n := nv) hinv.assign.trl_nodup fun v hv => by
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hv
    have := htrl_bdd l hl; omega
  unfold k6TrailLits at hle
  simpa [List.length_map, List.length_take, Nat.min_eq_left hte_len] using hle

theorem k6TailEq_putArr_var {L : K6Layout} {ks : K6State} {f : K6ArrField}
    (hf : f = .lvlArr ∨ f = .rsn ∨ f = .flags) {i : Nat} (hi : i < ks.nv.toNat)
    (val : BitVec 32) : K6TailEq L ks (ks.putArr f i val) := by
  refine ⟨by cases f <;> rfl, fun v hv _ => ?_⟩
  have hne : i ≠ v := by omega
  rcases hf with rfl | rfl | rfl <;> dsimp only [K6State.putArr]
  · exact ⟨List.getElem?_set_ne hne, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, List.getElem?_set_ne hne, rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, List.getElem?_set_ne hne, rfl, rfl, rfl, rfl⟩

private theorem m6_fl_bit0_and2 (fl b : BitVec 32) (h : (fl &&& 2#32) = 0#32) :
    (((fl &&& ~~~1#32) ||| (b &&& 1#32)) &&& 2#32) = 0#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  have hk0 := congrArg (·.getLsbD k) h
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not,
    BitVec.getLsbD_zero, hk, decide_true, Bool.true_and] at hk0 ⊢
  cases k with
  | zero => simp
  | succ k =>
    cases k with
    | zero => simpa using hk0
    | succ k =>
      have hf : Nat.testBit 2 (k + 2) = false :=
        Nat.testBit_lt_two_pow
          (by have := Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 2 ≤ k + 2); omega)
      simp [BitVec.getLsbD, hf]

theorem k6Inv_set_flags_bit0 {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    {i : Nat} (hi : i < L.maxV) (b : BitVec 32) (hinv : K6Inv L P ks) :
    let v := (ks.flags[i]?.getD 0#32 &&& ~~~1#32) ||| (b &&& 1#32)
    K6Inv L P (ks.putArr .flags i v) := by
  intro v
  have hcl := hinv.clauses
  refine ⟨hinv.shapes.putArr .flags i v,
    { acap_eq := hcl.acap_eq, max_v_eq := hcl.max_v_eq, max_orig_eq := hcl.max_orig_eq,
      max_cl_eq := hcl.max_cl_eq, nv_le := hcl.nv_le, nc_le := hcl.nc_le, alen_le := hcl.alen_le,
      nassump_le := hcl.nassump_le, nkl_le := hcl.nkl_le, nana_le := hcl.nana_le,
      cl_wf := hcl.cl_wf, cl_mono := hcl.cl_mono, incons_ok := hcl.incons_ok,
      assump_ok := hcl.assump_ok,
      flags_clean := fun u hu => by
        change (((ks.flags).set i v)[u]?.getD 0#32 &&& 2#32) = 0#32
        by_cases hui : u = i
        · subst hui
          rw [List.getElem?_set_self (by rw [hinv.shapes.flags_len]; exact hi), Option.getD_some]
          exact m6_fl_bit0_and2 _ _ (hcl.flags_clean u hu)
        · rw [List.getElem?_set_ne (Ne.symm hui)]; exact hcl.flags_clean u hu },
    by dsimp only [K6State.putArr]; exact hinv.watches,
    k6BaseAssignOk_cast hinv.assign (by k6_field) (by k6_field) (by k6_field) (by k6_field)
      (by k6_field) (by k6_field) (by k6_field) (by k6_field) (by k6_field),
    by dsimp only [K6State.putArr]; exact hinv.reasons⟩

theorem k6Inv_set_phase {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (v : BitVec 32) (hinv : K6Inv L P ks) : K6Inv L P (ks.putHdr .phase v) :=
  ⟨hinv.shapes.putHdr .phase v,
   k6ClausesOk_cast hinv.clauses,
   by dsimp only [K6State.putHdr]; exact hinv.watches,
   k6BaseAssignOk_cast hinv.assign (by k6_field) (by k6_field) (by k6_field) (by k6_field)
     (by k6_field) (by k6_field) (by k6_field) (by k6_field) (by k6_field),
   by dsimp only [K6State.putHdr]; exact hinv.reasons⟩

theorem k6Inv_set_nassump0 {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (hinv : K6Inv L P ks) : K6Inv L P (ks.putHdr .nassump 0#32) :=
  have hcl := hinv.clauses
  ⟨hinv.shapes.putHdr .nassump 0#32,
   { acap_eq := hcl.acap_eq, max_v_eq := hcl.max_v_eq, max_orig_eq := hcl.max_orig_eq,
     max_cl_eq := hcl.max_cl_eq, nv_le := hcl.nv_le, nc_le := hcl.nc_le, alen_le := hcl.alen_le,
     nassump_le := by dsimp only [K6State.putHdr]; simp,
     nkl_le := hcl.nkl_le, nana_le := hcl.nana_le, cl_wf := hcl.cl_wf, cl_mono := hcl.cl_mono,
     incons_ok := hcl.incons_ok,
     assump_ok := fun i hi => by dsimp only [K6State.putHdr] at hi; simp at hi,
     flags_clean := hcl.flags_clean },
   by dsimp only [K6State.putHdr]; exact hinv.watches,
   k6BaseAssignOk_cast hinv.assign (by k6_field) (by k6_field) (by k6_field) (by k6_field)
     (by k6_field) (by k6_field) (by k6_field) (by k6_field) (by k6_field),
   by dsimp only [K6State.putHdr]; exact hinv.reasons⟩

theorem k6PutHdr25_inv {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (v : BitVec 32) (hinv : K6Inv L P ks) : K6Inv L P (k6PutHdr25 ks v) :=
  ⟨k6PutHdr25_shapes hinv.shapes v,
   k6ClausesOk_cast hinv.clauses,
   by dsimp only [k6PutHdr25]; exact hinv.watches,
   k6BaseAssignOk_cast hinv.assign rfl rfl rfl rfl rfl rfl rfl rfl rfl,
   by dsimp only [k6PutHdr25]; exact hinv.reasons⟩

theorem m6_k6StateOfScratch_set25 (L : K6Layout) (scr : List (BitVec 32)) (v : BitVec 32)
    (hlen : L.scrLen = scr.length) :
    k6StateOfScratch L (scr.set (L.k6Base + 25) v) =
      k6PutHdr25 (k6StateOfScratch L scr) v := by
  have hm := L.hmaxV; have ha := L.hacap
  have hbd : L.k6Base + 25 < scr.length := by
    rw [← hlen]; unfold K6Layout.scrLen K6Layout.k6Fixed; omega
  have hdrop : (scr.set (L.k6Base + 25) v).drop L.k6Base =
      (scr.drop L.k6Base).set 25 v := by
    rw [m6_list_drop_set_ge scr v (Nat.le_add_right _ _)]
    simp
  have hsub : ∀ i, i < 25 →
      ((scr.drop L.k6Base).set 25 v)[i]?.getD 0#32 = (scr.drop L.k6Base)[i]?.getD 0#32 := by
    intro i hi; rw [List.getElem?_set_ne (by omega)]
  have htail : (((scr.drop L.k6Base).set 25 v).drop 25).take 7 =
      (((scr.drop L.k6Base).drop 25).take 7).set 0 v := by
    rw [m6_list_drop_set_ge _ v (Nat.le_refl _), Nat.sub_self, m6_list_take_set_lt _ v (by decide)]
  have hdl : ∀ k, 25 < k →
      ((scr.drop L.k6Base).set 25 v).drop k = (scr.drop L.k6Base).drop k :=
    fun k hk => m6_list_drop_set_lt _ v hk
  unfold k6StateOfScratch K6State.ofSlab k6PutHdr25
  rw [hdrop]
  simp only [hsub 0 (by decide), hsub 1 (by decide), hsub 2 (by decide), hsub 3 (by decide),
    hsub 4 (by decide), hsub 5 (by decide), hsub 6 (by decide), hsub 7 (by decide),
    hsub 8 (by decide), hsub 9 (by decide), hsub 10 (by decide), hsub 11 (by decide),
    hsub 12 (by decide), hsub 13 (by decide), hsub 14 (by decide), hsub 15 (by decide),
    hsub 16 (by decide), hsub 17 (by decide), hsub 18 (by decide), hsub 19 (by decide),
    hsub 20 (by decide), hsub 21 (by decide), hsub 22 (by decide), hsub 23 (by decide),
    hsub 24 (by decide), htail,
    hdl L.oLvl (by unfold K6Layout.oLvl; decide),
    hdl L.oRsn (by unfold K6Layout.oRsn; omega),
    hdl L.oQPrev (by unfold K6Layout.oQPrev; omega),
    hdl L.oQNext (by unfold K6Layout.oQNext; omega),
    hdl L.oQStamp (by unfold K6Layout.oQStamp; omega),
    hdl L.oTrl (by unfold K6Layout.oTrl; omega),
    hdl L.oFlags (by unfold K6Layout.oFlags; omega),
    hdl L.oAna (by unfold K6Layout.oAna; omega),
    hdl L.oKl (by unfold K6Layout.oKl; omega),
    hdl L.oAssump (by unfold K6Layout.oAssump; omega),
    hdl L.oVals (by unfold K6Layout.oVals; omega),
    hdl L.oWHead (by unfold K6Layout.oWHead; omega),
    hdl L.oWNext (by unfold K6Layout.oWNext; omega),
    hdl L.oWBlit (by unfold K6Layout.oWBlit; omega),
    hdl L.oClOff (by unfold K6Layout.oClOff; omega),
    hdl L.oClSz (by unfold K6Layout.oClSz; omega),
    hdl L.oArena (by unfold K6Layout.oArena; omega)]

theorem m6_k6StateOfScratch_incons {L : K6Layout} {scr : List (BitVec 32)}
    (hbd : L.k6Base + 6 < scr.length) :
    (k6StateOfScratch L scr).incons = scr[L.k6Base + 6]'hbd := by
  unfold k6StateOfScratch K6State.ofSlab
  simp only [List.getElem?_drop, List.getElem?_eq_getElem hbd, Option.getD_some]

theorem m6_k6StateOfScratch_neq {L : K6Layout} {scr : List (BitVec 32)}
    (hbd : L.k6Base + 24 < scr.length) :
    (k6StateOfScratch L scr).neq = scr[L.k6Base + 24]'hbd := by
  unfold k6StateOfScratch K6State.ofSlab
  simp only [List.getElem?_drop, List.getElem?_eq_getElem hbd, Option.getD_some]

theorem m6_k6Inv_of_prefix_set {L : K6Layout} {scr : List (BitVec 32)} {idx : Nat} {v : BitVec 32}
    (hi : idx < L.k6Base) :
    k6StateOfScratch L (scr.set idx v) = k6StateOfScratch L scr := by
  unfold k6StateOfScratch; rw [m6_list_drop_set_lt scr v hi]

theorem k6ShrinkNv_preserves_inv {L : K6Layout} {P : (Nat → Bool) → Prop}
    {ks : K6State} {mvC nv : BitVec 32}
    (hinv : K6Inv L P ks) (hsync : K6TrailSynced ks)
    (hnv1 : 1 ≤ nv.toNat) (hnv_le_mvC : nv.toNat ≤ mvC.toNat)
    (hmvC_leMax : mvC.toNat ≤ L.maxV) (hks_nv : ks.nv = mvC)
    (_hlvl0 : ks.lvl = 0#32) (hna0 : ks.nassump = 0#32)
    (hbdd : K6LitsBounded nv.toNat ks)
    (htrl_bdd : ∀ l ∈ k6TrailLits ks, l < 2 * nv.toNat) :
    let ks' := ((((((ks.putHdr .nv nv).putHdr .unass (nv - ks.trl_end)).putHdr .qlast
      (nv - 1#32)).putHdr .qsearch (nv - 1#32)).putHdr .qstamp nv)).putArr .qnext
      (nv.toNat - 1) 0xFFFFFFFF#32
    K6Inv L P ks' ∧ K6TrailSynced ks' ∧ ks'.nv = nv := by
  intro ks'
  have hte_le : ks.trl_end.toNat ≤ nv.toNat := m6_trl_end_le_of_bdd hinv htrl_bdd
  have hm := L.hmaxV
  have hnv_max : nv.toNat ≤ L.maxV := by omega
  have hnv_le_old : nv.toNat ≤ ks.nv.toNat := hks_nv ▸ hnv_le_mvC
  have hsh' : ks'.ShapesOk L :=
    ((((((hinv.shapes.putHdr _ _).putHdr _ _).putHdr _ _).putHdr _ _).putHdr _ _).putArr _ _ _)
  have h_nv : ks'.nv = nv := rfl
  have h_nc : ks'.nc = ks.nc := rfl
  have h_lvl : ks'.lvl = ks.lvl := rfl
  have h_prop : ks'.prop = ks.prop := rfl
  have h_te : ks'.trl_end = ks.trl_end := rfl
  have h_unass : ks'.unass = nv - ks.trl_end := rfl
  have h_incons : ks'.incons = ks.incons := rfl
  have h_alen : ks'.alen = ks.alen := rfl
  have h_acap : ks'.acap = ks.acap := rfl
  have h_na : ks'.nassump = ks.nassump := rfl
  have h_nkl : ks'.nkl = ks.nkl := rfl
  have h_nana : ks'.nana = ks.nana := rfl
  have h_mv : ks'.max_v = ks.max_v := rfl
  have h_mo : ks'.max_orig = ks.max_orig := rfl
  have h_mc : ks'.max_cl = ks.max_cl := rfl
  have h_lvlArr : ks'.lvlArr = ks.lvlArr := rfl
  have h_rsn : ks'.rsn = ks.rsn := rfl
  have h_trl : ks'.trl = ks.trl := rfl
  have h_flags : ks'.flags = ks.flags := rfl
  have h_assump : ks'.assump = ks.assump := rfl
  have h_vals : ks'.vals = ks.vals := rfl
  have h_arena : ks'.arena = ks.arena := rfl
  have h_kcl : ∀ cid, k6ClauseSize ks' cid = k6ClauseSize ks cid := fun _ => rfl
  have h_koff : ∀ cid, k6ClauseOff ks' cid = k6ClauseOff ks cid := fun _ => rfl
  have h_klits : ∀ cid, k6ClauseLits ks' cid = k6ClauseLits ks cid := fun _ => rfl
  have hcl' : K6ClausesOk L P ks' :=
    { acap_eq := h_acap ▸ hinv.clauses.acap_eq, max_v_eq := h_mv ▸ hinv.clauses.max_v_eq
      max_orig_eq := h_mo ▸ hinv.clauses.max_orig_eq, max_cl_eq := h_mc ▸ hinv.clauses.max_cl_eq
      nv_le := by rw [h_nv]; exact hnv_max, nc_le := by rw [h_nc]; exact hinv.clauses.nc_le
      alen_le := by rw [h_alen]; exact hinv.clauses.alen_le
      nassump_le := by rw [h_na]; exact hinv.clauses.nassump_le
      nkl_le := by rw [h_nkl]; exact hinv.clauses.nkl_le
      nana_le := by rw [h_nana]; exact hinv.clauses.nana_le
      cl_wf := fun cid hc => by
        rw [h_nc] at hc; have hw := hinv.clauses.cl_wf cid hc
        rw [h_kcl, h_koff, h_alen, h_klits, h_nv]; exact ⟨hw.1, hw.2.1, hbdd.1 cid hc, hw.2.2.2⟩
      cl_mono := fun c1 c2 h12 h2c => by
        rw [h_nc] at h2c; simpa only [h_koff, h_kcl] using hinv.clauses.cl_mono c1 c2 h12 h2c
      incons_ok := fun hi => hinv.clauses.incons_ok (h_incons ▸ hi)
      assump_ok := fun i hi => by rw [h_na] at hi; rw [hna0] at hi; simp at hi
      flags_clean := fun v hv => by
        rw [h_nv] at hv; rw [h_flags]; exact hinv.clauses.flags_clean v (by omega) }
  have hwat' : K6WatchesOk ks' := by
    obtain ⟨chains, hlen, hnd, hch, hmem⟩ := hinv.watches
    refine ⟨chains.take (2 * nv.toNat), by rw [h_nv, List.length_take, hlen]; omega, ?_,
      fun l hl => ?_, fun l hl w hw => ?_⟩
    · have hcat : chains = chains.take (2 * nv.toNat) ++ chains.drop (2 * nv.toNat) :=
        (List.take_append_drop _ _).symm
      rw [hcat, List.flatten_append, List.nodup_append] at hnd; exact hnd.1
    · rw [h_nv] at hl
      rw [List.getElem?_take_of_lt hl]; exact hch l (by omega)
    · rw [h_nv] at hl; rw [List.getElem?_take_of_lt hl] at hw
      have hm0 := hmem l (by omega) w hw
      rw [h_nv, h_nc, h_kcl, h_koff, h_klits, h_arena]
      exact ⟨hm0.1, hm0.2.1, hm0.2.2.1, hbdd.2 w hm0.1, hm0.2.2.2.2⟩
  have hun_eq : (nv - ks.trl_end).toNat + ks.trl_end.toNat = nv.toNat := by bv_omega
  have hasgn' : K6BaseAssignOk P ks' :=
    { trl_end_le := by rw [h_te, h_nv]; exact hte_le
      prop_le := by rw [h_prop, h_te]; exact hinv.assign.prop_le
      unass_eq := by rw [h_unass, h_te, h_nv]; exact hun_eq
      vals_dom := fun l hl => by
        rw [h_nv] at hl; rw [h_vals]; exact hinv.assign.vals_dom l (by omega)
      vals_neg_iff := fun l hl => by
        rw [h_nv] at hl; rw [h_vals]; exact hinv.assign.vals_neg_iff l (by omega)
      vals_nz_iff_trl := fun l hl => by
        rw [h_nv] at hl; rw [h_vals, h_te, h_trl]; exact hinv.assign.vals_nz_iff_trl l (by omega)
      trl_nodup := by simpa only [k6TrailLits, h_trl, h_te] using hinv.assign.trl_nodup
      trl_lt := fun l hl => by
        simp only [k6TrailLits, h_trl, h_te] at hl; rw [h_nv]; exact htrl_bdd l hl
      trl_lvl_le := fun v hv => by
        rw [h_nv] at hv; rw [h_lvlArr, h_lvl]; exact hinv.assign.trl_lvl_le v (by omega)
      unass_lvl_zero := fun v hv hz => by
        rw [h_nv] at hv; rw [h_vals] at hz; rw [h_lvlArr, h_rsn]
        exact hinv.assign.unass_lvl_zero v (by omega) hz
      trl_lvl_mono := fun i j hij hj => by
        rw [h_te] at hj; rw [h_lvlArr, h_trl]; exact hinv.assign.trl_lvl_mono i j hij hj
      dec_earliest := fun i j hji hi hpos heq => by
        rw [h_te] at hi; rw [h_lvlArr, h_trl] at hpos heq; rw [h_rsn, h_trl]
        exact hinv.assign.dec_earliest i j hji hi hpos heq
      lvl0_ok := fun i hi hl0 => by
        rw [h_te] at hi; rw [h_trl, h_lvlArr] at hl0; rw [h_trl, h_vals]
        exact hinv.assign.lvl0_ok i hi hl0 }
  have hsync' : K6TrailSynced ks' := fun i hi => by
    rw [h_te] at hi; rw [h_trl, h_vals]; exact hsync i hi
  have hrsn' : K6ReasonOk ks' := fun i hi => by
    rw [h_te] at hi; simpa only [h_trl, h_rsn, h_nc, h_klits] using hinv.reasons i hi
  exact ⟨⟨hsh', hcl', hwat', hasgn', hrsn'⟩, hsync', rfl⟩

theorem m6_fullDenseInvW_with_fuel_scr {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {fuel' : BitVec 64} {sig' : List (BitVec 64)} {scr' : List (BitVec 32)}
    (hsig : sig'.length = c.max_vars) (hscr : scr'.length = c.scratch_cap) :
    FullDenseInvW c F0 F_cur
      { s with
        core := { s.core with fuel := fuel' }
        scratch := { s.scratch with sim_sig := sig', scratch_buf := scr' } } := by
  let s' : FullState :=
    { s with
      core := { s.core with fuel := fuel' }
      scratch := { s.scratch with sim_sig := sig', scratch_buf := scr' } }
  have hlen' : s'.LengthsOk c :=
    ⟨{ h.1.core_ok with vals_len := h.1.core_ok.vals_len },
     { h.1.scratch_ok with sim_sig_len := hsig, scratch_buf_len := hscr }⟩
  have hw := h.2.1
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { hw with
      arena := { hw.arena with len_ok := hw.arena.len_ok }
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }
  exact ⟨hlen', hw', h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem m6_fullDenseInvW_with_scratch {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {fuel' : BitVec 64} {scr' : List (BitVec 32)} (hscr : scr'.length = c.scratch_cap) :
    FullDenseInvW c F0 F_cur
      { s with core := { s.core with fuel := fuel' }
               scratch := { s.scratch with scratch_buf := scr' } } :=
  m6_fullDenseInvW_with_fuel_scr h h.1.scratch_ok.sim_sig_len hscr

theorem m6_fullDenseInvW_with_sig {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {sig' : List (BitVec 64)} (hsig : sig'.length = c.max_vars) :
    FullDenseInvW c F0 F_cur { s with scratch := { s.scratch with sim_sig := sig' } } :=
  m6_fullDenseInvW_with_fuel_scr h hsig h.1.scratch_ok.scratch_buf_len

theorem m6_fullDenseInvW_with_flags {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) {flags' : List (BitVec 32)}
    (hfl : flags'.length = c.max_vars) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with flags := flags' } } := by
  let s' : FullState := { s with core := { s.core with flags := flags' } }
  have hw := h.2.1
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { hw with
      arena := { hw.arena with len_ok := hw.arena.len_ok }
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }
  exact ⟨⟨{ h.1.core_ok with flags_len := hfl }, h.1.scratch_ok⟩, hw',
    h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem m6_fullDenseInvW_with_tmk {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {tmk' : List (BitVec 32)} (ht : tmk'.length = 2 * c.max_vars) :
    FullDenseInvW c F0 F_cur { s with scratch := { s.scratch with tarjan_mark := tmk' } } :=
  ⟨⟨h.1.core_ok, { h.1.scratch_ok with tarjan_mark_len := ht }⟩,
    h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem m6_fullDenseInvW_with_ws2 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {ws2' : List (BitVec 32)} (hws2 : ws2'.length = 2 * c.max_vars) :
    FullDenseInvW c F0 F_cur { s with scratch := { s.scratch with work_stk2 := ws2' } } :=
  ⟨⟨h.1.core_ok, { h.1.scratch_ok with work_stk2_len := hws2 }⟩,
    h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem m6_fullDenseInvW_with_trc_ws2 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {trc' ws2' : List (BitVec 32)}
    (htrc : trc'.length = 2 * c.max_vars) (hws2 : ws2'.length = 2 * c.max_vars) :
    FullDenseInvW c F0 F_cur
      { s with scratch := { s.scratch with tarjan_reach := trc', work_stk2 := ws2' } } :=
  ⟨⟨h.1.core_ok, { h.1.scratch_ok with tarjan_reach_len := htrc, work_stk2_len := hws2 }⟩,
    h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem m6_fullDenseInvW_with_gu {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {gu' : List (BitVec 32)} (hgu : gu'.length = 64) :
    FullDenseInvW c F0 F_cur { s with scratch := { s.scratch with glue_used := gu' } } :=
  ⟨⟨h.1.core_ok, { h.1.scratch_ok with glue_used_len := hgu }⟩,
    h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem m6_fullDenseInvW_with_cls_scratch {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {scr' sstk' mclr' wso' : List (BitVec 32)}
    (hscr : scr'.length = c.scratch_cap) (hsst : sstk'.length = c.max_vars)
    (hmc : mclr'.length = c.max_vars) (hwso : wso'.length = 2 * c.max_vars) :
    FullDenseInvW c F0 F_cur
      { s with
        core := { s.core with min_clr := mclr' }
        scratch :=
          { s.scratch with scratch_buf := scr', shrink_stk := sstk', wsort := wso' } } := by
  let s' : FullState :=
    { s with
      core := { s.core with min_clr := mclr' }
      scratch := { s.scratch with scratch_buf := scr', shrink_stk := sstk', wsort := wso' } }
  have hw := h.2.1
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { hw with
      arena := { hw.arena with len_ok := hw.arena.len_ok }
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }
  exact ⟨⟨{ h.1.core_ok with min_clr_len_arr := hmc },
      { h.1.scratch_ok with scratch_buf_len := hscr, shrink_stk_len := hsst, wsort_len := hwso }⟩,
    hw', h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem m6_fullDenseInvW_set_repr {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) {rp' : List (BitVec 32)}
    (hrp : rp'.length = 2 * c.max_vars) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with repr := rp' } } := by
  let s' : FullState := { s with core := { s.core with repr := rp' } }
  have hw := h.2.1
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { hw with
      arena := { hw.arena with len_ok := hw.arena.len_ok }
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }
  exact ⟨⟨{ h.1.core_ok with repr_len := hrp }, h.1.scratch_ok⟩,
    hw', h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem m6_fullDenseInvW_set_sweep_cnt {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    (sc' : BitVec 64) :
    FullDenseInvW c F0 F_cur { s with scratch := { s.scratch with sweep_cnt := sc' } } :=
  ⟨⟨h.1.core_ok, { h.1.scratch_ok with sim_sig_len := h.1.scratch_ok.sim_sig_len }⟩,
    h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem m6_fullDenseInvW_set_inconsistent {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    (huns : (cnfOfClauses F_cur).Unsat) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with inconsistent := 1#64 } } := by
  have hw := h.2.1
  have hw' : FullWitnessInv c F0 F_cur { s.core with inconsistent := 1#64 } :=
    { hw with
      inconsistent_sound := fun _ => huns
      arena := { hw.arena with len_ok := hw.arena.len_ok }
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }
  exact ⟨⟨{ h.1.core_ok with vals_len := h.1.core_ok.vals_len }, h.1.scratch_ok⟩,
    hw', h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem m6_watchLayout_of_denseInvW {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hdw : FullDenseInvW c F0 F_cur s) : WatchStackLayout s.core := by
  have hwm := hdw.2.1.watches; unfold ModeWatchesInv at hwm
  rw [ite_eq_right (fun h0 => hdw.2.2.2.2.2.2 h0)] at hwm; exact hwm.layout

theorem m6_denseSlice_step_bin {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p rem : Nat} {w0 : BitVec 32} (hs : DenseWatchSliceOk F_cur k lit p rem)
    (hpos : 0 < rem) (hp : k.wstk[p]? = some w0)
    (hbin : (w0 &&& 0x80000000#32) ≠ 0#32) :
    w0 ≠ 0xFFFFFFFF#32 ∧ (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat]) ∧
    DenseWatchSliceOk F_cur k lit (p + 1) (rem - 1) := by
  cases hs with
  | empty => omega
  | bin hp' _ hne hlt hent hrest =>
    rw [hp] at hp'; cases Option.some.inj hp'; exact ⟨hne, hlt, hent, hrest⟩
  | occ hp' _ hflag _ _ _ _ =>
    rw [hp] at hp'; cases Option.some.inj hp'; exact absurd hflag hbin

theorem m6_denseSlice_step_occ {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p rem : Nat} {w0 : BitVec 32} (hs : DenseWatchSliceOk F_cur k lit p rem)
    (hpos : 0 < rem) (hp : k.wstk[p]? = some w0)
    (hocc : (w0 &&& 0x80000000#32) = 0#32) :
    2 ≤ rem ∧ 3 ≤ w0.toNat ∧
    ∃ cr, k.wstk[p + 1]? = some cr ∧ cr.toNat < 0x80000000 ∧
      cr.toNat ∈ fullArenaClauseRefsCore k ∧
      DenseWatchSliceOk F_cur k lit (p + 2) (rem - 2) := by
  cases hs with
  | empty => omega
  | bin hp' hflag _ _ _ _ =>
    rw [hp] at hp'; cases Option.some.inj hp'; exact absurd hocc hflag
  | occ hp' hp1 _ h3 hlt href hrest =>
    rw [hp] at hp'; cases Option.some.inj hp'; exact ⟨by omega, h3, _, hp1, hlt, href, hrest⟩

theorem m6_eqBufOk_push {F_cur : List (List Nat)} {s : FullState} {neq la lc : BitVec 32}
    (heq : M6EqBufOk F_cur s neq.toNat) (hne : neq.toNat < s.core.cur_vars)
    (hla : la.toNat < 2 * s.core.cur_vars) (hlc : lc.toNat < 2 * s.core.cur_vars)
    (hlv : LitEquiv (cnfOfClauses F_cur) la.toNat lc.toNat)
    (h2lt : 2 * neq.toNat + 1 < s.scratch.work_stk2.length) :
    let ws2' := (s.scratch.work_stk2.set (2 * neq.toNat) la).set (2 * neq.toNat + 1) lc
    let s' := { s with scratch := { s.scratch with work_stk2 := ws2' } }
    M6EqBufOk F_cur s' (neq.toNat + 1) := by
  intro ws2' s'
  refine ⟨by dsimp [s']; omega, fun i hi => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
  · dsimp only [s', ws2']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    exact heq.2 i hlt
  · dsimp only [s', ws2']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega), Option.getD_some,
      List.getElem?_set_self (by simp; exact h2lt), Option.getD_some]
    exact ⟨hla, hlc, hlv⟩

theorem m6_coneOk_of_tailEq {c : FullCfg} {F_cur : List (List Nat)} {L : K6Layout}
    {s : FullState} {scr' : List (BitVec 32)} {nv : Nat}
    (hcone : M6SweepConeOk F_cur s nv) (hL : L.scrLen = c.scratch_cap)
    (hLmv : L.maxV = k6MaxV c.scratch_cap) (hscr : s.scratch.scratch_buf.length = c.scratch_cap)
    (hscr' : scr'.length = c.scratch_cap)
    (hK : K6Inv L (ConeModelSet F_cur s.scratch.work_stk1 nv) (k6StateOfScratch L scr'))
    (hnv : (k6StateOfScratch L scr').nv = BitVec.ofNat 32 nv) :
    M6SweepConeOk F_cur { s with scratch := { s.scratch with scratch_buf := scr' } } nv := by
  have hge : k6MinScr ≤ scr'.length := by have := hcone.2.2.2.2.2.1; omega
  have hlt : scr'.length < dimacsBound := by have := hcone.2.2.2.2.2.2.1; omega
  have hscrInv : K6ScratchInv (ConeModelSet F_cur s.scratch.work_stk1 nv) scr' :=
    hK.to_scratchInv (hscr'.trans hL.symm) (by rw [hscr']; exact hLmv) hge hlt
  refine ⟨hcone.1, by rw [hscr', ← hscr]; exact hcone.2.1, hcone.2.2.1, hcone.2.2.2.1,
    hscrInv, hge, hlt, ?_⟩
  rw [k6LayoutOfCap_eq (hL.trans hscr'.symm) (by rw [hscr']; exact hLmv) hge hlt]
  exact hnv

theorem m6_coneHwm_of_tailEq {L : K6Layout} {hw : BitVec 32} {ks ks' : K6State}
    (hK : K6HwmClean L hw ks) (ht : K6TailEq L ks ks')
    (hhw : hw = 0xFFFFFFFF#32 ∨ ks.nv.toNat ≤ hw.toNat) : K6HwmClean L hw ks' := by
  rcases hhw with rfl | hnvle
  · exact Or.inl rfl
  · rcases hK with rfl | ⟨hle, hcl⟩
    · exact Or.inl rfl
    · refine Or.inr ⟨hle, fun v h1 h2 => ?_⟩
      have hc := ht.2 v (Nat.le_trans hnvle h1) h2
      have h0 := hcl v h1 h2
      rw [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1, hc.2.2.2.2.2.1, hc.2.2.2.2.2.2]
      exact h0

end LeanQbe.T.Examples.Kissat.Proof.Sweep

end
