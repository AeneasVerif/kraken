/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Congruence.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
public import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
public import LeanQbe.T.Logic.C0Step
public import LeanQbe.T.Logic.C0HeadStep
public import LeanQbe.T.Logic.ControlComb
public import Kraken.Mem
public import Kraken.Separation

/-!
# Congruence Memory Framing, `i32`/`u64` Work-Array Aliasing, and Scoped C0 Tactics

Provides `CongTactics` (`@[scoped c0_load]` / `@[scoped c0_store]` / `@[scoped bv_c0]`) for:
1. Standalone `array (t := i32)` and `array64` pointer indexing.
2. Constant-offset `FullMem` `tmp[0/1/2]` aliasing (`c.pTmp + {0,4,8}#64`).
3. `FullMemNoWks3` accessors and `u32 <-> u64` aliasing between `FullMem` and
   `FullMemNoWks3 ⋆ array64 c.pWsort ⋆ array64 c.pWorkStk1 ⋆ array64 c.pWorkStk2`.
4. Shared `BitVec` / `List` kernel lemmas used across `Proof.Congruence.*`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Congruence

public section

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Congruence.Spec
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open Kraken.Bedrock2.Test

/-! ## 1. Pure `BitVec` & `List` Index Helpers -/

theorem list_getElem_congr {α : Type _} {xs : List α} {i j : Nat}
    (h : i = j) (hi : i < xs.length) (hj : j < xs.length) : xs[i]'hi = xs[j]'hj := by
  subst h; rfl

theorem getElem?_eq_some_of_getD {α : Type _} [Inhabited α] {l : List α}
    {i : Nat} {v : α} (hi : i < l.length) (h : l[i]?.getD default = v) : l[i]? = some v := by
  rw [List.getElem?_eq_getElem hi, Option.getD_some] at h
  rw [List.getElem?_eq_getElem hi, h]

theorem getElem_of_getD {α : Type _} [Inhabited α] {xs : List α} {i : Nat}
    {v : α} (hi : i < xs.length) (h : xs[i]?.getD default = v) : xs[i]'hi = v := by
  rwa [List.getElem?_eq_getElem hi, Option.getD_some] at h

theorem bv_zext32_toNat (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide))]

theorem bv32_ult_lt {a b : BitVec 32} (h : a.ult b = true) : a.toNat < b.toNat := by
  simpa [BitVec.ult] using h

theorem bv32_ult_not_lt {a b : BitVec 32} (h : a.ult b = false) : ¬ a.toNat < b.toNat := by
  simpa [BitVec.ult] using h

theorem bv64_ult_lt {a b : BitVec 64} (h : a.ult b = true) : a.toNat < b.toNat := by
  simpa [BitVec.ult] using h

theorem bv64_ult_not_lt {a b : BitVec 64} (h : a.ult b = false) : ¬ a.toNat < b.toNat := by
  simpa [BitVec.ult] using h

theorem bv64_ule_le {a b : BitVec 64} (h : a.ule b = true) : a.toNat ≤ b.toNat := by
  simpa [BitVec.ule] using h

theorem bv64_ule_not_le {a b : BitVec 64} (h : a.ule b = false) : b.toNat < a.toNat := by
  have h' : ¬ a.toNat ≤ b.toNat := by simpa [BitVec.ule] using h
  omega

theorem bv64_ofNat_toNat_lt {n : Nat} (h : n < 2 ^ 64) :
    (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem bv32_ofNat_toNat_lt {n : Nat} (h : n < 2 ^ 32) :
    (BitVec.ofNat 32 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem bv64_add1_lt {a : BitVec 64} (h : a.toNat + 1 < 2 ^ 64) :
    (a + 1#64).toNat = a.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt h]

theorem bv64_add2_lt {a : BitVec 64} (h : a.toNat + 2 < 2 ^ 64) :
    (a + 2#64).toNat = a.toNat + 2 := by
  rw [BitVec.toNat_add, show (2#64 : BitVec 64).toNat = 2 from rfl, Nat.mod_eq_of_lt h]

theorem bv64_addk_lt_of {x : BitVec 64} {k : Nat} (hk : k < 2 ^ 64)
    (h : x.toNat + k < 2 ^ 64) : (x + BitVec.ofNat 64 k).toNat = x.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt h]

theorem bv32_add1_lt_of {x : BitVec 32} (h : x.toNat + 1 < 2 ^ 32) :
    (x + 1#32).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt h]

theorem bv64_sub1_pos {a : BitVec 64} (h : 0 < a.toNat) :
    (a - 1#64).toNat = a.toNat - 1 := by
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 1 ≤ a.toNat; omega))]
  rfl

theorem bv64_shl1_toNat (x : BitVec 64) :
    (x <<< (1 : Nat)).toNat = (2 * x.toNat) % 2 ^ 64 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]

theorem bv64_shl1_lt {x : BitVec 64} (h : 2 * x.toNat < 2 ^ 64) :
    (x <<< 1#64).toNat = 2 * x.toNat := by
  rw [show (x <<< 1#64 : BitVec 64) = x <<< (1 : Nat) from rfl,
    bv64_shl1_toNat, Nat.mod_eq_of_lt h]

theorem bv64_shl1_add1_lt {x : BitVec 64} (h : 2 * x.toNat + 1 < 2 ^ 64) :
    ((x <<< 1#64) + 1#64).toNat = 2 * x.toNat + 1 := by
  rw [BitVec.toNat_add, bv64_shl1_lt (by omega), show (1#64 : BitVec 64).toNat = 1 from rfl,
    Nat.mod_eq_of_lt h]

theorem bv64_ushiftRight1_toNat (x : BitVec 64) :
    (x >>> (1 : Nat)).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem bv64_shr1_toNat (x : BitVec 64) : (x >>> 1#64).toNat = x.toNat / 2 := by
  rw [show (x >>> 1#64 : BitVec 64) = x >>> (1 : Nat) from rfl,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]

theorem bv64_shr2_toNat (x : BitVec 64) : (x >>> 2#64).toNat = x.toNat / 4 := by
  rw [show (x >>> 2#64 : BitVec 64) = x >>> (2 : Nat) from rfl,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem bv32_ushr1_lt_of_lt2 {l : BitVec 32} {n : Nat} (hl : (l >>> 1).toNat < n) :
    l.toNat < 2 * n := by
  have h1 : (l >>> (1 : Nat)).toNat = l.toNat / 2 := by
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  change (l >>> (1 : Nat)).toNat < n at hl; rw [h1] at hl; omega

theorem bv32_div2_lt_of_lt2 {l : BitVec 32} {n : Nat} (hl : l.toNat < 2 * n) :
    (l >>> 1).toNat < n := by
  change (l >>> (1 : Nat)).toNat < n
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega

theorem bv64_mul8_eq {i : BitVec 64} : i * 8 = BitVec.ofNat 64 (8 * i.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, Nat.mul_comm]

theorem bv64_mul4_eq {i : BitVec 64} : i * 4 = BitVec.ofNat 64 (4 * i.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, Nat.mul_comm]

theorem bv64_add_zext32 {p : BitVec 64} {k : Nat} {i : BitVec 32}
    (h : p.toNat + k + i.toNat < 2 ^ 64) :
    (p + BitVec.ofNat 64 k + i.setWidth 64).toNat = p.toNat + k + i.toNat := by
  rw [BitVec.toNat_add, BitVec.toNat_add, bv_zext32_toNat, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

/-! ## 2. Scoped C0 Memory Accessors (`CongTactics`) -/

namespace CongTactics

@[scoped bv_c0] theorem bv64_add_zext32_nat (p : BitVec 64) (i : BitVec 32) :
    (p + i.setWidth 64).toNat = (p.toNat + i.toNat) % 2 ^ 64 := by
  rw [BitVec.toNat_add, bv_zext32_toNat]

@[scoped bv_c0] theorem bv64_shr1_bv_nat (x : BitVec 64) : (x >>> 1#64).toNat = x.toNat / 2 :=
  bv64_shr1_toNat x

@[scoped c0_load] theorem c0_load_arr32 {a : BitVec 64} {xs : List (BitVec 32)} {i : BitVec 64}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : i.toNat < xs.length)
    (hm : (array (t := i32) a xs ⋆ R) m) :
    loadVal m i32 (a + i * 4) = some xs[i.toNat] := by
  rw [bv64_mul4_eq]; exact loadVal_array (by decide) hi hm

@[scoped c0_load] theorem c0_load_arr32_0 {a : BitVec 64} {xs : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64} (h0 : 0 < xs.length)
    (hm : (array (t := i32) a xs ⋆ R) m) :
    loadVal m i32 a = some xs[0] := by
  simpa using loadVal_array (i := 0) (by decide) h0 hm

@[scoped c0_load] theorem c0_load_arr32_zext0 {a : BitVec 64} {xs : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64} (h0 : 0 < xs.length)
    (hm : (array (t := i32) a xs ⋆ R) m) :
    loadVal m i32 (a + (0#32).signExtend 64 * 4) = some xs[0] := by
  simpa using loadVal_array (i := 0) (by decide) h0 hm

@[scoped c0_store] theorem c0_store_arr32 {a : BitVec 64} {xs : List (BitVec 32)} {i : BitVec 64}
    (v : BitVec 32) {R : Mem 64 → Prop} {m : Mem 64} (hi : i.toNat < xs.length)
    (hm : (array (t := i32) a xs ⋆ R) m) :
    storeOk m i32 (a + i * 4) ∧
      (array (t := i32) a (xs.set i.toNat v) ⋆ R) (storeMem m i32 (a + i * 4) v) := by
  rw [bv64_mul4_eq]; exact store_array v (by decide) hi hm

@[scoped c0_store] theorem c0_store_arr32_0 {a : BitVec 64} {xs : List (BitVec 32)}
    (v : BitVec 32) {R : Mem 64 → Prop} {m : Mem 64} (h0 : 0 < xs.length)
    (hm : (array (t := i32) a xs ⋆ R) m) :
    storeOk m i32 a ∧
      (array (t := i32) a (xs.set 0 v) ⋆ R) (storeMem m i32 a v) := by
  simpa using store_array v (i := 0) (by decide) h0 hm

@[scoped c0_load] theorem c0_load_arr64 {a : BitVec 64} {xs : List (BitVec 64)} {i : BitVec 64}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : i.toNat < xs.length) (hm : (array64 a xs ⋆ R) m) :
    loadVal m i64 (a + i * 8) = some xs[i.toNat] := by
  rw [bv64_mul8_eq]; exact loadVal_array64 hi hm

@[scoped c0_load] theorem c0_load_arr64_0 {a : BitVec 64} {xs : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64} (h0 : 0 < xs.length) (hm : (array64 a xs ⋆ R) m) :
    loadVal m i64 (a + 0) = some xs[0] := by
  simpa using loadVal_array64 (i := 0) h0 hm

@[scoped c0_load] theorem c0_load_arr64_zext0 {a : BitVec 64} {xs : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64} (h0 : 0 < xs.length) (hm : (array64 a xs ⋆ R) m) :
    loadVal m i64 (a + (0#32).signExtend 64 * 8) = some xs[0] := by
  simpa using loadVal_array64 (i := 0) h0 hm

@[scoped c0_store] theorem c0_store_arr64 {a : BitVec 64} {xs : List (BitVec 64)} {i : BitVec 64}
    (v : BitVec 64) {R : Mem 64 → Prop} {m : Mem 64} (hi : i.toNat < xs.length)
    (hm : (array64 a xs ⋆ R) m) :
    storeOk m i64 (a + i * 8) ∧
      (array64 a (xs.set i.toNat v) ⋆ R) (storeMem m i64 (a + i * 8) v) := by
  rw [bv64_mul8_eq]; exact store_array64 v hi hm

@[scoped c0_store] theorem c0_store_arr64_0 {a : BitVec 64} {xs : List (BitVec 64)}
    (v : BitVec 64) {R : Mem 64 → Prop} {m : Mem 64} (h0 : 0 < xs.length)
    (hm : (array64 a xs ⋆ R) m) :
    storeOk m i64 (a + 0) ∧
      (array64 a (xs.set 0 v) ⋆ R) (storeMem m i64 (a + 0) v) := by
  simpa using store_array64 v (i := 0) h0 hm

@[scoped c0_store] theorem c0_store_arr64_zext0 {a : BitVec 64} {xs : List (BitVec 64)}
    (v : BitVec 64) {R : Mem 64 → Prop} {m : Mem 64} (h0 : 0 < xs.length)
    (hm : (array64 a xs ⋆ R) m) :
    storeOk m i64 (a + (0#32).signExtend 64 * 8) ∧
      (array64 a (xs.set 0 v) ⋆ R) (storeMem m i64 (a + (0#32).signExtend 64 * 8) v) := by
  simpa using store_array64 v (i := 0) h0 hm

@[scoped c0_load] theorem c0_load_full_tmp0_add {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (FullMem c s ⋆ R) m) (h0 : 0 < s.core.tmp.length) :
    loadVal m i32 (c.pTmp + 0#64) = some (s.core.tmp[0]'h0) := by
  simpa using FullArenaTactics.c0_load_full_tmp (i := 0#64) (by simpa using h0) hm

@[scoped c0_load] theorem c0_load_full_tmp1_add {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (FullMem c s ⋆ R) m) (h1 : 1 < s.core.tmp.length) :
    loadVal m i32 (c.pTmp + 4#64) = some (s.core.tmp[1]'h1) := by
  simpa using FullArenaTactics.c0_load_full_tmp (i := 1#64) (by simpa using h1) hm

@[scoped c0_load] theorem c0_load_full_tmp2_add {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (FullMem c s ⋆ R) m) (h2 : 2 < s.core.tmp.length) :
    loadVal m i32 (c.pTmp + 8#64) = some (s.core.tmp[2]'h2) := by
  simpa using FullArenaTactics.c0_load_full_tmp (i := 2#64) (by simpa using h2) hm

@[scoped c0_store] theorem c0_store_full_tmp0_add {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (h0 : 0 < s.core.tmp.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pTmp + 0#64) ∧
      (FullMem c { s with core := { s.core with tmp := s.core.tmp.set 0 v } } ⋆ R)
        (storeMem m i32 (c.pTmp + 0#64) v) := by
  simpa using FullArenaTactics.c0_store_full_tmp (i := 0#64) v (by simpa using h0) hm

@[scoped c0_store] theorem c0_store_full_tmp1_add {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (h1 : 1 < s.core.tmp.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pTmp + 4#64) ∧
      (FullMem c { s with core := { s.core with tmp := s.core.tmp.set 1 v } } ⋆ R)
        (storeMem m i32 (c.pTmp + 4#64) v) := by
  simpa using FullArenaTactics.c0_store_full_tmp (i := 1#64) v (by simpa using h1) hm

@[scoped c0_store] theorem c0_store_full_tmp2_add {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (h2 : 2 < s.core.tmp.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pTmp + 8#64) ∧
      (FullMem c { s with core := { s.core with tmp := s.core.tmp.set 2 v } } ⋆ R)
        (storeMem m i32 (c.pTmp + 8#64) v) := by
  simpa using FullArenaTactics.c0_store_full_tmp (i := 2#64) v (by simpa using h2) hm

end CongTactics

/-! ## 3. `FullMemNoWks3` Framing & `u32`/`u64` Work-Array Aliasing -/

/-- Remaining footprint of `FullMemNoWks3 c s` with `scratch_buf` separated out. -/
@[expose] def FullNoWks3ScrBufRest (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (hdrTailWords c s) ⋆
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
  unfold FullNoWks3ScrBufRest hdrTailWords
    HdrWordField.tailChunk0 HdrWordField.tailChunk1 HdrWordField.tailChunk2
    HdrWordField.tailChunk3 FullScrByteArrs FullScrU32A FullScrWksArrsNo3
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
      have hr0 := array_to_region (t := i32)
        (by simp [Ty.bytes, Ty.size, i32, hlen]; omega) h
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
      have hr0 := array_to_region (t := i64)
        (by simp [Ty.bytes, Ty.size, i64, hlen]; omega) hf
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
    unfold FullMemNoWks3 hdrTailWords HdrWordField.tailChunk0 HdrWordField.tailChunk1
      HdrWordField.tailChunk2 HdrWordField.tailChunk3 FullScratchArraysNo3 FullScrByteArrs
      FullScrU32A FullScrWksArrsNo3 FullScrMetaArrs FullScrDynArrs
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
      some ((hdrTailWords c s)[i]'(by simp [hi])) := by
  have h1 : (array64 (c.hdr + 32) (hdrTailWords c s) ⋆
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
       FullCoreArrays c s.core ⋆ FullScratchArraysNo3 c s.scratch ⋆ c.pad ⋆ R)) m := by
    unfold FullMemNoWks3 at hm; ecancel
  have hi' : i < (hdrTailWords c s).length := by simp [hi]
  have hld := loadVal_array64 hi' h1
  rwa [show c.hdr + (32 : BitVec 64) + BitVec.ofNat 64 (8 * i) =
    c.hdr + BitVec.ofNat 64 (32 + 8 * i) from ptr_add_ofNat c.hdr 32 (8 * i)] at hld

private theorem load_noWks3_field {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (f : HdrWordField) (ht : 4 ≤ f.wordIdx)
    (hm : (FullMemNoWks3 c s ⋆ R) m) :
    loadVal m i64 (c.hdr + BitVec.ofNat 64 f.byteOff) = some (f.get c s) := by
  have hlt : f.wordIdx - 4 < 140 := by have := f.wordIdx_lt; omega
  have hoff : f.byteOff = 32 + 8 * (f.wordIdx - 4) := by
    unfold HdrWordField.byteOff; omega
  rw [hoff]
  have h := load_noWks3_hdr (f.wordIdx - 4) hlt hm
  rwa [f.hdrTailWords_get ht c s] at h

namespace CongTactics

@[scoped c0_load] theorem load_noWks3_arena_len {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (FullMemNoWks3 c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 48) = some (BitVec.ofNat 64 s.core.arena_len) :=
  load_noWks3_field .arena_len (by decide) hm

@[scoped c0_load] theorem load_noWks3_vals_ptr {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (FullMemNoWks3 c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 64) = some c.pVals :=
  load_noWks3_field .values_ptr (by decide) hm

@[scoped c0_load] theorem load_noWks3_wvec_ptr {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (FullMemNoWks3 c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 104) = some c.pWvec :=
  load_noWks3_field .watch_vec_ptr (by decide) hm

@[scoped c0_load] theorem load_noWks3_arena_ptr {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (FullMemNoWks3 c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 112) = some c.pArena :=
  load_noWks3_field .arena_ptr (by decide) hm

@[scoped c0_load] theorem load_noWks3_wstk_ptr {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (FullMemNoWks3 c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 120) = some c.pWstk :=
  load_noWks3_field .watch_stk_ptr (by decide) hm

@[scoped c0_load] theorem load_noWks3_flags_ptr {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (FullMemNoWks3 c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 800) = some c.pFlags :=
  load_noWks3_field .flags_ptr (by decide) hm

@[scoped c0_load] theorem load_noWks3_work_stk1_ptr {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (FullMemNoWks3 c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 848) = some c.pWorkStk1 :=
  load_noWks3_field .work_stk1_ptr (by decide) hm

@[scoped c0_load] theorem load_noWks3_work_stk2_ptr {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (FullMemNoWks3 c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 856) = some c.pWorkStk2 :=
  load_noWks3_field .work_stk2_ptr (by decide) hm

@[scoped c0_load] theorem load_noWks3_scratch_buf_ptr {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (FullMemNoWks3 c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 920) = some c.pScratchBuf :=
  load_noWks3_field .scratch_buf_ptr (by decide) hm

@[scoped c0_load] theorem load_noWks3_scratch_cap {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (FullMemNoWks3 c s ⋆ R) m) :
    loadVal m i64 (c.hdr + 928) = some (BitVec.ofNat 64 c.scratch_cap) :=
  load_noWks3_field .scratch_cap (by decide) hm

@[scoped c0_load] theorem c0_load_noWks3_vals {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64} (hi : i.toNat < s.core.vals.length)
    (hm : (FullMemNoWks3 c s ⋆ R) m) :
    loadVal m i8 (c.pVals + i) = some (s.core.vals[i.toNat]'hi) := by
  have h1 : (array (t := i8) c.pVals s.core.vals ⋆
      (array (t := i8) c.pLitMark s.core.lit_mark ⋆ array (t := i8) c.pMark s.core.mrk ⋆
       FullCoreU32A c s.core ⋆ FullCoreU32B c s.core ⋆ FullCoreDynArrs c s.core ⋆
       dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
       array64 (c.hdr + 32) (hdrTailWords c s) ⋆ FullScratchArraysNo3 c s.scratch ⋆
       c.pad ⋆ R)) m := by
    unfold FullMemNoWks3 FullCoreArrays FullCoreByteArrs at hm; ecancel
  have hld := loadVal_array (i := i.toNat) (by decide) hi h1
  simpa [Ty.bytes, Ty.size, i8] using hld

@[scoped c0_load] theorem c0_load_noWks3_flags {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64} (hi : i.toNat < s.core.flags.length)
    (hm : (FullMemNoWks3 c s ⋆ R) m) :
    loadVal m i32 (c.pFlags + i * 4) = some (s.core.flags[i.toNat]'hi) := by
  have h1 : (array (t := i32) c.pFlags s.core.flags ⋆
      (FullCoreByteArrs c s.core ⋆
       array (t := i32) c.pLevel s.core.lvl ⋆ array (t := i32) c.pReason s.core.rsns ⋆
       array (t := i32) c.pTrail s.core.trl ⋆ array (t := i32) c.pTrailPos s.core.trail_pos ⋆
       array (t := i32) c.pTmp s.core.tmp ⋆ array (t := i32) c.pMinClr s.core.min_clr ⋆
       FullCoreU32B c s.core ⋆ FullCoreDynArrs c s.core ⋆
       dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
       array64 (c.hdr + 32) (hdrTailWords c s) ⋆ FullScratchArraysNo3 c s.scratch ⋆
       c.pad ⋆ R)) m := by
    unfold FullMemNoWks3 FullCoreArrays FullCoreU32A at hm; ecancel
  rw [bv64_mul4_eq]; exact loadVal_array (by decide) hi h1

@[scoped c0_load] theorem c0_load_noWks3_wvec {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64} (hi : i.toNat < s.core.wvec.length)
    (hm : (FullMemNoWks3 c s ⋆ R) m) :
    loadVal m i32 (c.pWvec + i * 4) = some (s.core.wvec[i.toNat]'hi) := by
  have h1 : (array (t := i32) c.pWvec s.core.wvec ⋆
      (FullCoreByteArrs c s.core ⋆ FullCoreU32A c s.core ⋆
       array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
       array (t := i32) c.pFrameDec s.core.frame_dec ⋆
       array (t := i32) c.pRepr s.core.repr ⋆ array (t := i32) c.pMinStk s.core.min_stk ⋆
       FullCoreDynArrs c s.core ⋆
       dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
       array64 (c.hdr + 32) (hdrTailWords c s) ⋆ FullScratchArraysNo3 c s.scratch ⋆
       c.pad ⋆ R)) m := by
    unfold FullMemNoWks3 FullCoreArrays FullCoreU32B at hm; ecancel
  rw [bv64_mul4_eq]; exact loadVal_array (by decide) hi h1

@[scoped c0_load] theorem c0_load_noWks3_wstk {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64} (hi : i.toNat < s.core.wstk.length)
    (hm : (FullMemNoWks3 c s ⋆ R) m) :
    loadVal m i32 (c.pWstk + i * 4) = some (s.core.wstk[i.toNat]'hi) := by
  have h1 : (array (t := i32) c.pWstk s.core.wstk ⋆
      (FullCoreByteArrs c s.core ⋆ FullCoreU32A c s.core ⋆ FullCoreU32B c s.core ⋆
       array (t := i32) c.pArena s.core.arena ⋆
       dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
       array64 (c.hdr + 32) (hdrTailWords c s) ⋆ FullScratchArraysNo3 c s.scratch ⋆
       c.pad ⋆ R)) m := by
    unfold FullMemNoWks3 FullCoreArrays FullCoreDynArrs at hm; ecancel
  rw [bv64_mul4_eq]; exact loadVal_array (by decide) hi h1

@[scoped c0_load] theorem c0_load_noWks3_arena {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64} (hi : i.toNat < s.core.arena.length)
    (hm : (FullMemNoWks3 c s ⋆ R) m) :
    loadVal m i32 (c.pArena + i * 4) = some (s.core.arena[i.toNat]'hi) := by
  have h1 : (array (t := i32) c.pArena s.core.arena ⋆
      (FullCoreByteArrs c s.core ⋆ FullCoreU32A c s.core ⋆ FullCoreU32B c s.core ⋆
       array (t := i32) c.pWstk s.core.wstk ⋆
       dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
       array64 (c.hdr + 32) (hdrTailWords c s) ⋆ FullScratchArraysNo3 c s.scratch ⋆
       c.pad ⋆ R)) m := by
    unfold FullMemNoWks3 FullCoreArrays FullCoreDynArrs at hm; ecancel
  rw [bv64_mul4_eq]; exact loadVal_array (by decide) hi h1

@[scoped c0_store] theorem c0_store_noWks3_scratch_buf {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64} (v : BitVec 32)
    (hi : i.toNat < s.scratch.scratch_buf.length) (hm : (FullMemNoWks3 c s ⋆ R) m) :
    storeOk m i32 (c.pScratchBuf + i * 4) ∧
      (FullMemNoWks3 c
        { s with scratch := { s.scratch with scratch_buf := s.scratch.scratch_buf.set i.toNat v } }
        ⋆ R) (storeMem m i32 (c.pScratchBuf + i * 4) v) := by
  have h1 := focus_noWks3_scratch_buf hm
  rw [bv64_mul4_eq]
  obtain ⟨hok, hst⟩ := store_array v (by decide) hi h1
  exact ⟨hok, unfocus_noWks3_scratch_buf hst⟩

end CongTactics

end

end LeanQbe.T.Examples.Kissat.Proof.Congruence
