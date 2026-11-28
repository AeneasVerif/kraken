/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Reorder
public import LeanQbe.T.Examples.Kissat.Proof.Reorder.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
public import LeanQbe.T.Logic.C0Step
public import LeanQbe.T.Logic.C0HeadStep
public import LeanQbe.T.Logic.ControlComb
public import Kraken.Mem
public import Kraken.Separation
import LeanQbe.T.AbiLemmas
import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
import LeanQbe.T.Logic.Bytes
import LeanQbe.T.Logic.Cells
import LeanQbe.T.Logic.MemLemmas
meta import LeanQbe.T.Logic.C0Step
meta import LeanQbe.T.Logic.C0HeadStep

/-!
# Memory Bridges & Scoped Accessor Tactics for `Proof.Reorder` (`Proof.Reorder.WpMem`)

1. `u32 <-> u64` pair packing (`packPairs64`, `unpackPairs32`, `array_i32_eq_array64_pack`,
   `array64_eq_array_i32_unpack`) and `ReorderMem <-> FullMem` bridges.
2. Scoped `ReorderTactics` (`@[scoped c0_load]` / `@[scoped c0_store]`) over `ReorderMem`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Reorder

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open LeanQbe.T.Examples.Kissat.Proof.Reorder.Spec
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open Kraken.Bedrock2.Test

/-! ## 1. `array32 <-> array64` Aliasing & `ReorderMem <-> FullMem` Bridges -/

/-- Pack adjacent `u32` pairs into little-endian `u64` words. -/
@[expose] def packPairs64 : List (BitVec 32) → List (BitVec 64)
  | [] => []
  | lo :: hi :: rest => ((hi.setWidth 64 <<< 32) ||| lo.setWidth 64) :: packPairs64 rest
  | [_] => []

/-- Unpack `u64` words back into little-endian `u32` pairs. -/
@[expose] def unpackPairs32 : List (BitVec 64) → List (BitVec 32)
  | [] => []
  | w :: rest => w.setWidth 32 :: (w >>> 32).setWidth 32 :: unpackPairs32 rest

theorem packPairs64_length : ∀ xs : List (BitVec 32),
    (packPairs64 xs).length = xs.length / 2
  | [] => rfl
  | [_] => by simp [packPairs64]
  | _ :: _ :: rest => by
    simp only [packPairs64, List.length_cons, packPairs64_length rest]; omega

theorem unpackPairs32_length (ys : List (BitVec 64)) :
    (unpackPairs32 ys).length = 2 * ys.length := by
  induction ys with
  | nil => rfl
  | cons _ _ ih => simp only [unpackPairs32, List.length_cons, ih]; omega

private theorem toBytes_8_split (w : BitVec 64) :
    Int.toBytes 8 (w.toNat : Int) =
      Int.toBytes 4 ((w.setWidth 32).toNat : Int) ++
        Int.toBytes 4 (((w >>> 32).setWidth 32).toNat : Int) := by
  have hw0 : ((w.setWidth 32).toNat : Int) = (w.toNat : Int) % (2 : Int) ^ (8 * 4) := by
    simp only [BitVec.toNat_setWidth]; omega
  have hw1 : (((w >>> 32).setWidth 32).toNat : Int) =
      ((w.toNat : Int) / (2 : Int) ^ 32) % (2 : Int) ^ (8 * 4) := by
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega
  rw [hw0, hw1, Int.toBytes_emod (n := 4) (x := (w.toNat : Int)),
    Int.toBytes_emod (n := 4) (x := (w.toNat : Int) / (2 : Int) ^ 32)]
  have hd : ∀ k : Int, (((k / 256) / 256) / 256) / 256 = k / (2 : Int) ^ 32 := fun k => by omega
  simp only [Int.toBytes, Int.take, List.cons_append, List.nil_append, hd]

private theorem cell_i32_eq_int4 (a : BitVec 64) (v : BitVec 32) :
    cell (t := i32) a v = int4 a (v.setWidth 64) := by
  unfold cell int4
  simp only [Ty.bytes, Ty.size, toBits, BitVec.setWidth_eq]
  congr 2
  rw [← Int.toBytes_emod, ← Int.toBytes_emod (x := ((v.setWidth 64).toNat : Int))]
  congr 1; dsimp only [Int.take]
  simp only [Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMul, BitVec.toInt_eq_msb_cond,
    BitVec.toNat_setWidth]
  have hlt : 0 ≤ (v.toNat : Int) ∧ (v.toNat : Int) < (2 ^ 32 : Int) :=
    ⟨Int.natCast_nonneg _, by exact_mod_cast v.isLt⟩
  have hlt64 : v.toNat < 2 ^ 64 := Nat.lt_trans v.isLt (by decide)
  rw [Nat.mod_eq_of_lt hlt64]
  cases v.msb
  · simp
  · simp only [↓reduceIte, Int.natCast_pow, Int.cast_ofNat_Int]; omega

private theorem cell64_eq_cell_i32_pair (a w : BitVec 64) :
    cell64 a w =
      (cell (t := i32) a (w.setWidth 32) ⋆ cell (t := i32) (a + 4) ((w >>> 32).setWidth 32)) := by
  rw [cell64_eq_word8, word8_eq_int4_sep, cell_i32_eq_int4, cell_i32_eq_int4,
    int4_setWidth32, int4_setWidth32]
  have hdrop : (Int.toBytes 8 (w.toNat : Int)).drop 4 =
      Int.toBytes 4 ((w >>> 32).toNat : Int) := by
    have h1 : (((w >>> 32).setWidth 32).toNat : Int) =
        ((w >>> 32).toNat : Int) % (2 : Int) ^ (8 * 4) := by
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega
    rw [toBytes_8_split, List.drop_left' (by simp [Int.toBytes_length]), h1, Int.toBytes_emod]
  unfold int4; rw [hdrop]

private theorem pack_pair_word (lo hi : BitVec 32) :
    let w : BitVec 64 := (hi.setWidth 64 <<< 32) ||| lo.setWidth 64
    w.setWidth 32 = lo ∧ (w >>> 32).setWidth 32 = hi := by
  dsimp only; constructor
  · apply BitVec.eq_of_getElem_eq; intro k hk; simp
  · apply BitVec.eq_of_getElem_eq; intro k hk
    have hk64 : k < 64 := by omega
    have h32 : 32 + k < 64 := by omega
    have hnot : ¬(32 + k < 32) := by omega
    simp [BitVec.getElem_setWidth, BitVec.getElem_ushiftRight, BitVec.getElem_or,
      BitVec.getElem_shiftLeft, BitVec.getLsbD_eq_getElem, hk, hk64, h32, hnot]

theorem array_i32_eq_array64_pack (a : BitVec 64) (xs : List (BitVec 32))
    (heven : xs.length % 2 = 0) :
    array (t := i32) a xs = array64 a (packPairs64 xs) := by
  match xs with
  | [] => rfl
  | [_] => simp at heven
  | lo :: hi :: rest =>
    have hrest : rest.length % 2 = 0 := by simp at heven; omega
    have hlo : (((hi.setWidth 64 <<< 32) ||| lo.setWidth 64).setWidth 32) = lo :=
      (pack_pair_word lo hi).1
    have hhi : ((((hi.setWidth 64 <<< 32) ||| lo.setWidth 64) >>> 32).setWidth 32) = hi :=
      (pack_pair_word lo hi).2
    have hstep : a + BitVec.ofNat 64 (Ty.bytes i32) + BitVec.ofNat 64 (Ty.bytes i32) = a + 8 := by
      change a + 4#64 + 4#64 = a + 8#64; bv_omega
    have h4 : a + BitVec.ofNat 64 (Ty.bytes i32) = a + 4 := by
      change a + 4#64 = a + 4; rfl
    rw [array_cons, array_cons, packPairs64, array64_cons,
      cell64_eq_cell_i32_pair, hlo, hhi, ← h4, hstep,
      array_i32_eq_array64_pack (a + 8) rest hrest, sep_assoc]

theorem array64_eq_array_i32_unpack (a : BitVec 64) (ys : List (BitVec 64)) :
    array64 a ys = array (t := i32) a (unpackPairs32 ys) := by
  induction ys generalizing a with
  | nil => rfl
  | cons w rest ih =>
    have hstep : a + BitVec.ofNat 64 (Ty.bytes i32) + BitVec.ofNat 64 (Ty.bytes i32) = a + 8 := by
      change a + 4#64 + 4#64 = a + 8#64; bv_omega
    have h4 : a + BitVec.ofNat 64 (Ty.bytes i32) = a + 4 := by
      change a + 4#64 = a + 4; rfl
    rw [array64_cons, cell64_eq_cell_i32_pair, unpackPairs32, array_cons, array_cons,
      ← h4, hstep, ih (a + 8), sep_assoc]

theorem reorderMem_of_fullMem {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hlen : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m) :
    ∃ wl wr : Arr64 c.max_vars, (ReorderMem c s wl wr ⋆ R) m := by
  have htm := hlen.scratch_ok.tarjan_mark_len; have htr := hlen.scratch_ok.tarjan_reach_len
  let wl : Arr64 c.max_vars := ⟨packPairs64 s.scratch.tarjan_mark, by
    rw [packPairs64_length, htm]; omega⟩
  let wr : Arr64 c.max_vars := ⟨packPairs64 s.scratch.tarjan_reach, by
    rw [packPairs64_length, htr]; omega⟩
  refine ⟨wl, wr, ?_⟩
  unfold FullMem FullScratchArrays FullScrWksArrs at hm
  rw [array_i32_eq_array64_pack c.pTarjanMark s.scratch.tarjan_mark (by omega),
    array_i32_eq_array64_pack c.pTarjanReach s.scratch.tarjan_reach (by omega)] at hm
  unfold ReorderMem; exact hm

theorem fullMem_of_reorderMem {c : FullCfg} {s : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (ReorderMem c s wl wr ⋆ R) m) :
    ∃ tmk trc : List (BitVec 32),
      tmk.length = 2 * c.max_vars ∧ trc.length = 2 * c.max_vars ∧
      (FullMem c { s with scratch := { s.scratch with tarjan_mark := tmk, tarjan_reach := trc } } ⋆
        R) m := by
  let tmk := unpackPairs32 wl.1; let trc := unpackPairs32 wr.1
  refine ⟨tmk, trc, by simp [tmk, unpackPairs32_length, wl.2],
    by simp [trc, unpackPairs32_length, wr.2], ?_⟩
  unfold ReorderMem at hm
  rw [array64_eq_array_i32_unpack c.pTarjanMark wl.1,
    array64_eq_array_i32_unpack c.pTarjanReach wr.1] at hm
  unfold FullMem FullScratchArrays FullScrWksArrs; exact hm

private theorem rm_bv64_mul4 (i : BitVec 64) :
    (i * 4 : BitVec 64) = BitVec.ofNat 64 (4 * i.toNat) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_mul, Nat.mul_comm]

private theorem rm_bv64_mul8 (i : BitVec 64) :
    (i * 8 : BitVec 64) = BitVec.ofNat 64 (8 * i.toNat) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_mul, Nat.mul_comm]

/-! ## 2. `ReorderTactics` (`c0_load` / `c0_store` Lemmas) -/

namespace ReorderTactics

@[scoped c0_load] theorem load_re_arena_len {c : FullCfg} {s : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (ReorderMem c s wl wr ⋆ R) m) :
    loadVal m i64 (c.hdr + 48) = some (BitVec.ofNat 64 s.core.arena_len) := by
  obtain ⟨_, _, _, _, hmF⟩ := fullMem_of_reorderMem hm; simpa using load_full_arena_len hmF

@[scoped c0_load] theorem load_re_wlen {c : FullCfg} {s : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (ReorderMem c s wl wr ⋆ R) m) :
    loadVal m i64 (c.hdr + 56) = some (BitVec.ofNat 64 s.core.wlen) := by
  obtain ⟨_, _, _, _, hmF⟩ := fullMem_of_reorderMem hm; simpa using load_full_wlen hmF

@[scoped c0_load] theorem load_re_values_ptr {c : FullCfg} {s : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (ReorderMem c s wl wr ⋆ R) m) : loadVal m i64 (c.hdr + 64) = some c.pVals := by
  obtain ⟨_, _, _, _, hmF⟩ := fullMem_of_reorderMem hm; simpa using load_full_values_ptr hmF

@[scoped c0_load] theorem load_re_watch_vec_ptr {c : FullCfg} {s : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (ReorderMem c s wl wr ⋆ R) m) : loadVal m i64 (c.hdr + 104) = some c.pWvec := by
  obtain ⟨_, _, _, _, hmF⟩ := fullMem_of_reorderMem hm; simpa using load_full_watch_vec_ptr hmF

@[scoped c0_load] theorem load_re_arena_ptr {c : FullCfg} {s : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (ReorderMem c s wl wr ⋆ R) m) : loadVal m i64 (c.hdr + 112) = some c.pArena := by
  obtain ⟨_, _, _, _, hmF⟩ := fullMem_of_reorderMem hm; simpa using load_full_arena_ptr hmF

@[scoped c0_load] theorem load_re_watch_stk_ptr {c : FullCfg} {s : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (ReorderMem c s wl wr ⋆ R) m) : loadVal m i64 (c.hdr + 120) = some c.pWstk := by
  obtain ⟨_, _, _, _, hmF⟩ := fullMem_of_reorderMem hm; simpa using load_full_watch_stk_ptr hmF

@[scoped c0_load] theorem load_re_score_ptr {c : FullCfg} {s : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (ReorderMem c s wl wr ⋆ R) m) : loadVal m i64 (c.hdr + 216) = some c.pScore := by
  obtain ⟨_, _, _, _, hmF⟩ := fullMem_of_reorderMem hm; simpa using load_full_score_ptr hmF

@[scoped c0_load] theorem load_re_scinc {c : FullCfg} {s : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (ReorderMem c s wl wr ⋆ R) m) :
    loadVal m i64 (c.hdr + 256) = some s.scratch.scinc := by
  obtain ⟨_, _, _, _, hmF⟩ := fullMem_of_reorderMem hm; simpa using load_full_scinc hmF

@[scoped c0_load] theorem load_re_q_prev_ptr {c : FullCfg} {s : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (ReorderMem c s wl wr ⋆ R) m) : loadVal m i64 (c.hdr + 368) = some c.pQPrev := by
  obtain ⟨_, _, _, _, hmF⟩ := fullMem_of_reorderMem hm; simpa using load_full_q_prev_ptr hmF

@[scoped c0_load] theorem load_re_q_next_ptr {c : FullCfg} {s : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (ReorderMem c s wl wr ⋆ R) m) : loadVal m i64 (c.hdr + 376) = some c.pQNext := by
  obtain ⟨_, _, _, _, hmF⟩ := fullMem_of_reorderMem hm; simpa using load_full_q_next_ptr hmF

@[scoped c0_load] theorem load_re_q_stamp_ptr {c : FullCfg} {s : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (ReorderMem c s wl wr ⋆ R) m) : loadVal m i64 (c.hdr + 384) = some c.pQStamp := by
  obtain ⟨_, _, _, _, hmF⟩ := fullMem_of_reorderMem hm; simpa using load_full_q_stamp_ptr hmF

@[scoped c0_load] theorem load_re_wsort_ptr {c : FullCfg} {s : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (ReorderMem c s wl wr ⋆ R) m) : loadVal m i64 (c.hdr + 408) = some c.pWsort := by
  obtain ⟨_, _, _, _, hmF⟩ := fullMem_of_reorderMem hm; simpa using load_full_wsort_ptr hmF

@[scoped c0_load] theorem load_re_stable {c : FullCfg} {s : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (ReorderMem c s wl wr ⋆ R) m) :
    loadVal m i64 (c.hdr + 552) = some s.scratch.stable := by
  obtain ⟨_, _, _, _, hmF⟩ := fullMem_of_reorderMem hm; simpa using load_full_stable hmF

@[scoped c0_load] theorem load_re_cur_vars {c : FullCfg} {s : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (ReorderMem c s wl wr ⋆ R) m) :
    loadVal m i64 (c.hdr + 776) = some (BitVec.ofNat 64 s.core.cur_vars) := by
  obtain ⟨_, _, _, _, hmF⟩ := fullMem_of_reorderMem hm; simpa using load_full_cur_vars hmF

@[scoped c0_load] theorem load_re_flags_ptr {c : FullCfg} {s : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (ReorderMem c s wl wr ⋆ R) m) : loadVal m i64 (c.hdr + 800) = some c.pFlags := by
  obtain ⟨_, _, _, _, hmF⟩ := fullMem_of_reorderMem hm; simpa using load_full_flags_ptr hmF

@[scoped c0_load] theorem load_re_tarjan_mark_ptr {c : FullCfg} {s : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (ReorderMem c s wl wr ⋆ R) m) :
    loadVal m i64 (c.hdr + 864) = some c.pTarjanMark := by
  obtain ⟨_, _, _, _, hmF⟩ := fullMem_of_reorderMem hm
  simpa using load_full_tarjan_mark_ptr hmF

@[scoped c0_load] theorem load_re_tarjan_reach_ptr {c : FullCfg} {s : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (ReorderMem c s wl wr ⋆ R) m) :
    loadVal m i64 (c.hdr + 872) = some c.pTarjanReach := by
  obtain ⟨_, _, _, _, hmF⟩ := fullMem_of_reorderMem hm
  simpa using load_full_tarjan_reach_ptr hmF

@[scoped c0_load] theorem c0_load_re_vals {c : FullCfg} {s : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hi : i.toNat < s.core.vals.length) (hm : (ReorderMem c s wl wr ⋆ R) m) :
    loadVal m i8 (c.pVals + i) = some s.core.vals[i.toNat] := by
  obtain ⟨tmk, trc, _, _, hmF⟩ := fullMem_of_reorderMem hm
  let s' := { s with scratch := { s.scratch with tarjan_mark := tmk, tarjan_reach := trc } }
  simpa [s'] using c0_load_full_vals (s := s') hi hmF

@[scoped c0_load] theorem c0_load_re_flags {c : FullCfg} {s : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hi : i.toNat < s.core.flags.length) (hm : (ReorderMem c s wl wr ⋆ R) m) :
    loadVal m i32 (c.pFlags + i * 4) = some s.core.flags[i.toNat] := by
  obtain ⟨tmk, trc, _, _, hmF⟩ := fullMem_of_reorderMem hm
  let s' := { s with scratch := { s.scratch with tarjan_mark := tmk, tarjan_reach := trc } }
  simpa [s'] using c0_load_full_flags (s := s') hi hmF

@[scoped c0_load] theorem c0_load_re_arena {c : FullCfg} {s : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hi : i.toNat < s.core.arena.length) (hm : (ReorderMem c s wl wr ⋆ R) m) :
    loadVal m i32 (c.pArena + i * 4) = some s.core.arena[i.toNat] := by
  obtain ⟨tmk, trc, _, _, hmF⟩ := fullMem_of_reorderMem hm
  let s' := { s with scratch := { s.scratch with tarjan_mark := tmk, tarjan_reach := trc } }
  simpa [s'] using c0_load_full_arena (s := s') hi hmF

@[scoped c0_load] theorem c0_load_re_wvec {c : FullCfg} {s : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hi : i.toNat < s.core.wvec.length) (hm : (ReorderMem c s wl wr ⋆ R) m) :
    loadVal m i32 (c.pWvec + i * 4) = some s.core.wvec[i.toNat] := by
  obtain ⟨tmk, trc, _, _, hmF⟩ := fullMem_of_reorderMem hm
  let s' := { s with scratch := { s.scratch with tarjan_mark := tmk, tarjan_reach := trc } }
  simpa [s'] using c0_load_full_wvec (s := s') hi hmF

@[scoped c0_load] theorem c0_load_re_wstk {c : FullCfg} {s : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hi : i.toNat < s.core.wstk.length) (hm : (ReorderMem c s wl wr ⋆ R) m) :
    loadVal m i32 (c.pWstk + i * 4) = some s.core.wstk[i.toNat] := by
  obtain ⟨tmk, trc, _, _, hmF⟩ := fullMem_of_reorderMem hm
  let s' := { s with scratch := { s.scratch with tarjan_mark := tmk, tarjan_reach := trc } }
  simpa [s'] using c0_load_full_wstk (s := s') hi hmF

@[scoped c0_load] theorem c0_load_re_q_stamp {c : FullCfg} {s : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hi : i.toNat < s.scratch.q_stamp.length) (hm : (ReorderMem c s wl wr ⋆ R) m) :
    loadVal m i32 (c.pQStamp + i * 4) = some s.scratch.q_stamp[i.toNat] := by
  obtain ⟨tmk, trc, _, _, hmF⟩ := fullMem_of_reorderMem hm
  let s' := { s with scratch := { s.scratch with tarjan_mark := tmk, tarjan_reach := trc } }
  simpa [s'] using c0_load_full_q_stamp (s := s') hi hmF

@[scoped c0_load] theorem c0_load_re_wsort {c : FullCfg} {s : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hi : i.toNat < s.scratch.wsort.length) (hm : (ReorderMem c s wl wr ⋆ R) m) :
    loadVal m i32 (c.pWsort + i * 4) = some s.scratch.wsort[i.toNat] := by
  obtain ⟨tmk, trc, _, _, hmF⟩ := fullMem_of_reorderMem hm
  let s' := { s with scratch := { s.scratch with tarjan_mark := tmk, tarjan_reach := trc } }
  simpa [s'] using c0_load_full_wsort (s := s') hi hmF

@[scoped c0_load] theorem load_re_wsort0 {c : FullCfg} {s : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hi : 0 < s.scratch.wsort.length) (hm : (ReorderMem c s wl wr ⋆ R) m) :
    loadVal m i32 c.pWsort = some s.scratch.wsort[0] := by
  obtain ⟨tmk, trc, _, _, hmF⟩ := fullMem_of_reorderMem hm
  let s' := { s with scratch := { s.scratch with tarjan_mark := tmk, tarjan_reach := trc } }
  simpa [s'] using load_full_wsort0 (s := s') hi hmF

@[scoped c0_load] theorem c0_load_re_score {c : FullCfg} {s : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hi : i.toNat < s.scratch.score.length) (hm : (ReorderMem c s wl wr ⋆ R) m) :
    loadVal m i64 (c.pScore + i * 8) = some s.scratch.score[i.toNat] := by
  obtain ⟨tmk, trc, _, _, hmF⟩ := fullMem_of_reorderMem hm
  let s' := { s with scratch := { s.scratch with tarjan_mark := tmk, tarjan_reach := trc } }
  simpa [s'] using c0_load_full_score (s := s') hi hmF

@[scoped c0_store] theorem store_re_score {c : FullCfg} {s : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : Nat} (v : BitVec 64)
    (hi : i < s.scratch.score.length) (hm : (ReorderMem c s wl wr ⋆ R) m) :
    storeOk m i64 (c.pScore + BitVec.ofNat 64 (8 * i)) ∧
      (ReorderMem c { s with scratch := { s.scratch with score := s.scratch.score.set i v } }
        wl wr ⋆ R) (storeMem m i64 (c.pScore + BitVec.ofNat 64 (8 * i)) v) := by
  unfold ReorderMem FullScrMetaArrs at hm ⊢
  change _ ∧ (dimacsState c.hdr _ _ _ _ ⋆ array64 (c.hdr + 32) (hdrTailWords c s) ⋆
    FullCoreArrays c s.core ⋆ (FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆
    (array (t := i32) c.pWsort s.scratch.wsort ⋆
    array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆
    array (t := i32) c.pWorkStk2 s.scratch.work_stk2 ⋆
    array64 c.pTarjanMark wl.1 ⋆ array64 c.pTarjanReach wr.1) ⋆
    (array64 c.pScore (s.scratch.score.set i v) ⋆ array64 c.pSimSig s.scratch.sim_sig ⋆
    array (t := i32) c.pGlueUsed s.scratch.glue_used ⋆
    array (t := i32) c.pLastLearned s.scratch.last_learned) ⋆
    FullScrDynArrs c s.scratch) ⋆ c.pad ⋆ R) _
  have hm' : (array64 c.pScore s.scratch.score ⋆
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
        s.core.d_cur s.core.d_val ⋆
      array64 (c.hdr + 32) (hdrTailWords c s) ⋆ FullCoreArrays c s.core ⋆
      FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆
      array (t := i32) c.pWsort s.scratch.wsort ⋆
      array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆
      array (t := i32) c.pWorkStk2 s.scratch.work_stk2 ⋆
      array64 c.pTarjanMark wl.1 ⋆ array64 c.pTarjanReach wr.1 ⋆
      array64 c.pSimSig s.scratch.sim_sig ⋆
      array (t := i32) c.pGlueUsed s.scratch.glue_used ⋆
      array (t := i32) c.pLastLearned s.scratch.last_learned ⋆
      FullScrDynArrs c s.scratch ⋆ c.pad ⋆ R)) m := by ecancel
  obtain ⟨h1, h2⟩ := store_array64 v hi hm'
  exact ⟨h1, by clear hm hm'; ecancel⟩

@[scoped c0_store] theorem c0_store_re_score {c : FullCfg} {s : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64} (v : BitVec 64)
    (hi : i.toNat < s.scratch.score.length) (hm : (ReorderMem c s wl wr ⋆ R) m) :
    storeOk m i64 (c.pScore + i * 8) ∧
      (ReorderMem c
        { s with scratch := { s.scratch with score := s.scratch.score.set i.toNat v } }
        wl wr ⋆ R) (storeMem m i64 (c.pScore + i * 8) v) := by
  rw [rm_bv64_mul8]; exact store_re_score v hi hm

@[scoped c0_store] theorem store_re_wsort {c : FullCfg} {s : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : Nat} (v : BitVec 32)
    (hi : i < s.scratch.wsort.length) (hm : (ReorderMem c s wl wr ⋆ R) m) :
    storeOk m i32 (c.pWsort + BitVec.ofNat 64 (4 * i)) ∧
      (ReorderMem c { s with scratch := { s.scratch with wsort := s.scratch.wsort.set i v } }
        wl wr ⋆ R) (storeMem m i32 (c.pWsort + BitVec.ofNat 64 (4 * i)) v) := by
  unfold ReorderMem at hm ⊢
  change _ ∧ (dimacsState c.hdr _ _ _ _ ⋆ array64 (c.hdr + 32) (hdrTailWords c s) ⋆
    FullCoreArrays c s.core ⋆ (FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆
    (array (t := i32) c.pWsort (s.scratch.wsort.set i v) ⋆
    array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆
    array (t := i32) c.pWorkStk2 s.scratch.work_stk2 ⋆
    array64 c.pTarjanMark wl.1 ⋆ array64 c.pTarjanReach wr.1) ⋆
    FullScrMetaArrs c s.scratch ⋆ FullScrDynArrs c s.scratch) ⋆ c.pad ⋆ R) _
  have hm' : (array (t := i32) c.pWsort s.scratch.wsort ⋆
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
        s.core.d_cur s.core.d_val ⋆
      array64 (c.hdr + 32) (hdrTailWords c s) ⋆ FullCoreArrays c s.core ⋆
      FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆
      array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆
      array (t := i32) c.pWorkStk2 s.scratch.work_stk2 ⋆
      array64 c.pTarjanMark wl.1 ⋆ array64 c.pTarjanReach wr.1 ⋆
      FullScrMetaArrs c s.scratch ⋆ FullScrDynArrs c s.scratch ⋆ c.pad ⋆ R)) m := by ecancel
  obtain ⟨h1, h2⟩ := store_array (t := i32) v (by decide) hi hm'
  have h2' : (array (t := i32) c.pWsort (s.scratch.wsort.set i v) ⋆
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
        s.core.d_cur s.core.d_val ⋆
      array64 (c.hdr + 32) (hdrTailWords c s) ⋆ FullCoreArrays c s.core ⋆
      FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆
      array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆
      array (t := i32) c.pWorkStk2 s.scratch.work_stk2 ⋆
      array64 c.pTarjanMark wl.1 ⋆ array64 c.pTarjanReach wr.1 ⋆
      FullScrMetaArrs c s.scratch ⋆ FullScrDynArrs c s.scratch ⋆ c.pad ⋆ R))
      (storeMem m i32 (c.pWsort + BitVec.ofNat 64 (4 * i)) v) := by
    simpa only [Ty.bytes, Ty.size, Nat.mul_comm] using h2
  exact ⟨h1, by clear hm hm'; ecancel⟩

@[scoped c0_store] theorem c0_store_re_wsort {c : FullCfg} {s : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64} (v : BitVec 32)
    (hi : i.toNat < s.scratch.wsort.length) (hm : (ReorderMem c s wl wr ⋆ R) m) :
    storeOk m i32 (c.pWsort + i * 4) ∧
      (ReorderMem c
        { s with scratch := { s.scratch with wsort := s.scratch.wsort.set i.toNat v } }
        wl wr ⋆ R) (storeMem m i32 (c.pWsort + i * 4) v) := by
  rw [rm_bv64_mul4]; exact store_re_wsort v hi hm

@[scoped c0_store] theorem store_re_wsort0 {c : FullCfg} {s : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32)
    (hi : 0 < s.scratch.wsort.length) (hm : (ReorderMem c s wl wr ⋆ R) m) :
    storeOk m i32 c.pWsort ∧
      (ReorderMem c { s with scratch := { s.scratch with wsort := s.scratch.wsort.set 0 v } }
        wl wr ⋆ R) (storeMem m i32 c.pWsort v) := by
  simpa using store_re_wsort v hi hm

@[scoped c0_load] theorem load_re_wl {c : FullCfg} {s : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : Nat}
    (hi : i < c.max_vars) (hm : (ReorderMem c s wl wr ⋆ R) m) :
    loadVal m i64 (c.pTarjanMark + BitVec.ofNat 64 (8 * i)) =
      some (wl.1[i]'(by rw [wl.2]; exact hi)) := by
  unfold ReorderMem at hm
  exact loadVal_array64 (R := _) (by rw [wl.2]; exact hi) (by ecancel)

@[scoped c0_load] theorem c0_load_re_wl {c : FullCfg} {s : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hi : i.toNat < c.max_vars) (hm : (ReorderMem c s wl wr ⋆ R) m) :
    loadVal m i64 (c.pTarjanMark + i * 8) =
      some (wl.1[i.toNat]'(by rw [wl.2]; exact hi)) := by
  rw [rm_bv64_mul8]; exact load_re_wl hi hm

@[scoped c0_load] theorem load_re_wl0 {c : FullCfg} {s : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hi : 0 < c.max_vars) (hm : (ReorderMem c s wl wr ⋆ R) m) :
    loadVal m i64 c.pTarjanMark = some (wl.1[0]'(by rw [wl.2]; exact hi)) := by
  simpa using load_re_wl hi hm

@[scoped c0_store] theorem store_re_wl {c : FullCfg} {s : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : Nat} (v : BitVec 64)
    (hi : i < c.max_vars) (hm : (ReorderMem c s wl wr ⋆ R) m) :
    storeOk m i64 (c.pTarjanMark + BitVec.ofNat 64 (8 * i)) ∧
      (ReorderMem c s ⟨wl.1.set i v, by simp [wl.2]⟩ wr ⋆ R)
        (storeMem m i64 (c.pTarjanMark + BitVec.ofNat 64 (8 * i)) v) := by
  unfold ReorderMem at hm ⊢
  have hi' : i < wl.1.length := by rw [wl.2]; exact hi
  have hm' : (array64 c.pTarjanMark wl.1 ⋆
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
        s.core.d_cur s.core.d_val ⋆
      array64 (c.hdr + 32) (hdrTailWords c s) ⋆ FullCoreArrays c s.core ⋆
      FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆
      array (t := i32) c.pWsort s.scratch.wsort ⋆
      array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆
      array (t := i32) c.pWorkStk2 s.scratch.work_stk2 ⋆
      array64 c.pTarjanReach wr.1 ⋆ FullScrMetaArrs c s.scratch ⋆
      FullScrDynArrs c s.scratch ⋆ c.pad ⋆ R)) m := by ecancel
  obtain ⟨h1, h2⟩ := store_array64 v hi' hm'
  exact ⟨h1, by ecancel⟩

@[scoped c0_store] theorem c0_store_re_wl {c : FullCfg} {s : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64} (v : BitVec 64)
    (hi : i.toNat < c.max_vars) (hm : (ReorderMem c s wl wr ⋆ R) m) :
    storeOk m i64 (c.pTarjanMark + i * 8) ∧
      (ReorderMem c s ⟨wl.1.set i.toNat v, by simp [wl.2]⟩ wr ⋆ R)
        (storeMem m i64 (c.pTarjanMark + i * 8) v) := by
  rw [rm_bv64_mul8]; exact store_re_wl v hi hm

@[scoped c0_store] theorem store_re_wl0 {c : FullCfg} {s : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 64)
    (hi : 0 < c.max_vars) (hm : (ReorderMem c s wl wr ⋆ R) m) :
    storeOk m i64 c.pTarjanMark ∧
      (ReorderMem c s ⟨wl.1.set 0 v, by simp [wl.2]⟩ wr ⋆ R)
        (storeMem m i64 c.pTarjanMark v) := by
  simpa using store_re_wl v hi hm

@[scoped c0_load] theorem load_re_wr {c : FullCfg} {s : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : Nat}
    (hi : i < c.max_vars) (hm : (ReorderMem c s wl wr ⋆ R) m) :
    loadVal m i64 (c.pTarjanReach + BitVec.ofNat 64 (8 * i)) =
      some (wr.1[i]'(by rw [wr.2]; exact hi)) := by
  unfold ReorderMem at hm
  exact loadVal_array64 (R := _) (by rw [wr.2]; exact hi) (by ecancel)

@[scoped c0_load] theorem c0_load_re_wr {c : FullCfg} {s : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hi : i.toNat < c.max_vars) (hm : (ReorderMem c s wl wr ⋆ R) m) :
    loadVal m i64 (c.pTarjanReach + i * 8) =
      some (wr.1[i.toNat]'(by rw [wr.2]; exact hi)) := by
  rw [rm_bv64_mul8]; exact load_re_wr hi hm

@[scoped c0_load] theorem load_re_wr0 {c : FullCfg} {s : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hi : 0 < c.max_vars) (hm : (ReorderMem c s wl wr ⋆ R) m) :
    loadVal m i64 c.pTarjanReach = some (wr.1[0]'(by rw [wr.2]; exact hi)) := by
  simpa using load_re_wr hi hm

@[scoped c0_store] theorem store_re_wr {c : FullCfg} {s : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : Nat} (v : BitVec 64)
    (hi : i < c.max_vars) (hm : (ReorderMem c s wl wr ⋆ R) m) :
    storeOk m i64 (c.pTarjanReach + BitVec.ofNat 64 (8 * i)) ∧
      (ReorderMem c s wl ⟨wr.1.set i v, by simp [wr.2]⟩ ⋆ R)
        (storeMem m i64 (c.pTarjanReach + BitVec.ofNat 64 (8 * i)) v) := by
  unfold ReorderMem at hm ⊢
  have hi' : i < wr.1.length := by rw [wr.2]; exact hi
  have hm' : (array64 c.pTarjanReach wr.1 ⋆
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
        s.core.d_cur s.core.d_val ⋆
      array64 (c.hdr + 32) (hdrTailWords c s) ⋆ FullCoreArrays c s.core ⋆
      FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆
      array (t := i32) c.pWsort s.scratch.wsort ⋆
      array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆
      array (t := i32) c.pWorkStk2 s.scratch.work_stk2 ⋆
      array64 c.pTarjanMark wl.1 ⋆ FullScrMetaArrs c s.scratch ⋆
      FullScrDynArrs c s.scratch ⋆ c.pad ⋆ R)) m := by ecancel
  obtain ⟨h1, h2⟩ := store_array64 v hi' hm'
  exact ⟨h1, by ecancel⟩

@[scoped c0_store] theorem c0_store_re_wr {c : FullCfg} {s : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64} (v : BitVec 64)
    (hi : i.toNat < c.max_vars) (hm : (ReorderMem c s wl wr ⋆ R) m) :
    storeOk m i64 (c.pTarjanReach + i * 8) ∧
      (ReorderMem c s wl ⟨wr.1.set i.toNat v, by simp [wr.2]⟩ ⋆ R)
        (storeMem m i64 (c.pTarjanReach + i * 8) v) := by
  rw [rm_bv64_mul8]; exact store_re_wr v hi hm

@[scoped c0_store] theorem store_re_wr0 {c : FullCfg} {s : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 64)
    (hi : 0 < c.max_vars) (hm : (ReorderMem c s wl wr ⋆ R) m) :
    storeOk m i64 c.pTarjanReach ∧
      (ReorderMem c s wl ⟨wr.1.set 0 v, by simp [wr.2]⟩ ⋆ R)
        (storeMem m i64 c.pTarjanReach v) := by
  simpa using store_re_wr v hi hm

end ReorderTactics

end LeanQbe.T.Examples.Kissat.Proof.Reorder
