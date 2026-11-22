module

public import LeanQbe.T.Examples.Kissat.FullM7Reorder
public import LeanQbe.T.Examples.Kissat.FullM4TernaryProof
import LeanQbe.T.AbiLemmas
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.SolverArena
import LeanQbe.T.Logic.Bytes
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.Cells
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.MemLemmas
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Wave 4 `PR-W4B`: Proofs for Weighted VMTF Reorder (`FullM7ReorderProof`)

M1-clean (zero expose, zero import-all) UNSAT-only correctness proofs (`XPost := False`) for
`m7ReorderModule`:
1. `m7ReorderWeightSpec` and `full_reorder_weight_m7_wp`.
2. `m7ReorderSiftSpec` and `full_reorder_sift_m7_wp` over `(u64 *)`-aliased `tarjan_mark` /
   `tarjan_reach` (`ReorderMem`).
3. `full_reorder_queue_m7_wp` proving exact `FullM4Ternary.fullReorderQueueSpec`.
4. `m7ReorderSpecTable`, `m7ReorderEnv`, `m7Reorder_moduleOk`, `m7ReorderQueueFn_wp`, and concrete
   `Mem 64` UNSAT NV `nv_m7_reorder_queue`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7Reorder

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM4Ternary
open Kraken.Bedrock2.Test

/-! ## 1. `ReorderMem` Aliasing (`tarjan_mark` / `tarjan_reach` as `array64`) & Tactics -/

/-- Fixed-length `u64` array view (`n` elements). -/
abbrev Arr64 (n : Nat) := { xs : List (BitVec 64) // xs.length = n }

private def packPairs64 : List (BitVec 32) → List (BitVec 64)
  | [] => []
  | lo :: hi :: rest => ((hi.setWidth 64 <<< 32) ||| lo.setWidth 64) :: packPairs64 rest
  | [_] => []

private def unpackPairs32 : List (BitVec 64) → List (BitVec 32)
  | [] => []
  | w :: rest => w.setWidth 32 :: (w >>> 32).setWidth 32 :: unpackPairs32 rest

private theorem packPairs64_single (x : BitVec 32) : packPairs64 [x] = [] := rfl

private theorem packPairs64_cons (lo hi : BitVec 32) (rest : List (BitVec 32)) :
    packPairs64 (lo :: hi :: rest) =
      ((hi.setWidth 64 <<< 32) ||| lo.setWidth 64) :: packPairs64 rest := rfl

private theorem unpackPairs32_cons (w : BitVec 64) (rest : List (BitVec 64)) :
    unpackPairs32 (w :: rest) =
      w.setWidth 32 :: (w >>> 32).setWidth 32 :: unpackPairs32 rest := rfl

private theorem packPairs64_length : ∀ xs : List (BitVec 32),
    (packPairs64 xs).length = xs.length / 2
  | [] => rfl
  | [_] => by rw [packPairs64_single]; simp
  | _ :: _ :: rest => by
    rw [packPairs64_cons, List.length_cons, packPairs64_length rest]; simp; omega

private theorem unpackPairs32_length (ys : List (BitVec 64)) :
    (unpackPairs32 ys).length = 2 * ys.length := by
  induction ys with
  | nil => rfl
  | cons _ _ ih =>
    rw [unpackPairs32_cons]
    simp only [List.length_cons, ih]; omega

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
  have hd : ∀ (k : Int),
      (((k / 256) / 256) / 256) / 256 = k / (2 : Int) ^ 32 := fun k => by omega
  simp only [Int.toBytes, Int.take, List.cons_append, List.nil_append, hd]

private theorem cell_i32_eq_int4 (a : BitVec 64) (v : BitVec 32) :
    cell (t := i32) a v = int4 a (v.setWidth 64) := by
  unfold cell int4
  simp only [Ty.bytes, Ty.size, toBits, BitVec.setWidth_eq]
  congr 2
  rw [← Int.toBytes_emod, ← Int.toBytes_emod (x := ((v.setWidth 64).toNat : Int))]
  congr 1
  dsimp only [Int.take]
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
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      omega
    rw [toBytes_8_split, List.drop_left' (by simp [Int.toBytes_length]), h1, Int.toBytes_emod]
  unfold int4
  rw [hdrop]

private theorem pack_pair_word (lo hi : BitVec 32) :
    let w : BitVec 64 := (hi.setWidth 64 <<< 32) ||| lo.setWidth 64
    w.setWidth 32 = lo ∧ (w >>> 32).setWidth 32 = hi := by
  dsimp only
  constructor
  · apply BitVec.eq_of_getElem_eq; intro k hk
    simp
  · apply BitVec.eq_of_getElem_eq; intro k hk
    have hk64 : k < 64 := by omega
    have h32 : 32 + k < 64 := by omega
    have hnot : ¬(32 + k < 32) := by omega
    simp [BitVec.getElem_setWidth, BitVec.getElem_ushiftRight, BitVec.getElem_or,
      BitVec.getElem_shiftLeft, BitVec.getLsbD_eq_getElem, hk, hk64, h32, hnot]

private theorem array_i32_eq_array64_pack (a : BitVec 64) (xs : List (BitVec 32))
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
    rw [array_cons, array_cons, packPairs64_cons, array64_cons,
      cell64_eq_cell_i32_pair, hlo, hhi, ← h4, hstep,
      array_i32_eq_array64_pack (a + 8) rest hrest, sep_assoc]

private theorem array64_eq_array_i32_unpack (a : BitVec 64) (ys : List (BitVec 64)) :
    array64 a ys = array (t := i32) a (unpackPairs32 ys) := by
  induction ys generalizing a with
  | nil => rfl
  | cons w rest ih =>
    have hstep : a + BitVec.ofNat 64 (Ty.bytes i32) + BitVec.ofNat 64 (Ty.bytes i32) = a + 8 := by
      change a + 4#64 + 4#64 = a + 8#64; bv_omega
    have h4 : a + BitVec.ofNat 64 (Ty.bytes i32) = a + 4 := by
      change a + 4#64 = a + 4; rfl
    rw [array64_cons, unpackPairs32_cons, array_cons, array_cons,
      cell64_eq_cell_i32_pair, ← h4, hstep, ih (a + 8), sep_assoc]

/-- Variant of `FullMem` viewing `tarjan_mark` and `tarjan_reach` as `max_vars`-length `u64`
arrays (`wl`, `wr`). -/
def ReorderMem (c : FullCfg) (s : FullState) (wl wr : Arr64 c.max_vars) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
  FullCoreArrays c s.core ⋆
  (FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆
    (array (t := i32) c.pWsort s.scratch.wsort ⋆
      array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆
      array (t := i32) c.pWorkStk2 s.scratch.work_stk2 ⋆
      array64 c.pTarjanMark wl.1 ⋆ array64 c.pTarjanReach wr.1) ⋆
    FullScrMetaArrs c s.scratch ⋆ FullScrDynArrs c s.scratch) ⋆
  c.pad

/-- Boundedness of `wsort[0 ..< n)` indices below `cur_vars`. -/
def WsortBounded (wsort : List (BitVec 32)) (n cv : Nat) : Prop :=
  ∀ i < n, (wsort[i]?.getD 0#32).toNat < cv

private theorem reorderMem_of_fullMem {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hlen : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m) :
    ∃ wl wr : Arr64 c.max_vars, (ReorderMem c s wl wr ⋆ R) m := by
  have htm := hlen.scratch_ok.tarjan_mark_len
  have htr := hlen.scratch_ok.tarjan_reach_len
  let wl : Arr64 c.max_vars := ⟨packPairs64 s.scratch.tarjan_mark, by
    rw [packPairs64_length, htm]; omega⟩
  let wr : Arr64 c.max_vars := ⟨packPairs64 s.scratch.tarjan_reach, by
    rw [packPairs64_length, htr]; omega⟩
  refine ⟨wl, wr, ?_⟩
  unfold FullMem FullScratchArrays FullScrWksArrs at hm
  rw [array_i32_eq_array64_pack c.pTarjanMark s.scratch.tarjan_mark (by omega),
    array_i32_eq_array64_pack c.pTarjanReach s.scratch.tarjan_reach (by omega)] at hm
  unfold ReorderMem
  exact hm

private theorem fullMem_of_reorderMem {c : FullCfg} {s : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (ReorderMem c s wl wr ⋆ R) m) :
    ∃ tmk trc : List (BitVec 32),
      tmk.length = 2 * c.max_vars ∧ trc.length = 2 * c.max_vars ∧
      (FullMem c { s with scratch := { s.scratch with tarjan_mark := tmk, tarjan_reach := trc } } ⋆
        R) m := by
  let tmk := unpackPairs32 wl.1
  let trc := unpackPairs32 wr.1
  refine ⟨tmk, trc, by simp [tmk, unpackPairs32_length, wl.2],
    by simp [trc, unpackPairs32_length, wr.2], ?_⟩
  unfold ReorderMem at hm
  rw [array64_eq_array_i32_unpack c.pTarjanMark wl.1,
    array64_eq_array_i32_unpack c.pTarjanReach wr.1] at hm
  unfold FullMem FullScratchArrays FullScrWksArrs
  exact hm

private theorem bv64_mul4_eq (i : BitVec 64) :
    (i * 4 : BitVec 64) = BitVec.ofNat 64 (4 * i.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, Nat.mul_comm]

private theorem bv64_mul8_eq (i : BitVec 64) :
    (i * 8 : BitVec 64) = BitVec.ofNat 64 (8 * i.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, Nat.mul_comm]

namespace ReorderTactics

open FullArenaTactics
open scoped FullArenaTactics

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
    (hm : (ReorderMem c s wl wr ⋆ R) m) :
    loadVal m i64 (c.hdr + 64) = some c.pVals := by
  obtain ⟨_, _, _, _, hmF⟩ := fullMem_of_reorderMem hm; simpa using load_full_values_ptr hmF

@[scoped c0_load] theorem load_re_watch_vec_ptr {c : FullCfg} {s : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (ReorderMem c s wl wr ⋆ R) m) :
    loadVal m i64 (c.hdr + 104) = some c.pWvec := by
  obtain ⟨_, _, _, _, hmF⟩ := fullMem_of_reorderMem hm; simpa using load_full_watch_vec_ptr hmF

@[scoped c0_load] theorem load_re_arena_ptr {c : FullCfg} {s : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (ReorderMem c s wl wr ⋆ R) m) :
    loadVal m i64 (c.hdr + 112) = some c.pArena := by
  obtain ⟨_, _, _, _, hmF⟩ := fullMem_of_reorderMem hm; simpa using load_full_arena_ptr hmF

@[scoped c0_load] theorem load_re_watch_stk_ptr {c : FullCfg} {s : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (ReorderMem c s wl wr ⋆ R) m) :
    loadVal m i64 (c.hdr + 120) = some c.pWstk := by
  obtain ⟨_, _, _, _, hmF⟩ := fullMem_of_reorderMem hm; simpa using load_full_watch_stk_ptr hmF

@[scoped c0_load] theorem load_re_q_prev_ptr {c : FullCfg} {s : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (ReorderMem c s wl wr ⋆ R) m) :
    loadVal m i64 (c.hdr + 368) = some c.pQPrev := by
  obtain ⟨_, _, _, _, hmF⟩ := fullMem_of_reorderMem hm; simpa using load_full_q_prev_ptr hmF

@[scoped c0_load] theorem load_re_q_next_ptr {c : FullCfg} {s : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (ReorderMem c s wl wr ⋆ R) m) :
    loadVal m i64 (c.hdr + 376) = some c.pQNext := by
  obtain ⟨_, _, _, _, hmF⟩ := fullMem_of_reorderMem hm; simpa using load_full_q_next_ptr hmF

@[scoped c0_load] theorem load_re_q_stamp_ptr {c : FullCfg} {s : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (ReorderMem c s wl wr ⋆ R) m) :
    loadVal m i64 (c.hdr + 384) = some c.pQStamp := by
  obtain ⟨_, _, _, _, hmF⟩ := fullMem_of_reorderMem hm; simpa using load_full_q_stamp_ptr hmF

@[scoped c0_load] theorem load_re_wsort_ptr {c : FullCfg} {s : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (ReorderMem c s wl wr ⋆ R) m) :
    loadVal m i64 (c.hdr + 408) = some c.pWsort := by
  obtain ⟨_, _, _, _, hmF⟩ := fullMem_of_reorderMem hm; simpa using load_full_wsort_ptr hmF

@[scoped c0_load] theorem load_re_cur_vars {c : FullCfg} {s : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (ReorderMem c s wl wr ⋆ R) m) :
    loadVal m i64 (c.hdr + 776) = some (BitVec.ofNat 64 s.core.cur_vars) := by
  obtain ⟨_, _, _, _, hmF⟩ := fullMem_of_reorderMem hm; simpa using load_full_cur_vars hmF

@[scoped c0_load] theorem load_re_flags_ptr {c : FullCfg} {s : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (ReorderMem c s wl wr ⋆ R) m) :
    loadVal m i64 (c.hdr + 800) = some c.pFlags := by
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

private theorem hdrTailWords_set_wsort (c : FullCfg) (s : FullState) (ws : List (BitVec 32)) :
    Full.hdrTailWords c { s with scratch := { s.scratch with wsort := ws } } =
      Full.hdrTailWords c s := rfl

private theorem fullScrByteArrs_set_wsort (c : FullCfg) (s : FullState) (ws : List (BitVec 32)) :
    FullScrByteArrs c { s.scratch with wsort := ws } = FullScrByteArrs c s.scratch := rfl

private theorem fullScrU32A_set_wsort (c : FullCfg) (s : FullState) (ws : List (BitVec 32)) :
    FullScrU32A c { s.scratch with wsort := ws } = FullScrU32A c s.scratch := rfl

private theorem fullScrMetaArrs_set_wsort (c : FullCfg) (s : FullState) (ws : List (BitVec 32)) :
    FullScrMetaArrs c { s.scratch with wsort := ws } = FullScrMetaArrs c s.scratch := rfl

private theorem fullScrDynArrs_set_wsort (c : FullCfg) (s : FullState) (ws : List (BitVec 32)) :
    FullScrDynArrs c { s.scratch with wsort := ws } = FullScrDynArrs c s.scratch := rfl

@[scoped c0_store] theorem store_re_wsort {c : FullCfg} {s : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : Nat} (v : BitVec 32)
    (hi : i < s.scratch.wsort.length) (hm : (ReorderMem c s wl wr ⋆ R) m) :
    storeOk m i32 (c.pWsort + BitVec.ofNat 64 (4 * i)) ∧
      (ReorderMem c { s with scratch := { s.scratch with wsort := s.scratch.wsort.set i v } }
        wl wr ⋆ R) (storeMem m i32 (c.pWsort + BitVec.ofNat 64 (4 * i)) v) := by
  unfold ReorderMem at hm ⊢
  rw [hdrTailWords_set_wsort, fullScrByteArrs_set_wsort, fullScrU32A_set_wsort,
    fullScrMetaArrs_set_wsort, fullScrDynArrs_set_wsort]
  dsimp only
  have hm' : (array (t := i32) c.pWsort s.scratch.wsort ⋆
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
      array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆ FullCoreArrays c s.core ⋆
      FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆
      array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆
      array (t := i32) c.pWorkStk2 s.scratch.work_stk2 ⋆
      array64 c.pTarjanMark wl.1 ⋆ array64 c.pTarjanReach wr.1 ⋆
      FullScrMetaArrs c s.scratch ⋆ FullScrDynArrs c s.scratch ⋆ c.pad ⋆ R)) m := by ecancel
  obtain ⟨h1, h2⟩ := store_array (t := i32) v (by decide) hi hm'
  have h2' : (array (t := i32) c.pWsort (s.scratch.wsort.set i v) ⋆
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
      array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆ FullCoreArrays c s.core ⋆
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
  rw [bv64_mul4_eq]; exact store_re_wsort v hi hm

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
  have hi' : i < wl.1.length := by rw [wl.2]; exact hi
  exact loadVal_array64 (R := _) hi' (by ecancel)

@[scoped c0_load] theorem c0_load_re_wl {c : FullCfg} {s : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hi : i.toNat < c.max_vars) (hm : (ReorderMem c s wl wr ⋆ R) m) :
    loadVal m i64 (c.pTarjanMark + i * 8) =
      some (wl.1[i.toNat]'(by rw [wl.2]; exact hi)) := by
  rw [bv64_mul8_eq]; exact load_re_wl hi hm

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
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
      array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆ FullCoreArrays c s.core ⋆
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
  rw [bv64_mul8_eq]; exact store_re_wl v hi hm

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
  have hi' : i < wr.1.length := by rw [wr.2]; exact hi
  exact loadVal_array64 (R := _) hi' (by ecancel)

@[scoped c0_load] theorem c0_load_re_wr {c : FullCfg} {s : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hi : i.toNat < c.max_vars) (hm : (ReorderMem c s wl wr ⋆ R) m) :
    loadVal m i64 (c.pTarjanReach + i * 8) =
      some (wr.1[i.toNat]'(by rw [wr.2]; exact hi)) := by
  rw [bv64_mul8_eq]; exact load_re_wr hi hm

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
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
      array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆ FullCoreArrays c s.core ⋆
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
  rw [bv64_mul8_eq]; exact store_re_wr v hi hm

@[scoped c0_store] theorem store_re_wr0 {c : FullCfg} {s : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 64)
    (hi : 0 < c.max_vars) (hm : (ReorderMem c s wl wr ⋆ R) m) :
    storeOk m i64 c.pTarjanReach ∧
      (ReorderMem c s wl ⟨wr.1.set 0 v, by simp [wr.2]⟩ ⋆ R)
        (storeMem m i64 c.pTarjanReach v) := by
  simpa using store_re_wr v hi hm

end ReorderTactics

/-! ## 2. Specifications & Helper Function Proofs -/

/-- Contract for `full_reorder_weight_m7(sz)`: returns quantized weight `≤ 2^40` cleanly. -/
def m7ReorderWeightSpec : Spec [i64] [i64] := fun (_sz, ()) m Q _ =>
  ∀ w : BitVec 64, w.toNat ≤ 2 ^ 40 → Q (w, ()) m

/-- Contract for `full_reorder_sift_m7(h, start, n)`: preserves `ReorderMem` and
`WsortBounded · n cur_vars` without touching indices `≥ n`. -/
def m7ReorderSiftSpec : Spec [i64, i64, i64] [] :=
  fun (h, _start, n, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (wl wr : Arr64 c.max_vars) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧
      WsortBounded s.scratch.wsort n.toNat s.core.cur_vars ∧
      (ReorderMem c s wl wr ⋆ R) m ∧
      ∀ (ws' : List (BitVec 32)) (m' : Mem 64),
        ws'.length = s.scratch.wsort.length →
        WsortBounded ws' n.toNat s.core.cur_vars →
        (∀ j, n.toNat ≤ j → ws'[j]? = s.scratch.wsort[j]?) →
        let s' := { s with scratch := { s.scratch with wsort := ws' } }
        (ReorderMem c s' wl wr ⋆ R) m' → Q () m'

private theorem wsortBounded_mono {ws : List (BitVec 32)} {n1 n2 cv : Nat}
    (hle : n1 ≤ n2) (h : WsortBounded ws n2 cv) : WsortBounded ws n1 cv :=
  fun i hi => h i (by omega)

private theorem wsortBounded_set {ws : List (BitVec 32)} {n cv idx : Nat}
    (v : BitVec 32) (h : WsortBounded ws n cv) (hv : v.toNat < cv) :
    WsortBounded (ws.set idx v) n cv := by
  intro i hi
  by_cases he : i = idx
  · subst he
    by_cases hl : i < ws.length
    · rw [List.getElem?_set_self hl, Option.getD_some]; exact hv
    · rw [List.getElem?_eq_none (by simp; omega), Option.getD_none]; exact Nat.zero_lt_of_lt hv
  · rw [List.getElem?_set_ne (Ne.symm he)]; exact h i hi

private theorem wsortBounded_push {ws : List (BitVec 32)} {n cv : Nat} {v : BitVec 32}
    (h : WsortBounded ws n cv) (hn : n < ws.length) (hv : v.toNat < cv) :
    WsortBounded (ws.set n v) (n + 1) cv := by
  intro i hi
  by_cases he : i = n
  · subst he; rw [List.getElem?_set_self hn, Option.getD_some]; exact hv
  · rw [List.getElem?_set_ne (Ne.symm he)]; exact h i (by omega)

private theorem wsortBounded_get {ws : List (BitVec 32)} {n cv i : Nat}
    (h : WsortBounded ws n cv) (hi : i < n) (hl : i < ws.length) :
    (ws[i]'hl).toNat < cv := by
  have h1 := h i hi
  rw [List.getElem?_eq_getElem hl, Option.getD_some] at h1
  exact h1

theorem full_reorder_weight_m7_wp (Γ : Env) :
    ∀ a m Q X, m7ReorderWeightSpec a m Q X → Func.wp Γ full_reorder_weight_m7_body a m Q X := by
  rintro ⟨sz, ⟨⟩⟩ m Q X hQ
  unfold Func.wp full_reorder_weight_m7_body
  c0_hsplit
  · c0_hsteps; exact hQ 0#64 (by decide)
  · c0_hsplit
    · c0_hsteps; exact hQ 0#64 (by decide)
    · c0_hsteps
      apply hQ
      simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      exact Nat.div_le_self _ _

section ReorderSiftProof

open scoped ReorderTactics

private def SiftWsortEq (s s1 : FullState) : Prop :=
  s1 = { s with scratch := { s.scratch with wsort := s1.scratch.wsort } }

private theorem siftWsortEq_refl (s : FullState) : SiftWsortEq s s := by
  rcases s with ⟨_, ⟨_⟩⟩; rfl

private theorem siftWsortEq_qstamp {s s1 : FullState} (h : SiftWsortEq s s1) :
    s1.scratch.q_stamp = s.scratch.q_stamp := by
  unfold SiftWsortEq at h; rw [h]

private theorem siftWsortEq_curVars {s s1 : FullState} (h : SiftWsortEq s s1) :
    s1.core.cur_vars = s.core.cur_vars := by
  unfold SiftWsortEq at h; rw [h]

private theorem siftWsortEq_flags {s s1 : FullState} (h : SiftWsortEq s s1) :
    s1.core.flags.length = s.core.flags.length := by
  unfold SiftWsortEq at h; rw [h]

private theorem siftWsortEq_set {s s1 : FullState} (h : SiftWsortEq s s1)
    (ws : List (BitVec 32)) :
    SiftWsortEq s { s1 with scratch := { s1.scratch with wsort := ws } } := by
  unfold SiftWsortEq at h ⊢; rw [h]

private theorem siftWsortEq_elim {s s1 : FullState} (h : SiftWsortEq s s1) :
    s1 = { s with scratch := { s.scratch with wsort := s1.scratch.wsort } } := h

private theorem zext64_32_lt_of_lt {x : BitVec 32} {n : Nat} (h : x.toNat < n) :
    (BitVec.setWidth 64 x).toNat < n := by
  have hz : (BitVec.setWidth 64 x).toNat = x.toNat := by bv_omega
  omega

private theorem child_nat_of_hc {root n : BitVec 64} (hroot : root.toNat < 2 ^ 29)
    (h : ¬n.toNat ≤ ((root <<< (1 : Nat)).toNat + (1 : BitVec 64).toNat) % 2 ^ 64) :
    ((root <<< 1) + 1#64).toNat < n.toNat := by
  have hsh : ((root <<< (1 : Nat)).toNat + (1 : BitVec 64).toNat) % 2 ^ 64 =
      2 * root.toNat + 1 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one]; bv_omega
  have h2 : ((root <<< 1) + 1#64).toNat = 2 * root.toNat + 1 := by bv_omega
  omega

private theorem bv64_lt_of_not_le {a b : BitVec 64} (h : ¬(b ≤ a)) : a.toNat < b.toNat := by
  bv_omega

private theorem right_nat_of_hc {root n : BitVec 64} (hroot : root.toNat < 2 ^ 29)
    (h : ¬n.toNat ≤
      ((root <<< OfNat.ofNat 1 + (1 : BitVec 64)).toNat + (1 : BitVec 64).toNat) % 2 ^ 64) :
    ((root <<< 1) + 1#64 + 1#64).toNat < n.toNat := by
  have hsh :
      ((root <<< OfNat.ofNat 1 + (1 : BitVec 64)).toNat + (1 : BitVec 64).toNat) % 2 ^ 64 =
        2 * root.toNat + 2 := by
    rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one]
    have : (1 : BitVec 64).toNat = 1 := rfl
    omega
  have h2 : ((root <<< 1) + 1#64 + 1#64).toNat = 2 * root.toNat + 2 := by bv_omega
  omega

private theorem wsortBounded_swap {ws : List (BitVec 32)} {n cv i j : Nat}
    {vi vj : BitVec 32} (hwb : WsortBounded ws n cv)
    (hvi : vi.toNat < cv) (hvj : vj.toNat < cv) :
    WsortBounded ((ws.set i vi).set j vj) n cv :=
  wsortBounded_set _ (wsortBounded_set _ hwb hvi) hvj

theorem full_reorder_sift_m7_wp (Γ : Env) :
    ∀ a m Q X, m7ReorderSiftSpec a m Q X → Func.wp Γ full_reorder_sift_m7_body a m Q X := by
  rintro ⟨h, start, n, ⟨⟩⟩ m Q X ⟨c, s, wl, wr, R, rfl, hlen, hwb, hm, hQ⟩
  have hQ' : ∀ (s1 : FullState) (m1 : Mem 64),
      SiftWsortEq s s1 → s1.scratch.wsort.length = s.scratch.wsort.length →
      WsortBounded s1.scratch.wsort n.toNat s.core.cur_vars →
      (∀ j, n.toNat ≤ j → s1.scratch.wsort[j]? = s.scratch.wsort[j]?) →
      (ReorderMem c s1 wl wr ⋆ R) m1 → Q () m1 :=
    fun s1 m1 hs1_eq hlen1 hwb1 hpres1 hm1 =>
      hQ s1.scratch.wsort m1 hlen1 hwb1 hpres1 (siftWsortEq_elim hs1_eq ▸ hm1)
  clear hQ
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hlen.core_ok.cur_vars_le
  have hcv_29 : s.core.cur_vars < 2 ^ 29 := by omega
  have hws_len := hlen.scratch_ok.wsort_len
  have hqs_len := hlen.scratch_ok.q_stamp_len
  unfold Func.wp full_reorder_sift_m7_body
  c0_hsplit
  · c0_hsteps; exact hQ' s m (siftWsortEq_refl s) rfl hwb (fun _ _ => rfl) hm
  · c0_hsplit
    · c0_hsteps; exact hQ' s m (siftWsortEq_refl s) rfl hwb (fun _ _ => rfl) hm
    · c0_hsplit
      · c0_hsteps; exact hQ' s m (siftWsortEq_refl s) rfl hwb (fun _ _ => rfl) hm
      · have hn_pos : 1 ≤ n.toNat := by bv_omega
        have hst_lt : start.toNat < n.toNat := by bv_omega
        have hn_le : n.toNat ≤ s.core.cur_vars := by omega
        c0_hsteps_nogrp
        refine wp_while_break_state (fun root : BitVec 64 => (root, ()))
          (fun _ m1 =>
            ∃ s1 : FullState,
              SiftWsortEq s s1 ∧
              s1.scratch.wsort.length = s.scratch.wsort.length ∧
              WsortBounded s1.scratch.wsort n.toNat s.core.cur_vars ∧
              (∀ j, n.toNat ≤ j → s1.scratch.wsort[j]? = s.scratch.wsort[j]?) ∧
              (ReorderMem c s1 wl wr ⋆ R) m1)
          (fun root : BitVec 64 => (root, ()))
          (fun root => n.toNat - root.toNat)
          (fun root m1 =>
            root.toNat < n.toNat ∧
            ∃ s1 : FullState,
              SiftWsortEq s s1 ∧
              s1.scratch.wsort.length = s.scratch.wsort.length ∧
              WsortBounded s1.scratch.wsort n.toNat s.core.cur_vars ∧
              (∀ j, n.toNat ≤ j → s1.scratch.wsort[j]? = s.scratch.wsort[j]?) ∧
              (ReorderMem c s1 wl wr ⋆ R) m1)
          (fun B _ m1 ⟨s1, hs1_eq, hws1_len, hwb1, hpres1, hm1⟩ => by
            c0_hsteps; exact hQ' s1 m1 hs1_eq hws1_len hwb1 hpres1 hm1)
          (fun B L root m1 hB hL ⟨hroot, s1, hs1_eq, hws1_len, hwb1, hpres1, hm1⟩ => ?_)
          (fun B L _ hL => by
            c0_hsteps
            exact hL start m ⟨hst_lt, s, siftWsortEq_refl s, rfl, hwb, fun _ _ => rfl, hm⟩)
        have hqs1_len : s1.scratch.q_stamp.length = c.max_vars := by
          rw [siftWsortEq_qstamp hs1_eq]; exact hqs_len
        have hchild_eq : ((root <<< 1) + 1#64).toNat = 2 * root.toNat + 1 := by bv_omega
        have hroot_lt_ws : root.toNat < s1.scratch.wsort.length := by omega
        have hbv0_lt : (s1.scratch.wsort[root.toNat]'hroot_lt_ws).toNat < s.core.cur_vars :=
          wsortBounded_get hwb1 hroot hroot_lt_ws
        have hbv0_mv :
            (BitVec.setWidth 64 (s1.scratch.wsort[root.toNat]'hroot_lt_ws)).toNat <
              c.max_vars := zext64_32_lt_of_lt (Nat.lt_of_lt_of_le hbv0_lt hcv_le)
        have hbv0_qs :
            (BitVec.setWidth 64 (s1.scratch.wsort[root.toNat]'hroot_lt_ws)).toNat <
              s1.scratch.q_stamp.length := hqs1_len ▸ hbv0_mv
        c0_hsplit
        · c0_hsplit
          · c0_hsteps; exact hB root m1 ⟨s1, hs1_eq, hws1_len, hwb1, hpres1, hm1⟩
          · have hch_nat : ((root <<< 1) + 1#64).toNat < n.toNat :=
              child_nat_of_hc (by omega) ‹_›
            have hch_lt : 2 * root.toNat + 1 < n.toNat := hchild_eq ▸ hch_nat
            have hch_lt_ws : ((root <<< 1) + 1#64).toNat < s1.scratch.wsort.length := by omega
            have hcv0_lt :
                (s1.scratch.wsort[((root <<< 1) + 1#64).toNat]'hch_lt_ws).toNat <
                  s.core.cur_vars := wsortBounded_get hwb1 hch_nat hch_lt_ws
            have hcv0_mv :
                (BitVec.setWidth 64
                  (s1.scratch.wsort[((root <<< 1) + 1#64).toNat]'hch_lt_ws)).toNat <
                  c.max_vars := zext64_32_lt_of_lt (Nat.lt_of_lt_of_le hcv0_lt hcv_le)
            have hcv0_qs :
                (BitVec.setWidth 64
                  (s1.scratch.wsort[((root <<< 1) + 1#64).toNat]'hch_lt_ws)).toNat <
                  s1.scratch.q_stamp.length := hqs1_len ▸ hcv0_mv
            have hrch_eq :
                ((root <<< 1) + 1#64 + 1#64).toNat = 2 * root.toNat + 2 := by bv_omega
            c0_hsteps_nogrp
            refine wp_join_group (ts := [i64, i32, i64, i32])
              (fun xs m' =>
                m' = m1 ∧ (xs.1 = root ∨ xs.1 = (root <<< 1) + 1#64) ∧
                xs.1.toNat < n.toNat ∧ xs.2.1.toNat < s.core.cur_vars)
              ?_ ?_
            · rintro J xs m' ⟨hm_eq, hx_eq, hx_lt, hxv_lt⟩
              subst m'
              dsimp only [Blocks.get]
              c0_hsteps_nogrp
              refine wp_join_group (ts := [i64, i32])
                (fun ys m'' =>
                  m'' = m1 ∧
                  (ys.1 = root ∨ ys.1 = (root <<< 1) + 1#64 ∨ ys.1 = (root <<< 1) + 1#64 + 1#64) ∧
                  ys.1.toNat < n.toNat ∧ ys.2.1.toNat < s.core.cur_vars)
                ?_ ?_
              · rintro J2 ys m'' ⟨hm_eq', hy_eq, hy_lt, hyv_lt⟩
                subst m''
                c0_hsplit
                · c0_hsteps; exact hB _ m1 ⟨s1, hs1_eq, hws1_len, hwb1, hpres1, hm1⟩
                · have hgt : root.toNat < ys.1.toNat := by
                    rcases hy_eq with h1 | h1 | h1
                    · exact absurd h1 (by assumption)
                    · rw [h1, hchild_eq]; omega
                    · rw [h1, hrch_eq]; omega
                  have hys_ws : ys.1.toNat < s1.scratch.wsort.length := by omega
                  have hys_ws' :
                      ys.1.toNat < (s1.scratch.wsort.set root.toNat ys.2.1).length := by
                    simpa using hys_ws
                  c0_hsteps
                  let ws2 := (s1.scratch.wsort.set root.toNat ys.2.1).set ys.1.toNat
                    (s1.scratch.wsort[root.toNat]'hroot_lt_ws)
                  exact hL ys.1 _ (by omega)
                    ⟨hy_lt, { s1 with scratch := { s1.scratch with wsort := ws2 } },
                     siftWsortEq_set hs1_eq _, by simp [ws2, hws1_len],
                     wsortBounded_swap hwb1 hyv_lt hbv0_lt,
                     fun j hj => by
                       dsimp only [ws2]
                       rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
                       exact hpres1 j hj,
                     by assumption⟩
              · intro J2 hJ2
                c0_hsplit
                · have hrch_nat : ((root <<< 1) + 1#64 + 1#64).toNat < n.toNat := by
                    clear hB hL hQ' hwb1 hpres1 hm1 hbv0_lt hbv0_mv hbv0_qs
                    clear hcv0_lt hcv0_mv hcv0_qs hx_eq hx_lt hxv_lt
                    have hone : (1 : BitVec 64).toNat = 1 := rfl
                    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
                      hone, Nat.shiftLeft_eq, Nat.pow_one, Nat.reducePow, Nat.reduceMod] at *
                    omega
                  have hrch_n : 2 * root.toNat + 2 < n.toNat := hrch_eq ▸ hrch_nat
                  have hrch_ws :
                      ((root <<< 1) + 1#64 + 1#64).toNat < s1.scratch.wsort.length := by omega
                  have hrv_lt :
                      (s1.scratch.wsort[((root <<< 1) + 1#64 + 1#64).toNat]'hrch_ws).toNat <
                        s.core.cur_vars := wsortBounded_get hwb1 hrch_nat hrch_ws
                  have hrv_mv :
                      (BitVec.setWidth 64
                        (s1.scratch.wsort[((root <<< 1) + 1#64 + 1#64).toNat]'hrch_ws)).toNat <
                        c.max_vars := zext64_32_lt_of_lt (Nat.lt_of_lt_of_le hrv_lt hcv_le)
                  have hrv_qs :
                      (BitVec.setWidth 64
                        (s1.scratch.wsort[((root <<< 1) + 1#64 + 1#64).toNat]'hrch_ws)).toNat <
                        s1.scratch.q_stamp.length := hqs1_len ▸ hrv_mv
                  c0_hsteps_nogrp
                  refine wp_join_group (ts := [i64, i32])
                    (fun zs m'' =>
                      m'' = m1 ∧
                      (zs.1 = root ∨ zs.1 = (root <<< 1) + 1#64 ∨
                        zs.1 = (root <<< 1) + 1#64 + 1#64) ∧
                      zs.1.toNat < n.toNat ∧ zs.2.1.toNat < s.core.cur_vars)
                    (fun J3 _ m'' ⟨hm_z, hz⟩ => by
                      subst m''; dsimp only [Blocks.get]; c0_hsteps; exact hJ2 _ m1 ⟨rfl, hz⟩)
                    (fun J3 hJ3 => by
                      c0_hsteps_nogrp
                      all_goals
                        refine hJ3 _ m1 ⟨rfl, ?_, ?_, ?_⟩
                        · first | exact Or.inr (Or.inr rfl) | exact hx_eq.imp_right Or.inl
                        · first | exact hrch_nat | exact hx_lt
                        · first | exact hrv_lt | exact hxv_lt)
                · c0_hsteps
                  exact hJ2 _ m1 ⟨rfl, hx_eq.imp_right Or.inl, hx_lt, hxv_lt⟩
            · intro J1 hJ1
              c0_hsteps_nogrp
              all_goals
                refine hJ1 _ m1 ⟨rfl, ?_, ?_, ?_⟩
                · first | exact Or.inl rfl | exact Or.inr rfl
                · first | exact hroot | exact hch_nat
                · first | exact hbv0_lt | exact hcv0_lt
        · exact absurd ‹true = false› (by decide)

end ReorderSiftProof

/-! ## 3. `full_reorder_queue_m7` (`FullM4Ternary.fullReorderQueueSpec`) -/

section ReorderQueueProof

open scoped ReorderTactics FullArenaTactics

private theorem ushr1_nat_lt {x : BitVec 64} {n : Nat} (h : x.toNat < 2 * n) :
    (x >>> (1 : Nat)).toNat < n := by
  have : (x >>> (1 : Nat)).toNat = x.toNat / 2 := by
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega

private theorem ushr1_bv_lt {x : BitVec 64} {n : Nat} (h : x.toNat < 2 * n) :
    (x >>> (1 : BitVec 64)).toNat < n := by
  change (x >>> (1 : Nat)).toNat < n; exact ushr1_nat_lt h

private theorem zext32_ushr1_lt {x : BitVec 32} {n : Nat}
    (h : (BitVec.setWidth 64 x).toNat < 2 * n) :
    ((BitVec.setWidth 64 x) >>> (1 : BitVec 64)).toNat < n :=
  ushr1_bv_lt h

private theorem zext32_ushr1_nat_lt {x : BitVec 32} {n : Nat}
    (h : (BitVec.setWidth 64 x).toNat < 2 * n) :
    ((BitVec.setWidth 64 x) >>> (1 : Nat)).toNat < n :=
  ushr1_nat_lt h

private theorem shl1_nat_lt {x : BitVec 64} {n : Nat} (h : x.toNat < 2 * n) (hn : n < 2 ^ 29) :
    (x <<< (1 : Nat)).toNat < 4 * n := by
  have h1 : (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
    simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  omega

private theorem shl1_bv_lt {x : BitVec 64} {n : Nat} (h : x.toNat < 2 * n) (hn : n < 2 ^ 29) :
    (x <<< (1 : BitVec 64)).toNat < 4 * n := by
  change (x <<< (1 : Nat)).toNat < 4 * n; exact shl1_nat_lt h hn

private theorem shl1_add1_nat_lt {x : BitVec 64} {n : Nat} (h : x.toNat < 2 * n) (hn : n < 2 ^ 29) :
    ((x <<< (1 : Nat)) + 1#64).toNat < 4 * n := by
  have h1 : (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
    simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have h2 : ((x <<< (1 : Nat)) + 1#64).toNat = 2 * x.toNat + 1 := by
    rw [BitVec.toNat_add, h1]
    have hlt : 2 * x.toNat + 1 < 2 ^ 64 := by omega
    rw [show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt hlt]
  omega

private theorem shl1_add1_bv_lt {x : BitVec 64} {n : Nat} (h : x.toNat < 2 * n) (hn : n < 2 ^ 29) :
    ((x <<< (1 : BitVec 64)) + 1#64).toNat < 4 * n := by
  change ((x <<< (1 : Nat)) + 1#64).toNat < 4 * n; exact shl1_add1_nat_lt h hn

private theorem shl1_mul2_nat_lt {x : BitVec 64} {m : Nat}
    (h : x.toNat < m) (hm : m < 2 * 2 ^ 28) : (x <<< (1 : Nat)).toNat < 2 * m := by
  have h2lt : x.toNat * 2 < 2 ^ 30 := by omega
  have h64 : x.toNat * 2 < 2 ^ 64 := lt_trans h2lt (by decide)
  have h1 : (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
    simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one, Nat.mod_eq_of_lt h64]
    omega
  omega

private theorem shl1_mul2_bv_lt {x : BitVec 64} {m : Nat}
    (h : x.toNat < m) (hm : m < 2 * 2 ^ 28) : (x <<< (1 : BitVec 64)).toNat < 2 * m := by
  change (x <<< (1 : Nat)).toNat < 2 * m; exact shl1_mul2_nat_lt h hm

private theorem zext32_bv32_ushr1_lt {x : BitVec 32} {n : Nat}
    (h : (BitVec.setWidth 64 x).toNat < 2 * n) :
    (BitVec.setWidth 64 (x >>> (1 : Nat))).toNat < n := by
  have hz1 : (BitVec.setWidth 64 x).toNat = x.toNat := by bv_omega
  have hz2 : (BitVec.setWidth 64 (x >>> (1 : Nat))).toNat = (x >>> (1 : Nat)).toNat := by bv_omega
  have hdiv : (x >>> (1 : Nat)).toNat = x.toNat / 2 := by
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega

private theorem zext32_bv32_ushr1_bv_lt {x : BitVec 32} {n : Nat}
    (h : (BitVec.setWidth 64 x).toNat < 2 * n) :
    (BitVec.setWidth 64 (x >>> (1 : BitVec 32))).toNat < n := by
  change (BitVec.setWidth 64 (x >>> (1 : Nat))).toNat < n
  exact zext32_bv32_ushr1_lt h

private theorem bv64_lt_of_mod_lt {v : BitVec 64} {m : Nat} (hm : m < 2 ^ 30)
    (h : v.toNat < m % 2 ^ 64) : v.toNat < m := by
  rw [Nat.mod_eq_of_lt (lt_trans hm (by decide))] at h
  exact h

private theorem bv64_lt_two_mul_mod {x : BitVec 64} {m : Nat} (hm : m < 2 ^ 29)
    (h : x.toNat < 2 * (m % 2 ^ 64) % 2 ^ 64) : x.toNat < 2 * m := by
  have hm64 : m < 2 ^ 64 := lt_trans hm (by decide)
  have h2m64 : 2 * m < 2 ^ 64 := lt_trans (Nat.mul_lt_mul_of_pos_left hm (by decide)) (by decide)
  rw [Nat.mod_eq_of_lt hm64, Nat.mod_eq_of_lt h2m64] at h
  exact h

private theorem bv64_off3_add_toNat {off j : BitVec 64} (ho : off.toNat < 2 ^ 29)
    (hj : j.toNat < 2 ^ 29) :
    ((off + 3#64) + j).toNat = off.toNat + 3 + j.toNat ∧
    (off.toNat + 3 % 2 ^ 64 + j.toNat) % 2 ^ 64 = off.toNat + 3 + j.toNat ∧
    ((off.toNat + 3 % 2 ^ 64) % 2 ^ 64 + j.toNat) % 2 ^ 64 = off.toNat + 3 + j.toNat := by
  have ho30 : off.toNat + 3 < 2 ^ 30 := by omega
  have hoj31 : off.toNat + 3 + j.toNat < 2 ^ 31 := by omega
  have ho64 : off.toNat + 3 < 2 ^ 64 := lt_trans ho30 (by decide)
  have hoj64 : off.toNat + 3 + j.toNat < 2 ^ 64 := lt_trans hoj31 (by decide)
  have h1 : ((off + 3#64) + j).toNat = off.toNat + 3 + j.toNat := by bv_omega
  have hm3 : (3 : Nat) % 2 ^ 64 = 3 := by decide
  rw [hm3, Nat.mod_eq_of_lt ho64, Nat.mod_eq_of_lt hoj64]
  exact ⟨h1, rfl, rfl⟩

private theorem m7_arena_lit_2cv {arena : List (BitVec 32)} {i j cv : Nat}
    (hij : i = j) (hcv : cv < 2 ^ 29) (hi : i < arena.length) (hj : j < arena.length)
    (hc : (arena[j]'hj).toNat < 2 * (cv % 2 ^ 64) % 2 ^ 64) :
    (BitVec.setWidth 64 (arena[i]'hi)).toNat < 2 * cv := by
  subst hij
  have h32 : (arena[i]'hi).toNat < 2 ^ 64 := lt_trans (BitVec.isLt _) (by decide)
  have hz : (BitVec.setWidth 64 (arena[i]'hi)).toNat = (arena[i]'hi).toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt h32]
  exact hz ▸ bv64_lt_two_mul_mod hcv (x := BitVec.setWidth 64 (arena[i]'hi)) (hz ▸ hc)

private theorem m7_off_bounds {arena_len arena_arr_len : Nat} {off n3 : BitVec 64}
    (har29 : arena_len < 2 ^ 29) (har_le : arena_len ≤ arena_arr_len)
    (h1 : off.toNat < arena_len % 2 ^ 64)
    (h2 : ¬arena_len % 2 ^ 64 < (off.toNat + n3.toNat) % 2 ^ 64) (hn3 : n3.toNat = 3) :
    off.toNat + 3 ≤ arena_len ∧ off.toNat < 2 ^ 29 ∧
    (off + 2#64).toNat = off.toNat + 2 ∧
    off.toNat < arena_arr_len ∧ (off + 2#64).toNat < arena_arr_len := by
  have har64 : arena_len < 2 ^ 64 := lt_trans har29 (by decide)
  rw [Nat.mod_eq_of_lt har64] at h1 h2
  rw [hn3] at h2
  have ho29 : off.toNat < 2 ^ 29 := Nat.lt_trans h1 har29
  have ho3_30 : off.toNat + 3 < 2 ^ 30 := by omega
  have ho3_64 : off.toNat + 3 < 2 ^ 64 := lt_trans ho3_30 (by decide)
  rw [Nat.mod_eq_of_lt ho3_64] at h2
  have hoff3 : off.toNat + 3 ≤ arena_len := Nat.le_of_not_lt h2
  have ho2_30 : off.toNat + 2 < 2 ^ 30 := by omega
  have ho2_64 : off.toNat + 2 < 2 ^ 64 := lt_trans ho2_30 (by decide)
  have ho2 : (off + 2#64).toNat = off.toNat + 2 := by
    rw [BitVec.toNat_add, show (2#64 : BitVec 64).toNat = 2 from rfl, Nat.mod_eq_of_lt ho2_64]
  exact ⟨hoff3, ho29, ho2, Nat.lt_of_lt_of_le h1 har_le,
    ho2 ▸ Nat.lt_of_lt_of_le (by omega) (Nat.le_trans hoff3 har_le)⟩

private theorem m7_sz_off3_le {arena : List (BitVec 32)} {arena_len : Nat} {off n2 n3 : BitVec 64}
    (hoff3 : off.toNat + 3 ≤ arena_len) (har29 : arena_len < 2 ^ 29)
    {hi1 : (off.toNat + n2.toNat) % 2 ^ 64 < arena.length}
    (hi2 : (off + 2#64).toNat < arena.length) (ho2 : (off + 2#64).toNat = off.toNat + 2)
    (hle : (arena[(off.toNat + n2.toNat) % 2 ^ 64]'hi1).toNat ≤
      (2 ^ 64 - (off.toNat + n3.toNat) % 2 ^ 64 + arena_len) % 2 ^ 64)
    (hn2 : n2.toNat = 2) (hn3 : n3.toNat = 3) :
    off.toNat + 3 + (BitVec.setWidth 64 (arena[(off + 2#64).toNat]'hi2)).toNat ≤ arena_len ∧
    (BitVec.setWidth 64 (arena[(off + 2#64).toNat]'hi2)).toNat < 2 ^ 29 := by
  have ho2_30 : off.toNat + 2 < 2 ^ 30 := by omega
  have ho2_64 : off.toNat + 2 < 2 ^ 64 := lt_trans ho2_30 (by decide)
  have ho3_30 : off.toNat + 3 < 2 ^ 30 := by omega
  have ho3_64 : off.toNat + 3 < 2 ^ 64 := lt_trans ho3_30 (by decide)
  have hi_eq : (off.toNat + n2.toNat) % 2 ^ 64 = (off + 2#64).toNat := by
    rw [hn2, ho2, Nat.mod_eq_of_lt ho2_64]
  have helem : arena[(off.toNat + n2.toNat) % 2 ^ 64]'hi1 = arena[(off + 2#64).toNat]'hi2 := by
    clear hle; revert hi1; rw [hi_eq]; intro _; rfl
  have hsub1 : 2 ^ 64 - (off.toNat + 3) + arena_len = (arena_len - (off.toNat + 3)) + 2 ^ 64 := by
    omega
  have hrem29 : arena_len - (off.toNat + 3) < 2 ^ 29 := by omega
  have hrem : arena_len - (off.toNat + 3) < 2 ^ 64 := lt_trans hrem29 (by decide)
  have hrhs : (2 ^ 64 - (off.toNat + n3.toNat) % 2 ^ 64 + arena_len) % 2 ^ 64 =
      arena_len - (off.toNat + 3) := by
    rw [hn3, Nat.mod_eq_of_lt ho3_64, hsub1, Nat.add_mod_right, Nat.mod_eq_of_lt hrem]
  rw [helem, hrhs] at hle
  have h32 : (arena[(off + 2#64).toNat]'hi2).toNat < 2 ^ 64 := lt_trans (BitVec.isLt _) (by decide)
  have hz : (BitVec.setWidth 64 (arena[(off + 2#64).toNat]'hi2)).toNat =
      (arena[(off + 2#64).toNat]'hi2).toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt h32]
  rw [hz]; exact ⟨by omega, by omega⟩

private theorem m7_arena_k_lt {arena : List (BitVec 32)} {off k n2 : BitVec 64}
    (ho2 : (off + 2#64).toNat = off.toNat + 2) (hoff : off.toNat < 2 ^ 29)
    {hi1 : (off.toNat + n2.toNat) % 2 ^ 64 < arena.length}
    (hi2 : (off + 2#64).toNat < arena.length)
    (hc : k.toNat < (arena[(off.toNat + n2.toNat) % 2 ^ 64]'hi1).toNat) (hn2 : n2.toNat = 2) :
    k.toNat < (BitVec.setWidth 64 (arena[(off + 2#64).toNat]'hi2)).toNat := by
  have ho2_30 : off.toNat + 2 < 2 ^ 30 := by omega
  have ho2_64 : off.toNat + 2 < 2 ^ 64 := lt_trans ho2_30 (by decide)
  have heq : (off.toNat + n2.toNat) % 2 ^ 64 = (off + 2#64).toNat := by
    rw [hn2, ho2, Nat.mod_eq_of_lt ho2_64]
  have helem : arena[(off.toNat + n2.toNat) % 2 ^ 64]'hi1 = arena[(off + 2#64).toNat]'hi2 := by
    clear hc; revert hi1; rw [heq]; intro _; rfl
  have h32 : (arena[(off + 2#64).toNat]'hi2).toNat < 2 ^ 64 := lt_trans (BitVec.isLt _) (by decide)
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt h32, ← helem]
  exact hc

private theorem wp_call_spec {Γ : Env} {rs as bs : List Ty} {Q : Post rs} {X : XPost}
    {f : Sym} {args : Tup (Arg Val) as} {k : Tup Val bs → Expr Val Cont rs} {m : Mem 64}
    {spec : Spec as bs} (hEnv : EnvSpec Γ f spec)
    (hSpec : spec (vals args) m (fun r m' => wp Γ Q X (k r) m') X) :
    wp Γ Q X (.call f args k) m :=
  ⟨fun r m' => wp Γ Q X (k r) m', X, hEnv _ _ _ _ hSpec, fun _ _ h => h, fun _ _ _ _ h => h⟩

private theorem bv64_lt_shl1_ofNat {v : BitVec 64} {m : Nat} (hm : m < 2 ^ 29)
    (h : v.toNat < (BitVec.ofNat 64 m <<< (1 : Nat)).toNat) : v.toNat < 2 * m := by
  have hm64 : m < 2 ^ 64 := lt_trans hm (by decide)
  have h1 : (BitVec.ofNat 64 m <<< (1 : Nat)).toNat = 2 * m := by
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.pow_one]
    rw [Nat.mod_eq_of_lt hm64, Nat.mod_eq_of_lt (by omega)]
    omega
  omega

private theorem bv64_zext32_toNat_lt {v : BitVec 64} {m : Nat} (hm : m < 2 ^ 29)
    (hv : v.toNat < m) : (BitVec.setWidth 32 v).toNat < m := by
  have : v.toNat < 2 ^ 32 := lt_trans hv (lt_trans hm (by decide))
  have hz : (BitVec.setWidth 32 v).toNat = v.toNat := by bv_omega
  omega

private theorem bv64_add1_toNat {x : BitVec 64} {m : Nat} (hm : m < 2 ^ 30) (hx : x.toNat < m) :
    (x + 1#64).toNat = x.toNat + 1 ∧ (x + 1#64).toNat ≤ m ∧ m - (x + 1#64).toNat < m - x.toNat := by
  have : x.toNat < 2 ^ 64 - 1 := lt_trans hx (lt_trans hm (by decide))
  bv_omega

private theorem bv64_add1_sub_lt {x : BitVec 64} {m : Nat} (hm : m < 2 ^ 30) (hx : x.toNat < m) :
    m - (x + 1#64).toNat < m - x.toNat :=
  (bv64_add1_toNat hm hx).2.2

private theorem bv64_add2_sub_lt {x : BitVec 64} {m : Nat} (hm : m < 2 ^ 30) (hx : x.toNat < m) :
    m - (x + 2#64).toNat < m - x.toNat := by
  have : x.toNat < 2 ^ 64 - 2 := lt_trans hx (lt_trans hm (by decide))
  bv_omega

private theorem bv64_sub1_toNat {x : BitVec 64} {m : Nat} (hm : m < 2 ^ 30)
    (hx_le : x.toNat ≤ m) (hx_pos : 0 < x.toNat) :
    (x - 1#64).toNat = x.toNat - 1 ∧ (x - 1#64).toNat < x.toNat ∧
    (x - 1#64).toNat ≤ m ∧ (x - 1#64).toNat < m := by
  have : x.toNat < 2 ^ 64 := lt_of_le_of_lt hx_le (lt_trans hm (by decide))
  bv_omega

private theorem bv64_ushr1_le {x : BitVec 64} {m : Nat} (hx : x.toNat ≤ m) :
    (x >>> 1#64).toNat ≤ m := by
  have h1 : (x >>> 1#64).toNat = x.toNat / 2 := by
    change (x >>> (1 : Nat)).toNat = x.toNat / 2
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega

private theorem bv64_pos_of_ne_zero {x : BitVec 64} (h : x ≠ 0#64) : 0 < x.toNat := by
  bv_omega

private theorem siftWsortEq_lengthsOk {c : FullCfg} {s s1 : FullState}
    (hlen : s.LengthsOk c) (hs1 : SiftWsortEq s s1)
    (hwl : s1.scratch.wsort.length = s.scratch.wsort.length) : s1.LengthsOk c := by
  unfold SiftWsortEq at hs1
  rw [hs1]
  exact ⟨hlen.core_ok, { hlen.scratch_ok with wsort_len := hwl.trans hlen.scratch_ok.wsort_len }⟩

private theorem m7_we_le_wlen {ws wc : BitVec 32} {wlen : Nat}
    (hwl : wlen < 2 ^ 29) (hws : ws.toNat < wlen % 2 ^ 64)
    (hwc : wc.toNat ≤ (2 ^ 64 - ws.toNat + wlen) % 2 ^ 64) :
    ws.toNat ≤ wlen ∧
    ((BitVec.setWidth 64 ws) + (BitVec.setWidth 64 wc)).toNat ≤ wlen := by
  have hws' : ws.toNat < wlen := by
    rw [Nat.mod_eq_of_lt (lt_trans hwl (by decide))] at hws; exact hws
  have hsub : (2 ^ 64 - ws.toNat + wlen) % 2 ^ 64 = wlen - ws.toNat := by
    rw [show 2 ^ 64 - ws.toNat + wlen = (wlen - ws.toNat) + 2 ^ 64 by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  have hwc' : wc.toNat ≤ wlen - ws.toNat := hsub ▸ hwc
  have hz1 : (BitVec.setWidth 64 ws).toNat = ws.toNat := by bv_omega
  have hz2 : (BitVec.setWidth 64 wc).toNat = wc.toNat := by bv_omega
  have hadd : (BitVec.setWidth 64 ws + BitVec.setWidth 64 wc).toNat = ws.toNat + wc.toNat := by
    rw [BitVec.toNat_add, hz1, hz2, Nat.mod_eq_of_lt (by omega)]
  omega

private theorem wsortBounded_lift {ws ws' : List (BitVec 32)} {k n cv : Nat}
    (hwb : WsortBounded ws n cv) (hwb' : WsortBounded ws' k cv)
    (hpres : ∀ j, k ≤ j → ws'[j]? = ws[j]?) :
    WsortBounded ws' n cv := by
  intro j hj
  by_cases hjk : j < k
  · exact hwb' j hjk
  · rw [hpres j (Nat.le_of_not_lt hjk)]; exact hwb j hj

private theorem wsortBounded_shrink {ws : List (BitVec 32)} {k n cv : Nat}
    (hwb : WsortBounded ws n cv) (hk : k ≤ n) : WsortBounded ws k cv :=
  fun j hj => hwb j (Nat.lt_of_lt_of_le hj hk)

private def QueuePostOk (c : FullCfg) (s : FullState) (R : Mem 64 → Prop)
    (m' : Mem 64) : Prop :=
  ∃ s' : FullState,
    s'.core = s.core ∧ s'.LengthsOk c ∧ FullExtScratchPres s s' ∧ (FullMem c s' ⋆ R) m'

private def QueueRelinkOk (c : FullCfg) (s0 s1 : FullState) (n : Nat) : Prop :=
  s1.core = s0.core ∧ s1.LengthsOk c ∧ FullExtScratchPres s0 s1 ∧
  WsortBounded s1.scratch.wsort n s1.core.cur_vars

private theorem queueRelinkOk_of_reorder {c : FullCfg} {s0 s1 : FullState}
    {wl wr : Arr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {n : Nat}
    (hlen0 : s0.LengthsOk c) (hs1 : SiftWsortEq s0 s1)
    (hwl : s1.scratch.wsort.length = s0.scratch.wsort.length)
    (hwb : WsortBounded s1.scratch.wsort n s0.core.cur_vars)
    (hm : (ReorderMem c s1 wl wr ⋆ R) m) :
    ∃ s2 : FullState, QueueRelinkOk c s0 s2 n ∧ (FullMem c s2 ⋆ R) m := by
  obtain ⟨tmk, trc, htmk, htrc, hmF⟩ := fullMem_of_reorderMem hm
  have hs1' := siftWsortEq_elim hs1
  refine ⟨{ s1 with scratch := { s1.scratch with tarjan_mark := tmk, tarjan_reach := trc } },
    ⟨?_, ?_, ?_, ?_⟩, hmF⟩
  · rw [hs1']
  · constructor
    · rw [hs1']; exact hlen0.core_ok
    · exact {
        walk_vals_len := by rw [hs1']; exact hlen0.scratch_ok.walk_vals_len
        phases_len := by rw [hs1']; exact hlen0.scratch_ok.phases_len
        phases_target_len := by rw [hs1']; exact hlen0.scratch_ok.phases_target_len
        phases_best_len := by rw [hs1']; exact hlen0.scratch_ok.phases_best_len
        walk_best_len := by rw [hs1']; exact hlen0.scratch_ok.walk_best_len
        heap_len_arr := by rw [hs1']; exact hlen0.scratch_ok.heap_len_arr
        pos_len := by rw [hs1']; exact hlen0.scratch_ok.pos_len
        shrink_stk_len := by rw [hs1']; exact hlen0.scratch_ok.shrink_stk_len
        q_prev_len := by rw [hs1']; exact hlen0.scratch_ok.q_prev_len
        q_next_len := by rw [hs1']; exact hlen0.scratch_ok.q_next_len
        q_stamp_len := by rw [hs1']; exact hlen0.scratch_ok.q_stamp_len
        wsort_len := by simpa using hwl.trans hlen0.scratch_ok.wsort_len
        work_stk1_len := by rw [hs1']; exact hlen0.scratch_ok.work_stk1_len
        work_stk2_len := by rw [hs1']; exact hlen0.scratch_ok.work_stk2_len
        tarjan_mark_len := htmk
        tarjan_reach_len := htrc
        score_len := by rw [hs1']; exact hlen0.scratch_ok.score_len
        sim_sig_len := by rw [hs1']; exact hlen0.scratch_ok.sim_sig_len
        glue_used_len := by rw [hs1']; exact hlen0.scratch_ok.glue_used_len
        last_learned_len := by rw [hs1']; exact hlen0.scratch_ok.last_learned_len
        delayed_len_arr := by rw [hs1']; exact hlen0.scratch_ok.delayed_len_arr
        red_refs_len := by rw [hs1']; exact hlen0.scratch_ok.red_refs_len
        extend_stk_len := by rw [hs1']; exact hlen0.scratch_ok.extend_stk_len
        scratch_buf_len := by rw [hs1']; exact hlen0.scratch_ok.scratch_buf_len }
  · exact ⟨by rw [hs1'], by rw [hs1']⟩
  · rw [hs1']; exact hwb

private theorem queueRelinkOk_lengths {c : FullCfg} {s0 s1 : FullState} {n : Nat}
    (h : QueueRelinkOk c s0 s1 n) :
    s1.core.cur_vars = s0.core.cur_vars ∧
    s1.core.vals.length = 2 * c.max_vars ∧
    s1.scratch.wsort.length = 2 * c.max_vars ∧
    s1.scratch.q_prev.length = c.max_vars ∧
    s1.scratch.q_next.length = c.max_vars ∧
    s1.scratch.q_stamp.length = c.max_vars :=
  ⟨h.1 ▸ rfl, h.2.1.core_ok.vals_len, h.2.1.scratch_ok.wsort_len,
   h.2.1.scratch_ok.q_prev_len, h.2.1.scratch_ok.q_next_len, h.2.1.scratch_ok.q_stamp_len⟩

private theorem queueRelinkOk_wsort_get {c : FullCfg} {s0 s1 : FullState} {n : Nat}
    (h : QueueRelinkOk c s0 s1 n) {i : Nat} (hin : i < n) (hil : i < s1.scratch.wsort.length) :
    (s1.scratch.wsort[i]'hil).toNat < s0.core.cur_vars := by
  have := h.2.2.2 i hin
  rw [List.getElem?_eq_getElem hil, Option.getD_some, h.1] at this
  exact this

private theorem queueRelinkOk_to_post {c : FullCfg} {s0 s1 : FullState} {n : Nat}
    {R : Mem 64 → Prop} {m : Mem 64}
    (h : QueueRelinkOk c s0 s1 n) (hm : (FullMem c s1 ⋆ R) m) : QueuePostOk c s0 R m :=
  ⟨s1, h.1, h.2.1, h.2.2.1, hm⟩

private theorem queueRelinkOk_set_qprev {c : FullCfg} {s0 s1 : FullState} {n : Nat}
    (h : QueueRelinkOk c s0 s1 n) (i : Nat) (v : BitVec 32) :
    QueueRelinkOk c s0
      { s1 with scratch := { s1.scratch with q_prev := s1.scratch.q_prev.set i v } } n :=
  ⟨h.1, ⟨h.2.1.core_ok, { h.2.1.scratch_ok with
    q_prev_len := by simp [h.2.1.scratch_ok.q_prev_len] }⟩, h.2.2.1, h.2.2.2⟩

private theorem queueRelinkOk_set_qnext {c : FullCfg} {s0 s1 : FullState} {n : Nat}
    (h : QueueRelinkOk c s0 s1 n) (i : Nat) (v : BitVec 32) :
    QueueRelinkOk c s0
      { s1 with scratch := { s1.scratch with q_next := s1.scratch.q_next.set i v } } n :=
  ⟨h.1, ⟨h.2.1.core_ok, { h.2.1.scratch_ok with
    q_next_len := by simp [h.2.1.scratch_ok.q_next_len] }⟩, h.2.2.1, h.2.2.2⟩

private theorem queueRelinkOk_set_qstamp {c : FullCfg} {s0 s1 : FullState} {n : Nat}
    (h : QueueRelinkOk c s0 s1 n) (i : Nat) (v : BitVec 32) :
    QueueRelinkOk c s0
      { s1 with scratch := { s1.scratch with q_stamp := s1.scratch.q_stamp.set i v } } n :=
  ⟨h.1, ⟨h.2.1.core_ok, { h.2.1.scratch_ok with
    q_stamp_len := by simp [h.2.1.scratch_ok.q_stamp_len] }⟩, h.2.2.1, h.2.2.2⟩

private theorem queueRelinkOk_set_qfirst {c : FullCfg} {s0 s1 : FullState} {n : Nat}
    (h : QueueRelinkOk c s0 s1 n) (v : BitVec 64) :
    QueueRelinkOk c s0 { s1 with scratch := { s1.scratch with q_first := v } } n :=
  ⟨h.1, ⟨h.2.1.core_ok, { h.2.1.scratch_ok with }⟩, h.2.2.1, h.2.2.2⟩

private theorem queueRelinkOk_set_qlast {c : FullCfg} {s0 s1 : FullState} {n : Nat}
    (h : QueueRelinkOk c s0 s1 n) (v : BitVec 64) :
    QueueRelinkOk c s0 { s1 with scratch := { s1.scratch with q_last := v } } n :=
  ⟨h.1, ⟨h.2.1.core_ok, { h.2.1.scratch_ok with }⟩, h.2.2.1, h.2.2.2⟩

private theorem queueRelinkOk_set_qsidx {c : FullCfg} {s0 s1 : FullState} {n : Nat}
    (h : QueueRelinkOk c s0 s1 n) (v : BitVec 64) :
    QueueRelinkOk c s0 { s1 with scratch := { s1.scratch with q_search_idx := v } } n :=
  ⟨h.1, ⟨h.2.1.core_ok, { h.2.1.scratch_ok with }⟩, h.2.2.1, h.2.2.2⟩

private theorem queueRelinkOk_set_qsstamp {c : FullCfg} {s0 s1 : FullState} {n : Nat}
    (h : QueueRelinkOk c s0 s1 n) (v : BitVec 64) :
    QueueRelinkOk c s0 { s1 with scratch := { s1.scratch with q_search_stamp := v } } n :=
  ⟨h.1, ⟨h.2.1.core_ok, { h.2.1.scratch_ok with }⟩, h.2.2.1, h.2.2.2⟩

private theorem queueRelinkOk_set_qcurstamp {c : FullCfg} {s0 s1 : FullState} {n : Nat}
    (h : QueueRelinkOk c s0 s1 n) (v : BitVec 64) :
    QueueRelinkOk c s0 { s1 with scratch := { s1.scratch with q_cur_stamp := v } } n :=
  ⟨h.1, ⟨h.2.1.core_ok, { h.2.1.scratch_ok with }⟩, h.2.2.1, h.2.2.2⟩

private theorem queueRelinkOk_hdr3 {c : FullCfg} {s0 s1 : FullState} {n : Nat}
    (h : QueueRelinkOk c s0 s1 n) (a b d : BitVec 64) :
    QueueRelinkOk c s0
      { s1 with scratch := { s1.scratch with q_first := a, q_last := b, q_cur_stamp := d } } n :=
  ⟨h.1, ⟨h.2.1.core_ok, { h.2.1.scratch_ok with }⟩, h.2.2.1, h.2.2.2⟩

local macro "m7_sat_add_lit " c:ident s:ident R:ident mcur:ident hcont:ident : tactic =>
  `(tactic| (
    c0_hsplit
    · c0_hsteps_nogrp
      refine wp_join_group (ts := [i64])
        (fun _ m' => ∃ wl' wr' : Arr64 ($c).max_vars, (ReorderMem $c $s wl' wr' ⋆ $R) m')
        (fun _ _ m' ⟨wl', wr', hm'⟩ => by
          dsimp only [Blocks.get]; c0_hsteps
          exact $hcont () _ ⟨_, _, by assumption⟩)
        (fun J_sa hJ_sa => by
          c0_hsteps_nogrp
          all_goals exact hJ_sa _ $mcur ⟨_, _, by assumption⟩)
    · c0_hsteps_nogrp
      refine wp_join_group (ts := [i64])
        (fun _ m' => ∃ wl' wr' : Arr64 ($c).max_vars, (ReorderMem $c $s wl' wr' ⋆ $R) m')
        (fun _ _ m' ⟨wl', wr', hm'⟩ => by
          dsimp only [Blocks.get]; c0_hsteps
          exact $hcont () _ ⟨_, _, by assumption⟩)
        (fun J_sa hJ_sa => by
          c0_hsteps_nogrp
          all_goals exact hJ_sa _ $mcur ⟨_, _, by assumption⟩)))

private theorem m7_sat_add_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    {c : FullCfg} {s : FullState} {wl wr : Arr64 c.max_vars}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (ReorderMem c s wl wr ⋆ R) m)
    {lit v : BitVec 32} {cap w : BitVec 64}
    (hv : (BitVec.setWidth 64 v).toNat < c.max_vars)
    (J : Cont [])
    (hJ : ∀ m', (∃ wl' wr' : Arr64 c.max_vars, (ReorderMem c s wl' wr' ⋆ R) m') →
      wp Γ Q X (Expr.jump J ()) m') :
    wp Γ Q X
      (Expr.let_
        { sig := [i32, i32], code := OpCode.and i32, args := (Arg.var lit, Arg.imm 1, ()) }
        fun p_2 =>
        Expr.let_
          { sig := [i32, i32], code := OpCode.cmp CmpOp.eq i32 Ty.bool rfl,
            args := (Arg.var p_2.fst, Arg.imm 0, ()) }
          fun p_3 =>
          Expr.jnz (Arg.var p_3.fst)
            (Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var v, ()) }
              fun p_4 =>
              Expr.let_
                { sig := [i64, i64], code := OpCode.mul i64,
                  args := (Arg.var p_4.fst, Arg.imm 8, ()) }
                fun p_5 =>
                Expr.let_
                  { sig := [i64, i64], code := OpCode.add i64,
                    args := (Arg.var c.pTarjanMark, Arg.var p_5.fst, ()) }
                  fun p_6 =>
                  Expr.load i64 (Arg.var p_6.fst) fun ld =>
                    Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var v, ()) }
                      fun p =>
                      Expr.let_
                        { sig := [i64, i64], code := OpCode.mul i64,
                          args := (Arg.var p.fst, Arg.imm 8, ()) }
                        fun p =>
                        Expr.let_
                          { sig := [i64, i64], code := OpCode.add i64,
                            args := (Arg.var c.pTarjanMark, Arg.var p.fst, ()) }
                          fun p =>
                          Expr.group (sig := [[i64]])
                            (fun _ =>
                              Blocks.cons
                                (fun p_7 =>
                                  Expr.store (Arg.var p_7.fst) (Arg.var p.fst) (Expr.jump J ()))
                                Blocks.nil)
                            fun Js =>
                            Expr.let_
                              { sig := [i64, i64], code := OpCode.sub i64,
                                args := (Arg.var cap, Arg.var w, ()) }
                              fun p =>
                              Expr.let_
                                { sig := [i64, i64], code := OpCode.cmp CmpOp.ugt i64 Ty.bool rfl,
                                  args := (Arg.var ld, Arg.var p.fst, ()) }
                                fun p =>
                                Expr.jnz (Arg.var p.fst)
                                  (Expr.jump Js.fst (Arg.var cap, ()))
                                  (Expr.let_
                                    { sig := [i64, i64], code := OpCode.add i64,
                                      args := (Arg.var ld, Arg.var w, ()) }
                                    fun p => Expr.jump Js.fst (Arg.var p.fst, ())))
            (Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var v, ()) }
              fun p_4 =>
              Expr.let_
                { sig := [i64, i64], code := OpCode.mul i64,
                  args := (Arg.var p_4.fst, Arg.imm 8, ()) }
                fun p_5 =>
                Expr.let_
                  { sig := [i64, i64], code := OpCode.add i64,
                    args := (Arg.var c.pTarjanReach, Arg.var p_5.fst, ()) }
                  fun p_6 =>
                  Expr.load i64 (Arg.var p_6.fst) fun ld =>
                    Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var v, ()) }
                      fun p =>
                      Expr.let_
                        { sig := [i64, i64], code := OpCode.mul i64,
                          args := (Arg.var p.fst, Arg.imm 8, ()) }
                        fun p =>
                        Expr.let_
                          { sig := [i64, i64], code := OpCode.add i64,
                            args := (Arg.var c.pTarjanReach, Arg.var p.fst, ()) }
                          fun p =>
                          Expr.group (sig := [[i64]])
                            (fun _ =>
                              Blocks.cons
                                (fun p_7 =>
                                  Expr.store (Arg.var p_7.fst) (Arg.var p.fst) (Expr.jump J ()))
                                Blocks.nil)
                            fun Js =>
                            Expr.let_
                              { sig := [i64, i64], code := OpCode.sub i64,
                                args := (Arg.var cap, Arg.var w, ()) }
                              fun p =>
                              Expr.let_
                                { sig := [i64, i64], code := OpCode.cmp CmpOp.ugt i64 Ty.bool rfl,
                                  args := (Arg.var ld, Arg.var p.fst, ()) }
                                fun p =>
                                Expr.jnz (Arg.var p.fst)
                                  (Expr.jump Js.fst (Arg.var cap, ()))
                                  (Expr.let_
                                    { sig := [i64, i64], code := OpCode.add i64,
                                      args := (Arg.var ld, Arg.var w, ()) }
                                    fun p => Expr.jump Js.fst (Arg.var p.fst, ()))))
      m := by
  c0_hsteps_nogrp
  c0_hsplit
  · c0_hsteps_nogrp
    refine wp_join_group (ts := [i64])
      (fun _ m' => ∃ wl' wr' : Arr64 c.max_vars, (ReorderMem c s wl' wr' ⋆ R) m')
      (fun _ _ m' ⟨wl', wr', hm'⟩ => by
        dsimp only [Blocks.get]; c0_hsteps
        exact hJ _ ⟨_, _, by assumption⟩)
      (fun J_sa hJ_sa => by
        c0_hsteps_nogrp
        all_goals exact hJ_sa _ m ⟨_, _, by assumption⟩)
  · c0_hsteps_nogrp
    refine wp_join_group (ts := [i64])
      (fun _ m' => ∃ wl' wr' : Arr64 c.max_vars, (ReorderMem c s wl' wr' ⋆ R) m')
      (fun _ _ m' ⟨wl', wr', hm'⟩ => by
        dsimp only [Blocks.get]; c0_hsteps
        exact hJ _ ⟨_, _, by assumption⟩)
      (fun J_sa hJ_sa => by
        c0_hsteps_nogrp
        all_goals exact hJ_sa _ m ⟨_, _, by assumption⟩)

theorem full_reorder_queue_m7_wp (Γ : Env)
    (hWeight : EnvSpec Γ "full_reorder_weight_m7" m7ReorderWeightSpec)
    (hArenaNext : EnvSpec Γ "full_arena_next" fullArenaNextSpec)
    (hSift : EnvSpec Γ "full_reorder_sift_m7" m7ReorderSiftSpec) :
    ∀ a m Q X, fullReorderQueueSpec a m Q X →
      Func.wp Γ full_reorder_queue_m7_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hmF, hQ⟩
  have hQ' : ∀ r m', QueuePostOk c s R m' → Q r m' := by
    intro r m' ⟨s', hcore, hlen', hext, hm'⟩
    exact hQ r s' m' hcore hlen' hext hm'
  clear hQ
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have har := c.harena; unfold dimacsBound at har
  have hwc := c.hwcap; unfold dimacsBound at hwc
  have hcv_le := hlen.core_ok.cur_vars_le
  have hcv_29 : s.core.cur_vars < 2 ^ 29 := by omega
  have hcv_30 : s.core.cur_vars < 2 ^ 30 := lt_trans hcv_29 (by decide)
  have h2cv_le : 2 * s.core.cur_vars ≤ 2 * c.max_vars := Nat.mul_le_mul_left 2 hcv_le
  have h2cv_30 : 2 * s.core.cur_vars < 2 ^ 30 := by omega
  have hvals_len := hlen.core_ok.vals_len
  have hvals_2cv : 2 * s.core.cur_vars ≤ s.core.vals.length := hvals_len ▸ h2cv_le
  have hflags_len := hlen.core_ok.flags_len
  have harena_le := hlen.core_ok.arena_len_le
  have har_len := hlen.core_ok.arena_len_arr
  have har_29 : s.core.arena_len < 2 ^ 29 := by omega
  have har_le_arr : s.core.arena_len ≤ s.core.arena.length := by omega
  have hwlen_le := hlen.core_ok.wlen_le
  have hwlen_29 : s.core.wlen < 2 ^ 29 := by omega
  have hwstk_len := hlen.core_ok.wstk_len_arr
  have hwlen_stk : s.core.wlen ≤ s.core.wstk.length := by omega
  have hwvec_len := hlen.core_ok.wvec_len
  have hws_len := hlen.scratch_ok.wsort_len
  obtain ⟨wl, wr, hmR⟩ := reorderMem_of_fullMem hlen hmF
  clear hmF
  unfold Func.wp full_reorder_queue_m7_body
  c0_hsteps_nogrp
  -- Loop 1: zero wl[v], wr[v] for v = 0 ..< cur_vars
  refine wp_while_state1 (fun v : BitVec 64 => v)
    (fun v => s.core.cur_vars - v.toNat)
    (fun v m1 => v.toNat ≤ s.core.cur_vars ∧
      ∃ wl1 wr1 : Arr64 c.max_vars, (ReorderMem c s wl1 wr1 ⋆ R) m1)
    (fun J1 hJ1 => by c0_hsteps; exact hJ1 0#64 m ⟨Nat.zero_le _, wl, wr, hmR⟩)
    (fun J1 v m1 ⟨hv, wl1, wr1, hm1⟩ hJ1 => ?_)
  c0_hsplit
  · have hv_lt : v.toNat < s.core.cur_vars := bv64_lt_of_mod_lt hcv_30 ‹_›
    have hv_mv : v.toNat < c.max_vars := Nat.lt_of_lt_of_le hv_lt hcv_le
    have hvp1 := bv64_add1_toNat hcv_30 hv_lt
    c0_hsteps
    exact hJ1 (v + 1#64) _ hvp1.2.2 ⟨hvp1.2.1, _, _, by assumption⟩
  · -- Loop 2: arena clause scan wrapped in J_after2
    refine wp_join_group (ts := [i64])
      (fun _ m2 => ∃ wl2 wr2 : Arr64 c.max_vars, (ReorderMem c s wl2 wr2 ⋆ R) m2)
      ?_ ?_
    · rintro _ _ m2 ⟨wl2, wr2, hm2⟩
      dsimp only [Blocks.get]
      c0_hsteps_nogrp
      -- Loop 3: binary watches scan for lit = 0 ..< 2 * cur_vars
      refine wp_while_state1 (fun lit : BitVec 64 => lit)
        (fun lit => 2 * s.core.cur_vars - lit.toNat)
        (fun lit m3 => lit.toNat ≤ 2 * s.core.cur_vars ∧
          ∃ wl3 wr3 : Arr64 c.max_vars, (ReorderMem c s wl3 wr3 ⋆ R) m3)
        (fun J3 hJ3 => by c0_hsteps; exact hJ3 0#64 m2 ⟨Nat.zero_le _, wl2, wr2, hm2⟩)
        (fun J3 lit m3 ⟨hlit, wl3, wr3, hm3⟩ hJ3 => ?_)
      c0_hsplit
      · have hlit_nat : lit.toNat < 2 * s.core.cur_vars := bv64_lt_two_mul_mod hcv_29 ‹_›
        have hlit_2mx : lit.toNat < 2 * c.max_vars := Nat.lt_of_lt_of_le hlit_nat h2cv_le
        have hlit_vals : lit.toNat < s.core.vals.length := Nat.lt_of_lt_of_le hlit_nat hvals_2cv
        have hlit_v1 : (lit >>> (1 : BitVec 64)).toNat < s.core.flags.length :=
          hflags_len.symm ▸ Nat.lt_of_lt_of_le (ushr1_bv_lt hlit_nat) hcv_le
        have hlit_v2 : (lit >>> (1 : Nat)).toNat < s.core.flags.length :=
          hflags_len.symm ▸ Nat.lt_of_lt_of_le (ushr1_nat_lt hlit_nat) hcv_le
        have hlit_mv1 : (lit >>> (1 : BitVec 64)).toNat < c.max_vars :=
          Nat.lt_of_lt_of_le (ushr1_bv_lt hlit_nat) hcv_le
        have hlit_mv2 : (lit >>> (1 : Nat)).toNat < c.max_vars :=
          Nat.lt_of_lt_of_le (ushr1_nat_lt hlit_nat) hcv_le
        have hlit_w0 : (lit <<< (1 : BitVec 64)).toNat < s.core.wvec.length :=
          hwvec_len.symm ▸ shl1_bv_lt hlit_2mx hmx
        have hlit_w0n : (lit <<< (1 : Nat)).toNat < s.core.wvec.length :=
          hwvec_len.symm ▸ shl1_nat_lt hlit_2mx hmx
        have hlit_w1 : ((lit <<< (1 : BitVec 64)) + 1#64).toNat < s.core.wvec.length :=
          hwvec_len.symm ▸ shl1_add1_bv_lt hlit_2mx hmx
        have hlit_w1n : ((lit <<< (1 : Nat)) + 1#64).toNat < s.core.wvec.length :=
          hwvec_len.symm ▸ shl1_add1_nat_lt hlit_2mx hmx
        have hlitp1 := bv64_add1_toNat h2cv_30 hlit_nat
        c0_hsteps_nogrp
        refine wp_join_group (ts := [])
          (fun _ m3' => ∃ wl3' wr3' : Arr64 c.max_vars, (ReorderMem c s wl3' wr3' ⋆ R) m3')
          (fun _ _ m3' ⟨wl3', wr3', hm3'⟩ => by
            dsimp only [Blocks.get]; c0_hsteps
            exact hJ3 (lit + 1#64) m3' hlitp1.2.2 ⟨hlitp1.2.1, wl3', wr3', hm3'⟩)
          (fun J_next hJ_next => ?_)
        c0_hsplit
        · c0_hsplit
          · c0_hsteps_nogrp
            refine wp_join_group (ts := [])
              (fun _ m3' => ∃ wl3' wr3' : Arr64 c.max_vars, (ReorderMem c s wl3' wr3' ⋆ R) m3')
              (fun _ _ m3' hm3' => by dsimp only [Blocks.get]; c0_hsteps; exact hJ_next () m3' hm3')
              (fun J_next2 hJ_next2 => ?_)
            c0_hsplit
            · c0_hsplit
              · c0_hsplit
                · refine wp_join_group (ts := [i64])
                    (fun _ m3' =>
                      ∃ wl3' wr3' : Arr64 c.max_vars, (ReorderMem c s wl3' wr3' ⋆ R) m3')
                    (fun _ _ m3' hm3' => by
                      dsimp only [Blocks.get]; c0_hsteps; exact hJ_next2 () m3' hm3')
                    (fun J_aw hJ_aw => ?_)
                  have hwe_le :
                      ((BitVec.setWidth 64 s.core.wvec[2 * lit.toNat % 2 ^ 64]) +
                        (BitVec.setWidth 64
                          s.core.wvec[(2 * lit.toNat + 1) % 2 ^ 64])).toNat ≤
                        s.core.wlen :=
                    (m7_we_le_wlen hwlen_29 ‹_› ‹_›).2
                  have hwe_29 :
                      ((BitVec.setWidth 64 s.core.wvec[2 * lit.toNat % 2 ^ 64]) +
                        (BitVec.setWidth 64
                          s.core.wvec[(2 * lit.toNat + 1) % 2 ^ 64])).toNat < 2 ^ 30 :=
                    Nat.lt_of_le_of_lt hwe_le (lt_trans hwlen_29 (by decide))
                  refine wp_while_state1 (fun wi : BitVec 64 => wi)
                    (fun wi =>
                      ((BitVec.setWidth 64 s.core.wvec[2 * lit.toNat % 2 ^ 64]) +
                        (BitVec.setWidth 64
                          s.core.wvec[(2 * lit.toNat + 1) % 2 ^ 64])).toNat - wi.toNat)
                    (fun wi m4 =>
                      ∃ wl4 wr4 : Arr64 c.max_vars, (ReorderMem c s wl4 wr4 ⋆ R) m4)
                    (fun J_wi hJ_wi => by c0_hsteps; exact hJ_wi _ m3 ⟨wl3, wr3, hm3⟩)
                    (fun J_wi wi m4 ⟨wl4, wr4, hm4⟩ hJ_wi => ?_)
                  c0_hsplit
                  · have hwi_we :
                        wi.toNat <
                          ((BitVec.setWidth 64 s.core.wvec[2 * lit.toNat % 2 ^ 64]) +
                            (BitVec.setWidth 64
                              s.core.wvec[(2 * lit.toNat + 1) % 2 ^ 64])).toNat := by
                      dsimp only [lift2, Arg.val] at *; exact ‹_›
                    have hwi_stk : wi.toNat < s.core.wstk.length :=
                      Nat.lt_of_lt_of_le hwi_we (Nat.le_trans hwe_le hwlen_stk)
                    c0_hsteps_nogrp
                    c0_hsplit
                    · c0_hsteps
                      exact hJ_wi (wi + 2#64) m4
                        (bv64_add2_sub_lt hwe_29 hwi_we) ⟨wl4, wr4, hm4⟩
                    · c0_hsteps; exact hJ_aw (wi, ()) m4 ⟨wl4, wr4, hm4⟩
                    · refine wp_join_group (ts := [])
                        (fun _ m4' =>
                          ∃ wl4' wr4' : Arr64 c.max_vars, (ReorderMem c s wl4' wr4' ⋆ R) m4')
                        (fun _ _ m4' ⟨wl4', wr4', hm4'⟩ => by
                          dsimp only [Blocks.get]; c0_hsteps
                          exact hJ_wi (wi + 1#64) m4'
                            (bv64_add1_sub_lt hwe_29 hwi_we) ⟨wl4', wr4', hm4'⟩)
                        (fun J_cont hJ_cont => ?_)
                      c0_hsplit
                      · c0_hsplit
                        · have hother_lt :
                              (BitVec.setWidth 64
                                (s.core.wstk[wi.toNat]'hwi_stk &&& 2147483647#32)).toNat <
                                2 * s.core.cur_vars :=
                            bv64_lt_shl1_ofNat hcv_29 ‹_›
                          have hov_vals :
                              (BitVec.setWidth 64
                                (s.core.wstk[wi.toNat]'hwi_stk &&& 2147483647#32)).toNat <
                                s.core.vals.length :=
                            Nat.lt_of_lt_of_le hother_lt hvals_2cv
                          have hov_fl1 :
                              (BitVec.setWidth 64
                                ((s.core.wstk[wi.toNat]'hwi_stk &&& 2147483647#32) >>>
                                  (1 : BitVec 32))).toNat <
                                s.core.flags.length :=
                            hflags_len.symm ▸ Nat.lt_of_lt_of_le
                              (zext32_bv32_ushr1_bv_lt hother_lt) hcv_le
                          have hov_fl2 :
                              (BitVec.setWidth 64
                                ((s.core.wstk[wi.toNat]'hwi_stk &&& 2147483647#32) >>>
                                  (1 : Nat))).toNat <
                                s.core.flags.length :=
                            hflags_len.symm ▸ Nat.lt_of_lt_of_le
                              (zext32_bv32_ushr1_lt hother_lt) hcv_le
                          have hov_mv1 :
                              ((BitVec.setWidth 64
                                (s.core.wstk[wi.toNat]'hwi_stk &&& 2147483647#32)) >>>
                                  (1 : BitVec 64)).toNat <
                                c.max_vars :=
                            Nat.lt_of_lt_of_le (zext32_ushr1_lt hother_lt) hcv_le
                          have hov_mv2 :
                              ((BitVec.setWidth 64
                                (s.core.wstk[wi.toNat]'hwi_stk &&& 2147483647#32)) >>>
                                  (1 : Nat)).toNat <
                                c.max_vars :=
                            Nat.lt_of_lt_of_le (zext32_ushr1_nat_lt hother_lt) hcv_le
                          c0_hsteps_nogrp
                          refine wp_join_group (ts := [])
                            (fun _ m4' =>
                              ∃ wl4' wr4' : Arr64 c.max_vars, (ReorderMem c s wl4' wr4' ⋆ R) m4')
                            (fun _ _ m4' hm4' => by
                              dsimp only [Blocks.get]; c0_hsteps; exact hJ_cont () m4' hm4')
                            (fun J_nw hJ_nw => ?_)
                          c0_hsteps_nogrp
                          c0_hsplit
                          · refine wp_join_group (ts := [])
                              (fun _ m4' =>
                                ∃ wl4' wr4' : Arr64 c.max_vars,
                                  (ReorderMem c s wl4' wr4' ⋆ R) m4')
                              (fun _ _ m4' ⟨wl4', wr4', hm4'⟩ => by
                                dsimp only [Blocks.get]
                                refine wp_join_group (ts := [])
                                  (fun _ m4'' =>
                                    ∃ wl4'' wr4'' : Arr64 c.max_vars,
                                      (ReorderMem c s wl4'' wr4'' ⋆ R) m4'')
                                  (fun _ _ m4'' hm4'' => by
                                    c0_hsteps; exact hJ_nw () m4'' hm4'')
                                  (fun J_nw' hJ_nw' => by
                                    m7_sat_add_lit c s R m4' hJ_nw'))
                              (fun J_lit2 hJ_lit2 => by
                                m7_sat_add_lit c s R m4 hJ_lit2)
                          · c0_hsteps; exact hJ_nw () m4 ⟨wl4, wr4, hm4⟩
                          · c0_hsteps; exact hJ_nw () m4 ⟨wl4, wr4, hm4⟩
                        · c0_hsteps; exact hJ_cont () m4 ⟨wl4, wr4, hm4⟩
                      · c0_hsteps; exact hJ_cont () m4 ⟨wl4, wr4, hm4⟩
                  · c0_hsteps; exact hJ_aw (wi, ()) m4 ⟨wl4, wr4, hm4⟩
                · c0_hsteps; exact hJ_next2 () m3 ⟨wl3, wr3, hm3⟩
              · c0_hsteps; exact hJ_next2 () m3 ⟨wl3, wr3, hm3⟩
            · c0_hsteps; exact hJ_next2 () m3 ⟨wl3, wr3, hm3⟩
          · c0_hsteps; exact hJ_next () m3 ⟨wl3, wr3, hm3⟩
        · c0_hsteps; exact hJ_next () m3 ⟨wl3, wr3, hm3⟩
      · -- Loop 4: fold wl[v], wr[v] for v = 0 ..< cur_vars
        refine wp_while_state1 (fun v : BitVec 64 => v)
          (fun v => s.core.cur_vars - v.toNat)
          (fun v m4 => v.toNat ≤ s.core.cur_vars ∧
            ∃ wl4 wr4 : Arr64 c.max_vars, (ReorderMem c s wl4 wr4 ⋆ R) m4)
          (fun J4 hJ4 => by c0_hsteps; exact hJ4 0#64 m3 ⟨Nat.zero_le _, wl3, wr3, hm3⟩)
          (fun J4 v m4 ⟨hv, wl4, wr4, hm4⟩ hJ4 => ?_)
        c0_hsplit
        · have hv_lt : v.toNat < s.core.cur_vars := bv64_lt_of_mod_lt hcv_30 ‹_›
          have hv_mv : v.toNat < c.max_vars := Nat.lt_of_lt_of_le hv_lt hcv_le
          have hvp1 := bv64_add1_toNat hcv_30 hv_lt
          c0_hsteps_nogrp
          refine wp_join_group (ts := [i64]) (fun _ m' => m' = m4)
            (fun _ _ m4' hm_eq => by
              subst m4'; dsimp only [Blocks.get]; c0_hsteps
              exact hJ4 (v + 1#64) _ hvp1.2.2 ⟨hvp1.2.1, _, _, by assumption⟩)
            (fun Jf hJf => by c0_hsteps; all_goals exact hJf _ m4 rfl)
        · -- Loop 5: collect active vars into wsort (n, v)
          refine wp_while_state (fun p : BitVec 64 × BitVec 64 × PUnit => p)
            (fun p => s.core.cur_vars - p.2.1.toNat)
            (fun p m5 => p.2.1.toNat ≤ s.core.cur_vars ∧ p.1.toNat ≤ p.2.1.toNat ∧
              ∃ (s5 : FullState) (wl5 wr5 : Arr64 c.max_vars),
                SiftWsortEq s s5 ∧ s5.scratch.wsort.length = s.scratch.wsort.length ∧
                WsortBounded s5.scratch.wsort p.1.toNat s.core.cur_vars ∧
                (ReorderMem c s5 wl5 wr5 ⋆ R) m5)
            (fun J5 hJ5 => by
              c0_hsteps
              exact hJ5 (0#64, 0#64, ()) m4 ⟨Nat.zero_le _, Nat.zero_le _, s, wl4, wr4,
                siftWsortEq_refl s, rfl, fun _ h => absurd h (Nat.not_lt_zero _), hm4⟩)
            (fun J5 ⟨n, v, ⟨⟩⟩ m5 ⟨hv, hn_le, s5, wl5, wr5, hs5_eq, hws5_len, hwb5, hm5⟩ hJ5 => ?_)
          c0_hsplit
          · have hv_lt : v.toNat < s.core.cur_vars := bv64_lt_of_mod_lt hcv_30 ‹_›
            have hv_fl : v.toNat < s5.core.flags.length :=
              (siftWsortEq_flags hs5_eq).symm ▸ hflags_len.symm ▸ Nat.lt_of_lt_of_le hv_lt hcv_le
            have hvp1 := bv64_add1_toNat hcv_30 hv_lt
            have hn_lt : n.toNat < s.core.cur_vars := Nat.lt_of_le_of_lt hn_le hv_lt
            have hnp1 := bv64_add1_toNat hcv_30 hn_lt
            c0_hsteps_nogrp
            refine wp_join_group (ts := [i64])
              (fun n' m5' => n'.1.toNat ≤ v.toNat + 1 ∧
                ∃ (s5' : FullState),
                  SiftWsortEq s s5' ∧ s5'.scratch.wsort.length = s.scratch.wsort.length ∧
                  WsortBounded s5'.scratch.wsort n'.1.toNat s.core.cur_vars ∧
                  (ReorderMem c s5' wl5 wr5 ⋆ R) m5')
              (fun _ ⟨n', ⟨⟩⟩ m5' ⟨hn', s5', hs5', hlen5', hwb5', hm5'⟩ => by
                dsimp only [Blocks.get]; c0_hsteps
                exact hJ5 (n', v + 1#64, ()) m5' hvp1.2.2
                  ⟨hvp1.2.1, hvp1.1 ▸ hn', s5', wl5, wr5, hs5', hlen5', hwb5', hm5'⟩)
              (fun Jc hJc => ?_)
            c0_hsplit
            · have hn_ws : n.toNat < s5.scratch.wsort.length :=
                hws5_len.symm ▸ hws_len.symm ▸
                  Nat.lt_of_lt_of_le hn_lt
                    (Nat.le_trans hcv_le (Nat.le_mul_of_pos_left _ (by decide)))
              have hv_cv : (BitVec.setWidth 32 v).toNat < s.core.cur_vars :=
                bv64_zext32_toNat_lt hcv_29 hv_lt
              c0_hsteps
              refine hJc (n + 1#64, ()) _
                ⟨Nat.le_trans (Nat.le_of_eq hnp1.1) (Nat.succ_le_succ hn_le),
                 { s5 with scratch := { s5.scratch with
                     wsort := s5.scratch.wsort.set n.toNat (BitVec.setWidth 32 v) } },
                 siftWsortEq_set hs5_eq _,
                 by simp [hws5_len],
                 hnp1.1 ▸ wsortBounded_push hwb5 hn_ws hv_cv,
                 ?_⟩
              assumption
            · c0_hsteps
              exact hJc (n, ()) m5
                ⟨Nat.le_trans hn_le (Nat.le_succ _), s5, hs5_eq, hws5_len, hwb5, hm5⟩
          · -- Post-collection: heapsort (Loops 6 & 7) + Phase 2 VMTF relink
            have hn_cv : n.toNat ≤ s.core.cur_vars := Nat.le_trans hn_le hv
            have hn_29 : n.toNat < 2 ^ 30 := Nat.lt_of_le_of_lt hn_cv (lt_trans hcv_29 (by decide))
            have hcv_ws : s.core.cur_vars ≤ 2 * c.max_vars :=
              Nat.le_trans hcv_le (Nat.le_mul_of_pos_left _ (by decide))
            refine wp_join_group (ts := [])
              (fun _ m6 => ∃ (s6 : FullState) (wl6 wr6 : Arr64 c.max_vars),
                SiftWsortEq s s6 ∧ s6.scratch.wsort.length = s.scratch.wsort.length ∧
                WsortBounded s6.scratch.wsort n.toNat s.core.cur_vars ∧
                (ReorderMem c s6 wl6 wr6 ⋆ R) m6)
              ?_ ?_
            · rintro _ _ m6 ⟨s6, wl6, wr6, hs6_eq, hws6_len, hwb6, hm6⟩
              dsimp only [Blocks.get]
              obtain ⟨s7, hs7, hmF7⟩ :=
                queueRelinkOk_of_reorder hlen hs6_eq hws6_len hwb6 hm6
              have hlen7 := queueRelinkOk_lengths hs7
              c0_hsteps_nogrp
              -- Loop 7b: zero q_prev, q_next, q_stamp for i = 0 ..< cur_vars
              refine wp_while_state1 (fun i : BitVec 64 => i)
                (fun i => s.core.cur_vars - i.toNat)
                (fun i m7 => i.toNat ≤ s.core.cur_vars ∧ ∃ s7' : FullState,
                  QueueRelinkOk c s s7' n.toNat ∧ (FullMem c s7' ⋆ R) m7)
                (fun J7 hJ7 => by c0_hsteps; exact hJ7 0#64 m6 ⟨Nat.zero_le _, s7, hs7, hmF7⟩)
                (fun J7 i m7 ⟨hi7, s7', hs7', hm7⟩ hJ7 => ?_)
              have h7len := queueRelinkOk_lengths hs7'
              c0_hsplit
              · have hi7_lt : i.toNat < s.core.cur_vars := bv64_lt_of_mod_lt hcv_30 ‹_›
                have hi7_mv : i.toNat < c.max_vars := Nat.lt_of_lt_of_le hi7_lt hcv_le
                have hi7_qp : i.toNat < s7'.scratch.q_prev.length := h7len.2.2.2.1.symm ▸ hi7_mv
                have hi7_qn : i.toNat < s7'.scratch.q_next.length := h7len.2.2.2.2.1.symm ▸ hi7_mv
                have hi7_qs : i.toNat < s7'.scratch.q_stamp.length :=
                  h7len.2.2.2.2.2.symm ▸ hi7_mv
                have hi7p1 := bv64_add1_toNat hcv_30 hi7_lt
                c0_hsteps
                exact hJ7 (i + 1#64) _ hi7p1.2.2
                  ⟨hi7p1.2.1, _, queueRelinkOk_set_qstamp (queueRelinkOk_set_qnext
                    (queueRelinkOk_set_qprev hs7' _ _) _ _) _ _, by assumption⟩
              · c0_hsplit
                · c0_hsteps
                  exact hQ' (0#64, ()) _ (queueRelinkOk_to_post
                    (queueRelinkOk_set_qcurstamp (queueRelinkOk_set_qsstamp
                      (queueRelinkOk_set_qsidx (queueRelinkOk_set_qlast
                        (queueRelinkOk_set_qfirst hs7' _) _) _) _) _) (by assumption))
                · have hn_pos : 0 < n.toNat := bv64_pos_of_ne_zero ‹_›
                  have hn1_p := bv64_sub1_toNat hn_29 (le_refl _) hn_pos
                  refine wp_while_state (fun p : BitVec 64 × BitVec 64 × BitVec 64 × PUnit => p)
                    (fun p => n.toNat - p.2.2.1.toNat)
                    (fun p m8 => p.2.2.1.toNat ≤ n.toNat ∧ ∃ s8 : FullState,
                      QueueRelinkOk c s s8 n.toNat ∧ (FullMem c s8 ⋆ R) m8)
                    (fun J8 hJ8 => by
                      c0_hsteps
                      exact hJ8 (4294967295#64, 0#64, 0#64, ()) m7
                        ⟨Nat.zero_le _, s7', hs7', hm7⟩)
                    (fun J8 ⟨bidx, bstamp, i, ⟨⟩⟩ m8 ⟨hi, s8, hs8, hm8⟩ hJ8 => ?_)
                  have h8len := queueRelinkOk_lengths hs8
                  c0_hsplit
                  · have hi_nat : i.toNat < n.toNat := ‹_›
                    have hi_ws : i.toNat < s8.scratch.wsort.length :=
                      h8len.2.2.1.symm ▸ Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hi_nat hn_cv) hcv_ws
                    have hv_lt : (s8.scratch.wsort[i.toNat]'hi_ws).toNat < s.core.cur_vars :=
                      queueRelinkOk_wsort_get hs8 hi_nat hi_ws
                    have hv_mv : (BitVec.setWidth 64 (s8.scratch.wsort[i.toNat]'hi_ws)).toNat <
                        c.max_vars := zext64_32_lt_of_lt (Nat.lt_of_lt_of_le hv_lt hcv_le)
                    have hip1 := bv64_add1_toNat hn_29 hi_nat
                    c0_hsteps_nogrp
                    refine wp_join_group (ts := [i32])
                      (fun _ m8' => ∃ s8' : FullState,
                        QueueRelinkOk c s s8' n.toNat ∧ (FullMem c s8' ⋆ R) m8')
                      (fun _ _ m8' ⟨s8', hs8', hm8'⟩ => ?_)
                      (fun Jp hJp => by
                        c0_hsplit
                        · have hi_pos : 0 < i.toNat := ‹_›
                          have hi1_p := bv64_sub1_toNat hn_29 (Nat.le_of_lt hi_nat) hi_pos
                          have hi1_ws : (i - 1#64).toNat < s8.scratch.wsort.length :=
                            h8len.2.2.1.symm ▸
                              Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hi1_p.2.2.2 hn_cv) hcv_ws
                          c0_hsteps; exact hJp (_, ()) m8 ⟨s8, hs8, hm8⟩
                        · c0_hsteps; exact hJp (_, ()) m8 ⟨s8, hs8, hm8⟩)
                    have h8' := queueRelinkOk_lengths hs8'
                    have hv_qp : (BitVec.setWidth 64 (s8.scratch.wsort[i.toNat]'hi_ws)).toNat <
                        s8'.scratch.q_prev.length := h8'.2.2.2.1.symm ▸ hv_mv
                    c0_hsteps_nogrp
                    refine wp_join_group (ts := [i32])
                      (fun _ m8'' => ∃ s8'' : FullState,
                        QueueRelinkOk c s s8'' n.toNat ∧ (FullMem c s8'' ⋆ R) m8'')
                      (fun _ _ m8'' ⟨s8'', hs8'', hm8''⟩ => ?_)
                      (fun Jn hJn => by
                        c0_hsplit
                        · have hi1_ws : (i + 1#64).toNat < s8'.scratch.wsort.length :=
                            h8'.2.2.1.symm ▸
                              Nat.lt_of_lt_of_le
                                (Nat.lt_of_lt_of_le ‹(i + 1#64).toNat < n.toNat› hn_cv) hcv_ws
                          c0_hsteps
                          exact hJn (_, ()) _
                            ⟨_, queueRelinkOk_set_qprev hs8' _ _, by assumption⟩
                        · c0_hsteps
                          exact hJn (_, ()) _
                            ⟨_, queueRelinkOk_set_qprev hs8' _ _, by assumption⟩)
                    have h8'' := queueRelinkOk_lengths hs8''
                    have hv_qn : (BitVec.setWidth 64 (s8.scratch.wsort[i.toNat]'hi_ws)).toNat <
                        s8''.scratch.q_next.length := h8''.2.2.2.2.1.symm ▸ hv_mv
                    have hv_qs : (BitVec.setWidth 64 (s8.scratch.wsort[i.toNat]'hi_ws)).toNat <
                        s8''.scratch.q_stamp.length := h8''.2.2.2.2.2.symm ▸ hv_mv
                    c0_hsteps_nogrp
                    refine wp_join_group (ts := [i64, i64])
                      (fun p' m9 =>
                        ∃ s9 : FullState, QueueRelinkOk c s s9 n.toNat ∧ (FullMem c s9 ⋆ R) m9)
                      (fun _ ⟨nbi, nbs, ⟨⟩⟩ m9 ⟨s9, hs9, hm9⟩ => by
                        dsimp only [Blocks.get]; c0_hsteps
                        exact hJ8 (nbi, nbs, i + 1#64, ()) m9 hip1.2.2 ⟨hip1.2.1, s9, hs9, hm9⟩)
                      (fun Jb hJb => ?_)
                    have hv_v0 : ((BitVec.setWidth 64 (s8.scratch.wsort[i.toNat]'hi_ws)) <<<
                        (1 : BitVec 64)).toNat < s8''.core.vals.length :=
                      h8''.2.1.symm ▸ shl1_mul2_bv_lt hv_mv hmx
                    have hv_v0n : ((BitVec.setWidth 64 (s8.scratch.wsort[i.toNat]'hi_ws)) <<<
                        (1 : Nat)).toNat < s8''.core.vals.length :=
                      h8''.2.1.symm ▸ shl1_mul2_nat_lt hv_mv hmx
                    c0_hsteps_nogrp
                    c0_hsplit
                    · c0_hsteps
                      exact hJb (_, _, ()) _
                        ⟨_, queueRelinkOk_set_qstamp (queueRelinkOk_set_qnext hs8'' _ _) _ _,
                         by assumption⟩
                    · c0_hsteps
                      exact hJb (_, _, ()) _
                        ⟨_, queueRelinkOk_set_qstamp (queueRelinkOk_set_qnext hs8'' _ _) _ _,
                         by assumption⟩
                  · have hn_ws0 : 0 < s8.scratch.wsort.length :=
                      h8len.2.2.1.symm ▸ Nat.lt_of_lt_of_le hn_pos (Nat.le_trans hn_cv hcv_ws)
                    have hn_wsl : (n - 1#64).toNat < s8.scratch.wsort.length :=
                      h8len.2.2.1.symm ▸
                        Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hn1_p.2.2.2 hn_cv) hcv_ws
                    c0_hsteps_nogrp
                    refine wp_join_group (ts := [i64, i64])
                      (fun _ m9 =>
                        ∃ s9 : FullState, QueueRelinkOk c s s9 n.toNat ∧ (FullMem c s9 ⋆ R) m9)
                      (fun _ _ m9 ⟨s9, hs9, hm9⟩ => by
                        try dsimp only [Blocks.get]
                        c0_hsteps
                        exact hQ' (n, ()) _ (queueRelinkOk_to_post
                          (queueRelinkOk_set_qsstamp (queueRelinkOk_set_qsidx hs9 _) _)
                          (by assumption)))
                      (fun Jf hJf => ?_)
                    c0_hsplit
                    · have hv_lt : (s8.scratch.wsort[(n - 1#64).toNat]'hn_wsl).toNat <
                          s.core.cur_vars := queueRelinkOk_wsort_get hs8 hn1_p.2.2.2 hn_wsl
                      have hqlast_qs : (BitVec.setWidth 64
                          (s8.scratch.wsort[(n - 1#64).toNat]'hn_wsl)).toNat <
                          s8.scratch.q_stamp.length :=
                        h8len.2.2.2.2.2.symm ▸ zext64_32_lt_of_lt (Nat.lt_of_lt_of_le hv_lt hcv_le)
                      c0_hsteps
                      exact hJf (_, _, ()) _ ⟨_, queueRelinkOk_hdr3 hs8 _ _ _, by assumption⟩
                    · c0_hsteps
                      exact hJf (_, _, ()) _ ⟨_, queueRelinkOk_hdr3 hs8 _ _ _, by assumption⟩
            · -- Entry of 157: Loops 6 & 7 heapsort
              intro J6 hJ6
              c0_hsplit
              · have hn_pos : 0 < n.toNat := Nat.lt_trans Nat.zero_lt_one ‹_›
                have hn1_p := bv64_sub1_toNat hn_29 (le_refl _) hn_pos
                c0_hsteps_nogrp
                -- Loop 6: build heap
                refine wp_while_state1 (fun i : BitVec 64 => i)
                  (fun i => i.toNat)
                  (fun i m6 => i.toNat ≤ n.toNat ∧
                    ∃ (s6 : FullState) (wl6 wr6 : Arr64 c.max_vars),
                      SiftWsortEq s s6 ∧ s6.scratch.wsort.length = s.scratch.wsort.length ∧
                      WsortBounded s6.scratch.wsort n.toNat s.core.cur_vars ∧
                      (ReorderMem c s6 wl6 wr6 ⋆ R) m6)
                  (fun J_bld hJ_bld => by
                    c0_hsteps
                    exact hJ_bld (n >>> 1#64) m5 ⟨bv64_ushr1_le (le_refl _), s5, wl5, wr5,
                      hs5_eq, hws5_len, hwb5, hm5⟩)
                  (fun J_bld i m6 ⟨hi, s6, wl6, wr6, hs6_eq, hws6_len, hwb6, hm6⟩ hJ_bld => ?_)
                c0_hsplit
                · have hip := bv64_sub1_toNat hn_29 hi ‹_›
                  c0_hsteps_nogrp
                  apply wp_call_spec hSift
                  refine ⟨c, s6, wl6, wr6, R, rfl, siftWsortEq_lengthsOk hlen hs6_eq hws6_len,
                    (by change WsortBounded s6.scratch.wsort n.toNat s6.core.cur_vars
                        rw [siftWsortEq_curVars hs6_eq]; exact hwb6),
                    hm6, fun ws' m6' hwl' hwb' _ hm6' => ?_⟩
                  c0_hsteps
                  exact hJ_bld (i - 1#64) m6' hip.2.1
                    ⟨hip.2.2.1, { s6 with scratch := { s6.scratch with wsort := ws' } },
                     wl6, wr6, siftWsortEq_set hs6_eq ws', hwl'.trans hws6_len,
                     (by change WsortBounded ws' n.toNat s.core.cur_vars
                         rw [← siftWsortEq_curVars hs6_eq]; exact hwb'),
                     hm6'⟩
                · -- Loop 7: pop heap
                  refine wp_while_state1 (fun e : BitVec 64 => e)
                    (fun e => e.toNat)
                    (fun e m7 => e.toNat ≤ n.toNat ∧
                      ∃ (s7 : FullState) (wl7 wr7 : Arr64 c.max_vars),
                        SiftWsortEq s s7 ∧ s7.scratch.wsort.length = s.scratch.wsort.length ∧
                        WsortBounded s7.scratch.wsort n.toNat s.core.cur_vars ∧
                        (ReorderMem c s7 wl7 wr7 ⋆ R) m7)
                    (fun J_pop hJ_pop => by
                      c0_hsteps
                      exact hJ_pop n m6 ⟨le_refl _, s6, wl6, wr6,
                        hs6_eq, hws6_len, hwb6, hm6⟩)
                    (fun J_pop e m7 ⟨he, s7, wl7, wr7, hs7_eq, hws7_len, hwb7, hm7⟩ hJ_pop => ?_)
                  c0_hsplit
                  · have he_pos : 0 < e.toNat := Nat.lt_trans Nat.zero_lt_one ‹_›
                    have hep := bv64_sub1_toNat hn_29 he he_pos
                    have he1_n : (e - 1#64).toNat < n.toNat := Nat.lt_of_lt_of_le hep.2.1 he
                    have h0_ws : 0 < s7.scratch.wsort.length :=
                      hws7_len.symm ▸ hws_len.symm ▸
                        Nat.lt_of_lt_of_le hn_pos (Nat.le_trans hn_cv hcv_ws)
                    have he_ws : (e - 1#64).toNat < s7.scratch.wsort.length :=
                      hws7_len.symm ▸ hws_len.symm ▸
                        Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le he1_n hn_cv) hcv_ws
                    have hv0_lt : (s7.scratch.wsort[0]'h0_ws).toNat < s.core.cur_vars :=
                      wsortBounded_get hwb7 hn_pos h0_ws
                    have hve_lt :
                        (s7.scratch.wsort[(e - 1#64).toNat]'he_ws).toNat < s.core.cur_vars :=
                      wsortBounded_get hwb7 he1_n he_ws
                    have he_ws' : (e - 1#64).toNat <
                        (s7.scratch.wsort.set 0
                          (s7.scratch.wsort[(e - 1#64).toNat]'he_ws)).length := by
                      simpa using he_ws
                    c0_hsteps_nogrp
                    let ws_sw := (s7.scratch.wsort.set 0
                      (s7.scratch.wsort[(e - 1#64).toNat]'he_ws)).set
                      (e - 1#64).toNat (s7.scratch.wsort[0]'h0_ws)
                    have hwb_sw : WsortBounded ws_sw n.toNat s.core.cur_vars :=
                      wsortBounded_swap hwb7 hve_lt hv0_lt
                    apply wp_call_spec hSift
                    refine ⟨c, { s7 with scratch := { s7.scratch with wsort := ws_sw } },
                      wl7, wr7, R, rfl,
                      siftWsortEq_lengthsOk hlen (siftWsortEq_set hs7_eq ws_sw)
                        (by simpa [ws_sw] using hws7_len),
                      (by change WsortBounded ws_sw (e - 1#64).toNat s7.core.cur_vars
                          rw [siftWsortEq_curVars hs7_eq]
                          exact wsortBounded_shrink hwb_sw (Nat.le_of_lt he1_n)),
                      by assumption, fun ws' m7' hwl' hwb' hpres' hm7' => ?_⟩
                    c0_hsteps
                    exact hJ_pop (e - 1#64) m7' hep.2.1
                      ⟨Nat.le_of_lt he1_n,
                       { s7 with scratch := { s7.scratch with wsort := ws' } },
                       wl7, wr7, siftWsortEq_set hs7_eq ws',
                       (hwl'.trans (by simp only [ws_sw, List.length_set])).trans hws7_len,
                       wsortBounded_lift hwb_sw
                         (by change WsortBounded ws' (e - 1#64).toNat s.core.cur_vars
                             rw [← siftWsortEq_curVars hs7_eq]; exact hwb')
                         hpres',
                       hm7'⟩
                  · c0_hsteps; exact hJ6 () m7 ⟨s7, wl7, wr7, hs7_eq, hws7_len, hwb7, hm7⟩
              · c0_hsteps; exact hJ6 () m5 ⟨s5, wl5, wr5, hs5_eq, hws5_len, hwb5, hm5⟩
    · -- Loop 2 entry (`off = 0`)
      intro J_after2 hJ_after2
      refine wp_while_state1 (fun off : BitVec 64 => off)
        (fun off => s.core.arena_len - off.toNat)
        (fun _ m2 => ∃ wl2 wr2 : Arr64 c.max_vars, (ReorderMem c s wl2 wr2 ⋆ R) m2)
        (fun J2 hJ2 => by c0_hsteps; exact hJ2 0#64 m1 ⟨wl1, wr1, hm1⟩)
        (fun J2 off m2 ⟨wl2, wr2, hm2⟩ hJ2 => ?_)
      c0_hsplit
      · c0_hsplit
        · c0_hsteps; exact hJ_after2 (off, ()) m2 ⟨wl2, wr2, hm2⟩
        · rcases m7_off_bounds har_29 har_le_arr (by assumption) (by assumption) rfl with
              ⟨hoff3_le, hoff_29, hoff2_eq, hoff_lt, hoff2_lt⟩
          c0_hsteps_nogrp
          refine wp_join_group (ts := [])
            (fun _ m2' => ∃ wl2' wr2' : Arr64 c.max_vars, (ReorderMem c s wl2' wr2' ⋆ R) m2')
            (fun _ _ m2' ⟨wl2', wr2', hm2'⟩ => by
              dsimp only [Blocks.get]
              c0_hsteps_nogrp
              obtain ⟨tmk, trc, htmk, htrc, hmF'⟩ := fullMem_of_reorderMem hm2'
              apply wp_call_spec hArenaNext
              refine ⟨c, _, R, rfl, ?_, hmF', ?_⟩
              · exact ⟨hlen.core_ok, { hlen.scratch_ok with
                  tarjan_mark_len := htmk, tarjan_reach_len := htrc }⟩
              · c0_hsplit
                · c0_hsteps; exact hJ_after2 (off, ()) m2' ⟨wl2', wr2', hm2'⟩
                · c0_hsteps
                  refine hJ2 _ m2' ?_ ⟨wl2', wr2', hm2'⟩
                  first
                  | exact Nat.sub_lt_sub_left
                      (Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide)) hoff3_le)
                      (Nat.lt_of_not_le (by assumption))
                  | (clear hJ2 hJ_after2 hm2 hm2' hmF' hSift hArenaNext hWeight hQ'
                     have hlt : off.toNat < s.core.arena_len :=
                       Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide)) hoff3_le
                     bv_omega))
            (fun J_skip hJ_skip => ?_)
          c0_hsplit
          · c0_hsplit
            · -- Check clause bounds & scan literals
              rcases m7_sz_off3_le hoff3_le har_29 hoff2_lt hoff2_eq (by assumption) rfl rfl with
                ⟨hsz_le, hsz_29⟩
              c0_hsteps_nogrp
              refine wp_join_group (ts := [Ty.bool, i64, i64])
                (fun _ m2' => m2' = m2)
                (fun _ ⟨sat, un, _⟩ m2' hm_eq => by
                  subst m2'
                  dsimp only [Blocks.get]
                  c0_hsteps_nogrp
                  refine wp_join_group (ts := [i64])
                    (fun _ m2'' =>
                      ∃ wl2'' wr2'' : Arr64 c.max_vars, (ReorderMem c s wl2'' wr2'' ⋆ R) m2'')
                    (fun _ _ m2'' hm2'' => by
                      c0_hsteps; exact hJ_skip () m2'' hm2'')
                    (fun J_cw hJ_cw => ?_)
                  c0_hsplit
                  · c0_hsteps; exact hJ_cw _ m2 ⟨wl2, wr2, hm2⟩
                  · c0_hsplit
                    · c0_hsplit
                      · c0_hsteps_nogrp
                        apply wp_call_spec hWeight
                        intro w hw_le
                        refine wp_join_group (ts := [i64])
                          (fun _ m2k =>
                            ∃ wl2k wr2k : Arr64 c.max_vars, (ReorderMem c s wl2k wr2k ⋆ R) m2k)
                          (fun _ _ m2k hm2k => by
                            c0_hsteps; exact hJ_cw _ m2k hm2k)
                          (fun J_ak hJ_ak => ?_)
                        c0_hsplit
                        · refine wp_while_state1 (fun k : BitVec 64 => k)
                            (fun k => (BitVec.setWidth 64
                              (s.core.arena[(off + 2#64).toNat]'hoff2_lt)).toNat - k.toNat)
                            (fun k m2k =>
                              k.toNat ≤ (BitVec.setWidth 64
                                (s.core.arena[(off + 2#64).toNat]'hoff2_lt)).toNat ∧
                              ∃ wl2k wr2k : Arr64 c.max_vars, (ReorderMem c s wl2k wr2k ⋆ R) m2k)
                            (fun J_k hJ_k => by
                              c0_hsteps; exact hJ_k 0#64 m2 ⟨Nat.zero_le _, wl2, wr2, hm2⟩)
                            (fun J_k k m2k ⟨hk, wl2k, wr2k, hm2k⟩ hJ_k => ?_)
                          c0_hsplit
                          · have hk_lt :
                                k.toNat <
                                  (BitVec.setWidth 64
                                    (s.core.arena[(off + 2#64).toNat]'hoff2_lt)).toNat :=
                              m7_arena_k_lt hoff2_eq hoff_29 hoff2_lt (by assumption) rfl
                            have hk_29 : k.toNat < 2 ^ 29 := Nat.lt_trans hk_lt hsz_29
                            have hk3 := bv64_off3_add_toNat hoff_29 hk_29
                            have hk1 := bv64_add1_toNat (lt_trans hsz_29 (by decide)) hk_lt
                            have hk_ar : ((off + 3#64) + k).toNat < s.core.arena.length :=
                              hk3.1 ▸ Nat.lt_of_lt_of_le (Nat.add_lt_add_left hk_lt (off.toNat + 3))
                                (Nat.le_trans hsz_le har_le_arr)
                            c0_hsteps_nogrp
                            refine wp_join_group (ts := [])
                              (fun _ m2k' =>
                                ∃ wl2k' wr2k' : Arr64 c.max_vars,
                                  (ReorderMem c s wl2k' wr2k' ⋆ R) m2k')
                              (fun _ _ m2k' hm2k' => by
                                dsimp only [Blocks.get]; c0_hsteps
                                exact hJ_k (k + 1#64) m2k' hk1.2.2 ⟨hk1.2.1, hm2k'⟩)
                              (fun J_kl hJ_kl => ?_)
                            c0_hsplit
                            · have hlit_2cv :
                                  (BitVec.setWidth 64
                                    (s.core.arena[((off + 3#64) + k).toNat]'hk_ar)).toNat <
                                    2 * s.core.cur_vars := by
                                refine m7_arena_lit_2cv ?_ hcv_29 hk_ar _ (by assumption)
                                have h3b : (3 : BitVec 64).toNat = 3 := rfl
                                have hm3 : (3 : Nat) % 2 ^ 64 = 3 := by decide
                                rw [hk3.1, ← hk3.2.1]; simp only [h3b, hm3]
                              have hlit_2mx :
                                  (BitVec.setWidth 64
                                    (s.core.arena[((off + 3#64) + k).toNat]'hk_ar)).toNat <
                                    2 * c.max_vars := Nat.lt_of_lt_of_le hlit_2cv h2cv_le
                              have hlit_val :
                                  (BitVec.setWidth 64
                                    (s.core.arena[((off + 3#64) + k).toNat]'hk_ar)).toNat <
                                    s.core.vals.length := hvals_len ▸ hlit_2mx
                              have hlit_mv1 :
                                  ((BitVec.setWidth 64
                                    (s.core.arena[((off + 3#64) + k).toNat]'hk_ar)) >>>
                                      (1 : BitVec 64)).toNat <
                                    c.max_vars := zext32_ushr1_lt hlit_2mx
                              have hlit_mv2 :
                                  ((BitVec.setWidth 64
                                    (s.core.arena[((off + 3#64) + k).toNat]'hk_ar)) >>>
                                      (1 : Nat)).toNat <
                                    c.max_vars := zext32_ushr1_nat_lt hlit_2mx
                              have hlit_mv3 :
                                  (BitVec.setWidth 64
                                    (s.core.arena[((off + 3#64) + k).toNat]'hk_ar >>>
                                      (1 : Nat))).toNat <
                                    c.max_vars := zext32_bv32_ushr1_lt hlit_2mx
                              have hlit_mv4 :
                                  (BitVec.setWidth 64
                                    (s.core.arena[((off + 3#64) + k).toNat]'hk_ar >>>
                                      (1 : BitVec 32))).toNat <
                                    c.max_vars := zext32_bv32_ushr1_bv_lt hlit_2mx
                              c0_hsteps_nogrp
                              refine wp_join_group (ts := [])
                                (fun _ m2k' =>
                                  ∃ wl2k' wr2k' : Arr64 c.max_vars,
                                    (ReorderMem c s wl2k' wr2k' ⋆ R) m2k')
                                (fun _ _ m2k' hm2k' => by
                                  dsimp only [Blocks.get]; c0_hsteps
                                  exact hJ_kl () m2k' hm2k')
                                (fun J_val0 hJ_val0 => ?_)
                              c0_hsplit
                              · c0_hsteps_nogrp
                                refine wp_join_group (ts := [])
                                  (fun _ m2k' =>
                                    ∃ wl2k' wr2k' : Arr64 c.max_vars,
                                      (ReorderMem c s wl2k' wr2k' ⋆ R) m2k')
                                  (fun _ _ m2k' hm2k' => by
                                    dsimp only [Blocks.get]; c0_hsteps
                                    exact hJ_val0 () m2k' hm2k')
                                  (fun J_sa hJ_sa => by
                                    clear hJ2 hJ_after2 hJ_skip hJ_cw hJ_ak hJ_k hJ_kl hJ_val0
                                    clear hlit_2cv hlit_2mx hlit_mv1 hlit_mv2 hk1 hk3 hk_29 hk_lt
                                    clear hsz_le hsz_29 hoff3_le hoff_29 hoff2_eq hm2 hm1 hmR
                                    exact m7_sat_add_wp hm2k hlit_mv3 J_sa
                                      (fun m' hm' => by c0_hsteps; exact hJ_sa () m' hm'))
                              · c0_hsteps; exact hJ_val0 () m2k ⟨wl2k, wr2k, hm2k⟩
                            · c0_hsteps; exact hJ_kl () m2k ⟨wl2k, wr2k, hm2k⟩
                          · c0_hsteps; exact hJ_ak _ m2k ⟨wl2k, wr2k, hm2k⟩
                        · c0_hsteps; exact hJ_ak _ m2 ⟨wl2, wr2, hm2⟩
                      · c0_hsteps; exact hJ_cw _ m2 ⟨wl2, wr2, hm2⟩
                    · c0_hsteps; exact hJ_cw _ m2 ⟨wl2, wr2, hm2⟩)
                (fun J_su hJ_su => ?_)
              refine wp_while_state (fun p : BitVec 64 × BitVec 64 × PUnit => p)
                (fun p => (BitVec.setWidth 64
                  (s.core.arena[(off + 2#64).toNat]'hoff2_lt)).toNat - p.2.1.toNat)
                (fun p m_su => m_su = m2 ∧
                  p.2.1.toNat ≤ (BitVec.setWidth 64
                    (s.core.arena[(off + 2#64).toNat]'hoff2_lt)).toNat)
                (fun J_j hJ_j => by
                  c0_hsteps; exact hJ_j (0#64, 0#64, ()) m2 ⟨rfl, Nat.zero_le _⟩)
                (fun J_j ⟨un, j, ⟨⟩⟩ m_su ⟨hm_eq, hj⟩ hJ_j => ?_)
              subst m_su
              c0_hsplit
              · have hj_lt :
                    j.toNat <
                      (BitVec.setWidth 64
                        (s.core.arena[(off + 2#64).toNat]'hoff2_lt)).toNat :=
                  m7_arena_k_lt hoff2_eq hoff_29 hoff2_lt (by assumption) rfl
                have hj_29 : j.toNat < 2 ^ 29 := Nat.lt_trans hj_lt hsz_29
                have hj3 := bv64_off3_add_toNat hoff_29 hj_29
                have hj1 := bv64_add1_toNat (lt_trans hsz_29 (by decide)) hj_lt
                have hj_ar : ((off + 3#64) + j).toNat < s.core.arena.length :=
                  hj3.1 ▸ Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj_lt (off.toNat + 3))
                    (Nat.le_trans hsz_le har_le_arr)
                c0_hsteps_nogrp
                refine wp_join_group (ts := [Ty.bool, i64])
                  (fun _ m_su' => m_su' = m2)
                  (fun _ ⟨sat, un', _⟩ m_su' hm_eq' => by
                    subst m_su'
                    dsimp only [Blocks.get]
                    c0_hsteps
                    exact hJ_j (un', j + 1#64, ()) m2 hj1.2.2 ⟨rfl, hj1.2.1⟩)
                  (fun J_lit hJ_lit => ?_)
                c0_hsplit
                · have hj_2cv :
                      (BitVec.setWidth 64
                        (s.core.arena[((off + 3#64) + j).toNat]'hj_ar)).toNat <
                        2 * s.core.cur_vars := by
                    refine m7_arena_lit_2cv ?_ hcv_29 hj_ar _ (by assumption)
                    have h3b : (3 : BitVec 64).toNat = 3 := rfl
                    have hm3 : (3 : Nat) % 2 ^ 64 = 3 := by decide
                    rw [hj3.1, ← hj3.2.1]; simp only [h3b, hm3]
                  have hj_val :
                      (BitVec.setWidth 64
                        (s.core.arena[((off + 3#64) + j).toNat]'hj_ar)).toNat <
                        s.core.vals.length :=
                    hvals_len ▸ Nat.lt_of_lt_of_le hj_2cv h2cv_le
                  clear hJ2 hJ_after2 hJ_skip hm1 hmR hsz_le hsz_29 hoff3_le hoff_29 hoff2_eq
                  clear hj3 hj1 hj_2cv hj_lt hj_29 hSift hArenaNext hWeight hQ'
                  c0_hsteps_nogrp
                  c0_hsplit
                  · c0_hsteps; exact hJ_su (true, un, j, ()) m2 rfl
                  · c0_hsteps
                    all_goals exact hJ_lit (false, _, ()) m2 rfl
                · c0_hsteps; exact hJ_lit (false, un, ()) m2 rfl
              · c0_hsteps; exact hJ_su (false, un, j, ()) m2 rfl
            · c0_hsteps; exact hJ_skip () m2 ⟨wl2, wr2, hm2⟩
          · c0_hsteps; exact hJ_skip () m2 ⟨wl2, wr2, hm2⟩
      · c0_hsteps; exact hJ_after2 (off, ()) m2 ⟨wl2, wr2, hm2⟩

end ReorderQueueProof

/-! ## 4. Module Soundness (`m7Reorder_moduleOk`) & Concrete `Mem 64` NV (`XPost := False`) -/

section ModuleOkAndNV

/-- Four-entry C0 specification table for `m7ReorderModule` (including extern `full_arena_next`). -/
def m7ReorderSpecTable : List SpecEntry :=
  [ SpecEntry.mk "full_reorder_weight_m7" [i64] [i64] m7ReorderWeightSpec true,
    SpecEntry.mk "full_reorder_sift_m7" [i64, i64, i64] [] m7ReorderSiftSpec true,
    SpecEntry.mk "full_reorder_queue_m7" [i64] [i64] fullReorderQueueSpec true,
    SpecEntry.mk "full_arena_next" [i64, i32] [i32] fullArenaNextSpec true ]

/-- Specification environment generated by `m7ReorderSpecTable`. -/
def m7ReorderEnv : Env := Env.ofTable m7ReorderSpecTable

theorem m7ReorderEnv_noExit :
    ∀ f as bs xs m Q X X',
      m7ReorderEnv f as bs xs m Q X → m7ReorderEnv f as bs xs m Q X' :=
  Env.ofTable_noExit (by
    intro e he
    simp [m7ReorderSpecTable] at he
    rcases he with rfl | rfl | rfl | rfl <;> rfl)

private theorem m7ReorderEnv_weight :
    EnvSpec m7ReorderEnv "full_reorder_weight_m7" m7ReorderWeightSpec := by
  intro a m Q X h
  dsimp [m7ReorderEnv, m7ReorderSpecTable, Env.ofTable, Env.ofTable._f,
    SpecEntry.cast, SpecEntry.eff]
  exact Or.inl ⟨⟨rfl, rfl, rfl⟩, h⟩

private theorem m7ReorderEnv_sift :
    EnvSpec m7ReorderEnv "full_reorder_sift_m7" m7ReorderSiftSpec := by
  intro a m Q X h
  dsimp [m7ReorderEnv, m7ReorderSpecTable, Env.ofTable, Env.ofTable._f,
    SpecEntry.cast, SpecEntry.eff]
  exact Or.inr ⟨by decide, Or.inl ⟨⟨rfl, rfl, rfl⟩, h⟩⟩

private theorem m7ReorderEnv_arenaNext :
    EnvSpec m7ReorderEnv "full_arena_next" fullArenaNextSpec := by
  intro a m Q X h
  dsimp [m7ReorderEnv, m7ReorderSpecTable, Env.ofTable, Env.ofTable._f,
    SpecEntry.cast, SpecEntry.eff]
  exact Or.inr ⟨by decide, Or.inr ⟨by decide, Or.inr ⟨by decide, Or.inl ⟨⟨rfl, rfl, rfl⟩, h⟩⟩⟩⟩

theorem m7Reorder_tableImpl :
    TableImpl m7ReorderEnv m7ReorderFns m7ReorderSpecTable := by
  unfold m7ReorderFns m7_reorder_fns m7ReorderSpecTable
  refine ⟨SpecEntry.Impl.of (full_reorder_weight_m7_wp _),
    SpecEntry.Impl.of (full_reorder_sift_m7_wp _),
    SpecEntry.Impl.of (full_reorder_queue_m7_wp _ m7ReorderEnv_weight
      m7ReorderEnv_arenaNext m7ReorderEnv_sift),
    trivial⟩

/-- Whole-module C0 soundness for `m7ReorderModule` under `m7ReorderEnv`. -/
theorem m7Reorder_moduleOk : ModuleOk m7ReorderEnv m7ReorderModule := by
  refine Env.ofTable_moduleOk m7Reorder_acyclic ?_ m7Reorder_tableImpl
  unfold m7ReorderModule m7ReorderFns m7_reorder_fns
  exact ⟨full_reorder_weight_m7_wf, full_reorder_sift_m7_wf, full_reorder_queue_m7_wf, trivial⟩

/-- Drop-in Wave-3/4 function correctness theorem for `m7ReorderQueueFn`. -/
theorem m7ReorderQueueFn_wp :
    ∀ a m Q X, fullReorderQueueSpec a m Q X →
      Func.wp m7ReorderEnv m7ReorderQueueFn.body a m Q X :=
  full_reorder_queue_m7_wp m7ReorderEnv m7ReorderEnv_weight
    m7ReorderEnv_arenaNext m7ReorderEnv_sift

/-- Concrete `Mem 64` UNSAT NV theorem (`XPost := False`) on `nvM4TernaryMem`. -/
theorem nv_m7_reorder_queue (Q : Post [i64])
    (hQ : ∀ r s' m', PreservesCoreSlice FullState.core nvM4TernaryState s' →
      s'.LengthsOk nvM4TernaryCfg → FullExtScratchPres nvM4TernaryState s' →
      FullMem nvM4TernaryCfg s' m' → Q r m') :
    Func.wp m7ReorderEnv m7ReorderQueueFn.body (nvM4TernaryCfg.hdr, ())
      nvM4TernaryMem Q (fun _ _ _ _ => False) := by
  refine m7ReorderQueueFn_wp _ _ _ _ ⟨nvM4TernaryCfg, nvM4TernaryState, emp, rfl,
    nvM4Ternary_lengths, ?_, ?_⟩
  · rw [sep_emp]; exact nvM4TernaryMem_ok
  · intro r s' m' hcore hlen hext hm'
    rw [sep_emp] at hm'
    exact hQ r s' m' hcore hlen hext hm'

end ModuleOkAndNV

end LeanQbe.T.Examples.Kissat.FullM7Reorder

end
