module

public import LeanQbe.T.Examples.Kissat.FullM7FidelityCore
public import LeanQbe.T.Examples.Kissat.FullM4TernaryProof
public import LeanQbe.T.Examples.Kissat.FullM4Proof1
public import LeanQbe.T.Examples.Kissat.FullM6ProofUtil
public import LeanQbe.T.Examples.Kissat.FullSpec1
public import LeanQbe.T.Examples.Kissat.FullSpec2
import LeanQbe.T.AbiLemmas
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullSpec
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
# Kissat `FullM7Fidelity` Core Proofs — Part 1 (`Reorder`)

M1-clean UNSAT-only proofs (`public section`, `0` `@[expose]`, `0` `@[local]`, `0` `import all`,
`XPost := False`, `0` SAT proofs) for:
- `full_reorder_sift_fid_wp` (`fidReorderSiftSpec` = `FullM7Reorder.fidReorderSiftSpec`).
- `full_reorder_queue_fid_wp` (`FullM4Ternary.fullReorderQueueSpec`), removing the unused
  `vals[lit] == 0` filter in the arena clause weight loop, inlining `reorder_weight`, and adding
  the upstream `if (h->stable != 0)` VSIDS score rescale/update/heapify branch.
- `full_reorder_fid_wp` (`FullM4.m4ReorderSpec`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7FidelityCore

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM4Ternary
open Kraken.Bedrock2.Test

/-! ## 1. `FidReorderMem` <-> `FullMem` Helpers & `FidReorderTactics` -/

/-- Fixed-length `u64` array view (`n` elements). -/
abbrev FidArr64 (n : Nat) := { xs : List (BitVec 64) // xs.length = n }

/-- Variant of `FullMem` viewing `tarjan_mark` and `tarjan_reach` as `max_vars`-length `u64`
arrays (`wl`, `wr`). -/
def FidReorderMem (c : FullCfg) (s : FullState) (wl wr : FidArr64 c.max_vars) : Mem 64 → Prop :=
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
def FidWsortBounded (wsort : List (BitVec 32)) (n cv : Nat) : Prop :=
  ∀ i < n, (wsort[i]?.getD 0#32).toNat < cv

/-- Canonical sift helper specification for `full_reorder_sift_fid` over `FidReorderMem`. -/
def fidReorderSiftSpec : Spec [i64, i64, i64] [] :=
  fun (h, _start, n, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (wl wr : FidArr64 c.max_vars) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧
      FidWsortBounded s.scratch.wsort n.toNat s.core.cur_vars ∧
      (FidReorderMem c s wl wr ⋆ R) m ∧
      ∀ (ws' : List (BitVec 32)) (m' : Mem 64),
        ws'.length = s.scratch.wsort.length →
        FidWsortBounded ws' n.toNat s.core.cur_vars →
        (∀ j, n.toNat ≤ j → ws'[j]? = s.scratch.wsort[j]?) →
        let s' := { s with scratch := { s.scratch with wsort := ws' } }
        (FidReorderMem c s' wl wr ⋆ R) m' → Q () m'

theorem fidReorderSiftSpec_monoX {a m Q X X'} (h : fidReorderSiftSpec a m Q X) :
    fidReorderSiftSpec a m Q X' :=
  h

private def fidPackPairs64 : List (BitVec 32) → List (BitVec 64)
  | [] => []
  | lo :: hi :: rest => ((hi.setWidth 64 <<< 32) ||| lo.setWidth 64) :: fidPackPairs64 rest
  | [_] => []

private def fidUnpackPairs32 : List (BitVec 64) → List (BitVec 32)
  | [] => []
  | w :: rest => w.setWidth 32 :: (w >>> 32).setWidth 32 :: fidUnpackPairs32 rest

private theorem fidPackPairs64_single (x : BitVec 32) : fidPackPairs64 [x] = [] := rfl
private theorem fidPackPairs64_cons2 (lo hi : BitVec 32) (rest : List (BitVec 32)) :
    fidPackPairs64 (lo :: hi :: rest) =
      ((hi.setWidth 64 <<< 32) ||| lo.setWidth 64) :: fidPackPairs64 rest := rfl

private theorem fidUnpackPairs32_cons (w : BitVec 64) (rest : List (BitVec 64)) :
    fidUnpackPairs32 (w :: rest) =
      w.setWidth 32 :: (w >>> 32).setWidth 32 :: fidUnpackPairs32 rest := rfl

private theorem fid_packPairs64_length : ∀ xs : List (BitVec 32),
    (fidPackPairs64 xs).length = xs.length / 2
  | [] => rfl
  | [_] => by rw [fidPackPairs64_single, List.length_nil, List.length_singleton]
  | _ :: _ :: rest => by
    rw [fidPackPairs64_cons2, List.length_cons, fid_packPairs64_length rest]
    simp only [List.length_cons]; omega

private theorem fid_unpackPairs32_length (ys : List (BitVec 64)) :
    (fidUnpackPairs32 ys).length = 2 * ys.length := by
  induction ys with
  | nil => rfl
  | cons _ _ ih => rw [fidUnpackPairs32_cons]; simp only [List.length_cons, ih]; omega

private theorem fid_toBytes_8_split (w : BitVec 64) :
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
  have hd : ∀ (k : Int), (((k / 256) / 256) / 256) / 256 = k / (2 : Int) ^ 32 := fun _ => by
    omega
  simp only [Int.toBytes, Int.take, List.cons_append, List.nil_append, hd]

private theorem fid_cell_i32_eq_int4 (a : BitVec 64) (v : BitVec 32) :
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
  rw [Nat.mod_eq_of_lt hlt64]; cases v.msb
  · simp
  · simp only [↓reduceIte, Int.natCast_pow, Int.cast_ofNat_Int]; omega

private theorem fid_cell64_eq_cell_i32_pair (a w : BitVec 64) :
    cell64 a w =
      (cell (t := i32) a (w.setWidth 32) ⋆ cell (t := i32) (a + 4) ((w >>> 32).setWidth 32)) := by
  rw [cell64_eq_word8, word8_eq_int4_sep, fid_cell_i32_eq_int4, fid_cell_i32_eq_int4,
    int4_setWidth32, int4_setWidth32]
  have hdrop : (Int.toBytes 8 (w.toNat : Int)).drop 4 =
      Int.toBytes 4 ((w >>> 32).toNat : Int) := by
    have h1 : (((w >>> 32).setWidth 32).toNat : Int) =
        ((w >>> 32).toNat : Int) % (2 : Int) ^ (8 * 4) := by
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega
    rw [fid_toBytes_8_split, List.drop_left' (by simp [Int.toBytes_length]), h1, Int.toBytes_emod]
  unfold int4; rw [hdrop]

private theorem fid_pack_pair_word (lo hi : BitVec 32) :
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

private theorem fid_array_i32_eq_array64_pack (a : BitVec 64) (xs : List (BitVec 32))
    (heven : xs.length % 2 = 0) :
    array (t := i32) a xs = array64 a (fidPackPairs64 xs) := by
  match xs with
  | [] => rfl
  | [_] => simp at heven
  | lo :: hi :: rest =>
    have hrest : rest.length % 2 = 0 := by simp at heven; omega
    have hlo := (fid_pack_pair_word lo hi).1; have hhi := (fid_pack_pair_word lo hi).2
    have hstep : a + BitVec.ofNat 64 (Ty.bytes i32) + BitVec.ofNat 64 (Ty.bytes i32) = a + 8 := by
      change a + 4#64 + 4#64 = a + 8#64; bv_omega
    have h4 : a + BitVec.ofNat 64 (Ty.bytes i32) = a + 4 := by change a + 4#64 = a + 4; rfl
    rw [fidPackPairs64_cons2]
    rw [array_cons, array_cons, array64_cons, fid_cell64_eq_cell_i32_pair, hlo, hhi, ← h4, hstep,
      fid_array_i32_eq_array64_pack (a + 8) rest hrest, sep_assoc]

private theorem fid_array64_eq_array_i32_unpack (a : BitVec 64) (ys : List (BitVec 64)) :
    array64 a ys = array (t := i32) a (fidUnpackPairs32 ys) := by
  induction ys generalizing a with
  | nil => rfl
  | cons w rest ih =>
    have hstep : a + BitVec.ofNat 64 (Ty.bytes i32) + BitVec.ofNat 64 (Ty.bytes i32) = a + 8 := by
      change a + 4#64 + 4#64 = a + 8#64; bv_omega
    have h4 : a + BitVec.ofNat 64 (Ty.bytes i32) = a + 4 := by change a + 4#64 = a + 4; rfl
    rw [fidUnpackPairs32_cons]
    rw [array64_cons, array_cons, array_cons, fid_cell64_eq_cell_i32_pair, ← h4, hstep,
      ih (a + 8), sep_assoc]

private theorem fid_reorderMem_of_fullMem {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hlen : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m) :
    ∃ wl wr : FidArr64 c.max_vars, (FidReorderMem c s wl wr ⋆ R) m := by
  have htm := hlen.scratch_ok.tarjan_mark_len; have htr := hlen.scratch_ok.tarjan_reach_len
  let wl : FidArr64 c.max_vars := ⟨fidPackPairs64 s.scratch.tarjan_mark, by
    rw [fid_packPairs64_length, htm]; omega⟩
  let wr : FidArr64 c.max_vars := ⟨fidPackPairs64 s.scratch.tarjan_reach, by
    rw [fid_packPairs64_length, htr]; omega⟩
  refine ⟨wl, wr, ?_⟩
  unfold FullMem FullScratchArrays FullScrWksArrs at hm
  rw [fid_array_i32_eq_array64_pack c.pTarjanMark s.scratch.tarjan_mark (by omega),
    fid_array_i32_eq_array64_pack c.pTarjanReach s.scratch.tarjan_reach (by omega)] at hm
  unfold FidReorderMem; exact hm

private theorem fid_fullMem_of_reorderMem {c : FullCfg} {s : FullState}
    {wl wr : FidArr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FidReorderMem c s wl wr ⋆ R) m) :
    ∃ tmk trc : List (BitVec 32),
      tmk.length = 2 * c.max_vars ∧ trc.length = 2 * c.max_vars ∧
      (FullMem c { s with scratch := { s.scratch with tarjan_mark := tmk, tarjan_reach := trc } } ⋆
        R) m := by
  let tmk := fidUnpackPairs32 wl.1; let trc := fidUnpackPairs32 wr.1
  refine ⟨tmk, trc, by simp [tmk, fid_unpackPairs32_length, wl.2],
    by simp [trc, fid_unpackPairs32_length, wr.2], ?_⟩
  unfold FidReorderMem at hm
  rw [fid_array64_eq_array_i32_unpack c.pTarjanMark wl.1,
    fid_array64_eq_array_i32_unpack c.pTarjanReach wr.1] at hm
  unfold FullMem FullScratchArrays FullScrWksArrs; exact hm

private theorem fid_bv64_mul4_eq (i : BitVec 64) :
    (i * 4 : BitVec 64) = BitVec.ofNat 64 (4 * i.toNat) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_mul, Nat.mul_comm]

private theorem fid_bv64_mul8_eq (i : BitVec 64) :
    (i * 8 : BitVec 64) = BitVec.ofNat 64 (8 * i.toNat) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_mul, Nat.mul_comm]

namespace FidReorderTactics

open FullArenaTactics
open scoped FullArenaTactics

@[scoped c0_load] theorem load_fidre_arena_len {c : FullCfg} {s : FullState}
    {wl wr : FidArr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FidReorderMem c s wl wr ⋆ R) m) :
    loadVal m i64 (c.hdr + 48) = some (BitVec.ofNat 64 s.core.arena_len) := by
  obtain ⟨_, _, _, _, hmF⟩ := fid_fullMem_of_reorderMem hm; simpa using load_full_arena_len hmF

@[scoped c0_load] theorem load_fidre_wlen {c : FullCfg} {s : FullState}
    {wl wr : FidArr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FidReorderMem c s wl wr ⋆ R) m) :
    loadVal m i64 (c.hdr + 56) = some (BitVec.ofNat 64 s.core.wlen) := by
  obtain ⟨_, _, _, _, hmF⟩ := fid_fullMem_of_reorderMem hm; simpa using load_full_wlen hmF

@[scoped c0_load] theorem load_fidre_values_ptr {c : FullCfg} {s : FullState}
    {wl wr : FidArr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FidReorderMem c s wl wr ⋆ R) m) : loadVal m i64 (c.hdr + 64) = some c.pVals := by
  obtain ⟨_, _, _, _, hmF⟩ := fid_fullMem_of_reorderMem hm; simpa using load_full_values_ptr hmF

@[scoped c0_load] theorem load_fidre_watch_vec_ptr {c : FullCfg} {s : FullState}
    {wl wr : FidArr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FidReorderMem c s wl wr ⋆ R) m) : loadVal m i64 (c.hdr + 104) = some c.pWvec := by
  obtain ⟨_, _, _, _, hmF⟩ := fid_fullMem_of_reorderMem hm; simpa using load_full_watch_vec_ptr hmF

@[scoped c0_load] theorem load_fidre_arena_ptr {c : FullCfg} {s : FullState}
    {wl wr : FidArr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FidReorderMem c s wl wr ⋆ R) m) : loadVal m i64 (c.hdr + 112) = some c.pArena := by
  obtain ⟨_, _, _, _, hmF⟩ := fid_fullMem_of_reorderMem hm; simpa using load_full_arena_ptr hmF

@[scoped c0_load] theorem load_fidre_watch_stk_ptr {c : FullCfg} {s : FullState}
    {wl wr : FidArr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FidReorderMem c s wl wr ⋆ R) m) : loadVal m i64 (c.hdr + 120) = some c.pWstk := by
  obtain ⟨_, _, _, _, hmF⟩ := fid_fullMem_of_reorderMem hm; simpa using load_full_watch_stk_ptr hmF

@[scoped c0_load] theorem load_fidre_score_ptr {c : FullCfg} {s : FullState}
    {wl wr : FidArr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FidReorderMem c s wl wr ⋆ R) m) : loadVal m i64 (c.hdr + 216) = some c.pScore := by
  obtain ⟨_, _, _, _, hmF⟩ := fid_fullMem_of_reorderMem hm; simpa using load_full_score_ptr hmF

@[scoped c0_load] theorem load_fidre_scinc {c : FullCfg} {s : FullState}
    {wl wr : FidArr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FidReorderMem c s wl wr ⋆ R) m) :
    loadVal m i64 (c.hdr + 256) = some s.scratch.scinc := by
  obtain ⟨_, _, _, _, hmF⟩ := fid_fullMem_of_reorderMem hm; simpa using load_full_scinc hmF

@[scoped c0_load] theorem load_fidre_q_prev_ptr {c : FullCfg} {s : FullState}
    {wl wr : FidArr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FidReorderMem c s wl wr ⋆ R) m) : loadVal m i64 (c.hdr + 368) = some c.pQPrev := by
  obtain ⟨_, _, _, _, hmF⟩ := fid_fullMem_of_reorderMem hm; simpa using load_full_q_prev_ptr hmF

@[scoped c0_load] theorem load_fidre_q_next_ptr {c : FullCfg} {s : FullState}
    {wl wr : FidArr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FidReorderMem c s wl wr ⋆ R) m) : loadVal m i64 (c.hdr + 376) = some c.pQNext := by
  obtain ⟨_, _, _, _, hmF⟩ := fid_fullMem_of_reorderMem hm; simpa using load_full_q_next_ptr hmF

@[scoped c0_load] theorem load_fidre_q_stamp_ptr {c : FullCfg} {s : FullState}
    {wl wr : FidArr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FidReorderMem c s wl wr ⋆ R) m) : loadVal m i64 (c.hdr + 384) = some c.pQStamp := by
  obtain ⟨_, _, _, _, hmF⟩ := fid_fullMem_of_reorderMem hm; simpa using load_full_q_stamp_ptr hmF

@[scoped c0_load] theorem load_fidre_wsort_ptr {c : FullCfg} {s : FullState}
    {wl wr : FidArr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FidReorderMem c s wl wr ⋆ R) m) : loadVal m i64 (c.hdr + 408) = some c.pWsort := by
  obtain ⟨_, _, _, _, hmF⟩ := fid_fullMem_of_reorderMem hm; simpa using load_full_wsort_ptr hmF

@[scoped c0_load] theorem load_fidre_stable {c : FullCfg} {s : FullState}
    {wl wr : FidArr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FidReorderMem c s wl wr ⋆ R) m) :
    loadVal m i64 (c.hdr + 552) = some s.scratch.stable := by
  obtain ⟨_, _, _, _, hmF⟩ := fid_fullMem_of_reorderMem hm; simpa using load_full_stable hmF

@[scoped c0_load] theorem load_fidre_cur_vars {c : FullCfg} {s : FullState}
    {wl wr : FidArr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FidReorderMem c s wl wr ⋆ R) m) :
    loadVal m i64 (c.hdr + 776) = some (BitVec.ofNat 64 s.core.cur_vars) := by
  obtain ⟨_, _, _, _, hmF⟩ := fid_fullMem_of_reorderMem hm; simpa using load_full_cur_vars hmF

@[scoped c0_load] theorem load_fidre_flags_ptr {c : FullCfg} {s : FullState}
    {wl wr : FidArr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FidReorderMem c s wl wr ⋆ R) m) : loadVal m i64 (c.hdr + 800) = some c.pFlags := by
  obtain ⟨_, _, _, _, hmF⟩ := fid_fullMem_of_reorderMem hm; simpa using load_full_flags_ptr hmF

@[scoped c0_load] theorem load_fidre_tarjan_mark_ptr {c : FullCfg} {s : FullState}
    {wl wr : FidArr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FidReorderMem c s wl wr ⋆ R) m) :
    loadVal m i64 (c.hdr + 864) = some c.pTarjanMark := by
  obtain ⟨_, _, _, _, hmF⟩ := fid_fullMem_of_reorderMem hm
  simpa using load_full_tarjan_mark_ptr hmF

@[scoped c0_load] theorem load_fidre_tarjan_reach_ptr {c : FullCfg} {s : FullState}
    {wl wr : FidArr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FidReorderMem c s wl wr ⋆ R) m) :
    loadVal m i64 (c.hdr + 872) = some c.pTarjanReach := by
  obtain ⟨_, _, _, _, hmF⟩ := fid_fullMem_of_reorderMem hm
  simpa using load_full_tarjan_reach_ptr hmF

@[scoped c0_load] theorem c0_load_fidre_vals {c : FullCfg} {s : FullState}
    {wl wr : FidArr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hi : i.toNat < s.core.vals.length) (hm : (FidReorderMem c s wl wr ⋆ R) m) :
    loadVal m i8 (c.pVals + i) = some s.core.vals[i.toNat] := by
  obtain ⟨tmk, trc, _, _, hmF⟩ := fid_fullMem_of_reorderMem hm
  let s' := { s with scratch := { s.scratch with tarjan_mark := tmk, tarjan_reach := trc } }
  simpa [s'] using c0_load_full_vals (s := s') hi hmF

@[scoped c0_load] theorem c0_load_fidre_flags {c : FullCfg} {s : FullState}
    {wl wr : FidArr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hi : i.toNat < s.core.flags.length) (hm : (FidReorderMem c s wl wr ⋆ R) m) :
    loadVal m i32 (c.pFlags + i * 4) = some s.core.flags[i.toNat] := by
  obtain ⟨tmk, trc, _, _, hmF⟩ := fid_fullMem_of_reorderMem hm
  let s' := { s with scratch := { s.scratch with tarjan_mark := tmk, tarjan_reach := trc } }
  simpa [s'] using c0_load_full_flags (s := s') hi hmF

@[scoped c0_load] theorem c0_load_fidre_arena {c : FullCfg} {s : FullState}
    {wl wr : FidArr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hi : i.toNat < s.core.arena.length) (hm : (FidReorderMem c s wl wr ⋆ R) m) :
    loadVal m i32 (c.pArena + i * 4) = some s.core.arena[i.toNat] := by
  obtain ⟨tmk, trc, _, _, hmF⟩ := fid_fullMem_of_reorderMem hm
  let s' := { s with scratch := { s.scratch with tarjan_mark := tmk, tarjan_reach := trc } }
  simpa [s'] using c0_load_full_arena (s := s') hi hmF

@[scoped c0_load] theorem c0_load_fidre_wvec {c : FullCfg} {s : FullState}
    {wl wr : FidArr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hi : i.toNat < s.core.wvec.length) (hm : (FidReorderMem c s wl wr ⋆ R) m) :
    loadVal m i32 (c.pWvec + i * 4) = some s.core.wvec[i.toNat] := by
  obtain ⟨tmk, trc, _, _, hmF⟩ := fid_fullMem_of_reorderMem hm
  let s' := { s with scratch := { s.scratch with tarjan_mark := tmk, tarjan_reach := trc } }
  simpa [s'] using c0_load_full_wvec (s := s') hi hmF

@[scoped c0_load] theorem c0_load_fidre_wstk {c : FullCfg} {s : FullState}
    {wl wr : FidArr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hi : i.toNat < s.core.wstk.length) (hm : (FidReorderMem c s wl wr ⋆ R) m) :
    loadVal m i32 (c.pWstk + i * 4) = some s.core.wstk[i.toNat] := by
  obtain ⟨tmk, trc, _, _, hmF⟩ := fid_fullMem_of_reorderMem hm
  let s' := { s with scratch := { s.scratch with tarjan_mark := tmk, tarjan_reach := trc } }
  simpa [s'] using c0_load_full_wstk (s := s') hi hmF

@[scoped c0_load] theorem c0_load_fidre_q_stamp {c : FullCfg} {s : FullState}
    {wl wr : FidArr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hi : i.toNat < s.scratch.q_stamp.length) (hm : (FidReorderMem c s wl wr ⋆ R) m) :
    loadVal m i32 (c.pQStamp + i * 4) = some s.scratch.q_stamp[i.toNat] := by
  obtain ⟨tmk, trc, _, _, hmF⟩ := fid_fullMem_of_reorderMem hm
  let s' := { s with scratch := { s.scratch with tarjan_mark := tmk, tarjan_reach := trc } }
  simpa [s'] using c0_load_full_q_stamp (s := s') hi hmF

@[scoped c0_load] theorem c0_load_fidre_wsort {c : FullCfg} {s : FullState}
    {wl wr : FidArr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hi : i.toNat < s.scratch.wsort.length) (hm : (FidReorderMem c s wl wr ⋆ R) m) :
    loadVal m i32 (c.pWsort + i * 4) = some s.scratch.wsort[i.toNat] := by
  obtain ⟨tmk, trc, _, _, hmF⟩ := fid_fullMem_of_reorderMem hm
  let s' := { s with scratch := { s.scratch with tarjan_mark := tmk, tarjan_reach := trc } }
  simpa [s'] using c0_load_full_wsort (s := s') hi hmF

@[scoped c0_load] theorem load_fidre_wsort0 {c : FullCfg} {s : FullState}
    {wl wr : FidArr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hi : 0 < s.scratch.wsort.length) (hm : (FidReorderMem c s wl wr ⋆ R) m) :
    loadVal m i32 c.pWsort = some s.scratch.wsort[0] := by
  obtain ⟨tmk, trc, _, _, hmF⟩ := fid_fullMem_of_reorderMem hm
  let s' := { s with scratch := { s.scratch with tarjan_mark := tmk, tarjan_reach := trc } }
  simpa [s'] using load_full_wsort0 (s := s') hi hmF

@[scoped c0_load] theorem c0_load_fidre_score {c : FullCfg} {s : FullState}
    {wl wr : FidArr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hi : i.toNat < s.scratch.score.length) (hm : (FidReorderMem c s wl wr ⋆ R) m) :
    loadVal m i64 (c.pScore + i * 8) = some s.scratch.score[i.toNat] := by
  obtain ⟨tmk, trc, _, _, hmF⟩ := fid_fullMem_of_reorderMem hm
  let s' := { s with scratch := { s.scratch with tarjan_mark := tmk, tarjan_reach := trc } }
  simpa [s'] using c0_load_full_score (s := s') hi hmF

private theorem fid_hdrTailWords_set_wsort (c : FullCfg) (s : FullState)
    (ws : List (BitVec 32)) :
    Full.hdrTailWords c { s with scratch := { s.scratch with wsort := ws } } =
      Full.hdrTailWords c s := rfl
private theorem fid_hdrTailWords_set_score (c : FullCfg) (s : FullState)
    (sc : List (BitVec 64)) :
    Full.hdrTailWords c { s with scratch := { s.scratch with score := sc } } =
      Full.hdrTailWords c s := rfl
private theorem fid_fullScrByteArrs_set_wsort (c : FullCfg) (s : FullState)
    (ws : List (BitVec 32)) :
    FullScrByteArrs c { s.scratch with wsort := ws } = FullScrByteArrs c s.scratch := rfl
private theorem fid_fullScrU32A_set_wsort (c : FullCfg) (s : FullState)
    (ws : List (BitVec 32)) :
    FullScrU32A c { s.scratch with wsort := ws } = FullScrU32A c s.scratch := rfl
private theorem fid_fullScrMetaArrs_set_wsort (c : FullCfg) (s : FullState)
    (ws : List (BitVec 32)) :
    FullScrMetaArrs c { s.scratch with wsort := ws } = FullScrMetaArrs c s.scratch := rfl
private theorem fid_fullScrDynArrs_set_wsort (c : FullCfg) (s : FullState)
    (ws : List (BitVec 32)) :
    FullScrDynArrs c { s.scratch with wsort := ws } = FullScrDynArrs c s.scratch := rfl
private theorem fid_fullScrByteArrs_set_score (c : FullCfg) (s : FullState)
    (sc : List (BitVec 64)) :
    FullScrByteArrs c { s.scratch with score := sc } = FullScrByteArrs c s.scratch := rfl
private theorem fid_fullScrU32A_set_score (c : FullCfg) (s : FullState)
    (sc : List (BitVec 64)) :
    FullScrU32A c { s.scratch with score := sc } = FullScrU32A c s.scratch := rfl
private theorem fid_fullScrDynArrs_set_score (c : FullCfg) (s : FullState)
    (sc : List (BitVec 64)) :
    FullScrDynArrs c { s.scratch with score := sc } = FullScrDynArrs c s.scratch := rfl

@[scoped c0_store] theorem store_fidre_score {c : FullCfg} {s : FullState}
    {wl wr : FidArr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : Nat} (v : BitVec 64)
    (hi : i < s.scratch.score.length) (hm : (FidReorderMem c s wl wr ⋆ R) m) :
    storeOk m i64 (c.pScore + BitVec.ofNat 64 (8 * i)) ∧
      (FidReorderMem c { s with scratch := { s.scratch with score := s.scratch.score.set i v } }
        wl wr ⋆ R) (storeMem m i64 (c.pScore + BitVec.ofNat 64 (8 * i)) v) := by
  unfold FidReorderMem FullScrMetaArrs at hm ⊢
  rw [fid_hdrTailWords_set_score, fid_fullScrByteArrs_set_score, fid_fullScrU32A_set_score,
    fid_fullScrDynArrs_set_score]
  dsimp only
  have hm' : (array64 c.pScore s.scratch.score ⋆
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
      array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆ FullCoreArrays c s.core ⋆
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

@[scoped c0_store] theorem c0_store_fidre_score {c : FullCfg} {s : FullState}
    {wl wr : FidArr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64} (v : BitVec 64)
    (hi : i.toNat < s.scratch.score.length) (hm : (FidReorderMem c s wl wr ⋆ R) m) :
    storeOk m i64 (c.pScore + i * 8) ∧
      (FidReorderMem c
        { s with scratch := { s.scratch with score := s.scratch.score.set i.toNat v } }
        wl wr ⋆ R) (storeMem m i64 (c.pScore + i * 8) v) := by
  rw [fid_bv64_mul8_eq]; exact store_fidre_score v hi hm

@[scoped c0_store] theorem store_fidre_wsort {c : FullCfg} {s : FullState}
    {wl wr : FidArr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : Nat} (v : BitVec 32)
    (hi : i < s.scratch.wsort.length) (hm : (FidReorderMem c s wl wr ⋆ R) m) :
    storeOk m i32 (c.pWsort + BitVec.ofNat 64 (4 * i)) ∧
      (FidReorderMem c { s with scratch := { s.scratch with wsort := s.scratch.wsort.set i v } }
        wl wr ⋆ R) (storeMem m i32 (c.pWsort + BitVec.ofNat 64 (4 * i)) v) := by
  unfold FidReorderMem at hm ⊢
  rw [fid_hdrTailWords_set_wsort, fid_fullScrByteArrs_set_wsort, fid_fullScrU32A_set_wsort,
    fid_fullScrMetaArrs_set_wsort, fid_fullScrDynArrs_set_wsort]
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

@[scoped c0_store] theorem c0_store_fidre_wsort {c : FullCfg} {s : FullState}
    {wl wr : FidArr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64} (v : BitVec 32)
    (hi : i.toNat < s.scratch.wsort.length) (hm : (FidReorderMem c s wl wr ⋆ R) m) :
    storeOk m i32 (c.pWsort + i * 4) ∧
      (FidReorderMem c
        { s with scratch := { s.scratch with wsort := s.scratch.wsort.set i.toNat v } }
        wl wr ⋆ R) (storeMem m i32 (c.pWsort + i * 4) v) := by
  rw [fid_bv64_mul4_eq]; exact store_fidre_wsort v hi hm

@[scoped c0_store] theorem store_fidre_wsort0 {c : FullCfg} {s : FullState}
    {wl wr : FidArr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32)
    (hi : 0 < s.scratch.wsort.length) (hm : (FidReorderMem c s wl wr ⋆ R) m) :
    storeOk m i32 c.pWsort ∧
      (FidReorderMem c { s with scratch := { s.scratch with wsort := s.scratch.wsort.set 0 v } }
        wl wr ⋆ R) (storeMem m i32 c.pWsort v) := by
  simpa using store_fidre_wsort v hi hm

@[scoped c0_load] theorem load_fidre_wl {c : FullCfg} {s : FullState}
    {wl wr : FidArr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : Nat}
    (hi : i < c.max_vars) (hm : (FidReorderMem c s wl wr ⋆ R) m) :
    loadVal m i64 (c.pTarjanMark + BitVec.ofNat 64 (8 * i)) =
      some (wl.1[i]'(by rw [wl.2]; exact hi)) := by
  unfold FidReorderMem at hm
  have hi' : i < wl.1.length := by rw [wl.2]; exact hi
  exact loadVal_array64 (R := _) hi' (by ecancel)

@[scoped c0_load] theorem c0_load_fidre_wl {c : FullCfg} {s : FullState}
    {wl wr : FidArr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hi : i.toNat < c.max_vars) (hm : (FidReorderMem c s wl wr ⋆ R) m) :
    loadVal m i64 (c.pTarjanMark + i * 8) =
      some (wl.1[i.toNat]'(by rw [wl.2]; exact hi)) := by
  rw [fid_bv64_mul8_eq]; exact load_fidre_wl hi hm

@[scoped c0_load] theorem load_fidre_wl0 {c : FullCfg} {s : FullState}
    {wl wr : FidArr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hi : 0 < c.max_vars) (hm : (FidReorderMem c s wl wr ⋆ R) m) :
    loadVal m i64 c.pTarjanMark = some (wl.1[0]'(by rw [wl.2]; exact hi)) := by
  simpa using load_fidre_wl hi hm

@[scoped c0_store] theorem store_fidre_wl {c : FullCfg} {s : FullState}
    {wl wr : FidArr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : Nat} (v : BitVec 64)
    (hi : i < c.max_vars) (hm : (FidReorderMem c s wl wr ⋆ R) m) :
    storeOk m i64 (c.pTarjanMark + BitVec.ofNat 64 (8 * i)) ∧
      (FidReorderMem c s ⟨wl.1.set i v, by simp [wl.2]⟩ wr ⋆ R)
        (storeMem m i64 (c.pTarjanMark + BitVec.ofNat 64 (8 * i)) v) := by
  unfold FidReorderMem at hm ⊢
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

@[scoped c0_store] theorem c0_store_fidre_wl {c : FullCfg} {s : FullState}
    {wl wr : FidArr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64} (v : BitVec 64)
    (hi : i.toNat < c.max_vars) (hm : (FidReorderMem c s wl wr ⋆ R) m) :
    storeOk m i64 (c.pTarjanMark + i * 8) ∧
      (FidReorderMem c s ⟨wl.1.set i.toNat v, by simp [wl.2]⟩ wr ⋆ R)
        (storeMem m i64 (c.pTarjanMark + i * 8) v) := by
  rw [fid_bv64_mul8_eq]; exact store_fidre_wl v hi hm

@[scoped c0_store] theorem store_fidre_wl0 {c : FullCfg} {s : FullState}
    {wl wr : FidArr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 64)
    (hi : 0 < c.max_vars) (hm : (FidReorderMem c s wl wr ⋆ R) m) :
    storeOk m i64 c.pTarjanMark ∧
      (FidReorderMem c s ⟨wl.1.set 0 v, by simp [wl.2]⟩ wr ⋆ R)
        (storeMem m i64 c.pTarjanMark v) := by
  simpa using store_fidre_wl v hi hm

@[scoped c0_load] theorem load_fidre_wr {c : FullCfg} {s : FullState}
    {wl wr : FidArr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : Nat}
    (hi : i < c.max_vars) (hm : (FidReorderMem c s wl wr ⋆ R) m) :
    loadVal m i64 (c.pTarjanReach + BitVec.ofNat 64 (8 * i)) =
      some (wr.1[i]'(by rw [wr.2]; exact hi)) := by
  unfold FidReorderMem at hm
  have hi' : i < wr.1.length := by rw [wr.2]; exact hi
  exact loadVal_array64 (R := _) hi' (by ecancel)

@[scoped c0_load] theorem c0_load_fidre_wr {c : FullCfg} {s : FullState}
    {wl wr : FidArr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64}
    (hi : i.toNat < c.max_vars) (hm : (FidReorderMem c s wl wr ⋆ R) m) :
    loadVal m i64 (c.pTarjanReach + i * 8) =
      some (wr.1[i.toNat]'(by rw [wr.2]; exact hi)) := by
  rw [fid_bv64_mul8_eq]; exact load_fidre_wr hi hm

@[scoped c0_load] theorem load_fidre_wr0 {c : FullCfg} {s : FullState}
    {wl wr : FidArr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64}
    (hi : 0 < c.max_vars) (hm : (FidReorderMem c s wl wr ⋆ R) m) :
    loadVal m i64 c.pTarjanReach = some (wr.1[0]'(by rw [wr.2]; exact hi)) := by
  simpa using load_fidre_wr hi hm

@[scoped c0_store] theorem store_fidre_wr {c : FullCfg} {s : FullState}
    {wl wr : FidArr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : Nat} (v : BitVec 64)
    (hi : i < c.max_vars) (hm : (FidReorderMem c s wl wr ⋆ R) m) :
    storeOk m i64 (c.pTarjanReach + BitVec.ofNat 64 (8 * i)) ∧
      (FidReorderMem c s wl ⟨wr.1.set i v, by simp [wr.2]⟩ ⋆ R)
        (storeMem m i64 (c.pTarjanReach + BitVec.ofNat 64 (8 * i)) v) := by
  unfold FidReorderMem at hm ⊢
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

@[scoped c0_store] theorem c0_store_fidre_wr {c : FullCfg} {s : FullState}
    {wl wr : FidArr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {i : BitVec 64} (v : BitVec 64)
    (hi : i.toNat < c.max_vars) (hm : (FidReorderMem c s wl wr ⋆ R) m) :
    storeOk m i64 (c.pTarjanReach + i * 8) ∧
      (FidReorderMem c s wl ⟨wr.1.set i.toNat v, by simp [wr.2]⟩ ⋆ R)
        (storeMem m i64 (c.pTarjanReach + i * 8) v) := by
  rw [fid_bv64_mul8_eq]; exact store_fidre_wr v hi hm

@[scoped c0_store] theorem store_fidre_wr0 {c : FullCfg} {s : FullState}
    {wl wr : FidArr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 64)
    (hi : 0 < c.max_vars) (hm : (FidReorderMem c s wl wr ⋆ R) m) :
    storeOk m i64 c.pTarjanReach ∧
      (FidReorderMem c s wl ⟨wr.1.set 0 v, by simp [wr.2]⟩ ⋆ R)
        (storeMem m i64 c.pTarjanReach v) := by
  simpa using store_fidre_wr v hi hm

end FidReorderTactics

/-! ## 2. Pure & Arithmetic Helpers -/

private theorem fidWsortBounded_mono {ws : List (BitVec 32)} {n1 n2 cv : Nat}
    (hle : n1 ≤ n2) (h : FidWsortBounded ws n2 cv) : FidWsortBounded ws n1 cv :=
      fun i hi => h i (by omega)

private theorem fidWsortBounded_set {ws : List (BitVec 32)} {n cv idx : Nat}
    (v : BitVec 32) (h : FidWsortBounded ws n cv) (hv : v.toNat < cv) :
    FidWsortBounded (ws.set idx v) n cv := by
  intro i hi; by_cases he : i = idx
  · subst he; by_cases hl : i < ws.length
    · rw [List.getElem?_set_self hl, Option.getD_some]; exact hv
    · rw [List.getElem?_eq_none (by simp; omega), Option.getD_none]; exact Nat.zero_lt_of_lt hv
  · rw [List.getElem?_set_ne (Ne.symm he)]; exact h i hi

private theorem fidWsortBounded_push {ws : List (BitVec 32)} {n cv : Nat} {v : BitVec 32}
    (h : FidWsortBounded ws n cv) (hn : n < ws.length) (hv : v.toNat < cv) :
    FidWsortBounded (ws.set n v) (n + 1) cv := by
  intro i hi; by_cases he : i = n
  · subst he; rw [List.getElem?_set_self hn, Option.getD_some]; exact hv
  · rw [List.getElem?_set_ne (Ne.symm he)]; exact h i (by omega)

private theorem fidWsortBounded_get {ws : List (BitVec 32)} {n cv i : Nat}
    (h : FidWsortBounded ws n cv) (hi : i < n) (hl : i < ws.length) : (ws[i]'hl).toNat < cv := by
  have h1 := h i hi; rw [List.getElem?_eq_getElem hl, Option.getD_some] at h1; exact h1

private theorem fidWsortBounded_swap {ws : List (BitVec 32)} {n cv i j : Nat}
    {vi vj : BitVec 32} (hwb : FidWsortBounded ws n cv)
    (hvi : vi.toNat < cv) (hvj : vj.toNat < cv) :
    FidWsortBounded ((ws.set i vi).set j vj) n cv :=
  fidWsortBounded_set _ (fidWsortBounded_set _ hwb hvi) hvj

private theorem fidWsortBounded_lift {ws ws' : List (BitVec 32)} {k n cv : Nat}
    (hwb : FidWsortBounded ws n cv) (hwb' : FidWsortBounded ws' k cv)
    (hpres : ∀ j, k ≤ j → ws'[j]? = ws[j]?) : FidWsortBounded ws' n cv := by
  intro j hj; by_cases hjk : j < k
  · exact hwb' j hjk
  · rw [hpres j (Nat.le_of_not_lt hjk)]; exact hwb j hj

private theorem fidWsortBounded_shrink {ws : List (BitVec 32)} {k n cv : Nat}
    (hwb : FidWsortBounded ws n cv) (hk : k ≤ n) : FidWsortBounded ws k cv :=
  fun j hj => hwb j (Nat.lt_of_lt_of_le hj hk)

private def FidSiftWsortEq (s s1 : FullState) : Prop :=
  s1 = { s with scratch := { s.scratch with wsort := s1.scratch.wsort } }

private theorem fidSiftWsortEq_refl (s : FullState) : FidSiftWsortEq s s := by
  rcases s with ⟨_, ⟨_⟩⟩; rfl
private theorem fidSiftWsortEq_qstamp {s s1 : FullState} (h : FidSiftWsortEq s s1) :
    s1.scratch.q_stamp = s.scratch.q_stamp := by unfold FidSiftWsortEq at h; rw [h]
private theorem fidSiftWsortEq_curVars {s s1 : FullState} (h : FidSiftWsortEq s s1) :
    s1.core.cur_vars = s.core.cur_vars := by unfold FidSiftWsortEq at h; rw [h]
private theorem fidSiftWsortEq_flags {s s1 : FullState} (h : FidSiftWsortEq s s1) :
    s1.core.flags.length = s.core.flags.length := by unfold FidSiftWsortEq at h; rw [h]
private theorem fidSiftWsortEq_set {s s1 : FullState} (h : FidSiftWsortEq s s1)
    (ws : List (BitVec 32)) :
    FidSiftWsortEq s { s1 with scratch := { s1.scratch with wsort := ws } } := by
  unfold FidSiftWsortEq at h ⊢; rw [h]

private theorem fidSiftWsortEq_lengthsOk {c : FullCfg} {s s1 : FullState}
    (hlen : s.LengthsOk c) (hs1 : FidSiftWsortEq s s1)
    (hwl : s1.scratch.wsort.length = s.scratch.wsort.length) : s1.LengthsOk c := by
  unfold FidSiftWsortEq at hs1; rw [hs1]
  exact ⟨hlen.core_ok, { hlen.scratch_ok with wsort_len := hwl.trans hlen.scratch_ok.wsort_len }⟩

private theorem fid_zext64_32_lt_of_lt {x : BitVec 32} {n : Nat} (h : x.toNat < n) :
    (BitVec.setWidth 64 x).toNat < n := by
  have hz : (BitVec.setWidth 64 x).toNat = x.toNat := by bv_omega
  omega

private theorem fid_child_nat_of_hc {root n : BitVec 64} (hroot : root.toNat < 2 ^ 29)
    (h : ¬n.toNat ≤ ((root <<< (1 : Nat)).toNat + (1 : BitVec 64).toNat) % 2 ^ 64) :
    ((root <<< 1) + 1#64).toNat < n.toNat := by
  have hsh : ((root <<< (1 : Nat)).toNat + (1 : BitVec 64).toNat) % 2 ^ 64 =
      2 * root.toNat + 1 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one]; bv_omega
  have h2 : ((root <<< 1) + 1#64).toNat = 2 * root.toNat + 1 := by bv_omega
  omega

private theorem fid_ushr1_nat_lt {x : BitVec 64} {n : Nat} (h : x.toNat < 2 * n) :
    (x >>> (1 : Nat)).toNat < n := by
  have : (x >>> (1 : Nat)).toNat = x.toNat / 2 := by
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega
private theorem fid_ushr1_bv_lt {x : BitVec 64} {n : Nat} (h : x.toNat < 2 * n) :
    (x >>> (1 : BitVec 64)).toNat < n := fid_ushr1_nat_lt h
private theorem fid_zext32_ushr1_lt {x : BitVec 32} {n : Nat}
    (h : (BitVec.setWidth 64 x).toNat < 2 * n) :
    ((BitVec.setWidth 64 x) >>> (1 : BitVec 64)).toNat < n := fid_ushr1_bv_lt h
private theorem fid_zext32_ushr1_nat_lt {x : BitVec 32} {n : Nat}
    (h : (BitVec.setWidth 64 x).toNat < 2 * n) :
    ((BitVec.setWidth 64 x) >>> (1 : Nat)).toNat < n := fid_ushr1_nat_lt h
private theorem fid_shl1_nat_lt {x : BitVec 64} {n : Nat} (h : x.toNat < 2 * n) (hn : n < 2 ^ 29) :
    (x <<< (1 : Nat)).toNat < 4 * n := by
  have h1 : (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
    simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one,
      Nat.mod_eq_of_lt (by omega : x.toNat * 2 ^ 1 < 2 ^ 64)]; omega
  omega
private theorem fid_shl1_bv_lt {x : BitVec 64} {n : Nat} (h : x.toNat < 2 * n) (hn : n < 2 ^ 29) :
    (x <<< (1 : BitVec 64)).toNat < 4 * n := fid_shl1_nat_lt h hn
private theorem fid_shl1_add1_nat_lt {x : BitVec 64} {n : Nat} (h : x.toNat < 2 * n)
    (hn : n < 2 ^ 29) : ((x <<< (1 : Nat)) + 1#64).toNat < 4 * n := by
  have h1 : (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
    simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one,
      Nat.mod_eq_of_lt (by omega : x.toNat * 2 ^ 1 < 2 ^ 64)]; omega
  have h2 : ((x <<< (1 : Nat)) + 1#64).toNat = 2 * x.toNat + 1 := by
    rw [BitVec.toNat_add, h1, show (1#64 : BitVec 64).toNat = 1 from rfl,
      Nat.mod_eq_of_lt (by omega)]
  omega
private theorem fid_shl1_add1_bv_lt {x : BitVec 64} {n : Nat} (h : x.toNat < 2 * n)
    (hn : n < 2 ^ 29) : ((x <<< (1 : BitVec 64)) + 1#64).toNat < 4 * n :=
  fid_shl1_add1_nat_lt h hn
private theorem fid_shl1_mul2_nat_lt {x : BitVec 64} {m : Nat}
    (h : x.toNat < m) (hm : m < 2 * 2 ^ 28) : (x <<< (1 : Nat)).toNat < 2 * m := by
  have h64 : x.toNat * 2 < 2 ^ 64 := lt_trans (by omega : x.toNat * 2 < 2 ^ 30) (by decide)
  have h1 : (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
    simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one, Nat.mod_eq_of_lt h64]; omega
  omega
private theorem fid_shl1_mul2_bv_lt {x : BitVec 64} {m : Nat}
    (h : x.toNat < m) (hm : m < 2 * 2 ^ 28) : (x <<< (1 : BitVec 64)).toNat < 2 * m :=
  fid_shl1_mul2_nat_lt h hm
private theorem fid_zext32_bv32_ushr1_lt {x : BitVec 32} {n : Nat}
    (h : (BitVec.setWidth 64 x).toNat < 2 * n) :
    (BitVec.setWidth 64 (x >>> (1 : Nat))).toNat < n := by
  have hz1 : (BitVec.setWidth 64 x).toNat = x.toNat := by bv_omega
  have hz2 : (BitVec.setWidth 64 (x >>> (1 : Nat))).toNat = (x >>> (1 : Nat)).toNat := by bv_omega
  have hdiv : (x >>> (1 : Nat)).toNat = x.toNat / 2 := by
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega
private theorem fid_zext32_bv32_ushr1_bv_lt {x : BitVec 32} {n : Nat}
    (h : (BitVec.setWidth 64 x).toNat < 2 * n) :
    (BitVec.setWidth 64 (x >>> (1 : BitVec 32))).toNat < n := fid_zext32_bv32_ushr1_lt h

private theorem fid_bv64_lt_of_mod_lt {v : BitVec 64} {m : Nat} (hm : m < 2 ^ 30)
    (h : v.toNat < m % 2 ^ 64) : v.toNat < m := by
  rw [Nat.mod_eq_of_lt (lt_trans hm (by decide))] at h; exact h
private theorem fid_bv64_lt_two_mul_mod {x : BitVec 64} {m : Nat} (hm : m < 2 ^ 29)
    (h : x.toNat < 2 * (m % 2 ^ 64) % 2 ^ 64) : x.toNat < 2 * m := by
  have hm64 : m < 2 ^ 64 := lt_trans hm (by decide)
  have h2m64 : 2 * m < 2 ^ 64 := lt_trans (Nat.mul_lt_mul_of_pos_left hm (by decide)) (by decide)
  rw [Nat.mod_eq_of_lt hm64, Nat.mod_eq_of_lt h2m64] at h; exact h
private theorem fid_bv64_off3_add_toNat {off j : BitVec 64} (ho : off.toNat < 2 ^ 29)
    (hj : j.toNat < 2 ^ 29) :
    ((off + 3#64) + j).toNat = off.toNat + 3 + j.toNat ∧
    (off.toNat + 3 % 2 ^ 64 + j.toNat) % 2 ^ 64 = off.toNat + 3 + j.toNat ∧
    ((off.toNat + 3 % 2 ^ 64) % 2 ^ 64 + j.toNat) % 2 ^ 64 = off.toNat + 3 + j.toNat := by
  have ho64 : off.toNat + 3 < 2 ^ 64 := lt_trans (by omega : off.toNat + 3 < 2 ^ 30) (by decide)
  have hoj64 : off.toNat + 3 + j.toNat < 2 ^ 64 :=
    lt_trans (by omega : off.toNat + 3 + j.toNat < 2 ^ 31) (by decide)
  have h1 : ((off + 3#64) + j).toNat = off.toNat + 3 + j.toNat := by bv_omega
  have hm3 : (3 : Nat) % 2 ^ 64 = 3 := by decide
  rw [hm3, Nat.mod_eq_of_lt ho64, Nat.mod_eq_of_lt hoj64]; exact ⟨h1, rfl, rfl⟩
private theorem fid_arena_lit_2cv {arena : List (BitVec 32)} {i j cv : Nat}
    (hij : i = j) (hcv : cv < 2 ^ 29) (hi : i < arena.length) (hj : j < arena.length)
    (hc : (arena[j]'hj).toNat < 2 * (cv % 2 ^ 64) % 2 ^ 64) :
    (BitVec.setWidth 64 (arena[i]'hi)).toNat < 2 * cv := by
  subst hij
  have h32 : (arena[i]'hi).toNat < 2 ^ 64 := lt_trans (BitVec.isLt _) (by decide)
  have hz : (BitVec.setWidth 64 (arena[i]'hi)).toNat = (arena[i]'hi).toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt h32]
  exact hz ▸ fid_bv64_lt_two_mul_mod hcv (x := BitVec.setWidth 64 (arena[i]'hi)) (hz ▸ hc)

private theorem fid_off_bounds {arena_len arena_arr_len : Nat} {off n3 : BitVec 64}
    (har29 : arena_len < 2 ^ 29) (har_le : arena_len ≤ arena_arr_len)
    (h1 : off.toNat < arena_len % 2 ^ 64)
    (h2 : ¬arena_len % 2 ^ 64 < (off.toNat + n3.toNat) % 2 ^ 64) (hn3 : n3.toNat = 3) :
    off.toNat + 3 ≤ arena_len ∧ off.toNat < 2 ^ 29 ∧ (off + 2#64).toNat = off.toNat + 2 ∧
    off.toNat < arena_arr_len ∧ (off + 2#64).toNat < arena_arr_len := by
  have har64 : arena_len < 2 ^ 64 := lt_trans har29 (by decide)
  rw [Nat.mod_eq_of_lt har64] at h1 h2; rw [hn3] at h2
  have ho29 : off.toNat < 2 ^ 29 := Nat.lt_trans h1 har29
  rw [Nat.mod_eq_of_lt (lt_trans (by omega : off.toNat + 3 < 2 ^ 30) (by decide))] at h2
  have hoff3 : off.toNat + 3 ≤ arena_len := Nat.le_of_not_lt h2
  have ho2 : (off + 2#64).toNat = off.toNat + 2 := by
    rw [BitVec.toNat_add, show (2#64 : BitVec 64).toNat = 2 from rfl,
      Nat.mod_eq_of_lt (lt_trans (by omega : off.toNat + 2 < 2 ^ 30) (by decide))]
  exact ⟨hoff3, ho29, ho2, Nat.lt_of_lt_of_le h1 har_le,
    ho2 ▸ Nat.lt_of_lt_of_le (by omega) (Nat.le_trans hoff3 har_le)⟩

private theorem fid_sz_off3_le {arena : List (BitVec 32)} {arena_len : Nat} {off n2 n3 : BitVec 64}
    (hoff3 : off.toNat + 3 ≤ arena_len) (har29 : arena_len < 2 ^ 29)
    {hi1 : (off.toNat + n2.toNat) % 2 ^ 64 < arena.length}
    (hi2 : (off + 2#64).toNat < arena.length) (ho2 : (off + 2#64).toNat = off.toNat + 2)
    (hle : (arena[(off.toNat + n2.toNat) % 2 ^ 64]'hi1).toNat ≤
      (2 ^ 64 - (off.toNat + n3.toNat) % 2 ^ 64 + arena_len) % 2 ^ 64)
    (hn2 : n2.toNat = 2) (hn3 : n3.toNat = 3) :
    off.toNat + 3 + (BitVec.setWidth 64 (arena[(off + 2#64).toNat]'hi2)).toNat ≤ arena_len ∧
    (BitVec.setWidth 64 (arena[(off + 2#64).toNat]'hi2)).toNat < 2 ^ 29 := by
  have ho2_64 : off.toNat + 2 < 2 ^ 64 := lt_trans (by omega : off.toNat + 2 < 2 ^ 30) (by decide)
  have ho3_64 : off.toNat + 3 < 2 ^ 64 := lt_trans (by omega : off.toNat + 3 < 2 ^ 30) (by decide)
  have hi_eq : (off.toNat + n2.toNat) % 2 ^ 64 = (off + 2#64).toNat := by
    rw [hn2, ho2, Nat.mod_eq_of_lt ho2_64]
  have helem : arena[(off.toNat + n2.toNat) % 2 ^ 64]'hi1 = arena[(off + 2#64).toNat]'hi2 := by
    clear hle; revert hi1; rw [hi_eq]; intro _; rfl
  have hrem29 : arena_len - (off.toNat + 3) < 2 ^ 29 := by omega
  have hrem : arena_len - (off.toNat + 3) < 2 ^ 64 := lt_trans hrem29 (by decide)
  have hrhs : (2 ^ 64 - (off.toNat + n3.toNat) % 2 ^ 64 + arena_len) % 2 ^ 64 =
      arena_len - (off.toNat + 3) := by
    rw [hn3, Nat.mod_eq_of_lt ho3_64,
      show 2 ^ 64 - (off.toNat + 3) + arena_len = (arena_len - (off.toNat + 3)) + 2 ^ 64 by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt hrem]
  rw [helem, hrhs] at hle
  have h32 : (arena[(off + 2#64).toNat]'hi2).toNat < 2 ^ 64 := lt_trans (BitVec.isLt _) (by decide)
  have hz : (BitVec.setWidth 64 (arena[(off + 2#64).toNat]'hi2)).toNat =
      (arena[(off + 2#64).toNat]'hi2).toNat := by rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt h32]
  rw [hz]; exact ⟨by omega, by omega⟩

private theorem fid_arena_k_lt {arena : List (BitVec 32)} {off k n2 : BitVec 64}
    (ho2 : (off + 2#64).toNat = off.toNat + 2) (hoff : off.toNat < 2 ^ 29)
    {hi1 : (off.toNat + n2.toNat) % 2 ^ 64 < arena.length}
    (hi2 : (off + 2#64).toNat < arena.length)
    (hc : k.toNat < (arena[(off.toNat + n2.toNat) % 2 ^ 64]'hi1).toNat) (hn2 : n2.toNat = 2) :
    k.toNat < (BitVec.setWidth 64 (arena[(off + 2#64).toNat]'hi2)).toNat := by
  have ho2_64 : off.toNat + 2 < 2 ^ 64 := lt_trans (by omega : off.toNat + 2 < 2 ^ 30) (by decide)
  have heq : (off.toNat + n2.toNat) % 2 ^ 64 = (off + 2#64).toNat := by
    rw [hn2, ho2, Nat.mod_eq_of_lt ho2_64]
  have helem : arena[(off.toNat + n2.toNat) % 2 ^ 64]'hi1 = arena[(off + 2#64).toNat]'hi2 := by
    clear hc; revert hi1; rw [heq]; intro _; rfl
  have h32 : (arena[(off + 2#64).toNat]'hi2).toNat < 2 ^ 64 := lt_trans (BitVec.isLt _) (by decide)
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt h32, ← helem]; exact hc

private theorem fid_bv64_lt_shl1_ofNat {v : BitVec 64} {m : Nat} (hm : m < 2 ^ 29)
    (h : v.toNat < (BitVec.ofNat 64 m <<< (1 : Nat)).toNat) : v.toNat < 2 * m := by
  have hm64 : m < 2 ^ 64 := lt_trans hm (by decide)
  have h1 : (BitVec.ofNat 64 m <<< (1 : Nat)).toNat = 2 * m := by
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.pow_one]
    rw [Nat.mod_eq_of_lt hm64, Nat.mod_eq_of_lt (by omega)]; omega
  omega
private theorem fid_bv64_add1_toNat {x : BitVec 64} {m : Nat} (hm : m < 2 ^ 30) (hx : x.toNat < m) :
    (x + 1#64).toNat = x.toNat + 1 ∧ (x + 1#64).toNat ≤ m ∧ m - (x + 1#64).toNat < m - x.toNat := by
  have : x.toNat < 2 ^ 64 - 1 := lt_trans hx (lt_trans hm (by decide)); bv_omega
private theorem fid_bv64_add1_sub_lt {x : BitVec 64} {m : Nat} (hm : m < 2 ^ 30)
    (hx : x.toNat < m) : m - (x + 1#64).toNat < m - x.toNat := (fid_bv64_add1_toNat hm hx).2.2
private theorem fid_bv64_add2_sub_lt {x : BitVec 64} {m : Nat} (hm : m < 2 ^ 30)
    (hx : x.toNat < m) : m - (x + 2#64).toNat < m - x.toNat := by
  have : x.toNat < 2 ^ 64 - 2 := lt_trans hx (lt_trans hm (by decide)); bv_omega
private theorem fid_bv64_sub1_toNat {x : BitVec 64} {m : Nat} (hm : m < 2 ^ 30)
    (hx_le : x.toNat ≤ m) (hx_pos : 0 < x.toNat) :
    (x - 1#64).toNat = x.toNat - 1 ∧ (x - 1#64).toNat < x.toNat ∧
    (x - 1#64).toNat ≤ m ∧ (x - 1#64).toNat < m := by
  have : x.toNat < 2 ^ 64 := lt_of_le_of_lt hx_le (lt_trans hm (by decide)); bv_omega
private theorem fid_bv64_ushr1_le {x : BitVec 64} {m : Nat} (hx : x.toNat ≤ m) :
    (x >>> 1#64).toNat ≤ m := by
  have h1 : (x >>> 1#64).toNat = x.toNat / 2 := by
    change (x >>> (1 : Nat)).toNat = x.toNat / 2
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega
private theorem fid_bv64_pos_of_ne_zero {x : BitVec 64} (h : x ≠ 0#64) : 0 < x.toNat := by bv_omega

private theorem fid_we_le_wlen {ws wc : BitVec 32} {wlen : Nat}
    (hwl : wlen < 2 ^ 29) (hws : ws.toNat < wlen % 2 ^ 64)
    (hwc : wc.toNat ≤ (2 ^ 64 - ws.toNat + wlen) % 2 ^ 64) :
    ws.toNat ≤ wlen ∧ ((BitVec.setWidth 64 ws) + (BitVec.setWidth 64 wc)).toNat ≤ wlen := by
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

private theorem fid_wp_call_spec {Γ : Env} {rs as bs : List Ty} {Q : Post rs} {X : XPost}
    {f : Sym} {args : Tup (Arg Val) as} {k : Tup Val bs → Expr Val Cont rs} {m : Mem 64}
    {spec : Spec as bs} (hEnv : EnvSpec Γ f spec)
    (hSpec : spec (vals args) m (fun r m' => wp Γ Q X (k r) m') X) :
    wp Γ Q X (.call f args k) m :=
  ⟨fun r m' => wp Γ Q X (k r) m', X, hEnv _ _ _ _ hSpec, fun _ _ h => h, fun _ _ _ _ h => h⟩

/-! ## 3. `full_reorder_sift_fid_wp` -/

section FidReorderSiftProof

open scoped FidReorderTactics

/-- Parametric `Func.wp` proof for `full_reorder_sift_fid` (`fidReorderSiftSpec`). -/
theorem full_reorder_sift_fid_wp (Γ : Env) :
    ∀ a m Q X, fidReorderSiftSpec a m Q X → Func.wp Γ full_reorder_sift_fid_body a m Q X := by
  rintro ⟨h, start, n, ⟨⟩⟩ m Q X ⟨c, s, wl, wr, R, rfl, hlen, hwb, hm, hQ⟩
  have hQ' : ∀ (s1 : FullState) (m1 : Mem 64),
      FidSiftWsortEq s s1 → s1.scratch.wsort.length = s.scratch.wsort.length →
      FidWsortBounded s1.scratch.wsort n.toNat s.core.cur_vars →
      (∀ j, n.toNat ≤ j → s1.scratch.wsort[j]? = s.scratch.wsort[j]?) →
      (FidReorderMem c s1 wl wr ⋆ R) m1 → Q () m1 :=
    fun s1 m1 hs1_eq hlen1 hwb1 hpres1 hm1 =>
      hQ s1.scratch.wsort m1 hlen1 hwb1 hpres1 (hs1_eq ▸ hm1)
  clear hQ
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hlen.core_ok.cur_vars_le; have hcv_29 : s.core.cur_vars < 2 ^ 29 := by omega
  have hws_len := hlen.scratch_ok.wsort_len; have hqs_len := hlen.scratch_ok.q_stamp_len
  unfold Func.wp full_reorder_sift_fid_body
  c0_hsplit
  · c0_hsteps; exact hQ' s m (fidSiftWsortEq_refl s) rfl hwb (fun _ _ => rfl) hm
  · c0_hsplit
    · c0_hsteps; exact hQ' s m (fidSiftWsortEq_refl s) rfl hwb (fun _ _ => rfl) hm
    · c0_hsplit
      · c0_hsteps; exact hQ' s m (fidSiftWsortEq_refl s) rfl hwb (fun _ _ => rfl) hm
      · have hn_pos : 1 ≤ n.toNat := by bv_omega
        have hst_lt : start.toNat < n.toNat := by bv_omega
        have hn_le : n.toNat ≤ s.core.cur_vars := by omega
        c0_hsteps_nogrp
        refine wp_while_break_state (fun root : BitVec 64 => (root, ()))
          (fun _ m1 => ∃ s1 : FullState,
            FidSiftWsortEq s s1 ∧ s1.scratch.wsort.length = s.scratch.wsort.length ∧
            FidWsortBounded s1.scratch.wsort n.toNat s.core.cur_vars ∧
            (∀ j, n.toNat ≤ j → s1.scratch.wsort[j]? = s.scratch.wsort[j]?) ∧
            (FidReorderMem c s1 wl wr ⋆ R) m1)
          (fun root : BitVec 64 => (root, ())) (fun root => n.toNat - root.toNat)
          (fun root m1 => root.toNat < n.toNat ∧ ∃ s1 : FullState,
            FidSiftWsortEq s s1 ∧ s1.scratch.wsort.length = s.scratch.wsort.length ∧
            FidWsortBounded s1.scratch.wsort n.toNat s.core.cur_vars ∧
            (∀ j, n.toNat ≤ j → s1.scratch.wsort[j]? = s.scratch.wsort[j]?) ∧
            (FidReorderMem c s1 wl wr ⋆ R) m1)
          (fun B _ m1 ⟨s1, hs1_eq, hws1_len, hwb1, hpres1, hm1⟩ => by
            c0_hsteps; exact hQ' s1 m1 hs1_eq hws1_len hwb1 hpres1 hm1)
          (fun B L root m1 hB hL ⟨hroot, s1, hs1_eq, hws1_len, hwb1, hpres1, hm1⟩ => ?_)
          (fun B L _ hL => by
            c0_hsteps
            exact hL start m ⟨hst_lt, s, fidSiftWsortEq_refl s, rfl, hwb, fun _ _ => rfl, hm⟩)
        have hqs1_len : s1.scratch.q_stamp.length = c.max_vars := by
          rw [fidSiftWsortEq_qstamp hs1_eq]; exact hqs_len
        have hchild_eq : ((root <<< 1) + 1#64).toNat = 2 * root.toNat + 1 := by bv_omega
        have hroot_lt_ws : root.toNat < s1.scratch.wsort.length := by omega
        have hbv0_lt : (s1.scratch.wsort[root.toNat]'hroot_lt_ws).toNat < s.core.cur_vars :=
          fidWsortBounded_get hwb1 hroot hroot_lt_ws
        have hbv0_mv :
            (BitVec.setWidth 64 (s1.scratch.wsort[root.toNat]'hroot_lt_ws)).toNat < c.max_vars :=
          fid_zext64_32_lt_of_lt (Nat.lt_of_lt_of_le hbv0_lt hcv_le)
        have hbv0_qs : (BitVec.setWidth 64 (s1.scratch.wsort[root.toNat]'hroot_lt_ws)).toNat <
            s1.scratch.q_stamp.length := hqs1_len ▸ hbv0_mv
        c0_hsplit
        · c0_hsplit
          · c0_hsteps; exact hB root m1 ⟨s1, hs1_eq, hws1_len, hwb1, hpres1, hm1⟩
          · have hch_nat : ((root <<< 1) + 1#64).toNat < n.toNat :=
              fid_child_nat_of_hc (by omega) ‹_›
            have hch_lt_ws : ((root <<< 1) + 1#64).toNat < s1.scratch.wsort.length := by omega
            have hcv0_lt : (s1.scratch.wsort[((root <<< 1) + 1#64).toNat]'hch_lt_ws).toNat <
                s.core.cur_vars := fidWsortBounded_get hwb1 hch_nat hch_lt_ws
            have hcv0_mv : (BitVec.setWidth 64
                (s1.scratch.wsort[((root <<< 1) + 1#64).toNat]'hch_lt_ws)).toNat < c.max_vars :=
              fid_zext64_32_lt_of_lt (Nat.lt_of_lt_of_le hcv0_lt hcv_le)
            have hcv0_qs : (BitVec.setWidth 64
                (s1.scratch.wsort[((root <<< 1) + 1#64).toNat]'hch_lt_ws)).toNat <
                s1.scratch.q_stamp.length := hqs1_len ▸ hcv0_mv
            have hrch_eq : ((root <<< 1) + 1#64 + 1#64).toNat = 2 * root.toNat + 2 := by bv_omega
            c0_hsteps_nogrp
            refine wp_join_group (ts := [i64, i32, i64, i32])
              (fun xs m' => m' = m1 ∧ (xs.1 = root ∨ xs.1 = (root <<< 1) + 1#64) ∧
                xs.1.toNat < n.toNat ∧ xs.2.1.toNat < s.core.cur_vars) ?_ ?_
            · rintro J xs m' ⟨hm_eq, hx_eq, hx_lt, hxv_lt⟩
              subst m'; dsimp only [Blocks.get]; c0_hsteps_nogrp
              refine wp_join_group (ts := [i64, i32])
                (fun ys m'' => m'' = m1 ∧
                  (ys.1 = root ∨ ys.1 = (root <<< 1) + 1#64 ∨ ys.1 = (root <<< 1) + 1#64 + 1#64) ∧
                  ys.1.toNat < n.toNat ∧ ys.2.1.toNat < s.core.cur_vars) ?_ ?_
              · rintro J2 ys m'' ⟨hm_eq', hy_eq, hy_lt, hyv_lt⟩
                subst m''; c0_hsplit
                · c0_hsteps; exact hB _ m1 ⟨s1, hs1_eq, hws1_len, hwb1, hpres1, hm1⟩
                · have hgt : root.toNat < ys.1.toNat := by
                    rcases hy_eq with h1 | h1 | h1
                    · exact absurd h1 (by assumption)
                    · rw [h1, hchild_eq]; omega
                    · rw [h1, hrch_eq]; omega
                  have hys_ws : ys.1.toNat < s1.scratch.wsort.length := by omega
                  have hys_ws' : ys.1.toNat < (s1.scratch.wsort.set root.toNat ys.2.1).length := by
                    simpa using hys_ws
                  c0_hsteps
                  let ws2 := (s1.scratch.wsort.set root.toNat ys.2.1).set ys.1.toNat
                    (s1.scratch.wsort[root.toNat]'hroot_lt_ws)
                  exact hL ys.1 _ (by omega)
                    ⟨hy_lt, { s1 with scratch := { s1.scratch with wsort := ws2 } },
                     fidSiftWsortEq_set hs1_eq _, by simp [ws2, hws1_len],
                     fidWsortBounded_swap hwb1 hyv_lt hbv0_lt,
                     fun j hj => by
                       dsimp only [ws2]; rw [List.getElem?_set_ne (by omega),
                         List.getElem?_set_ne (by omega)]; exact hpres1 j hj,
                     by assumption⟩
              · intro J2 hJ2; c0_hsplit
                · have hrch_nat : ((root <<< 1) + 1#64 + 1#64).toNat < n.toNat := by
                    clear hB hL hQ' hwb1 hpres1 hm1 hbv0_lt hbv0_mv hbv0_qs
                    clear hcv0_lt hcv0_mv hcv0_qs hx_eq hx_lt hxv_lt
                    have hone : (1 : BitVec 64).toNat = 1 := rfl
                    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
                      hone, Nat.shiftLeft_eq, Nat.pow_one, Nat.reducePow, Nat.reduceMod] at *
                    omega
                  have hrch_ws : ((root <<< 1) + 1#64 + 1#64).toNat < s1.scratch.wsort.length := by
                    omega
                  have hrv_lt : (s1.scratch.wsort[((root <<< 1) + 1#64 + 1#64).toNat]'hrch_ws).toNat
                      < s.core.cur_vars := fidWsortBounded_get hwb1 hrch_nat hrch_ws
                  have hrv_mv : (BitVec.setWidth 64
                      (s1.scratch.wsort[((root <<< 1) + 1#64 + 1#64).toNat]'hrch_ws)).toNat <
                      c.max_vars := fid_zext64_32_lt_of_lt (Nat.lt_of_lt_of_le hrv_lt hcv_le)
                  have hrv_qs : (BitVec.setWidth 64
                      (s1.scratch.wsort[((root <<< 1) + 1#64 + 1#64).toNat]'hrch_ws)).toNat <
                      s1.scratch.q_stamp.length := hqs1_len ▸ hrv_mv
                  c0_hsteps_nogrp
                  refine wp_join_group (ts := [i64, i32])
                    (fun zs m'' => m'' = m1 ∧
                      (zs.1 = root ∨ zs.1 = (root <<< 1) + 1#64 ∨
                        zs.1 = (root <<< 1) + 1#64 + 1#64) ∧
                      zs.1.toNat < n.toNat ∧ zs.2.1.toNat < s.core.cur_vars)
                    (fun _ _ m'' ⟨hm_z, hz⟩ => by
                      subst m''; dsimp only [Blocks.get]; c0_hsteps; exact hJ2 _ m1 ⟨rfl, hz⟩)
                    (fun J3 hJ3 => by
                      c0_hsteps_nogrp; all_goals
                        refine hJ3 _ m1 ⟨rfl, ?_, ?_, ?_⟩
                        · first | exact Or.inr (Or.inr rfl) | exact hx_eq.imp_right Or.inl
                        · first | exact hrch_nat | exact hx_lt
                        · first | exact hrv_lt | exact hxv_lt)
                · c0_hsteps; exact hJ2 _ m1 ⟨rfl, hx_eq.imp_right Or.inl, hx_lt, hxv_lt⟩
            · intro J1 hJ1; c0_hsteps_nogrp; all_goals
                refine hJ1 _ m1 ⟨rfl, ?_, ?_, ?_⟩
                · first | exact Or.inl rfl | exact Or.inr rfl
                · first | exact hroot | exact hch_nat
                · first | exact hbv0_lt | exact hcv0_lt
        · exact absurd ‹true = false› (by decide)

end FidReorderSiftProof

/-! ## 4. `full_reorder_queue_fid_wp` (`FullM4Ternary.fullReorderQueueSpec`) -/

section FidReorderQueueProof

open scoped FidReorderTactics FullArenaTactics

private def FidQueuePostOk (c : FullCfg) (s : FullState) (R : Mem 64 → Prop) (m' : Mem 64) : Prop :=
  ∃ s' : FullState,
    s'.core = s.core ∧ s'.LengthsOk c ∧ FullExtScratchPres s s' ∧ (FullMem c s' ⋆ R) m'

private def FidQueueRelinkOk (c : FullCfg) (s0 s1 : FullState) (n : Nat) : Prop :=
  s1.core = s0.core ∧ s1.LengthsOk c ∧ FullExtScratchPres s0 s1 ∧
  FidWsortBounded s1.scratch.wsort n s1.core.cur_vars

private theorem fidQueueRelinkOk_of_reorder {c : FullCfg} {s0 s1 : FullState}
    {wl wr : FidArr64 c.max_vars} {R : Mem 64 → Prop} {m : Mem 64} {n : Nat}
    (hlen0 : s0.LengthsOk c) (hs1 : FidSiftWsortEq s0 s1)
    (hwl : s1.scratch.wsort.length = s0.scratch.wsort.length)
    (hwb : FidWsortBounded s1.scratch.wsort n s0.core.cur_vars)
    (hm : (FidReorderMem c s1 wl wr ⋆ R) m) :
    ∃ s2 : FullState, FidQueueRelinkOk c s0 s2 n ∧ (FullMem c s2 ⋆ R) m := by
  obtain ⟨tmk, trc, htmk, htrc, hmF⟩ := fid_fullMem_of_reorderMem hm
  have hs1' : s1 = { s0 with scratch := { s0.scratch with wsort := s1.scratch.wsort } } := hs1
  refine ⟨{ s1 with scratch := { s1.scratch with tarjan_mark := tmk, tarjan_reach := trc } },
    ⟨by rw [hs1'], ⟨by rw [hs1']; exact hlen0.core_ok,
      { walk_vals_len := by rw [hs1']; exact hlen0.scratch_ok.walk_vals_len
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
        tarjan_mark_len := htmk, tarjan_reach_len := htrc
        score_len := by rw [hs1']; exact hlen0.scratch_ok.score_len
        sim_sig_len := by rw [hs1']; exact hlen0.scratch_ok.sim_sig_len
        glue_used_len := by rw [hs1']; exact hlen0.scratch_ok.glue_used_len
        last_learned_len := by rw [hs1']; exact hlen0.scratch_ok.last_learned_len
        delayed_len_arr := by rw [hs1']; exact hlen0.scratch_ok.delayed_len_arr
        red_refs_len := by rw [hs1']; exact hlen0.scratch_ok.red_refs_len
        extend_stk_len := by rw [hs1']; exact hlen0.scratch_ok.extend_stk_len
        scratch_buf_len := by rw [hs1']; exact hlen0.scratch_ok.scratch_buf_len }⟩,
     ⟨by rw [hs1'], by rw [hs1']⟩, by rw [hs1']; exact hwb⟩, hmF⟩

private theorem fidQueueRelinkOk_lengths {c : FullCfg} {s0 s1 : FullState} {n : Nat}
    (h : FidQueueRelinkOk c s0 s1 n) :
    s1.core.cur_vars = s0.core.cur_vars ∧ s1.core.vals.length = 2 * c.max_vars ∧
    s1.scratch.wsort.length = 2 * c.max_vars ∧ s1.scratch.q_prev.length = c.max_vars ∧
    s1.scratch.q_next.length = c.max_vars ∧ s1.scratch.q_stamp.length = c.max_vars :=
  ⟨h.1 ▸ rfl, h.2.1.core_ok.vals_len, h.2.1.scratch_ok.wsort_len,
   h.2.1.scratch_ok.q_prev_len, h.2.1.scratch_ok.q_next_len, h.2.1.scratch_ok.q_stamp_len⟩

private theorem fidQueueRelinkOk_wsort_get {c : FullCfg} {s0 s1 : FullState} {n : Nat}
    (h : FidQueueRelinkOk c s0 s1 n) {i : Nat} (hin : i < n) (hil : i < s1.scratch.wsort.length) :
    (s1.scratch.wsort[i]'hil).toNat < s0.core.cur_vars := by
  have := h.2.2.2 i hin; rw [List.getElem?_eq_getElem hil, Option.getD_some,
    h.1] at this; exact this

private theorem fidQueueRelinkOk_to_post {c : FullCfg} {s0 s1 : FullState} {n : Nat}
    {R : Mem 64 → Prop} {m : Mem 64}
    (h : FidQueueRelinkOk c s0 s1 n) (hm : (FullMem c s1 ⋆ R) m) : FidQueuePostOk c s0 R m :=
  ⟨s1, h.1, h.2.1, h.2.2.1, hm⟩

private theorem fidQueueRelinkOk_set_qprev {c : FullCfg} {s0 s1 : FullState} {n : Nat}
    (h : FidQueueRelinkOk c s0 s1 n) (i : Nat) (v : BitVec 32) :
    FidQueueRelinkOk c s0
      { s1 with scratch := { s1.scratch with q_prev := s1.scratch.q_prev.set i v } } n :=
  ⟨h.1, ⟨h.2.1.core_ok, { h.2.1.scratch_ok with
    q_prev_len := by simp [h.2.1.scratch_ok.q_prev_len] }⟩, h.2.2.1, h.2.2.2⟩
private theorem fidQueueRelinkOk_set_qnext {c : FullCfg} {s0 s1 : FullState} {n : Nat}
    (h : FidQueueRelinkOk c s0 s1 n) (i : Nat) (v : BitVec 32) :
    FidQueueRelinkOk c s0
      { s1 with scratch := { s1.scratch with q_next := s1.scratch.q_next.set i v } } n :=
  ⟨h.1, ⟨h.2.1.core_ok, { h.2.1.scratch_ok with
    q_next_len := by simp [h.2.1.scratch_ok.q_next_len] }⟩, h.2.2.1, h.2.2.2⟩
private theorem fidQueueRelinkOk_set_qstamp {c : FullCfg} {s0 s1 : FullState} {n : Nat}
    (h : FidQueueRelinkOk c s0 s1 n) (i : Nat) (v : BitVec 32) :
    FidQueueRelinkOk c s0
      { s1 with scratch := { s1.scratch with q_stamp := s1.scratch.q_stamp.set i v } } n :=
  ⟨h.1, ⟨h.2.1.core_ok, { h.2.1.scratch_ok with
    q_stamp_len := by simp [h.2.1.scratch_ok.q_stamp_len] }⟩, h.2.2.1, h.2.2.2⟩
private theorem fidQueueRelinkOk_set_qfirst {c : FullCfg} {s0 s1 : FullState} {n : Nat}
    (h : FidQueueRelinkOk c s0 s1 n) (v : BitVec 64) :
    FidQueueRelinkOk c s0 { s1 with scratch := { s1.scratch with q_first := v } } n :=
  ⟨h.1, ⟨h.2.1.core_ok, { h.2.1.scratch_ok with }⟩, h.2.2.1, h.2.2.2⟩
private theorem fidQueueRelinkOk_set_qlast {c : FullCfg} {s0 s1 : FullState} {n : Nat}
    (h : FidQueueRelinkOk c s0 s1 n) (v : BitVec 64) :
    FidQueueRelinkOk c s0 { s1 with scratch := { s1.scratch with q_last := v } } n :=
  ⟨h.1, ⟨h.2.1.core_ok, { h.2.1.scratch_ok with }⟩, h.2.2.1, h.2.2.2⟩
private theorem fidQueueRelinkOk_set_qsidx {c : FullCfg} {s0 s1 : FullState} {n : Nat}
    (h : FidQueueRelinkOk c s0 s1 n) (v : BitVec 64) :
    FidQueueRelinkOk c s0 { s1 with scratch := { s1.scratch with q_search_idx := v } } n :=
  ⟨h.1, ⟨h.2.1.core_ok, { h.2.1.scratch_ok with }⟩, h.2.2.1, h.2.2.2⟩
private theorem fidQueueRelinkOk_set_qsstamp {c : FullCfg} {s0 s1 : FullState} {n : Nat}
    (h : FidQueueRelinkOk c s0 s1 n) (v : BitVec 64) :
    FidQueueRelinkOk c s0 { s1 with scratch := { s1.scratch with q_search_stamp := v } } n :=
  ⟨h.1, ⟨h.2.1.core_ok, { h.2.1.scratch_ok with }⟩, h.2.2.1, h.2.2.2⟩
private theorem fidQueueRelinkOk_set_qcurstamp {c : FullCfg} {s0 s1 : FullState} {n : Nat}
    (h : FidQueueRelinkOk c s0 s1 n) (v : BitVec 64) :
    FidQueueRelinkOk c s0 { s1 with scratch := { s1.scratch with q_cur_stamp := v } } n :=
  ⟨h.1, ⟨h.2.1.core_ok, { h.2.1.scratch_ok with }⟩, h.2.2.1, h.2.2.2⟩
private theorem fidQueueRelinkOk_hdr3 {c : FullCfg} {s0 s1 : FullState} {n : Nat}
    (h : FidQueueRelinkOk c s0 s1 n) (a b d : BitVec 64) :
    FidQueueRelinkOk c s0
      { s1 with scratch := { s1.scratch with q_first := a, q_last := b, q_cur_stamp := d } } n :=
  ⟨h.1, ⟨h.2.1.core_ok, { h.2.1.scratch_ok with }⟩, h.2.2.1, h.2.2.2⟩

private theorem fid_bv64_ext_pres_heap {s sb s' : FullState}
    (hp1 : FullExtScratchPres s sb) (hp2 : FullExtScratchPres sb s') :
    FullExtScratchPres s s' :=
  ⟨hp2.1.trans hp1.1, hp2.2.trans hp1.2⟩

private def fidDummyVal : (t : Ty) → Val t
  | .bool => false
  | .bits n => BitVec.zero n
  | .float f => BitVec.zero f.width
  | .pair a b => (fidDummyVal a, fidDummyVal b)

private def fidDummyTup : (ts : List Ty) → Tup Val ts
  | [] => ()
  | t :: ts => (fidDummyVal t, fidDummyTup ts)

private def fidSkipLets {rs : List Ty} : Nat → Expr Val Cont rs → Expr Val Cont rs
  | 0, e => e
  | fuel + 1, .let_ (ts := ts) _ k => fidSkipLets fuel (k (fidDummyTup ts))
  | _, e => e

private def fidSkip {rs : List Ty} : Nat → Expr Val Cont rs → Expr Val Cont rs
  | 0, e => e
  | fuel + 1, .let_ (ts := ts) _ k => fidSkip fuel (k (fidDummyTup ts))
  | fuel + 1, .load t _ k => fidSkip fuel (k (fidDummyVal t))
  | _, e => e

private def fidLoad64 {rs : List Ty} (v : Val i64) : Expr Val Cont rs → Expr Val Cont rs
  | .load (.bits 64) _ k => k v
  | _ => .hlt

private def fidLet64 {rs : List Ty} (v : Val i64) : Expr Val Cont rs → Expr Val Cont rs
  | .let_ (ts := [.bits 64]) _ k => k (v, ())
  | _ => .hlt

private def fidGrp0Exit {rs : List Ty} : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[]]) bodies _ =>
    match bodies (fun _ _ => False, ()) with
    | .cons f .nil => f ()
  | _ => .hlt

private def fidGrp1Exit {rs : List Ty} : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 64]]) bodies _ =>
    match bodies (fun _ _ => False, ()) with
    | .cons f .nil => f (0#64, ())
  | _ => .hlt

private def fidGrp2Exit {rs : List Ty} (n : Val i64) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 64, .bits 64]]) bodies _ =>
    match bodies (fun _ _ => False, ()) with
    | .cons f .nil => f (n, 0#64, ())
  | _ => .hlt

private def fidThen {rs : List Ty} : Expr Val Cont rs → Expr Val Cont rs
  | .jnz _ t _ => t
  | _ => .hlt

private def fidElse {rs : List Ty} : Expr Val Cont rs → Expr Val Cont rs
  | .jnz _ _ e => e
  | _ => .hlt

private def fidNextLoad64 {rs : List Ty} (v : Val i64) (e : Expr Val Cont rs) :
    Expr Val Cont rs :=
  fidLoad64 v (fidSkipLets 10 e)

private def fidNextLoad64Let64 {rs : List Ty} (v lv : Val i64) (e : Expr Val Cont rs) :
    Expr Val Cont rs :=
  fidLet64 lv (fidSkipLets 1 (fidNextLoad64 v e))

private def fidSkipWhile1 {rs : List Ty} (e : Expr Val Cont rs) : Expr Val Cont rs :=
  fidElse (fidSkip 16 (fidGrp1Exit (fidSkip 16 e)))

private def fidCmp (c : CmpOp) (t : Ty) (a b : Arg Val t) : Op Val [t.mask] :=
  { sig := [t, t], code := OpCode.cmp c t, args := (a, b, ()) }

private def fidLoop4Wrap (cv wl wr : Val i64) (k : Expr Val Cont [i64]) : Expr Val Cont [i64] :=
  Expr.group (sig := [[i64]])
    (fun Js => Blocks.cons
      (fun p => Expr.let_ (fidCmp .ult i64 (.var p.fst) (.var cv)) fun c0 =>
        Expr.jnz (.var c0.fst)
          (Expr.let_ (op2 (.mul i64) (.var p.fst) (.imm 8)) fun off0 =>
          Expr.let_ (op2 (.add i64) (.var wl) (.var off0.fst)) fun ptr0 =>
          Expr.load i64 (.var ptr0.fst) fun a =>
          Expr.let_ (op2 (.mul i64) (.var p.fst) (.imm 8)) fun off1 =>
          Expr.let_ (op2 (.add i64) (.var wr) (.var off1.fst)) fun ptr1 =>
          Expr.load i64 (.var ptr1.fst) fun b =>
          Expr.let_ (op2 (.mul i64) (.var p.fst) (.imm 8)) fun off2 =>
          Expr.let_ (op2 (.add i64) (.var wl) (.var off2.fst)) fun ptr2 =>
          Expr.group (sig := [[i64]])
            (fun _ => Blocks.cons
              (fun pj => Expr.store (.var pj.fst) (.var ptr2.fst)
                (Expr.let_ (op2 (.add i64) (.var p.fst) (.imm 1)) fun nxt =>
                  Expr.jump Js.fst (.var nxt.fst, ())))
              Blocks.nil)
            (fun Js1 => Expr.let_ (fidCmp .uge i64 (.var a) (.var b)) fun ge =>
              Expr.jnz (.var ge.fst)
                (Expr.let_ (op1 (.sext 32 64) (.imm 1)) fun s1 =>
                Expr.let_ (op2 (.shl i64) (.var b) (.var s1.fst)) fun sh =>
                Expr.let_ (op2 (.add i64) (.var a) (.var sh.fst)) fun sum =>
                Expr.jump Js1.fst (.var sum.fst, ()))
                (Expr.let_ (op1 (.sext 32 64) (.imm 1)) fun s1 =>
                Expr.let_ (op2 (.shl i64) (.var a) (.var s1.fst)) fun sh =>
                Expr.let_ (op2 (.add i64) (.var b) (.var sh.fst)) fun sum =>
                Expr.jump Js1.fst (.var sum.fst, ()))))
          k)
      Blocks.nil)
    (fun Js => Expr.jump Js.fst (.imm 0, ()))

private def fidPost4Wrap (h : Val i64) (kt ke : Expr Val Cont [i64]) : Expr Val Cont [i64] :=
  Expr.let_ (op2 (.add i64) (.var h) (.imm 552)) fun p =>
  Expr.load i64 (.var p.fst) fun ld =>
  Expr.let_ (fidCmp .ne i64 (.var ld) (.imm 0)) fun p =>
  Expr.jnz (.var p.fst) kt ke

private def fidStableBody (h cv fl wl : Val i64) : Expr Val Cont [i64] :=
  Expr.call (as := [i64]) (bs := []) "full_rescale" (Arg.var h, ()) fun _ =>
  Expr.let_ (op2 (.add i64) (.var h) (.imm 216)) fun p =>
  Expr.load i64 (.var p.fst) fun sc =>
  Expr.group (sig := [[i64, i64]])
    (fun Js => Blocks.cons
      (fun p => Expr.let_ (fidCmp .ult i64 (.var p.fst) (.var cv)) fun c0 =>
        Expr.jnz (.var c0.fst)
          (Expr.group (sig := [[i64]])
            (fun _ => Blocks.cons
              (fun p3 => Expr.let_ (op2 (.add i64) (.var p.fst) (.imm 1)) fun nsv =>
                Expr.jump Js.fst (.var nsv.fst, .var p3.fst, ()))
              Blocks.nil)
            (fun Js1 => Expr.let_ (op2 (.mul i64) (.var p.fst) (.imm 4)) fun p3 =>
              Expr.let_ (op2 (.add i64) (.var fl) (.var p3.fst)) fun p4 =>
              Expr.load i32 (.var p4.fst) fun ld =>
              Expr.let_ (op2 (.and i32) (.var ld) (.imm 1)) fun p5 =>
              Expr.let_ (fidCmp .ne i32 (.var p5.fst) (.imm 0)) fun p6 =>
              Expr.jnz (.var p6.fst)
                (Expr.let_ (op2 (.mul i64) (.var p.fst) (.imm 8)) fun p7 =>
                Expr.let_ (op2 (.add i64) (.var wl) (.var p7.fst)) fun p8 =>
                Expr.load i64 (.var p8.fst) fun ld =>
                Expr.let_ (fidCmp .ugt i64 (.var ld) (.var p.snd.fst)) fun p9 =>
                Expr.jnz (.var p9.fst)
                  (Expr.let_ (op2 (.mul i64) (.var p.fst) (.imm 8)) fun p =>
                  Expr.let_ (op2 (.add i64) (.var wl) (.var p.fst)) fun p =>
                  Expr.load i64 (.var p.fst) fun ld =>
                  Expr.jump Js1.fst (.var ld, ()))
                  (Expr.jump Js1.fst (.var p.snd.fst, ())))
                (Expr.jump Js1.fst (.var p.snd.fst, ()))))
          (Expr.let_ (op2 (.add i64) (.var h) (.imm 256)) fun p3 =>
          Expr.load i64 (.var p3.fst) fun ld1 =>
          Expr.group (sig := [[i64]])
            (fun _ => Blocks.cons
              (fun p4 => Expr.group (sig := [[i64]])
                (fun JsA => Blocks.cons
                  (fun p5 => Expr.let_ (fidCmp .ult i64 (.var p5.fst) (.var cv)) fun p6 =>
                    Expr.jnz (.var p6.fst)
                      (Expr.group (sig := [[]])
                        (fun _ => Blocks.cons
                          (fun _ => Expr.let_ (op2 (.add i64) (.var p5.fst) (.imm 1)) fun p =>
                            Expr.jump JsA.fst (.var p.fst, ()))
                          Blocks.nil)
                        (fun Js1 => Expr.let_ (op2 (.mul i64) (.var p5.fst) (.imm 4)) fun p7 =>
                          Expr.let_ (op2 (.add i64) (.var fl) (.var p7.fst)) fun p8 =>
                          Expr.load i32 (.var p8.fst) fun ld2 =>
                          Expr.let_ (op2 (.and i32) (.var ld2) (.imm 1)) fun p9 =>
                          Expr.let_ (fidCmp .ne i32 (.var p9.fst) (.imm 0)) fun p10 =>
                          Expr.jnz (.var p10.fst)
                            (Expr.let_ (op2 (.mul i64) (.var p5.fst) (.imm 8)) fun p11 =>
                            Expr.let_ (op2 (.add i64) (.var wl) (.var p11.fst)) fun p12 =>
                            Expr.load i64 (.var p12.fst) fun ld3 =>
                            Expr.let_ (fidCmp .ugt i64 (.var ld3) (.imm 0)) fun p13 =>
                            Expr.jnz (.var p13.fst)
                              (Expr.group (sig := [[i64]])
                                (fun _ => Blocks.cons
                                  (fun p_d => Expr.group (sig := [[i64]])
                                    (fun _ => Blocks.cons
                                      (fun p_c => Expr.let_
                                        (op2 (.mul i64) (.var p5.fst) (.imm 8)) fun p14 =>
                                        Expr.let_ (op2 (.add i64) (.var sc) (.var p14.fst))
                                          fun p15 =>
                                        Expr.load i64 (.var p15.fst) fun ld4 =>
                                        Expr.group (sig := [[i64]])
                                          (fun _ => Blocks.cons
                                            (fun p16 =>
                                              Expr.let_ (op2 (.mul i64) (.var p5.fst) (.imm 8))
                                                fun p17 =>
                                              Expr.let_ (op2 (.add i64) (.var sc) (.var p17.fst))
                                                fun p18 =>
                                              Expr.store (.var p16.fst) (.var p18.fst)
                                                (Expr.let_ (op1 (.trunc 64 32) (.var p5.fst))
                                                  fun p =>
                                                Expr.call (as := [i64, i32]) (bs := [])
                                                  "full_heap_up" (Arg.var h, Arg.var p.fst, ())
                                                  fun _ => Expr.jump Js1.fst ()))
                                            Blocks.nil)
                                          (fun JsC => Expr.let_ (op1 (.sext 32 64) (.imm 60))
                                            fun p16 =>
                                            Expr.let_ (op2 (.shl i64) (.imm 1) (.var p16.fst))
                                              fun p17 =>
                                            Expr.let_ (op2 (.sub i64) (.var p17.fst) (.var p_c.fst))
                                              fun p18 =>
                                            Expr.let_ (fidCmp .ugt i64 (.var ld4) (.var p18.fst))
                                              fun p19 =>
                                            Expr.jnz (.var p19.fst)
                                              (Expr.let_ (op1 (.sext 32 64) (.imm 60)) fun p =>
                                              Expr.let_ (op2 (.shl i64) (.imm 1) (.var p.fst))
                                                fun p => Expr.jump JsC.fst (.var p.fst, ()))
                                              (Expr.let_ (op2 (.add i64) (.var ld4) (.var p_c.fst))
                                                fun p => Expr.jump JsC.fst (.var p.fst, ()))))
                                      Blocks.nil)
                                    (fun JsD => Expr.let_ (op1 (.sext 32 64) (.imm 52)) fun p14 =>
                                      Expr.let_ (op2 (.shl i64) (.imm 1) (.var p14.fst))
                                        fun p15 =>
                                      Expr.let_ (fidCmp .ugt i64 (.var p_d.fst) (.var p15.fst))
                                        fun p16 =>
                                      Expr.jnz (.var p16.fst)
                                        (Expr.let_ (op1 (.sext 32 64) (.imm 52)) fun p =>
                                        Expr.let_ (op2 (.shl i64) (.imm 1) (.var p.fst))
                                          fun p => Expr.jump JsD.fst (.var p.fst, ()))
                                        (Expr.jump JsD.fst (.var p_d.fst, ()))))
                                  Blocks.nil)
                                (fun JsB => Expr.let_ (fidCmp .ugt i64 (.var p.snd.fst) (.imm 0))
                                  fun p =>
                                  Expr.jnz (.var p.fst)
                                    (Expr.let_ (op2 (.mul i64) (.var p5.fst) (.imm 8)) fun p =>
                                    Expr.let_ (op2 (.add i64) (.var wl) (.var p.fst)) fun p =>
                                    Expr.load i64 (.var p.fst) fun ld =>
                                    Expr.let_ (op1 (.sext 32 64) (.imm 20)) fun p =>
                                    Expr.let_ (op2 (.lshr i64) (.var ld) (.var p.fst)) fun p =>
                                    Expr.let_ (op1 (.sext 32 64) (.imm 20)) fun p14 =>
                                    Expr.let_ (op2 (.lshr i64) (.var p4.fst) (.var p14.fst))
                                      fun p15 =>
                                    Expr.let_ (op2 (.mul i64) (.var p.fst) (.var p15.fst))
                                      fun p => Expr.jump JsB.fst (.var p.fst, ()))
                                    (Expr.jump JsB.fst (.imm 0, ()))))
                              (Expr.jump Js1.fst ()))
                            (Expr.jump Js1.fst ())))
                      (Expr.ret (.var cv, ())))
                  Blocks.nil)
                (fun JsA => Expr.jump JsA.fst (.imm 0, ())))
              Blocks.nil)
            (fun JsR => Expr.let_ (op1 (.sext 32 64) (.imm 20)) fun p =>
              Expr.let_ (op2 (.shl i64) (.imm 1) (.var p.fst)) fun p =>
              Expr.let_ (fidCmp .ult i64 (.var ld1) (.var p.fst)) fun p =>
              Expr.jnz (.var p.fst)
                (Expr.let_ (op1 (.sext 32 64) (.imm 20)) fun p =>
                Expr.let_ (op2 (.shl i64) (.imm 1) (.var p.fst)) fun p =>
                Expr.jump JsR.fst (.var p.fst, ()))
                (Expr.jump JsR.fst (.var ld1, ())))))
      Blocks.nil)
    (fun Js => Expr.jump Js.fst (.imm 0, .imm 0, ()))

private def fidFocusWrap (h cv fl ws : Val i64) (k : Val i64 → Expr Val Cont [i64]) :
    Expr Val Cont [i64] :=
  Expr.group (sig := [[i64, i64]])
    (fun Js => Blocks.cons
      (fun p => Expr.let_ (fidCmp .ult i64 (.var p.snd.fst) (.var cv)) fun p2 =>
        Expr.jnz (.var p2.fst)
          (Expr.group (sig := [[i64]])
            (fun _ => Blocks.cons
              (fun p3 => Expr.let_ (op2 (.add i64) (.var p.snd.fst) (.imm 1)) fun p =>
                Expr.jump Js.fst (.var p3.fst, .var p.fst, ()))
              Blocks.nil)
            (fun Js1 => Expr.let_ (op2 (.mul i64) (.var p.snd.fst) (.imm 4)) fun p3 =>
              Expr.let_ (op2 (.add i64) (.var fl) (.var p3.fst)) fun p4 =>
              Expr.load i32 (.var p4.fst) fun ld =>
              Expr.let_ (op2 (.and i32) (.var ld) (.imm 1)) fun p5 =>
              Expr.let_ (fidCmp .ne i32 (.var p5.fst) (.imm 0)) fun p6 =>
              Expr.jnz (.var p6.fst)
                (Expr.let_ (op2 (.mul i64) (.var p.fst) (.imm 4)) fun p7 =>
                Expr.let_ (op2 (.add i64) (.var ws) (.var p7.fst)) fun p8 =>
                Expr.let_ (op1 (.trunc 64 32) (.var p.snd.fst)) fun p9 =>
                Expr.store (.var p9.fst) (.var p8.fst)
                  (Expr.let_ (op2 (.add i64) (.var p.fst) (.imm 1)) fun p =>
                    Expr.jump Js1.fst (.var p.fst, ())))
                (Expr.jump Js1.fst (.var p.fst, ()))))
          (Expr.group (sig := [[]])
            (fun _ => Blocks.cons (fun _ => k p.fst) Blocks.nil)
            (fun Js => Expr.let_ (fidCmp .ugt i64 (.var p.fst) (.imm 1)) fun p3 =>
              Expr.jnz (.var p3.fst)
                (Expr.let_ (op1 (.sext 32 64) (.imm 1)) fun p4 =>
                Expr.let_ (op2 (.lshr i64) (.var p.fst) (.var p4.fst)) fun p5 =>
                Expr.group (sig := [[i64]])
                  (fun Js1 => Blocks.cons
                    (fun p6 => Expr.let_ (fidCmp .ugt i64 (.var p6.fst) (.imm 0)) fun p7 =>
                      Expr.jnz (.var p7.fst)
                        (Expr.let_ (op2 (.sub i64) (.var p6.fst) (.imm 1)) fun p8 =>
                        Expr.call (as := [i64, i64, i64]) (bs := []) "full_reorder_sift_fid"
                          (Arg.var h, Arg.var p8.fst, Arg.var p.fst, ())
                          fun _ => Expr.jump Js1.fst (.var p8.fst, ()))
                        (Expr.group (sig := [[i64]])
                          (fun Js2 => Blocks.cons
                            (fun pe => Expr.let_ (fidCmp .ugt i64 (.var pe.fst) (.imm 1)) fun p8 =>
                              Expr.jnz (.var p8.fst)
                                (Expr.let_ (op2 (.sub i64) (.var pe.fst) (.imm 1)) fun pe1 =>
                                Expr.let_ (op1 (.sext 32 64) (.imm 0)) fun p9 =>
                                Expr.let_ (op2 (.mul i64) (.var p9.fst) (.imm 4)) fun p10 =>
                                Expr.let_ (op2 (.add i64) (.var ws) (.var p10.fst)) fun p11 =>
                                Expr.load i32 (.var p11.fst) fun ld =>
                                Expr.let_ (op1 (.sext 32 64) (.imm 0)) fun p12 =>
                                Expr.let_ (op2 (.mul i64) (.var p12.fst) (.imm 4)) fun p13 =>
                                Expr.let_ (op2 (.add i64) (.var ws) (.var p13.fst)) fun p14 =>
                                Expr.let_ (op2 (.mul i64) (.var pe1.fst) (.imm 4)) fun p15 =>
                                Expr.let_ (op2 (.add i64) (.var ws) (.var p15.fst)) fun p16 =>
                                Expr.load i32 (.var p16.fst) fun ld1 =>
                                Expr.store (.var ld1) (.var p14.fst)
                                  (Expr.let_ (op2 (.mul i64) (.var pe1.fst) (.imm 4)) fun p17 =>
                                  Expr.let_ (op2 (.add i64) (.var ws) (.var p17.fst)) fun p18 =>
                                  Expr.store (.var ld) (.var p18.fst)
                                    (Expr.call (as := [i64, i64, i64]) (bs := [])
                                      "full_reorder_sift_fid"
                                      (Arg.var h, Arg.imm (t := i64) 0, Arg.var pe1.fst, ())
                                      fun _ => Expr.jump Js2.fst (.var pe1.fst, ()))))
                                (Expr.jump Js.fst ()))
                            Blocks.nil)
                          (fun Js2 => Expr.jump Js2.fst (.var p.fst, ()))))
                    Blocks.nil)
                  (fun Js1 => Expr.jump Js1.fst (.var p5.fst, ())))
                (Expr.jump Js.fst ()))))
      Blocks.nil)
    (fun Js => Expr.jump Js.fst (.imm 0, .imm 0, ()))

private def fidPhase2Step (h n cv vl ws qp qn qs : Val i64) : Expr Val Cont [i64] :=
  Expr.group (sig := [[i64]])
    (fun Js => Blocks.cons
      (fun p4 => Expr.let_ (fidCmp .ult i64 (.var p4.fst) (.var cv)) fun p5 =>
        Expr.jnz (.var p5.fst)
          (Expr.let_ (op2 (.mul i64) (.var p4.fst) (.imm 4)) fun p =>
           Expr.let_ (op2 (.add i64) (.var qp) (.var p.fst)) fun p =>
           Expr.store (Arg.imm (t := i32) 4294967295) (Arg.var p.fst) <|
           Expr.let_ (op2 (.mul i64) (.var p4.fst) (.imm 4)) fun p =>
           Expr.let_ (op2 (.add i64) (.var qn) (.var p.fst)) fun p =>
           Expr.store (Arg.imm (t := i32) 4294967295) (Arg.var p.fst) <|
           Expr.let_ (op2 (.mul i64) (.var p4.fst) (.imm 4)) fun p =>
           Expr.let_ (op2 (.add i64) (.var qs) (.var p.fst)) fun p =>
           Expr.store (Arg.imm (t := i32) 0) (Arg.var p.fst) <|
           Expr.let_ (op2 (.add i64) (.var p4.fst) (.imm 1)) fun p =>
           Expr.jump Js.fst (Arg.var p.fst, ()))
          (Expr.let_ (fidCmp .eq i64 (.var n) (.imm 0)) fun p6 =>
           Expr.jnz (.var p6.fst)
             (Expr.let_ (op2 (.add i64) (.var h) (.imm 608)) fun p =>
              Expr.store (Arg.imm (t := i64) 4294967295) (Arg.var p.fst) <|
              Expr.let_ (op2 (.add i64) (.var h) (.imm 616)) fun p =>
              Expr.store (Arg.imm (t := i64) 4294967295) (Arg.var p.fst) <|
              Expr.let_ (op2 (.add i64) (.var h) (.imm 624)) fun p =>
              Expr.store (Arg.imm (t := i64) 4294967295) (Arg.var p.fst) <|
              Expr.let_ (op2 (.add i64) (.var h) (.imm 640)) fun p =>
              Expr.store (Arg.imm (t := i64) 0) (Arg.var p.fst) <|
              Expr.let_ (op2 (.add i64) (.var h) (.imm 632)) fun p =>
              Expr.store (Arg.imm (t := i64) 0) (Arg.var p.fst) <|
              Expr.ret (Arg.imm (t := i64) 0, ()))
             (Expr.group (sig := [[i64, i64, i64]])
               (fun JsL => Blocks.cons
                 (fun p7 => Expr.let_ (fidCmp .ult i64 (.var p7.snd.snd.fst) (.var n)) fun p8 =>
                   Expr.jnz (.var p8.fst)
                     (Expr.let_ (op2 (.mul i64) (.var p7.snd.snd.fst) (.imm 4)) fun p9 =>
                      Expr.let_ (op2 (.add i64) (.var ws) (.var p9.fst)) fun p10 =>
                      Expr.load i32 (Arg.var p10.fst) fun ld =>
                      Expr.let_ (op1 (.zext 32 64) (.var ld)) fun p11 =>
                      Expr.let_ (op2 (.mul i64) (.var p11.fst) (.imm 4)) fun p12 =>
                      Expr.let_ (op2 (.add i64) (.var qp) (.var p12.fst)) fun p13 =>
                      Expr.group (sig := [[i32]])
                        (fun _ => Blocks.cons
                          (fun p14 => Expr.store (Arg.var p14.fst) (Arg.var p13.fst) <|
                            Expr.let_ (op1 (.zext 32 64) (.var ld)) fun p15 =>
                            Expr.let_ (op2 (.mul i64) (.var p15.fst) (.imm 4)) fun p16 =>
                            Expr.let_ (op2 (.add i64) (.var qn) (.var p16.fst)) fun p17 =>
                            Expr.group (sig := [[i32]])
                              (fun _ => Blocks.cons
                                (fun pN => Expr.store (Arg.var pN.fst) (Arg.var p17.fst) <|
                                  Expr.let_ (op1 (.zext 32 64) (.var ld)) fun p =>
                                  Expr.let_ (op2 (.mul i64) (.var p.fst) (.imm 4)) fun p =>
                                  Expr.let_ (op2 (.add i64) (.var qs) (.var p.fst)) fun p =>
                                  Expr.let_ (op2 (.add i64) (.var p7.snd.snd.fst) (.imm 1))
                                    fun p18 =>
                                  Expr.let_ (op1 (.trunc 64 32) (.var p18.fst)) fun p19 =>
                                  Expr.store (Arg.var p19.fst) (Arg.var p.fst) <|
                                  Expr.group (sig := [[i64, i64]])
                                    (fun _ => Blocks.cons
                                      (fun p => Expr.let_
                                        (op2 (.add i64) (.var p7.snd.snd.fst) (.imm 1)) fun p20 =>
                                        Expr.jump JsL.fst
                                          (Arg.var p.fst, Arg.var p.snd.fst, Arg.var p20.fst, ()))
                                      Blocks.nil)
                                    (fun JsB =>
                                      Expr.let_ (op1 (.zext 32 64) (.var ld)) fun p =>
                                      Expr.let_ (op1 (.sext 32 64) (.imm 1)) fun p20 =>
                                      Expr.let_ (op2 (.shl i64) (.var p.fst) (.var p20.fst))
                                        fun p =>
                                      Expr.let_ (op2 (.add i64) (.var vl) (.var p.fst)) fun p =>
                                      Expr.load i8 (Arg.var p.fst) fun ld1 =>
                                      Expr.let_ (op1 (.trunc 32 8) (.imm 0)) fun p =>
                                      Expr.let_ (op1 (.sext 8 32) (.var ld1)) fun p21 =>
                                      Expr.let_ (op1 (.sext 8 32) (.var p.fst)) fun p =>
                                      Expr.let_ (fidCmp .eq i32 (.var p21.fst) (.var p.fst))
                                        fun p =>
                                      Expr.jnz (Arg.var p.fst)
                                        (Expr.let_ (op1 (.zext 32 64) (.var ld)) fun p =>
                                         Expr.let_ (op2 (.add i64) (.var p7.snd.snd.fst) (.imm 1))
                                           fun p22 =>
                                         Expr.jump JsB.fst (Arg.var p.fst, Arg.var p22.fst, ()))
                                        (Expr.jump JsB.fst
                                          (Arg.var p7.fst, Arg.var p7.snd.fst, ()))))
                              Blocks.nil)
                            (fun JsN =>
                              Expr.let_ (op2 (.add i64) (.var p7.snd.snd.fst) (.imm 1)) fun p18 =>
                              Expr.let_ (fidCmp .ult i64 (.var p18.fst) (.var n)) fun p =>
                              Expr.jnz (Arg.var p.fst)
                                (Expr.let_ (op2 (.add i64) (.var p7.snd.snd.fst) (.imm 1)) fun p =>
                                 Expr.let_ (op2 (.mul i64) (.var p.fst) (.imm 4)) fun p =>
                                 Expr.let_ (op2 (.add i64) (.var ws) (.var p.fst)) fun p =>
                                 Expr.load i32 (Arg.var p.fst) fun ld =>
                                 Expr.jump JsN.fst (Arg.var ld, ()))
                                (Expr.jump JsN.fst (Arg.imm (t := i32) 4294967295, ()))))
                          Blocks.nil)
                        (fun JsP =>
                          Expr.let_ (fidCmp .ugt i64 (.var p7.snd.snd.fst) (.imm 0)) fun p =>
                          Expr.jnz (Arg.var p.fst)
                            (Expr.let_ (op2 (.sub i64) (.var p7.snd.snd.fst) (.imm 1)) fun p =>
                             Expr.let_ (op2 (.mul i64) (.var p.fst) (.imm 4)) fun p =>
                             Expr.let_ (op2 (.add i64) (.var ws) (.var p.fst)) fun p =>
                             Expr.load i32 (Arg.var p.fst) fun ld =>
                             Expr.jump JsP.fst (Arg.var ld, ()))
                            (Expr.jump JsP.fst (Arg.imm (t := i32) 4294967295, ()))) )
                     (Expr.let_ (op1 (.sext 32 64) (.imm 0)) fun p9 =>
                      Expr.let_ (op2 (.mul i64) (.var p9.fst) (.imm 4)) fun p10 =>
                      Expr.let_ (op2 (.add i64) (.var ws) (.var p10.fst)) fun p11 =>
                      Expr.load i32 (Arg.var p11.fst) fun ld =>
                      Expr.let_ (op1 (.zext 32 64) (.var ld)) fun p12 =>
                      Expr.let_ (op2 (.add i64) (.var h) (.imm 608)) fun p13 =>
                      Expr.store (Arg.var p12.fst) (Arg.var p13.fst) <|
                      Expr.let_ (op2 (.sub i64) (.var n) (.imm 1)) fun p14 =>
                      Expr.let_ (op2 (.mul i64) (.var p14.fst) (.imm 4)) fun p15 =>
                      Expr.let_ (op2 (.add i64) (.var ws) (.var p15.fst)) fun p16 =>
                      Expr.load i32 (Arg.var p16.fst) fun ld =>
                      Expr.let_ (op1 (.zext 32 64) (.var ld)) fun p17 =>
                      Expr.let_ (op2 (.add i64) (.var h) (.imm 616)) fun p18 =>
                      Expr.store (Arg.var p17.fst) (Arg.var p18.fst) <|
                      Expr.let_ (op2 (.add i64) (.var h) (.imm 640)) fun p19 =>
                      Expr.store (Arg.var n) (Arg.var p19.fst) <|
                      Expr.group (sig := [[i64, i64]])
                        (fun _ => Blocks.cons
                          (fun p20 => Expr.let_ (op2 (.add i64) (.var h) (.imm 624)) fun p21 =>
                            Expr.store (Arg.var p20.fst) (Arg.var p21.fst) <|
                            Expr.let_ (op2 (.add i64) (.var h) (.imm 632)) fun p22 =>
                            Expr.store (Arg.var p20.snd.fst) (Arg.var p22.fst) <|
                            Expr.ret (Arg.var n, ()))
                          Blocks.nil)
                        (fun JsS =>
                          Expr.let_ (fidCmp .uge i64 (.var p7.fst) (.var cv)) fun p20 =>
                          Expr.jnz (Arg.var p20.fst)
                            (Expr.let_ (op2 (.sub i64) (.var n) (.imm 1)) fun p21 =>
                             Expr.let_ (op2 (.mul i64) (.var p21.fst) (.imm 4)) fun p22 =>
                             Expr.let_ (op2 (.add i64) (.var ws) (.var p22.fst)) fun p23 =>
                             Expr.load i32 (Arg.var p23.fst) fun ld =>
                             Expr.let_ (op1 (.zext 32 64) (.var ld)) fun p24 =>
                             Expr.jump JsS.fst (Arg.var p24.fst, Arg.var n, ()))
                            (Expr.jump JsS.fst (Arg.var p7.fst, Arg.var p7.snd.fst, ())))))
                 Blocks.nil)
               (fun JsL => Expr.jump JsL.fst (.imm 4294967295, .imm 0, .imm 0, ())))))
      Blocks.nil)
    (fun Js => Expr.jump Js.fst (.imm 0, ()))

private def fidLoop34Expr (h cv nlits wlen vl fl wvec wstk ws qp qn qs wl wr w2 wcap : Val i64) :
    Expr Val Cont [i64] :=
  full_reorder_queue_fid_body Val Cont (h, ())
    |> fidNextLoad64Let64 cv nlits
    |> fidNextLoad64 0#64 |> fidNextLoad64 wlen |> fidNextLoad64 vl
    |> fidNextLoad64 fl
    |> fidNextLoad64 0#64 |> fidNextLoad64 wvec |> fidNextLoad64 wstk
    |> fidNextLoad64 ws |> fidNextLoad64 qp |> fidNextLoad64 qn |> fidNextLoad64 qs
    |> fidNextLoad64 wl |> fidNextLoad64 wr
    |> (fun e => fidLet64 w2 (fidSkipLets 1 e))
    |> (fun e => fidLet64 wcap (fidSkipLets 1 e))
    |> fidSkipWhile1
    |> (fun e => fidGrp1Exit (fidSkip 16 e))

private theorem fid_queue_stable_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {wl4 wr4 : FidArr64 c.max_vars}
    {m4 : Mem 64}
    (hRescale : EnvSpec Γ "full_rescale" fullRescaleSpec)
    (hHeapUp : EnvSpec Γ "full_heap_up" fullHeapUpSpec)
    (hlen : s.LengthsOk c)
    (hQ' : ∀ r m', FidQueuePostOk c s R m' → Q r m')
    (hcv_le : s.core.cur_vars ≤ c.max_vars)
    (hcv_30 : s.core.cur_vars < 2 ^ 30)
    (hm4 : (FidReorderMem c s wl4 wr4 ⋆ R) m4) :
    wp Γ Q X (fidStableBody c.hdr (BitVec.ofNat 64 s.core.cur_vars) c.pFlags c.pTarjanMark)
      m4 := by
  unfold fidStableBody; dsimp only [fidCmp]
  obtain ⟨tmk0, trc0, htmk0, htrc0, hmF0⟩ := fid_fullMem_of_reorderMem hm4
  let sF0 : FullState :=
    { s with scratch := { s.scratch with tarjan_mark := tmk0, tarjan_reach := trc0 } }
  have hlenF0 : sF0.LengthsOk c := ⟨hlen.core_ok, { hlen.scratch_ok with
    tarjan_mark_len := htmk0, tarjan_reach_len := htrc0 }⟩
  have hextF0 : FullExtScratchPres s sF0 := ⟨rfl, rfl⟩
  c0_call hRescale
  refine ⟨c, sF0, R, rfl, hlenF0, hmF0,
    fun r_s sF1 mF1 hsF1_core hsF1_len hsF1_p hmF1 => ?_⟩
  obtain ⟨wl1, wr1, hm1r⟩ := fid_reorderMem_of_fullMem hsF1_len hmF1
  have hce1 : sF1.core = s.core := hsF1_core
  have hext1 : FullExtScratchPres s sF1 := fid_bv64_ext_pres_heap hextF0 hsF1_p.1
  have hfl1_len : sF1.core.flags.length = c.max_vars := hsF1_len.core_ok.flags_len
  have hcv1_eq : sF1.core.cur_vars = s.core.cur_vars := by rw [hce1]
  c0_hsteps_nogrp
  -- Loop A (`sv`, `maxw`): compute max active weight `wl[sv]`
  refine wp_while_state (fun p : BitVec 64 × BitVec 64 × PUnit => p)
    (fun p => s.core.cur_vars - p.1.toNat)
    (fun p m_a => p.1.toNat ≤ s.core.cur_vars ∧ m_a = mF1)
    (fun Ja hJa => by c0_hsteps; exact hJa (0#64, 0#64, ()) mF1 ⟨Nat.zero_le _, rfl⟩)
    (fun Ja ⟨sv, maxw, ⟨⟩⟩ m_a ⟨hsv, hma⟩ hJa => ?_)
  subst m_a
  c0_hsplit
  · have hsv_lt : sv.toNat < s.core.cur_vars := fid_bv64_lt_of_mod_lt hcv_30 ‹_›
    have hsv_fl : sv.toNat < sF1.core.flags.length :=
      hfl1_len.symm ▸ Nat.lt_of_lt_of_le hsv_lt hcv_le
    have hsv_mv : sv.toNat < c.max_vars := Nat.lt_of_lt_of_le hsv_lt hcv_le
    have hsvp1 := fid_bv64_add1_toNat hcv_30 hsv_lt
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64]) (fun _ mg => mg = mF1) ?_ ?_
    · rintro _ ⟨mw', _⟩ mg hmg
      subst mg; dsimp only [Blocks.get]; c0_hsteps
      exact hJa (sv + 1#64, mw', ()) mF1 hsvp1.2.2 ⟨hsvp1.2.1, rfl⟩
    · intro Jg hJg
      c0_hsplit
      · c0_hsplit
        · c0_hsteps; exact hJg (_, ()) mF1 rfl
        · c0_hsteps; exact hJg (_, ()) mF1 rfl
      · c0_hsteps; exact hJg (_, ()) mF1 rfl
  · c0_hsteps_nogrp
    refine wp_join_group (ts := [i64]) (fun _ m_sr => m_sr = mF1) ?_ ?_
    · rintro _ ⟨scale_ref, _⟩ m_sr hmsr
      subst m_sr; dsimp only [Blocks.get]; c0_hsteps_nogrp
      -- Loop B (`sv` = `0 ..< cv`): boost `sc[sv]` and call `full_heap_up(h, (u32)sv)`
      refine wp_while_state1 (fun sv : BitVec 64 => sv)
        (fun sv => s.core.cur_vars - sv.toNat)
        (fun sv m_b => sv.toNat ≤ s.core.cur_vars ∧
          ∃ (sb : FullState) (wlb wrb : FidArr64 c.max_vars),
            sb.core = s.core ∧ sb.LengthsOk c ∧ FullExtScratchPres s sb ∧
            (FidReorderMem c sb wlb wrb ⋆ R) m_b)
        (fun Jb hJb => by
          c0_hsteps
          exact hJb 0#64 mF1 ⟨Nat.zero_le _, sF1, wl1, wr1, hsF1_core, hsF1_len,
            hext1, hm1r⟩)
        (fun Jb sv m_b ⟨hsv, sb, wlb, wrb, hsb_core, hsb_len, hsb_ext, hmb⟩ hJb => ?_)
      c0_hsplit
      · have hsv_lt : sv.toNat < s.core.cur_vars := fid_bv64_lt_of_mod_lt hcv_30 ‹_›
        have hsv_fl : sv.toNat < sb.core.flags.length :=
          hsb_len.core_ok.flags_len.symm ▸ Nat.lt_of_lt_of_le hsv_lt hcv_le
        have hsv_mv : sv.toNat < c.max_vars := Nat.lt_of_lt_of_le hsv_lt hcv_le
        have hsv_sc : sv.toNat < sb.scratch.score.length :=
          hsb_len.scratch_ok.score_len.symm ▸ hsv_mv
        have hsvp1 := fid_bv64_add1_toNat hcv_30 hsv_lt
        c0_hsteps_nogrp
        refine wp_join_group (ts := [])
          (fun _ m_bn => ∃ (sb' : FullState) (wlb' wrb' : FidArr64 c.max_vars),
            sb'.core = s.core ∧ sb'.LengthsOk c ∧ FullExtScratchPres s sb' ∧
            (FidReorderMem c sb' wlb' wrb' ⋆ R) m_bn)
          (fun _ _ m_bn ⟨sb', wlb', wrb', hsb'_core, hsb'_len, hsb'_ext, hmbn⟩ => by
            dsimp only [Blocks.get]; c0_hsteps
            exact hJb (sv + 1#64) m_bn hsvp1.2.2
              ⟨hsvp1.2.1, sb', wlb', wrb', hsb'_core, hsb'_len, hsb'_ext, hmbn⟩)
          (fun Jbs hJbs => ?_)
        c0_hsplit
        · c0_hsplit
          · c0_hsteps_nogrp
            refine wp_join_group (ts := [i64]) (fun _ mad => mad = m_b) ?_ ?_
            · rintro _ ⟨ad1, _⟩ mad hmad
              subst mad; c0_hsteps_nogrp
              refine wp_join_group (ts := [i64]) (fun _ mad2 => mad2 = m_b) ?_ ?_
              · rintro _ ⟨ad2, _⟩ mad2 hmad2
                subst mad2; c0_hsteps_nogrp
                refine wp_join_group (ts := [i64]) (fun _ mnsc => mnsc = m_b) ?_ ?_
                · rintro _ ⟨nsc, _⟩ mnsc hmnsc
                  subst mnsc; c0_hsteps_nogrp
                  let sb1 : FullState :=
                    { sb with scratch :=
                      { sb.scratch with score :=
                        sb.scratch.score.set sv.toNat nsc } }
                  have hlen1 : sb1.LengthsOk c := ⟨hsb_len.core_ok,
                    { hsb_len.scratch_ok with
                      score_len := by simp [sb1, hsb_len.scratch_ok.score_len] }⟩
                  have hext1' : FullExtScratchPres s sb1 := ⟨hsb_ext.1, hsb_ext.2⟩
                  obtain ⟨tmk1, trc1, htmk1, htrc1, hmF1'⟩ :=
                    fid_fullMem_of_reorderMem (s := sb1) (wl := wlb) (wr := wrb)
                      (by assumption)
                  let sb1F : FullState := { sb1 with scratch :=
                    { sb1.scratch with tarjan_mark := tmk1, tarjan_reach := trc1 } }
                  have hlen1F : sb1F.LengthsOk c := ⟨hlen1.core_ok,
                    { hlen1.scratch_ok with
                      tarjan_mark_len := htmk1, tarjan_reach_len := htrc1 }⟩
                  have hext1F : FullExtScratchPres s sb1F := hext1'
                  c0_call hHeapUp
                  refine ⟨c, sb1F, R, rfl, hlen1F, hmF1',
                    fun _ sb2F m_b' hsb2_core hsb2_len hsb2_p hmF2' => ?_⟩
                  obtain ⟨wlb2, wrb2, hm_b2⟩ := fid_reorderMem_of_fullMem hsb2_len hmF2'
                  have hsb2_ce : sb2F.core = sb.core := hsb2_core
                  c0_hsteps
                  exact hJbs () m_b' ⟨sb2F, wlb2, wrb2,
                    hsb2_ce.trans hsb_core, hsb2_len,
                    fid_bv64_ext_pres_heap hext1F hsb2_p.1.1, hm_b2⟩
                · intro Jn hJn
                  c0_hsplit <;> (c0_hsteps; exact hJn (_, ()) m_b rfl)
              · intro Ja2 hJa2
                c0_hsplit <;> (c0_hsteps; exact hJa2 (_, ()) m_b rfl)
            · intro Ja1 hJa1
              c0_hsplit <;> (c0_hsteps; exact hJa1 (_, ()) m_b rfl)
          · c0_hsteps; exact hJbs () m_b ⟨sb, wlb, wrb, hsb_core, hsb_len, hsb_ext, hmb⟩
        · c0_hsteps; exact hJbs () m_b ⟨sb, wlb, wrb, hsb_core, hsb_len, hsb_ext, hmb⟩
      · obtain ⟨tmkF, trcF, htmkF, htrcF, hmFF⟩ := fid_fullMem_of_reorderMem hmb
        let sbF : FullState :=
          { sb with scratch := { sb.scratch with tarjan_mark := tmkF, tarjan_reach :=
            trcF } }
        have hlenF : sbF.LengthsOk c := ⟨hsb_len.core_ok, { hsb_len.scratch_ok with
          tarjan_mark_len := htmkF, tarjan_reach_len := htrcF }⟩
        c0_hsteps; exact hQ' _ _ ⟨sbF, hsb_core, hlenF, hsb_ext, hmFF⟩
    · intro Jsr hJsr; c0_hsplit <;> (c0_hsteps; exact hJsr (_, ()) mF1 rfl)

private theorem fid_queue_phase2_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    {c : FullCfg} {s s6 : FullState} {R : Mem 64 → Prop} {wl6 wr6 : FidArr64 c.max_vars}
    {n : BitVec 64} {m6 : Mem 64}
    (hlen : s.LengthsOk c)
    (hQ' : ∀ r m', FidQueuePostOk c s R m' → Q r m')
    (hcv_le : s.core.cur_vars ≤ c.max_vars)
    (hcv_30 : s.core.cur_vars < 2 ^ 30)
    (hn_cv : n.toNat ≤ s.core.cur_vars)
    (hn_29 : n.toNat < 2 ^ 30)
    (hs6_eq : FidSiftWsortEq s s6)
    (hws6_len : s6.scratch.wsort.length = s.scratch.wsort.length)
    (hwb6 : FidWsortBounded s6.scratch.wsort n.toNat s.core.cur_vars)
    (hm6 : (FidReorderMem c s6 wl6 wr6 ⋆ R) m6) :
    wp Γ Q X (fidPhase2Step c.hdr n (BitVec.ofNat 64 s.core.cur_vars) c.pVals c.pWsort
      c.pQPrev c.pQNext c.pQStamp) m6 := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_ws : s.core.cur_vars ≤ 2 * c.max_vars :=
    Nat.le_trans hcv_le (Nat.le_mul_of_pos_left _ (by decide))
  unfold fidPhase2Step; dsimp only [fidCmp]
  obtain ⟨s7, hs7, hmF7⟩ := fidQueueRelinkOk_of_reorder hlen hs6_eq hws6_len hwb6 hm6
  c0_hsteps_nogrp
  -- Loop 7b: zero q_prev, q_next, q_stamp
  refine wp_while_state1 (fun i : BitVec 64 => i) (fun i => s.core.cur_vars - i.toNat)
    (fun i m7 => i.toNat ≤ s.core.cur_vars ∧ ∃ s7' : FullState,
      FidQueueRelinkOk c s s7' n.toNat ∧ (FullMem c s7' ⋆ R) m7)
    (fun J7 hJ7 => by c0_hsteps; exact hJ7 0#64 m6 ⟨Nat.zero_le _, s7, hs7, hmF7⟩)
    (fun J7 i m7 ⟨hi7, s7', hs7', hm7⟩ hJ7 => ?_)
  have h7len := fidQueueRelinkOk_lengths hs7'
  c0_hsplit
  · have hi7_lt : i.toNat < s.core.cur_vars := fid_bv64_lt_of_mod_lt hcv_30 ‹_›
    have hi7_mv : i.toNat < c.max_vars := Nat.lt_of_lt_of_le hi7_lt hcv_le
    have hi7_qp : i.toNat < s7'.scratch.q_prev.length := h7len.2.2.2.1.symm ▸ hi7_mv
    have hi7_qn : i.toNat < s7'.scratch.q_next.length := h7len.2.2.2.2.1.symm ▸ hi7_mv
    have hi7_qs : i.toNat < s7'.scratch.q_stamp.length := h7len.2.2.2.2.2.symm ▸ hi7_mv
    have hi7p1 := fid_bv64_add1_toNat hcv_30 hi7_lt
    c0_hsteps
    exact hJ7 (i + 1#64) _ hi7p1.2.2
      ⟨hi7p1.2.1, _, fidQueueRelinkOk_set_qstamp (fidQueueRelinkOk_set_qnext
        (fidQueueRelinkOk_set_qprev hs7' _ _) _ _) _ _, by assumption⟩
  · c0_hsplit
    · c0_hsteps
      exact hQ' (0#64, ()) _ (fidQueueRelinkOk_to_post
        (fidQueueRelinkOk_set_qcurstamp (fidQueueRelinkOk_set_qsstamp
          (fidQueueRelinkOk_set_qsidx (fidQueueRelinkOk_set_qlast
            (fidQueueRelinkOk_set_qfirst hs7' _) _) _) _) _) (by assumption))
    · have hn_pos : 0 < n.toNat := fid_bv64_pos_of_ne_zero ‹_›
      have hn1_p := fid_bv64_sub1_toNat hn_29 (le_refl _) hn_pos
      refine wp_while_state (fun p : BitVec 64 × BitVec 64 × BitVec 64 × PUnit => p)
        (fun p => n.toNat - p.2.2.1.toNat)
        (fun p m8 => p.2.2.1.toNat ≤ n.toNat ∧ ∃ s8 : FullState,
          FidQueueRelinkOk c s s8 n.toNat ∧ (FullMem c s8 ⋆ R) m8)
        (fun J8 hJ8 => by
          c0_hsteps; exact hJ8 (4294967295#64, 0#64, 0#64, ()) m7
            ⟨Nat.zero_le _, s7', hs7', hm7⟩)
        (fun J8 ⟨bidx, bstamp, i, ⟨⟩⟩ m8 ⟨hi, s8, hs8, hm8⟩ hJ8 => ?_)
      have h8len := fidQueueRelinkOk_lengths hs8
      c0_hsplit
      · have hi_nat : i.toNat < n.toNat := ‹_›
        have hi_ws : i.toNat < s8.scratch.wsort.length :=
          h8len.2.2.1.symm ▸ Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hi_nat hn_cv) hcv_ws
        have hv_lt : (s8.scratch.wsort[i.toNat]'hi_ws).toNat < s.core.cur_vars :=
          fidQueueRelinkOk_wsort_get hs8 hi_nat hi_ws
        have hv_mv : (BitVec.setWidth 64 (s8.scratch.wsort[i.toNat]'hi_ws)).toNat < c.max_vars :=
          fid_zext64_32_lt_of_lt (Nat.lt_of_lt_of_le hv_lt hcv_le)
        have hip1 := fid_bv64_add1_toNat hn_29 hi_nat
        c0_hsteps_nogrp
        refine wp_join_group (ts := [i32])
          (fun _ m8' => ∃ s8' : FullState,
            FidQueueRelinkOk c s s8' n.toNat ∧ (FullMem c s8' ⋆ R) m8')
          (fun _ _ m8' ⟨s8', hs8', hm8'⟩ => ?_)
          (fun Jp hJp => by
            c0_hsplit
            · have hi_pos : 0 < i.toNat := ‹_›
              have hi1_p := fid_bv64_sub1_toNat hn_29 (Nat.le_of_lt hi_nat) hi_pos
              have hi1_ws : (i - 1#64).toNat < s8.scratch.wsort.length :=
                h8len.2.2.1.symm ▸
                  Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hi1_p.2.2.2 hn_cv) hcv_ws
              c0_hsteps; exact hJp (_, ()) m8 ⟨s8, hs8, hm8⟩
            · c0_hsteps; exact hJp (_, ()) m8 ⟨s8, hs8, hm8⟩)
        have h8' := fidQueueRelinkOk_lengths hs8'
        have hv_qp : (BitVec.setWidth 64 (s8.scratch.wsort[i.toNat]'hi_ws)).toNat <
            s8'.scratch.q_prev.length := h8'.2.2.2.1.symm ▸ hv_mv
        c0_hsteps_nogrp
        refine wp_join_group (ts := [i32])
          (fun _ m8'' => ∃ s8'' : FullState,
            FidQueueRelinkOk c s s8'' n.toNat ∧ (FullMem c s8'' ⋆ R) m8'')
          (fun _ _ m8'' ⟨s8'', hs8'', hm8''⟩ => ?_)
          (fun Jn hJn => by
            c0_hsplit
            · have hi1_ws : (i + 1#64).toNat < s8'.scratch.wsort.length :=
                h8'.2.2.1.symm ▸ Nat.lt_of_lt_of_le
                  (Nat.lt_of_lt_of_le ‹(i + 1#64).toNat < n.toNat› hn_cv) hcv_ws
              c0_hsteps
              exact hJn (_, ()) _ ⟨_, fidQueueRelinkOk_set_qprev hs8' _ _, by assumption⟩
            · c0_hsteps
              exact hJn (_, ()) _ ⟨_, fidQueueRelinkOk_set_qprev hs8' _ _, by assumption⟩)
        have h8'' := fidQueueRelinkOk_lengths hs8''
        have hv_qn : (BitVec.setWidth 64 (s8.scratch.wsort[i.toNat]'hi_ws)).toNat <
            s8''.scratch.q_next.length := h8''.2.2.2.2.1.symm ▸ hv_mv
        have hv_qs : (BitVec.setWidth 64 (s8.scratch.wsort[i.toNat]'hi_ws)).toNat <
            s8''.scratch.q_stamp.length := h8''.2.2.2.2.2.symm ▸ hv_mv
        c0_hsteps_nogrp
        refine wp_join_group (ts := [i64, i64])
          (fun _ m9 => ∃ s9 : FullState,
            FidQueueRelinkOk c s s9 n.toNat ∧ (FullMem c s9 ⋆ R) m9)
          (fun _ ⟨nbi, nbs, ⟨⟩⟩ m9 ⟨s9, hs9, hm9⟩ => by
            dsimp only [Blocks.get]; c0_hsteps
            exact hJ8 (nbi, nbs, i + 1#64, ()) m9 hip1.2.2 ⟨hip1.2.1, s9, hs9, hm9⟩)
          (fun Jb hJb => ?_)
        have hv_v0 : ((BitVec.setWidth 64 (s8.scratch.wsort[i.toNat]'hi_ws)) <<<
            (1 : BitVec 64)).toNat < s8''.core.vals.length :=
          h8''.2.1.symm ▸ fid_shl1_mul2_bv_lt hv_mv hmx
        have hv_v0n : ((BitVec.setWidth 64 (s8.scratch.wsort[i.toNat]'hi_ws)) <<<
            (1 : Nat)).toNat < s8''.core.vals.length :=
          h8''.2.1.symm ▸ fid_shl1_mul2_nat_lt hv_mv hmx
        c0_hsteps_nogrp; c0_hsplit
        · c0_hsteps; exact hJb (_, _, ()) _
            ⟨_, fidQueueRelinkOk_set_qstamp (fidQueueRelinkOk_set_qnext hs8'' _ _) _ _,
             by assumption⟩
        · c0_hsteps; exact hJb (_, _, ()) _
            ⟨_, fidQueueRelinkOk_set_qstamp (fidQueueRelinkOk_set_qnext hs8'' _ _) _ _,
             by assumption⟩
      · have hn_ws0 : 0 < s8.scratch.wsort.length :=
          h8len.2.2.1.symm ▸ Nat.lt_of_lt_of_le hn_pos (Nat.le_trans hn_cv hcv_ws)
        have hn_wsl : (n - 1#64).toNat < s8.scratch.wsort.length :=
          h8len.2.2.1.symm ▸ Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hn1_p.2.2.2 hn_cv) hcv_ws
        c0_hsteps_nogrp
        refine wp_join_group (ts := [i64, i64])
          (fun _ m9 => ∃ s9 : FullState,
            FidQueueRelinkOk c s s9 n.toNat ∧ (FullMem c s9 ⋆ R) m9)
          (fun _ _ m9 ⟨s9, hs9, hm9⟩ => by
            try dsimp only [Blocks.get]
            c0_hsteps
            exact hQ' (n, ()) _ (fidQueueRelinkOk_to_post
              (fidQueueRelinkOk_set_qsstamp (fidQueueRelinkOk_set_qsidx hs9 _) _)
              (by assumption)))
          (fun Jf hJf => ?_)
        c0_hsplit
        · have hv_lt : (s8.scratch.wsort[(n - 1#64).toNat]'hn_wsl).toNat < s.core.cur_vars :=
            fidQueueRelinkOk_wsort_get hs8 hn1_p.2.2.2 hn_wsl
          have hqlast_qs : (BitVec.setWidth 64
              (s8.scratch.wsort[(n - 1#64).toNat]'hn_wsl)).toNat <
              s8.scratch.q_stamp.length := h8len.2.2.2.2.2.symm ▸
                fid_zext64_32_lt_of_lt (Nat.lt_of_lt_of_le hv_lt hcv_le)
          c0_hsteps
          exact hJf (_, _, ()) _ ⟨_, fidQueueRelinkOk_hdr3 hs8 _ _ _, by assumption⟩
        · c0_hsteps
          exact hJf (_, _, ()) _ ⟨_, fidQueueRelinkOk_hdr3 hs8 _ _ _, by assumption⟩

private theorem fid_queue_focus_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {wl4 wr4 : FidArr64 c.max_vars}
    {m4 : Mem 64}
    (hSift : EnvSpec Γ "full_reorder_sift_fid" fidReorderSiftSpec)
    (hlen : s.LengthsOk c)
    (hcv_le : s.core.cur_vars ≤ c.max_vars)
    (hcv_29 : s.core.cur_vars < 2 ^ 29)
    (hcv_30 : s.core.cur_vars < 2 ^ 30)
    (hflags_len : s.core.flags.length = c.max_vars)
    (hm4 : (FidReorderMem c s wl4 wr4 ⋆ R) m4)
    (k : Val i64 → Expr Val Cont [i64])
    (hk : ∀ (n : BitVec 64) (s6 : FullState) (wl6 wr6 : FidArr64 c.max_vars) (m6 : Mem 64),
      n.toNat ≤ s.core.cur_vars → n.toNat < 2 ^ 30 → FidSiftWsortEq s s6 →
      s6.scratch.wsort.length = s.scratch.wsort.length →
      FidWsortBounded s6.scratch.wsort n.toNat s.core.cur_vars →
      (FidReorderMem c s6 wl6 wr6 ⋆ R) m6 → wp Γ Q X (k n) m6) :
    wp Γ Q X (fidFocusWrap c.hdr (BitVec.ofNat 64 s.core.cur_vars) c.pFlags c.pWsort k)
      m4 := by
  have hws_len := hlen.scratch_ok.wsort_len
  unfold fidFocusWrap; dsimp only [fidCmp]
  refine wp_while_state (fun p : BitVec 64 × BitVec 64 × PUnit => p)
    (fun p => s.core.cur_vars - p.2.1.toNat)
    (fun p m5 => p.2.1.toNat ≤ s.core.cur_vars ∧ p.1.toNat ≤ p.2.1.toNat ∧
      ∃ (s5 : FullState) (wl5 wr5 : FidArr64 c.max_vars),
        FidSiftWsortEq s s5 ∧ s5.scratch.wsort.length = s.scratch.wsort.length ∧
        FidWsortBounded s5.scratch.wsort p.1.toNat s.core.cur_vars ∧
        (FidReorderMem c s5 wl5 wr5 ⋆ R) m5)
    (fun J5 hJ5 => by
      c0_hsteps; exact hJ5 (0#64, 0#64, ()) m4 ⟨Nat.zero_le _, Nat.zero_le _, s, wl4, wr4,
        fidSiftWsortEq_refl s, rfl, fun _ h => absurd h (Nat.not_lt_zero _), hm4⟩)
    (fun J5 ⟨n, v, ⟨⟩⟩ m5 ⟨hv, hn_le, s5, wl5, wr5, hs5_eq, hws5_len, hwb5, hm5⟩ hJ5 => ?_)
  c0_hsplit
  · have hv_lt : v.toNat < s.core.cur_vars := fid_bv64_lt_of_mod_lt hcv_30 ‹_›
    have hv_fl : v.toNat < s5.core.flags.length :=
      (fidSiftWsortEq_flags hs5_eq).symm ▸ hflags_len.symm ▸ Nat.lt_of_lt_of_le hv_lt hcv_le
    have hvp1 := fid_bv64_add1_toNat hcv_30 hv_lt
    have hn_lt : n.toNat < s.core.cur_vars := Nat.lt_of_le_of_lt hn_le hv_lt
    have hnp1 := fid_bv64_add1_toNat hcv_30 hn_lt
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64])
      (fun n' m5' => n'.1.toNat ≤ v.toNat + 1 ∧ ∃ (s5' : FullState),
        FidSiftWsortEq s s5' ∧ s5'.scratch.wsort.length = s.scratch.wsort.length ∧
        FidWsortBounded s5'.scratch.wsort n'.1.toNat s.core.cur_vars ∧
        (FidReorderMem c s5' wl5 wr5 ⋆ R) m5')
      (fun _ ⟨n', ⟨⟩⟩ m5' ⟨hn', s5', hs5', hlen5', hwb5', hm5'⟩ => by
        dsimp only [Blocks.get]; c0_hsteps
        exact hJ5 (n', v + 1#64, ()) m5' hvp1.2.2
          ⟨hvp1.2.1, hvp1.1 ▸ hn', s5', wl5, wr5, hs5', hlen5', hwb5', hm5'⟩)
      (fun Jc hJc => ?_)
    c0_hsplit
    · have hn_ws : n.toNat < s5.scratch.wsort.length :=
        hws5_len.symm ▸ hws_len.symm ▸ Nat.lt_of_lt_of_le hn_lt
          (Nat.le_trans hcv_le (Nat.le_mul_of_pos_left _ (by decide)))
      have hv_cv : (BitVec.setWidth 32 v).toNat < s.core.cur_vars := by
        have : v.toNat < 2 ^ 32 := lt_trans hv_lt (lt_trans hcv_29 (by decide))
        have hz : (BitVec.setWidth 32 v).toNat = v.toNat := by bv_omega
        omega
      c0_hsteps
      refine hJc (n + 1#64, ()) _
        ⟨Nat.le_trans (Nat.le_of_eq hnp1.1) (Nat.succ_le_succ hn_le),
         { s5 with scratch := { s5.scratch with
             wsort := s5.scratch.wsort.set n.toNat (BitVec.setWidth 32 v) } },
         fidSiftWsortEq_set hs5_eq _, by simp [hws5_len],
         hnp1.1 ▸ fidWsortBounded_push hwb5 hn_ws hv_cv, ?_⟩
      assumption
    · c0_hsteps; exact hJc (n, ()) m5
        ⟨Nat.le_trans hn_le (Nat.le_succ _), s5, hs5_eq, hws5_len, hwb5, hm5⟩
  · have hn_cv : n.toNat ≤ s.core.cur_vars := Nat.le_trans hn_le hv
    have hn_29 : n.toNat < 2 ^ 30 := Nat.lt_of_le_of_lt hn_cv (lt_trans hcv_29 (by decide))
    have hcv_ws : s.core.cur_vars ≤ 2 * c.max_vars :=
      Nat.le_trans hcv_le (Nat.le_mul_of_pos_left _ (by decide))
    refine wp_join_group (ts := [])
      (fun _ m6 => ∃ (s6 : FullState) (wl6 wr6 : FidArr64 c.max_vars),
        FidSiftWsortEq s s6 ∧ s6.scratch.wsort.length = s.scratch.wsort.length ∧
        FidWsortBounded s6.scratch.wsort n.toNat s.core.cur_vars ∧
        (FidReorderMem c s6 wl6 wr6 ⋆ R) m6) ?_ ?_
    · rintro _ _ m6 ⟨s6, wl6, wr6, hs6_eq, hws6_len, hwb6, hm6⟩
      dsimp only [Blocks.get]
      exact hk n s6 wl6 wr6 m6 hn_cv hn_29 hs6_eq hws6_len hwb6 hm6
    · intro J6 hJ6; c0_hsplit
      · have hn_pos : 0 < n.toNat := Nat.lt_trans Nat.zero_lt_one ‹_›
        have hn1_p := fid_bv64_sub1_toNat hn_29 (le_refl _) hn_pos
        c0_hsteps_nogrp
        refine wp_while_state1 (fun i : BitVec 64 => i) (fun i => i.toNat)
          (fun i m6 => i.toNat ≤ n.toNat ∧ ∃ (s6 : FullState) (wl6 wr6 : FidArr64 c.max_vars),
            FidSiftWsortEq s s6 ∧ s6.scratch.wsort.length = s.scratch.wsort.length ∧
            FidWsortBounded s6.scratch.wsort n.toNat s.core.cur_vars ∧
            (FidReorderMem c s6 wl6 wr6 ⋆ R) m6)
          (fun J_bld hJ_bld => by
            c0_hsteps; exact hJ_bld (n >>> 1#64) m5 ⟨fid_bv64_ushr1_le (le_refl _),
              s5, wl5, wr5, hs5_eq, hws5_len, hwb5, hm5⟩)
          (fun J_bld i m6 ⟨hi, s6, wl6, wr6, hs6_eq, hws6_len, hwb6, hm6⟩ hJ_bld => ?_)
        c0_hsplit
        · have hip := fid_bv64_sub1_toNat hn_29 hi ‹_›
          c0_hsteps_nogrp; apply fid_wp_call_spec hSift
          refine ⟨c, s6, wl6, wr6, R, rfl, fidSiftWsortEq_lengthsOk hlen hs6_eq hws6_len,
            (by change FidWsortBounded s6.scratch.wsort n.toNat s6.core.cur_vars
                rw [fidSiftWsortEq_curVars hs6_eq]; exact hwb6),
            hm6, fun ws' m6' hwl' hwb' _ hm6' => ?_⟩
          c0_hsteps
          exact hJ_bld (i - 1#64) m6' hip.2.1
            ⟨hip.2.2.1, { s6 with scratch := { s6.scratch with wsort := ws' } },
             wl6, wr6, fidSiftWsortEq_set hs6_eq ws', hwl'.trans hws6_len,
             (by change FidWsortBounded ws' n.toNat s.core.cur_vars
                 rw [← fidSiftWsortEq_curVars hs6_eq]; exact hwb'), hm6'⟩
        · refine wp_while_state1 (fun e : BitVec 64 => e) (fun e => e.toNat)
            (fun e m7 => e.toNat ≤ n.toNat ∧ ∃ (s7 : FullState) (wl7 wr7 : FidArr64 c.max_vars),
              FidSiftWsortEq s s7 ∧ s7.scratch.wsort.length = s.scratch.wsort.length ∧
              FidWsortBounded s7.scratch.wsort n.toNat s.core.cur_vars ∧
              (FidReorderMem c s7 wl7 wr7 ⋆ R) m7)
            (fun J_pop hJ_pop => by
              c0_hsteps; exact hJ_pop n m6 ⟨le_refl _, s6, wl6, wr6,
                hs6_eq, hws6_len, hwb6, hm6⟩)
            (fun J_pop e m7 ⟨he, s7, wl7, wr7, hs7_eq, hws7_len, hwb7, hm7⟩ hJ_pop => ?_)
          c0_hsplit
          · have he_pos : 0 < e.toNat := Nat.lt_trans Nat.zero_lt_one ‹_›
            have hep := fid_bv64_sub1_toNat hn_29 he he_pos
            have he1_n : (e - 1#64).toNat < n.toNat := Nat.lt_of_lt_of_le hep.2.1 he
            have h0_ws : 0 < s7.scratch.wsort.length :=
              hws7_len.symm ▸ hws_len.symm ▸
                Nat.lt_of_lt_of_le hn_pos (Nat.le_trans hn_cv hcv_ws)
            have he_ws : (e - 1#64).toNat < s7.scratch.wsort.length :=
              hws7_len.symm ▸ hws_len.symm ▸
                Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le he1_n hn_cv) hcv_ws
            have hv0_lt : (s7.scratch.wsort[0]'h0_ws).toNat < s.core.cur_vars :=
              fidWsortBounded_get hwb7 hn_pos h0_ws
            have hve_lt : (s7.scratch.wsort[(e - 1#64).toNat]'he_ws).toNat < s.core.cur_vars :=
              fidWsortBounded_get hwb7 he1_n he_ws
            have he_ws' : (e - 1#64).toNat <
                (s7.scratch.wsort.set 0 (s7.scratch.wsort[(e - 1#64).toNat]'he_ws)).length := by
              simpa using he_ws
            c0_hsteps_nogrp
            let ws_sw := (s7.scratch.wsort.set 0
              (s7.scratch.wsort[(e - 1#64).toNat]'he_ws)).set
              (e - 1#64).toNat (s7.scratch.wsort[0]'h0_ws)
            have hwb_sw : FidWsortBounded ws_sw n.toNat s.core.cur_vars :=
              fidWsortBounded_swap hwb7 hve_lt hv0_lt
            apply fid_wp_call_spec hSift
            refine ⟨c, { s7 with scratch := { s7.scratch with wsort := ws_sw } },
              wl7, wr7, R, rfl,
              fidSiftWsortEq_lengthsOk hlen (fidSiftWsortEq_set hs7_eq ws_sw)
                (by simpa [ws_sw] using hws7_len),
              (by change FidWsortBounded ws_sw (e - 1#64).toNat s7.core.cur_vars
                  rw [fidSiftWsortEq_curVars hs7_eq]
                  exact fidWsortBounded_shrink hwb_sw (Nat.le_of_lt he1_n)),
              by assumption, fun ws' m7' hwl' hwb' hpres' hm7' => ?_⟩
            c0_hsteps
            exact hJ_pop (e - 1#64) m7' hep.2.1
              ⟨Nat.le_of_lt he1_n, { s7 with scratch := { s7.scratch with wsort := ws' } },
               wl7, wr7, fidSiftWsortEq_set hs7_eq ws',
               (hwl'.trans (by simp only [ws_sw, List.length_set])).trans hws7_len,
               fidWsortBounded_lift hwb_sw
                 (by change FidWsortBounded ws' (e - 1#64).toNat s.core.cur_vars
                     rw [← fidSiftWsortEq_curVars hs7_eq]; exact hwb')
                 hpres', hm7'⟩
          · c0_hsteps; exact hJ6 () m7 ⟨s7, wl7, wr7, hs7_eq, hws7_len, hwb7, hm7⟩
      · c0_hsteps; exact hJ6 () m5 ⟨s5, wl5, wr5, hs5_eq, hws5_len, hwb5, hm5⟩

private theorem fid_queue_post4_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {wl4 wr4 : FidArr64 c.max_vars}
    {m4 : Mem 64}
    (hRescale : EnvSpec Γ "full_rescale" fullRescaleSpec)
    (hHeapUp : EnvSpec Γ "full_heap_up" fullHeapUpSpec)
    (hSift : EnvSpec Γ "full_reorder_sift_fid" fidReorderSiftSpec)
    (hlen : s.LengthsOk c)
    (hQ' : ∀ r m', FidQueuePostOk c s R m' → Q r m')
    (hcv_le : s.core.cur_vars ≤ c.max_vars)
    (hcv_29 : s.core.cur_vars < 2 ^ 29)
    (hcv_30 : s.core.cur_vars < 2 ^ 30)
    (hflags_len : s.core.flags.length = c.max_vars)
    (hm4 : (FidReorderMem c s wl4 wr4 ⋆ R) m4) :
    wp Γ Q X (fidPost4Wrap c.hdr
      (fidStableBody c.hdr (BitVec.ofNat 64 s.core.cur_vars) c.pFlags c.pTarjanMark)
      (fidFocusWrap c.hdr (BitVec.ofNat 64 s.core.cur_vars) c.pFlags c.pWsort
        (fun n => fidPhase2Step c.hdr n (BitVec.ofNat 64 s.core.cur_vars)
          c.pVals c.pWsort c.pQPrev c.pQNext c.pQStamp))) m4 := by
  unfold fidPost4Wrap; dsimp only [fidCmp]
  c0_hsteps_nogrp
  c0_hsplit
  · exact fid_queue_stable_wp hRescale hHeapUp hlen hQ' hcv_le hcv_30 hm4
  · refine fid_queue_focus_wp hSift hlen hcv_le hcv_29 hcv_30 hflags_len hm4 _ ?_
    intro n s6 wl6 wr6 m6 hn_cv hn_29 hs6_eq hws6_len hwb6 hm6
    exact fid_queue_phase2_wp hlen hQ' hcv_le hcv_30 hn_cv hn_29 hs6_eq hws6_len hwb6 hm6

private theorem fid_queue_loop4_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {wl3 wr3 : FidArr64 c.max_vars}
    {m3 : Mem 64}
    (hcv_le : s.core.cur_vars ≤ c.max_vars)
    (hcv_30 : s.core.cur_vars < 2 ^ 30)
    (hm3 : (FidReorderMem c s wl3 wr3 ⋆ R) m3)
    {k : Expr Val Cont [i64]}
    (hk : ∀ wl4 wr4 m4, (FidReorderMem c s wl4 wr4 ⋆ R) m4 → wp Γ Q X k m4) :
    wp Γ Q X (fidLoop4Wrap (BitVec.ofNat 64 s.core.cur_vars)
      c.pTarjanMark c.pTarjanReach k) m3 := by
  unfold fidLoop4Wrap; dsimp only [fidCmp]
  refine wp_while_state1 (fun v : BitVec 64 => v) (fun v => s.core.cur_vars - v.toNat)
    (fun v m4 => v.toNat ≤ s.core.cur_vars ∧
      ∃ wl4 wr4 : FidArr64 c.max_vars, (FidReorderMem c s wl4 wr4 ⋆ R) m4)
    (fun J4 hJ4 => by c0_hsteps; exact hJ4 0#64 m3 ⟨Nat.zero_le _, wl3, wr3, hm3⟩)
    (fun J4 v m4 ⟨hv, wl4, wr4, hm4⟩ hJ4 => ?_)
  c0_hsplit
  · have hv_lt : v.toNat < s.core.cur_vars := fid_bv64_lt_of_mod_lt hcv_30 ‹_›
    have hv_mv : v.toNat < c.max_vars := Nat.lt_of_lt_of_le hv_lt hcv_le
    have hvp1 := fid_bv64_add1_toNat hcv_30 hv_lt
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i64]) (fun _ m' => m' = m4)
      (fun _ _ m4' hm_eq => by
        subst m4'; dsimp only [Blocks.get]; c0_hsteps
        exact hJ4 (v + 1#64) _ hvp1.2.2 ⟨hvp1.2.1, _, _, by assumption⟩)
      (fun Jf hJf => by c0_hsteps; all_goals exact hJf _ m4 rfl)
  · exact hk wl4 wr4 m4 hm4

private theorem fid_queue_loop34_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {wl2 wr2 : FidArr64 c.max_vars}
    {m2 : Mem 64}
    (hRescale : EnvSpec Γ "full_rescale" fullRescaleSpec)
    (hHeapUp : EnvSpec Γ "full_heap_up" fullHeapUpSpec)
    (hSift : EnvSpec Γ "full_reorder_sift_fid" fidReorderSiftSpec)
    (hlen : s.LengthsOk c)
    (hQ' : ∀ r m', FidQueuePostOk c s R m' → Q r m')
    (hcv_le : s.core.cur_vars ≤ c.max_vars)
    (hcv_29 : s.core.cur_vars < 2 ^ 29)
    (hcv_30 : s.core.cur_vars < 2 ^ 30)
    (h2cv_le : 2 * s.core.cur_vars ≤ 2 * c.max_vars)
    (h2cv_30 : 2 * s.core.cur_vars < 2 ^ 30)
    (hvals_2cv : 2 * s.core.cur_vars ≤ s.core.vals.length)
    (hflags_len : s.core.flags.length = c.max_vars)
    (hwlen_29 : s.core.wlen < 2 ^ 29)
    (hwlen_stk : s.core.wlen ≤ s.core.wstk.length)
    (hwvec_len : s.core.wvec.length = 4 * c.max_vars)
    (hm2 : (FidReorderMem c s wl2 wr2 ⋆ R) m2) :
    wp Γ Q X (fidLoop34Expr c.hdr (BitVec.ofNat 64 s.core.cur_vars)
      (BitVec.ofNat 64 s.core.cur_vars <<< 1#64) (BitVec.ofNat 64 s.core.wlen)
      c.pVals c.pFlags c.pWvec c.pWstk c.pWsort c.pQPrev c.pQNext c.pQStamp
      c.pTarjanMark c.pTarjanReach (1#64 <<< 40#64) (1#64 <<< 60#64)) m2 := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  conv => arg 4; whnf
  c0_hsteps_nogrp
  -- Loop 3: binary watches scan
  refine wp_while_state1 (fun lit : BitVec 64 => lit)
    (fun lit => 2 * s.core.cur_vars - lit.toNat)
    (fun lit m3 => lit.toNat ≤ 2 * s.core.cur_vars ∧
      ∃ wl3 wr3 : FidArr64 c.max_vars, (FidReorderMem c s wl3 wr3 ⋆ R) m3)
    (fun J3 hJ3 => by c0_hsteps; exact hJ3 0#64 m2 ⟨Nat.zero_le _, wl2, wr2, hm2⟩)
    (fun J3 lit m3 ⟨hlit, wl3, wr3, hm3⟩ hJ3 => ?_)
  c0_hsplit
  · have hlit_nat : lit.toNat < 2 * s.core.cur_vars := fid_bv64_lt_two_mul_mod hcv_29 ‹_›
    have hlit_2mx : lit.toNat < 2 * c.max_vars := Nat.lt_of_lt_of_le hlit_nat h2cv_le
    have hlit_vals : lit.toNat < s.core.vals.length := Nat.lt_of_lt_of_le hlit_nat hvals_2cv
    have hlit_v1 : (lit >>> (1 : BitVec 64)).toNat < s.core.flags.length :=
      hflags_len.symm ▸ Nat.lt_of_lt_of_le (fid_ushr1_bv_lt hlit_nat) hcv_le
    have hlit_v2 : (lit >>> (1 : Nat)).toNat < s.core.flags.length :=
      hflags_len.symm ▸ Nat.lt_of_lt_of_le (fid_ushr1_nat_lt hlit_nat) hcv_le
    have hlit_mv1 : (lit >>> (1 : BitVec 64)).toNat < c.max_vars :=
      Nat.lt_of_lt_of_le (fid_ushr1_bv_lt hlit_nat) hcv_le
    have hlit_mv2 : (lit >>> (1 : Nat)).toNat < c.max_vars :=
      Nat.lt_of_lt_of_le (fid_ushr1_nat_lt hlit_nat) hcv_le
    have hlit_w0 : (lit <<< (1 : BitVec 64)).toNat < s.core.wvec.length :=
      hwvec_len.symm ▸ fid_shl1_bv_lt hlit_2mx hmx
    have hlit_w0n : (lit <<< (1 : Nat)).toNat < s.core.wvec.length :=
      hwvec_len.symm ▸ fid_shl1_nat_lt hlit_2mx hmx
    have hlit_w1 : ((lit <<< (1 : BitVec 64)) + 1#64).toNat < s.core.wvec.length :=
      hwvec_len.symm ▸ fid_shl1_add1_bv_lt hlit_2mx hmx
    have hlit_w1n : ((lit <<< (1 : Nat)) + 1#64).toNat < s.core.wvec.length :=
      hwvec_len.symm ▸ fid_shl1_add1_nat_lt hlit_2mx hmx
    have hlitp1 := fid_bv64_add1_toNat h2cv_30 hlit_nat
    c0_hsteps_nogrp
    refine wp_join_group (ts := [])
      (fun _ m3' => ∃ wl3' wr3' : FidArr64 c.max_vars, (FidReorderMem c s wl3' wr3' ⋆ R) m3')
      (fun _ _ m3' ⟨wl3', wr3', hm3'⟩ => by
        dsimp only [Blocks.get]; c0_hsteps
        exact hJ3 (lit + 1#64) m3' hlitp1.2.2 ⟨hlitp1.2.1, wl3', wr3', hm3'⟩)
      (fun J_next hJ_next => ?_)
    c0_hsplit
    · c0_hsplit
      · c0_hsteps_nogrp
        refine wp_join_group (ts := [])
          (fun _ m3' =>
            ∃ wl3' wr3' : FidArr64 c.max_vars, (FidReorderMem c s wl3' wr3' ⋆ R) m3')
          (fun _ _ m3' hm3' => by dsimp only [Blocks.get]; c0_hsteps; exact hJ_next () m3' hm3')
          (fun J_next2 hJ_next2 => ?_)
        c0_hsplit
        · c0_hsplit
          · c0_hsplit
            · refine wp_join_group (ts := [i64])
                (fun _ m3' => ∃ wl3' wr3' :
                  FidArr64 c.max_vars, (FidReorderMem c s wl3' wr3' ⋆ R) m3')
                (fun _ _ m3' hm3' => by
                  dsimp only [Blocks.get]; c0_hsteps; exact hJ_next2 () m3' hm3')
                (fun J_aw hJ_aw => ?_)
              have hwe_le := (fid_we_le_wlen hwlen_29 ‹_› ‹_›).2
              have hwe_29 : ((BitVec.setWidth 64 s.core.wvec[2 * lit.toNat % 2 ^ 64]) +
                  (BitVec.setWidth 64 s.core.wvec[(2 * lit.toNat + 1) % 2 ^ 64])).toNat <
                  2 ^ 30 := Nat.lt_of_le_of_lt hwe_le (lt_trans hwlen_29 (by decide))
              refine wp_while_state1 (fun wi : BitVec 64 => wi)
                (fun wi => ((BitVec.setWidth 64 s.core.wvec[2 * lit.toNat % 2 ^ 64]) +
                  (BitVec.setWidth 64 s.core.wvec[(2 * lit.toNat + 1) % 2 ^ 64])).toNat -
                  wi.toNat)
                (fun _ m4 =>
                  ∃ wl4 wr4 : FidArr64 c.max_vars, (FidReorderMem c s wl4 wr4 ⋆ R) m4)
                (fun J_wi hJ_wi => by c0_hsteps; exact hJ_wi _ m3 ⟨wl3, wr3, hm3⟩)
                (fun J_wi wi m4 ⟨wl4, wr4, hm4⟩ hJ_wi => ?_)
              c0_hsplit
              · have hwi_we : wi.toNat <
                    ((BitVec.setWidth 64 s.core.wvec[2 * lit.toNat % 2 ^ 64]) +
                      (BitVec.setWidth 64 s.core.wvec[(2 * lit.toNat + 1) % 2 ^ 64])).toNat := by
                  dsimp only [lift2, Arg.val] at *; exact ‹_›
                have hwi_stk : wi.toNat < s.core.wstk.length :=
                  Nat.lt_of_lt_of_le hwi_we (Nat.le_trans hwe_le hwlen_stk)
                c0_hsteps_nogrp; c0_hsplit
                · c0_hsteps; exact hJ_wi (wi + 2#64) m4 (fid_bv64_add2_sub_lt hwe_29 hwi_we)
                    ⟨wl4, wr4, hm4⟩
                · c0_hsteps; exact hJ_aw (wi, ()) m4 ⟨wl4, wr4, hm4⟩
                · refine wp_join_group (ts := [])
                    (fun _ m4' => ∃ wl4' wr4' : FidArr64 c.max_vars,
                      (FidReorderMem c s wl4' wr4' ⋆ R) m4')
                    (fun _ _ m4' ⟨wl4', wr4', hm4'⟩ => by
                      dsimp only [Blocks.get]; c0_hsteps
                      exact hJ_wi (wi + 1#64) m4' (fid_bv64_add1_sub_lt hwe_29 hwi_we)
                        ⟨wl4', wr4', hm4'⟩)
                    (fun J_cont hJ_cont => ?_)
                  c0_hsplit
                  · c0_hsplit
                    · have hother_lt : (BitVec.setWidth 64
                          (s.core.wstk[wi.toNat]'hwi_stk &&& 2147483647#32)).toNat <
                          2 * s.core.cur_vars := fid_bv64_lt_shl1_ofNat hcv_29 ‹_›
                      have hov_vals : (BitVec.setWidth 64
                          (s.core.wstk[wi.toNat]'hwi_stk &&& 2147483647#32)).toNat <
                          s.core.vals.length := Nat.lt_of_lt_of_le hother_lt hvals_2cv
                      have hov_fl1 : (BitVec.setWidth 64
                          ((s.core.wstk[wi.toNat]'hwi_stk &&& 2147483647#32) >>>
                            (1 : BitVec 32))).toNat < s.core.flags.length :=
                        hflags_len.symm ▸
                          Nat.lt_of_lt_of_le (fid_zext32_bv32_ushr1_bv_lt hother_lt) hcv_le
                      have hov_fl2 : (BitVec.setWidth 64
                          ((s.core.wstk[wi.toNat]'hwi_stk &&& 2147483647#32) >>>
                            (1 : Nat))).toNat < s.core.flags.length :=
                        hflags_len.symm ▸
                          Nat.lt_of_lt_of_le (fid_zext32_bv32_ushr1_lt hother_lt) hcv_le
                      have hov_mv1 : ((BitVec.setWidth 64
                          (s.core.wstk[wi.toNat]'hwi_stk &&& 2147483647#32)) >>>
                            (1 : BitVec 64)).toNat < c.max_vars :=
                        Nat.lt_of_lt_of_le (fid_zext32_ushr1_lt hother_lt) hcv_le
                      have hov_mv2 : ((BitVec.setWidth 64
                          (s.core.wstk[wi.toNat]'hwi_stk &&& 2147483647#32)) >>>
                            (1 : Nat)).toNat < c.max_vars :=
                        Nat.lt_of_lt_of_le (fid_zext32_ushr1_nat_lt hother_lt) hcv_le
                      c0_hsteps_nogrp
                      refine wp_join_group (ts := [])
                        (fun _ m4' => ∃ wl4' wr4' : FidArr64 c.max_vars,
                          (FidReorderMem c s wl4' wr4' ⋆ R) m4')
                        (fun _ _ m4' hm4' => by
                          dsimp only [Blocks.get]; c0_hsteps; exact hJ_cont () m4' hm4')
                        (fun J_nw hJ_nw => ?_)
                      c0_hsteps_nogrp; c0_hsplit
                      · refine wp_join_group (ts := [])
                          (fun _ m4' => ∃ wl4' wr4' : FidArr64 c.max_vars,
                            (FidReorderMem c s wl4' wr4' ⋆ R) m4')
                          (fun _ _ m4' ⟨wl4', wr4', hm4'⟩ => by
                            dsimp only [Blocks.get]
                            refine wp_join_group (ts := [])
                              (fun _ m4'' => ∃ wl4'' wr4'' : FidArr64 c.max_vars,
                                (FidReorderMem c s wl4'' wr4'' ⋆ R) m4'')
                              (fun _ _ m4'' hm4'' => by c0_hsteps; exact hJ_nw () m4'' hm4'')
                              (fun J_nw' hJ_nw' => by
                                c0_hsplit
                                · c0_hsteps_nogrp
                                  refine wp_join_group (ts := [i64])
                                    (fun _ m' => ∃ wl' wr' : FidArr64 c.max_vars,
                                      (FidReorderMem c s wl' wr' ⋆ R) m')
                                    (fun _ _ m' ⟨wl', wr', hm'⟩ => by
                                      dsimp only [Blocks.get]; c0_hsteps
                                      exact hJ_nw' () _ ⟨_, _, by assumption⟩)
                                    (fun J_sa hJ_sa => by
                                      c0_hsteps_nogrp
                                      all_goals exact hJ_sa _ m4' ⟨_, _, by assumption⟩)
                                · c0_hsteps_nogrp
                                  refine wp_join_group (ts := [i64])
                                    (fun _ m' => ∃ wl' wr' : FidArr64 c.max_vars,
                                      (FidReorderMem c s wl' wr' ⋆ R) m')
                                    (fun _ _ m' ⟨wl', wr', hm'⟩ => by
                                      dsimp only [Blocks.get]; c0_hsteps
                                      exact hJ_nw' () _ ⟨_, _, by assumption⟩)
                                    (fun J_sa hJ_sa => by
                                      c0_hsteps_nogrp
                                      all_goals exact hJ_sa _ m4' ⟨_, _, by assumption⟩)))
                          (fun J_lit2 hJ_lit2 => by
                            c0_hsplit
                            · c0_hsteps_nogrp
                              refine wp_join_group (ts := [i64])
                                (fun _ m' => ∃ wl' wr' : FidArr64 c.max_vars,
                                  (FidReorderMem c s wl' wr' ⋆ R) m')
                                (fun _ _ m' ⟨wl', wr', hm'⟩ => by
                                  dsimp only [Blocks.get]; c0_hsteps
                                  exact hJ_lit2 () _ ⟨_, _, by assumption⟩)
                                (fun J_sa hJ_sa => by
                                  c0_hsteps_nogrp
                                  all_goals exact hJ_sa _ m4 ⟨_, _, by assumption⟩)
                            · c0_hsteps_nogrp
                              refine wp_join_group (ts := [i64])
                                (fun _ m' => ∃ wl' wr' : FidArr64 c.max_vars,
                                  (FidReorderMem c s wl' wr' ⋆ R) m')
                                (fun _ _ m' ⟨wl', wr', hm'⟩ => by
                                  dsimp only [Blocks.get]; c0_hsteps
                                  exact hJ_lit2 () _ ⟨_, _, by assumption⟩)
                                (fun J_sa hJ_sa => by
                                  c0_hsteps_nogrp
                                  all_goals exact hJ_sa _ m4 ⟨_, _, by assumption⟩))
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
  · c0_hsteps_nogrp
    refine fid_queue_loop4_wp hcv_le hcv_30 hm3 fun wl4 wr4 m4 hm4 => ?_
    exact fid_queue_post4_wp hRescale hHeapUp hSift hlen hQ' hcv_le hcv_29 hcv_30 hflags_len hm4

/-- Parametric `Func.wp` proof for `full_reorder_queue_fid`, certifying canonical
`FullM4Ternary.fullReorderQueueSpec`. -/
theorem full_reorder_queue_fid_wp (Γ : Env)
    (hArenaNext : EnvSpec Γ "full_arena_next" fullArenaNextSpec)
    (hRescale : EnvSpec Γ "full_rescale" fullRescaleSpec)
    (hHeapUp : EnvSpec Γ "full_heap_up" fullHeapUpSpec)
    (hSift : EnvSpec Γ "full_reorder_sift_fid" fidReorderSiftSpec) :
    ∀ a m Q X, fullReorderQueueSpec a m Q X →
      Func.wp Γ full_reorder_queue_fid_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hmF, hQ⟩
  have hQ' : ∀ r m', FidQueuePostOk c s R m' → Q r m' := by
    intro r m' ⟨s', hcore, hlen', hext, hm'⟩; exact hQ r s' m' hcore hlen' hext hm'
  clear hQ
  have hmx := c.hmaxv; have har := c.harena; have hwc := c.hwcap; unfold dimacsBound at hmx har hwc
  have hcv_le := hlen.core_ok.cur_vars_le
  have hcv_29 : s.core.cur_vars < 2 ^ 29 := by omega
  have hcv_30 : s.core.cur_vars < 2 ^ 30 := lt_trans hcv_29 (by decide)
  have h2cv_le : 2 * s.core.cur_vars ≤ 2 * c.max_vars := Nat.mul_le_mul_left 2 hcv_le
  have h2cv_30 : 2 * s.core.cur_vars < 2 ^ 30 := by omega
  have hvals_len := hlen.core_ok.vals_len
  have hvals_2cv : 2 * s.core.cur_vars ≤ s.core.vals.length := hvals_len ▸ h2cv_le
  have hflags_len := hlen.core_ok.flags_len
  have harena_le := hlen.core_ok.arena_len_le; have har_len := hlen.core_ok.arena_len_arr
  have har_29 : s.core.arena_len < 2 ^ 29 := by omega
  have har_le_arr : s.core.arena_len ≤ s.core.arena.length := by omega
  have hwlen_le := hlen.core_ok.wlen_le; have hwlen_29 : s.core.wlen < 2 ^ 29 := by omega
  have hwstk_len := hlen.core_ok.wstk_len_arr
  have hwlen_stk : s.core.wlen ≤ s.core.wstk.length := by omega
  have hwvec_len := hlen.core_ok.wvec_len; have hws_len := hlen.scratch_ok.wsort_len
  obtain ⟨wl, wr, hmR⟩ := fid_reorderMem_of_fullMem hlen hmF
  clear hmF
  unfold Func.wp full_reorder_queue_fid_body
  c0_hsteps_nogrp
  -- Loop 1: zero wl[v], wr[v]
  refine wp_while_state1 (fun v : BitVec 64 => v) (fun v => s.core.cur_vars - v.toNat)
    (fun v m1 => v.toNat ≤ s.core.cur_vars ∧
      ∃ wl1 wr1 : FidArr64 c.max_vars, (FidReorderMem c s wl1 wr1 ⋆ R) m1)
    (fun J1 hJ1 => by c0_hsteps; exact hJ1 0#64 m ⟨Nat.zero_le _, wl, wr, hmR⟩)
    (fun J1 v m1 ⟨hv, wl1, wr1, hm1⟩ hJ1 => ?_)
  c0_hsplit
  · have hv_lt : v.toNat < s.core.cur_vars := fid_bv64_lt_of_mod_lt hcv_30 ‹_›
    have hv_mv : v.toNat < c.max_vars := Nat.lt_of_lt_of_le hv_lt hcv_le
    have hvp1 := fid_bv64_add1_toNat hcv_30 hv_lt
    c0_hsteps; exact hJ1 (v + 1#64) _ hvp1.2.2 ⟨hvp1.2.1, _, _, by assumption⟩
  · -- Loop 2: arena clause scan wrapped in J_after2
    refine wp_join_group (ts := [i64])
      (fun _ m2 => ∃ wl2 wr2 : FidArr64 c.max_vars, (FidReorderMem c s wl2 wr2 ⋆ R) m2) ?_ ?_
    · rintro _ _ m2 ⟨wl2, wr2, hm2⟩
      dsimp only [Blocks.get]
      exact fid_queue_loop34_wp hRescale hHeapUp hSift hlen hQ' hcv_le hcv_29 hcv_30 h2cv_le
        h2cv_30 hvals_2cv hflags_len hwlen_29 hwlen_stk hwvec_len hm2
    · -- Loop 2 entry (`off = 0`)
      intro J_after2 hJ_after2
      refine wp_while_state1 (fun off : BitVec 64 => off) (fun off => s.core.arena_len - off.toNat)
        (fun _ m2 => ∃ wl2 wr2 : FidArr64 c.max_vars, (FidReorderMem c s wl2 wr2 ⋆ R) m2)
        (fun J2 hJ2 => by c0_hsteps; exact hJ2 0#64 m1 ⟨wl1, wr1, hm1⟩)
        (fun J2 off m2 ⟨wl2, wr2, hm2⟩ hJ2 => ?_)
      c0_hsplit
      · c0_hsplit
        · c0_hsteps; exact hJ_after2 (off, ()) m2 ⟨wl2, wr2, hm2⟩
        · rcases fid_off_bounds har_29 har_le_arr (by assumption) (by assumption) rfl with
              ⟨hoff3_le, hoff_29, hoff2_eq, hoff_lt, hoff2_lt⟩
          c0_hsteps_nogrp
          refine wp_join_group (ts := [])
            (fun _ m2' => ∃ wl2' wr2' : FidArr64 c.max_vars, (FidReorderMem c s wl2' wr2' ⋆ R) m2')
            (fun _ _ m2' ⟨wl2', wr2', hm2'⟩ => by
              dsimp only [Blocks.get]; c0_hsteps_nogrp
              obtain ⟨tmk, trc, htmk, htrc, hmF'⟩ := fid_fullMem_of_reorderMem hm2'
              apply fid_wp_call_spec hArenaNext
              refine ⟨c, _, R, rfl, ?_, hmF', ?_⟩
              · exact ⟨hlen.core_ok, { hlen.scratch_ok with
                  tarjan_mark_len := htmk, tarjan_reach_len := htrc }⟩
              · c0_hsplit
                · c0_hsteps; exact hJ_after2 (off, ()) m2' ⟨wl2', wr2', hm2'⟩
                · c0_hsteps; refine hJ2 _ m2' ?_ ⟨wl2', wr2', hm2'⟩
                  first
                  | exact Nat.sub_lt_sub_left
                      (Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide)) hoff3_le)
                      (Nat.lt_of_not_le (by assumption))
                  | (clear hJ2 hJ_after2 hm2 hm2' hmF' hSift hArenaNext hRescale hHeapUp hQ'
                     have hlt : off.toNat < s.core.arena_len :=
                       Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide)) hoff3_le
                     bv_omega))
            (fun J_skip hJ_skip => ?_)
          c0_hsplit
          · c0_hsplit
            · rcases fid_sz_off3_le hoff3_le har_29 hoff2_lt hoff2_eq (by assumption) rfl rfl with
                ⟨hsz_le, hsz_29⟩
              c0_hsteps_nogrp
              refine wp_join_group (ts := [Ty.bool, i64, i64]) (fun _ m2' => m2' = m2)
                (fun _ ⟨sat, un, _⟩ m2' hm_eq => by
                  subst m2'; dsimp only [Blocks.get]; c0_hsteps_nogrp
                  refine wp_join_group (ts := [i64])
                    (fun _ m2'' => ∃ wl2'' wr2'' : FidArr64 c.max_vars,
                      (FidReorderMem c s wl2'' wr2'' ⋆ R) m2'')
                    (fun _ _ m2'' hm2'' => by c0_hsteps; exact hJ_skip () m2'' hm2'')
                    (fun J_cw hJ_cw => ?_)
                  c0_hsplit
                  · c0_hsteps; exact hJ_cw _ m2 ⟨wl2, wr2, hm2⟩
                  · c0_hsplit
                    · c0_hsplit
                      · c0_hsteps_nogrp
                        refine wp_join_group (ts := [i64]) (fun _ mw => mw = m2)
                          (fun _ ⟨w, _⟩ mw hmw => by
                            subst mw; dsimp only [Blocks.get]; c0_hsteps_nogrp
                            refine wp_join_group (ts := [i64])
                              (fun _ m2k => ∃ wl2k wr2k : FidArr64 c.max_vars,
                                (FidReorderMem c s wl2k wr2k ⋆ R) m2k)
                              (fun _ _ m2k hm2k => by c0_hsteps; exact hJ_cw _ m2k hm2k)
                              (fun J_ak hJ_ak => ?_)
                            c0_hsplit
                            · refine wp_while_state1 (fun k : BitVec 64 => k)
                                (fun k => (BitVec.setWidth 64
                                  (s.core.arena[(off + 2#64).toNat]'hoff2_lt)).toNat - k.toNat)
                                (fun k m2k => k.toNat ≤ (BitVec.setWidth 64
                                    (s.core.arena[(off + 2#64).toNat]'hoff2_lt)).toNat ∧
                                  ∃ wl2k wr2k :
                                    FidArr64 c.max_vars, (FidReorderMem c s wl2k wr2k ⋆ R) m2k)
                                (fun J_k hJ_k => by
                                  c0_hsteps; exact hJ_k 0#64 m2 ⟨Nat.zero_le _, wl2, wr2, hm2⟩)
                                (fun J_k k m2k ⟨hk, wl2k, wr2k, hm2k⟩ hJ_k => ?_)
                              c0_hsplit
                              · have hk_lt : k.toNat < (BitVec.setWidth 64
                                    (s.core.arena[(off + 2#64).toNat]'hoff2_lt)).toNat :=
                                  fid_arena_k_lt hoff2_eq hoff_29 hoff2_lt (by assumption) rfl
                                have hk_29 : k.toNat < 2 ^ 29 := Nat.lt_trans hk_lt hsz_29
                                have hk3 := fid_bv64_off3_add_toNat hoff_29 hk_29
                                have hk1 := fid_bv64_add1_toNat (lt_trans hsz_29 (by decide)) hk_lt
                                have hk_ar : ((off + 3#64) + k).toNat < s.core.arena.length :=
                                  hk3.1 ▸ Nat.lt_of_lt_of_le (Nat.add_lt_add_left hk_lt (off.toNat
                                    + 3))
                                    (Nat.le_trans hsz_le har_le_arr)
                                c0_hsteps_nogrp
                                refine wp_join_group (ts := [])
                                  (fun _ m2k' => ∃ wl2k' wr2k' : FidArr64 c.max_vars,
                                    (FidReorderMem c s wl2k' wr2k' ⋆ R) m2k')
                                  (fun _ _ m2k' hm2k' => by
                                    dsimp only [Blocks.get]; c0_hsteps
                                    exact hJ_k (k + 1#64) m2k' hk1.2.2 ⟨hk1.2.1, hm2k'⟩)
                                  (fun J_kl hJ_kl => ?_)
                                c0_hsplit
                                · have hlit_2cv : (BitVec.setWidth 64
                                      (s.core.arena[((off + 3#64) + k).toNat]'hk_ar)).toNat <
                                      2 * s.core.cur_vars := by
                                    refine fid_arena_lit_2cv ?_ hcv_29 hk_ar _ (by assumption)
                                    have h3b : (3 : BitVec 64).toNat = 3 := rfl
                                    have hm3 : (3 : Nat) % 2 ^ 64 = 3 := by decide
                                    rw [hk3.1, ← hk3.2.1]; simp only [h3b, hm3]
                                  have hlit_2mx := Nat.lt_of_lt_of_le hlit_2cv h2cv_le
                                  have hlit_mv3 : (BitVec.setWidth 64
                                      (s.core.arena[((off + 3#64) + k).toNat]'hk_ar >>>
                                        (1 : Nat))).toNat < c.max_vars :=
                                    fid_zext32_bv32_ushr1_lt hlit_2mx
                                  have hlit_mv4 : (BitVec.setWidth 64
                                      (s.core.arena[((off + 3#64) + k).toNat]'hk_ar >>>
                                        (1 : BitVec 32))).toNat < c.max_vars :=
                                    fid_zext32_bv32_ushr1_bv_lt hlit_2mx
                                  clear hJ2 hJ_after2 hJ_skip hJ_cw hJ_ak hJ_k
                                  clear hlit_2cv hlit_2mx hk1 hk3 hk_29 hk_lt hsz_le hsz_29
                                  clear hoff3_le hoff_29 hoff2_eq hm2 hm1 hmR
                                  c0_hsteps_nogrp
                                  refine wp_join_group (ts := [])
                                    (fun _ m' => ∃ wl' wr' : FidArr64 c.max_vars,
                                      (FidReorderMem c s wl' wr' ⋆ R) m')
                                    (fun _ _ m' hm' => by
                                      try dsimp only [Blocks.get]
                                      c0_hsteps; exact hJ_kl () m' hm')
                                    (fun Js hJs => by
                                      c0_hsplit
                                      · c0_hsteps_nogrp
                                        refine wp_join_group (ts := [i64])
                                          (fun _ m' => ∃ wl' wr' : FidArr64 c.max_vars,
                                            (FidReorderMem c s wl' wr' ⋆ R) m')
                                          (fun _ _ m' ⟨wl', wr', hm'⟩ => by
                                            dsimp only [Blocks.get]; c0_hsteps
                                            exact hJs () _ ⟨_, _, by assumption⟩)
                                          (fun J_sa hJ_sa => by
                                            c0_hsteps_nogrp
                                            all_goals exact hJ_sa _ m2k ⟨_, _, by assumption⟩)
                                      · c0_hsteps_nogrp
                                        refine wp_join_group (ts := [i64])
                                          (fun _ m' => ∃ wl' wr' : FidArr64 c.max_vars,
                                            (FidReorderMem c s wl' wr' ⋆ R) m')
                                          (fun _ _ m' ⟨wl', wr', hm'⟩ => by
                                            dsimp only [Blocks.get]; c0_hsteps
                                            exact hJs () _ ⟨_, _, by assumption⟩)
                                          (fun J_sa hJ_sa => by
                                            c0_hsteps_nogrp
                                            all_goals exact hJ_sa _ m2k ⟨_, _, by assumption⟩))
                                · c0_hsteps; exact hJ_kl () m2k ⟨wl2k, wr2k, hm2k⟩
                              · c0_hsteps; exact hJ_ak _ m2k ⟨wl2k, wr2k, hm2k⟩
                            · c0_hsteps; exact hJ_ak _ m2 ⟨wl2, wr2, hm2⟩)
                          (fun Jw hJw => by
                            c0_hsteps_nogrp
                            all_goals exact hJw (_, ()) m2 rfl)
                      · c0_hsteps; exact hJ_cw _ m2 ⟨wl2, wr2, hm2⟩
                    · c0_hsteps; exact hJ_cw _ m2 ⟨wl2, wr2, hm2⟩)
                (fun J_su hJ_su => ?_)
              refine wp_while_state (fun p : BitVec 64 × BitVec 64 × PUnit => p)
                (fun p => (BitVec.setWidth 64
                  (s.core.arena[(off + 2#64).toNat]'hoff2_lt)).toNat - p.2.1.toNat)
                (fun p m_su => m_su = m2 ∧ p.2.1.toNat ≤ (BitVec.setWidth 64
                    (s.core.arena[(off + 2#64).toNat]'hoff2_lt)).toNat)
                (fun J_j hJ_j => by c0_hsteps; exact hJ_j (0#64, 0#64, ()) m2 ⟨rfl, Nat.zero_le _⟩)
                (fun J_j ⟨un, j, ⟨⟩⟩ m_su ⟨hm_eq, hj⟩ hJ_j => ?_)
              subst m_su; c0_hsplit
              · have hj_lt : j.toNat < (BitVec.setWidth 64
                    (s.core.arena[(off + 2#64).toNat]'hoff2_lt)).toNat :=
                  fid_arena_k_lt hoff2_eq hoff_29 hoff2_lt (by assumption) rfl
                have hj_29 : j.toNat < 2 ^ 29 := Nat.lt_trans hj_lt hsz_29
                have hj3 := fid_bv64_off3_add_toNat hoff_29 hj_29
                have hj1 := fid_bv64_add1_toNat (lt_trans hsz_29 (by decide)) hj_lt
                have hj_ar : ((off + 3#64) + j).toNat < s.core.arena.length :=
                  hj3.1 ▸ Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj_lt (off.toNat + 3))
                    (Nat.le_trans hsz_le har_le_arr)
                c0_hsteps_nogrp
                refine wp_join_group (ts := [Ty.bool, i64]) (fun _ m_su' => m_su' = m2)
                  (fun _ ⟨sat, un', _⟩ m_su' hm_eq' => by
                    subst m_su'; dsimp only [Blocks.get]; c0_hsteps
                    exact hJ_j (un', j + 1#64, ()) m2 hj1.2.2 ⟨rfl, hj1.2.1⟩)
                  (fun J_lit hJ_lit => ?_)
                c0_hsplit
                · have hj_2cv : (BitVec.setWidth 64
                      (s.core.arena[((off + 3#64) + j).toNat]'hj_ar)).toNat < 2 * s.core.cur_vars
                        := by
                    refine fid_arena_lit_2cv ?_ hcv_29 hj_ar _ (by assumption)
                    have h3b : (3 : BitVec 64).toNat = 3 := rfl
                    have hm3 : (3 : Nat) % 2 ^ 64 = 3 := by decide
                    rw [hj3.1, ← hj3.2.1]; simp only [h3b, hm3]
                  have hj_val : (BitVec.setWidth 64
                      (s.core.arena[((off + 3#64) + j).toNat]'hj_ar)).toNat < s.core.vals.length :=
                    hvals_len ▸ Nat.lt_of_lt_of_le hj_2cv h2cv_le
                  clear hJ2 hJ_after2 hJ_skip hm1 hmR hsz_le hsz_29 hoff3_le hoff_29 hoff2_eq
                  clear hj3 hj1 hj_2cv hj_lt hj_29 hSift hArenaNext hRescale hHeapUp hQ'
                  c0_hsteps_nogrp; c0_hsplit
                  · c0_hsteps; exact hJ_su (true, un, j, ()) m2 rfl
                  · c0_hsteps; all_goals exact hJ_lit (false, _, ()) m2 rfl
                · c0_hsteps; exact hJ_lit (false, un, ()) m2 rfl
              · c0_hsteps; exact hJ_su (false, un, j, ()) m2 rfl
            · c0_hsteps; exact hJ_skip () m2 ⟨wl2, wr2, hm2⟩
          · c0_hsteps; exact hJ_skip () m2 ⟨wl2, wr2, hm2⟩
      · c0_hsteps; exact hJ_after2 (off, ()) m2 ⟨wl2, wr2, hm2⟩

end FidReorderQueueProof

/-! ## 5. `full_reorder_fid_wp` (`FullM4.m4ReorderSpec`) -/

section FidReorderTopProof

open LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open scoped FullArenaTactics

private theorem fid_arenaPermEq_refl (k : FullCoreState) : FullArenaPermEq k k :=
  ⟨rfl, rfl, fun _ _ => ⟨rfl, rfl, List.Perm.refl _⟩⟩

/-- Parametric `Func.wp` proof for `full_reorder_fid`, directly certifying canonical
`FullM4.m4ReorderSpec`. -/
theorem full_reorder_fid_wp (Γ : Env)
    (hQueue : ∀ a m Q X, fullReorderQueueSpec a m Q X →
      Γ "full_reorder_queue_m7" [i64] [i64] a m Q X) :
    ∀ a m Q X, FullM4.m4ReorderSpec a m Q X → Func.wp Γ full_reorder_fid_body a m Q X := by
  rintro ⟨h, budget, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hsp, hm, hQ⟩
  unfold Func.wp full_reorder_fid_body
  c0_hsteps
  · exact hQ 0#64 s m hsp (fid_arenaPermEq_refl s.core) rfl rfl hm
  · c0_call hQueue
    refine ⟨c, s, R, rfl, hsp.lengths, hm, ?_⟩
    rintro ⟨r, ⟨⟩⟩ s1 m1 hc1 hlen1 hpres1 hm1
    have hce1 := fullCoreState_agrees_with_scratch hc1
    c0_hsteps
    exact hQ r s1 m1 (fullSparseInv_of_core_eq hsp hlen1 hce1 hpres1)
      (hce1 ▸ fid_arenaPermEq_refl s.core) (by rw [hce1]) (by rw [hce1]) hm1

end FidReorderTopProof

end LeanQbe.T.Examples.Kissat.FullM7FidelityCore
