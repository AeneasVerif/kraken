/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S5ReduceProbeProof0
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullArena1
import LeanQbe.T.Examples.Kissat.FullReduceLemmas1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.MemLemmas
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Step 13 S5 `full_sort_reds` Shared Bridge & Step Lemmas (`Proof1b0`)

Defines `step13SortRedsSpec`, the `scratch_buf` u32/u64 memory bridge (`loadVal_sb32`,
`store_sb32`, `loadVal_sb64`, `store_sb64`), bucket counting helpers (`countPrefix`,
`sumBuckets`), and compact step-invariant lemmas used by `full_sort_reds_s5_wp` (`Proof1b`).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S5

open Std Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open FullArenaTactics
open scoped FullArenaTactics

@[expose] public section

/-- Step-13 `full_sort_reds` contract (`#3048` Option A: radix sort uses `h->scratch_buf`
when `4 * n + 512 ≤ c.scratch_cap`, preserving `sb'.length = c.scratch_cap`). -/
def step13SortRedsSpec : Spec [i64, i64] [] := fun (h, n, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ n.toNat ≤ c.red_cap ∧
    (∀ k < n.toNat, (s.scratch.red_refs[k]?.getD 0#32).toNat + 2 < c.arena_cap) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ rr' sb' m', rr'.length = c.red_cap → sb'.length = c.scratch_cap →
      (∀ k < n.toNat, ∃ j < n.toNat, rr'[k]? = s.scratch.red_refs[j]?) →
      (FullMem c { s with scratch := { s.scratch with red_refs := rr', scratch_buf := sb' } } ⋆ R)
        m' → Q () m'

end

public section

/-! ## 1. `scratch_buf` u32/u64 memory bridge -/

def pairU64 (lo hi : BitVec 32) : BitVec 64 :=
  BitVec.ofNat 64 (lo.toNat + 2 ^ 32 * hi.toNat)

def pairU64At (sb : List (BitVec 32)) (idx : Nat) : BitVec 64 :=
  pairU64 (sb[2 * idx]?.getD 0#32) (sb[2 * idx + 1]?.getD 0#32)

def sbWithU64 (sb : List (BitVec 32)) (idx : Nat) (w : BitVec 64) : List (BitVec 32) :=
  (sb.set (2 * idx) (w.setWidth 32)).set (2 * idx + 1) ((w >>> 32).setWidth 32)

private def sbRest (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆ FullCoreByteArrs c s.core ⋆
  FullCoreU32A c s.core ⋆ FullCoreU32B c s.core ⋆ array (t := i32) c.pArena s.core.arena ⋆
  array (t := i32) c.pWstk s.core.wstk ⋆ FullScrByteArrs c s.scratch ⋆
  FullScrU32A c s.scratch ⋆ FullScrWksArrs c s.scratch ⋆ FullScrMetaArrs c s.scratch ⋆
  array (t := i32) c.pDelayed s.scratch.delayed ⋆
  array (t := i32) c.pRedRefs s.scratch.red_refs ⋆
  array (t := i32) c.pExtendStk s.scratch.extend_stk ⋆ c.pad

private theorem focus_sb {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) :
    (array (t := i32) c.pScratchBuf s.scratch.scratch_buf ⋆ (sbRest c s ⋆ R)) m := by
  unfold FullMem FullCoreArrays FullCoreDynArrs FullScratchArrays FullScrDynArrs at hm
  unfold sbRest; ecancel

private theorem unfocus_sb {c : FullCfg} {s : FullState} {sb' : List (BitVec 32)}
    {R : Mem 64 → Prop} {m' : Mem 64}
    (hm : (array (t := i32) c.pScratchBuf sb' ⋆ (sbRest c s ⋆ R)) m') :
    (FullMem c { s with scratch := { s.scratch with scratch_buf := sb' } } ⋆ R) m' := by
  let sc' : FullScratch := { s.scratch with scratch_buf := sb' }
  change (FullMem c { s with scratch := sc' } ⋆ R) m'
  unfold FullMem FullCoreArrays FullCoreDynArrs FullScratchArrays FullScrDynArrs
  rw [show Full.hdrTailWords c { s with scratch := sc' } = Full.hdrTailWords c s from rfl,
    show FullScrByteArrs c sc' = FullScrByteArrs c s.scratch from rfl,
    show FullScrU32A c sc' = FullScrU32A c s.scratch from rfl,
    show FullScrWksArrs c sc' = FullScrWksArrs c s.scratch from rfl,
    show FullScrMetaArrs c sc' = FullScrMetaArrs c s.scratch from rfl]
  unfold sbRest at hm; dsimp only [sc']; ecancel

private theorem pairU64_toNat (lo hi : BitVec 32) :
    (pairU64 lo hi).toNat = lo.toNat + 2 ^ 32 * hi.toNat := by
  have := lo.isLt; have := hi.isLt
  unfold pairU64; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

private theorem pairU64_of_word (w : BitVec 64) :
    pairU64 (w.setWidth 32) ((w >>> 32).setWidth 32) = w := by
  have := w.isLt; apply BitVec.eq_of_toNat_eq
  rw [pairU64_toNat, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega

private theorem cons_inj_step {α : Type} {a b : α} {xs ys : List α}
    (h1 : a = b) (h2 : xs = ys) : a :: xs = b :: ys := by subst h1 h2; rfl

private theorem toBytes4_bv32_eq_nat (x : BitVec 32) :
    Int.toBytes 4 x.toInt = Int.toBytes 4 (x.toNat : Int) := by
  have hx := x.isLt; rw [BitVec.toInt_eq_msb_cond]; cases x.msb
  · simp
  · simp only [↓reduceIte, Int.toBytes, Int.take]
    repeat apply cons_inj_step (congrArg (fun z : Int => z.toNat.toUInt8) (by omega))
    rfl

private theorem toBytes8_bv64_eq_nat (x : BitVec 64) :
    Int.toBytes 8 x.toInt = Int.toBytes 8 (x.toNat : Int) := by
  have hx := x.isLt; rw [BitVec.toInt_eq_msb_cond]; cases x.msb
  · simp
  · simp only [↓reduceIte, Int.toBytes, Int.take]
    repeat apply cons_inj_step (congrArg (fun z : Int => z.toNat.toUInt8) (by omega))
    rfl

private theorem toBytes8_pair (lo hi : BitVec 32) :
    Int.toBytes 8 (pairU64 lo hi).toInt = Int.toBytes 4 lo.toInt ++ Int.toBytes 4 hi.toInt := by
  rw [toBytes8_bv64_eq_nat, toBytes4_bv32_eq_nat lo, toBytes4_bv32_eq_nat hi, pairU64_toNat]
  have hlo := lo.isLt; have hhi := hi.isLt
  simp only [Int.toBytes, Int.take, List.cons_append, List.nil_append]
  repeat apply cons_inj_step (congrArg (fun z : Int => z.toNat.toUInt8) (by omega))
  rfl

private theorem array_i32_pair_eq_cell64 (a : BitVec 64) (lo hi : BitVec 32) :
    array (t := i32) a ([lo, hi] : List (Val i32)) = cell64 a (pairU64 lo hi) := by
  have hpair : bytesOf ([lo, hi] : List (Val i32)) = Int.toBytes 8 (pairU64 lo hi).toInt := by
    simp only [bytesOf, List.flatMap_cons, List.flatMap_nil, List.append_nil, toBits,
      Ty.bytes, Ty.size, BitVec.setWidth_eq]
    exact (toBytes8_pair lo hi).symm
  have hlen : i32.bytes * ([lo, hi] : List (Val i32)).length ≤ 2 ^ 64 := by
    change 4 * 2 ≤ 2 ^ 64; omega
  funext m; unfold cell64; apply propext; constructor
  · intro hm; exact ((array_eq_bytesOf a ([lo, hi] : List (Val i32)) hlen hm).trans
      (congrArg (·.At a) hpair)).symm
  · intro hm; have hby := array_bytes a ([lo, hi] : List (Val i32)) hlen
    rw [← hm, ← hpair]; exact hby

private theorem array_i32_pair_focus (a : BitVec 64) (xs : List (BitVec 32)) {idx : Nat}
    (h : 2 * idx + 1 < xs.length) :
    array (t := i32) a xs =
      (cell64 (a + BitVec.ofNat 64 (8 * idx)) (pairU64 xs[2 * idx] xs[2 * idx + 1]) ⋆
        (array (t := i32) a (xs.take (2 * idx)) ⋆
          array (t := i32) (a + BitVec.ofNat 64 (4 * (2 * idx + 2)))
            (xs.drop (2 * idx + 2)))) := by
  have hs := array_slice_focus (t := i32) a xs (off := 2 * idx) (sz := 2) (by omega)
  have htake : (xs.drop (2 * idx)).take 2 = [xs[2 * idx], xs[2 * idx + 1]] := by
    apply List.ext_getElem (by simp; omega)
    intro k hk _; simp only [List.getElem_take, List.getElem_drop]
    match k with | 0 => rfl | 1 => rfl
  simp only [Ty.bytes, Ty.size] at hs
  rw [hs, htake, array_i32_pair_eq_cell64,
    show (32 + 7) / 8 * (2 * idx) = 8 * idx by omega,
    show (32 + 7) / 8 * (2 * idx + 2) = 4 * (2 * idx + 2) by omega]

private theorem sbWithU64_get0 {sb : List (BitVec 32)} {idx : Nat} {w : BitVec 64}
    (h : 2 * idx + 1 < sb.length) :
    (sbWithU64 sb idx w)[2 * idx]'(by simp [sbWithU64]; omega) = w.setWidth 32 := by
  unfold sbWithU64; rw [List.getElem_set_ne (by omega), List.getElem_set_self]

private theorem sbWithU64_get1 {sb : List (BitVec 32)} {idx : Nat} {w : BitVec 64}
    (h : 2 * idx + 1 < sb.length) :
    (sbWithU64 sb idx w)[2 * idx + 1]'(by simp [sbWithU64]; omega) =
      (w >>> 32).setWidth 32 := by
  unfold sbWithU64; rw [List.getElem_set_self]

private theorem array_i32_set_pair (a : BitVec 64) (xs : List (BitVec 32)) {idx : Nat}
    (h : 2 * idx + 1 < xs.length) (w : BitVec 64) :
    array (t := i32) a (sbWithU64 xs idx w) =
      (cell64 (a + BitVec.ofNat 64 (8 * idx)) w ⋆
        (array (t := i32) a (xs.take (2 * idx)) ⋆
          array (t := i32) (a + BitVec.ofNat 64 (4 * (2 * idx + 2)))
            (xs.drop (2 * idx + 2)))) := by
  have hs := array_i32_pair_focus a (sbWithU64 xs idx w) (idx := idx) (by simp [sbWithU64]; omega)
  have ht : (sbWithU64 xs idx w).take (2 * idx) = xs.take (2 * idx) := by
    dsimp only [sbWithU64]; rw [List.take_set_of_le (by omega), List.take_set_of_le (by omega)]
  have hd : (sbWithU64 xs idx w).drop (2 * idx + 2) = xs.drop (2 * idx + 2) := by
    dsimp only [sbWithU64]; rw [List.drop_set_of_lt (by omega), List.drop_set_of_lt (by omega)]
  rw [hs, ht, hd, sbWithU64_get0 h, sbWithU64_get1 h, pairU64_of_word]

theorem loadVal_sb32 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {p : BitVec 64} {idx : Nat} (hi : idx < s.scratch.scratch_buf.length)
    (hp : p = c.pScratchBuf + BitVec.ofNat 64 (4 * idx)) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 p = some (s.scratch.scratch_buf[idx]'hi) := by
  subst p; exact load_full_scratch_buf hi hm

theorem store_sb32 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {p : BitVec 64} {idx : Nat} (v : BitVec 32) (hi : idx < s.scratch.scratch_buf.length)
    (hp : p = c.pScratchBuf + BitVec.ofNat 64 (4 * idx)) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 p ∧
      (FullMem c { s with scratch := { s.scratch with
        scratch_buf := s.scratch.scratch_buf.set idx v } } ⋆ R) (storeMem m i32 p v) := by
  subst p; exact store_full_scratch_buf v hi hm

theorem loadVal_sb64 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {p : BitVec 64} {idx : Nat} (hi : 2 * idx + 1 < s.scratch.scratch_buf.length)
    (hp : p = c.pScratchBuf + BitVec.ofNat 64 (8 * idx)) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i64 p = some (pairU64At s.scratch.scratch_buf idx) := by
  subst p; have hf := focus_sb hm
  rw [array_i32_pair_focus c.pScratchBuf s.scratch.scratch_buf hi, sep_assoc] at hf
  have hld := loadVal_cell64 hf; unfold pairU64At
  rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem hi]; exact hld

theorem store_sb64 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {p : BitVec 64} {idx : Nat} (w : BitVec 64)
    (hi : 2 * idx + 1 < s.scratch.scratch_buf.length)
    (hp : p = c.pScratchBuf + BitVec.ofNat 64 (8 * idx)) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i64 p ∧
      (FullMem c { s with scratch := { s.scratch with
        scratch_buf := sbWithU64 s.scratch.scratch_buf idx w } } ⋆ R)
        (storeMem m i64 p w) := by
  subst p; have hf := focus_sb hm
  rw [array_i32_pair_focus c.pScratchBuf s.scratch.scratch_buf hi, sep_assoc] at hf
  obtain ⟨hok, hst⟩ := store_cell64 w hf
  rw [← sep_assoc, ← array_i32_set_pair c.pScratchBuf s.scratch.scratch_buf hi w] at hst
  exact ⟨hok, unfocus_sb hst⟩

theorem sbWithU64_len {sb : List (BitVec 32)} {idx : Nat} {w : BitVec 64} :
    (sbWithU64 sb idx w).length = sb.length := by simp [sbWithU64]

theorem pairU64At_sbWithU64_self {sb : List (BitVec 32)} {idx : Nat} {w : BitVec 64}
    (h : 2 * idx + 1 < sb.length) : pairU64At (sbWithU64 sb idx w) idx = w := by
  unfold pairU64At sbWithU64
  rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega),
    List.getElem?_set_self (by simp; omega)]
  exact pairU64_of_word w

theorem pairU64At_sbWithU64_ne {sb : List (BitVec 32)} {idx k : Nat} {w : BitVec 64}
    (hne : k ≠ idx) : pairU64At (sbWithU64 sb idx w) k = pairU64At sb k := by
  unfold pairU64At sbWithU64
  rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
    List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]

theorem sbWithU64_getElem?_lt {sb : List (BitVec 32)} {idx j : Nat} {w : BitVec 64}
    (hj : j < 2 * idx) : (sbWithU64 sb idx w)[j]? = sb[j]? := by
  unfold sbWithU64; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]

theorem sbWithU64_getElem?_gt {sb : List (BitVec 32)} {idx j : Nat} {w : BitVec 64}
    (hj : 2 * idx + 1 < j) : (sbWithU64 sb idx w)[j]? = sb[j]? := by
  unfold sbWithU64; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]

/-! ## 2. Counting, prefix-sum, and invariant-step helpers -/

def countPrefix (f : Nat → Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | i + 1, b => countPrefix f i b + if f i = b then 1 else 0

def sumBuckets (f : Nat → Nat) (n : Nat) : Nat → Nat
  | 0 => 0
  | b + 1 => sumBuckets f n b + countPrefix f n b

theorem countPrefix_zero (f : Nat → Nat) (b : Nat) : countPrefix f 0 b = 0 := by simp [countPrefix]

theorem sumBuckets_zero (f : Nat → Nat) (n : Nat) : sumBuckets f n 0 = 0 := by simp [sumBuckets]

theorem countPrefix_le (f : Nat → Nat) (i b : Nat) : countPrefix f i b ≤ i := by
  induction i with
  | zero => simp [countPrefix]
  | succ i ih => simp only [countPrefix]; split <;> omega

theorem countPrefix_mono (f : Nat → Nat) {a b : Nat} (hab : a ≤ b) (c : Nat) :
    countPrefix f a c ≤ countPrefix f b c := by
  induction b with
  | zero =>
    have ha : a = 0 := by omega
    subst ha; exact Nat.le_refl _
  | succ b ih =>
    by_cases hlt : a ≤ b
    · have := ih hlt; simp only [countPrefix]; split <;> omega
    · have heq : a = b + 1 := by omega
      rw [heq]; exact Nat.le_refl _

theorem countPrefix_lt_of_eq (f : Nat → Nat) {i n b : Nat} (hin : i < n) (heq : f i = b) :
    countPrefix f i b < countPrefix f n b := by
  have h1 : countPrefix f i b < countPrefix f (i + 1) b := by
    simp only [countPrefix, heq, ↓reduceIte]; omega
  exact Nat.lt_of_lt_of_le h1 (countPrefix_mono f (by omega) b)

theorem sumBuckets_mono (f : Nat → Nat) (n : Nat) {a b : Nat} (hab : a ≤ b) :
    sumBuckets f n a ≤ sumBuckets f n b := by
  induction b with
  | zero =>
    have ha : a = 0 := by omega
    subst ha; exact Nat.le_refl _
  | succ b ih =>
    by_cases heq : a = b + 1
    · rw [heq]; exact Nat.le_refl _
    · have := ih (by omega); simp only [sumBuckets]; omega

theorem sumBuckets_eq_n (f : Nat → Nat) (n : Nat) (hf : ∀ k < n, f k < 256) :
    sumBuckets f n 256 = n := by
  induction n with
  | zero =>
    have hz : ∀ k, sumBuckets f 0 k = 0 := by
      intro k; induction k with
      | zero => rfl
      | succ k ih => simp [sumBuckets, countPrefix, ih]
    exact hz 256
  | succ n ih =>
    have ih' := ih (fun k hk => hf k (by omega))
    have hstep : ∀ k, sumBuckets f (n + 1) k =
        sumBuckets f n k + (if f n < k then 1 else 0) := by
      intro k; induction k with
      | zero => simp [sumBuckets]
      | succ k ihk =>
        simp only [sumBuckets, countPrefix, ihk]; split <;> split <;> split <;> omega
    have hfn := hf n (Nat.lt_succ_self n)
    rw [hstep 256]
    split
    · exact congrArg (· + 1) ih'
    · contradiction

theorem sumBuckets_cover (f : Nat → Nat) (n : Nat) (hf : ∀ k < n, f k < 256)
    {p : Nat} (hp : p < n) :
    ∃ b < 256, sumBuckets f n b ≤ p ∧ p < sumBuckets f n b + countPrefix f n b := by
  have hs : p < sumBuckets f n 256 := by rw [sumBuckets_eq_n f n hf]; exact hp
  have aux : ∀ k, p < sumBuckets f n k →
      ∃ b < k, sumBuckets f n b ≤ p ∧ p < sumBuckets f n b + countPrefix f n b := by
    intro k hk; induction k with
    | zero => simp [sumBuckets] at hk
    | succ k ih =>
      simp only [sumBuckets] at hk
      by_cases hk2 : p < sumBuckets f n k
      · obtain ⟨b, hbk, hb1, hb2⟩ := ih hk2; exact ⟨b, by omega, hb1, hb2⟩
      · exact ⟨k, Nat.lt_succ_self k, by omega, hk⟩
  exact aux 256 hs

abbrev radixSrcOff (use0 : Bool) (n : Nat) : Nat := if use0 then 2 * n else 3 * n
abbrev radixDstOff (use0 : Bool) (n : Nat) : Nat := if use0 then 3 * n else 2 * n

theorem radix_addr_add {base c_base : BitVec 64} (off i : Nat)
    (hoff : 4 * (off + i) < 2 ^ 64) (hbi : base = c_base + BitVec.ofNat 64 (4 * off)) :
    base + BitVec.ofNat 64 i * 4#64 = c_base + BitVec.ofNat 64 (4 * (off + i)) := by
  rw [hbi, BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), show 4 * off + i * 4 = 4 * (off + i) by omega,
    Nat.mod_eq_of_lt hoff]

theorem radix_addr_add_bv {base c_base : BitVec 64} (off : Nat) (i : BitVec 64)
    (hoff : 4 * (off + i.toNat) < 2 ^ 64) (hbi : base = c_base + BitVec.ofNat 64 (4 * off)) :
    base + i * 4#64 = c_base + BitVec.ofNat 64 (4 * (off + i.toNat)) := by
  rw [hbi, BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat,
    show (4#64).toNat = 4 from rfl]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    show 4 * off + i.toNat * 4 = 4 * (off + i.toNat) by omega, Nat.mod_eq_of_lt hoff]

theorem radixSrcOff_le (use0 : Bool) (n : Nat) : radixSrcOff use0 n ≤ 3 * n := by
  cases use0 <;> simp [radixSrcOff] <;> omega

theorem radixDstOff_le (use0 : Bool) (n : Nat) : radixDstOff use0 n ≤ 3 * n := by
  cases use0 <;> simp [radixDstOff] <;> omega

theorem radixSrcOff_lt (use0 : Bool) {n k cap : Nat} (hk : k < n) (hcap : 4 * n + 512 ≤ cap) :
    radixSrcOff use0 n + k < cap := by cases use0 <;> simp [radixSrcOff] <;> omega

theorem radixDstOff_lt (use0 : Bool) {n k cap : Nat} (hk : k < n) (hcap : 4 * n + 512 ≤ cap) :
    radixDstOff use0 n + k < cap := by cases use0 <;> simp [radixDstOff] <;> omega

theorem bv64_succ_toNat (x : BitVec 64) (hx : x.toNat + 1 < 2 ^ 64) :
    (x + 1#64).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#64).toNat = 1 from rfl]; exact Nat.mod_eq_of_lt hx

theorem bv64_pred_toNat (x : BitVec 64) (hx : 0 < x.toNat) :
    (x - 1#64).toNat = x.toNat - 1 := by
  rw [BitVec.toNat_sub, show (1#64).toNat = 1 from rfl]; omega

theorem ins_swap_step {rr0 rr2 : List (BitVec 32)} {n j jy : Nat} {y : BitVec 32}
    (hlen : rr2.length = rr0.length) (hj : j < rr0.length) (hy : some y = rr0[jy]?)
    (hmem2 : ∀ k < n, k ≠ j → ∃ j0 < n, rr2[k]? = rr0[j0]?) (hjy : jy < n) :
    ∀ k < n, k ≠ j - 1 → ∃ j0 < n, (rr2.set j y)[k]? = rr0[j0]? := by
  intro k hk _
  by_cases hkj : k = j
  · subst hkj; exact ⟨jy, hjy, by rw [List.getElem?_set_self (by omega), hy]⟩
  · rw [List.getElem?_set_ne (Ne.symm hkj)]; exact hmem2 k hk hkj

theorem ins_finish_step {rr0 rr1 rr2 : List (BitVec 32)} {n jf jx i : Nat}
    (hlen : rr2.length = rr0.length) (hjf : jf < rr0.length) (hi : i < rr1.length)
    (hxeq : rr1[i]? = rr0[jx]?) (hjx : jx < n)
    (hmem2 : ∀ k < n, k ≠ jf → ∃ j0 < n, rr2[k]? = rr0[j0]?) :
    ∀ k < n, ∃ j0 < n, (rr2.set jf (rr1[i]'hi))[k]? = rr0[j0]? := by
  intro k hk
  by_cases hkj : k = jf
  · subst hkj; exact ⟨jx, hjx, by rw [List.getElem?_set_self (by omega), ← hxeq,
      List.getElem?_eq_getElem hi]⟩
  · rw [List.getElem?_set_ne (Ne.symm hkj)]; exact hmem2 k hk hkj

theorem radix_count_inv {sb1 sb3 : List (BitVec 32)} {keyFn : Nat → Nat}
    {n i cap : Nat} {btv : BitVec 64} (hlen3 : sb3.length = cap)
    (hcap : 4 * n + 512 ≤ cap) (hpre3 : ∀ j, j < 4 * n → sb3[j]? = sb1[j]?)
    (hcnt3 : ∀ k < 256, (pairU64At sb3 (2 * n + k)).toNat = countPrefix keyFn i k)
    (hbt_lt : btv.toNat < 256) (hbt_nat : btv.toNat = keyFn i)
    (hcv1_nat : (pairU64At sb3 (2 * n + btv.toNat) + 1#64).toNat =
      countPrefix keyFn i btv.toNat + 1) :
    let sb' := sbWithU64 sb3 (2 * n + btv.toNat) (pairU64At sb3 (2 * n + btv.toNat) + 1#64)
    (∀ j, j < 4 * n → sb'[j]? = sb1[j]?) ∧
    (∀ k < 256, (pairU64At sb' (2 * n + k)).toNat = countPrefix keyFn (i + 1) k) := by
  refine ⟨fun j hj => ?_, fun k hk => ?_⟩
  · rw [sbWithU64_getElem?_lt (by omega)]; exact hpre3 j hj
  · rw [countPrefix]
    by_cases hkb : k = btv.toNat
    · subst hkb; rw [pairU64At_sbWithU64_self (by rw [hlen3]; omega), hcv1_nat, hbt_nat]
      split
      · rfl
      · contradiction
    · rw [pairU64At_sbWithU64_ne (by omega), hcnt3 k hk]
      split
      · exact absurd (hbt_nat.trans ‹_›).symm hkb
      · rfl

theorem radix_pref_inv {sb1 sb4 : List (BitVec 32)} {keyFn : Nat → Nat}
    {n bp cap : Nat} {pos : BitVec 64} (hlen4 : sb4.length = cap) (hcap : 4 * n + 512 ≤ cap)
    (hbp_lt : bp < 256) (hpos_eq : pos.toNat = sumBuckets keyFn n bp)
    (hpre4 : ∀ j, j < 4 * n → sb4[j]? = sb1[j]?)
    (hpref4 : ∀ k < bp, (pairU64At sb4 (2 * n + k)).toNat = sumBuckets keyFn n k)
    (hrem4 : ∀ k, bp ≤ k → k < 256 → (pairU64At sb4 (2 * n + k)).toNat = countPrefix keyFn n k) :
    let sb' := sbWithU64 sb4 (2 * n + bp) pos
    (∀ j, j < 4 * n → sb'[j]? = sb1[j]?) ∧
    (∀ k < bp + 1, (pairU64At sb' (2 * n + k)).toNat = sumBuckets keyFn n k) ∧
    (∀ k, bp + 1 ≤ k → k < 256 → (pairU64At sb' (2 * n + k)).toNat = countPrefix keyFn n k) := by
  refine ⟨fun j hj => ?_, fun k hk => ?_, fun k hk1 hk2 => ?_⟩
  · rw [sbWithU64_getElem?_lt (by omega)]; exact hpre4 j hj
  · by_cases hkb : k = bp
    · subst hkb; rw [pairU64At_sbWithU64_self (by rw [hlen4]; omega), hpos_eq]
    · rw [pairU64At_sbWithU64_ne (by omega)]; exact hpref4 k (by omega)
  · rw [pairU64At_sbWithU64_ne (by omega)]; exact hrem4 k (by omega) hk2

theorem radix_scatter_inv {sb1 sb5 : List (BitVec 32)} {keyFn : Nat → Nat}
    {use0 : Bool} {n is_ cap : Nat} {btv dpos : BitVec 64} {id32 : BitVec 32}
    (hkey_lt : ∀ k < n, keyFn k < 256) (hlen5 : sb5.length = cap) (hcap : 4 * n + 512 ≤ cap)
    (hrk5 : ∀ j, j < 2 * n → sb5[j]? = sb1[j]?)
    (hsr5 : ∀ k < n, sb5[radixSrcOff use0 n + k]? = sb1[radixSrcOff use0 n + k]?)
    (hcnt5 : ∀ b < 256, (pairU64At sb5 (2 * n + b)).toNat =
      sumBuckets keyFn n b + countPrefix keyFn is_ b)
    (hdst5 : ∀ b < 256, ∀ p, sumBuckets keyFn n b ≤ p →
      p < sumBuckets keyFn n b + countPrefix keyFn is_ b →
      (sb5[radixDstOff use0 n + p]?.getD 0#32).toNat < n)
    (hbt_lt : btv.toNat < 256) (hbt_nat : btv.toNat = keyFn is_) (hdpos_lt : dpos.toNat < n)
    (hdpos_eq : dpos.toNat = sumBuckets keyFn n btv.toNat + countPrefix keyFn is_ btv.toNat)
    (his_lt : is_ < n) (hid_lt : id32.toNat < n) (hn29 : n < 2 ^ 29) :
    let sb5' := sb5.set (radixDstOff use0 n + dpos.toNat) id32
    let sb'' := sbWithU64 sb5' (2 * n + btv.toNat) (dpos + 1#64)
    (∀ j, j < 2 * n → sb''[j]? = sb1[j]?) ∧
    (∀ k < n, sb''[radixSrcOff use0 n + k]? = sb1[radixSrcOff use0 n + k]?) ∧
    (∀ b < 256, (pairU64At sb'' (2 * n + b)).toNat =
      sumBuckets keyFn n b + countPrefix keyFn (is_ + 1) b) ∧
    (∀ b < 256, ∀ p, sumBuckets keyFn n b ≤ p →
      p < sumBuckets keyFn n b + countPrefix keyFn (is_ + 1) b →
      (sb''[radixDstOff use0 n + p]?.getD 0#32).toNat < n) := by
  intro sb5' sb''
  have h5'len : sb5'.length = cap := by dsimp only [sb5']; rw [List.length_set, hlen5]
  have hdst_idx : radixDstOff use0 n + dpos.toNat < sb5.length := by
    rw [hlen5]; cases use0 <;> simp [radixDstOff] <;> omega
  have hne_pair : ∀ b : Nat, 2 * (2 * n + b) ≠ radixDstOff use0 n + dpos.toNat ∧
      2 * (2 * n + b) + 1 ≠ radixDstOff use0 n + dpos.toNat := fun b => by
    cases use0 <;> simp [radixDstOff] <;> omega
  refine ⟨fun j hj => ?_, fun k hk => ?_, fun b hb => ?_, fun b hb p hp1 hp2 => ?_⟩
  · rw [sbWithU64_getElem?_lt (by omega)]
    dsimp only [sb5']; rw [List.getElem?_set_ne (by cases use0 <;> simp [radixDstOff] <;> omega)]
    exact hrk5 j hj
  · rw [sbWithU64_getElem?_lt (by cases use0 <;> simp [radixSrcOff] <;> omega)]
    dsimp only [sb5']
    rw [List.getElem?_set_ne (by cases use0 <;> simp [radixSrcOff, radixDstOff] <;> omega)]
    exact hsr5 k hk
  · rw [countPrefix]
    by_cases hkb : b = btv.toNat
    · subst hkb
      have hslf := pairU64At_sbWithU64_self (sb := sb5') (idx := 2 * n + btv.toNat)
        (w := dpos + 1#64) (by rw [h5'len]; omega)
      change (pairU64At sb'' (2 * n + btv.toNat)).toNat =
        sumBuckets keyFn n btv.toNat + (countPrefix keyFn is_ btv.toNat +
          if keyFn is_ = btv.toNat then 1 else 0)
      rw [hslf, bv64_succ_toNat _ (by omega), hdpos_eq, hbt_nat]
      split
      · omega
      · contradiction
    · change (pairU64At sb'' (2 * n + b)).toNat =
        sumBuckets keyFn n b + (countPrefix keyFn is_ b + if keyFn is_ = b then 1 else 0)
      rw [pairU64At_sbWithU64_ne (by omega)]
      have hcnt5' : pairU64At sb5' (2 * n + b) = pairU64At sb5 (2 * n + b) := by
        unfold pairU64At sb5'
        rw [List.getElem?_set_ne (hne_pair b).1.symm, List.getElem?_set_ne (hne_pair b).2.symm]
      rw [hcnt5', hcnt5 b hb]
      split
      · exact absurd (hbt_nat.trans ‹_›).symm hkb
      · rfl
  · rw [countPrefix] at hp2
    have hp_lt_n : p < n := by
      have h1 : sumBuckets keyFn n b + (countPrefix keyFn is_ b +
          if keyFn is_ = b then 1 else 0) ≤ sumBuckets keyFn n (b + 1) := by
        rw [sumBuckets]
        split
        · have hc := countPrefix_lt_of_eq keyFn his_lt ‹_›; omega
        · have hc := countPrefix_mono keyFn (Nat.le_of_lt his_lt) b; omega
      have h2 := sumBuckets_mono keyFn n (show b + 1 ≤ 256 by omega)
      have h3 := sumBuckets_eq_n keyFn n hkey_lt
      omega
    rw [sbWithU64_getElem?_lt (by cases use0 <;> simp [radixDstOff] <;> omega)]
    by_cases hpd : p = dpos.toNat
    · subst hpd; dsimp only [sb5']
      rw [List.getElem?_set_self hdst_idx, Option.getD_some]; exact hid_lt
    · dsimp only [sb5']; rw [List.getElem?_set_ne (by omega)]
      apply hdst5 b hb p hp1
      by_cases hkb : b = btv.toNat
      · subst hkb
        split at hp2
        · omega
        · exact absurd hbt_nat.symm ‹_›
      · split at hp2
        · exact absurd (hbt_nat.trans ‹_›).symm hkb
        · omega

theorem heap_swap_mem {rr0 rr2 : List (BitVec 32)} {n ed : Nat}
    (h0_rr : 0 < rr2.length) (hed_rr : ed < rr2.length) (hed_lt : ed < n)
    (hmem2 : ∀ k < n, ∃ j < n, rr2[k]? = rr0[j]?) :
    let rr_sw := (rr2.set 0 (rr2[ed]'hed_rr)).set ed (rr2[0]'h0_rr)
    ∀ k < n, ∃ j < n, rr_sw[k]? = rr0[j]? := by
  intro rr_sw k hk
  by_cases hke : k = ed
  · subst hke; obtain ⟨j, hj, heq⟩ := hmem2 0 (by omega); refine ⟨j, hj, ?_⟩
    dsimp only [rr_sw]; rw [List.getElem?_set_self (by simp; omega), ← heq,
      List.getElem?_eq_getElem h0_rr]
  · by_cases hk0 : k = 0
    · subst hk0; obtain ⟨j, hj, heq⟩ := hmem2 ed hed_lt; refine ⟨j, hj, ?_⟩
      dsimp only [rr_sw]; rw [List.getElem?_set_ne (Ne.symm hke), List.getElem?_set_self h0_rr,
        ← heq, List.getElem?_eq_getElem hed_rr]
    · obtain ⟨j, hj, heq⟩ := hmem2 k hk; refine ⟨j, hj, ?_⟩
      dsimp only [rr_sw]
      rw [List.getElem?_set_ne (Ne.symm hke), List.getElem?_set_ne (Ne.symm hk0), heq]

/-! ## 3. Combined radix memory-step lemmas for `Proof1b` -/

theorem radix_src_load {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m3 : Mem 64}
    {src : BitVec 64} {sb1 sb3 : List (BitVec 32)} {use0 : Bool} {n i cap : Nat}
    (hsb : s.scratch.scratch_buf = sb3) (hlen3 : sb3.length = cap) (hcap : 4 * n + 512 ≤ cap)
    (hi_lt : i < n) (hn29 : n < 2 ^ 29)
    (hsrc_eq : src = c.pScratchBuf + BitVec.ofNat 64 (4 * radixSrcOff use0 n))
    (hsrc_lt : ∀ k < n, (sb1[radixSrcOff use0 n + k]?.getD 0#32).toNat < n)
    (hrk3 : ∀ j, j < 2 * n → sb3[j]? = sb1[j]?)
    (hsr3 : ∀ k < n, sb3[radixSrcOff use0 n + k]? = sb1[radixSrcOff use0 n + k]?)
    (hm3 : (FullMem c s ⋆ R) m3) :
    let idx := radixSrcOff use0 n + i
    have hidx : idx < s.scratch.scratch_buf.length := by
      rw [hsb, hlen3]; exact radixSrcOff_lt use0 hi_lt hcap
    let sid := s.scratch.scratch_buf[idx]'hidx
    loadVal m3 i32 (src + BitVec.ofNat 64 i * 4#64) = some sid ∧
    sid.toNat < n ∧
    loadVal m3 i64 (c.pScratchBuf + sid.setWidth 64 * 8#64) =
      some (pairU64At sb3 sid.toNat) ∧
    pairU64At sb3 sid.toNat = pairU64At sb1 (sb1[idx]?.getD 0#32).toNat := by
  have hidx : radixSrcOff use0 n + i < s.scratch.scratch_buf.length := by
    rw [hsb, hlen3]; exact radixSrcOff_lt use0 hi_lt hcap
  have hsb_len : s.scratch.scratch_buf.length = cap := by rw [hsb, hlen3]
  have hsrc_le := radixSrcOff_le use0 n
  have hsrc_i := radix_addr_add (radixSrcOff use0 n) i (by omega) hsrc_eq
  have hsid_eq : s.scratch.scratch_buf[radixSrcOff use0 n + i]'hidx =
      sb1[radixSrcOff use0 n + i]?.getD 0#32 := by
    have heq := hsr3 i hi_lt
    rw [← hsb, List.getElem?_eq_getElem hidx] at heq; rw [← heq]; rfl
  have hsb1_lt : (sb1[radixSrcOff use0 n + i]?.getD 0#32).toNat < n := hsrc_lt i hi_lt
  have hsid_lt : (s.scratch.scratch_buf[radixSrcOff use0 n + i]'hidx).toNat < n := by
    rw [hsid_eq]; exact hsb1_lt
  have hsid64 : (s.scratch.scratch_buf[radixSrcOff use0 n + i]'hidx).setWidth 64 * 8#64 =
      BitVec.ofNat 64 (8 * (s.scratch.scratch_buf[radixSrcOff use0 n + i]'hidx).toNat) := by
    rw [bv32_zext64_eq]; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, show (8#64).toNat = 8 from rfl]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega), Nat.mul_comm]
  refine ⟨loadVal_sb32 hidx hsrc_i hm3, hsid_lt, ?_, ?_⟩
  · have hld := loadVal_sb64 (idx := (s.scratch.scratch_buf[radixSrcOff use0 n + i]'hidx).toNat)
      (by rw [hsb_len]; omega) (congrArg (c.pScratchBuf + ·) hsid64) hm3
    let sid_n := (s.scratch.scratch_buf[radixSrcOff use0 n + i]'hidx).toNat
    have heq : pairU64At s.scratch.scratch_buf sid_n = pairU64At sb3 sid_n := by
      have h1 : s.scratch.scratch_buf[2 * sid_n]? = sb3[2 * sid_n]? := congrArg (·[2 * sid_n]?) hsb
      have h2 : s.scratch.scratch_buf[2 * sid_n + 1]? = sb3[2 * sid_n + 1]? :=
        congrArg (·[2 * sid_n + 1]?) hsb
      dsimp only [pairU64At]; rw [h1, h2]
    rwa [heq] at hld
  · change pairU64At sb3 (s.scratch.scratch_buf[radixSrcOff use0 n + i]'hidx).toNat = _
    rw [hsid_eq]; unfold pairU64At; rw [hrk3 _ (by omega), hrk3 _ (by omega)]

theorem radix_btv_nat {sb1 sb3 : List (BitVec 32)} {shift : BitVec 64} {idx : Nat}
    {sid : BitVec 32}
    (hrk_eq : pairU64At sb3 sid.toNat = pairU64At sb1 (sb1[idx]?.getD 0#32).toNat) :
    ((pairU64At sb3 sid.toNat >>> shift) &&& 255#64).toNat =
      ((pairU64At sb1 (sb1[idx]?.getD 0#32).toNat >>> shift.toNat) &&& 255#64).toNat := by
  rw [hrk_eq, BitVec.toNat_and, BitVec.toNat_and, BitVec.toNat_ushiftRight]; rfl

theorem radix_ptr_eqs (c : FullCfg) (n : BitVec 64) (hn29 : n.toNat < 2 ^ 29) :
    c.pScratchBuf + (2#64 * n) * 4#64 = c.pScratchBuf + BitVec.ofNat 64 (4 * (2 * n.toNat)) ∧
    (c.pScratchBuf + (2#64 * n) * 4#64) + n * 4#64 =
      c.pScratchBuf + BitVec.ofNat 64 (4 * (3 * n.toNat)) ∧
    c.pScratchBuf + (2#64 * n) * 8#64 = c.pScratchBuf + BitVec.ofNat 64 (8 * (2 * n.toNat)) ∧
    (∀ b : BitVec 64, b.toNat < 256 →
      (c.pScratchBuf + (2#64 * n) * 8#64) + b * 8#64 =
        c.pScratchBuf + BitVec.ofNat 64 (8 * (2 * n.toNat + b.toNat))) := by
  have h1 : c.pScratchBuf + (2#64 * n) * 4#64 =
      c.pScratchBuf + BitVec.ofNat 64 (4 * (2 * n.toNat)) := by
    congr 1; apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_mul]; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [Nat.mul_comm]
  have h2 : (c.pScratchBuf + (2#64 * n) * 4#64) + n * 4#64 =
      c.pScratchBuf + BitVec.ofNat 64 (4 * (3 * n.toNat)) := by
    rw [h1, BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), show 4 * (2 * n.toNat) + n.toNat * 4 =
      4 * (3 * n.toNat) by omega, Nat.mod_eq_of_lt (by omega)]
  have h3 : c.pScratchBuf + (2#64 * n) * 8#64 =
      c.pScratchBuf + BitVec.ofNat 64 (8 * (2 * n.toNat)) := by
    congr 1; apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_mul]; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [Nat.mul_comm]
  refine ⟨h1, h2, h3, fun b hb => ?_⟩
  rw [h3, BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), show 8 * (2 * n.toNat) + b.toNat * 8 =
    8 * (2 * n.toNat + b.toNat) by omega, Nat.mod_eq_of_lt (by omega)]

theorem radix_init_step {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m0 : Mem 64}
    {sb0 : List (BitVec 32)} {n i : BitVec 64} (rk : BitVec 64)
    (hsb : s.scratch.scratch_buf = sb0) (hlen0 : sb0.length = c.scratch_cap)
    (hcap : 4 * n.toNat + 512 ≤ c.scratch_cap) (hi_lt : i.toNat < n.toNat)
    (hn29 : n.toNat < 2 ^ 29) (hidx0 : c.pScratchBuf + (2#64 * n) * 4#64 =
      c.pScratchBuf + BitVec.ofNat 64 (4 * (2 * n.toNat)))
    (hidx0_lt : ∀ k < i.toNat, (sb0[2 * n.toNat + k]?.getD 0#32).toNat < n.toNat)
    (hm0 : (FullMem c s ⋆ R) m0) :
    let idx0P := c.pScratchBuf + (2#64 * n) * 4#64
    let sb0a := sbWithU64 sb0 i.toNat rk
    let sb0b := sb0a.set (2 * n.toNat + i.toNat) (i.setWidth 32)
    storeOk m0 i64 (c.pScratchBuf + i * 8#64) ∧
    storeOk (storeMem m0 i64 (c.pScratchBuf + i * 8#64) rk) i32 (idx0P + i * 4#64) ∧
    sb0b.length = c.scratch_cap ∧
    (∀ k < i.toNat + 1, (sb0b[2 * n.toNat + k]?.getD 0#32).toNat < n.toNat) ∧
    (FullMem c { s with scratch := { s.scratch with scratch_buf := sb0b } } ⋆ R)
      (storeMem (storeMem m0 i64 (c.pScratchBuf + i * 8#64) rk) i32 (idx0P + i * 4#64)
        (i.setWidth 32)) := by
  intro idx0P sb0a sb0b
  have hrki : c.pScratchBuf + i * 8#64 = c.pScratchBuf + BitVec.ofNat 64 (8 * i.toNat) := by
    congr 1; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, show (8#64).toNat = 8 from rfl]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mul_comm]
  obtain ⟨hok1, hst1⟩ := store_sb64 rk (by rw [hsb, hlen0]; omega) hrki hm0
  have hidx0p := radix_addr_add_bv (2 * n.toNat) i (by omega) hidx0
  have hlen0a : (sbWithU64 s.scratch.scratch_buf i.toNat rk).length = c.scratch_cap := by
    rw [sbWithU64_len, hsb, hlen0]
  obtain ⟨hok2, hst2⟩ := store_sb32 (i.setWidth 32) (by rw [hlen0a]; omega) hidx0p hst1
  refine ⟨hok1, hok2, by dsimp only [sb0b]; rw [List.length_set, sbWithU64_len, hlen0],
    fun k hk => ?_, ?_⟩
  · by_cases hki : k = i.toNat
    · subst hki; dsimp only [sb0b]
      rw [List.getElem?_set_self (by rw [sbWithU64_len, hlen0]; omega), Option.getD_some,
        BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; exact hi_lt
    · dsimp only [sb0b]; rw [List.getElem?_set_ne (by omega)]
      rw [sbWithU64_getElem?_gt (by omega)]; exact hidx0_lt k (by omega)
  · simpa [hsb, sb0a, sb0b] using hst2

theorem radix_zero_step {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m2 : Mem 64}
    {sb1 sb2 : List (BitVec 32)} {n : Nat} {b cntP : BitVec 64}
    (hsb : s.scratch.scratch_buf = sb2) (hlen2 : sb2.length = c.scratch_cap)
    (hcap : 4 * n + 512 ≤ c.scratch_cap) (hb_lt : b.toNat < 256)
    (hcnt_addr : cntP + b * 8#64 = c.pScratchBuf + BitVec.ofNat 64 (8 * (2 * n + b.toNat)))
    (hpre2 : ∀ j, j < 4 * n → sb2[j]? = sb1[j]?)
    (hzr2 : ∀ k < b.toNat, pairU64At sb2 (2 * n + k) = 0#64)
    (hm2 : (FullMem c s ⋆ R) m2) :
    let sb2' := sbWithU64 sb2 (2 * n + b.toNat) 0#64
    storeOk m2 i64 (cntP + b * 8#64) ∧
    sb2'.length = c.scratch_cap ∧
    (∀ j, j < 4 * n → sb2'[j]? = sb1[j]?) ∧
    (∀ k < b.toNat + 1, pairU64At sb2' (2 * n + k) = 0#64) ∧
    (FullMem c { s with scratch := { s.scratch with scratch_buf := sb2' } } ⋆ R)
      (storeMem m2 i64 (cntP + b * 8#64) 0#64) := by
  intro sb2'
  obtain ⟨hok, hst⟩ := store_sb64 0#64 (by rw [hsb, hlen2]; omega) hcnt_addr hm2
  refine ⟨hok, by rw [sbWithU64_len, hlen2], fun j hj => by
      rw [sbWithU64_getElem?_lt (by omega)]; exact hpre2 j hj,
    fun k hk => by
      by_cases hkb : k = b.toNat
      · subst hkb; exact pairU64At_sbWithU64_self (by rw [hlen2]; omega)
      · rw [pairU64At_sbWithU64_ne (by omega)]; exact hzr2 k (by omega),
    by simpa [hsb, sb2'] using hst⟩

theorem radix_count_step {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m3 : Mem 64}
    {sb1 sb3 : List (BitVec 32)} {keyFn : Nat → Nat} {n : Nat} {btv cntP : BitVec 64} {i : Nat}
    (hsb : s.scratch.scratch_buf = sb3) (hlen3 : sb3.length = c.scratch_cap)
    (hcap : 4 * n + 512 ≤ c.scratch_cap) (hi_lt : i < n) (hn29 : n < 2 ^ 29)
    (hpre3 : ∀ j, j < 4 * n → sb3[j]? = sb1[j]?)
    (hcnt3 : ∀ k < 256, (pairU64At sb3 (2 * n + k)).toNat = countPrefix keyFn i k)
    (hbt_lt : btv.toNat < 256) (hbt_nat : btv.toNat = keyFn i)
    (hcnt_addr : cntP + btv * 8#64 = c.pScratchBuf + BitVec.ofNat 64 (8 * (2 * n + btv.toNat)))
    (hm3 : (FullMem c s ⋆ R) m3) :
    let cv := pairU64At sb3 (2 * n + btv.toNat)
    let sb3' := sbWithU64 sb3 (2 * n + btv.toNat) (cv + 1#64)
    loadVal m3 i64 (cntP + btv * 8#64) = some cv ∧
    storeOk m3 i64 (cntP + btv * 8#64) ∧
    sb3'.length = c.scratch_cap ∧
    (∀ j, j < 4 * n → sb3'[j]? = sb1[j]?) ∧
    (∀ k < 256, (pairU64At sb3' (2 * n + k)).toNat = countPrefix keyFn (i + 1) k) ∧
    (FullMem c { s with scratch := { s.scratch with scratch_buf := sb3' } } ⋆ R)
      (storeMem m3 i64 (cntP + btv * 8#64) (cv + 1#64)) := by
  intro cv sb3'
  have hld := loadVal_sb64 (by rw [hsb, hlen3]; omega) hcnt_addr hm3
  rw [hsb] at hld
  have hcv1_nat : (cv + 1#64).toNat = countPrefix keyFn i btv.toNat + 1 := by
    have hle := countPrefix_le keyFn i btv.toNat
    dsimp only [cv]; rw [bv64_succ_toNat _ (by rw [hcnt3 btv.toNat hbt_lt]; omega),
      hcnt3 btv.toNat hbt_lt]
  obtain ⟨hok, hst⟩ := store_sb64 (cv + 1#64) (by rw [hsb, hlen3]; omega) hcnt_addr hm3
  obtain ⟨hp', hc'⟩ := radix_count_inv hlen3 hcap hpre3 hcnt3 hbt_lt hbt_nat hcv1_nat
  exact ⟨hld, hok, by rw [sbWithU64_len, hlen3], hp', hc', by simpa [hsb, sb3'] using hst⟩

theorem radix_pref_step {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m4 : Mem 64}
    {sb1 sb4 : List (BitVec 32)} {keyFn : Nat → Nat} {n : Nat} {pos bp cntP : BitVec 64}
    (hsb : s.scratch.scratch_buf = sb4) (hlen4 : sb4.length = c.scratch_cap)
    (hcap : 4 * n + 512 ≤ c.scratch_cap) (hn29 : n < 2 ^ 29)
    (hkey_lt : ∀ k < n, keyFn k < 256) (hbp_lt : bp.toNat < 256)
    (hpos_eq : pos.toNat = sumBuckets keyFn n bp.toNat)
    (hcnt_addr : cntP + bp * 8#64 = c.pScratchBuf + BitVec.ofNat 64 (8 * (2 * n + bp.toNat)))
    (hpre4 : ∀ j, j < 4 * n → sb4[j]? = sb1[j]?)
    (hpref4 : ∀ k < bp.toNat, (pairU64At sb4 (2 * n + k)).toNat = sumBuckets keyFn n k)
    (hrem4 : ∀ k, bp.toNat ≤ k → k < 256 →
      (pairU64At sb4 (2 * n + k)).toNat = countPrefix keyFn n k)
    (hm4 : (FullMem c s ⋆ R) m4) :
    let cntv := pairU64At sb4 (2 * n + bp.toNat)
    let sb4' := sbWithU64 sb4 (2 * n + bp.toNat) pos
    loadVal m4 i64 (cntP + bp * 8#64) = some cntv ∧
    storeOk m4 i64 (cntP + bp * 8#64) ∧
    (pos + cntv).toNat = sumBuckets keyFn n (bp.toNat + 1) ∧
    sb4'.length = c.scratch_cap ∧
    (∀ j, j < 4 * n → sb4'[j]? = sb1[j]?) ∧
    (∀ k < bp.toNat + 1, (pairU64At sb4' (2 * n + k)).toNat = sumBuckets keyFn n k) ∧
    (∀ k, bp.toNat + 1 ≤ k → k < 256 →
      (pairU64At sb4' (2 * n + k)).toNat = countPrefix keyFn n k) ∧
    (FullMem c { s with scratch := { s.scratch with scratch_buf := sb4' } } ⋆ R)
      (storeMem m4 i64 (cntP + bp * 8#64) pos) := by
  intro cntv sb4'
  have hld := loadVal_sb64 (by rw [hsb, hlen4]; omega) hcnt_addr hm4
  rw [hsb] at hld
  obtain ⟨hok, hst⟩ := store_sb64 pos (by rw [hsb, hlen4]; omega) hcnt_addr hm4
  have hsum_next : sumBuckets keyFn n (bp.toNat + 1) ≤ n := by
    have htot := sumBuckets_eq_n keyFn n hkey_lt
    have hmn := sumBuckets_mono keyFn n (show bp.toNat + 1 ≤ 256 by omega)
    omega
  have hsum_unfold : sumBuckets keyFn n bp.toNat + countPrefix keyFn n bp.toNat ≤ n := by
    simpa [sumBuckets] using hsum_next
  have hpos1 : (pos + cntv).toNat = sumBuckets keyFn n (bp.toNat + 1) := by
    dsimp only [cntv]
    rw [BitVec.toNat_add, hpos_eq, hrem4 bp.toNat (Nat.le_refl _) hbp_lt,
      Nat.mod_eq_of_lt (by omega)]
    rfl
  obtain ⟨hpa, hpb, hpc⟩ := radix_pref_inv hlen4 hcap hbp_lt hpos_eq hpre4 hpref4 hrem4
  refine ⟨hld, hok, hpos1, by rw [sbWithU64_len, hlen4], hpa, hpb, hpc, ?_⟩
  simpa [hsb, sb4'] using hst

theorem radix_scatter_step {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m5 : Mem 64}
    {sb1 sb5 : List (BitVec 32)} {keyFn : Nat → Nat} {use0 : Bool} {n is_ cap : Nat}
    {dst cntP btv : BitVec 64} {id32 : BitVec 32}
    (hsb : s.scratch.scratch_buf = sb5) (hlen5 : sb5.length = cap) (hcap : 4 * n + 512 ≤ cap)
    (hn29 : n < 2 ^ 29) (hkey_lt : ∀ k < n, keyFn k < 256)
    (hdst_eq : dst = c.pScratchBuf + BitVec.ofNat 64 (4 * radixDstOff use0 n))
    (hcnt_addr : cntP + btv * 8#64 = c.pScratchBuf + BitVec.ofNat 64 (8 * (2 * n + btv.toNat)))
    (hrk5 : ∀ j, j < 2 * n → sb5[j]? = sb1[j]?)
    (hsr5 : ∀ k < n, sb5[radixSrcOff use0 n + k]? = sb1[radixSrcOff use0 n + k]?)
    (hcnt5 : ∀ b < 256, (pairU64At sb5 (2 * n + b)).toNat =
      sumBuckets keyFn n b + countPrefix keyFn is_ b)
    (hdst5 : ∀ b < 256, ∀ p, sumBuckets keyFn n b ≤ p →
      p < sumBuckets keyFn n b + countPrefix keyFn is_ b →
      (sb5[radixDstOff use0 n + p]?.getD 0#32).toNat < n)
    (hbt_lt : btv.toNat < 256) (hbt_nat : btv.toNat = keyFn is_)
    (his_lt : is_ < n) (hid_lt : id32.toNat < n) (hm5 : (FullMem c s ⋆ R) m5) :
    let dpos := pairU64At sb5 (2 * n + btv.toNat)
    let sb5' := sb5.set (radixDstOff use0 n + dpos.toNat) id32
    let sb'' := sbWithU64 sb5' (2 * n + btv.toNat) (dpos + 1#64)
    loadVal m5 i64 (cntP + btv * 8#64) = some dpos ∧
    storeOk m5 i32 (dst + BitVec.ofNat 64 dpos.toNat * 4#64) ∧
    storeOk (storeMem m5 i32 (dst + BitVec.ofNat 64 dpos.toNat * 4#64) id32) i64
      (cntP + btv * 8#64) ∧
    sb''.length = cap ∧
    (∀ j, j < 2 * n → sb''[j]? = sb1[j]?) ∧
    (∀ k < n, sb''[radixSrcOff use0 n + k]? = sb1[radixSrcOff use0 n + k]?) ∧
    (∀ b < 256, (pairU64At sb'' (2 * n + b)).toNat =
      sumBuckets keyFn n b + countPrefix keyFn (is_ + 1) b) ∧
    (∀ b < 256, ∀ p, sumBuckets keyFn n b ≤ p →
      p < sumBuckets keyFn n b + countPrefix keyFn (is_ + 1) b →
      (sb''[radixDstOff use0 n + p]?.getD 0#32).toNat < n) ∧
    (FullMem c { s with scratch := { s.scratch with scratch_buf := sb'' } } ⋆ R)
      (storeMem (storeMem m5 i32 (dst + BitVec.ofNat 64 dpos.toNat * 4#64) id32) i64
        (cntP + btv * 8#64) (dpos + 1#64)) := by
  intro dpos sb5' sb''
  have hld := loadVal_sb64 (by rw [hsb, hlen5]; omega) hcnt_addr hm5
  rw [hsb] at hld
  have hdpos_eq := hcnt5 btv.toNat hbt_lt
  have hdpos_lt_b : dpos.toNat < sumBuckets keyFn n (btv.toNat + 1) := by
    dsimp only [dpos]; rw [hdpos_eq, sumBuckets]
    have := countPrefix_lt_of_eq keyFn his_lt hbt_nat.symm; omega
  have hsum_le_n : sumBuckets keyFn n (btv.toNat + 1) ≤ n := by
    have htot := sumBuckets_eq_n keyFn n hkey_lt
    have hmn := sumBuckets_mono keyFn n (show btv.toNat + 1 ≤ 256 by omega)
    omega
  have hdpos_lt : dpos.toNat < n := Nat.lt_of_lt_of_le hdpos_lt_b hsum_le_n
  have hdst_idx : radixDstOff use0 n + dpos.toNat < s.scratch.scratch_buf.length := by
    rw [hsb, hlen5]; exact radixDstOff_lt use0 hdpos_lt hcap
  have hdst_le := radixDstOff_le use0 n
  have hdst_p := radix_addr_add (radixDstOff use0 n) dpos.toNat (by omega) hdst_eq
  obtain ⟨hok1, hst1⟩ := store_sb32 id32 hdst_idx hdst_p hm5
  have h5'len : sb5'.length = cap := by dsimp only [sb5']; rw [List.length_set, hlen5]
  have hsb1 : ({ s with scratch := { s.scratch with
      scratch_buf := s.scratch.scratch_buf.set (radixDstOff use0 n + dpos.toNat) id32 }
      }).scratch.scratch_buf = sb5' := by simp [hsb, sb5']
  obtain ⟨hok2, hst2⟩ := store_sb64 (dpos + 1#64) (by rw [hsb1, h5'len]; omega) hcnt_addr hst1
  obtain ⟨ha, hb, hc, hd⟩ := radix_scatter_inv hkey_lt hlen5 hcap hrk5 hsr5 hcnt5 hdst5
    hbt_lt hbt_nat hdpos_lt hdpos_eq his_lt hid_lt hn29
  refine ⟨hld, hok1, hok2, by rw [sbWithU64_len, h5'len], ha, hb, hc, hd, ?_⟩
  simpa [hsb, sb5', sb''] using hst2

theorem radix_scatter_reload {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m5 : Mem 64} {sb5 : List (BitVec 32)} {keyFn : Nat → Nat} {use0 : Bool}
    {n is_ cap : Nat} {dst cntP btv : BitVec 64} (id32 : BitVec 32)
    (hsb : s.scratch.scratch_buf = sb5) (hlen5 : sb5.length = cap) (hcap : 4 * n + 512 ≤ cap)
    (hn29 : n < 2 ^ 29) (hkey_lt : ∀ k < n, keyFn k < 256)
    (hdst_eq : dst = c.pScratchBuf + BitVec.ofNat 64 (4 * radixDstOff use0 n))
    (hcnt_addr : cntP + btv * 8#64 = c.pScratchBuf + BitVec.ofNat 64 (8 * (2 * n + btv.toNat)))
    (hcnt5 : ∀ b < 256, (pairU64At sb5 (2 * n + b)).toNat =
      sumBuckets keyFn n b + countPrefix keyFn is_ b)
    (hbt_lt : btv.toNat < 256) (hbt_nat : btv.toNat = keyFn is_)
    (his_lt : is_ < n) (hm5 : (FullMem c s ⋆ R) m5) :
    let dpos := pairU64At sb5 (2 * n + btv.toNat)
    loadVal (storeMem m5 i32 (dst + dpos * 4#64) id32) i64 (cntP + btv * 8#64) = some dpos := by
  intro dpos
  have hdpos_lt : dpos.toNat < n := by
    have h1 := hcnt5 btv.toNat hbt_lt
    have h2 := countPrefix_lt_of_eq keyFn his_lt hbt_nat.symm
    have h3 := sumBuckets_mono keyFn n (show btv.toNat + 1 ≤ 256 by omega)
    have h4 := sumBuckets_eq_n keyFn n hkey_lt
    have h5 : sumBuckets keyFn n (btv.toNat + 1) =
        sumBuckets keyFn n btv.toNat + countPrefix keyFn n btv.toNat := by simp [sumBuckets]
    change dpos.toNat = _ at h1; omega
  have hdst_le := radixDstOff_le use0 n
  have hdst_p := radix_addr_add_bv (radixDstOff use0 n) dpos (by omega) hdst_eq
  obtain ⟨_, hst1⟩ :=
    store_sb32 id32 (by rw [hsb, hlen5]; exact radixDstOff_lt use0 hdpos_lt hcap) hdst_p hm5
  have hld := loadVal_sb64 (by simp [hsb, hlen5]; omega) hcnt_addr hst1
  simp only [hsb] at hld
  have hne : radixDstOff use0 n + dpos.toNat < 2 * (2 * n + btv.toNat) := by
    cases use0 <;> simp [radixDstOff] <;> omega
  have hpair : pairU64At (sb5.set (radixDstOff use0 n + dpos.toNat) id32) (2 * n + btv.toNat) =
      pairU64At sb5 (2 * n + btv.toNat) := by
    unfold pairU64At
    rw [List.getElem?_set_ne (Nat.ne_of_lt hne),
      List.getElem?_set_ne (Nat.ne_of_lt (Nat.lt_succ_of_lt hne))]
  rwa [hpair] at hld

theorem radix_copy1_step {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m2 : Mem 64}
    {sb2 : List (BitVec 32)} {rr0 : List (BitVec 32)} {use0 : Bool} {n : Nat} {ic1 : BitVec 64}
    {src tmprr : BitVec 64}
    (hsb : s.scratch.scratch_buf = sb2) (hrr : s.scratch.red_refs = rr0)
    (hlen2 : sb2.length = c.scratch_cap) (hrr_len : rr0.length = c.red_cap)
    (hcap : 4 * n + 512 ≤ c.scratch_cap) (hn_cap : n ≤ c.red_cap) (hn29 : n < 2 ^ 29)
    (hic1_lt : ic1.toNat < n)
    (hsrc_eq : src = c.pScratchBuf + BitVec.ofNat 64 (4 * radixSrcOff use0 n))
    (htmpeq : tmprr = c.pScratchBuf + BitVec.ofNat 64 (4 * radixDstOff use0 n))
    (hsr2 : ∀ k < n, (sb2[radixSrcOff use0 n + k]?.getD 0#32).toNat < n)
    (hcp2 : ∀ k < ic1.toNat, ∃ j < n, sb2[radixDstOff use0 n + k]? = rr0[j]?)
    (hm2 : (FullMem c s ⋆ R) m2) :
    let hsrc_idx : radixSrcOff use0 n + ic1.toNat < sb2.length := by
      rw [hlen2]; exact radixSrcOff_lt use0 hic1_lt hcap
    let si := sb2[radixSrcOff use0 n + ic1.toNat]'hsrc_idx
    let hsi_rr : (si.setWidth 64).toNat < rr0.length := by
      have h1 := hsr2 ic1.toNat hic1_lt
      rw [List.getElem?_eq_getElem hsrc_idx, Option.getD_some] at h1
      change (si.setWidth 64).toNat < rr0.length
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega), hrr_len]
      exact Nat.lt_of_lt_of_le h1 hn_cap
    let sb2' := sb2.set (radixDstOff use0 n + ic1.toNat) (rr0[(si.setWidth 64).toNat]'hsi_rr)
    loadVal m2 i32 (src + ic1 * 4#64) = some si ∧
    loadVal m2 i32 (c.pRedRefs + si.setWidth 64 * 4#64) =
      some (rr0[(si.setWidth 64).toNat]'hsi_rr) ∧
    storeOk m2 i32 (tmprr + ic1 * 4#64) ∧
    sb2'.length = c.scratch_cap ∧
    (∀ k < n, (sb2'[radixSrcOff use0 n + k]?.getD 0#32).toNat < n) ∧
    (∀ k < ic1.toNat + 1, ∃ j < n, sb2'[radixDstOff use0 n + k]? = rr0[j]?) ∧
    (FullMem c { s with scratch := { s.scratch with scratch_buf := sb2' } } ⋆ R)
      (storeMem m2 i32 (tmprr + ic1 * 4#64) (rr0[(si.setWidth 64).toNat]'hsi_rr)) := by
  intro hsrc_idx si hsi_rr sb2'
  have hsrc_le := radixSrcOff_le use0 n
  have hdst_le := radixDstOff_le use0 n
  have hsrc_i := radix_addr_add_bv (radixSrcOff use0 n) ic1 (by omega) hsrc_eq
  have hld1 := loadVal_sb32 (by rw [hsb]; exact hsrc_idx) hsrc_i hm2
  have hld1_eq : some (s.scratch.scratch_buf[radixSrcOff use0 n + ic1.toNat]'(by
      rw [hsb]; exact hsrc_idx)) = some si := by
    rw [← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem, hsb]
  rw [hld1_eq] at hld1
  have hsi_lt : si.toNat < n := by
    have := hsr2 ic1.toNat hic1_lt
    rwa [List.getElem?_eq_getElem hsrc_idx, Option.getD_some] at this
  have hsi64_lt : (si.setWidth 64).toNat < n := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; exact hsi_lt
  have hrr_ptr : c.pRedRefs + si.setWidth 64 * 4#64 =
      c.pRedRefs + BitVec.ofNat 64 (4 * (si.setWidth 64).toNat) := by
    congr 1; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      show (4#64).toNat = 4 from rfl]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega), Nat.mul_comm]
  have hld2 := load_full_red_refs (by rw [hrr]; exact hsi_rr) hm2
  have hld2_eq : some (s.scratch.red_refs[(si.setWidth 64).toNat]'(by rw [hrr]; exact hsi_rr)) =
      some (rr0[(si.setWidth 64).toNat]'hsi_rr) := by
    rw [← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem, hrr]
  rw [← hrr_ptr, hld2_eq] at hld2
  have htmp_idx : radixDstOff use0 n + ic1.toNat < sb2.length := by
    rw [hlen2]; exact radixDstOff_lt use0 hic1_lt hcap
  have htmp_i := radix_addr_add_bv (radixDstOff use0 n) ic1 (by omega) htmpeq
  obtain ⟨hok, hst⟩ := store_sb32 (rr0[(si.setWidth 64).toNat]'hsi_rr)
    (by rw [hsb]; exact htmp_idx) htmp_i hm2
  have hst_eq : s.scratch.scratch_buf.set (radixDstOff use0 n + ic1.toNat)
      (rr0[(si.setWidth 64).toNat]'hsi_rr) = sb2' := by rw [hsb]
  refine ⟨hld1, hld2, hok, by dsimp only [sb2']; rw [List.length_set, hlen2],
    fun k hk => ?_, fun k hk => ?_, by rwa [hst_eq] at hst⟩
  · dsimp only [sb2']
    rw [List.getElem?_set_ne (by cases use0 <;> simp [radixSrcOff, radixDstOff] <;> omega)]
    exact hsr2 k hk
  · by_cases hkc : k = ic1.toNat
    · subst hkc; refine ⟨_, hsi_lt, ?_⟩
      dsimp only [sb2']; rw [List.getElem?_set_self htmp_idx, List.getElem?_eq_getElem (by omega)]
      congr 2
    · dsimp only [sb2']; rw [List.getElem?_set_ne (by omega)]; exact hcp2 k (by omega)

theorem radix_copy2_step {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m3 : Mem 64}
    {sb2 rr0 rr1 : List (BitVec 32)} {use0 : Bool} {n : Nat} {ic2 tmprr : BitVec 64}
    (hsb : s.scratch.scratch_buf = sb2) (hrr : s.scratch.red_refs = rr1)
    (hlen2 : sb2.length = c.scratch_cap) (hlenr1 : rr1.length = c.red_cap)
    (hcap : 4 * n + 512 ≤ c.scratch_cap) (hn_cap : n ≤ c.red_cap) (hn29 : n < 2 ^ 29)
    (hic2_lt : ic2.toNat < n)
    (htmpeq : tmprr = c.pScratchBuf + BitVec.ofNat 64 (4 * radixDstOff use0 n))
    (hcp2 : ∀ k < n, ∃ j < n, sb2[radixDstOff use0 n + k]? = rr0[j]?)
    (hcpr1 : ∀ k < ic2.toNat, ∃ j < n, rr1[k]? = rr0[j]?)
    (hm3 : (FullMem c s ⋆ R) m3) :
    let htmp_idx : radixDstOff use0 n + ic2.toNat < sb2.length := by
      rw [hlen2]; exact radixDstOff_lt use0 hic2_lt hcap
    let v := sb2[radixDstOff use0 n + ic2.toNat]'htmp_idx
    let rr1' := rr1.set ic2.toNat v
    loadVal m3 i32 (tmprr + ic2 * 4#64) = some v ∧
    storeOk m3 i32 (c.pRedRefs + ic2 * 4#64) ∧
    rr1'.length = c.red_cap ∧
    (∀ k < ic2.toNat + 1, ∃ j < n, rr1'[k]? = rr0[j]?) ∧
    (FullMem c { s with scratch := { s.scratch with red_refs := rr1' } } ⋆ R)
      (storeMem m3 i32 (c.pRedRefs + ic2 * 4#64) v) := by
  intro htmp_idx v rr1'
  have hdst_le := radixDstOff_le use0 n
  have htmp_i := radix_addr_add_bv (radixDstOff use0 n) ic2 (by omega) htmpeq
  have hld := loadVal_sb32 (by rw [hsb]; exact htmp_idx) htmp_i hm3
  have hld_eq : some (s.scratch.scratch_buf[radixDstOff use0 n + ic2.toNat]'(by
      rw [hsb]; exact htmp_idx)) = some v := by
    rw [← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem, hsb]
  rw [hld_eq] at hld
  have hic2_rr : ic2.toNat < rr1.length := by omega
  have hrr_ptr : c.pRedRefs + ic2 * 4#64 = c.pRedRefs + BitVec.ofNat 64 (4 * ic2.toNat) := by
    congr 1; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, show (4#64).toNat = 4 from rfl]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mul_comm]
  have hst := store_full_red_refs (c := c) (s := s) (R := R) v (by rw [hrr]; exact hic2_rr) hm3
  have hst_eq : s.scratch.red_refs.set ic2.toNat v = rr1' := by rw [hrr]
  rw [← hrr_ptr, hst_eq] at hst
  refine ⟨hld, hst.1, by dsimp only [rr1']; rw [List.length_set, hlenr1], fun k hk => ?_,
    hst.2⟩
  by_cases hkc : k = ic2.toNat
  · subst hkc; obtain ⟨j, hj, hjeq⟩ := hcp2 ic2.toNat hic2_lt
    refine ⟨j, hj, ?_⟩
    dsimp only [rr1']
    rw [List.getElem?_set_self hic2_rr, ← hjeq, List.getElem?_eq_getElem htmp_idx]
  · dsimp only [rr1']; rw [List.getElem?_set_ne (Ne.symm hkc)]; exact hcpr1 k (by omega)

end

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S5
