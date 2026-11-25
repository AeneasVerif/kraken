/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityVivK6
public import LeanQbe.T.Examples.Kissat.FullSpec
import LeanQbe.T.Examples.Kissat.FullM5OtfsLemmas1
import LeanQbe.T.Examples.Kissat.FullReduceLemmas1
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.MemLemmas
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity `u64` Array Bridge & `full_unwatch_large_fid_wp` (`FullFidelityVivK6Proof0a`)

UNSAT-only `Func.wp` proof (`public section`, `0 @[expose]`, `0 import all`, `std3`) for:
1. `u32`-pair <-> `u64` memory bridge (`packU32Pair`, `loadVal_array32_as_i64`,
   `store_array32_as_i64`) reused by `full_unwatch_large_fid` and `full_bva_commit_fid`.
2. `full_unwatch_large_fid_wp` (`Full.fullUnwatchLargeSpec`, `2x-u64` + `u64` + `u32` shift loop,
   two `u32` sentinel stores).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityVivK6
open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics

/-! ## 1. `u32`-Pair ↔ `u64` Memory Bridge (`array (t := i32)` Load/Store as `i64`) -/

/-- Pack two little-endian `BitVec 32` words `(lo, hi)` into one `BitVec 64`. -/
def packU32Pair (lo hi : BitVec 32) : BitVec 64 :=
  lo.setWidth 64 ||| (hi.setWidth 64 <<< 32)

private theorem nat_or_mul_two_pow : ∀ (k a b : Nat), a < 2 ^ k → a ||| (b * 2 ^ k) = a + b * 2 ^ k
  | 0, a, b, ha => by
    have ha0 : a = 0 := by omega
    subst ha0; simp
  | k + 1, a, b, ha => by
    have hq : a / 2 < 2 ^ k := by rw [Nat.pow_succ] at ha; omega
    have ih := nat_or_mul_two_pow k (a / 2) b hq
    have h1 : (a ||| b * 2 ^ (k + 1)) = 2 * ((a / 2) ||| (b * 2 ^ k)) + a % 2 := by
      generalize hq : a / 2 ||| b * 2 ^ k = q
      apply Nat.eq_of_testBit_eq; intro i
      cases i with
      | zero =>
        have heven : (b * 2 ^ (k + 1)).testBit 0 = false := by
          rw [Nat.mul_comm, Nat.testBit_two_pow_mul]; simp
        rw [Nat.testBit_or, heven, Bool.or_false, Nat.testBit_zero, Nat.testBit_zero]
        have hodd : (2 * q + a % 2) % 2 = a % 2 := by omega
        rw [hodd]
      | succ j =>
        rw [Nat.testBit_or, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ,
          Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_div_cancel _ (by decide : 0 < 2)]
        have hdiv : (2 * q + a % 2) / 2 = q := by omega
        rw [hdiv, ← hq, Nat.testBit_or]
    have hdiv_a : 2 * (a / 2) + a % 2 = a := Nat.div_add_mod a 2
    rw [h1, ih, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm (b * 2 ^ k) 2]
    omega

private theorem packU32Pair_or_eq_add (lo hi : BitVec 32) :
    (lo.setWidth 64 ||| (hi.setWidth 64 <<< 32)).toNat = lo.toNat + hi.toNat * 2 ^ 32 := by
  have hlo : lo.toNat < 2 ^ 32 := lo.isLt
  have hhi : hi.toNat < 2 ^ 32 := hi.isLt
  have hsh : (hi.setWidth 64 <<< 32).toNat = hi.toNat * 2 ^ 32 := by
    simp [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
      Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega : hi.toNat * 2 ^ 32 < 2 ^ 64)]
  rw [BitVec.toNat_or, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : lo.toNat < 2 ^ 64), hsh]
  exact nat_or_mul_two_pow 32 lo.toNat hi.toNat hlo

theorem packU32Pair_lo (lo hi : BitVec 32) : (packU32Pair lo hi).setWidth 32 = lo := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, packU32Pair, packU32Pair_or_eq_add,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt lo.isLt]

theorem packU32Pair_hi (lo hi : BitVec 32) : ((packU32Pair lo hi) >>> 32).setWidth 32 = hi := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, packU32Pair,
    packU32Pair_or_eq_add, Nat.add_mul_div_right _ _ (by decide : 0 < 2 ^ 32),
    Nat.div_eq_of_lt lo.isLt, Nat.zero_add, Nat.mod_eq_of_lt hi.isLt]

theorem packU32Pair_of_bv64 (v : BitVec 64) :
    packU32Pair (v.setWidth 32) ((v >>> 32).setWidth 32) = v := by
  apply BitVec.eq_of_toNat_eq
  rw [packU32Pair, packU32Pair_or_eq_add, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hlt : v.toNat < 2 ^ 64 := v.isLt
  have hdiv : v.toNat / 2 ^ 32 < 2 ^ 32 := by omega
  rw [Nat.mod_eq_of_lt hdiv]
  have := Nat.div_add_mod v.toNat (2 ^ 32)
  omega

private theorem toBytes_add_split (a b : Nat) (x : Int) :
    Int.toBytes (a + b) x = Int.toBytes a x ++ Int.toBytes b (x / (256 : Int) ^ a) := by
  induction a generalizing x with
  | zero => simp [Int.toBytes]
  | succ k ih =>
    rw [Nat.succ_add, Int.toBytes, Int.toBytes, List.cons_append]
    congr 1
    rw [ih (x / 256), Int.ediv_ediv_of_nonneg (by decide : (0 : Int) ≤ 256)]
    congr 2; rw [Int.pow_succ, Int.mul_comm]

private theorem toBytes_eq_of_bv32 (x : BitVec 32) :
    Int.toBytes 4 x.toInt = Int.toBytes 4 (x.toNat : Int) := by
  rw [← Int.toBytes_emod (n := 4), ← Int.toBytes_emod (n := 4) (x := (x.toNat : Int))]
  congr 1; simp only [Int.take, BitVec.toInt_eq_msb_cond]
  cases x.msb
  · rfl
  · simp only [↓reduceIte]
    have hsub : (x.toNat : Int) - (2 ^ 32 : Nat) = (x.toNat : Int) - (2 : Int) ^ 32 := by simp
    rw [hsub, Int.sub_emod_right]

private theorem toBytes_eq_of_bv64 (v : BitVec 64) :
    Int.toBytes 8 v.toInt = Int.toBytes 8 (v.toNat : Int) := by
  rw [← Int.toBytes_emod (n := 8), ← Int.toBytes_emod (n := 8) (x := (v.toNat : Int))]
  congr 1; simp only [Int.take, BitVec.toInt_eq_msb_cond]
  cases v.msb
  · rfl
  · simp only [↓reduceIte]
    have hsub : (v.toNat : Int) - (2 ^ 64 : Nat) = (v.toNat : Int) - (2 : Int) ^ 64 := by simp
    rw [hsub, Int.sub_emod_right]

theorem cell_i32_pair_eq_cell64 (a : BitVec 64) (lo hi : BitVec 32) :
    (cell (t := i32) a lo ⋆ cell (t := i32) (a + 4) hi) = cell64 a (packU32Pair lo hi) := by
  have hlo : lo.toNat < 2 ^ 32 := lo.isLt
  have hpack : Int.toBytes 8 (packU32Pair lo hi).toInt =
      Int.toBytes 4 lo.toInt ++ Int.toBytes 4 hi.toInt := by
    rw [toBytes_eq_of_bv64, toBytes_eq_of_bv32 lo, toBytes_eq_of_bv32 hi,
      show (8 : Nat) = 4 + 4 from rfl, toBytes_add_split 4 4]
    congr 1
    · rw [← Int.toBytes_emod (n := 4), ← Int.toBytes_emod (n := 4) (x := (lo.toNat : Int))]
      congr 1; simp only [Int.take, packU32Pair, packU32Pair_or_eq_add]
      have hcast : ((lo.toNat + hi.toNat * 2 ^ 32 : Nat) : Int) =
          (lo.toNat : Int) + (hi.toNat : Int) * (2 : Int) ^ 32 := by
        rw [Int.natCast_add, Int.natCast_mul, Int.natCast_pow]; rfl
      rw [hcast, Int.add_mul_emod_self_right]
    · congr 1
      rw [packU32Pair, packU32Pair_or_eq_add]
      have hcast : ((lo.toNat + hi.toNat * 2 ^ 32 : Nat) : Int) =
          (lo.toNat : Int) + (hi.toNat : Int) * (256 : Int) ^ 4 := by
        rw [show (256 : Int) ^ 4 = (2 : Int) ^ 32 from by decide,
          Int.natCast_add, Int.natCast_mul, Int.natCast_pow]; rfl
      rw [hcast, Int.add_mul_ediv_right _ _ (by decide),
        Int.ediv_eq_zero_of_lt (by omega) (by omega), Int.zero_add]
  change (Eq ((Int.toBytes 4 (lo.setWidth 32).toInt).At a) ⋆
      Eq ((Int.toBytes 4 (hi.setWidth 32).toInt).At (a + 4))) =
    Eq ((Int.toBytes 8 ((packU32Pair lo hi).setWidth 64).toInt).At a)
  rw [BitVec.setWidth_eq, BitVec.setWidth_eq, BitVec.setWidth_eq, hpack]
  have hlen : (Int.toBytes 4 lo.toInt).length + (Int.toBytes 4 hi.toInt).length ≤ 2 ^ 64 := by
    simp [Int.toBytes_length]
  have ha := Mem.At_append_sep (Int.toBytes 4 lo.toInt) (Int.toBytes 4 hi.toInt) a hlen
  simpa [Int.toBytes_length] using ha.symm

theorem array_i32_focus2 (a : BitVec 64) (xs : List (BitVec 32)) {i : Nat}
    (hi : i + 1 < xs.length) :
    array (t := i32) a xs =
      (cell64 (a + BitVec.ofNat 64 (4 * i)) (packU32Pair xs[i] xs[i + 1]) ⋆
        (array (t := i32) a (xs.take i) ⋆
          array (t := i32) (a + BitVec.ofNat 64 (4 * i) + 8) (xs.drop (i + 2)))) := by
  have hi0 : i < xs.length := by omega
  conv => lhs; rw [← List.take_append_drop i xs, List.drop_eq_getElem_cons hi0,
    List.drop_eq_getElem_cons hi]
  rw [array_append, array_cons, array_cons, List.length_take_of_le (Nat.le_of_lt hi0)]
  have hb4 : (i32 : Ty).bytes = 4 := rfl
  have hadd4 : a + BitVec.ofNat 64 (4 * i) + BitVec.ofNat 64 4 =
      a + BitVec.ofNat 64 (4 * i) + 4 := rfl
  have hadd8 : a + BitVec.ofNat 64 (4 * i) + 4 + BitVec.ofNat 64 4 =
      a + BitVec.ofNat 64 (4 * i) + 8 := by bv_omega
  rw [hb4, hadd4, hadd8]
  have hre : (array (t := i32) a (xs.take i) ⋆
      (cell (t := i32) (a + BitVec.ofNat 64 (4 * i)) xs[i] ⋆
        (cell (t := i32) (a + BitVec.ofNat 64 (4 * i) + 4) xs[i + 1] ⋆
          array (t := i32) (a + BitVec.ofNat 64 (4 * i) + 8) (xs.drop (i + 2))))) =
      ((cell (t := i32) (a + BitVec.ofNat 64 (4 * i)) xs[i] ⋆
        cell (t := i32) (a + BitVec.ofNat 64 (4 * i) + 4) xs[i + 1]) ⋆
        (array (t := i32) a (xs.take i) ⋆
          array (t := i32) (a + BitVec.ofNat 64 (4 * i) + 8) (xs.drop (i + 2)))) := by ac_rfl
  rw [hre, cell_i32_pair_eq_cell64]

theorem array_i32_set2 (a : BitVec 64) (xs : List (BitVec 32)) {i : Nat}
    (hi : i + 1 < xs.length) (lo hiV : BitVec 32) :
    array (t := i32) a ((xs.set i lo).set (i + 1) hiV) =
      (cell64 (a + BitVec.ofNat 64 (4 * i)) (packU32Pair lo hiV) ⋆
        (array (t := i32) a (xs.take i) ⋆
          array (t := i32) (a + BitVec.ofNat 64 (4 * i) + 8) (xs.drop (i + 2)))) := by
  rw [array_i32_focus2 a ((xs.set i lo).set (i + 1) hiV) (i := i) (by simp [hi])]
  have hg0 : ((xs.set i lo).set (i + 1) hiV)[i]'(by simp; omega) = lo := by
    rw [List.getElem_set_ne (by omega), List.getElem_set_self]
  have hg1 : ((xs.set i lo).set (i + 1) hiV)[i + 1]'(by simp [hi]) = hiV := by
    rw [List.getElem_set_self]
  rw [hg0, hg1, List.take_set_of_le (by omega), List.take_set_of_le (Nat.le_refl i),
    List.drop_set_of_lt (by omega), List.drop_set_of_lt (by omega)]

/-- Read two adjacent `i32` array elements `(xs[i], xs[i+1])` as one `i64` word. -/
theorem loadVal_array32_as_i64 {a : BitVec 64} {xs : List (BitVec 32)} {i : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : i + 1 < xs.length)
    (hm : (array (t := i32) a xs ⋆ R) m) :
    loadVal m i64 (a + BitVec.ofNat 64 (4 * i)) = some (packU32Pair xs[i] xs[i + 1]) := by
  rw [array_i32_focus2 a xs hi, sep_assoc] at hm
  exact loadVal_cell64 hm

/-- Store one `i64` word `v` into two adjacent `i32` array elements `(xs[i], xs[i+1])`. -/
theorem store_array32_as_i64 {a : BitVec 64} {xs : List (BitVec 32)} {i : Nat} (v : BitVec 64)
    {R : Mem 64 → Prop} {m : Mem 64} (hi : i + 1 < xs.length)
    (hm : (array (t := i32) a xs ⋆ R) m) :
    storeOk m i64 (a + BitVec.ofNat 64 (4 * i)) ∧
      (array (t := i32) a ((xs.set i (v.setWidth 32)).set (i + 1) ((v >>> 32).setWidth 32)) ⋆ R)
        (storeMem m i64 (a + BitVec.ofNat 64 (4 * i)) v) := by
  rw [array_i32_focus2 a xs hi, sep_assoc] at hm
  obtain ⟨hok, hst⟩ := store_cell64 v hm
  refine ⟨hok, ?_⟩
  rw [array_i32_set2 a xs hi (v.setWidth 32) ((v >>> 32).setWidth 32), packU32Pair_of_bv64,
    sep_assoc]
  exact hst

/-! ## 2. `full_unwatch_large_fid_wp` (`Full.fullUnwatchLargeSpec`, `G1-P2.1b`) -/

section UnwatchLargeFid

open FullM5Otfs Full.FullReduceSpecs Full.FullReduceHelpers

private theorem fid_bv32_lshr31_cases (w : BitVec 32) :
    ((w &&& 0x80000000#32) = 0#32 → (w >>> (31 : Nat)).toNat = 0) ∧
    ((w &&& 0x80000000#32) ≠ 0#32 → (w >>> (31 : Nat)).toNat = 1) ∧
    (w >>> (31 : Nat)).toNat ≤ 1 := by
  have heq : (w >>> (31 : Nat)) = (w >>> 31#32) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ushiftRight]
  rw [heq]
  exact m5_bv32_lshr31_cases w

private theorem fid_unwatch_step_ok {dense : Bool} {k : FullCoreState} {lit off0 end0 : Nat}
    {p : BitVec 64} {w : BitVec 32}
    (hp_ge2 : off0 + 2 ≤ p.toNat) (hpe : p.toNat ≤ end0) (_hend : end0 < 2 ^ 64)
    (hw_some : k.wstk[p.toNat - 1]? = some w)
    (hinv : ∀ F_cur, ModeWatchesInv F_cur k →
      ModeWatchSliceOk dense F_cur k lit off0 (p.toNat - off0) ∧
      ModeWatchSliceOk dense F_cur k lit p.toNat (end0 - p.toNat)) :
    let p' := p - 2#64 + (w >>> (31 : Nat)).setWidth 64
    p'.toNat - off0 < p.toNat - off0 ∧ off0 ≤ p'.toNat ∧ p'.toNat ≤ end0 ∧
    ∀ F_cur, ModeWatchesInv F_cur k →
      ModeWatchSliceOk dense F_cur k lit off0 (p'.toNat - off0) ∧
      ModeWatchSliceOk dense F_cur k lit p'.toNat (end0 - p'.toNat) := by
  intro p'
  have hp2_toNat : (p - 2#64).toNat = p.toNat - 2 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, show (2#64).toNat = 2 from rfl]; omega),
      show (2#64).toNat = 2 from rfl]
  have hsh_le := (fid_bv32_lshr31_cases w).2.2
  have hp'_toNat : p'.toNat = p.toNat - 2 + (w >>> (31 : Nat)).toNat := by
    dsimp only [p']; rw [BitVec.toNat_add, hp2_toNat, zext_toNat _ (by decide)]
    exact Nat.mod_eq_of_lt (by omega)
  refine ⟨by omega, by omega, by omega, fun F_cur hmw => ?_⟩
  obtain ⟨hpre, hsuf⟩ := hinv F_cur hmw
  rcases m5_modeWatchSlice_split_last hpre (by omega) with
    ⟨w0, hw0, hfl0, hne0, hlt0, hent0, hpre1⟩ |
    ⟨_, w0, cr, hw0, hcr, hfl0, hsz0, hlt0, href0, hpre2⟩
  · rw [show off0 + (p.toNat - off0) - 1 = p.toNat - 1 by omega, hw_some] at hw0
    cases hw0
    have hsh1 := (fid_bv32_lshr31_cases w).2.1 hfl0
    have hp'_eq : p'.toNat = p.toNat - 1 := by rw [hp'_toNat, hsh1]; omega
    rw [hp'_eq, show p.toNat - 1 - off0 = p.toNat - off0 - 1 by omega,
      show end0 - (p.toNat - 1) = (end0 - p.toNat) + 1 by omega]
    exact ⟨hpre1, m5_modeWatchSlice_cons_bin hw_some hfl0 hne0 hlt0 hent0
      (by simpa only [show p.toNat - 1 + 1 = p.toNat by omega] using hsuf)⟩
  · rw [show off0 + (p.toNat - off0) - 1 = p.toNat - 1 by omega, hw_some] at hcr
    cases hcr
    have hcr_msb0 : (w &&& 0x80000000#32) = 0#32 := (m5_bv32_lt_highbit_iff w).mp (by omega)
    have hsh0 := (fid_bv32_lshr31_cases w).1 hcr_msb0
    have hp'_eq : p'.toNat = p.toNat - 2 := by rw [hp'_toNat, hsh0]; omega
    rw [hp'_eq, show p.toNat - 2 - off0 = p.toNat - off0 - 2 by omega,
      show end0 - (p.toNat - 2) = (end0 - p.toNat) + 2 by omega]
    rw [show off0 + (p.toNat - off0) - 2 = p.toNat - 2 by omega] at hw0
    exact ⟨hpre2, m5_modeWatchSlice_cons_pair hw0
      (by simpa only [show p.toNat - 2 + 1 = p.toNat - 1 by omega] using hw_some)
      hfl0 hsz0 hlt0 href0 (by simpa only [show p.toNat - 2 + 2 = p.toNat by omega] using hsuf)⟩

private theorem fid_unwatch_fin_inv {dense : Bool} {c : FullCfg} {k : FullCoreState}
    {wstk1 : List (BitVec 32)} {lit p_nat : Nat}
    (hdense : dense = decide (k.dense_mode ≠ 0#64))
    (hlen : k.LengthsOk c) (hlay : WatchStackLayout k) (hlit : lit < 2 * k.cur_vars)
    (hsz2 : 2 ≤ fullWatchSizeCore k lit)
    (hp_ge2 : fullWatchOffCore k lit + 2 ≤ p_nat)
    (hpe : p_nat ≤ fullWatchOffCore k lit + fullWatchSizeCore k lit)
    (hout1 : ∀ i, i < p_nat - 2 ∨ fullWatchOffCore k lit + fullWatchSizeCore k lit - 2 ≤ i →
      wstk1[i]? = k.wstk[i]?)
    (hsh1 : ∀ j, j < fullWatchOffCore k lit + fullWatchSizeCore k lit - p_nat →
      wstk1[(p_nat - 2) + j]? = k.wstk[p_nat + j]?)
    (hinv_found : ∀ F_cur, ModeWatchesInv F_cur k →
      ModeWatchSliceOk dense F_cur k lit (fullWatchOffCore k lit)
        (p_nat - 2 - fullWatchOffCore k lit) ∧
      ModeWatchSliceOk dense F_cur k lit p_nat
        (fullWatchOffCore k lit + fullWatchSizeCore k lit - p_nat)) :
    let off0 := fullWatchOffCore k lit
    let sz0 := fullWatchSizeCore k lit
    let end0 := off0 + sz0
    let wstk2 := (wstk1.set (end0 - 2) 0xFFFFFFFF#32).set (end0 - 1) 0xFFFFFFFF#32
    let wvec' := k.wvec.set (2 * lit + 1) (BitVec.ofNat 32 (sz0 - 2))
    let wu' := k.wusable + 2#64
    WatchStackLayout { k with wvec := wvec', wstk := wstk2, wusable := wu' } ∧
    ∀ F_cur, ModeWatchesInv F_cur k →
      ModeWatchesInv F_cur { k with wvec := wvec', wstk := wstk2, wusable := wu' } := by
  intro off0 sz0 end0 wstk2 wvec' wu'
  have hout_fin : ∀ i, i < off0 ∨ off0 + sz0 ≤ i → wstk2[i]? = k.wstk[i]? := fun i hi => by
    dsimp only [wstk2]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    exact hout1 i (by omega)
  have hpre_fin : ∀ j < p_nat - 2 - off0, wstk2[off0 + j]? = k.wstk[off0 + j]? := fun j hj => by
    dsimp only [wstk2]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    exact hout1 (off0 + j) (Or.inl (by omega))
  have hsuf_fin : ∀ j < end0 - p_nat, wstk2[(p_nat - 2) + j]? = k.wstk[p_nat + j]? := fun j hj => by
    dsimp only [wstk2]
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    exact hsh1 j (by omega)
  have hns_fin : ∀ j < sz0 - 2, wstk2[off0 + j]? ≠ some 0xFFFFFFFF#32 := by
    intro j hj
    by_cases hjp : j < p_nat - 2 - off0
    · rw [hpre_fin j hjp]; exact hlay.no_sentinel lit hlit j (by omega)
    · have hj' : j - (p_nat - 2 - off0) < end0 - p_nat := by omega
      have heq := hsuf_fin (j - (p_nat - 2 - off0)) hj'
      rw [show p_nat - 2 + (j - (p_nat - 2 - off0)) = off0 + j by omega,
        show p_nat + (j - (p_nat - 2 - off0)) = off0 + (j + 2) by omega] at heq
      rw [heq]; exact hlay.no_sentinel lit hlit (j + 2) (by omega)
  refine ⟨(watchStackLayout_shrink_slice hlay hlen hlit (new_sz := sz0 - 2) (by omega) hout_fin
      hns_fin wu' k.num_binary).1, fun F_cur hmw => ?_⟩
  obtain ⟨hpre_ok, hsuf_ok⟩ := hinv_found F_cur hmw
  have hF_refl : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
    rw [CNF.entails_def]; exact fun _ hx => hx
  have hpre_w2 : ModeWatchSliceOk dense F_cur { k with wstk := wstk2 } lit off0
      (p_nat - 2 - off0) :=
    ModeWatchSliceOk.relocate (k := k) (k' := { k with wstk := wstk2 }) (p := off0) (p' := off0)
      hF_refl (Nat.le_refl _) (fun _ hr => hr) hpre_fin hpre_ok
  have hsuf_w2 : ModeWatchSliceOk dense F_cur { k with wstk := wstk2 } lit
      (off0 + (p_nat - 2 - off0)) (end0 - p_nat) :=
    ModeWatchSliceOk.relocate (k := k) (k' := { k with wstk := wstk2 }) (p := p_nat)
      (p' := off0 + (p_nat - 2 - off0)) hF_refl (Nat.le_refl _) (fun _ hr => hr)
      (fun j hj => by
        rw [show off0 + (p_nat - 2 - off0) + j = (p_nat - 2) + j by omega]
        exact hsuf_fin j hj) hsuf_ok
  have hslice_w2 : ModeWatchSliceOk dense F_cur { k with wstk := wstk2 } lit off0 (sz0 - 2) := by
    have happ := m5_modeWatchSlice_append hpre_w2 hsuf_w2
    rwa [show p_nat - 2 - off0 + (end0 - p_nat) = sz0 - 2 by omega] at happ
  subst hdense
  exact modeWatchesInv_shrink_slice hmw hlen hlit (new_sz := sz0 - 2) (by omega) hout_fin wu'
    k.num_binary hslice_w2

private theorem fullMem_wstk_split {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) :
    ∃ F : Mem 64 → Prop,
      (array (t := i32) c.pWstk s.core.wstk ⋆ F) m ∧
      ∀ ws' m', (array (t := i32) c.pWstk ws' ⋆ F) m' →
        (FullMem c { s with core := { s.core with wstk := ws' } } ⋆ R) m' := by
  refine ⟨(dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur
      s.core.d_val ⋆ array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
      (FullCoreByteArrs c s.core ⋆ FullCoreU32A c s.core ⋆ FullCoreU32B c s.core ⋆
        array (t := i32) c.pArena s.core.arena) ⋆
      FullScratchArrays c s.scratch ⋆ c.pad) ⋆ R, ?_, fun ws' m' hm' => ?_⟩
  · unfold FullMem FullCoreArrays FullCoreDynArrs at hm; exact sep_cast hm (by ac_rfl)
  · unfold FullMem FullCoreArrays FullCoreDynArrs; exact sep_cast hm' (by ac_rfl)

private theorem loadVal_fullMem_wstk_i64 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {idx : BitVec 64} (hi : idx.toNat + 1 < s.core.wstk.length)
    (hm : (FullMem c s ⋆ R) m) :
    loadVal m i64 (c.pWstk + idx * 4) =
      some (packU32Pair (s.core.wstk[idx.toNat]'(by omega)) (s.core.wstk[idx.toNat + 1]'hi)) := by
  obtain ⟨F, hmF, _⟩ := fullMem_wstk_split hm
  have h := loadVal_array32_as_i64 hi hmF
  rwa [show c.pWstk + idx * 4 = c.pWstk + BitVec.ofNat 64 (4 * idx.toNat) from by
    rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]]

private theorem loadVal_fullMem_wstk_i64_off8 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {idx : BitVec 64} (hi : idx.toNat + 3 < s.core.wstk.length)
    (hm : (FullMem c s ⋆ R) m) :
    loadVal m i64 (c.pWstk + idx * 4 + 8) =
      some (packU32Pair (s.core.wstk[idx.toNat + 2]'(by omega))
        (s.core.wstk[idx.toNat + 3]'hi)) := by
  obtain ⟨F, hmF, _⟩ := fullMem_wstk_split hm
  have h := loadVal_array32_as_i64 (i := idx.toNat + 2) (by omega) hmF
  have haddr : c.pWstk + idx * 4 + 8 = c.pWstk + BitVec.ofNat 64 (4 * (idx.toNat + 2)) := by
    apply BitVec.eq_of_toNat_eq
    have h4 : (4 : BitVec 64).toNat = 4 := rfl
    have h8 : (8 : BitVec 64).toNat = 8 := rfl
    simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, h4, h8]
    rw [Nat.mul_add]; omega
  rwa [haddr]

private theorem store_fullMem_wstk_i64 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {idx : BitVec 64} (v : BitVec 64) (hi : idx.toNat + 1 < s.core.wstk.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i64 (c.pWstk + idx * 4) ∧
      (FullMem c { s with core := { s.core with
          wstk := (s.core.wstk.set idx.toNat (v.setWidth 32)).set (idx.toNat + 1)
            ((v >>> 32).setWidth 32) } } ⋆ R)
        (storeMem m i64 (c.pWstk + idx * 4) v) := by
  obtain ⟨F, hmF, hback⟩ := fullMem_wstk_split hm
  have haddr : c.pWstk + idx * 4 = c.pWstk + BitVec.ofNat 64 (4 * idx.toNat) := by
    rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]
  obtain ⟨hok, hst⟩ := store_array32_as_i64 v hi hmF
  rw [← haddr] at hok hst
  exact ⟨hok, hback _ _ hst⟩

private theorem store_fullMem_wstk_i64_off8 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {idx : BitVec 64} (v : BitVec 64) (hi : idx.toNat + 3 < s.core.wstk.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i64 (c.pWstk + idx * 4 + 8) ∧
      (FullMem c { s with core := { s.core with
          wstk := (s.core.wstk.set (idx.toNat + 2) (v.setWidth 32)).set (idx.toNat + 3)
            ((v >>> 32).setWidth 32) } } ⋆ R)
        (storeMem m i64 (c.pWstk + idx * 4 + 8) v) := by
  obtain ⟨F, hmF, hback⟩ := fullMem_wstk_split hm
  have haddr : c.pWstk + idx * 4 + 8 = c.pWstk + BitVec.ofNat 64 (4 * (idx.toNat + 2)) := by
    apply BitVec.eq_of_toNat_eq
    have h4 : (4 : BitVec 64).toNat = 4 := rfl
    have h8 : (8 : BitVec 64).toNat = 8 := rfl
    simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, h4, h8]
    rw [Nat.mul_add]; omega
  obtain ⟨hok, hst⟩ := store_array32_as_i64 (i := idx.toNat + 2) v (by omega) hmF
  rw [← haddr] at hok hst
  exact ⟨hok, hback _ _ hst⟩

private theorem shift_step1 {ws orig : List (BitVec 32)} {cap p0 pc : Nat}
    (hlen : ws.length = cap) (hp0 : 2 ≤ p0) (hpc_lo : p0 ≤ pc) (hpc_lt : pc < cap)
    (hout : ∀ i, i < p0 - 2 ∨ pc - 2 ≤ i → ws[i]? = orig[i]?)
    (hsh : ∀ j, j < pc - p0 → ws[(p0 - 2) + j]? = orig[p0 + j]?) :
    let ws' := ws.set (pc - 2) (ws[pc]'(by omega))
    ws'.length = cap ∧
    (∀ i, i < p0 - 2 ∨ (pc + 1) - 2 ≤ i → ws'[i]? = orig[i]?) ∧
    (∀ j, j < (pc + 1) - p0 → ws'[(p0 - 2) + j]? = orig[p0 + j]?) := by
  refine ⟨by simp [hlen], fun i hi => ?_, fun j hj => ?_⟩
  · rw [List.getElem?_set_ne (by omega)]; exact hout i (by omega)
  · by_cases hjeq : j = pc - p0
    · subst hjeq
      have hq : p0 - 2 + (pc - p0) = pc - 2 := by omega
      have hp : p0 + (pc - p0) = pc := by omega
      rw [hq, List.getElem?_set_self (by omega), hp, ← hout pc (Or.inr (by omega)),
        List.getElem?_eq_getElem (by omega)]
    · rw [List.getElem?_set_ne (by omega)]; exact hsh j (by omega)

private theorem shift_step2 {ws orig : List (BitVec 32)} {cap p0 pc : Nat}
    (hlen : ws.length = cap) (hp0 : 2 ≤ p0) (hpc_lo : p0 ≤ pc) (hpc_lt : pc + 1 < cap)
    (hout : ∀ i, i < p0 - 2 ∨ pc - 2 ≤ i → ws[i]? = orig[i]?)
    (hsh : ∀ j, j < pc - p0 → ws[(p0 - 2) + j]? = orig[p0 + j]?) :
    let ws' := (ws.set (pc - 2) (ws[pc]'(by omega))).set (pc - 1) (ws[pc + 1]'(by omega))
    ws'.length = cap ∧
    (∀ i, i < p0 - 2 ∨ (pc + 2) - 2 ≤ i → ws'[i]? = orig[i]?) ∧
    (∀ j, j < (pc + 2) - p0 → ws'[(p0 - 2) + j]? = orig[p0 + j]?) := by
  have hs1 := shift_step1 hlen hp0 hpc_lo (by omega) hout hsh
  have hget1 : (ws.set (pc - 2) (ws[pc]'(by omega)))[pc + 1]'(by simp [hlen]; omega) =
      ws[pc + 1]'(by omega) := by rw [List.getElem_set_ne (by omega)]
  have hs2 := shift_step1 hs1.1 hp0 (by omega : p0 ≤ pc + 1) hpc_lt hs1.2.1 hs1.2.2
  simpa only [show pc + 1 - 2 = pc - 1 by omega, show pc + 1 + 1 = pc + 2 by omega, hget1] using hs2

private theorem shift_step4 {ws orig : List (BitVec 32)} {cap p0 pc : Nat}
    (hlen : ws.length = cap) (hp0 : 2 ≤ p0) (hpc_lo : p0 ≤ pc) (hpc_lt : pc + 3 < cap)
    (hout : ∀ i, i < p0 - 2 ∨ pc - 2 ≤ i → ws[i]? = orig[i]?)
    (hsh : ∀ j, j < pc - p0 → ws[(p0 - 2) + j]? = orig[p0 + j]?) :
    let ws2 := (ws.set (pc - 2) (ws[pc]'(by omega))).set (pc - 1) (ws[pc + 1]'(by omega))
    let ws4 := (ws2.set pc (ws[pc + 2]'(by omega))).set (pc + 1) (ws[pc + 3]'(by omega))
    ws4.length = cap ∧
    (∀ i, i < p0 - 2 ∨ (pc + 4) - 2 ≤ i → ws4[i]? = orig[i]?) ∧
    (∀ j, j < (pc + 4) - p0 → ws4[(p0 - 2) + j]? = orig[p0 + j]?) := by
  have hs2a := shift_step2 hlen hp0 hpc_lo (by omega) hout hsh
  let ws2 := (ws.set (pc - 2) (ws[pc]'(by omega))).set (pc - 1) (ws[pc + 1]'(by omega))
  have hg2 : ws2[pc + 2]'(by simp [ws2, hlen]; omega) = ws[pc + 2]'(by omega) := by
    dsimp only [ws2]; rw [List.getElem_set_ne (by omega), List.getElem_set_ne (by omega)]
  have hg3 : ws2[pc + 3]'(by simp [ws2, hlen]; omega) = ws[pc + 3]'(by omega) := by
    dsimp only [ws2]; rw [List.getElem_set_ne (by omega), List.getElem_set_ne (by omega)]
  have hs2b := shift_step2 hs2a.1 hp0 (by omega : p0 ≤ pc + 2) hpc_lt hs2a.2.1 hs2a.2.2
  simpa only [ws2, show pc + 2 - 2 = pc by omega, show pc + 2 - 1 = pc + 1 by omega,
    show pc + 2 + 2 = pc + 4 by omega, hg2, hg3] using hs2b

/-- `full_unwatch_large_fid` (`2x-u64` + `u64` + `u32` watch-shift loop and two `u32` sentinel
stores) satisfies exact `Full.fullUnwatchLargeSpec` parametrically in `Γ`. -/
theorem full_unwatch_large_fid_wp (Γ : Env) :
    ∀ a m Q X, Full.fullUnwatchLargeSpec a m Q X →
      Func.wp Γ full_unwatch_large_fid_body a m Q X := by
  rintro ⟨h, lit, cref, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hlay, hm, hQ⟩
  have hcv_le := hlen.core_ok.cur_vars_le
  have hwv_len := hlen.core_ok.wvec_len
  have hws_len := hlen.core_ok.wstk_len_arr
  have hwl_le := hlen.core_ok.wlen_le
  have hmax_lt : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  have hwcap_lt : c.wcap < 2 * 2 ^ 28 := c.hwcap
  have hret_same : Q () m :=
    hQ s.core.wvec s.core.wstk s.core.wusable m hlen hlay (fun _ h => h) hm
  let dense : Bool := decide (s.core.dense_mode ≠ 0#64)
  have hnlits_eq :
      ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat = 2 * s.core.cur_vars := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.shiftLeft_eq, Nat.pow_one, Nat.mod_eq_of_lt (by omega)]; omega
  unfold Func.wp full_unwatch_large_fid_body
  c0_hsteps_nogrp
  · exact hret_same
  · exact hret_same
  · exact hret_same
  · have hlit_lt : lit.toNat < 2 * s.core.cur_vars := by
      have h1 : ¬ ((BitVec.ofNat 64 s.core.cur_vars) <<< (1 : Nat)).toNat ≤
          (lit.setWidth 64).toNat := by c0_bound
      rw [hnlits_eq, zext_toNat lit (by decide)] at h1; omega
    have hcr_msb : (cref &&& 0x80000000#32) = 0#32 := by assumption
    have h2l_eq : ((lit.setWidth 64) <<< (1 : Nat)).toNat = 2 * lit.toNat := by
      rw [BitVec.toNat_shiftLeft, zext_toNat lit (by decide), Nat.shiftLeft_eq, Nat.pow_one,
        Nat.mod_eq_of_lt (by omega)]; omega
    have h2l1_eq : (((lit.setWidth 64) <<< (1 : Nat)) + (1 : BitVec 64)).toNat =
        2 * lit.toNat + 1 := by
      rw [BitVec.toNat_add, h2l_eq, show (1 : BitVec 64).toNat = 1 from rfl,
        Nat.mod_eq_of_lt (by omega)]
    have h2l_lt : 2 * lit.toNat < s.core.wvec.length := by omega
    have h2l1_lt : 2 * lit.toNat + 1 < s.core.wvec.length := by omega
    let off0 : Nat := fullWatchOff s lit.toNat
    let sz0 : Nat := fullWatchSize s lit.toNat
    have hoff_idx : (s.core.wvec[2 * lit.toNat]'h2l_lt).toNat = off0 := by
      unfold off0 fullWatchOff fullWatchOffCore
      rw [List.getElem?_eq_getElem h2l_lt, Option.getD_some]
    have hsz_idx : (s.core.wvec[2 * lit.toNat + 1]'h2l1_lt).toNat = sz0 := by
      unfold sz0 fullWatchSize fullWatchSizeCore
      rw [List.getElem?_eq_getElem h2l1_lt, Option.getD_some]
    have hbd_end : off0 + sz0 ≤ s.core.wlen := hlay.bounds lit.toNat hlit_lt
    have hbd0_w : (lit.setWidth 64 <<< (1 : Nat)).toNat < s.core.wvec.length := by
      rw [h2l_eq]; exact h2l_lt
    have hbd1_w : ((lit.setWidth 64 <<< (1 : Nat)) + (1 : BitVec 64)).toNat <
        s.core.wvec.length := by rw [h2l1_eq]; exact h2l1_lt
    have hoff_w : (s.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'hbd0_w).toNat = off0 := by
      simpa only [h2l_eq] using hoff_idx
    have hsz_w :
        (s.core.wvec[((lit.setWidth 64 <<< (1 : Nat)) + (1 : BitVec 64)).toNat]'hbd1_w).toNat =
        sz0 := by simpa only [h2l1_eq] using hsz_idx
    have hsz2 : 2 ≤ sz0 := by
      have h1 : BitVec.toNat (1 : BitVec 64) = 1 := rfl
      have h2 : BitVec.toNat (2 : BitVec 64) = 2 := rfl
      have hmod : (2 * lit.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = 2 * lit.toNat + 1 := by
        rw [h1]; omega
      have hc' : ¬ (s.core.wvec[2 * lit.toNat + 1]'h2l1_lt).toNat < 2 := by
        simpa only [hmod, h2] using hc
      rw [← hsz_idx]; omega
    let end0 : Nat := off0 + sz0
    have hoff64 : (BitVec.setWidth 64
        (s.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'hbd0_w)).toNat = off0 := by
      rw [zext_toNat _ (by decide), hoff_w]
    have hsz64 : (BitVec.setWidth 64
        (s.core.wvec[((lit.setWidth 64 <<< (1 : Nat)) +
          (1 : BitVec 64)).toNat]'hbd1_w)).toNat = sz0 := by
      rw [zext_toNat _ (by decide), hsz_w]
    have hend64 : (BitVec.setWidth 64
          (s.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'hbd0_w) +
        BitVec.setWidth 64
          (s.core.wvec[((lit.setWidth 64 <<< (1 : Nat)) +
            (1 : BitVec 64)).toNat]'hbd1_w)).toNat = end0 := by
      rw [BitVec.toNat_add, hoff64, hsz64]; exact Nat.mod_eq_of_lt (by omega)
    have hoff2_64 : (BitVec.setWidth 64
          (s.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'hbd0_w) + 2#64).toNat =
        off0 + 2 := by
      rw [BitVec.toNat_add, hoff64, show (2#64).toNat = 2 from rfl]
      exact Nat.mod_eq_of_lt (by omega)
    refine wp_loop_inv (ts := [i64])
      (fun (p, ()) m1 =>
        m1 = m ∧ off0 ≤ p.toNat ∧ p.toNat ≤ end0 ∧
        ∀ F_cur, ModeWatchesInv F_cur s.core →
          ModeWatchSliceOk dense F_cur s.core lit.toNat off0 (p.toNat - off0) ∧
          ModeWatchSliceOk dense F_cur s.core lit.toNat p.toNat (end0 - p.toNat))
      (fun (p, ()) _ => p.toNat - off0)
      (fun J1 hLoop1 => ?_) ?_
    · c0_hsteps
      refine hLoop1 _ m ⟨rfl, by rw [hend64]; omega, by rw [hend64]; exact Nat.le_refl _,
        fun F_cur hmw => ?_⟩
      rw [hend64, show end0 - off0 = sz0 by omega, Nat.sub_self]
      exact ⟨modeWatchesInv_slice_of_lt hmw hlit_lt, by
        cases dense <;> simp only [ModeWatchSliceOk, Bool.false_eq_true, ↓reduceIte]
        · exact .empty
        · exact .empty⟩
    · rintro J1 ⟨p, ⟨⟩⟩ m1 ⟨rfl, hop, hpe, hinv⟩ hLoop1
      c0_hsplit
      · have hp_ge2 : off0 + 2 ≤ p.toNat := by
          have hc' : (BitVec.setWidth 64
              (s.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'hbd0_w) + 2#64).toNat ≤
              p.toNat := by c0_bound
          rwa [hoff2_64] at hc'
        have hp1_toNat : (p - 1#64).toNat = p.toNat - 1 := by bv_omega
        have hp2_toNat : (p - 2#64).toNat = p.toNat - 2 := by bv_omega
        have hp1_lt : (p - 1#64).toNat < s.core.wstk.length := by rw [hp1_toNat]; omega
        let w : BitVec 32 := s.core.wstk[(p - 1#64).toNat]'hp1_lt
        have hw_some : s.core.wstk[p.toNat - 1]? = some w := by
          rw [List.getElem?_eq_getElem (by omega : p.toNat - 1 < s.core.wstk.length)]
          have : s.core.wstk[(p - 1#64).toNat]'hp1_lt = s.core.wstk[p.toNat - 1]'(by omega) := by
            simp only [hp1_toNat]
          exact congrArg some this.symm
        c0_hsplit
        · have hw_eq : w = cref := by assumption
          have hinv_found : ∀ F_cur, ModeWatchesInv F_cur s.core →
              ModeWatchSliceOk dense F_cur s.core lit.toNat off0 (p.toNat - 2 - off0) ∧
              ModeWatchSliceOk dense F_cur s.core lit.toNat p.toNat (end0 - p.toNat) := by
            intro F_cur hmw
            obtain ⟨hpre, hsuf⟩ := hinv F_cur hmw
            rcases m5_modeWatchSlice_split_last hpre (by omega) with
              ⟨w0, hw0, hfl0, _⟩ | ⟨_, _, _, _, _, _, _, _, _, hpre2⟩
            · rw [show off0 + (p.toNat - off0) - 1 = p.toNat - 1 by omega, hw_some] at hw0
              cases hw0; rw [hw_eq] at hfl0; exact absurd hcr_msb hfl0
            · exact ⟨by simpa only [show p.toNat - off0 - 2 = p.toNat - 2 - off0 by omega]
                using hpre2, hsuf⟩
          let ShiftInv : Tup Val [i64, i64] → Mem 64 → Prop := fun (pc, qc, ()) m2 =>
            p.toNat ≤ pc.toNat ∧ pc.toNat ≤ end0 ∧ qc.toNat = pc.toNat - 2 ∧
            ∃ wstk1 : List (BitVec 32), wstk1.length = c.wcap ∧
              (∀ i, i < p.toNat - 2 ∨ pc.toNat - 2 ≤ i → wstk1[i]? = s.core.wstk[i]?) ∧
              (∀ j, j < pc.toNat - p.toNat →
                wstk1[(p.toNat - 2) + j]? = s.core.wstk[p.toNat + j]?) ∧
              (FullMem c { s with core := { s.core with wstk := wstk1 } } ⋆ R) m2
          c0_hsteps_nogrp
          refine wp_join_group (ts := [i64, i64]) ShiftInv ?_ (fun Jp hJp => by
            c0_hsplit
            · c0_hsplit
              · have hp_lt : p.toNat < end0 := by
                  have hc' : p.toNat < (BitVec.setWidth 64
                      (s.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'hbd0_w) +
                    BitVec.setWidth 64
                      (s.core.wvec[((lit.setWidth 64 <<< (1 : Nat)) +
                        (1 : BitVec 64)).toNat]'hbd1_w)).toNat := by c0_bound
                  rwa [hend64] at hc'
                have hp1_n : (p + 1#64).toNat = p.toNat + 1 := by
                  rw [BitVec.toNat_add, show (1#64).toNat = 1 from rfl,
                    Nat.mod_eq_of_lt (by omega)]
                have hq1_n : ((p - 2#64) + 1#64).toNat = p.toNat - 2 + 1 := by
                  rw [BitVec.toNat_add, hp2_toNat, show (1#64).toNat = 1 from rfl,
                    Nat.mod_eq_of_lt (by omega)]
                have hpc_w : p.toNat < s.core.wstk.length := by omega
                have hqc_w : (p - 2#64).toNat < s.core.wstk.length := by
                  rw [hp2_toNat]; omega
                c0_hsteps_nogrp
                have hs1 := shift_step1 (p0 := p.toNat) (pc := p.toNat) hws_len
                  (by omega) (Nat.le_refl _) (by omega)
                  (fun _ _ => rfl) (fun _ hj => by omega)
                rw [show (2 : BitVec 64) = 2#64 from rfl, hp2_toNat] at hm
                exact hJp (p + 1#64, (p - 2#64) + 1#64, ()) m
                  ⟨by rw [hp1_n]; omega, by rw [hp1_n]; omega,
                   by rw [hp1_n, hq1_n]; omega, _, hs1.1,
                   by simpa only [hp1_n] using hs1.2.1,
                   by simpa only [hp1_n] using hs1.2.2, hm⟩
              · c0_hsteps
                exact hJp (p, p - 2#64, ()) m1
                  ⟨Nat.le_refl _, hpe, hp2_toNat, s.core.wstk, hws_len,
                   fun _ _ => rfl, fun _ hj => by omega, hm⟩
            · c0_hsteps
              exact hJp (p, p - 2#64, ()) m1
                ⟨Nat.le_refl _, hpe, hp2_toNat, s.core.wstk, hws_len,
                 fun _ _ => rfl, fun _ hj => by omega, hm⟩)
          rintro _ ⟨p0, q0, ⟨⟩⟩ m0 ⟨hp0_lo, hp0_hi, hq0_eq, wstk0, hlen0, hout0, hsh0, hm0⟩
          refine wp_loop_inv (ts := [i64, i64]) ShiftInv (fun (pc, _, ()) _ => end0 - pc.toNat)
            (fun J4 hLoop4 => by
              c0_hsteps
              exact hLoop4 (p0, q0, ()) m0
                ⟨hp0_lo, hp0_hi, hq0_eq, wstk0, hlen0, hout0, hsh0, hm0⟩)
            ?_
          rintro J4 ⟨pc, qc, ⟨⟩⟩ m2 ⟨hpc_lo, hpc_hi, hqc_eq, wstk1, hlen1, hout1, hsh1, hm2⟩
            hLoop4
          let sL : FullState := { s with core := { s.core with wstk := wstk1 } }
          c0_hsplit
          · -- 4-literal (`2 x u64`) unrolled copy step: `pc + 4 <= end0`
            have hpc4_nat : (pc + 4#64).toNat = pc.toNat + 4 := by bv_omega
            have hpc4_le : pc.toNat + 4 ≤ end0 := by
              have hc' : (pc + 4#64).toNat ≤ (BitVec.setWidth 64
                  (s.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'hbd0_w) +
                BitVec.setWidth 64
                  (s.core.wvec[((lit.setWidth 64 <<< (1 : Nat)) +
                    (1 : BitVec 64)).toNat]'hbd1_w)).toNat := by c0_bound
              rw [hpc4_nat, hend64] at hc'; exact hc'
            have hqc4_nat : (qc + 4#64).toNat = qc.toNat + 4 := by bv_omega
            have hld0 := loadVal_fullMem_wstk_i64 (s := sL) (idx := pc) (by dsimp [sL]; omega) hm2
            have hld1 := loadVal_fullMem_wstk_i64_off8 (s := sL) (idx := pc)
              (by dsimp [sL]; omega) hm2
            let v0 := packU32Pair (wstk1[pc.toNat]'(by omega)) (wstk1[pc.toNat + 1]'(by omega))
            let v1 := packU32Pair (wstk1[pc.toNat + 2]'(by omega)) (wstk1[pc.toNat + 3]'(by omega))
            obtain ⟨hok0, hst0⟩ := store_fullMem_wstk_i64 (s := sL) (idx := qc) v0
              (by dsimp [sL]; omega) hm2
            have hws0_eq :
                (wstk1.set qc.toNat (v0.setWidth 32)).set (qc.toNat + 1) ((v0 >>> 32).setWidth 32) =
                (wstk1.set (pc.toNat - 2) (wstk1[pc.toNat]'(by omega))).set (pc.toNat - 1)
                  (wstk1[pc.toNat + 1]'(by omega)) := by
              rw [packU32Pair_lo, packU32Pair_hi, hqc_eq,
                show pc.toNat - 2 + 1 = pc.toNat - 1 by omega]
            let sL1 : FullState := { s with core := { s.core with
              wstk := (wstk1.set qc.toNat (v0.setWidth 32)).set (qc.toNat + 1)
                ((v0 >>> 32).setWidth 32) } }
            have h0_add : ∀ x : BitVec 64,
                x + BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0) * 8 = x := fun x => by
              rw [show BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0) * 8 = 0#64 from rfl,
                BitVec.add_zero]
            have h1_add : ∀ x : BitVec 64,
                x + BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 1) * 8 = x + 8 := fun x => rfl
            c0_hsteps_nogrp
            refine wp_load_of (by dsimp only [Arg.val]; rw [h0_add]; exact hld0) ?_
            c0_hsteps_nogrp
            refine wp_load_of (by dsimp only [Arg.val]; rw [h1_add]; exact hld1) ?_
            c0_hsteps_nogrp
            refine wp_store_sep (by dsimp only [Arg.val]; rw [h0_add]; exact ⟨hok0, hst0⟩)
              fun m2a hm2a => ?_
            obtain ⟨hok1, hst1⟩ := store_fullMem_wstk_i64_off8 (s := sL1) (idx := qc) v1
              (by dsimp [sL1]; simp [hlen1]; omega) hm2a
            c0_hsteps_nogrp
            refine wp_store_sep (by dsimp only [Arg.val]; rw [h1_add]; exact ⟨hok1, hst1⟩)
              fun m2b hm2b => ?_
            c0_hsteps
            have hs4 := shift_step4 hlen1 (by omega) hpc_lo (by omega) hout1 hsh1
            have hws4_eq :
                ((sL1.core.wstk.set (qc.toNat + 2) (v1.setWidth 32)).set (qc.toNat + 3)
                  ((v1 >>> 32).setWidth 32)) =
                (((wstk1.set (pc.toNat - 2) (wstk1[pc.toNat]'(by omega))).set (pc.toNat - 1)
                    (wstk1[pc.toNat + 1]'(by omega))).set pc.toNat
                  (wstk1[pc.toNat + 2]'(by omega))).set (pc.toNat + 1)
                  (wstk1[pc.toNat + 3]'(by omega)) := by
              dsimp only [sL1]; rw [hws0_eq, packU32Pair_lo, packU32Pair_hi, hqc_eq,
                show pc.toNat - 2 + 2 = pc.toNat by omega,
                show pc.toNat - 2 + 3 = pc.toNat + 1 by omega]
            rw [hws4_eq] at hm2b
            exact hLoop4 (pc + 4#64, qc + 4#64, ()) m2b (by dsimp only; rw [hpc4_nat]; omega)
              ⟨by rw [hpc4_nat]; omega, by rw [hpc4_nat]; omega,
               by rw [hpc4_nat, hqc4_nat]; omega, _, hs4.1,
               by simpa only [hpc4_nat] using hs4.2.1,
               by simpa only [hpc4_nat] using hs4.2.2, hm2b⟩
          · -- After 4-lit loop: `end0 < pc + 4`
            have hpc4_gt : end0 < pc.toNat + 4 := by
              have h4 : (pc + 4#64).toNat = pc.toNat + 4 := by
                rw [BitVec.toNat_add, show (4#64).toNat = 4 from rfl, Nat.mod_eq_of_lt (by omega)]
              have hc' : ¬ (pc + 4#64).toNat ≤ (BitVec.setWidth 64
                  (s.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'hbd0_w) +
                BitVec.setWidth 64
                  (s.core.wvec[((lit.setWidth 64 <<< (1 : Nat)) +
                    (1 : BitVec 64)).toNat]'hbd1_w)).toNat := by c0_bound
              rw [h4, hend64] at hc'; omega
            let ShiftInv2 : Tup Val [i64, i64] → Mem 64 → Prop := fun (pc2, qc2, ()) m3 =>
              ShiftInv (pc2, qc2, ()) m3 ∧ end0 < pc2.toNat + 2
            refine wp_join_group (ts := [i64, i64]) ShiftInv2 ?_ ?_
            · rintro _ ⟨pc2, qc2, ⟨⟩⟩ m3
                ⟨⟨hpc2_lo, hpc2_hi, hqc2_eq, wstk2, hlen2, hout2, hsh2, hm3⟩, hpc2_gt⟩
              let FinInv : Tup Val [] → Mem 64 → Prop := fun () m4 =>
                ∃ wstk3 : List (BitVec 32), wstk3.length = c.wcap ∧
                  (∀ i, i < p.toNat - 2 ∨ end0 - 2 ≤ i → wstk3[i]? = s.core.wstk[i]?) ∧
                  (∀ j, j < end0 - p.toNat →
                    wstk3[(p.toNat - 2) + j]? = s.core.wstk[p.toNat + j]?) ∧
                  (FullMem c { s with core := { s.core with wstk := wstk3 } } ⋆ R) m4
              refine wp_join_group (ts := []) FinInv ?_ ?_
              · rintro _ ⟨⟩ m4 ⟨wstk3, hlen3, hout3, hsh3, hm4⟩
                clear hm hm0 hm2 hm3
                c0_hsteps_nogrp
                have hend_w : (BitVec.setWidth 64
                      s.core.wvec[(BitVec.setWidth 64 lit <<< (1 : Nat)).toNat] +
                    BitVec.setWidth 64 s.core.wvec[2 * lit.toNat + 1]).toNat = end0 := by
                  simpa only [h2l1_eq] using hend64
                have he2_toNat : (BitVec.setWidth 64
                      s.core.wvec[(BitVec.setWidth 64 lit <<< (1 : Nat)).toNat] +
                    BitVec.setWidth 64 s.core.wvec[2 * lit.toNat + 1] - 2#64).toNat =
                    end0 - 2 := by
                  rw [BitVec.toNat_sub_of_le (by
                    rw [BitVec.le_def, hend_w, show (2#64).toNat = 2 from rfl]; omega),
                    hend_w, show (2#64).toNat = 2 from rfl]
                have he1_toNat : (BitVec.setWidth 64
                      s.core.wvec[(BitVec.setWidth 64 lit <<< (1 : Nat)).toNat] +
                    BitVec.setWidth 64 s.core.wvec[2 * lit.toNat + 1] - 1#64).toNat =
                    end0 - 1 := by
                  rw [BitVec.toNat_sub_of_le (by
                    rw [BitVec.le_def, hend_w, show (1#64).toNat = 1 from rfl]; omega),
                    hend_w, show (1#64).toNat = 1 from rfl]
                have hsz_sub2 : (BitVec.setWidth 64
                      (s.core.wvec[((lit.setWidth 64 <<< (1 : Nat)) +
                        (1 : BitVec 64)).toNat]'hbd1_w) - 2#64).setWidth 32 =
                    BitVec.ofNat 32 (sz0 - 2) := by
                  apply BitVec.eq_of_toNat_eq
                  rw [BitVec.toNat_setWidth, BitVec.toNat_sub_of_le (by
                    rw [BitVec.le_def, hsz64, show (2#64).toNat = 2 from rfl]; omega),
                    hsz64, show (2#64).toNat = 2 from rfl, BitVec.toNat_ofNat,
                    Nat.mod_eq_of_lt (by omega)]
                let wvec' := s.core.wvec.set (2 * lit.toNat + 1) (BitVec.ofNat 32 (sz0 - 2))
                let wstk_fin :=
                  (wstk3.set (end0 - 2) 0xFFFFFFFF#32).set (end0 - 1) 0xFFFFFFFF#32
                let wu' := s.core.wusable + 2#64
                obtain ⟨hlay', hmw_pres⟩ := fid_unwatch_fin_inv rfl hlen.core_ok hlay hlit_lt hsz2
                  hp_ge2 hpe hout3 hsh3 hinv_found
                have hsz_sub2' :
                    (BitVec.setWidth 64 (s.core.wvec[2 * lit.toNat + 1]'(by omega)) -
                      2#64).setWidth 32 = BitVec.ofNat 32 (sz0 - 2) := by
                  simpa only [h2l1_eq] using hsz_sub2
                have hm' : (FullMem c { s with core := { s.core with
                    wusable := wu', wvec := wvec', wstk := wstk_fin } } ⋆ R) m := by
                  have h1 : (1#64 : BitVec 64) = 1 := rfl
                  have h2 : (2#64 : BitVec 64) = 2 := rfl
                  have hff : (4294967295 : BitVec 32) = 0xFFFFFFFF#32 := rfl
                  have hsz_r := hsz_sub2'; rw [h2] at hsz_r
                  have he2_r := he2_toNat; rw [h2] at he2_r
                  have he1_r := he1_toNat; rw [h1] at he1_r
                  simpa only [wvec', wstk_fin, wu', h1, h2, hff, h2l1_eq,
                    hsz_r, he2_r, he1_r] using hm
                exact hQ wvec' wstk_fin wu' _
                  ⟨{ hlen.core_ok with wvec_len := by simp [wvec', hwv_len],
                                       wstk_len_arr := by simp [wstk_fin, hlen3] },
                   hlen.scratch_ok⟩ hlay' hmw_pres hm'
              · -- Optional 1-literal `u32` tail: `if (p < end)`
                intro J1t hJ1t
                c0_hsplit
                · have hpc2_lt : pc2.toNat < end0 := by
                    have hc' : pc2.toNat < (BitVec.setWidth 64
                        (s.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'hbd0_w) +
                      BitVec.setWidth 64
                        (s.core.wvec[((lit.setWidth 64 <<< (1 : Nat)) +
                          (1 : BitVec 64)).toNat]'hbd1_w)).toNat := by c0_bound
                    rwa [hend64] at hc'
                  have hend_eq : pc2.toNat + 1 = end0 := by omega
                  have hpc2_w : pc2.toNat < wstk2.length := by omega
                  have hqc2_w : qc2.toNat < wstk2.length := by omega
                  c0_hsteps
                  have hs1 := shift_step1 hlen2 (by omega) hpc2_lo (by omega) hout2 hsh2
                  have hset_eq : wstk2.set qc2.toNat (wstk2[pc2.toNat]'hpc2_w) =
                      wstk2.set (pc2.toNat - 2) (wstk2[pc2.toNat]'(by omega)) := by
                    simp only [hqc2_eq]
                  rw [hset_eq] at hm
                  exact hJ1t () _ ⟨_, hs1.1, by simpa only [hend_eq] using hs1.2.1,
                    by simpa only [hend_eq] using hs1.2.2, hm⟩
                · have hpc2_eq : pc2.toNat = end0 := by
                    have hc' : ¬ pc2.toNat < (BitVec.setWidth 64
                        (s.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'hbd0_w) +
                      BitVec.setWidth 64
                        (s.core.wvec[((lit.setWidth 64 <<< (1 : Nat)) +
                          (1 : BitVec 64)).toNat]'hbd1_w)).toNat := by c0_bound
                    rw [hend64] at hc'; omega
                  c0_hsteps
                  exact hJ1t () m3 ⟨wstk2, hlen2, by simpa only [hpc2_eq] using hout2,
                    by simpa only [hpc2_eq] using hsh2, hm3⟩
            · -- Optional 2-literal `u64` step: `if (p + 2 <= end)`
              intro J2t hJ2t
              c0_hsplit
              · have hpc2_nat : (pc + 2#64).toNat = pc.toNat + 2 := by
                  rw [BitVec.toNat_add, show (2#64).toNat = 2 from rfl, Nat.mod_eq_of_lt (by omega)]
                have hqc2_nat : (qc + 2#64).toNat = qc.toNat + 2 := by
                  rw [BitVec.toNat_add, show (2#64).toNat = 2 from rfl, Nat.mod_eq_of_lt (by omega)]
                have hpc2_le : pc.toNat + 2 ≤ end0 := by
                  have hc' : (pc + 2#64).toNat ≤ (BitVec.setWidth 64
                      (s.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'hbd0_w) +
                    BitVec.setWidth 64
                      (s.core.wvec[((lit.setWidth 64 <<< (1 : Nat)) +
                        (1 : BitVec 64)).toNat]'hbd1_w)).toNat := by c0_bound
                  rw [hpc2_nat, hend64] at hc'; exact hc'
                have hld2 := loadVal_fullMem_wstk_i64 (s := sL) (idx := pc)
                  (by dsimp [sL]; omega) hm2
                let v2 := packU32Pair (wstk1[pc.toNat]'(by omega)) (wstk1[pc.toNat + 1]'(by omega))
                obtain ⟨hok2, hst2⟩ := store_fullMem_wstk_i64 (s := sL) (idx := qc) v2
                  (by dsimp [sL]; omega) hm2
                have hws2_eq :
                    (wstk1.set qc.toNat (v2.setWidth 32)).set (qc.toNat + 1)
                      ((v2 >>> 32).setWidth 32) =
                    (wstk1.set (pc.toNat - 2) (wstk1[pc.toNat]'(by omega))).set (pc.toNat - 1)
                      (wstk1[pc.toNat + 1]'(by omega)) := by
                  rw [packU32Pair_lo, packU32Pair_hi, hqc_eq,
                    show pc.toNat - 2 + 1 = pc.toNat - 1 by omega]
                rw [hws2_eq] at hst2
                have h0_add : ∀ x : BitVec 64,
                    x + BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0) * 8 = x := fun x => by
                  rw [show BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0) * 8 = 0#64 from rfl,
                    BitVec.add_zero]
                c0_hsteps_nogrp
                refine wp_load_of (by dsimp only [Arg.val]; rw [h0_add]; exact hld2) ?_
                try c0_hsteps_nogrp
                refine wp_store_sep (by dsimp only [Arg.val]; rw [h0_add]; exact ⟨hok2, hst2⟩)
                  fun m2c hm2c => ?_
                c0_hsteps
                have hs2 := shift_step2 hlen1 (by omega) hpc_lo (by omega) hout1 hsh1
                exact hJ2t (pc + 2#64, qc + 2#64, ()) m2c
                  ⟨⟨by rw [hpc2_nat]; omega, by rw [hpc2_nat]; omega,
                    by rw [hpc2_nat, hqc2_nat]; omega, _, hs2.1,
                    by simpa only [hpc2_nat] using hs2.2.1,
                    by simpa only [hpc2_nat] using hs2.2.2, hm2c⟩,
                   by rw [hpc2_nat]; omega⟩
              · have hpc2_gt : end0 < pc.toNat + 2 := by
                  have h2 : (pc + 2#64).toNat = pc.toNat + 2 := by
                    rw [BitVec.toNat_add, show (2#64).toNat = 2 from rfl,
                      Nat.mod_eq_of_lt (by omega)]
                  have hc' : ¬ (pc + 2#64).toNat ≤ (BitVec.setWidth 64
                      (s.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'hbd0_w) +
                    BitVec.setWidth 64
                      (s.core.wvec[((lit.setWidth 64 <<< (1 : Nat)) +
                        (1 : BitVec 64)).toNat]'hbd1_w)).toNat := by c0_bound
                  rw [h2, hend64] at hc'; omega
                c0_hsteps
                exact hJ2t (pc, qc, ()) m2
                  ⟨⟨hpc_lo, hpc_hi, hqc_eq, wstk1, hlen1, hout1, hsh1, hm2⟩, hpc2_gt⟩
        · c0_hsteps
          obtain ⟨hdec, hlo', hle', hinv'⟩ :=
            fid_unwatch_step_ok hp_ge2 hpe (by omega) hw_some hinv
          exact hLoop1 (p - 2#64 + (w >>> (31 : Nat)).setWidth 64, ()) m1 hdec
            ⟨rfl, hlo', hle', hinv'⟩
      · c0_hsteps; exact hret_same

end UnwatchLargeFid

end LeanQbe.T.Examples.Kissat.FullFidelityVivK6
