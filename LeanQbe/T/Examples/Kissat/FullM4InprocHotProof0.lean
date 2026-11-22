module

public import LeanQbe.T.Examples.Kissat.FullM4InprocHot
public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Examples.Kissat.FullCongLemmas2
public import LeanQbe.T.Examples.Kissat.FullKittenLemmas1
public import LeanQbe.T.Examples.Kissat.FullIngestLemmas1

/-!
# Kissat `D-Full` M4 Track A6 Proof Helpers (`FullM4InprocHotProof0`)

Provides `i64` <-> `i32 × i32` memory pair bridges and pure sorting / heap / compaction /
memory-focus helpers for `LeanQbe.T.Examples.Kissat.FullM4InprocHotProof`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM4InprocHot

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

/-! ## 1. `i64` <-> `i32 × i32` Memory Pair Bridges -/

private theorem toBytes4_of_nat {n : Nat} (hn : n < 2 ^ 32) :
    Int.toBytes 4 ((toBits i32 (BitVec.ofNat 32 n)).setWidth 32).toInt =
      Int.toBytes 4 (n : Int) := by
  have h1 : ((toBits i32 (BitVec.ofNat 32 n)).setWidth 32) = BitVec.ofNat 32 n := rfl
  rw [h1]
  have hmod : ((BitVec.ofNat 32 n).toInt) % (2 : Int) ^ (8 * 4) = (n : Int) := by
    rw [BitVec.toInt_eq_msb_cond]
    have htn : (BitVec.ofNat 32 n).toNat = n := by simp [Nat.mod_eq_of_lt hn]
    rw [htn]
    cases (BitVec.ofNat 32 n).msb <;>
      simp only [Bool.false_eq_true, ↓reduceIte, show (8 * 4 : Nat) = 32 by decide,
        show (2 : Int) ^ 32 = ((2 ^ 32 : Nat) : Int) by decide, Int.sub_emod_right] <;>
      omega
  rw [← Int.toBytes_emod 4, Int.take, show (8 * 4 : Nat) = 32 by decide, hmod]

private theorem int_toBytes_8_split (lo hi : Nat) (hlo : lo < 2 ^ 32) (_hhi : hi < 2 ^ 32) :
    Int.toBytes 8 ((lo + 2 ^ 32 * hi : Nat) : Int) =
      Int.toBytes 4 (lo : Int) ++ Int.toBytes 4 (hi : Int) := by
  have step : ∀ (x : Int), Int.toBytes 4 x =
      [ ((x.take 8).toNat.toUInt8),
        (((x / 256).take 8).toNat.toUInt8),
        (((x / 256 / 256).take 8).toNat.toUInt8),
        (((x / 256 / 256 / 256).take 8).toNat.toUInt8) ] := fun _ => rfl
  have step8 : ∀ (x : Int), Int.toBytes 8 x =
      [ ((x.take 8).toNat.toUInt8),
        (((x / 256).take 8).toNat.toUInt8),
        (((x / 256 / 256).take 8).toNat.toUInt8),
        (((x / 256 / 256 / 256).take 8).toNat.toUInt8),
        (((x / 256 / 256 / 256 / 256).take 8).toNat.toUInt8),
        (((x / 256 / 256 / 256 / 256 / 256).take 8).toNat.toUInt8),
        (((x / 256 / 256 / 256 / 256 / 256 / 256).take 8).toNat.toUInt8),
        (((x / 256 / 256 / 256 / 256 / 256 / 256 / 256).take 8).toNat.toUInt8) ] :=
    fun _ => rfl
  rw [step8, step, step]
  simp only [List.cons_append, List.nil_append, Int.take]
  have hL : (lo : Int) + 2 ^ 32 * (hi : Int) = ((lo + 2 ^ 32 * hi : Nat) : Int) := by
    simp only [Int.natCast_add, Int.natCast_mul]; rfl
  rw [← hL]
  have hd0 : ((lo : Int) + 2 ^ 32 * hi) % 2 ^ 8 = (lo : Int) % 2 ^ 8 := by omega
  have hd1 : (((lo : Int) + 2 ^ 32 * hi) / 256) % 2 ^ 8 = ((lo : Int) / 256) % 2 ^ 8 := by omega
  have hd2 : (((lo : Int) + 2 ^ 32 * hi) / 256 / 256) % 2 ^ 8 =
      ((lo : Int) / 256 / 256) % 2 ^ 8 := by omega
  have hd3 : (((lo : Int) + 2 ^ 32 * hi) / 256 / 256 / 256) % 2 ^ 8 =
      ((lo : Int) / 256 / 256 / 256) % 2 ^ 8 := by omega
  have hd4 : ((lo : Int) + 2 ^ 32 * hi) / 256 / 256 / 256 / 256 = (hi : Int) := by omega
  rw [hd0, hd1, hd2, hd3, hd4]

private theorem bv64_split_lo_hi (v : BitVec 64) :
    v.toNat = (v.setWidth 32).toNat + 2 ^ 32 * ((v >>> 32).setWidth 32).toNat := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hv := v.isLt
  have hd : v.toNat / 2 ^ 32 < 2 ^ 32 := by omega
  rw [Nat.mod_eq_of_lt hd, Nat.add_comm, Nat.mul_comm (2 ^ 32)]
  exact (Nat.div_add_mod' v.toNat (2 ^ 32)).symm

theorem bv64_join_lo_hi (lo hi : BitVec 32) :
    (lo.setWidth 64 ||| (hi.setWidth 64 <<< 32)).toNat = lo.toNat + 2 ^ 32 * hi.toNat := by
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_trans lo.isLt (by decide)),
    Nat.mod_eq_of_lt (Nat.lt_trans hi.isLt (by decide)), Nat.shiftLeft_eq]
  have hmul : hi.toNat * 2 ^ 32 < 2 ^ 64 := by have := hi.isLt; omega
  rw [Nat.mod_eq_of_lt hmul, ← Nat.shiftLeft_eq]
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.add_comm lo.toNat, Nat.testBit_or, Nat.testBit_shiftLeft,
    Nat.testBit_two_pow_mul_add _ lo.isLt]
  by_cases hj : j < 32
  · simp [hj, show ¬(32 ≤ j) by omega]
  · have hlt_lo : lo.toNat.testBit j = false :=
      Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le lo.isLt (Nat.pow_le_pow_right (by omega) (by omega)))
    simp [hj, show 32 ≤ j by omega, hlt_lo]

theorem bv64_pair_lo (lo hi : BitVec 32) :
    (lo.setWidth 64 ||| (hi.setWidth 64 <<< 32)).setWidth 32 = lo := by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_setWidth, bv64_join_lo_hi]
  have := lo.isLt; omega

theorem bv64_pair_hi (lo hi : BitVec 32) :
    ((lo.setWidth 64 ||| (hi.setWidth 64 <<< 32)) >>> 32).setWidth 32 = hi := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, bv64_join_lo_hi]
  have := lo.isLt; have := hi.isLt; omega

theorem cell32_pair_eq_cell64 (a : BitVec 64) (v : BitVec 64) :
    (cell (t := i32) a (v.setWidth 32) ⋆ cell (t := i32) (a + 4#64) ((v >>> 32).setWidth 32)) =
      cell64 a v := by
  let lo := v.setWidth 32
  let hi := (v >>> 32).setWidth 32
  have hlo_lt : lo.toNat < 2 ^ 32 := lo.isLt
  have hhi_lt : hi.toNat < 2 ^ 32 := hi.isLt
  have hlo_eq : BitVec.ofNat 32 lo.toNat = lo := BitVec.eq_of_toNat_eq (by simp)
  have hhi_eq : BitVec.ofNat 32 hi.toNat = hi := BitVec.eq_of_toNat_eq (by simp)
  have hb4_lo := hlo_eq ▸ toBytes4_of_nat hlo_lt
  have hb4_hi := hhi_eq ▸ toBytes4_of_nat hhi_lt
  have hv_toBytes : Int.toBytes 8 v.toInt =
      Int.toBytes 4 (lo.toNat : Int) ++ Int.toBytes 4 (hi.toNat : Int) := by
    have hv_mod : v.toInt % (2 : Int) ^ (8 * 8) = (v.toNat : Int) := by
      rw [BitVec.toInt_eq_msb_cond]
      cases v.msb <;>
        simp only [Bool.false_eq_true, ↓reduceIte, show (8 * 8 : Nat) = 64 by decide,
          show (2 : Int) ^ 64 = ((2 ^ 64 : Nat) : Int) by decide, Int.sub_emod_right] <;>
        (have := v.isLt; omega)
    rw [← Int.toBytes_emod 8, Int.take, show (8 * 8 : Nat) = 64 by decide, hv_mod]
    rw [bv64_split_lo_hi v]
    exact int_toBytes_8_split lo.toNat hi.toNat hlo_lt hhi_lt
  unfold cell cell64
  rw [show (i32 : Ty).bytes = 4 from rfl, hb4_lo, hb4_hi, hv_toBytes]
  have hlen : (Int.toBytes 4 (lo.toNat : Int)).length +
      (Int.toBytes 4 (hi.toNat : Int)).length ≤ 2 ^ 64 := by
    rw [Int.toBytes_length, Int.toBytes_length]; decide
  have hsep := Mem.At_append_sep (Int.toBytes 4 (lo.toNat : Int))
    (Int.toBytes 4 (hi.toNat : Int)) a hlen
  rw [Int.toBytes_length] at hsep
  exact hsep.symm

theorem array32_focus_pair {a : BitVec 64} {xs : List (BitVec 32)} {i : Nat}
    (hi : 2 * i + 1 < xs.length) :
    array (t := i32) a xs =
      (cell64 (a + BitVec.ofNat 64 (8 * i))
        (xs[2 * i].setWidth 64 ||| (xs[2 * i + 1].setWidth 64 <<< 32)) ⋆
        (array (t := i32) a (xs.take (2 * i)) ⋆
          array (t := i32) (a + BitVec.ofNat 64 (8 * i) + 8#64) (xs.drop (2 * i + 2)))) := by
  have hv_lo := bv64_pair_lo xs[2 * i] xs[2 * i + 1]
  have hv_hi := bv64_pair_hi xs[2 * i] xs[2 * i + 1]
  let v := xs[2 * i].setWidth 64 ||| (xs[2 * i + 1].setWidth 64 <<< 32)
  have hcell := cell32_pair_eq_cell64 (a + BitVec.ofNat 64 (8 * i)) v
  rw [hv_lo, hv_hi] at hcell
  rw [← hcell]
  have hdrop : xs.drop (2 * i) = xs[2 * i] :: xs[2 * i + 1] :: xs.drop (2 * i + 2) := by
    rw [List.drop_eq_getElem_cons (by omega),
      List.drop_eq_getElem_cons (i := 2 * i + 1) (by omega)]
  conv => lhs; rw [← List.take_append_drop (2 * i) xs, hdrop, array_append, array_cons,
    array_cons, show (i32 : Ty).bytes = 4 from rfl,
    List.length_take_of_le (by omega),
    show (4 * (2 * i) : Nat) = 8 * i by omega,
    BitVec.add_assoc (a + BitVec.ofNat 64 (8 * i)) 4#64 4#64,
    show (4#64 : BitVec 64) + 4#64 = 8#64 from rfl]
  ac_rfl

theorem load_array32_as_i64 {a : BitVec 64} {xs : List (BitVec 32)} {i : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : 2 * i + 1 < xs.length)
    (hm : (array (t := i32) a xs ⋆ R) m) :
    loadVal m i64 (a + BitVec.ofNat 64 (8 * i)) =
      some (xs[2 * i].setWidth 64 ||| (xs[2 * i + 1].setWidth 64 <<< 32)) := by
  rw [array32_focus_pair hi, sep_assoc] at hm
  exact loadVal_cell64 hm

theorem store_array32_as_i64 {a : BitVec 64} {xs : List (BitVec 32)} {i : Nat} (v : BitVec 64)
    {R : Mem 64 → Prop} {m : Mem 64} (hi : 2 * i + 1 < xs.length)
    (hm : (array (t := i32) a xs ⋆ R) m) :
    storeOk m i64 (a + BitVec.ofNat 64 (8 * i)) ∧
      (array (t := i32) a
        ((xs.set (2 * i) (v.setWidth 32)).set (2 * i + 1) ((v >>> 32).setWidth 32)) ⋆ R)
        (storeMem m i64 (a + BitVec.ofNat 64 (8 * i)) v) := by
  rw [array32_focus_pair hi, sep_assoc] at hm
  obtain ⟨hok, hst⟩ := store_cell64 v hm
  refine ⟨hok, ?_⟩
  let xs' := (xs.set (2 * i) (v.setWidth 32)).set (2 * i + 1) ((v >>> 32).setWidth 32)
  have hlen' : 2 * i + 1 < xs'.length := by simp [xs', hi]
  have htake : xs'.take (2 * i) = xs.take (2 * i) := by
    simp [xs', List.take_set_of_le (by omega : 2 * i ≤ 2 * i),
      List.take_set_of_le (by omega : 2 * i ≤ 2 * i + 1)]
  have hdrop : xs'.drop (2 * i + 2) = xs.drop (2 * i + 2) := by
    simp [xs', List.drop_set_of_lt (by omega : 2 * i < 2 * i + 2),
      List.drop_set_of_lt (by omega : 2 * i + 1 < 2 * i + 2)]
  have hget0 : xs'[2 * i] = v.setWidth 32 := by
    simp only [xs']
    rw [List.getElem_set_ne (by omega) (hj := by simp; omega),
      List.getElem_set_self (by simp; omega)]
  have hget1 : xs'[2 * i + 1] = (v >>> 32).setWidth 32 := by
    simp only [xs']
    rw [List.getElem_set_self (by simp; omega)]
  rw [← cell32_pair_eq_cell64 (a + BitVec.ofNat 64 (8 * i)) v] at hst
  have hdrop' : xs'.drop (2 * i) = xs'[2 * i] :: xs'[2 * i + 1] :: xs'.drop (2 * i + 2) := by
    rw [List.drop_eq_getElem_cons (by omega),
      List.drop_eq_getElem_cons (i := 2 * i + 1) (by omega)]
  have heq_arr : array (t := i32) a xs' =
      ((cell (t := i32) (a + BitVec.ofNat 64 (8 * i)) (v.setWidth 32) ⋆
        cell (t := i32) (a + BitVec.ofNat 64 (8 * i) + 4#64) ((v >>> 32).setWidth 32)) ⋆
        (array (t := i32) a (xs.take (2 * i)) ⋆
          array (t := i32) (a + BitVec.ofNat 64 (8 * i) + 8#64) (xs.drop (2 * i + 2)))) := by
    conv => lhs; rw [← List.take_append_drop (2 * i) xs', hdrop', array_append, array_cons,
      array_cons, show (i32 : Ty).bytes = 4 from rfl, htake, hdrop, hget0, hget1,
      List.length_take_of_le (by omega),
      show (4 * (2 * i) : Nat) = 8 * i by omega,
      BitVec.add_assoc (a + BitVec.ofNat 64 (8 * i)) 4#64 4#64,
      show (4#64 : BitVec 64) + 4#64 = 8#64 from rfl]
    ac_rfl
  rw [heq_arr, sep_assoc]
  exact hst

/-! ## 2. Defrag Pure Sort, Heap, Compaction, and `DefragMem` Helpers -/

def m4WsVal (ws : List (BitVec 32)) (i : Nat) : Nat :=
  (ws[i]?.getD 0#32).toNat

def m4WvecOff (wvec : List (BitVec 32)) (l : Nat) : Nat :=
  (wvec[2 * l]?.getD 0#32).toNat

def M4WsCovers (ws : List (BitVec 32)) (n nlits : Nat) (sz : Nat → Nat) : Prop :=
  (∀ i < n, m4WsVal ws i < nlits ∧ 0 < sz (m4WsVal ws i)) ∧
  (∀ i < n, ∀ j < n, i ≠ j → m4WsVal ws i ≠ m4WsVal ws j) ∧
  (∀ l < nlits, 0 < sz l → ∃ i < n, m4WsVal ws i = l)

def M4Sorted (key : Nat → Nat) (ws : List (BitVec 32)) (lo hi : Nat) : Prop :=
  ∀ i j, lo ≤ i → i ≤ j → j < hi → key (m4WsVal ws i) ≤ key (m4WsVal ws j)

def M4SplitLe (key : Nat → Nat) (ws : List (BitVec 32)) (mid hi : Nat) : Prop :=
  ∀ i < mid, ∀ j, mid ≤ j → j < hi → key (m4WsVal ws i) ≤ key (m4WsVal ws j)

private def m4SwapIdx (i j k : Nat) : Nat :=
  if k = i then j else if k = j then i else k

private theorem m4SwapIdx_invol (i j k : Nat) : m4SwapIdx i j (m4SwapIdx i j k) = k := by
  unfold m4SwapIdx; grind

private theorem m4WsVal_swap {ws : List (BitVec 32)} {i j : Nat}
    (hi : i < ws.length) (hj : j < ws.length) (k : Nat) :
    m4WsVal ((ws.set i (ws[j]'hj)).set j (ws[i]'hi)) k = m4WsVal ws (m4SwapIdx i j k) := by
  unfold m4WsVal m4SwapIdx
  by_cases hkj : k = j
  · subst hkj; rw [List.getElem?_set_self (by simp; omega)]
    by_cases hki : k = i <;> simp [hki, List.getElem?_eq_getElem hi]
  · rw [List.getElem?_set_ne (by omega)]
    by_cases hki : k = i
    · subst hki; rw [List.getElem?_set_self (by omega)]; simp [List.getElem?_eq_getElem hj]
    · rw [List.getElem?_set_ne (by omega)]; simp [hki, hkj]

private theorem m4Count_set {α : Type} [DecidableEq α] (l : List α) (i : Nat) (v x : α)
    (hi : i < l.length) :
    (l.set i v).count x + (if l[i] = x then 1 else 0) =
      l.count x + (if v = x then 1 else 0) := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a as ih =>
    cases i with
    | zero => simp [List.count_cons]; omega
    | succ i' =>
      have hi' : i' < as.length := by simpa using hi
      have ih' := ih i' hi'
      simp only [List.set_cons_succ, List.count_cons, List.getElem_cons_succ] at ih' ⊢; omega

theorem m4WsSwap_perm {ws : List (BitVec 32)} {i j : Nat}
    (hi : i < ws.length) (hj : j < ws.length) :
    ((ws.set i (ws[j]'hj)).set j (ws[i]'hi)).Perm ws := by
  by_cases hij : i = j
  · subst hij; rw [List.set_getElem_self hi, List.set_getElem_self hi]
  · rw [List.perm_iff_count]; intro x
    have h1 := m4Count_set ws i (ws[j]'hj) x hi
    have h2 := m4Count_set (ws.set i (ws[j]'hj)) j (ws[i]'hi) x
      (by rw [List.length_set]; exact hj)
    rw [List.getElem_set_ne hij] at h2; omega

theorem m4WsCovers_swap {ws : List (BitVec 32)} {n nlits i j : Nat} {sz : Nat → Nat}
    (hc : M4WsCovers ws n nlits sz) (hi : i < n) (hj : j < n) (hn : n ≤ ws.length) :
    M4WsCovers ((ws.set i (ws[j]'(by omega))).set j (ws[i]'(by omega))) n nlits sz := by
  obtain ⟨hb, hnd, hcov⟩ := hc
  have hlt : ∀ k < n, m4SwapIdx i j k < n := fun k hk => by unfold m4SwapIdx; grind
  refine ⟨fun k hk => by rw [m4WsVal_swap (by omega) (by omega)]; exact hb _ (hlt k hk),
    fun a ha b hb' hab => by
      rw [m4WsVal_swap (by omega) (by omega), m4WsVal_swap (by omega) (by omega)]
      refine hnd _ (hlt a ha) _ (hlt b hb') fun heq => hab ?_
      simpa [m4SwapIdx_invol] using congrArg (m4SwapIdx i j) heq,
    fun l hl hsz => by
      obtain ⟨k, hk, hkl⟩ := hcov l hl hsz
      exact ⟨m4SwapIdx i j k, hlt k hk, by
        rw [m4WsVal_swap (by omega) (by omega), m4SwapIdx_invol]; exact hkl⟩⟩

theorem m4Perm_take_of_drop_eq {α : Type} {l1 l2 : List α} {n : Nat}
    (hlen : l1.length = l2.length) (hn : n ≤ l2.length)
    (hperm : l1.Perm l2) (hsuf : ∀ i, n ≤ i → l1[i]? = l2[i]?) :
    (l1.take n).Perm (l2.take n) := by
  have hdrop : l1.drop n = l2.drop n := by
    apply List.ext_getElem
    · simp [List.length_drop, hlen]
    · intro i hi _; simp only [List.length_drop] at hi
      rw [List.getElem_drop, List.getElem_drop]
      have heq := hsuf (n + i) (by omega)
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at heq
      exact Option.some.inj heq
  have hsplit : (l1.take n ++ l2.drop n).Perm (l2.take n ++ l2.drop n) := by
    rw [← hdrop, List.take_append_drop, hdrop, List.take_append_drop]; exact hperm
  exact (List.perm_append_right_iff (l2.drop n)).mp hsplit

theorem m4WsCovers_of_perm_take {ws ws' : List (BitVec 32)} {n nlits : Nat}
    {sz : Nat → Nat} (hcov : M4WsCovers ws n nlits sz)
    (hn : n ≤ ws.length) (hn' : n ≤ ws'.length) (htp : (ws'.take n).Perm (ws.take n)) :
    M4WsCovers ws' n nlits sz := by
  have hlen_tk' : (ws'.take n).length = n := by rw [List.length_take]; omega
  have hlen_tk : (ws.take n).length = n := by rw [List.length_take]; omega
  have hmem_tk : ∀ (l : List (BitVec 32)), (l.take n).length = n → ∀ x,
      (∃ i < n, l[i]? = some x) ↔ x ∈ l.take n := fun l hlk x => by
    constructor
    · rintro ⟨i, hi, heq⟩; have hilt : i < l.length := by rw [List.length_take] at hlk; omega
      rw [List.getElem?_eq_getElem hilt, Option.some.injEq] at heq; subst heq
      have hgm := List.getElem_mem (l := l.take n) (n := i) (by omega)
      rwa [List.getElem_take] at hgm
    · intro hx; obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
      have hilt : i < l.length := by rw [hlk] at hi; rw [List.length_take] at hlk; omega
      refine ⟨i, by omega, ?_⟩; rw [List.getElem?_eq_getElem hilt, List.getElem_take]
  have hmem_iff : ∀ x, (∃ i < n, ws'[i]? = some x) ↔ (∃ i < n, ws[i]? = some x) := fun x =>
    (hmem_tk ws' hlen_tk' x).trans (htp.mem_iff.trans (hmem_tk ws hlen_tk x).symm)
  have hnd : (ws.take n).Nodup := List.pairwise_iff_getElem.mpr fun i j hi hj hij => by
    rw [List.getElem_take, List.getElem_take]
    intro heq; apply hcov.2.1 i (by omega) j (by omega) (by omega)
    unfold m4WsVal; rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega),
      Option.getD_some, Option.getD_some, heq]
  have hnd' : (ws'.take n).Nodup := htp.nodup_iff.mpr hnd
  refine ⟨fun i hi => ?_, fun a ha b hb hab => ?_, fun l hl hsz => ?_⟩
  · obtain ⟨j, hj, hjeq⟩ :=
      (hmem_iff (ws'[i]'(by omega))).mp ⟨i, hi, List.getElem?_eq_getElem (by omega)⟩
    have hveq : m4WsVal ws' i = m4WsVal ws j := by
      unfold m4WsVal; rw [List.getElem?_eq_getElem (by omega), Option.getD_some,
        hjeq, Option.getD_some]
    rw [hveq]; exact hcov.1 j hj
  · have hlt : a < b ∨ b < a := Nat.lt_or_gt_of_ne hab
    intro hveq
    have heqv : (ws'.take n)[a]'(by omega) = (ws'.take n)[b]'(by omega) := by
      rw [List.getElem_take, List.getElem_take]; apply BitVec.eq_of_toNat_eq
      unfold m4WsVal at hveq
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega),
        Option.getD_some, Option.getD_some] at hveq
      exact hveq
    rcases hlt with h1 | h2
    · exact List.pairwise_iff_getElem.mp hnd' a b (by omega) (by omega) h1 heqv
    · exact List.pairwise_iff_getElem.mp hnd' b a (by omega) (by omega) h2 heqv.symm
  · obtain ⟨j, hj, hjl⟩ := hcov.2.2 l hl hsz
    obtain ⟨i, hi, hieq⟩ :=
      (hmem_iff (ws[j]'(by omega))).mpr ⟨j, hj, List.getElem?_eq_getElem (by omega)⟩
    refine ⟨i, hi, ?_⟩
    unfold m4WsVal at hjl ⊢; rw [hieq, Option.getD_some]
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hjl; exact hjl

theorem m4Slice_take_succ {α : Type} {xs : List α} {lo i : Nat}
    (hli : lo ≤ i) (hi : i < xs.length) :
    (xs.drop lo).take (i - lo + 1) = (xs.drop lo).take (i - lo) ++ [xs[i]'hi] := by
  have h1 : xs[i]'hi = (xs.drop lo)[i - lo]'(by simp [List.length_drop]; omega) := by
    rw [List.getElem_drop]; congr 1; omega
  rw [h1, List.take_succ_eq_append_getElem]

theorem m4Slice_drop_succ {α : Type} {xs : List α} {i hi : Nat}
    (hih : i < hi) (hl : hi ≤ xs.length) :
    (xs.drop i).take (hi - i) = xs[i]'(by omega) :: (xs.drop (i + 1)).take (hi - (i + 1)) := by
  rw [List.drop_eq_getElem_cons (by omega), show hi - i = (hi - (i + 1)) + 1 by omega,
    List.take_succ_cons]

theorem m4Slice_take_add {α : Type} (xs : List α) (off a b : Nat) :
    (xs.drop off).take (a + b) = (xs.drop off).take a ++ (xs.drop (off + a)).take b := by
  rw [List.take_add, List.drop_drop]

theorem m4Slice_congr {α : Type} {xs ys : List α} {off n : Nat}
    (hxs : off + n ≤ xs.length) (hys : off + n ≤ ys.length)
    (heq : ∀ i, off ≤ i → i < off + n → xs[i]? = ys[i]?) :
    (xs.drop off).take n = (ys.drop off).take n := by
  apply List.ext_getElem
  · simp [List.length_take, List.length_drop]; omega
  · intro i hi _; simp only [List.length_take, List.length_drop] at hi
    rw [List.getElem_take, List.getElem_drop, List.getElem_take, List.getElem_drop]
    have hg := heq (off + i) (by omega) (by omega)
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at hg
    exact Option.some.inj hg

theorem m4Take_set_virt_perm {ws : List (BitVec 32)} {xl pl : BitVec 32}
    {j n : Nat} (hj : 0 < j) (hjn : j < n) (hn : n ≤ ws.length)
    (hpl : ws[j - 1]? = some pl) :
    (((ws.set j pl).set (j - 1) xl).take n).Perm ((ws.set j xl).take n) := by
  have h1 : ((ws.set j xl).take n).length = n := by simp [List.length_take]; omega
  have hpl' : ws[j - 1]'(by omega) = pl := by
    rw [List.getElem?_eq_getElem (by omega), Option.some.injEq] at hpl; exact hpl
  have hne : j ≠ j - 1 := by omega
  have heq : (((ws.set j pl).set (j - 1) xl).take n) =
      ((((ws.set j xl).take n).set (j - 1) (((ws.set j xl).take n)[j]'(by omega))).set
        j (((ws.set j xl).take n)[j - 1]'(by omega))) := by
    apply List.ext_getElem
    · simp [List.length_take]
    · intro k hk _; simp only [List.length_take] at hk
      by_cases hkj : k = j
      · subst hkj; simp [List.getElem_take, hne, hne.symm, hpl']
      · by_cases hk1 : k = j - 1
        · subst hk1; simp [List.getElem_take, hne]
        · simp [List.getElem_take, List.getElem_set, Ne.symm hkj, Ne.symm hk1]
  rw [heq]
  exact m4WsSwap_perm (i := j - 1) (j := j) (by rw [h1]; omega) (by rw [h1]; omega)

theorem m4Insert_sorted_done {key : Nat → Nat} {wsI wsJ : List (BitVec 32)}
    {blk j ii : Nat} {xl : BitVec 32}
    (hbj : blk ≤ j) (_hji : j ≤ ii) (hil : ii < wsJ.length) (_hilI : ii < wsI.length)
    (hunch : ∀ p, p < j ∨ ii < p → wsJ[p]? = wsI[p]?)
    (hpre : M4Sorted key wsI blk ii)
    (hsuf : M4Sorted key wsJ (j + 1) (ii + 1))
    (hgt : ∀ p, j < p → p ≤ ii → key xl.toNat < key (m4WsVal wsJ p))
    (hle : j = blk ∨ key (m4WsVal wsJ (j - 1)) ≤ key xl.toNat) :
    M4Sorted key (wsJ.set j xl) blk (ii + 1) := by
  intro a b ha hab hb
  have hval : ∀ p, m4WsVal (wsJ.set j xl) p =
      if p = j then xl.toNat else m4WsVal wsJ p := fun p => by
    unfold m4WsVal; by_cases hp : p = j
    · subst hp; simp only [↓reduceIte]; rw [List.getElem?_set_self (by omega), Option.getD_some]
    · simp only [hp, ↓reduceIte]; rw [List.getElem?_set_ne (Ne.symm hp)]
  have hval_pre : ∀ p, p < j → m4WsVal wsJ p = m4WsVal wsI p := fun p hp => by
    unfold m4WsVal; rw [hunch p (Or.inl hp)]
  rw [hval a, hval b]
  by_cases haj : a = j <;> by_cases hbj' : b = j <;> simp only [haj, hbj', ↓reduceIte]
  · exact Nat.le_refl _
  · exact Nat.le_of_lt (hgt b (by omega) (by omega))
  · rcases hle with hjb | hle'
    · omega
    · rw [hval_pre (j - 1) (by omega)] at hle'
      rw [hval_pre a (by omega)]
      exact Nat.le_trans (hpre a (j - 1) ha (by omega) (by omega)) hle'
  · by_cases hbj_lt : b < j
    · rw [hval_pre a (by omega), hval_pre b hbj_lt]; exact hpre a b ha hab (by omega)
    · by_cases haj_lt : a < j
      · have hgtb : key xl.toNat < key (m4WsVal wsJ b) := hgt b (by omega) (by omega)
        rcases hle with hjb | hle'
        · omega
        · rw [hval_pre (j - 1) (by omega)] at hle'
          rw [hval_pre a haj_lt]
          exact Nat.le_trans (Nat.le_trans (hpre a (j - 1) ha (by omega) (by omega)) hle')
            (Nat.le_of_lt hgtb)
      · exact hsuf a b (by omega) hab hb

def M4MergeInv (key : Nat → Nat) (wsM : List (BitVec 32))
    (src dst lo mid hi : Nat) (wsD : List (BitVec 32)) (li ri ki : Nat) : Prop :=
  wsD.length = wsM.length ∧
  lo ≤ li ∧ li ≤ mid ∧ mid ≤ ri ∧ ri ≤ hi ∧ ki = li + (ri - mid) ∧
  (∀ p, p < dst + lo ∨ dst + hi ≤ p → wsD[p]? = wsM[p]?) ∧
  (∀ p, dst + lo ≤ p → p < dst + ki → m4WsVal wsD p < 2 ^ 31 ∧
    (∀ q, src + li ≤ q → q < src + mid → key (m4WsVal wsD p) ≤ key (m4WsVal wsM q)) ∧
    (∀ q, src + ri ≤ q → q < src + hi → key (m4WsVal wsD p) ≤ key (m4WsVal wsM q))) ∧
  M4Sorted key wsD (dst + lo) (dst + ki) ∧
  (((wsD.drop (dst + lo)).take (ki - lo)) ++
    ((wsM.drop (src + li)).take (mid - li)) ++
    ((wsM.drop (src + ri)).take (hi - ri))).Perm ((wsM.drop (src + lo)).take (hi - lo))

theorem m4MergeInv_step_l {key : Nat → Nat} {wsM wsD : List (BitVec 32)}
    {src dst lo mid hi li ri ki : Nat} {v : BitVec 32}
    (hinv : M4MergeInv key wsM src dst lo mid hi wsD li ri ki)
    (hli : li < mid) (hhi : src + hi ≤ wsM.length) (hdhi : dst + hi ≤ wsD.length)
    (_hdisj : dst + hi ≤ src ∨ src + hi ≤ dst)
    (hsL : M4Sorted key wsM (src + lo) (src + mid))
    (hv : v = wsM[src + li]'(by have := hinv.2.2.2.1; have := hinv.2.2.2.2.1; omega))
    (hvl : v.toNat < 2 ^ 31)
    (hvs : ∀ q, src + ri ≤ q → q < src + hi → key v.toNat ≤ key (m4WsVal wsM q)) :
    M4MergeInv key wsM src dst lo mid hi (wsD.set (dst + ki) v) (li + 1) ri (ki + 1) := by
  obtain ⟨hlen, hlo_li, hli_mid, hmid_ri, hri_hi, hki, hpre, hbd, hsrt, hpm⟩ := hinv
  have hki_lt : ki < hi := by omega
  have hki_ge : lo ≤ ki := by omega
  have hdst_ki : dst + ki < wsD.length := by omega
  have hval_set : ∀ p, m4WsVal (wsD.set (dst + ki) v) p =
      if p = dst + ki then v.toNat else m4WsVal wsD p := fun p => by
    unfold m4WsVal; by_cases hp : p = dst + ki
    · subst hp; simp only [↓reduceIte]; rw [List.getElem?_set_self hdst_ki, Option.getD_some]
    · simp only [hp, ↓reduceIte]; rw [List.getElem?_set_ne (Ne.symm hp)]
  have hv_wsM : v.toNat = m4WsVal wsM (src + li) := by
    unfold m4WsVal; rw [hv, List.getElem?_eq_getElem (by omega), Option.getD_some]
  refine ⟨by rw [List.length_set, hlen], by omega, by omega, hmid_ri, hri_hi, by omega,
    fun p hp => by rw [List.getElem?_set_ne (by omega)]; exact hpre p hp,
    fun p hp1 hp2 => ?_, fun a b ha hab hb => ?_, ?_⟩
  · rw [hval_set p]; split
    · exact ⟨hvl, fun q hq1 hq2 => by
        rw [hv_wsM]; exact hsL (src + li) q (by omega) (by omega) hq2, hvs⟩
    · have hp_old := hbd p hp1 (by omega)
      exact ⟨hp_old.1, fun q hq1 hq2 => hp_old.2.1 q (by omega) hq2, hp_old.2.2⟩
  · rw [hval_set a, hval_set b]; split <;> split
    · exact Nat.le_refl _
    · omega
    · next hnb =>
      have ha_old := hbd a ha (by omega)
      rw [hv_wsM]; exact ha_old.2.1 (src + li) (by omega) (by omega)
    · exact hsrt a b ha (by omega) (by omega)
  · have htk : ((wsD.set (dst + ki) v).drop (dst + lo)).take (ki + 1 - lo) =
        ((wsD.drop (dst + lo)).take (ki - lo)) ++ [v] := by
      have h1 : (wsD.set (dst + ki) v).drop (dst + lo) =
          ((wsD.drop (dst + lo)).set (ki - lo) v) := by
        rw [List.drop_set]
        simp only [show ¬ dst + ki < dst + lo by omega, ↓reduceIte,
          show dst + ki - (dst + lo) = ki - lo by omega]
      have htake_s : ((wsD.drop (dst + lo)).set (ki - lo) v).take (ki - lo) =
          (wsD.drop (dst + lo)).take (ki - lo) := List.take_set_of_le (le_refl _)
      have hsuc : ki + 1 - lo = ki - lo + 1 := by omega
      rw [h1, hsuc, List.take_succ_eq_append_getElem (by simp [List.length_drop]; omega),
        htake_s, List.getElem_set_self (by simp [List.length_drop]; omega)]
    have hdrp : (wsM.drop (src + li)).take (mid - li) =
        v :: (wsM.drop (src + (li + 1))).take (mid - (li + 1)) := by
      have hd := m4Slice_drop_succ (xs := wsM) (i := src + li) (hi := src + mid)
        (by omega) (by omega)
      rw [hv]
      simpa [Nat.add_sub_add_left, show src + li + 1 = src + (li + 1) by omega] using hd
    have hcons_perm : (((wsD.drop (dst + lo)).take (ki - lo) ++ [v]) ++
        (wsM.drop (src + (li + 1))).take (mid - (li + 1)) ++
        (wsM.drop (src + ri)).take (hi - ri)).Perm
        (((wsD.drop (dst + lo)).take (ki - lo)) ++
          (v :: (wsM.drop (src + (li + 1))).take (mid - (li + 1))) ++
          (wsM.drop (src + ri)).take (hi - ri)) := by
      rw [List.append_assoc ((wsD.drop (dst + lo)).take (ki - lo)) [v], List.singleton_append]
    rw [htk]; refine hcons_perm.trans ?_; rw [← hdrp]; exact hpm

theorem m4MergeInv_step_r {key : Nat → Nat} {wsM wsD : List (BitVec 32)}
    {src dst lo mid hi li ri ki : Nat} {v : BitVec 32}
    (hinv : M4MergeInv key wsM src dst lo mid hi wsD li ri ki)
    (hri : ri < hi) (hhi : src + hi ≤ wsM.length) (hdhi : dst + hi ≤ wsD.length)
    (_hdisj : dst + hi ≤ src ∨ src + hi ≤ dst)
    (hsR : M4Sorted key wsM (src + mid) (src + hi))
    (hv : v = wsM[src + ri]'(by omega))
    (hvl : v.toNat < 2 ^ 31)
    (hvs : ∀ q, src + li ≤ q → q < src + mid → key v.toNat ≤ key (m4WsVal wsM q)) :
    M4MergeInv key wsM src dst lo mid hi (wsD.set (dst + ki) v) li (ri + 1) (ki + 1) := by
  obtain ⟨hlen, hlo_li, hli_mid, hmid_ri, hri_hi, hki, hpre, hbd, hsrt, hpm⟩ := hinv
  have hki_lt : ki < hi := by omega
  have hki_ge : lo ≤ ki := by omega
  have hdst_ki : dst + ki < wsD.length := by omega
  have hval_set : ∀ p, m4WsVal (wsD.set (dst + ki) v) p =
      if p = dst + ki then v.toNat else m4WsVal wsD p := fun p => by
    unfold m4WsVal; by_cases hp : p = dst + ki
    · subst hp; simp only [↓reduceIte]; rw [List.getElem?_set_self hdst_ki, Option.getD_some]
    · simp only [hp, ↓reduceIte]; rw [List.getElem?_set_ne (Ne.symm hp)]
  have hv_wsM : v.toNat = m4WsVal wsM (src + ri) := by
    unfold m4WsVal; rw [hv, List.getElem?_eq_getElem (by omega), Option.getD_some]
  refine ⟨by rw [List.length_set, hlen], hlo_li, hli_mid, by omega, by omega, by omega,
    fun p hp => by rw [List.getElem?_set_ne (by omega)]; exact hpre p hp,
    fun p hp1 hp2 => ?_, fun a b ha hab hb => ?_, ?_⟩
  · rw [hval_set p]; split
    · exact ⟨hvl, hvs, fun q hq1 hq2 => by
        rw [hv_wsM]; exact hsR (src + ri) q (by omega) (by omega) hq2⟩
    · have hp_old := hbd p hp1 (by omega)
      exact ⟨hp_old.1, hp_old.2.1, fun q hq1 hq2 => hp_old.2.2 q (by omega) hq2⟩
  · rw [hval_set a, hval_set b]; split <;> split
    · exact Nat.le_refl _
    · omega
    · next hnb =>
      have ha_old := hbd a ha (by omega)
      rw [hv_wsM]; exact ha_old.2.2 (src + ri) (by omega) (by omega)
    · exact hsrt a b ha (by omega) (by omega)
  · have htk : ((wsD.set (dst + ki) v).drop (dst + lo)).take (ki + 1 - lo) =
        ((wsD.drop (dst + lo)).take (ki - lo)) ++ [v] := by
      have h1 : (wsD.set (dst + ki) v).drop (dst + lo) =
          ((wsD.drop (dst + lo)).set (ki - lo) v) := by
        rw [List.drop_set]
        simp only [show ¬ dst + ki < dst + lo by omega, ↓reduceIte,
          show dst + ki - (dst + lo) = ki - lo by omega]
      have htake_s : ((wsD.drop (dst + lo)).set (ki - lo) v).take (ki - lo) =
          (wsD.drop (dst + lo)).take (ki - lo) := List.take_set_of_le (le_refl _)
      have hsuc : ki + 1 - lo = ki - lo + 1 := by omega
      rw [h1, hsuc, List.take_succ_eq_append_getElem (by simp [List.length_drop]; omega),
        htake_s, List.getElem_set_self (by simp [List.length_drop]; omega)]
    have hdrp : (wsM.drop (src + ri)).take (hi - ri) =
        v :: (wsM.drop (src + (ri + 1))).take (hi - (ri + 1)) := by
      have hd := m4Slice_drop_succ (xs := wsM) (i := src + ri) (hi := src + hi)
        (by omega) (by omega)
      rw [hv]
      simpa [Nat.add_sub_add_left, show src + ri + 1 = src + (ri + 1) by omega] using hd
    have hcons_perm : (((wsD.drop (dst + lo)).take (ki - lo) ++ [v]) ++
        (wsM.drop (src + li)).take (mid - li) ++
        (wsM.drop (src + (ri + 1))).take (hi - (ri + 1))).Perm
        (((wsD.drop (dst + lo)).take (ki - lo)) ++
          (wsM.drop (src + li)).take (mid - li) ++
          (v :: (wsM.drop (src + (ri + 1))).take (hi - (ri + 1)))) := by
      simpa [List.append_assoc] using List.Perm.append_left ((wsD.drop (dst + lo)).take (ki - lo))
        List.perm_middle.symm
    rw [htk]; refine hcons_perm.trans ?_; rw [← hdrp]; exact hpm

theorem m4MergeInv_init {key : Nat → Nat} {wsM wsD : List (BitVec 32)}
    {src dst lo mid hi : Nat} (hlen : wsD.length = wsM.length)
    (hlo : lo ≤ mid) (hmid : mid ≤ hi)
    (hpre : ∀ p, p < dst + lo ∨ dst + hi ≤ p → wsD[p]? = wsM[p]?) :
    M4MergeInv key wsM src dst lo mid hi wsD lo mid lo := by
  refine ⟨hlen, le_refl _, hlo, le_refl _, hmid, by simp, hpre,
    fun _ h1 h2 => by omega, fun a b ha hab hb => by omega, ?_⟩
  simp only [Nat.sub_self, List.take_zero, List.nil_append]
  rw [show hi - mid = (hi - lo) - (mid - lo) by omega,
    show src + mid = (src + lo) + (mid - lo) by omega, ← m4Slice_take_add,
    show (mid - lo) + (hi - lo - (mid - lo)) = hi - lo by omega]

theorem m4MergeInv_finish {key : Nat → Nat} {wsM wsD : List (BitVec 32)}
    {src dst lo mid hi li ri ki : Nat}
    (hinv : M4MergeInv key wsM src dst lo mid hi wsD li ri ki)
    (hli : mid ≤ li) (hri : hi ≤ ri) :
    wsD.length = wsM.length ∧ ki = hi ∧
    (∀ p, p < dst + lo ∨ dst + hi ≤ p → wsD[p]? = wsM[p]?) ∧
    (∀ p, dst + lo ≤ p → p < dst + hi → m4WsVal wsD p < 2 ^ 31) ∧
    M4Sorted key wsD (dst + lo) (dst + hi) ∧
    ((wsD.drop (dst + lo)).take (hi - lo)).Perm ((wsM.drop (src + lo)).take (hi - lo)) := by
  obtain ⟨hlen, h1, h2, h3, h4, hki, hpre, hbd, hsrt, hpm⟩ := hinv
  have hli_eq : li = mid := by omega
  have hri_eq : ri = hi := by omega
  have hki_eq : ki = hi := by omega
  subst hki_eq
  refine ⟨hlen, rfl, hpre, fun p hp1 hp2 => (hbd p hp1 hp2).1, hsrt, ?_⟩
  simpa [hli_eq, hri_eq, Nat.sub_self] using hpm

theorem m4Merge_perm_glue {wsM wsD wsD' : List (BitVec 32)} {src dst lo hi : Nat}
    (hlo : lo ≤ hi) (hd_len : dst + hi ≤ wsD.length) (hdp_len : dst + hi ≤ wsD'.length)
    (hpre : ∀ p, p < dst + lo ∨ dst + hi ≤ p → wsD'[p]? = wsD[p]?)
    (hp1 : ((wsD.drop dst).take lo).Perm ((wsM.drop src).take lo))
    (hp2 : ((wsD'.drop (dst + lo)).take (hi - lo)).Perm ((wsM.drop (src + lo)).take (hi - lo))) :
    ((wsD'.drop dst).take hi).Perm ((wsM.drop src).take hi) := by
  have heq_lo : (wsD'.drop dst).take lo = (wsD.drop dst).take lo :=
    m4Slice_congr (by omega) (by omega) fun p hp1' hp2' => hpre p (Or.inl (by omega))
  rw [show hi = lo + (hi - lo) by omega, m4Slice_take_add, m4Slice_take_add, heq_lo]
  exact hp1.append hp2

def M4MaxHeapHole (key : Nat → Nat) (ws : List (BitVec 32)) (lo hi hole : Nat) : Prop :=
  ∀ p, lo ≤ p → p < hi → p ≠ hole →
    (2 * p + 1 < hi → key (m4WsVal ws (2 * p + 1)) ≤ key (m4WsVal ws p)) ∧
    (2 * p + 2 < hi → key (m4WsVal ws (2 * p + 2)) ≤ key (m4WsVal ws p))

def M4HoleParent (key : Nat → Nat) (ws : List (BitVec 32)) (lo hi hole : Nat) : Prop :=
  lo < hole → lo ≤ (hole - 1) / 2 →
    (2 * hole + 1 < hi → key (m4WsVal ws (2 * hole + 1)) ≤ key (m4WsVal ws ((hole - 1) / 2))) ∧
    (2 * hole + 2 < hi → key (m4WsVal ws (2 * hole + 2)) ≤ key (m4WsVal ws ((hole - 1) / 2)))

theorem m4Wsort_sift_step {key : Nat → Nat} {ws : List (BitVec 32)}
    {lo hi root child : Nat} (hlo : lo ≤ root) (hchi : child < hi) (hhi : hi ≤ ws.length)
    (hch : child = 2 * root + 1 ∨ child = 2 * root + 2)
    (hmax : M4MaxHeapHole key ws lo hi root)
    (hpar : M4HoleParent key ws lo hi root)
    (hlt : key (m4WsVal ws root) < key (m4WsVal ws child))
    (hsib : (2 * root + 1 < hi → key (m4WsVal ws (2 * root + 1)) ≤ key (m4WsVal ws child)) ∧
      (2 * root + 2 < hi → key (m4WsVal ws (2 * root + 2)) ≤ key (m4WsVal ws child))) :
    let ws' := (ws.set root (ws[child]'(by omega))).set child (ws[root]'(by omega))
    M4MaxHeapHole key ws' lo hi child ∧ M4HoleParent key ws' lo hi child := by
  intro ws'
  have hrc : root ≠ child := by rcases hch with h | h <;> omega
  have hsw := m4WsVal_swap (ws := ws) (i := root) (j := child) (by omega) (by omega)
  refine ⟨fun p hp hpi _hpc => ?_, fun _ _ => ?_⟩
  · have hstep : ∀ c, (c = 2 * p + 1 ∨ c = 2 * p + 2) → c < hi →
        key (m4WsVal ws' c) ≤ key (m4WsVal ws' p) := by
      intro c hc hci
      have hne_pc : p ≠ c := by rcases hc with h | h <;> omega
      dsimp only [ws']; rw [hsw c, hsw p]
      by_cases hpr : p = root
      · rcases hpr with rfl; rw [show m4SwapIdx p child p = child by unfold m4SwapIdx; simp]
        by_cases hcc : c = child
        · rcases hcc with rfl
          rw [show m4SwapIdx p c c = p by simp [m4SwapIdx, hne_pc.symm]]
          exact Nat.le_of_lt hlt
        · rw [show m4SwapIdx p child c = c by simp [m4SwapIdx, hne_pc.symm, hcc]]
          rcases hc with rfl | rfl; exact hsib.1 hci; exact hsib.2 hci
      · rw [show m4SwapIdx root child p = p by simp [m4SwapIdx, hpr, _hpc]]
        by_cases hcr : c = root
        · subst hcr; have hproot : p = (c - 1) / 2 := by omega
          subst hproot; rw [show m4SwapIdx c child c = child by unfold m4SwapIdx; simp]
          rcases hch with rfl | rfl; exact (hpar (by omega) hp).1 hchi
          exact (hpar (by omega) hp).2 hchi
        · have hne_cc : c ≠ child := fun h => by
            subst h; rcases hch with rfl | rfl <;> rcases hc with hc' | hc' <;> omega
          rw [show m4SwapIdx root child c = c by simp [m4SwapIdx, hcr, hne_cc]]
          rcases hc with rfl | rfl; exact (hmax p hp hpi hpr).1 hci; exact (hmax p hp hpi hpr).2 hci
    exact ⟨hstep _ (Or.inl rfl), hstep _ (Or.inr rfl)⟩
  · rw [show (child - 1) / 2 = root by omega]; dsimp only [ws']; rw [hsw root]
    rw [show m4SwapIdx root child root = child by unfold m4SwapIdx; simp]
    have hc1 : 2 * child + 1 ≠ root ∧ 2 * child + 1 ≠ child := by omega
    have hc2 : 2 * child + 2 ≠ root ∧ 2 * child + 2 ≠ child := by omega
    exact ⟨fun h1 => by
        rw [hsw, show m4SwapIdx root child (2 * child + 1) = 2 * child + 1 by
          simp [m4SwapIdx, hc1.1, hc1.2]]
        exact (hmax child (by omega) hchi hrc.symm).1 h1,
      fun h2 => by
        rw [hsw, show m4SwapIdx root child (2 * child + 2) = 2 * child + 2 by
          simp [m4SwapIdx, hc2.1, hc2.2]]
        exact (hmax child (by omega) hchi hrc.symm).2 h2⟩

theorem m4Wsort_sift_done {wvec ws : List (BitVec 32)} {lo hi root : Nat}
    (hmax : M4MaxHeapHole (m4WvecOff wvec) ws lo hi root)
    (h1 : 2 * root + 1 < hi →
      m4WvecOff wvec (m4WsVal ws (2 * root + 1)) ≤ m4WvecOff wvec (m4WsVal ws root))
    (h2 : 2 * root + 2 < hi →
      m4WvecOff wvec (m4WsVal ws (2 * root + 2)) ≤ m4WvecOff wvec (m4WsVal ws root)) :
    FullWsortMaxHeap wvec ws lo hi := fun p hp1 hp2 => by
  dsimp only [m4WvecOff, m4WsVal] at hmax h1 h2 ⊢
  by_cases hpr : p = root
  · subst hpr; exact ⟨h1, h2⟩
  · exact hmax p hp1 hp2 hpr

theorem m4WsortMaxHeap_root_ge {wvec ws : List (BitVec 32)} {hi : Nat}
    (hmax : FullWsortMaxHeap wvec ws 0 hi) :
    ∀ i < hi, m4WvecOff wvec (m4WsVal ws i) ≤ m4WvecOff wvec (m4WsVal ws 0) := by
  intro i; induction i using Nat.strongRecOn with
  | ind i ih =>
    intro hilt; rcases Nat.eq_zero_or_pos i with rfl | hpos
    · exact Nat.le_refl _
    · have hrec := ih _ (show (i - 1) / 2 < i by omega) (by omega)
      have hstep := hmax ((i - 1) / 2) (by omega) (by omega)
      by_cases hodd : i = 2 * ((i - 1) / 2) + 1
      · have := hstep.1 (by omega); rw [← hodd] at this; exact Nat.le_trans this hrec
      · have := hstep.2 (by omega)
        rw [← show i = 2 * ((i - 1) / 2) + 2 by omega] at this
        exact Nat.le_trans this hrec

theorem m4Wsort_extract_swap {wvec ws : List (BitVec 32)} {e n : Nat}
    (hmax : FullWsortMaxHeap wvec ws 0 (e + 1))
    (hsp : M4SplitLe (m4WvecOff wvec) ws (e + 1) n)
    (hsrt : M4Sorted (m4WvecOff wvec) ws (e + 1) n)
    (he : 0 < e) (hen : e < n) (hn : n ≤ ws.length) :
    let ws' := (ws.set 0 (ws[e]'(by omega))).set e (ws[0]'(by omega))
    M4MaxHeapHole (m4WvecOff wvec) ws' 1 e 0 ∧
    M4SplitLe (m4WvecOff wvec) ws' e n ∧ M4Sorted (m4WvecOff wvec) ws' e n := by
  intro ws'; have hsw := m4WsVal_swap (ws := ws) (i := 0) (j := e) (by omega) (by omega)
  have hroot := m4WsortMaxHeap_root_ge hmax
  have hfix : ∀ k, 0 < k → k < e → m4SwapIdx 0 e k = k := fun k _ _ => by unfold m4SwapIdx; grind
  refine ⟨fun p hp hpe _ => ?_, fun i hi j hj1 hj2 => ?_, fun i j hi1 hij hj2 => ?_⟩
  · have hstep := hmax p (by omega) (by omega)
    constructor
    · intro h1; have hsw1 := hsw (2 * p + 1); have hswp := hsw p
      dsimp only [ws']; rw [hsw1, hswp, hfix _ hp hpe, hfix _ (by omega) h1]
      exact hstep.1 (by omega)
    · intro h2; have hsw2 := hsw (2 * p + 2); have hswp := hsw p
      dsimp only [ws']; rw [hsw2, hswp, hfix _ hp hpe, hfix _ (by omega) h2]
      exact hstep.2 (by omega)
  · rw [hsw i, hsw j]; have hisw : m4SwapIdx 0 e i < e + 1 := by unfold m4SwapIdx; grind
    by_cases hje : j = e
    · subst hje; rw [show m4SwapIdx 0 j j = 0 by unfold m4SwapIdx; grind]; exact hroot _ hisw
    · rw [show m4SwapIdx 0 e j = j by unfold m4SwapIdx; grind]; exact hsp _ hisw _ (by omega) hj2
  · rw [hsw i, hsw j]
    by_cases hie : i = e
    · subst hie; rw [show m4SwapIdx 0 i i = 0 by unfold m4SwapIdx; grind]
      by_cases hje : j = i
      · subst hje; rw [show m4SwapIdx 0 j j = 0 by unfold m4SwapIdx; grind]; exact Nat.le_refl _
      · rw [show m4SwapIdx 0 i j = j by unfold m4SwapIdx; grind]
        exact hsp 0 (by omega) j (by omega) hj2
    · rw [show m4SwapIdx 0 e i = i by unfold m4SwapIdx; grind,
        show m4SwapIdx 0 e j = j by unfold m4SwapIdx; grind]
      exact hsrt i j (by omega) hij hj2

theorem m4Wsort_extract_perm_post {wvec ws ws' : List (BitVec 32)} {e n : Nat}
    (hlen : ws'.length = ws.length) (hen : e ≤ n) (hn : n ≤ ws.length)
    (hperm : ws'.Perm ws) (hsuf : ∀ i, e ≤ i → ws'[i]? = ws[i]?)
    (hsp : M4SplitLe (m4WvecOff wvec) ws e n)
    (hsrt : M4Sorted (m4WvecOff wvec) ws e n) :
    M4SplitLe (m4WvecOff wvec) ws' e n ∧ M4Sorted (m4WvecOff wvec) ws' e n := by
  have htp := m4Perm_take_of_drop_eq hlen (by omega) hperm hsuf
  have htk' : (ws'.take e).length = e := by rw [List.length_take]; omega
  have htk : (ws.take e).length = e := by rw [List.length_take]; omega
  refine ⟨fun i hi j hj1 hj2 => ?_, fun i j hi1 hij hj2 => ?_⟩
  · have hmem : ws'[i]'(by omega) ∈ ws'.take e := by
      have hgm := List.getElem_mem (l := ws'.take e) (n := i) (by rw [htk']; exact hi)
      rwa [List.getElem_take] at hgm
    obtain ⟨i0, hi0, hget0⟩ := List.mem_iff_getElem.mp (htp.mem_iff.mp hmem)
    rw [htk] at hi0; rw [List.getElem_take] at hget0
    have hvi : m4WsVal ws' i = m4WsVal ws i0 := by
      unfold m4WsVal; rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega),
        Option.getD_some, Option.getD_some, hget0]
    have hvj : m4WsVal ws' j = m4WsVal ws j := by unfold m4WsVal; rw [hsuf j hj1]
    rw [hvi, hvj]; exact hsp i0 hi0 j hj1 hj2
  · have hvi : m4WsVal ws' i = m4WsVal ws i := by unfold m4WsVal; rw [hsuf i hi1]
    have hvj : m4WsVal ws' j = m4WsVal ws j := by unfold m4WsVal; rw [hsuf j (by omega)]
    rw [hvi, hvj]; exact hsrt i j hi1 hij hj2

theorem m4Set_virt_swap_eq {ws : List (BitVec 32)} {root ch : Nat} {cl rl : BitVec 32}
    (hr : root < ws.length) (hc : ch < ws.length) (hne : root ≠ ch)
    (hcl : cl = ws[ch]'hc) :
    let wsVirt := ws.set root rl
    ((ws.set root cl).set ch rl) =
      (wsVirt.set root (wsVirt[ch]'(by simp [wsVirt, hc]))).set ch
        (wsVirt[root]'(by simp [wsVirt, hr])) := by
  intro wsVirt
  apply List.ext_getElem
  · simp [wsVirt]
  · intro i hi _; simp only [List.length_set] at hi
    by_cases hic : i = ch <;> by_cases hir : i = root
    · subst hic hir; exact absurd rfl hne
    · subst hic; simp [hne, wsVirt]
    · subst hir; simp [hne, hcl, wsVirt]
    · simp [List.getElem_set, Ne.symm hic, Ne.symm hir, wsVirt]

theorem m4Defrag_sorted_gap {s : FullState} {ws : List (BitVec 32)} {n : Nat}
    (hlay : WatchStackLayout s.core)
    (hcov : M4WsCovers ws n (2 * s.core.cur_vars) (fullWatchSize s))
    (hsrt : M4Sorted (fullWatchOff s) ws 0 n) {i j : Nat} (hij : i < j) (hjn : j < n) :
    fullWatchOff s (m4WsVal ws i) + fullWatchSize s (m4WsVal ws i) ≤
      fullWatchOff s (m4WsVal ws j) := by
  have hi := hcov.1 i (by omega); have hj := hcov.1 j hjn
  have hle := hsrt i j (by omega) (by omega) hjn
  rcases hlay.disjoint _ _ hi.1 hj.1 (hcov.2.1 i (by omega) j hjn (by omega)) hi.2 hj.2 with h | h
  · exact h
  · exfalso; unfold fullWatchOff fullWatchSize at *; omega

theorem m4Wvec_set_even_eq {wvec : List (BitVec 32)} {l : Nat} {v : BitVec 32}
    (hl : 2 * l < wvec.length) (j : Nat) :
    (wvec.set (2 * l) v)[2 * j + 1]? = wvec[2 * j + 1]? ∧
    (j ≠ l → (wvec.set (2 * l) v)[2 * j]? = wvec[2 * j]?) ∧
    (wvec.set (2 * l) v)[2 * l]? = some v :=
  ⟨List.getElem?_set_ne (by omega), fun _ => List.getElem?_set_ne (by omega),
   List.getElem?_set_self hl⟩

theorem m4Defrag_finalize {s : FullState}
    {wvecC wstkC wsort2 : List (BitVec 32)} {n p : Nat} (hlay : WatchStackLayout s.core)
    (hcov : M4WsCovers wsort2 n (2 * s.core.cur_vars) (fullWatchSize s)) (_hp1 : 1 ≤ p)
    (hsz : ∀ l < 2 * s.core.cur_vars, (wvecC[2 * l + 1]?.getD 0#32).toNat = fullWatchSize s l)
    (hzero : ∀ l < 2 * s.core.cur_vars,
      fullWatchSize s l = 0 → (wvecC[2 * l]?.getD 0#32).toNat = 0)
    (hdone : ∀ j < n, let l := m4WsVal wsort2 j; let off := (wvecC[2 * l]?.getD 0#32).toNat;
      1 ≤ off ∧ off + fullWatchSize s l ≤ p ∧
      ∀ k < fullWatchSize s l, wstkC[off + k]? = s.core.wstk[fullWatchOff s l + k]?)
    (hdisj : ∀ a < n, ∀ b < n, a ≠ b →
      let la := m4WsVal wsort2 a; let lb := m4WsVal wsort2 b;
      (wvecC[2 * la]?.getD 0#32).toNat + fullWatchSize s la ≤
        (wvecC[2 * lb]?.getD 0#32).toNat ∨
      (wvecC[2 * lb]?.getD 0#32).toNat + fullWatchSize s lb ≤
        (wvecC[2 * la]?.getD 0#32).toNat) :
    let s' : FullState :=
      { s with core := { s.core with wvec := wvecC, wstk := wstkC, wlen := p, wusable := 0#64 }
               scratch := { s.scratch with wsort := wsort2 } }
    WatchStackLayout s'.core ∧
      ∀ l < 2 * s.core.cur_vars, fullWatchSize s' l = fullWatchSize s l ∧
        ∀ k < fullWatchSize s l,
          s'.core.wstk[fullWatchOff s' l + k]? = s.core.wstk[fullWatchOff s l + k]? := by
  intro s'; have hsz' : ∀ l < 2 * s.core.cur_vars, fullWatchSize s' l = fullWatchSize s l := hsz
  refine ⟨⟨fun l hl => ?_, fun l hl hp => ?_, fun l1 l2 h1 h2 hne hp1 hp2 => ?_,
    fun l hl k hk => ?_⟩, fun l hl => ⟨hsz' l hl, fun k hk => ?_⟩⟩
  · change fullWatchOffCore s'.core l + fullWatchSizeCore s'.core l ≤ p
    rw [show fullWatchSizeCore s'.core l = fullWatchSize s' l from rfl, hsz' l hl]
    rcases Nat.eq_zero_or_pos (fullWatchSize s l) with hz | hp
    · change (wvecC[2 * l]?.getD 0#32).toNat + _ ≤ p; rw [hz, hzero l hl hz]; omega
    · obtain ⟨j, hj, rfl⟩ := hcov.2.2 l hl hp; exact (hdone j hj).2.1
  · rw [show fullWatchSizeCore s'.core l = fullWatchSize s' l from rfl, hsz' l hl] at hp
    obtain ⟨j, hj, rfl⟩ := hcov.2.2 l hl hp; exact (hdone j hj).1
  · rw [show fullWatchSizeCore s'.core l1 = fullWatchSize s' l1 from rfl, hsz' l1 h1] at hp1 ⊢
    rw [show fullWatchSizeCore s'.core l2 = fullWatchSize s' l2 from rfl, hsz' l2 h2] at hp2 ⊢
    obtain ⟨a, ha, rfl⟩ := hcov.2.2 l1 h1 hp1; obtain ⟨b, hb, rfl⟩ := hcov.2.2 l2 h2 hp2
    exact hdisj a ha b hb fun hab => hne (by rw [hab])
  · rw [show fullWatchSizeCore s'.core l = fullWatchSize s' l from rfl, hsz' l hl] at hk
    obtain ⟨j, hj, rfl⟩ := hcov.2.2 l hl (by omega)
    change wstkC[(wvecC[2 * m4WsVal wsort2 j]?.getD 0#32).toNat + k]? ≠ _
    rw [(hdone j hj).2.2 k hk]; exact hlay.no_sentinel _ hl k hk
  · obtain ⟨j, hj, rfl⟩ := hcov.2.2 l hl (by omega); exact (hdone j hj).2.2 k hk

/-! ## 3. `DefragMem` Separation Focus & Array Accessors -/

def FullCoreU32BNoWvec (c : FullCfg) (k : FullCoreState) : Mem 64 → Prop :=
  array (t := i32) c.pFrameTrail k.frame_trail ⋆ array (t := i32) c.pFrameDec k.frame_dec ⋆
  array (t := i32) c.pRepr k.repr ⋆ array (t := i32) c.pMinStk k.min_stk

def FullScrWksNoWsort (c : FullCfg) (sc : FullScratch) : Mem 64 → Prop :=
  array (t := i32) c.pWorkStk1 sc.work_stk1 ⋆ array (t := i32) c.pWorkStk2 sc.work_stk2 ⋆
  array (t := i32) c.pTarjanMark sc.tarjan_mark ⋆
  array (t := i32) c.pTarjanReach sc.tarjan_reach

def FullDefragRest (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
  (FullCoreByteArrs c s.core ⋆ FullCoreU32A c s.core ⋆ FullCoreU32BNoWvec c s.core ⋆
    array (t := i32) c.pArena s.core.arena) ⋆
  (FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆ FullScrWksNoWsort c s.scratch ⋆
    FullScrMetaArrs c s.scratch ⋆ FullScrDynArrs c s.scratch) ⋆ c.pad

theorem fullMem_eq_defrag (c : FullCfg) (s : FullState) :
    FullMem c s = (array (t := i32) c.pWvec s.core.wvec ⋆
      (array (t := i32) c.pWsort s.scratch.wsort ⋆
      (array (t := i32) c.pWstk s.core.wstk ⋆ FullDefragRest c s))) := by
  unfold FullMem FullCoreArrays FullScratchArrays FullCoreU32B FullCoreDynArrs FullScrWksArrs
    FullDefragRest FullCoreU32BNoWvec FullScrWksNoWsort
  ac_rfl

def DefragMem (c : FullCfg) (s : FullState) (wvec ws wstk : List (BitVec 32))
    (R : Mem 64 → Prop) (m : Mem 64) : Prop :=
  (array (t := i32) c.pWvec wvec ⋆ (array (t := i32) c.pWsort ws ⋆
    (array (t := i32) c.pWstk wstk ⋆ (FullDefragRest c s ⋆ R)))) m

theorem focus_defrag {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) :
    DefragMem c s s.core.wvec s.scratch.wsort s.core.wstk R m := by
  unfold DefragMem; rw [fullMem_eq_defrag] at hm; exact sep_ac hm

theorem unfocus_defrag {c : FullCfg} {s : FullState}
    {wvec ws wstk : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : DefragMem c s wvec ws wstk R m) :
    (FullMem c { s with core := { s.core with wvec := wvec, wstk := wstk },
                        scratch := { s.scratch with wsort := ws } } ⋆ R) m := by
  unfold DefragMem at hm; rw [fullMem_eq_defrag]; exact sep_ac hm

theorem wp_load_sep_at {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {t : Ty} {a : Arg Val i64} {ptr : BitVec 64} {v : Val t}
    {k : Val t → Expr Val Cont rs} {m : Mem 64}
    (ha : a.val = ptr) (hld : loadVal m t ptr = some v) (hk : wp Γ Q X (k v) m) :
    wp Γ Q X (.load t a k) m := by
  subst ha; exact ⟨v, hld, hk⟩

theorem wp_store_sep_at {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {t : Ty} {v : Arg Val t} {a : Arg Val i64} {ptr : BitVec 64}
    {k : Expr Val Cont rs} {m : Mem 64} {P' : Mem 64 → Prop}
    (ha : a.val = ptr)
    (hs : storeOk m t ptr ∧ P' (storeMem m t ptr v.val))
    (hk : ∀ m', P' m' → wp Γ Q X k m') :
    wp Γ Q X (.store v a k) m := by
  subst ha; exact ⟨hs.1, hk _ hs.2⟩

theorem ptr_mul4_eq (p idx : BitVec 64) :
    p + idx * 4 = p + BitVec.ofNat 64 (4 * idx.toNat) := by
  congr 1; apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, Nat.mul_comm]

theorem ptr_mul8_eq (p idx : BitVec 64) :
    p + idx * 8 = p + BitVec.ofNat 64 (8 * idx.toNat) := by
  congr 1; apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, Nat.mul_comm]

theorem dsm_load_wvec64 {c : FullCfg} {s : FullState}
    {wvec ws wstk : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {i : Nat}
    (hi : 2 * i + 1 < wvec.length) (hm : DefragMem c s wvec ws wstk R m) :
    loadVal m i64 (c.pWvec + BitVec.ofNat 64 (8 * i)) =
      some (wvec[2 * i].setWidth 64 ||| (wvec[2 * i + 1].setWidth 64 <<< 32)) := by
  unfold DefragMem at hm
  exact load_array32_as_i64 hi hm

theorem dsm_store_wvec64_zero {c : FullCfg} {s : FullState}
    {wvec ws wstk : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {i : Nat}
    (hi : 2 * i + 1 < wvec.length) (hz : wvec[2 * i + 1] = 0#32)
    (hm : DefragMem c s wvec ws wstk R m) :
    storeOk m i64 (c.pWvec + BitVec.ofNat 64 (8 * i)) ∧
      DefragMem c s (wvec.set (2 * i) 0#32) ws wstk R
        (storeMem m i64 (c.pWvec + BitVec.ofNat 64 (8 * i)) 0#64) := by
  unfold DefragMem at hm ⊢
  obtain ⟨hok, hst⟩ := store_array32_as_i64 0#64 hi hm
  have h0_lo : (0#64 : BitVec 64).setWidth 32 = 0#32 := rfl
  have h0_hi : ((0#64 : BitVec 64) >>> 32).setWidth 32 = 0#32 := rfl
  have hget : (wvec.set (2 * i) 0#32)[2 * i + 1]'(by simp [hi]) = 0#32 := by
    rw [List.getElem_set_ne (by omega)]; exact hz
  have hst_eq :
      ((wvec.set (2 * i) ((0#64 : BitVec 64).setWidth 32)).set (2 * i + 1)
        (((0#64 : BitVec 64) >>> 32).setWidth 32)) = wvec.set (2 * i) 0#32 := by
    rw [h0_lo, h0_hi]; conv => lhs; arg 3; rw [← hget]
    exact List.set_getElem_self (by simp [hi])
  rw [hst_eq] at hst
  exact ⟨hok, hst⟩

theorem dsm_load_wvec {c : FullCfg} {s : FullState}
    {wvec ws wstk : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {i : Nat}
    (hi : i < wvec.length) (hm : DefragMem c s wvec ws wstk R m) :
    loadVal m i32 (c.pWvec + BitVec.ofNat 64 (4 * i)) = some wvec[i] := by
  unfold DefragMem at hm
  exact loadVal_array (t := i32) (by decide) hi hm

theorem dsm_store_wvec {c : FullCfg} {s : FullState}
    {wvec ws wstk : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {i : Nat}
    (v : BitVec 32) (hi : i < wvec.length) (hm : DefragMem c s wvec ws wstk R m) :
    storeOk m i32 (c.pWvec + BitVec.ofNat 64 (4 * i)) ∧
      DefragMem c s (wvec.set i v) ws wstk R
        (storeMem m i32 (c.pWvec + BitVec.ofNat 64 (4 * i)) v) := by
  unfold DefragMem at hm ⊢
  exact store_array (t := i32) v (by decide) hi hm

theorem dsm_load_ws {c : FullCfg} {s : FullState}
    {wvec ws wstk : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {i : Nat}
    (hi : i < ws.length) (hm : DefragMem c s wvec ws wstk R m) :
    loadVal m i32 (c.pWsort + BitVec.ofNat 64 (4 * i)) = some ws[i] := by
  unfold DefragMem at hm
  have hm' : (array (t := i32) c.pWsort ws ⋆
      (array (t := i32) c.pWvec wvec ⋆ array (t := i32) c.pWstk wstk ⋆
        (FullDefragRest c s ⋆ R))) m := sep_ac hm
  exact loadVal_array (t := i32) (by decide) hi hm'

theorem dsm_store_ws {c : FullCfg} {s : FullState}
    {wvec ws wstk : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {i : Nat}
    (v : BitVec 32) (hi : i < ws.length) (hm : DefragMem c s wvec ws wstk R m) :
    storeOk m i32 (c.pWsort + BitVec.ofNat 64 (4 * i)) ∧
      DefragMem c s wvec (ws.set i v) wstk R
        (storeMem m i32 (c.pWsort + BitVec.ofNat 64 (4 * i)) v) := by
  unfold DefragMem at hm ⊢
  have hm' : (array (t := i32) c.pWsort ws ⋆
      (array (t := i32) c.pWvec wvec ⋆ array (t := i32) c.pWstk wstk ⋆
        (FullDefragRest c s ⋆ R))) m := sep_ac hm
  obtain ⟨hok, hst⟩ := store_array (t := i32) v (by decide) hi hm'
  exact ⟨hok, sep_ac hst⟩

theorem dsm_load_wstk {c : FullCfg} {s : FullState}
    {wvec ws wstk : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {i : Nat}
    (hi : i < wstk.length) (hm : DefragMem c s wvec ws wstk R m) :
    loadVal m i32 (c.pWstk + BitVec.ofNat 64 (4 * i)) = some wstk[i] := by
  unfold DefragMem at hm
  have hm' : (array (t := i32) c.pWstk wstk ⋆
      (array (t := i32) c.pWvec wvec ⋆ array (t := i32) c.pWsort ws ⋆
        (FullDefragRest c s ⋆ R))) m := sep_ac hm
  exact loadVal_array (t := i32) (by decide) hi hm'

theorem dsm_store_wstk {c : FullCfg} {s : FullState}
    {wvec ws wstk : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {i : Nat}
    (v : BitVec 32) (hi : i < wstk.length) (hm : DefragMem c s wvec ws wstk R m) :
    storeOk m i32 (c.pWstk + BitVec.ofNat 64 (4 * i)) ∧
      DefragMem c s wvec ws (wstk.set i v) R
        (storeMem m i32 (c.pWstk + BitVec.ofNat 64 (4 * i)) v) := by
  unfold DefragMem at hm ⊢
  have hm' : (array (t := i32) c.pWstk wstk ⋆
      (array (t := i32) c.pWvec wvec ⋆ array (t := i32) c.pWsort ws ⋆
        (FullDefragRest c s ⋆ R))) m := sep_ac hm
  obtain ⟨hok, hst⟩ := store_array (t := i32) v (by decide) hi hm'
  exact ⟨hok, sep_ac hst⟩

/-! ## 4. `full_has_ternary_m4_wp` -/

section HasTernaryM4

open FullCongSpecs FullCongHelpers
open scoped FullArenaTactics FullCongTactics

private theorem ht_slice_pop_step {F_cur : List (List Nat)} {k : FullCoreState} {a p rem : Nat}
    (hslice : if k.dense_mode = 0#64 then WatchSliceOk F_cur k a p rem
      else DenseWatchSliceOk F_cur k a p rem) (hpos : 0 < rem) :
    ∃ w0 : BitVec 32, k.wstk[p]? = some w0 ∧
      ((w0 &&& 0x80000000#32) ≠ 0#32 ∧
        (if k.dense_mode = 0#64 then WatchSliceOk F_cur k a (p + 1) (rem - 1)
         else DenseWatchSliceOk F_cur k a (p + 1) (rem - 1)) ∨
       (w0 &&& 0x80000000#32) = 0#32 ∧ 2 ≤ rem ∧
        ∃ cr : BitVec 32, k.wstk[p + 1]? = some cr ∧ cr.toNat ∈ fullArenaClauseRefsCore k ∧
        (if k.dense_mode = 0#64 then WatchSliceOk F_cur k a (p + 2) (rem - 2)
         else DenseWatchSliceOk F_cur k a (p + 2) (rem - 2))) := by
  by_cases hdm : k.dense_mode = 0#64 <;> simp only [hdm, ↓reduceIte] at hslice ⊢
  · cases hslice with
    | empty => omega
    | bin hp hf _ _ _ hrest => exact ⟨_, hp, Or.inl ⟨hf, hrest⟩⟩
    | large hp hp1 hf _ href hrest => exact ⟨_, hp, Or.inr ⟨hf, by omega, _, hp1, href, hrest⟩⟩
  · cases hslice with
    | empty => omega
    | bin hp hf _ _ _ hrest => exact ⟨_, hp, Or.inl ⟨hf, hrest⟩⟩
    | occ hp hp1 hf _ _ href hrest => exact ⟨_, hp, Or.inr ⟨hf, by omega, _, hp1, href, hrest⟩⟩

private theorem ht_ternary_of_unassigned_hits {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hlen : s.LengthsOk c)
    (hw : FullWitnessInv c F0 F_cur s.core) (hnd : Full.FullArenaVarsNodup s)
    (_hcl0 : s.core.cur_level = 0) {cr : Nat} {a b cl : BitVec 32}
    (hcr : cr ∈ fullArenaClauseRefs s) (hng : fullArenaClauseGarb s cr = false)
    (hnosat : ∀ k < fullArenaClauseSizeCore s.core cr,
      s.core.vals[(s.core.arena[cr + 3 + k]?.getD 0#32).toNat]?.getD 0#8 ≠ 1#8)
    (hcnt : ((fullArenaClauseLits s cr).filter (fun l => s.core.vals[l]?.getD 0#8 == 0#8)).length =
      3)
    (ha : a.toNat ∈ (fullArenaClauseLits s cr).filter (fun l => s.core.vals[l]?.getD 0#8 == 0#8))
    (hb : b.toNat ∈ (fullArenaClauseLits s cr).filter (fun l => s.core.vals[l]?.getD 0#8 == 0#8))
    (hc : cl.toNat ∈ (fullArenaClauseLits s cr).filter (fun l => s.core.vals[l]?.getD 0#8 == 0#8))
    (hab : a ≠ b) (hac : a ≠ cl) (hbc : b ≠ cl) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [a.toNat, b.toNat, cl.toNat]) := by
  have hwf := hw.arena.refs_wf cr hcr
  have hbd : cr + 3 + fullArenaClauseSizeCore s.core cr ≤ s.core.arena.length := by
    have := hlen.core_ok.arena_len_le; have := hlen.core_ok.arena_len_arr; omega
  have hnd_lits : (fullArenaClauseLits s cr).Nodup := nodup_of_map_nodup (hnd cr hcr hng)
  let unass := (fullArenaClauseLits s cr).filter (fun l => s.core.vals[l]?.getD 0#8 == 0#8)
  have hsub := nodup_len3_subset (hnd_lits.filter _) hcnt ha hb hc
    (fun h => hab (BitVec.eq_of_toNat_eq h))
    (fun h => hac (BitVec.eq_of_toNat_eq h))
    (fun h => hbc (BitVec.eq_of_toNat_eq h))
  refine entails_of_eval_mem fun α hα => ?_
  have hsat_cl := CNF.entails_clause_def.mp (hw.arena.entails cr hcr hng) α hα
  rw [← clauseEvalVal_iff, clauseEvalVal, List.any_eq_true] at hsat_cl
  obtain ⟨l, hl_mem, hl_true⟩ := hsat_cl
  have hl_lt : l < 2 * s.core.cur_vars := hw.arena.lits_lt cr hcr hng l hl_mem
  have hv_dom := hw.vals_domain l hl_lt
  obtain ⟨k, hk_lt, hget_k⟩ := (mem_fullArenaClauseLitsCore_iff hbd).mp hl_mem
  have hne1 : s.core.vals[l]?.getD 0#8 ≠ 1#8 := by
    have h := hnosat k hk_lt
    have hget_a : s.core.arena[cr + 3 + k]?.getD 0#32 = s.core.arena[cr + 3 + k]'(by omega) := by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    rwa [hget_a, hget_k] at h
  rcases hv_dom with hv0 | hv1 | hvm1
  · have hl_un : l ∈ unass := List.mem_filter.mpr ⟨hl_mem, by simp [hv0]⟩
    rcases hsub l hl_un with rfl | rfl | rfl
    · exact ⟨a.toNat, by simp, hl_true⟩
    · exact ⟨b.toNat, by simp, hl_true⟩
    · exact ⟨cl.toNat, by simp, hl_true⟩
  · exact absurd hv1 hne1
  · exfalso
    obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff l hl_lt).mp hvm1
    have hlvl0 : (s.core.lvl[(s.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
      have := hw.lvl_le i hi; omega
    have hunit := hw.level0_sound i hi hlvl0; rw [heq] at hunit
    have hsat_u := CNF.entails_clause_def.mp hunit α hα
    rw [← clauseEvalVal_iff, clauseEvalVal] at hsat_u; have hln : l ^^^ 1 = litNeg l := rfl
    simp only [List.any_cons, List.any_nil, Bool.or_false, hln, evalLitVal_litNeg,
      hl_true] at hsat_u
    cases hsat_u

private theorem ht_m4_take_step {s : FullState} {cr sz : Nat}
    (hlen : fullArenaClauseSizeCore s.core cr = sz)
    (hbd : cr + 3 + sz ≤ s.core.arena.length) {i : Nat} (hi : i < sz) :
    (fullArenaClauseLits s cr).take (i + 1) =
      (fullArenaClauseLits s cr).take i ++ [(s.core.arena[cr + 3 + i]'(by omega)).toNat] := by
  have hlen_l : (fullArenaClauseLits s cr).length = sz := by
    unfold fullArenaClauseLits fullArenaClauseLitsCore
    simp only [List.length_map, List.length_take, List.length_drop]; omega
  have hget_l : (fullArenaClauseLits s cr)[i]'(by omega) =
      (s.core.arena[cr + 3 + i]'(by omega)).toNat := by
    unfold fullArenaClauseLits fullArenaClauseLitsCore
    simp [List.getElem_map, List.getElem_take, List.getElem_drop]
  rw [List.take_succ_eq_append_getElem (by omega), hget_l]

private theorem ht_m4_take_all {s : FullState} {cr sz : Nat}
    (hlen : fullArenaClauseSizeCore s.core cr = sz)
    (_hbd : cr + 3 + sz ≤ s.core.arena.length) :
    (fullArenaClauseLits s cr).take sz = fullArenaClauseLits s cr := by
  apply List.take_of_length_le
  unfold fullArenaClauseLits fullArenaClauseLitsCore
  simp only [List.length_map, List.length_take, List.length_drop]; omega

private theorem ht_m4_filt_zero {s : FullState} {cr l i : Nat}
    (htk : (fullArenaClauseLits s cr).take (i + 1) = (fullArenaClauseLits s cr).take i ++ [l])
    (hv0 : s.core.vals[l]?.getD 0#8 = 0#8) :
    ((fullArenaClauseLits s cr).take (i + 1)).filter
      (fun x => s.core.vals[x]?.getD 0#8 == 0#8) =
    ((fullArenaClauseLits s cr).take i).filter
      (fun x => s.core.vals[x]?.getD 0#8 == 0#8) ++ [l] := by
  rw [htk, List.filter_append, List.filter_cons, hv0]; simp

private theorem ht_m4_filt_nz {s : FullState} {cr l i : Nat}
    (htk : (fullArenaClauseLits s cr).take (i + 1) = (fullArenaClauseLits s cr).take i ++ [l])
    (hv0 : s.core.vals[l]?.getD 0#8 ≠ 0#8) :
    ((fullArenaClauseLits s cr).take (i + 1)).filter
      (fun x => s.core.vals[x]?.getD 0#8 == 0#8) =
    ((fullArenaClauseLits s cr).take i).filter
      (fun x => s.core.vals[x]?.getD 0#8 == 0#8) := by
  rw [htk, List.filter_append, List.filter_cons,
    show (s.core.vals[l]?.getD 0#8 == 0#8) = false from by
      cases heq : (s.core.vals[l]?.getD 0#8 == 0#8)
      · rfl
      · exact absurd (beq_iff_eq.mp heq) hv0]
  simp

/-- **#1 (`full_has_ternary_m4`)**: proves `Full.fullHasTernarySpec` by scanning the smallest
occurrence list among `{a, b, cl}` (when `b < 2 * cur_vars` / `cl < 2 * cur_vars`). -/
theorem full_has_ternary_m4_wp (Γ : Env) :
    ∀ args m Q X, Full.fullHasTernarySpec args m Q X →
      Func.wp Γ full_has_ternary_m4_body args m Q X := by
  rintro ⟨h, a, b, cl, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hnd, hcl0, ha_lt, hm0, hQ⟩
  have hmx := c.hmaxv; have hwc := c.hwcap; have hac := c.harena
  unfold dimacsBound at hmx hwc hac; have hcl := hlen.core_ok
  have hcv_le := hcl.cur_vars_le; have hwvl := hcl.wvec_len
  have hwsl := hcl.wstk_len_arr; have hwle := hcl.wlen_le
  have harl := hcl.arena_len_arr; have hale := hcl.arena_len_le; have hvl := hcl.vals_len
  have ha_v : a.toNat < s.core.vals.length := by omega
  have hnl_eq : (BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat)).toNat = 2 * s.core.cur_vars := by
    rw [BitVec.toNat_shiftLeft, bv64_ofNat_toNat (by omega)]
    simp [Nat.shiftLeft_eq]; omega
  have ha_shl1 : (a.setWidth 64 <<< (1 : Nat) + 1#64).toNat = 2 * a.toNat + 1 := by
    rw [BitVec.toNat_add, bv64_shl1_toNat, bv_zext32_toNat]; bv_omega
  fc_to_group
  fc_split
  · fc_to_group; exact hQ false (fun h => by cases h)
  · refine wp_join_group (ts := [i32, i32])
      (fun (scan1, min1, ()) m1 =>
        m1 = m0 ∧ scan1.toNat < 2 * s.core.cur_vars ∧
        min1 = s.core.wvec[2 * scan1.toNat + 1]?.getD 0#32) ?_ ?_
    · rintro _ ⟨scan1, min1, ⟨⟩⟩ m1 ⟨hm1, hscan1_lt, hmin1_eq⟩
      subst m1
      fc_to_group
      refine wp_join_group (ts := [i32, i32])
        (fun (scan, min_sz, ()) m1 =>
          m1 = m0 ∧ scan.toNat < 2 * s.core.cur_vars ∧
          min_sz = s.core.wvec[2 * scan.toNat + 1]?.getD 0#32) ?_ ?_
      · rintro _ ⟨scan, min_sz, ⟨⟩⟩ m1 ⟨hm1, hscan_lt, hmin_eq⟩
        subst m1
        have hw_bd := hw.watches.bounds scan.toNat hscan_lt
        have hshl : (scan.setWidth 64 <<< (1 : Nat)).toNat = 2 * scan.toNat := by
          rw [bv64_shl1_toNat, bv_zext32_toNat]; omega
        have hslice0 : if s.core.dense_mode = 0#64 then
              WatchSliceOk F_cur s.core scan.toNat (fullWatchOffCore s.core scan.toNat)
                (fullWatchSizeCore s.core scan.toNat)
            else DenseWatchSliceOk F_cur s.core scan.toNat (fullWatchOffCore s.core scan.toNat)
                (fullWatchSizeCore s.core scan.toNat) := by
          have hwat := hw.watches; unfold ModeWatchesInv at hwat
          by_cases hdm : s.core.dense_mode = 0#64 <;> simp only [hdm, ↓reduceIte] at hwat ⊢
          · exact hwat.slices scan.toNat hscan_lt
          · exact hwat.slices scan.toNat hscan_lt
        fc_split
        · fc_to_group; exact hQ false (fun h => by cases h)
        · fc_to_group
          generalize hoff_v :
            (s.core.wvec[(scan.setWidth 64 <<< (1 : Nat)).toNat]'(by omega)).setWidth 64 = off
          have hoff_n : off.toNat = fullWatchOffCore s.core scan.toNat := by
            rw [← hoff_v, bv_zext32_toNat]; unfold fullWatchOffCore
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
            exact congrArg BitVec.toNat (list_getElem_congr hshl (by omega) (by omega))
          have hwsz_n : min_sz.toNat = fullWatchSizeCore s.core scan.toNat := by
            rw [hmin_eq]; rfl
          have hend_n : (off + min_sz.setWidth 64).toNat = off.toNat + min_sz.toNat := by
            rw [BitVec.toNat_add, bv_zext32_toNat]
            exact Nat.mod_eq_of_lt (by omega)
          refine wp_loop_break_group (brkTs := [i64]) (lpTs := [i64])
            (fun _ mb => mb = m0)
            (fun rem (p, ()) ml =>
              ml = m0 ∧ p.toNat ≤ (off + min_sz.setWidth 64).toNat ∧
              rem = (off + min_sz.setWidth 64).toNat - p.toNat ∧
              (if s.core.dense_mode = 0#64 then
                 WatchSliceOk F_cur s.core scan.toNat p.toNat
                   ((off + min_sz.setWidth 64).toNat - p.toNat)
               else DenseWatchSliceOk F_cur s.core scan.toNat p.toNat
                   ((off + min_sz.setWidth 64).toNat - p.toNat)))
            ?_ ?_ ?_
          · rintro _ ⟨_, ⟨⟩⟩ mb hmb; subst mb
            fc_to_group; exact hQ false (fun h => by cases h)
          · rintro B L rem ⟨p, ⟨⟩⟩ ml hB hL ⟨hml, hp_le, rfl, hslice⟩
            subst ml; fc_split
            {
            have hp_lt : p.toNat < (off + min_sz.setWidth 64).toNat := by bv_omega
            have hp_w : p.toNat < s.core.wstk.length := by omega
            obtain ⟨w0, hw0_get, hcase⟩ := ht_slice_pop_step hslice (by omega)
            have hw0_eq : s.core.wstk[p.toNat]'hp_w = w0 := by
              rw [List.getElem?_eq_getElem hp_w] at hw0_get; exact Option.some.inj hw0_get
            have hp1_n : (p + 1#64).toNat = p.toNat + 1 := by bv_omega
            fc_split
            · rcases hcase with ⟨_, hrest⟩ | ⟨hf0, _⟩
              · fc_to_group; exact hL ((off + min_sz.setWidth 64).toNat - (p + 1#64).toNat)
                  (p + 1#64, ()) m0 (by omega)
                  ⟨rfl, by omega, rfl, by simpa [hp1_n, Nat.sub_sub] using hrest⟩
              · exfalso; rw [hw0_eq] at hc; exact hc hf0
            · rcases hcase with ⟨hf1, _⟩ | ⟨_, hrem2, cr, hcr_get, hcr_ref, hrest2⟩
              · exfalso; rw [hw0_eq] at hc
                change (w0 &&& 0x80000000#32) = 0#32 at hc
                exact hf1 hc
              · have hp1_n' : (p + 1).toNat = p.toNat + 1 := hp1_n
                have hp1_w : (p + 1).toNat < s.core.wstk.length := by omega
                have hcr_eq : s.core.wstk[(p + 1).toNat]'hp1_w = cr := by
                  rw [list_getElem_congr hp1_n' hp1_w (by omega)]
                  rw [List.getElem?_eq_getElem (by omega)] at hcr_get
                  exact Option.some.inj hcr_get
                have hp1_m : (p.toNat + (1 : BitVec 64).toNat) % 2 ^ 64 = p.toNat + 1 :=
                  show (p.toNat + 1) % 2 ^ 64 = p.toNat + 1 from Nat.mod_eq_of_lt (by omega)
                have hcr_m : s.core.wstk[(p.toNat + (1 : BitVec 64).toNat) % 2 ^ 64]'(by omega) =
                    cr := by
                  rw [list_getElem_congr hp1_m _ (by omega)]
                  rw [List.getElem?_eq_getElem (by omega)] at hcr_get
                  exact Option.some.inj hcr_get
                have hcr_wf := hw.arena.refs_wf cr.toNat hcr_ref
                have hp2_n : (p + 1#64 + 1#64).toNat = p.toNat + 2 := by bv_omega
                have hcont2 : L (p + 1 + 1, ()) m0 :=
                  hL ((off + min_sz.setWidth 64).toNat - (p + 1#64 + 1#64).toNat)
                    (p + 1#64 + 1#64, ()) m0 (by omega)
                    ⟨rfl, by omega, rfl, by simpa [hp2_n, Nat.sub_sub] using hrest2⟩
                have hcr_arr : cr.toNat < s.core.arena.length := by omega
                have hcr2_m : (cr.toNat + (2 : BitVec 64).toNat) % 2 ^ 64 = cr.toNat + 2 :=
                  show (cr.toNat + 2) % 2 ^ 64 = cr.toNat + 2 from Nat.mod_eq_of_lt (by omega)
                have hcr_w : ((s.core.wstk[(p + 1).toNat]'hp1_w).setWidth 64).toNat <
                    s.core.arena.length := by rw [hcr_eq, bv_zext32_toNat]; exact hcr_arr
                have hcr2_w : ((s.core.wstk[(p + 1).toNat]'hp1_w).setWidth 64 + 2).toNat <
                    s.core.arena.length := by
                  rw [hcr_eq, BitVec.toNat_add, bv_zext32_toNat, hcr2_m]; omega
                fc_split
                · fc_split
                  · exact hcont2
                  · have hng_red := hc; clear hc; fc_split
                    · exact hcont2
                    · have hsz_ge3 := hc; clear hc
                      simp only [hcr_m, hcr2_m] at hng_red hsz_ge3
                      have hng : fullArenaClauseGarb s cr.toNat = false := by
                        unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
                        rw [List.getElem?_eq_getElem hcr_arr, Option.getD_some]
                        exact garb_false_of_and_480000 hng_red
                      let sz_bv := s.core.arena[cr.toNat + 2]'(by omega)
                      have hsz_eq : sz_bv.toNat = fullArenaClauseSizeCore s.core cr.toNat := by
                        unfold fullArenaClauseSizeCore
                        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                      have hsz3 : 3 ≤ sz_bv.toNat := by
                        change ¬sz_bv.toNat < 3 at hsz_ge3; omega
                      have hsz_cv : sz_bv.toNat ≤ s.core.cur_vars := by
                        rw [hsz_eq]; exact fullArenaClauseSize_le_cur_vars hlen hw hnd hcr_ref hng
                      have hbd_ar : cr.toNat + 3 + sz_bv.toNat ≤ s.core.arena.length := by omega
                      fc_to_group
                      refine wp_loop_break_group
                        (brkTs := [i32, .bool, .bool, .bool, .bool, i32])
                        (lpTs := [i32, .bool, .bool, .bool, i32])
                        (fun (nf, ha, hb, hcf, sat, _, ()) mb2 =>
                          mb2 = m0 ∧
                          (sat = false →
                            (∀ k < sz_bv.toNat,
                              s.core.vals[(s.core.arena[cr.toNat + 3 + k]?.getD 0#32).toNat]?.getD
                                0#8 ≠ 1#8) ∧
                            nf.toNat = ((fullArenaClauseLits s cr.toNat).filter
                              (fun l => s.core.vals[l]?.getD 0#8 == 0#8)).length ∧
                            (ha = true → a.toNat ∈ (fullArenaClauseLits s cr.toNat).filter
                              (fun l => s.core.vals[l]?.getD 0#8 == 0#8)) ∧
                            (hb = true → b.toNat ∈ (fullArenaClauseLits s cr.toNat).filter
                              (fun l => s.core.vals[l]?.getD 0#8 == 0#8)) ∧
                            (hcf = true → cl.toNat ∈ (fullArenaClauseLits s cr.toNat).filter
                              (fun l => s.core.vals[l]?.getD 0#8 == 0#8))))
                        (fun rem2 (nf, ha, hb, hcf, i, ()) mi =>
                          mi = m0 ∧ i.toNat ≤ sz_bv.toNat ∧ rem2 = sz_bv.toNat - i.toNat ∧
                          (∀ k < i.toNat,
                            s.core.vals[(s.core.arena[cr.toNat + 3 + k]?.getD 0#32).toNat]?.getD
                              0#8 ≠ 1#8) ∧
                          nf.toNat = (((fullArenaClauseLits s cr.toNat).take i.toNat).filter
                            (fun l => s.core.vals[l]?.getD 0#8 == 0#8)).length ∧
                          (ha = true →
                            a.toNat ∈ ((fullArenaClauseLits s cr.toNat).take i.toNat).filter
                              (fun l => s.core.vals[l]?.getD 0#8 == 0#8)) ∧
                          (hb = true →
                            b.toNat ∈ ((fullArenaClauseLits s cr.toNat).take i.toNat).filter
                              (fun l => s.core.vals[l]?.getD 0#8 == 0#8)) ∧
                          (hcf = true → cl.toNat ∈
                            ((fullArenaClauseLits s cr.toNat).take i.toNat).filter
                              (fun l => s.core.vals[l]?.getD 0#8 == 0#8)))
                        ?_ ?_ ?_
                      · rintro _ ⟨nf, ha, hb, hcf, sat, _, ⟨⟩⟩ mb2 ⟨hmb2, hpost⟩
                        subst mb2; fc_split_fast
                        · exact hcont2
                        · have hsat_f : sat = false := hc
                          clear hc; fc_split_fast
                          · have hnf3_eq : nf = 3#32 := beq_iff_eq.mp hc
                            clear hc; fc_split_fast
                            · have hha_t : ha = true := hc
                              clear hc; fc_split_fast
                              · have hhb_t : hb = true := hc
                                clear hc; fc_split_fast
                                · have hhc_t : hcf = true := hc
                                  fc_to_group
                                  obtain ⟨hnosat, hcnt, hha, hhb, hhc⟩ := hpost hsat_f
                                  have hnf3 : nf.toNat = 3 := by rw [hnf3_eq]; rfl
                                  exact hQ true fun _ hab hac hbc =>
                                    ht_ternary_of_unassigned_hits hlen hw hnd hcl0 hcr_ref hng
                                      (hsz_eq ▸ hnosat) (hnf3 ▸ hcnt.symm)
                                      (hha hha_t) (hhb hhb_t) (hhc hhc_t) hab hac hbc
                                · exact hcont2
                              · exact hcont2
                            · exact hcont2
                          · exact hcont2
                      · rintro B2 L2 rem2 ⟨nf, ha, hb, hcf, i, ⟨⟩⟩ mi hB2 hL2
                          ⟨hmi, hi_le, rfl, hnosat_i, hcnt_i, hha_i, hhb_i, hhc_i⟩
                        subst mi; fc_split
                        · simp only [hcr_m, hcr2_m] at hc; have hi_lt : i.toNat < sz_bv.toNat := hc
                          have hi1_n : (i + 1#32).toNat = i.toNat + 1 :=
                            show (i.toNat + 1) % 2 ^ 32 = i.toNat + 1 from
                              Nat.mod_eq_of_lt (by omega)
                          have hcr3i_m : (cr.toNat + (3 : BitVec 64).toNat + i.toNat) % 2 ^ 64 =
                              cr.toNat + 3 + i.toNat :=
                            show (cr.toNat + 3 + i.toNat) % 2 ^ 64 = cr.toNat + 3 + i.toNat from
                              Nat.mod_eq_of_lt (by omega)
                          let l := s.core.arena[cr.toNat + 3 + i.toNat]'(by omega)
                          have hl_mem : l.toNat ∈ fullArenaClauseLits s cr.toNat := by
                            rw [mem_fullArenaClauseLitsCore_iff (by omega)]
                            exact ⟨i.toNat, by omega, rfl⟩
                          have hl_lt : l.toNat < 2 * s.core.cur_vars :=
                            hw.arena.lits_lt cr.toNat hcr_ref hng l.toNat hl_mem
                          have htake_step := ht_m4_take_step hsz_eq.symm hbd_ar hi_lt
                          change (fullArenaClauseLits s cr.toNat).take (i.toNat + 1) =
                            (fullArenaClauseLits s cr.toNat).take i.toNat ++ [l.toNat] at htake_step
                          have hnf_le : nf.toNat ≤ i.toNat := by
                            rw [hcnt_i]; have h1 := List.length_filter_le
                              (l := (fullArenaClauseLits s cr.toNat).take i.toNat)
                              (p := fun l => s.core.vals[l]?.getD 0#8 == 0#8)
                            have h2 :
                                ((fullArenaClauseLits s cr.toNat).take i.toNat).length ≤ i.toNat :=
                              List.length_take_le _ _
                            omega
                          have hnf1_n : (nf + 1#32).toNat = nf.toNat + 1 :=
                            show (nf.toNat + 1) % 2 ^ 32 = nf.toNat + 1 from
                              Nat.mod_eq_of_lt (by omega)
                          have hcr3i_n : ((s.core.wstk[(p + 1).toNat]'hp1_w).setWidth 64 + 3 +
                              i.setWidth 64).toNat = cr.toNat + 3 + i.toNat := by
                            rw [hcr_eq, BitVec.toNat_add, BitVec.toNat_add, bv_zext32_toNat,
                              bv_zext32_toNat]
                            show ((cr.toNat + 3) % 2 ^ 64 + i.toNat) % 2 ^ 64 =
                              cr.toNat + 3 + i.toNat
                            omega
                          have hcr3i_w : ((s.core.wstk[(p + 1).toNat]'hp1_w).setWidth 64 + 3 +
                              i.setWidth 64).toNat < s.core.arena.length := by omega
                          have hl_v :
                              ((s.core.arena[((s.core.wstk[(p + 1).toNat]'hp1_w).setWidth 64 +
                                  3 + i.setWidth 64).toNat]'hcr3i_w).setWidth 64).toNat <
                                s.core.vals.length := by
                            rw [list_getElem_congr hcr3i_n hcr3i_w (by omega), bv_zext32_toNat]
                            change l.toNat < s.core.vals.length; omega
                          fc_split
                          · fc_to_group
                            exact hB2 (nf, ha, hb, hcf, true, i, ()) m0 ⟨rfl, fun h => by cases h⟩
                          · simp only [hcr_m, hcr3i_m] at hc
                            have hne1_l : s.core.vals[l.toNat]?.getD 0#8 ≠ 1#8 := by
                              rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                              intro h1
                              change (0#32).slt
                                (BitVec.signExtend 32
                                  (s.core.vals[l.toNat]'(by omega))) = false at hc
                              rw [h1] at hc; exact absurd hc (by decide)
                            have hnosat_next : ∀ k < (i + 1#32).toNat,
                                s.core.vals[(s.core.arena[cr.toNat + 3 + k]?.getD 0#32).toNat]?.getD
                                  0#8 ≠ 1#8 := fun k hk => by
                              rw [hi1_n] at hk
                              by_cases hki : k = i.toNat
                              · subst hki
                                have ha_get : s.core.arena[cr.toNat + 3 + i.toNat]?.getD 0#32 = l :=
                                  by rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                                rw [ha_get]; exact hne1_l
                              · exact hnosat_i k (by omega)
                            fc_to_group; refine wp_join_group (ts := [i32, .bool, .bool, .bool])
                              (fun (nf', ha', hb', hcf', ()) m' => m' = m0 ∧
                                nf'.toNat = (((fullArenaClauseLits s cr.toNat).take
                                  (i.toNat + 1)).filter
                                    (fun x => s.core.vals[x]?.getD 0#8 == 0#8)).length ∧
                                (ha' = true → a.toNat ∈ ((fullArenaClauseLits s cr.toNat).take
                                  (i.toNat + 1)).filter
                                    (fun x => s.core.vals[x]?.getD 0#8 == 0#8)) ∧
                                (hb' = true → b.toNat ∈ ((fullArenaClauseLits s cr.toNat).take
                                  (i.toNat + 1)).filter
                                    (fun x => s.core.vals[x]?.getD 0#8 == 0#8)) ∧
                                (hcf' = true → cl.toNat ∈ ((fullArenaClauseLits s cr.toNat).take
                                  (i.toNat + 1)).filter
                                    (fun x => s.core.vals[x]?.getD 0#8 == 0#8)))
                              ?_ ?_
                            · rintro _ ⟨nf', ha', hb', hcf', ⟨⟩⟩ m'
                                ⟨hm', hcnt', hha', hhb', hhc'⟩
                              subst m'; fc_to_group
                              exact hL2 (sz_bv.toNat - (i + 1#32).toNat)
                                (nf', ha', hb', hcf', i + 1#32, ()) m0 (by omega)
                                ⟨rfl, by omega, rfl, hnosat_next,
                                 hi1_n ▸ hcnt', hi1_n ▸ hha', hi1_n ▸ hhb', hi1_n ▸ hhc'⟩
                            · intro Js hJs
                              fc_split
                              · simp only [hcr_m, hcr3i_m] at hc
                                have hval0 : s.core.vals[l.toNat]?.getD 0#8 = 0#8 := by
                                  rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                                  have hdom := hw.vals_domain l.toNat hl_lt
                                  rw [List.getElem?_eq_getElem (by omega),
                                    Option.getD_some] at hdom
                                  rcases hdom with h | h | h
                                  · exact h
                                  · exfalso; rw [h] at hc; exact absurd hc (by decide)
                                  · exfalso; rw [h] at hc; exact absurd hc (by decide)
                                have hfilt_step := ht_m4_filt_zero htake_step hval0
                                fc_to_group; refine wp_join_group (ts := [.bool])
                                  (fun (ha', ()) m' => m' = m0 ∧ (ha' = true → ha = true ∨ l = a))
                                  ?_ ?_
                                · rintro _ ⟨ha', ⟨⟩⟩ m' ⟨hm', hha'⟩; subst m'
                                  fc_to_group; refine wp_join_group (ts := [.bool])
                                    (fun (hb', ()) m' => m' = m0 ∧ (hb' = true → hb = true ∨ l = b))
                                    ?_ ?_
                                  · rintro _ ⟨hb', ⟨⟩⟩ m' ⟨hm', hhb'⟩; subst m'
                                    fc_to_group; refine wp_join_group (ts := [.bool])
                                      (fun (hcf', ()) m' =>
                                        m' = m0 ∧ (hcf' = true → hcf = true ∨ l = cl))
                                      ?_ ?_
                                    · rintro _ ⟨hcf', ⟨⟩⟩ m' ⟨hm', hhc'⟩; subst m'
                                      fc_to_group
                                      refine hJs (nf + 1#32, ha', hb', hcf', ()) m0
                                        ⟨rfl, ?_, ?_, ?_, ?_⟩
                                      · rw [hfilt_step, List.length_append, hnf1_n, hcnt_i]; simp
                                      · intro ht; rw [hfilt_step, List.mem_append]
                                        rcases hha' ht with h1 | h2
                                        · exact Or.inl (hha_i h1)
                                        · exact Or.inr (by simp [h2])
                                      · intro ht; rw [hfilt_step, List.mem_append]
                                        rcases hhb' ht with h1 | h2
                                        · exact Or.inl (hhb_i h1)
                                        · exact Or.inr (by simp [h2])
                                      · intro ht; rw [hfilt_step, List.mem_append]
                                        rcases hhc' ht with h1 | h2
                                        · exact Or.inl (hhc_i h1)
                                        · exact Or.inr (by simp [h2])
                                    · intro Jc hJc; fc_split_fast
                                      · fc_to_group
                                        rw [list_getElem_congr hcr3i_n (by omega) (by omega),
                                          beq_iff_eq] at hc
                                        exact hJc (true, ()) m0 ⟨rfl, fun _ => Or.inr hc⟩
                                      · fc_to_group; exact hJc (hcf, ()) m0 ⟨rfl, fun h => Or.inl h⟩
                                  · intro Jb hJb; fc_split_fast
                                    · fc_to_group
                                      rw [list_getElem_congr hcr3i_n (by omega) (by omega),
                                        beq_iff_eq] at hc
                                      exact hJb (true, ()) m0 ⟨rfl, fun _ => Or.inr hc⟩
                                    · fc_to_group; exact hJb (hb, ()) m0 ⟨rfl, fun h => Or.inl h⟩
                                · intro Ja hJa; fc_split_fast
                                  · fc_to_group
                                    rw [list_getElem_congr hcr3i_n (by omega) (by omega),
                                      beq_iff_eq] at hc
                                    exact hJa (true, ()) m0 ⟨rfl, fun _ => Or.inr hc⟩
                                  · fc_to_group; exact hJa (ha, ()) m0 ⟨rfl, fun h => Or.inl h⟩
                              · simp only [hcr_m, hcr3i_m] at hc
                                have hne0_l : s.core.vals[l.toNat]?.getD 0#8 ≠ 0#8 := by
                                  rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                                  exact fun h0 => hc (by rw [h0]; rfl)
                                have hfilt_step := ht_m4_filt_nz htake_step hne0_l
                                fc_to_group
                                exact hJs (nf, ha, hb, hcf, ()) m0 ⟨rfl,
                                  by rw [hfilt_step]; exact hcnt_i,
                                  by rw [hfilt_step]; exact hha_i,
                                  by rw [hfilt_step]; exact hhb_i,
                                  by rw [hfilt_step]; exact hhc_i⟩
                        · simp only [hcr_m, hcr2_m] at hc
                          have hi_eq : i.toNat = sz_bv.toNat := by
                            change ¬i.toNat < sz_bv.toNat at hc; omega
                          have htake_all := hi_eq ▸ ht_m4_take_all hsz_eq.symm hbd_ar
                          rw [htake_all] at hcnt_i hha_i hhb_i hhc_i
                          rw [hi_eq] at hnosat_i
                          exact hB2 (nf, ha, hb, hcf, false, i, ()) m0
                            ⟨rfl, fun _ => ⟨hnosat_i, hcnt_i, hha_i, hhb_i, hhc_i⟩⟩
                      · intro B2 L2 hB2 hL2; fc_to_group
                        refine hL2 sz_bv.toNat (0#32, false, false, false, 0#32, ()) m0 ?_
                        dsimp only
                        refine ⟨rfl, by simp, by simp, fun _ h => by simp at h, by simp,
                          ?_, ?_, ?_⟩ <;> exact fun h => by cases h }
            { have hp_eq : p.toNat = (off + min_sz.setWidth 64).toNat := by bv_omega
              exact hB (p, ()) m0 rfl }
          · intro B1 L1 hB1 hL1; fc_to_group
            exact hL1 min_sz.toNat (off, ()) m0
              ⟨rfl, by omega, by rw [hend_n]; omega,
               by rw [hend_n, hoff_n, hwsz_n, Nat.add_sub_cancel_left]; exact hslice0⟩
      · intro Jc hJc
        fc_split
        · have hcl_lt : cl.toNat < 2 * s.core.cur_vars := by omega
          have hcl_v : cl.toNat < s.core.vals.length := by omega
          have hcl_shl1 : (cl.setWidth 64 <<< (1 : Nat) + 1#64).toNat = 2 * cl.toNat + 1 := by
            rw [BitVec.toNat_add, bv64_shl1_toNat, bv_zext32_toNat]; bv_omega
          fc_split
          · fc_to_group; exact hQ false (fun h => by cases h)
          · fc_to_group
            refine wp_join_group (ts := [i32, i32])
              (fun (scan, min_sz, ()) m1 =>
                m1 = m0 ∧ scan.toNat < 2 * s.core.cur_vars ∧
                min_sz = s.core.wvec[2 * scan.toNat + 1]?.getD 0#32)
              (fun _ xs m1 h => by fc_to_group; exact hJc xs m1 h)
              (fun Jc' hJc' => by
                fc_split
                · have hix : (BitVec.setWidth 64 cl <<< 1 + 1).toNat = 2 * cl.toNat + 1 := by
                    rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, bv_zext32_toNat,
                      show (1 : BitVec 64).toNat = 1 from rfl, Nat.shiftLeft_eq]
                    omega
                  have hget_cl : s.core.wvec[(BitVec.setWidth 64 cl <<< 1 + 1).toNat]'(by omega) =
                      s.core.wvec[2 * cl.toNat + 1]?.getD 0#32 := by
                    rw [list_getElem_congr hix _ (by omega),
                      List.getElem?_eq_getElem (by omega), Option.getD_some]
                  rw [hget_cl]
                  exact hJc' (cl, s.core.wvec[2 * cl.toNat + 1]?.getD 0#32, ()) m0
                    ⟨rfl, hcl_lt, rfl⟩
                · exact hJc' (scan1, min1, ()) m0 ⟨rfl, hscan1_lt, hmin1_eq⟩)
        · exact hJc (scan1, min1, ()) m0 ⟨rfl, hscan1_lt, hmin1_eq⟩
    · intro Jb hJb
      fc_split
      · have hb_lt : b.toNat < 2 * s.core.cur_vars := by omega
        have hb_v : b.toNat < s.core.vals.length := by omega
        have hb_shl1 : (b.setWidth 64 <<< (1 : Nat) + 1#64).toNat = 2 * b.toNat + 1 := by
          rw [BitVec.toNat_add, bv64_shl1_toNat, bv_zext32_toNat]; bv_omega
        fc_split
        · fc_to_group; exact hQ false (fun h => by cases h)
        · fc_to_group
          refine wp_join_group (ts := [i32, i32])
            (fun (scan, min_sz, ()) m1 =>
              m1 = m0 ∧ scan.toNat < 2 * s.core.cur_vars ∧
              min_sz = s.core.wvec[2 * scan.toNat + 1]?.getD 0#32)
            (fun _ xs m1 h => by fc_to_group; exact hJb xs m1 h)
            (fun Jb' hJb' => by
              fc_split
              · have hix : (BitVec.setWidth 64 b <<< 1 + 1).toNat = 2 * b.toNat + 1 := by
                  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, bv_zext32_toNat,
                    show (1 : BitVec 64).toNat = 1 from rfl, Nat.shiftLeft_eq]
                  omega
                have hget_b : s.core.wvec[(BitVec.setWidth 64 b <<< 1 + 1).toNat]'(by omega) =
                    s.core.wvec[2 * b.toNat + 1]?.getD 0#32 := by
                  rw [list_getElem_congr hix _ (by omega),
                    List.getElem?_eq_getElem (by omega), Option.getD_some]
                rw [hget_b]
                exact hJb' (b, s.core.wvec[2 * b.toNat + 1]?.getD 0#32, ()) m0
                  ⟨rfl, hb_lt, rfl⟩
              · have hix : (BitVec.setWidth 64 a <<< 1 + 1).toNat = 2 * a.toNat + 1 := by
                  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, bv_zext32_toNat,
                    show (1 : BitVec 64).toNat = 1 from rfl, Nat.shiftLeft_eq]
                  omega
                have hget_a : s.core.wvec[(BitVec.setWidth 64 a <<< 1 + 1).toNat]'(by omega) =
                    s.core.wvec[2 * a.toNat + 1]?.getD 0#32 := by
                  rw [list_getElem_congr hix _ (by omega),
                    List.getElem?_eq_getElem (by omega), Option.getD_some]
                rw [hget_a]
                exact hJb' (a, s.core.wvec[2 * a.toNat + 1]?.getD 0#32, ()) m0
                  ⟨rfl, ha_lt, rfl⟩)
      · have hix : (BitVec.setWidth 64 a <<< 1 + 1).toNat = 2 * a.toNat + 1 := by
          rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, bv_zext32_toNat,
            show (1 : BitVec 64).toNat = 1 from rfl, Nat.shiftLeft_eq]
          omega
        have hget_a : s.core.wvec[(BitVec.setWidth 64 a <<< 1 + 1).toNat]'(by omega) =
            s.core.wvec[2 * a.toNat + 1]?.getD 0#32 := by
          rw [list_getElem_congr hix _ (by omega),
            List.getElem?_eq_getElem (by omega), Option.getD_some]
        rw [hget_a]
        exact hJb (a, s.core.wvec[2 * a.toNat + 1]?.getD 0#32, ()) m0 ⟨rfl, ha_lt, rfl⟩

end HasTernaryM4

end LeanQbe.T.Examples.Kissat.FullM4InprocHot
