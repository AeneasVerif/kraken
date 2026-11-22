module

public import LeanQbe.T.Examples.Kissat.FullBvaHeap
public import LeanQbe.T.Examples.Kissat.FullBvaFwdSpec
public import LeanQbe.T.Logic.C0HeadStep
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` 3-Hop BVA & Binary-Heap Specs & Shared Helpers

Shared foundations, tactics, canonical specs for all `13` functions of `FullBvaHeap`, and
pure bit-mask / scan / `LmBit2Inv` helpers extracted so `FullBvaHeapLemmas{1..6,4a,4b}` compile
as parallel siblings without linear serialization.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullBvaHeap

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

/-! ## 1. `i64` Reinterpretation over `repr` & Scoped Tactics (`FullBvaHeapTactics`) -/

@[expose] def pack64 (lo hi : BitVec 32) : BitVec 64 :=
  lo.setWidth 64 ||| (hi.setWidth 64 <<< 32)

@[expose] def repr64Get (r : List (BitVec 32)) (i : Nat) : BitVec 64 :=
  pack64 (r[2 * i]?.getD 0#32) (r[2 * i + 1]?.getD 0#32)

@[expose] def repr64Set (r : List (BitVec 32)) (i : Nat) (v : BitVec 64) : List (BitVec 32) :=
  (r.set (2 * i) (v.setWidth 32)).set (2 * i + 1) ((v >>> 32).setWidth 32)

theorem repr64Set_length (r : List (BitVec 32)) (i : Nat) (v : BitVec 64) :
    (repr64Set r i v).length = r.length := by
  simp [repr64Set]

private theorem toBytes_append_nat (a b n : Nat) :
    Int.toBytes (a + b) (n : Int) =
      Int.toBytes a (n : Int) ++ Int.toBytes b ((n / 256 ^ a : Nat) : Int) := by
  induction a generalizing n with
  | zero => simp [Int.toBytes]
  | succ a ih =>
    rw [Nat.succ_add, Int.toBytes, Int.toBytes, List.cons_append]
    congr 1
    have h1 : (n : Int) / 256 = ((n / 256 : Nat) : Int) := by omega
    rw [h1, ih (n / 256), Nat.div_div_eq_div_mul, Nat.mul_comm 256, ← Nat.pow_succ]

private theorem toBytes8_eq_append (v : BitVec 64) :
    Int.toBytes 8 v.toInt =
      Int.toBytes 4 (v.setWidth 32).toInt ++ Int.toBytes 4 ((v >>> 32).setWidth 32).toInt := by
  have h0 (n : Nat) (x : Int) : Int.toBytes n x = Int.toBytes n (x % (2 ^ (8 * n) : Int)) :=
    (Int.toBytes_emod n x).symm
  have hnat (n : Nat) (b : BitVec (8 * n)) :
      Int.toBytes n b.toInt = Int.toBytes n (b.toNat : Int) := by
    rw [h0, h0 n (b.toNat : Int)]
    congr 1
    rw [BitVec.toInt_eq_msb_cond]
    have ha : 0 ≤ (b.toNat : Int) ∧ (b.toNat : Int) < (2 ^ (8 * n) : Int) :=
      ⟨Int.natCast_nonneg _, by exact_mod_cast b.isLt⟩
    cases b.msb
    · simp [Int.emod_eq_of_lt ha.1 ha.2]
    · simp only [↓reduceIte]
      have hpow : (2 : Int) ^ (8 * n) = ((2 ^ (8 * n) : Nat) : Int) := by push_cast; rfl
      rw [← hpow, Int.sub_emod_right, Int.emod_eq_of_lt ha.1 ha.2]
  rw [hnat 8 v, hnat 4 (v.setWidth 32), hnat 4 ((v >>> 32).setWidth 32)]
  have hlo : ((v.setWidth 32).toNat : Int) = (v.toNat : Int) % 2 ^ 32 := by
    rw [BitVec.toNat_setWidth]; exact_mod_cast rfl
  have hhi : (((v >>> 32).setWidth 32).toNat : Int) = ((v.toNat / 2 ^ 32 : Nat) : Int) := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have hlt : v.toNat / 2 ^ 32 < 2 ^ 32 := by have := v.isLt; omega
    rw [Nat.mod_eq_of_lt hlt]
  rw [hlo, hhi, Int.toBytes_emod 4 (v.toNat : Int)]
  exact toBytes_append_nat 4 4 v.toNat

private theorem nat_or_mul_two_pow32 {a b : Nat} (ha : a < 2 ^ 32) :
    a ||| (b * 2 ^ 32) = a + b * 2 ^ 32 := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_or]
  by_cases hk : k < 32
  · have h0 : Nat.testBit (b * 2 ^ 32) k = false := by
      rw [Nat.mul_comm, Nat.testBit_two_pow_mul]; simp [Nat.not_le.mpr hk]
    have hpow : 2 ^ 32 = 2 ^ k * 2 ^ (32 - k) := by
      rw [← Nat.pow_add, Nat.add_sub_cancel' (by omega)]
    have hdiv : (a + b * 2 ^ 32) / 2 ^ k = a / 2 ^ k + b * 2 ^ (32 - k) := by
      rw [hpow, ← Nat.mul_assoc, Nat.mul_comm b (2 ^ k), Nat.mul_assoc,
        Nat.add_mul_div_left _ _ (Nat.two_pow_pos k)]
    have heven : 2 ∣ 2 ^ (32 - k) := by
      obtain ⟨m, hm⟩ : ∃ m, 32 - k = m + 1 := ⟨31 - k, by omega⟩
      rw [hm, Nat.pow_succ]; exact Nat.dvd_mul_left 2 _
    obtain ⟨q, hq⟩ := heven
    rw [h0, Bool.or_false, Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq,
      hdiv, hq, Nat.mul_comm 2 q, ← Nat.mul_assoc, Nat.add_mul_mod_self_right]
  · have h0 : Nat.testBit a k = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega)))
    have hhi' : Nat.testBit (b * 2 ^ 32) k = Nat.testBit b (k - 32) := by
      rw [Nat.mul_comm, Nat.testBit_two_pow_mul]; simp [Nat.le_of_not_lt hk]
    have hpow : 2 ^ k = 2 ^ 32 * 2 ^ (k - 32) := by
      rw [← Nat.pow_add, Nat.add_sub_cancel' (by omega)]
    have hdiv : (a + b * 2 ^ 32) / 2 ^ k = b / 2 ^ (k - 32) := by
      rw [hpow, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_right _ _ (by decide),
        Nat.div_eq_of_lt ha, Nat.zero_add]
    rw [h0, hhi', Bool.false_or, Nat.testBit_eq_decide_div_mod_eq,
      Nat.testBit_eq_decide_div_mod_eq, hdiv]

private theorem pack64_lo (lo hi : BitVec 32) : (pack64 lo hi).setWidth 32 = lo := by
  unfold pack64; apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_or, BitVec.toNat_shiftLeft]
  have h1 : lo.toNat < 2 ^ 32 := lo.isLt
  have h2 : hi.toNat < 2 ^ 32 := hi.isLt
  rw [Nat.mod_eq_of_lt (by omega : lo.toNat < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : hi.toNat < 2 ^ 64), Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (by omega : hi.toNat * 2 ^ 32 < 2 ^ 64),
    nat_or_mul_two_pow32 h1, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h1]

private theorem pack64_hi (lo hi : BitVec 32) : ((pack64 lo hi) >>> 32).setWidth 32 = hi := by
  unfold pack64; apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_or,
    BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow]
  have h1 : lo.toNat < 2 ^ 32 := lo.isLt
  have h2 : hi.toNat < 2 ^ 32 := hi.isLt
  rw [Nat.mod_eq_of_lt (by omega : lo.toNat < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : hi.toNat < 2 ^ 64), Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (by omega : hi.toNat * 2 ^ 32 < 2 ^ 64),
    nat_or_mul_two_pow32 h1, Nat.add_mul_div_right _ _ (by decide), Nat.div_eq_of_lt h1,
    Nat.zero_add, Nat.mod_eq_of_lt h2]

private theorem cell64_eq_cell32_sep (a : BitVec 64) (v : BitVec 64) :
    cell64 a v =
      (cell (t := i32) a (v.setWidth 32) ⋆ cell (t := i32) (a + 4) ((v >>> 32).setWidth 32)) := by
  unfold cell64 cell
  simp only [Ty.bytes, Ty.size, i32, toBits, BitVec.setWidth_eq]
  rw [toBytes8_eq_append v]
  exact Mem.At_append_sep _ _ a (by simp [Int.toBytes_length])

private theorem cell32_sep_eq_cell64 (a : BitVec 64) (lo hi : BitVec 32) :
    (cell (t := i32) a lo ⋆ cell (t := i32) (a + 4) hi) = cell64 a (pack64 lo hi) := by
  rw [cell64_eq_cell32_sep a (pack64 lo hi), pack64_lo, pack64_hi]

private theorem array32_focus_pair (a : BitVec 64) (xs : List (BitVec 32)) {i : Nat}
    (hi : 2 * i + 1 < xs.length) :
    array (t := i32) a xs =
      (cell64 (a + BitVec.ofNat 64 (8 * i)) (repr64Get xs i) ⋆
        (array (t := i32) a (xs.take (2 * i)) ⋆
          array (t := i32) (a + BitVec.ofNat 64 (8 * i) + 8) (xs.drop (2 * i + 2)))) := by
  have h1 : 2 * i < xs.length := by omega
  have hdrop : xs.drop (2 * i) = xs[2 * i] :: xs[2 * i + 1] :: xs.drop (2 * i + 2) := by
    rw [List.drop_eq_getElem_cons h1, List.drop_eq_getElem_cons hi]
  conv => lhs; rw [← List.take_append_drop (2 * i) xs, hdrop]
  rw [array_append, array_cons, array_cons, List.length_take_of_le (Nat.le_of_lt h1)]
  have h42 : (i32.bytes * (2 * i)) = 8 * i := by simp [Ty.bytes, Ty.size]; omega
  have h4 : BitVec.ofNat 64 i32.bytes = 4 := rfl
  have h44 : a + BitVec.ofNat 64 (8 * i) + 4 + 4 = a + BitVec.ofNat 64 (8 * i) + 8 := by
    bv_omega
  rw [h42, h4, h44]
  have hget : repr64Get xs i = pack64 xs[2 * i] xs[2 * i + 1] := by
    unfold repr64Get
    rw [List.getElem?_eq_getElem h1, List.getElem?_eq_getElem hi, Option.getD_some,
      Option.getD_some]
  rw [hget, ← sep_assoc (cell (a + BitVec.ofNat 64 (8 * i)) _), cell32_sep_eq_cell64,
    ← sep_assoc, sep_comm (array a _), sep_assoc]

private theorem array32_set_pair (a : BitVec 64) (xs : List (BitVec 32)) {i : Nat}
    (hi : 2 * i + 1 < xs.length) (v : BitVec 64) :
    array (t := i32) a (repr64Set xs i v) =
      (cell64 (a + BitVec.ofNat 64 (8 * i)) v ⋆
        (array (t := i32) a (xs.take (2 * i)) ⋆
          array (t := i32) (a + BitVec.ofNat 64 (8 * i) + 8) (xs.drop (2 * i + 2)))) := by
  have h1 : 2 * i < xs.length := by omega
  have hlen : (repr64Set xs i v).length = xs.length := repr64Set_length xs i v
  have htake : (repr64Set xs i v).take (2 * i) = xs.take (2 * i) := by
    unfold repr64Set
    rw [List.take_set_of_le (by omega), List.take_set_of_le (Nat.le_refl _)]
  have hdrop : (repr64Set xs i v).drop (2 * i + 2) = xs.drop (2 * i + 2) := by
    unfold repr64Set
    rw [List.drop_set_of_lt (by omega), List.drop_set_of_lt (by omega)]
  have hget : repr64Get (repr64Set xs i v) i = v := by
    unfold repr64Get repr64Set
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_self h1,
      List.getElem?_set_self (by simp [hi]), Option.getD_some, Option.getD_some]
    unfold pack64
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_or, BitVec.toNat_setWidth, BitVec.toNat_shiftLeft,
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    have hv := v.isLt
    rw [Nat.mod_eq_of_lt (by omega : v.toNat % 2 ^ 32 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : v.toNat / 2 ^ 32 < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : v.toNat / 2 ^ 32 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : (v.toNat / 2 ^ 32) * 2 ^ 32 < 2 ^ 64),
      nat_or_mul_two_pow32 (Nat.mod_lt _ (by decide))]
    omega
  rw [array32_focus_pair a (repr64Set xs i v) (by rw [hlen]; exact hi), hget, htake, hdrop]

namespace FullBvaHeapTactics

open FullArenaTactics
open scoped FullArenaTactics

private theorem m8 (a i : BitVec 64) : a + i * 8 = a + BitVec.ofNat 64 (8 * i.toNat) := by
  rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, c0_mul_ofNat]

private theorem ufM {c : FullCfg} {s s' : FullState} {G G' B B' R : Mem 64 → Prop}
    {m' : Mem 64} (_hs : FullMem c s = (G ⋆ B)) (hs' : FullMem c s' = (G' ⋆ B'))
    (hb : B' = B) (h : ((G' ⋆ B) ⋆ R) m') : (FullMem c s' ⋆ R) m' := by rw [hs', hb]; exact h

private def reprRest (c : FullCfg) (s : FullState) (R : Mem 64 → Prop) : Mem 64 → Prop :=
  (array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
    array (t := i32) c.pFrameDec s.core.frame_dec ⋆
    array (t := i32) c.pWvec s.core.wvec ⋆ array (t := i32) c.pMinStk s.core.min_stk ⋆
    (FullCoreByteArrs c s.core ⋆ FullCoreU32A c s.core ⋆ FullCoreDynArrs c s.core ⋆
      fullCoreOuter c s)) ⋆ R

@[scoped c0_load] theorem load_full_repr64 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {i : Nat} (hi : 2 * i + 1 < s.core.repr.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i64 (c.pRepr + BitVec.ofNat 64 (8 * i)) = some (repr64Get s.core.repr i) := by
  rw [fullMem_eq_coreU32B] at hm; unfold FullCoreU32B at hm
  have h1 : (array (t := i32) c.pRepr s.core.repr ⋆ reprRest c s R) m := by
    unfold reprRest; ecancel
  rw [array32_focus_pair c.pRepr s.core.repr hi, sep_assoc] at h1
  exact loadVal_cell64 h1

@[scoped c0_load] theorem c0_load_full_repr64 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {i : BitVec 64} (hi : 2 * i.toNat + 1 < s.core.repr.length)
    (hm : (FullMem c s ⋆ R) m) :
    loadVal m i64 (c.pRepr + i * 8) = some (repr64Get s.core.repr i.toNat) := by
  rw [m8]; exact load_full_repr64 hi hm

@[scoped c0_store] theorem store_full_repr64 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {i : Nat} (v : BitVec 64) (hi : 2 * i + 1 < s.core.repr.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i64 (c.pRepr + BitVec.ofNat 64 (8 * i)) ∧
      (FullMem c { s with core := { s.core with repr := repr64Set s.core.repr i v } } ⋆ R)
        (storeMem m i64 (c.pRepr + BitVec.ofNat 64 (8 * i)) v) := by
  have h1 := hm; rw [fullMem_eq_coreU32B] at h1; unfold FullCoreU32B at h1
  have h2 : (array (t := i32) c.pRepr s.core.repr ⋆ reprRest c s R) m := by
    unfold reprRest; ecancel
  rw [array32_focus_pair c.pRepr s.core.repr hi, sep_assoc] at h2
  obtain ⟨hok, hst⟩ := store_cell64 v h2
  rw [← sep_assoc, ← array32_set_pair c.pRepr s.core.repr hi v] at hst
  exact ⟨hok, ufM (fullMem_eq_coreU32B c s) (fullMem_eq_coreU32B c _) rfl
    (by unfold FullCoreU32B; unfold reprRest at hst; dsimp only; ecancel)⟩

@[scoped c0_store] theorem c0_store_full_repr64 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {i : BitVec 64} (v : BitVec 64) (hi : 2 * i.toNat + 1 < s.core.repr.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i64 (c.pRepr + i * 8) ∧
      (FullMem c { s with core := { s.core with repr := repr64Set s.core.repr i.toNat v } } ⋆ R)
        (storeMem m i64 (c.pRepr + i * 8) v) := by
  rw [m8]; exact store_full_repr64 v hi hm

@[scoped c0_load] theorem load_full_scratch_buf0 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : 0 < s.scratch.scratch_buf.length)
    (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 c.pScratchBuf = some s.scratch.scratch_buf[0] := by
  simpa using load_full_scratch_buf (i := 0) hi hm

@[scoped c0_store] theorem store_full_scratch_buf0 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 0 < s.scratch.scratch_buf.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 c.pScratchBuf ∧
      (FullMem c { s with scratch :=
        { s.scratch with scratch_buf := s.scratch.scratch_buf.set 0 v } } ⋆ R)
        (storeMem m i32 c.pScratchBuf v) := by
  simpa using store_full_scratch_buf (i := 0) v hi hm

@[scoped c0_load] theorem load_full_scratch_buf_imm {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {d : Nat} (hd : d % 4 = 0) (hd64 : d < 2 ^ 64)
    (hi : d / 4 < s.scratch.scratch_buf.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 (c.pScratchBuf + BitVec.ofNat 64 d) = some s.scratch.scratch_buf[d / 4] := by
  have heq : BitVec.ofNat 64 d = BitVec.ofNat 64 (4 * (d / 4)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd64,
      Nat.mod_eq_of_lt (by omega)]; omega
  rw [heq]; exact load_full_scratch_buf hi hm

@[scoped c0_store] theorem store_full_scratch_buf_imm {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {d : Nat} (v : BitVec 32) (hd : d % 4 = 0)
    (hd64 : d < 2 ^ 64) (hi : d / 4 < s.scratch.scratch_buf.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pScratchBuf + BitVec.ofNat 64 d) ∧
      (FullMem c { s with scratch :=
        { s.scratch with scratch_buf := s.scratch.scratch_buf.set (d / 4) v } } ⋆ R)
        (storeMem m i32 (c.pScratchBuf + BitVec.ofNat 64 d) v) := by
  have heq : BitVec.ofNat 64 d = BitVec.ofNat 64 (4 * (d / 4)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd64,
      Nat.mod_eq_of_lt (by omega)]; omega
  rw [heq]; exact store_full_scratch_buf v hi hm

@[scoped c0_load] theorem load_full_tmp0 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hi : 0 < s.core.tmp.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 c.pTmp = some s.core.tmp[0] := by
  simpa using load_full_tmp (i := 0) hi hm

@[scoped c0_store] theorem store_full_tmp0 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (v : BitVec 32) (hi : 0 < s.core.tmp.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 c.pTmp ∧
      (FullMem c { s with core := { s.core with tmp := s.core.tmp.set 0 v } } ⋆ R)
        (storeMem m i32 c.pTmp v) := by
  simpa using store_full_tmp (i := 0) v hi hm

@[scoped c0_load] theorem load_full_tarjan_mark0 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : 0 < s.scratch.tarjan_mark.length)
    (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 c.pTarjanMark = some s.scratch.tarjan_mark[0] := by
  simpa using load_full_tarjan_mark (i := 0) hi hm

@[scoped c0_store] theorem store_full_tarjan_mark0 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 0 < s.scratch.tarjan_mark.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 c.pTarjanMark ∧
      (FullMem c { s with scratch :=
        { s.scratch with tarjan_mark := s.scratch.tarjan_mark.set 0 v } } ⋆ R)
        (storeMem m i32 c.pTarjanMark v) := by
  simpa using store_full_tarjan_mark (i := 0) v hi hm

@[scoped bv_c0] theorem bv32_lshr1_nat (x : BitVec 32) : (x >>> (1 : Nat)).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

@[scoped bv_c0] theorem bv32_lshr1_bv (x : BitVec 32) :
    (x >>> (1 : BitVec 32)).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

@[scoped bv_c0] theorem bv64_lshr1_nat (x : BitVec 64) : (x >>> (1 : Nat)).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

@[scoped bv_c0] theorem bv64_lshr1_bv (x : BitVec 64) :
    (x >>> (1 : BitVec 64)).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

@[scoped bv_c0] theorem bv32_shl1_nat (x : BitVec 32) :
    (x <<< (1 : Nat)).toNat = (2 * x.toNat) % 2 ^ 32 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]

@[scoped bv_c0] theorem bv32_shl1_bv (x : BitVec 32) :
    (x <<< (1 : BitVec 32)).toNat = (2 * x.toNat) % 2 ^ 32 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]

@[scoped bv_c0] theorem bv64_shl1_nat (x : BitVec 64) :
    (x <<< (1 : Nat)).toNat = (2 * x.toNat) % 2 ^ 64 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]

@[scoped bv_c0] theorem bv64_shl1_bv (x : BitVec 64) :
    (x <<< (1 : BitVec 64)).toNat = (2 * x.toNat) % 2 ^ 64 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]

@[scoped bv_c0] theorem bv64_shl2_nat (x : BitVec 64) :
    (x <<< (2 : Nat)).toNat = (4 * x.toNat) % 2 ^ 64 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]

@[scoped bv_c0] theorem bv64_shl2_bv (x : BitVec 64) :
    (x <<< (2 : BitVec 64)).toNat = (4 * x.toNat) % 2 ^ 64 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]

@[scoped bv_c0] theorem bv64_setWidth_32 (x : BitVec 32) :
    (BitVec.setWidth 64 x).toNat = x.toNat := by
  simp [BitVec.toNat_setWidth]; have := x.isLt; omega

@[scoped bv_c0] theorem bv32_lshr1_shl1_or_lt2 {x y : BitVec 32} (hy : y.toNat < 2) :
    (((x >>> (1 : Nat)) <<< (1 : Nat)) ||| y).toNat = 2 * (x.toNat / 2) + y.toNat := by
  have hlt : 2 * (x.toNat / 2) < 2 ^ 32 := by have := x.isLt; omega
  have hev : ((x >>> (1 : Nat)) <<< (1 : Nat)).toNat = 2 * (x.toNat / 2) := by
    rw [bv32_shl1_nat, bv32_lshr1_nat, Nat.mod_eq_of_lt hlt]
  rcases (by omega : y.toNat = 0 ∨ y.toNat = 1) with h0 | h1
  · have hy0 : y = 0#32 := BitVec.eq_of_toNat_eq h0; subst hy0
    rw [BitVec.or_zero, hev]; rfl
  · have hy1 : y = 1#32 := BitVec.eq_of_toNat_eq h1; subst hy1
    rw [FullBvaFwdTactics.bv32_or1_of_even (by omega), hev]; rfl

@[scoped bv_c0] theorem bv_repr64Set_len (r : List (BitVec 32)) (i : Nat) (v : BitVec 64) :
    (repr64Set r i v).length = r.length := repr64Set_length r i v

/-- Fast `c0_hsteps` variant with `pruneJnz := false` (never runs `simp only [bv_c0] at *` across
large nested-loop contexts). -/
scoped elab "c0_hfast" : tactic => LeanQbe.T.C0HeadStep.headSteps { pruneJnz := false } 10000

end FullBvaHeapTactics

open FullBvaHeapTactics
open scoped FullArenaTactics FullBvaHeapTactics

/-! ## 2. Pure Generalized BVA Soundness, `PH_VIV`, & Clause-Matching Lemmas -/

namespace FullBvaHeapHelpers

/-- Generalized fresh-variable BVA extension formula over multi-literal residue clauses `Qs`:
adjoins `[2 * fv, f]` (`f ∈ L`) and `(2 * fv + 1) :: R` (`R ∈ Qs`) to `F_cur`. -/
@[expose] def bvaExtendGen (fv : Nat) (L : List Nat) (Qs : List (List Nat))
    (F_cur : List (List Nat)) : List (List Nat) :=
  L.map (fun f => [2 * fv, f]) ++ Qs.map (fun R => (2 * fv + 1) :: R) ++ F_cur

theorem bvaExtendGen_entails_orig (fv : Nat) (L : List Nat) (Qs : List (List Nat))
    (F_cur : List (List Nat)) :
    (cnfOfClauses (bvaExtendGen fv L Qs F_cur)).Entails (cnfOfClauses F_cur) := by
  rw [CNF.entails_def]; intro α hα; rw [cnf_sat_cnfOfClauses_iff] at hα ⊢
  exact fun cl hcl => hα cl (List.mem_append_right _ hcl)

theorem bvaExtendGen_entails_pos {fv : Nat} {L : List Nat} {Qs : List (List Nat)}
    {F_cur : List (List Nat)} {f : Nat} (hf : f ∈ L) :
    (cnfOfClauses (bvaExtendGen fv L Qs F_cur)).EntailsClause (cnfClause [2 * fv, f]) :=
  entails_mem_cnfOfClauses
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨f, hf, rfl⟩)))

theorem bvaExtendGen_entails_neg {fv : Nat} {L : List Nat} {Qs : List (List Nat)}
    {F_cur : List (List Nat)} {R : List Nat} (hR : R ∈ Qs) :
    (cnfOfClauses (bvaExtendGen fv L Qs F_cur)).EntailsClause (cnfClause ((2 * fv + 1) :: R)) :=
  entails_mem_cnfOfClauses
    (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨R, hR, rfl⟩)))

/-- Generalized fresh-variable BVA UNSAT soundness: any model `α` of `F_cur` extends to a model
of `bvaExtendGen mv_cur L Qs F_cur` by setting `mv_cur := true` iff `α` satisfies every residue
clause `R ∈ Qs`. -/
theorem extUnsatSound_bvaExtendGen {F0 : CNF Nat} {mv_cur : Nat} {F_cur : List (List Nat)}
    {L : List Nat} {Qs : List (List Nat)} (hs : ExtUnsatSound F0 mv_cur F_cur)
    (hL : ∀ f ∈ L, f < 2 * mv_cur) (hQ : ∀ R ∈ Qs, ∀ q ∈ R, q < 2 * mv_cur)
    (hprod : ∀ f ∈ L, ∀ R ∈ Qs, (cnfOfClauses F_cur).EntailsClause (cnfClause (f :: R))) :
    ExtUnsatSound F0 (mv_cur + 1) (bvaExtendGen mv_cur L Qs F_cur) := by
  refine ⟨fun c hc l hl => ?_, fun hu => hs.2 ?_⟩
  · unfold bvaExtendGen at hc
    simp only [List.mem_append, List.mem_map] at hc
    rcases hc with (⟨f, hf, rfl⟩ | ⟨R, hR, rfl⟩) | hmem
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · simp [litVar]
      · have := hL l hf; simp [litVar]; omega
    · simp only [List.mem_cons] at hl
      rcases hl with rfl | hmemR
      · simp [litVar]; omega
      · have := hQ R hR l hmemR; simp [litVar]; omega
    · exact Nat.lt_succ_of_lt (hs.1 c hmem l hl)
  · rw [CNF.unsat_iff_not_sat] at hu ⊢
    intro α hα
    let b : Bool := Qs.all (clauseEvalVal α)
    let α' : Nat → Bool := substUpdate α mv_cur b
    have hfresh_lit : ∀ x < 2 * mv_cur, evalLitVal α' x = evalLitVal α x := fun x hx => by
      have hne : litVar x ≠ mv_cur := by simp [litVar]; omega
      simp [evalLitVal, α', substUpdate_ne α b hne]
    have hfresh_cl : ∀ R : List Nat, (∀ x ∈ R, x < 2 * mv_cur) →
        clauseEvalVal α' R = clauseEvalVal α R := fun R hR => by
      unfold clauseEvalVal; induction R with
      | nil => rfl
      | cons x xs ih =>
        simp only [List.any_cons, hfresh_lit x (hR x (by simp)),
          ih (fun y hy => hR y (by simp [hy]))]
    apply hu α'
    rw [cnf_sat_cnfOfClauses_iff]
    intro c hc
    unfold bvaExtendGen at hc
    simp only [List.mem_append, List.mem_map] at hc
    rcases hc with (⟨f, hf, rfl⟩ | ⟨R, hR, rfl⟩) | hmem
    · rw [← clauseEvalVal_iff, clauseEvalVal]
      simp only [List.any_cons, List.any_nil, Bool.or_false, hfresh_lit f (hL f hf)]
      have hpos : evalLitVal α' (2 * mv_cur) = b := by simp [evalLitVal, litVar, litSign, α']
      rw [hpos]
      cases hb : b
      · simp only [Bool.false_or]
        obtain ⟨R0, hR0, hR0f⟩ := List.all_eq_false.mp hb
        have hR0_eq : clauseEvalVal α R0 = false := Bool.eq_false_iff.mpr hR0f
        have hcl := (clauseEvalVal_iff α _).mpr (CNF.entails_clause_def.mp (hprod f hf R0 hR0) α hα)
        simp only [clauseEvalVal, List.any_cons] at hcl
        change (evalLitVal α f || clauseEvalVal α R0) = true at hcl
        rwa [hR0_eq, Bool.or_false] at hcl
      · simp
    · rw [← clauseEvalVal_iff, clauseEvalVal, List.any_cons]
      have hneg : evalLitVal α' (2 * mv_cur + 1) = !b := by
        have hv : litVar (2 * mv_cur + 1) = mv_cur := by simp [litVar]; omega
        have hs' : litSign (2 * mv_cur + 1) = true := by simp [litSign]
        simp [evalLitVal, hv, hs', α']
      change (evalLitVal α' (2 * mv_cur + 1) || clauseEvalVal α' R) = true
      rw [hneg, hfresh_cl R (hQ R hR)]
      cases hb : b
      · simp
      · simp only [Bool.not_true, Bool.false_or]
        exact List.all_eq_true.mp hb R hR
    · have hcs := (cnf_sat_cnfOfClauses_iff α F_cur).mp hα c hmem
      exact (clause_sat_substUpdate_fresh b fun x hx hv => by
        have hlt := hs.1 c hmem x hx; omega).mpr hcs

/-- Generalized fresh-variable introduction for `bvaExtendGen` preserving `FullWitnessInv` and
`FullDenseInv`. -/
theorem fullDenseInv_add_fresh_var_gen {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} {L : List Nat} {Qs : List (List Nat)}
    (hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hmrk : FullLitMarksClear c s) (hnodup : FullArenaVarsNodup s)
    (hext : FullExtScratchOk c s) (hl0 : s.core.cur_level = 0) (hdm : s.core.dense_mode ≠ 0#64)
    (hcv_lt : s.core.cur_vars < c.max_vars)
    (hL : ∀ f ∈ L, f < 2 * s.core.cur_vars)
    (hQs : ∀ R ∈ Qs, ∀ q ∈ R, q < 2 * s.core.cur_vars)
    (hprod : ∀ f ∈ L, ∀ R ∈ Qs, (cnfOfClauses F_cur).EntailsClause (cnfClause (f :: R)))
    (hlen' : s'.LengthsOk c)
    {vals' mrk' flags' lvl' rsns' wvec' : _} {unass' : BitVec 64}
    (hcore' : s'.core =
      { s.core with
        cur_vars := s.core.cur_vars + 1, vals := vals', mrk := mrk', flags := flags',
        lvl := lvl', rsns := rsns', wvec := wvec', unassigned := unass' })
    (hv0 : vals'[2 * s.core.cur_vars]?.getD 1#8 = 0#8)
    (hv1 : vals'[2 * s.core.cur_vars + 1]?.getD 1#8 = 0#8)
    (hv_oth : ∀ l < 2 * c.max_vars, l / 2 ≠ s.core.cur_vars → vals'[l]? = s.core.vals[l]?)
    (hmrk_fv : mrk'[s.core.cur_vars]?.getD 1#8 = 0#8)
    (hmrk_oth : ∀ v < c.max_vars, v ≠ s.core.cur_vars → mrk'[v]? = s.core.mrk[v]?)
    (hlvl_oth : ∀ v < c.max_vars, v ≠ s.core.cur_vars → lvl'[v]? = s.core.lvl[v]?)
    (hrsns_oth : ∀ v < c.max_vars, v ≠ s.core.cur_vars → rsns'[v]? = s.core.rsns[v]?)
    (hwvec_0 : ∀ k < 4, wvec'[4 * s.core.cur_vars + k]?.getD 1#32 = 0#32)
    (hwvec_oth : ∀ i < 4 * c.max_vars, i / 4 ≠ s.core.cur_vars → wvec'[i]? = s.core.wvec[i]?)
    (hll' : s'.scratch.last_learned = s.scratch.last_learned)
    (hext' : s'.scratch.extend_len = s.scratch.extend_len) :
    let F_next := bvaExtendGen s.core.cur_vars L Qs F_cur
    FullWitnessInv c F0 F_next s'.core ∧ FullDenseInv c F0 s' := by
  intro F_next
  let fv := s.core.cur_vars
  have ⟨hw0, hd0⟩ := FullBvaFwdHelpers.fullDenseInv_add_fresh_var (L := []) (Q := [])
    hlen hw hmrk hnodup hext hl0 hdm hcv_lt (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ h => nomatch h) hlen' hcore' hv0 hv1 hv_oth hmrk_fv hmrk_oth hlvl_oth hrsns_oth
    hwvec_0 hwvec_oth hll' hext'
  have hcv' : s'.core.cur_vars = fv + 1 := by rw [hcore']
  have hext_next : ExtUnsatSound F0 s'.core.cur_vars F_next :=
    hcv'.symm ▸ extUnsatSound_bvaExtendGen hw.ext_sound hL hQs hprod
  have hent_gen : (cnfOfClauses F_next).Entails
      (cnfOfClauses (FullBvaFwdHelpers.bvaExtendFormula fv [] [] F_cur)) := by
    simpa [FullBvaFwdHelpers.bvaExtendFormula] using bvaExtendGen_entails_orig fv L Qs F_cur
  have hw' : FullWitnessInv c F0 F_next s'.core := hw0.replace_extSound hext_next hent_gen
  exact ⟨hw', ⟨⟨hlen', F_next, hw'⟩, hd0.2.1, hd0.2.2.1, hd0.2.2.2.1, hd0.2.2.2.2.1,
    hd0.2.2.2.2.2⟩⟩

/-- Bit-20 (`PH_VIV = 0x00100000`) updates on arena clause headers leave `PH_GARB` (bit 19) and
`PH_SHRK` (bit 23) unchanged, hence preserve `fullArenaClauseRefsCore`, `FullWitnessInv`, and
`FullDenseInv`. -/
theorem bv32_or_viv_garb (x : BitVec 32) :
    ((x ||| 0x00100000#32) &&& 0x00080000#32) = (x &&& 0x00080000#32) := by
  rw [BitVec.and_or_distrib_right,
    show (0x00100000#32 &&& 0x00080000#32) = 0#32 from rfl, BitVec.or_zero]

theorem bv32_or_viv_shrk (x : BitVec 32) :
    ((x ||| 0x00100000#32) &&& 0x00800000#32) = (x &&& 0x00800000#32) := by
  rw [BitVec.and_or_distrib_right,
    show (0x00100000#32 &&& 0x00800000#32) = 0#32 from rfl, BitVec.or_zero]

theorem bv32_and_not_viv_garb (x : BitVec 32) :
    ((x &&& ~~~0x00100000#32) &&& 0x00080000#32) = (x &&& 0x00080000#32) := by
  rw [BitVec.and_assoc, show (~~~0x00100000#32 &&& 0x00080000#32) = 0x00080000#32 from rfl]

theorem bv32_and_not_viv_shrk (x : BitVec 32) :
    ((x &&& ~~~0x00100000#32) &&& 0x00800000#32) = (x &&& 0x00800000#32) := by
  rw [BitVec.and_assoc, show (~~~0x00100000#32 &&& 0x00800000#32) = 0x00800000#32 from rfl]

theorem bv32_viv_roundtrip {x : BitVec 32} (h : (x &&& 0x00100000#32) = 0#32) :
    ((x ||| 0x00100000#32) &&& ~~~0x00100000#32) = x := by
  rw [BitVec.and_or_distrib_right,
    show (0x00100000#32 &&& ~~~0x00100000#32) = 0#32 from rfl, BitVec.or_zero]
  have h1 : x = x &&& (~~~0x00100000#32 ||| 0x00100000#32) := by
    rw [show (~~~0x00100000#32 ||| 0x00100000#32) = BitVec.allOnes 32 from rfl, BitVec.and_allOnes]
  conv => rhs; rw [h1, BitVec.and_or_distrib_left, h, BitVec.or_zero]

theorem fullWitnessInv_set_hdr_bit20 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hlen : k.LengthsOk c) (hw : FullWitnessInv c F0 F_cur k)
    (hl0 : k.cur_level = 0) {cref : Nat} (href : cref ∈ fullArenaClauseRefsCore k) (v : BitVec 32)
    (h19 : (v &&& 0x00080000#32) = (fullArenaHdrCore k cref &&& 0x00080000#32))
    (h23 : (v &&& 0x00800000#32) = (fullArenaHdrCore k cref &&& 0x00800000#32)) :
    let k' : FullCoreState := { k with arena := k.arena.set cref v }
    k'.LengthsOk c ∧ fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k ∧
    FullWitnessInv c F0 F_cur k' ∧
    (∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r ∧
      fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r ∧
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r) := by
  intro k'
  have hcref_wf := hw.arena.refs_wf cref href
  have har_len : cref < k.arena.length := by
    have := hlen.arena_len_le; have := hlen.arena_len_arr; omega
  have ha_cref : k'.arena[cref]? = some v := List.getElem?_set_self har_len
  have hne_out : ∀ r ∈ fullArenaClauseRefsCore k, r ≠ cref →
      (r + 3 + fullArenaClauseSizeCore k r ≤ cref ∧ fullArenaNextOff k.arena k.arena_len r ≤ cref) ∨
      (cref + 3 ≤ fullArenaNextOff k.arena k.arena_len cref ∧
        fullArenaNextOff k.arena k.arena_len cref ≤ r) := fun r hr hne => by
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl ⟨by have := fullArenaScanRefs_disjoint hr href hlt
                       have := (hw.arena.refs_wf r hr).2.2.1; omega,
        fullArenaScanRefs_disjoint hr href hlt⟩
    · exact Or.inr ⟨by omega, fullArenaScanRefs_disjoint href hr hgt⟩
  have hnxt : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaNextOff k'.arena k.arena_len r = fullArenaNextOff k.arena k.arena_len r := by
    intro r hr; by_cases hrc : r = cref
    · subst r
      have h2eq : k'.arena[cref + 2]? = k.arena[cref + 2]? := List.getElem?_set_ne (by omega)
      have h1 : ¬ (cref + 3 > k.arena_len) := by omega
      have h2 : ¬ (cref + 3 + (k.arena[cref + 2]?.getD 0#32).toNat > k.arena_len) := by
        unfold fullArenaClauseSizeCore at hcref_wf; omega
      unfold fullArenaNextOff
      simp only [h1, ↓reduceIte, h2eq, h2, ha_cref, Option.getD_some]
      rw [h23, show fullArenaHdrCore k cref = k.arena[cref]?.getD 0#32 from rfl]
      split
      · exact fullArenaSkipShrk_congr fun i hi _ => List.getElem?_set_ne (by omega)
      · rfl
    · refine fullArenaNextOff_congr_block (List.getElem?_set_ne (Ne.symm hrc)) ?_ ?_
      · rcases hne_out r hr hrc with ⟨hlt, _⟩ | ⟨h3, hgt⟩
        · have := (hw.arena.refs_wf r hr).2.1; exact List.getElem?_set_ne (by omega)
        · exact List.getElem?_set_ne (by omega)
      · intro i hi1 _
        rcases hne_out r hr hrc with ⟨_, hle⟩ | ⟨h3, hgt⟩
        · exact List.getElem?_set_ne (by omega)
        · have := (hw.arena.refs_wf r hr).2.2.1; exact List.getElem?_set_ne (by omega)
  have hrefs : fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k :=
    fullArenaClauseRefsCore_congr rfl hnxt
  have hsz_eq : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r := fun r hr => by
    unfold fullArenaClauseSizeCore; dsimp only [k']
    by_cases hrc : r = cref
    · subst r; rw [List.getElem?_set_ne (by omega)]
    · rcases hne_out r hr hrc with ⟨hlt, _⟩ | ⟨h3, hgt⟩
      · have := (hw.arena.refs_wf r hr).2.1; rw [List.getElem?_set_ne (by omega)]
      · rw [List.getElem?_set_ne (by omega)]
  have hgarb_eq : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r := fun r hr => by
    unfold fullArenaClauseGarbCore fullArenaHdrCore; dsimp only [k']
    by_cases hrc : r = cref
    · subst r; rw [List.getElem?_set_self har_len, Option.getD_some, h19]; rfl
    · rw [List.getElem?_set_ne (Ne.symm hrc)]
  have hlits_eq : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r := fun r hr => by
    have hwf := hw.arena.refs_wf r hr
    have hk_bd : r + 3 + fullArenaClauseSizeCore k r ≤ k.arena.length := by
      have := hlen.arena_len_le; have := hlen.arena_len_arr; omega
    refine fullArenaClauseLitsCore_eq_of_hold hk_bd (by simpa [k'] using hk_bd) (hsz_eq r hr) ?_
    intro j hj; dsimp only [k']; apply List.getElem?_set_ne
    by_cases hrc : r = cref
    · subst r; omega
    · rcases hne_out r hr hrc with ⟨h1, _⟩ | ⟨h3, h2⟩ <;> omega
  have harena' : FullArenaClausesInv c F_cur k' := by
    refine ⟨hw.arena.len_ok, ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs] at hr; dsimp only [k'] at hnxt ⊢
      rw [hnxt r hr, hsz_eq r hr]; exact hw.arena.refs_wf r hr
    · intro r hr hsh; rw [hrefs] at hr
      have hsh0 : (fullArenaHdrCore k r &&& 0x00800000#32) ≠ 0#32 := by
        by_cases hrc : r = cref
        · subst r; unfold fullArenaHdrCore at hsh h23 ⊢; simpa [ha_cref, h23] using hsh
        · unfold fullArenaHdrCore at hsh ⊢
          simpa [k', List.getElem?_set_ne (Ne.symm hrc)] using hsh
      obtain ⟨t, ht1, ht2, hsent⟩ := hw.arena.shrk_term r hr hsh0
      have hget_r : k.arena[r]? = some (fullArenaHdrCore k r) := by
        have hr3 := (hw.arena.refs_wf r hr).1
        have : r < k.arena.length := by have := hlen.arena_len_le; have := hlen.arena_len_arr; omega
        unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem this, Option.getD_some]
      obtain ⟨t0, ht0_lo, _, ht0_nxt, ht0_sent⟩ :=
        fullArenaNextOff_hits_sentinel (hw.arena.refs_wf r hr).1
          (by rw [hget_r, Option.getD_some]; exact hsh0) ht1 ht2 hsent
      have ht0_ne : t0 ≠ cref := by
        by_cases hrc : r = cref
        · subst r; have := (hw.arena.refs_wf cref hr).2.1; omega
        · rcases hne_out r hr hrc with ⟨_, hle⟩ | ⟨h3, hgt⟩
          · omega
          · have := (hw.arena.refs_wf r hr).2.1; omega
      have hnxt_le : fullArenaNextOff k.arena k.arena_len r ≤ k.arena_len :=
        (hw.arena.refs_wf r hr).2.2.2.1
      refine ⟨t0, by rw [hsz_eq r hr]; exact ht0_lo, by dsimp only [k']; omega, ?_⟩
      dsimp only [k']; rw [List.getElem?_set_ne ht0_ne.symm]; exact ht0_sent
    · intro r hr hng l hl; rw [hrefs] at hr
      rw [hgarb_eq r hr] at hng; rw [hlits_eq r hr] at hl
      exact hw.arena.lits_lt r hr hng l hl
    · intro r hr hng; rw [hrefs] at hr
      rw [hgarb_eq r hr] at hng; rw [hlits_eq r hr]
      exact hw.arena.entails r hr hng
  have hno_rsn : ∀ idx < k.trail_end,
      k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 :=
    fun idx hidx => hw.level0_rsn_none idx hidx (by have := hw.lvl_le idx hidx; omega)
  refine ⟨{ hlen with arena_len_arr := by simp [k', hlen.arena_len_arr] }, hrefs,
    { hw with
      arena := harena'
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hrefs ▸ hr)
      reason_inv := fun idx hidx hne => absurd (hno_rsn idx hidx) hne
      reason_lit_mem := fun idx hidx hne _ => absurd (hno_rsn idx hidx) hne },
    fun r hr => ⟨hgarb_eq r hr, hsz_eq r hr, hlits_eq r hr⟩⟩

/-- Updating only non-soundness core scratch (`repr`, `min_clr`, `tmp`, `tmp_cnt`, `tmp_len`,
`flags`) preserves `FullWitnessInv`. -/
theorem fullWitnessInv_with_core_aux {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k)
    {repr' min_clr' tmp' flags' : List (BitVec 32)} {tc' tl' : Nat} :
    FullWitnessInv c F0 F_cur
      { k with repr := repr', min_clr := min_clr', tmp := tmp', flags := flags',
               tmp_cnt := tc', tmp_len := tl' } :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }

theorem fullDenseInv_with_core_aux {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {repr' min_clr' tmp' flags' : List (BitVec 32)} {tc' tl' : Nat} {sc' : FullScratch}
    (hr : repr'.length = 2 * c.max_vars) (hmc : min_clr'.length = c.max_vars)
    (htmp : tmp'.length = c.max_vars) (hfl : flags'.length = c.max_vars)
    (htl : tl' ≤ c.max_vars) (hsc : sc'.LengthsOk c)
    (hll : sc'.last_learned = s.scratch.last_learned)
    (hext : sc'.extend_len = s.scratch.extend_len) :
    FullDenseInvW c F0 F_cur
      { core := { s.core with repr := repr', min_clr := min_clr', tmp := tmp', flags := flags',
                              tmp_cnt := tc', tmp_len := tl' }
        scratch := sc' } :=
  ⟨⟨{ hinv.1.core_ok with repr_len := hr, min_clr_len_arr := hmc, tmp_len_arr := htmp,
                          flags_len := hfl, tmp_len_le := htl }, hsc⟩,
   fullWitnessInv_with_core_aux hinv.2.1,
   hinv.2.2.1, hinv.2.2.2.1,
   ⟨fun i hi => by dsimp only; rw [hll]; exact hinv.2.2.2.2.1.1 i hi,
    by dsimp only; rw [hext]; exact hinv.2.2.2.2.1.2⟩,
   hinv.2.2.2.2.2.1, hinv.2.2.2.2.2.2⟩

/-- `FullDenseInvW` without `FullLitMarksClear`, for helpers (`hop1`..`hop3`, `pick_cand`) that do
not read or modify `lit_mark` and are called while `full_bva_try_lit` holds bit-0 factor marks. -/
@[expose] def FullDenseInvNoLm (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s : FullState) : Prop :=
  s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ FullArenaVarsNodup s ∧
  FullExtScratchOk c s ∧ s.core.cur_level = 0 ∧ s.core.dense_mode ≠ 0#64

theorem FullDenseInvW.toNoLm {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    (h : FullDenseInvW c F0 F_cur s) : FullDenseInvNoLm c F0 F_cur s :=
  ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem fullDenseInvNoLm_with_core_aux {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hinv : FullDenseInvNoLm c F0 F_cur s)
    {repr' min_clr' tmp' flags' : List (BitVec 32)} {tc' tl' : Nat} {sc' : FullScratch}
    (hr : repr'.length = 2 * c.max_vars) (hmc : min_clr'.length = c.max_vars)
    (htmp : tmp'.length = c.max_vars) (hfl : flags'.length = c.max_vars)
    (htl : tl' ≤ c.max_vars) (hsc : sc'.LengthsOk c)
    (hll : sc'.last_learned = s.scratch.last_learned)
    (hext : sc'.extend_len = s.scratch.extend_len) :
    FullDenseInvNoLm c F0 F_cur
      { core := { s.core with repr := repr', min_clr := min_clr', tmp := tmp', flags := flags',
                              tmp_cnt := tc', tmp_len := tl' }
        scratch := sc' } :=
  ⟨⟨{ hinv.1.core_ok with repr_len := hr, min_clr_len_arr := hmc, tmp_len_arr := htmp,
                          flags_len := hfl, tmp_len_le := htl }, hsc⟩,
   fullWitnessInv_with_core_aux hinv.2.1,
   hinv.2.2.1,
   ⟨fun i hi => by dsimp only; rw [hll]; exact hinv.2.2.2.1.1 i hi,
    by dsimp only; rw [hext]; exact hinv.2.2.2.1.2⟩,
   hinv.2.2.2.2.1, hinv.2.2.2.2.2⟩

/-- Pigeonhole permutation lemma for `full_bva_match_large`: if `R` and `D` are `Nodup`,
`f ∈ D`, `f ∉ R`, `D.length = R.length + 1`, and every element of `D` is either `f` or in `R`,
then `D` is a permutation of `f :: R` (so `D` and `f :: R` are semantically equivalent clauses). -/
theorem nodup_sublist_perm_of_length {α : Type} [DecidableEq α] :
    ∀ {xs ys : List α}, xs.Nodup → ys.Nodup → (∀ x ∈ xs, x ∈ ys) → xs.length = ys.length →
      xs.Perm ys
  | [], [], _, _, _, _ => List.Perm.nil
  | [], _ :: _, _, _, _, hlen => by simp at hlen
  | x :: xs, ys, hnx, hny, hsub, hlen => by
    have hx_mem : x ∈ ys := hsub x (by simp)
    have ⟨hx_notin, hnx'⟩ := List.nodup_cons.mp hnx
    have hperm_y : ys.Perm (x :: ys.erase x) := List.perm_cons_erase hx_mem
    have hny' : (ys.erase x).Nodup := (List.nodup_cons.mp (hny.perm hperm_y)).2
    have hlen' : xs.length = (ys.erase x).length := by
      have h1 := hperm_y.length_eq; simp only [List.length_cons] at h1 hlen; omega
    have hsub' : ∀ z ∈ xs, z ∈ ys.erase x := fun z hz => by
      have hzy : z ∈ ys := hsub z (by simp [hz])
      have hzx : z ≠ x := fun h => hx_notin (h ▸ hz)
      exact (List.mem_erase_of_ne hzx).mpr hzy
    exact (List.Perm.cons x (nodup_sublist_perm_of_length hnx' hny' hsub' hlen')).trans
      hperm_y.symm

theorem clause_entails_of_perm {F : CNF Nat} {C1 C2 : List Nat} (hp : C1.Perm C2)
    (h1 : F.EntailsClause (cnfClause C1)) : F.EntailsClause (cnfClause C2) := by
  rw [CNF.entails_clause_def] at h1 ⊢
  intro α hα
  have h1' := (clauseEvalVal_iff α C1).mpr (h1 α hα)
  rw [← clauseEvalVal_iff]
  simp only [clauseEvalVal, List.any_eq_true] at h1' ⊢
  obtain ⟨x, hx, hxt⟩ := h1'
  exact ⟨x, hp.subset hx, hxt⟩

theorem filter_ne_nodup_length {l : List Nat} {x : Nat} (hnd : l.Nodup) (hx : x ∈ l) :
    (l.filter (· != x)).length + 1 = l.length := by
  have hperm := (List.perm_cons_erase hx).filter (· != x)
  have he : (x :: l.erase x).filter (· != x) = l.erase x := by
    simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    exact List.filter_eq_self.mpr fun y hy => by
      have hne : y ≠ x := fun h => by
        subst h; exact (List.nodup_cons.mp (hnd.perm (List.perm_cons_erase hx))).1 hy
      simp [hne]
  rw [he] at hperm
  have h1 := hperm.length_eq
  have h2 := (List.perm_cons_erase hx).length_eq
  simp only [List.length_cons] at h2; omega

theorem bva_match_large_perm {R D : List Nat} {f : Nat}
    (hR_nd : R.Nodup) (hD_nd : D.Nodup) (hf_in : f ∈ D)
    (hlen : D.length = R.length + 1) (hsub : ∀ x ∈ D, x ≠ f → x ∈ R) :
    D.Perm (f :: R) ∧ (D.filter (· != f)).Perm R := by
  have hD'_nd : (D.filter (· != f)).Nodup := hD_nd.filter _
  have hD'_len : (D.filter (· != f)).length = R.length := by
    have := filter_ne_nodup_length hD_nd hf_in; omega
  have hD'_sub : ∀ x ∈ D.filter (· != f), x ∈ R := fun x hx => by
    simp only [List.mem_filter, bne_iff_ne, ne_eq] at hx
    exact hsub x hx.1 hx.2
  have hfilt : (D.filter (· != f)).Perm R :=
    nodup_sublist_perm_of_length hD'_nd hR_nd hD'_sub hD'_len
  have herase : (D.filter (· != f)).Perm (D.erase f) := by
    have hperm := (List.perm_cons_erase hf_in).filter (· != f)
    have he : (f :: D.erase f).filter (· != f) = D.erase f := by
      simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      exact List.filter_eq_self.mpr fun y hy => by
        have hne : y ≠ f := fun h => by
          subst h; exact (List.nodup_cons.mp (hD_nd.perm (List.perm_cons_erase hf_in))).1 hy
        simp [hne]
    rwa [he] at hperm
  have hD_perm : D.Perm (f :: R) :=
    (List.perm_cons_erase hf_in).trans ((herase.symm.trans hfilt).cons f)
  exact ⟨hD_perm, hfilt⟩

theorem bva_bin_swap_entails {F_cur : List (List Nat)} {a b : Nat}
    (h : (cnfOfClauses F_cur).EntailsClause (cnfClause [a, b])) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [b, a]) :=
  clause_entails_of_perm (List.Perm.swap b a []) h

theorem nodup_of_map_div2 {l : List Nat} (h : (l.map (· / 2)).Nodup) : l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at h
    exact List.nodup_cons.mpr ⟨fun hx => h.1 ⟨x, hx, rfl⟩, ih h.2⟩

end FullBvaHeapHelpers

open FullBvaHeapHelpers

/-! ## 3. Specifications for All `13` `FullBvaHeap` Functions -/

/-- Stronger fresh-var spec preserving `tarjan_mark`, `tarjan_reach`, `sim_sig` alongside all
canonical `Full.fullInitFreshVarSpec` guarantees. -/
@[expose] def fullInitFreshVarHeapSpec : Spec [i64, i32] [] := fun (h, fv, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ fv.toNat < s.core.cur_vars ∧ (FullMem c s ⋆ R) m ∧
    ∀ vals' mrk' flags' lvl' rsns' wvec' unass' sc' m',
      let s' : FullState :=
        { s with
          core := { s.core with vals := vals', mrk := mrk', flags := flags', lvl := lvl',
                                rsns := rsns', wvec := wvec', unassigned := unass' }
          scratch := sc' }
      s'.LengthsOk c → FullExtScratchPres s s' →
      sc'.scratch_buf = s.scratch.scratch_buf →
      sc'.wsort = s.scratch.wsort →
      sc'.tarjan_mark = s.scratch.tarjan_mark →
      sc'.tarjan_reach = s.scratch.tarjan_reach →
      sc'.sim_sig = s.scratch.sim_sig →
      vals'[2 * fv.toNat]?.getD 1#8 = 0#8 → vals'[2 * fv.toNat + 1]?.getD 1#8 = 0#8 →
      (∀ l < 2 * c.max_vars, l / 2 ≠ fv.toNat → vals'[l]? = s.core.vals[l]?) →
      mrk'[fv.toNat]?.getD 1#8 = 0#8 →
      (∀ v < c.max_vars, v ≠ fv.toNat → mrk'[v]? = s.core.mrk[v]?) →
      lvl'[fv.toNat]?.getD 1#32 = 0#32 →
      (∀ v < c.max_vars, v ≠ fv.toNat → lvl'[v]? = s.core.lvl[v]?) →
      rsns'[fv.toNat]?.getD 0#32 = 0xFFFFFFFF#32 →
      (∀ v < c.max_vars, v ≠ fv.toNat → rsns'[v]? = s.core.rsns[v]?) →
      (∀ k < 4, wvec'[4 * fv.toNat + k]?.getD 1#32 = 0#32) →
      (∀ i < 4 * c.max_vars, i / 4 ≠ fv.toNat → wvec'[i]? = s.core.wvec[i]?) →
      (FullMem c s' ⋆ R) m' → Q () m'

@[expose]
def fullBvaHop1Spec : Spec [i64, i32, i32] [i64] := fun (h, src_lit, _dst_idx, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvNoLm c F0 F_cur s ∧ src_lit.toNat < 2 * s.core.cur_vars ∧
    s.core.tmp_cnt ≤ s.core.cur_vars ∧
    (∀ i < s.core.tmp_cnt, (s.core.min_clr[i]?.getD 0#32).toNat < c.max_vars) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (r : BitVec 64) repr' mclr' tc' ant' m',
      let s' : FullState :=
        { core := { s.core with repr := repr', min_clr := mclr', tmp_cnt := tc' }
          scratch := { s.scratch with ant_sz := ant' } }
      FullDenseInvNoLm c F0 F_cur s' → tc' ≤ s.core.cur_vars →
      (∀ i < tc', (mclr'[i]?.getD 0#32).toNat < c.max_vars) →
      ant'.toNat ≤ s.scratch.ant_sz.toNat →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

@[expose]
def fullBvaHop2Spec : Spec [i64, i32, i32] [i64] := fun (h, src_lit, _dst_idx, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvNoLm c F0 F_cur s ∧ src_lit.toNat < 2 * s.core.cur_vars ∧
    s.core.tmp_cnt ≤ s.core.cur_vars ∧ s.core.tmp_len ≤ s.core.cur_vars ∧
    (∀ i < s.core.tmp_cnt, (s.core.min_clr[i]?.getD 0#32).toNat < c.max_vars) ∧
    (∀ i < s.core.tmp_len, (s.scratch.shrink_stk[i]?.getD 0#32).toNat < c.max_vars) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (r : BitVec 64) repr' mclr' tc' tl' ant' sig' shrk' m',
      let s' : FullState :=
        { core := { s.core with repr := repr', min_clr := mclr', tmp_cnt := tc', tmp_len := tl' }
          scratch := { s.scratch with ant_sz := ant', sim_sig := sig', shrink_stk := shrk' } }
      FullDenseInvNoLm c F0 F_cur s' → tc' ≤ s.core.cur_vars → tl' ≤ s.core.cur_vars →
      (∀ i < tc', (mclr'[i]?.getD 0#32).toNat < c.max_vars) →
      (∀ i < tl', (shrk'[i]?.getD 0#32).toNat < c.max_vars) →
      ant'.toNat ≤ s.scratch.ant_sz.toNat →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

@[expose]
def fullBvaHop3Spec : Spec [i64, i32, i32] [i64] := fun (h, src_lit, _dst_idx, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvNoLm c F0 F_cur s ∧ src_lit.toNat < 2 * s.core.cur_vars ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (r : BitVec 64) repr' mclr' ant' sig' shrk' m',
      let s' : FullState :=
        { core := { s.core with repr := repr', min_clr := mclr', tmp_cnt := 0, tmp_len := 0 }
          scratch := { s.scratch with ant_sz := ant', sim_sig := sig', shrink_stk := shrk' } }
      FullDenseInvNoLm c F0 F_cur s' → (FullMem c s' ⋆ R) m' → Q (r, ()) m'

@[expose] def fullFheapUpSpec : Spec [i64, i64, i64, i32] [] :=
  fun (hp_ptr, ps_ptr, wvec_ptr, p, ()) m Q _ =>
    ∃ (nlits : Nat) (hp ps wvec : List (BitVec 32)) (R : Mem 64 → Prop),
      nlits ≤ hp.length ∧ nlits ≤ ps.length ∧ 2 * nlits ≤ wvec.length ∧ nlits < 2 ^ 30 ∧
      p.toNat < nlits ∧
      (∀ i ≤ p.toNat, (hp[i]?.getD 0#32).toNat < nlits) ∧
      (array (t := i32) hp_ptr hp ⋆ array (t := i32) ps_ptr ps ⋆
        array (t := i32) wvec_ptr wvec ⋆ R) m ∧
      ∀ hp' ps' m',
        hp'.length = hp.length → ps'.length = ps.length →
        (∀ i ≤ p.toNat, ∃ j ≤ p.toNat, hp'[i]? = hp[j]?) →
        (∀ i, p.toNat < i → hp'[i]? = hp[i]?) →
        (array (t := i32) hp_ptr hp' ⋆ array (t := i32) ps_ptr ps' ⋆
          array (t := i32) wvec_ptr wvec ⋆ R) m' → Q () m'

@[expose] def fullFheapDownSpec : Spec [i64, i64, i64, i32, i32] [] :=
  fun (hp_ptr, ps_ptr, wvec_ptr, p, n, ()) m Q _ =>
    ∃ (nlits : Nat) (hp ps wvec : List (BitVec 32)) (R : Mem 64 → Prop),
      nlits ≤ hp.length ∧ nlits ≤ ps.length ∧ 2 * nlits ≤ wvec.length ∧ nlits < 2 ^ 30 ∧
      p.toNat < n.toNat ∧ n.toNat ≤ nlits ∧
      (∀ i < n.toNat, (hp[i]?.getD 0#32).toNat < nlits) ∧
      (array (t := i32) hp_ptr hp ⋆ array (t := i32) ps_ptr ps ⋆
        array (t := i32) wvec_ptr wvec ⋆ R) m ∧
      ∀ hp' ps' m',
        hp'.length = hp.length → ps'.length = ps.length →
        (∀ i < n.toNat, ∃ j < n.toNat, hp'[i]? = hp[j]?) →
        (∀ i, n.toNat ≤ i → hp'[i]? = hp[i]?) →
        (array (t := i32) hp_ptr hp' ⋆ array (t := i32) ps_ptr ps' ⋆
          array (t := i32) wvec_ptr wvec ⋆ R) m' → Q () m'

/-- Soundness invariant for one entry `w` in BVA row `r` with factor literal `fr`:
either a binary watch word `w = PW_BIN_FLAG | q` with residue `[q]`, or a live irredundant size
`3..5` arena clause ref containing `fr` with residue `(lits w).filter (· != fr)`. -/
@[expose] def BvaRowEntryOk (F_cur : List (List Nat)) (s : FullState) (fr : Nat) (w : BitVec 32)
    (res : List Nat) : Prop :=
  if (w &&& 0x80000000#32) ≠ 0#32 then
    let q := (w &&& 0x7FFFFFFF#32).toNat
    q < 2 * s.core.cur_vars ∧ res = [q] ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [fr, q])
  else
    w.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s w.toNat = false ∧
    3 ≤ fullArenaClauseSize s w.toNat ∧ fullArenaClauseSize s w.toNat ≤ 5 ∧
    fr ∈ fullArenaClauseLits s w.toNat ∧
    res.Perm ((fullArenaClauseLits s w.toNat).filter (· != fr)) ∧
    (fullArenaClauseLits s w.toNat).Perm (fr :: res)

/-- Complete inductive invariant for the BVA scratch matrix over steps `0 ..< step` (`1 ≤ step`):
tracks `scr[0..step)` factor literals, `scr[16..16+step)` row lengths `2..64`, `scr[64+r*64+m]`
clauses, `scr[1088+r*64+m]` parent indices, and residue lists `res` whose full Cartesian product
with `scr[0..r]` is entailed by `F_cur`. -/
@[expose]
def BvaMatrixInv (c : FullCfg) (F_cur : List (List Nat)) (s : FullState) (step : Nat) : Prop :=
  2304 ≤ c.scratch_cap ∧ 1 ≤ step ∧ step ≤ 16 ∧
  (∀ r < step,
    let fr := (s.scratch.scratch_buf[r]?.getD 0#32).toNat
    let qn := (s.scratch.scratch_buf[16 + r]?.getD 0#32).toNat
    fr < 2 * s.core.cur_vars ∧ 2 ≤ qn ∧ qn ≤ 64 ∧
    ∀ m < qn, ∃ res : List Nat,
      (∀ x ∈ res, x < 2 * s.core.cur_vars) ∧ (res.map (· / 2)).Nodup ∧
      BvaRowEntryOk F_cur s fr (s.scratch.scratch_buf[64 + r * 64 + m]?.getD 0#32) res ∧
      (∀ t ≤ r,
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s.scratch.scratch_buf[t]?.getD 0#32).toNat :: res))) ∧
      (0 < r →
        let pi := (s.scratch.scratch_buf[1088 + r * 64 + m]?.getD 0#32).toNat
        pi < (s.scratch.scratch_buf[16 + (r - 1)]?.getD 0#32).toNat ∧
        BvaRowEntryOk F_cur s (s.scratch.scratch_buf[r - 1]?.getD 0#32).toNat
          (s.scratch.scratch_buf[64 + (r - 1) * 64 + pi]?.getD 0#32) res))

@[expose] def fullBvaMatchLargeSpec : Spec [i64, i32, i32, i32] [.bool] :=
  fun (h, cur_cr, next_lit, d_ref, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R_mem : Mem 64 → Prop) (R_set : List Nat),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      FullArenaVarsNodup s ∧ s.core.cur_level = 0 ∧ s.core.dense_mode ≠ 0#64 ∧
      cur_cr.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s cur_cr.toNat = false ∧
      d_ref.toNat ∈ fullArenaClauseRefs s ∧
      R_set.Nodup ∧ (∀ x ∈ R_set, x < 2 * s.core.cur_vars) ∧
      fullArenaClauseSize s cur_cr.toNat = R_set.length + 1 ∧
      (∀ l < 2 * s.core.cur_vars,
        (s.core.lit_mark[l]?.getD 0#8 &&& 2#8) ≠ 0#8 → l ∈ R_set) ∧
      (FullMem c s ⋆ R_mem) m ∧
      ∀ ok : Bool,
        (ok = true →
          fullArenaClauseGarb s d_ref.toNat = false ∧
          (fullArenaHdr s d_ref.toNat &&& 0x00100000#32) = 0#32 ∧
          fullArenaClauseSize s d_ref.toNat = fullArenaClauseSize s cur_cr.toNat ∧
          next_lit.toNat ∈ fullArenaClauseLits s d_ref.toNat ∧
          (fullArenaClauseLits s d_ref.toNat).Perm (next_lit.toNat :: R_set) ∧
          ((fullArenaClauseLits s d_ref.toNat).filter (· != next_lit.toNat)).Perm R_set ∧
          (cnfOfClauses F_cur).EntailsClause (cnfClause (next_lit.toNat :: R_set))) →
        Q (ok, ()) m

@[expose] def fullBvaScanCandsSpec : Spec [i64, i32, i32, i64] [i32] :=
  fun (h, row_off, cur_qn, init_lits, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧ s.core.cur_level = 0 ∧
      s.core.dense_mode ≠ 0#64 ∧
      init_lits.toNat ≤ 2 * s.core.cur_vars ∧
      (∀ l < 2 * c.max_vars, (s.core.lit_mark[l]?.getD 0#8 &&& 0xFE#8) = 0#8) ∧
      row_off.toNat + cur_qn.toNat ≤ c.scratch_cap ∧ cur_qn.toNat ≤ 64 ∧
      (∀ qi < cur_qn.toNat,
        let w := s.scratch.scratch_buf[row_off.toNat + qi]?.getD 0#32
        if (w &&& 0x80000000#32) ≠ 0#32 then (w &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars
        else w.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s w.toNat = false) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ncntd : BitVec 32) wsort' ws1' ws2' m',
        let s' : FullState :=
          { s with scratch :=
            { s.scratch with wsort := wsort', work_stk1 := ws1', work_stk2 := ws2' } }
        s'.LengthsOk c →
        ncntd.toNat ≤ init_lits.toNat →
        (∀ i < ncntd.toNat, (ws1'[i]?.getD 0#32).toNat < init_lits.toNat) →
        (FullMem c s' ⋆ R) m' → Q (ncntd, ()) m'

@[expose] def fullBvaPickCandSpec : Spec [i64, i32, i32] [i32] :=
  fun (h, ncntd, f0, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvNoLm c F0 F_cur s ∧
      f0.toNat < 2 * s.core.cur_vars ∧ ncntd.toNat ≤ 2 * s.core.cur_vars ∧
      (∀ i < ncntd.toNat, (s.scratch.work_stk1[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (r : BitVec 32) repr' mclr' tc' tl' wsort' ant' sig' shrk' m',
        let s' : FullState :=
          { core := { s.core with repr := repr', min_clr := mclr', tmp_cnt := tc', tmp_len := tl' }
            scratch := { s.scratch with wsort := wsort', ant_sz := ant', sim_sig := sig',
                                        shrink_stk := shrk' } }
        FullDenseInvNoLm c F0 F_cur s' →
        (r = 0xFFFFFFFF#32 ∨ r.toNat < 2 * s.core.cur_vars) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

@[expose] def fullBvaFilterRowSpec : Spec [i64, i32, i32, i32, i32, i32] [i32] :=
  fun (h, row_off, nrow_off, par_off, cur_qn, best_lit, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop) (step : Nat),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧ s.core.cur_level = 0 ∧
      s.core.dense_mode ≠ 0#64 ∧
      1 ≤ step ∧ step < 16 ∧ 2304 ≤ c.scratch_cap ∧
      row_off.toNat = 64 + (step - 1) * 64 ∧
      nrow_off.toNat = 64 + step * 64 ∧
      par_off.toNat = 1088 + step * 64 ∧
      cur_qn.toNat = (s.scratch.scratch_buf[16 + (step - 1)]?.getD 0#32).toNat ∧
      best_lit.toNat < 2 * s.core.cur_vars ∧
      BvaMatrixInv c F_cur s step ∧
      (∀ l < 2 * c.max_vars, (s.core.lit_mark[l]?.getD 0#8 &&& 0xFE#8) = 0#8) ∧
      (∀ r < step, (s.core.lit_mark[(s.scratch.scratch_buf[r]?.getD 0#32).toNat]?.getD 0#8 &&&
        1#8) ≠ 0#8) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (new_qn : BitVec 32) sb' m',
        let s' : FullState := { s with scratch := { s.scratch with scratch_buf := sb' } }
        s'.LengthsOk c → new_qn.toNat ≤ 64 →
        (∀ idx < c.scratch_cap,
          ¬ (nrow_off.toNat ≤ idx ∧ idx < nrow_off.toNat + 64) →
          ¬ (par_off.toNat ≤ idx ∧ idx < par_off.toNat + 64) →
          sb'[idx]? = s.scratch.scratch_buf[idx]?) →
        (∀ nm < new_qn.toNat,
          let pi := (sb'[par_off.toNat + nm]?.getD 0#32).toNat
          pi < cur_qn.toNat ∧
          ∃ res : List Nat,
            (∀ x ∈ res, x < 2 * s.core.cur_vars) ∧ (res.map (· / 2)).Nodup ∧
            BvaRowEntryOk F_cur s (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat
              (s.scratch.scratch_buf[row_off.toNat + pi]?.getD 0#32) res ∧
            BvaRowEntryOk F_cur s best_lit.toNat (sb'[nrow_off.toNat + nm]?.getD 0#32) res ∧
            (∀ t < step, (cnfOfClauses F_cur).EntailsClause
              (cnfClause ((s.scratch.scratch_buf[t]?.getD 0#32).toNat :: res))) ∧
            (cnfOfClauses F_cur).EntailsClause (cnfClause (best_lit.toNat :: res))) →
        (FullMem c s' ⋆ R) m' → Q (new_qn, ()) m'

@[expose] def fullBvaCommitSpec : Spec [i64, i32] [.bool] := fun (h, best_k, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧
    1 ≤ best_k.toNat ∧ best_k.toNat < 16 ∧
    BvaMatrixInv c F_cur s (best_k.toNat + 1) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) s' m',
      FullDenseInv c F0 s' → s.core.cur_vars ≤ s'.core.cur_vars → s'.core.fuel = s.core.fuel →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

@[expose]
def fullBvaTryLitHeapSpec : Spec [i64, i32, i64] [.bool] := fun (h, f0, _init_cv, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInv c F0 s ∧ f0.toNat < 2 * s.core.cur_vars ∧ (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) s' m',
      FullDenseInv c F0 s' → s.core.cur_vars ≤ s'.core.cur_vars → s'.core.fuel = s.core.fuel →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

@[expose] def fullFactorHeapSpec : Spec [i64, i64] [i64] := fun (h, _budget, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullDenseInv c F0 s' → s.core.cur_vars ≤ s'.core.cur_vars → s'.core.fuel = s.core.fuel →
      r = 1#64 → (FullMem c s' ⋆ R) m' → Q (r, ()) m'


open FullBvaHeapTactics FullBvaHeapHelpers
open scoped FullArenaTactics FullBvaHeapTactics

/-! ## 1. Pure Bit-Mask & Exact-Restoration Helpers -/

namespace FullBvaHeapScanHelpers

theorem bv32_garb_zero_of_and_580000 {x : BitVec 32} (h : (x &&& 0x00580000#32) = 0#32) :
    (x &&& 0x00080000#32) = 0#32 := by
  have h1 := congrArg (· &&& 0x00080000#32) h
  rw [BitVec.and_assoc, show (0x00580000#32 &&& 0x00080000#32) = 0x00080000#32 from rfl,
    BitVec.zero_and] at h1
  exact h1

theorem bv32_viv_zero_of_and_580000 {x : BitVec 32} (h : (x &&& 0x00580000#32) = 0#32) :
    (x &&& 0x00100000#32) = 0#32 := by
  have h1 := congrArg (· &&& 0x00100000#32) h
  rw [BitVec.and_assoc, show (0x00580000#32 &&& 0x00100000#32) = 0x00100000#32 from rfl,
    BitVec.zero_and] at h1
  exact h1

theorem bv8_bit_zero_of_and_fe {x : BitVec 8} (h : (x &&& 0xFE#8) = 0#8) :
    (x &&& 2#8) = 0#8 ∧ (x &&& 4#8) = 0#8 := by
  constructor
  · have h1 := congrArg (· &&& 2#8) h
    rw [BitVec.and_assoc, show (0xFE#8 &&& 2#8) = 2#8 from rfl, BitVec.zero_and] at h1; exact h1
  · have h1 := congrArg (· &&& 4#8) h
    rw [BitVec.and_assoc, show (0xFE#8 &&& 4#8) = 4#8 from rfl, BitVec.zero_and] at h1; exact h1

theorem bv8_clear_bit1_of_zero {x : BitVec 8} (hx : (x &&& 2#8) = 0#8) :
    (x &&& 0xFD#8) = x := by
  have h1 : x = x &&& (0xFD#8 ||| 2#8) := by
    rw [show (0xFD#8 ||| 2#8) = BitVec.allOnes 8 from rfl, BitVec.and_allOnes]
  conv => rhs; rw [h1, BitVec.and_or_distrib_left, hx, BitVec.or_zero]

theorem bv8_clear_bit2_of_zero {x : BitVec 8} (hx : (x &&& 4#8) = 0#8) :
    (x &&& 0xFB#8) = x := by
  have h1 : x = x &&& (0xFB#8 ||| 4#8) := by
    rw [show (0xFB#8 ||| 4#8) = BitVec.allOnes 8 from rfl, BitVec.and_allOnes]
  conv => rhs; rw [h1, BitVec.and_or_distrib_left, hx, BitVec.or_zero]

theorem bv8_clear_bit1_eq_of_or2 {x y : BitVec 8} (hx : (x &&& 2#8) = 0#8)
    (hy : y = x ∨ y = (x ||| 2#8)) : (y &&& 0xFD#8) = x := by
  rcases hy with rfl | rfl
  · exact bv8_clear_bit1_of_zero hx
  · rw [BitVec.and_or_distrib_right, show (2#8 &&& 0xFD#8) = 0#8 from rfl, BitVec.or_zero]
    exact bv8_clear_bit1_of_zero hx

theorem bv8_clear_bit2_eq_of_or4 {x y : BitVec 8} (hx : (x &&& 4#8) = 0#8)
    (hy : y = x ∨ y = (x ||| 4#8)) : (y &&& 0xFB#8) = x := by
  rcases hy with rfl | rfl
  · exact bv8_clear_bit2_of_zero hx
  · rw [BitVec.and_or_distrib_right, show (4#8 &&& 0xFB#8) = 0#8 from rfl, BitVec.or_zero]
    exact bv8_clear_bit2_of_zero hx

theorem bv8_or2_and_bit2 (x : BitVec 8) : ((x ||| 2#8) &&& 4#8) = (x &&& 4#8) := by
  rw [BitVec.and_or_distrib_right, show (2#8 &&& 4#8) = 0#8 from rfl, BitVec.or_zero]

theorem bv8_or2_and_bit0 (x : BitVec 8) : ((x ||| 2#8) &&& 1#8) = (x &&& 1#8) := by
  rw [BitVec.and_or_distrib_right, show (2#8 &&& 1#8) = 0#8 from rfl, BitVec.or_zero]

theorem bv8_or4_and_bit1 (x : BitVec 8) : ((x ||| 4#8) &&& 2#8) = (x &&& 2#8) := by
  rw [BitVec.and_or_distrib_right, show (4#8 &&& 2#8) = 0#8 from rfl, BitVec.or_zero]

theorem bv8_or2_idem (x : BitVec 8) : ((x ||| 2#8) ||| 2#8) = (x ||| 2#8) := by
  rw [BitVec.or_assoc, show (2#8 ||| 2#8) = 2#8 from rfl]

theorem bv8_or4_idem (x : BitVec 8) : ((x ||| 4#8) ||| 4#8) = (x ||| 4#8) := by
  rw [BitVec.or_assoc, show (4#8 ||| 4#8) = 4#8 from rfl]

theorem bv32_clear_viv_of_zero {x : BitVec 32} (hx : (x &&& 0x00100000#32) = 0#32) :
    (x &&& ~~~0x00100000#32) = x := by
  have h1 : x = x &&& (~~~0x00100000#32 ||| 0x00100000#32) := by
    rw [show (~~~0x00100000#32 ||| 0x00100000#32) = BitVec.allOnes 32 from rfl, BitVec.and_allOnes]
  conv => rhs; rw [h1, BitVec.and_or_distrib_left, hx, BitVec.or_zero]

theorem bv32_clear_viv_eq_of_or {x y : BitVec 32} (hx : (x &&& 0x00100000#32) = 0#32)
    (hy : y = x ∨ y = (x ||| 0x00100000#32)) : (y &&& ~~~0x00100000#32) = x := by
  rcases hy with rfl | rfl
  · exact bv32_clear_viv_of_zero hx
  · exact bv32_viv_roundtrip hx

theorem bv32_or_viv_idem (x : BitVec 32) :
    ((x ||| 0x00100000#32) ||| 0x00100000#32) = (x ||| 0x00100000#32) := by
  rw [BitVec.or_assoc, show (0x00100000#32 ||| 0x00100000#32) = 0x00100000#32 from rfl]

theorem bv32_and_not_viv_eq (x : BitVec 32) :
    (x &&& (0x00100000#32 ^^^ 0xFFFFFFFF#32)) = (x &&& ~~~0x00100000#32) := rfl

theorem list_eq_of_getElem?_eq {α : Type _} {xs ys : List α} (hlen : xs.length = ys.length)
    (h : ∀ i < ys.length, xs[i]? = ys[i]?) : xs = ys := by
  apply List.ext_getElem?; intro i
  by_cases hi : i < ys.length
  · exact h i hi
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-- Preserve `FullArenaVarsNodup` across bit-20 (`PH_VIV`) header updates. -/
theorem fullArenaVarsNodup_of_bit20 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {cref : Nat} {v : BitVec 32} (hlen : s.core.LengthsOk c)
    (hw : FullWitnessInv c F0 F_cur s.core) (hl0 : s.core.cur_level = 0)
    (hnodup : FullArenaVarsNodup s) (href : cref ∈ fullArenaClauseRefsCore s.core)
    (h19 : (v &&& 0x00080000#32) = (fullArenaHdrCore s.core cref &&& 0x00080000#32))
    (h23 : (v &&& 0x00800000#32) = (fullArenaHdrCore s.core cref &&& 0x00800000#32)) :
    FullArenaVarsNodup { s with core := { s.core with arena := s.core.arena.set cref v } } := by
  have ⟨_, hrefs, _, hall⟩ := fullWitnessInv_set_hdr_bit20 hlen hw hl0 href v h19 h23
  intro r hr hng
  change r ∈ fullArenaClauseRefsCore { s.core with arena := s.core.arena.set cref v } at hr
  rw [hrefs] at hr
  have ⟨hgb, _, hlts⟩ := hall r hr
  change fullArenaClauseGarbCore { s.core with arena := s.core.arena.set cref v } r = false at hng
  rw [hgb] at hng
  change ((fullArenaClauseLitsCore { s.core with arena := s.core.arena.set cref v } r).map
    (· / 2)).Nodup
  rw [hlts]; exact hnodup r hr hng

theorem fullArenaClauseLitsCore_congr {k1 k2 : FullCoreState} {r : Nat}
    (hsz : fullArenaClauseSizeCore k2 r = fullArenaClauseSizeCore k1 r)
    (hlits : ∀ j < fullArenaClauseSizeCore k1 r, k2.arena[r + 3 + j]? = k1.arena[r + 3 + j]?) :
    fullArenaClauseLitsCore k2 r = fullArenaClauseLitsCore k1 r := by
  unfold fullArenaClauseLitsCore; rw [hsz]
  apply congrArg (List.map BitVec.toNat)
  apply List.ext_getElem?; intro j
  by_cases hj : j < fullArenaClauseSizeCore k1 r
  · simp only [List.getElem?_take_of_lt hj, List.getElem?_drop]; exact hlits j hj
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]

/-- Zero-AST-duplication HOAS `Expr` slicers for factoring inner loop `wp` sub-theorems. -/
@[expose] def eLet64 {rs : List Ty} (v : Val i64) : Expr Val Cont rs → Expr Val Cont rs
  | .let_ (ts := [.bits 64]) _ k => k (v, ()) | _ => .hlt

@[expose] def eLet32 {rs : List Ty} (v : Val i32) : Expr Val Cont rs → Expr Val Cont rs
  | .let_ (ts := [.bits 32]) _ k => k (v, ()) | _ => .hlt

@[expose] def eLetBool {rs : List Ty} (v : Val .bool) : Expr Val Cont rs → Expr Val Cont rs
  | .let_ (ts := [.bool]) _ k => k (v, ()) | _ => .hlt

@[expose] def eLoad64 {rs : List Ty} (v : Val i64) : Expr Val Cont rs → Expr Val Cont rs
  | .load (.bits 64) _ k => k v | _ => .hlt

@[expose] def eLoad32 {rs : List Ty} (v : Val i32) : Expr Val Cont rs → Expr Val Cont rs
  | .load (.bits 32) _ k => k v | _ => .hlt

@[expose] def eThen {rs : List Ty} : Expr Val Cont rs → Expr Val Cont rs
  | .jnz _ t _ => t | _ => .hlt

@[expose] def eElse {rs : List Ty} : Expr Val Cont rs → Expr Val Cont rs
  | .jnz _ _ e => e | _ => .hlt

@[expose] def eGrp0_3 {rs : List Ty} (J : Cont [i32, i32, i32]) (xs : Tup Val [i32, i32, i32]) :
    Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32, .bits 32, .bits 32]]) bs _ =>
    match bs (J, ()) with | .cons f .nil => f xs
  | _ => .hlt

@[expose]
def eGrp0_4 {rs : List Ty} (J : Cont [i32, i32, i32, i32]) (xs : Tup Val [i32, i32, i32, i32]) :
    Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32, .bits 32, .bits 32, .bits 32]]) bs _ =>
    match bs (J, ()) with | .cons f .nil => f xs
  | _ => .hlt

@[expose] def eGrpBody_2 {rs : List Ty} (J : Cont [i32, i32]) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32, .bits 32]]) _ body => body (J, ()) | _ => .hlt

@[expose]
def eGrpBody_3 {rs : List Ty} (J : Cont [i32, i32, i32]) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32, .bits 32, .bits 32]]) _ body => body (J, ()) | _ => .hlt

@[expose]
def eGrpBody_mp {rs : List Ty} (J : Cont [i32, i32, i64, i32]) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32, .bits 32, .bits 64, .bits 32]]) _ body => body (J, ()) | _ => .hlt

@[expose]
def eGrp0_mp {rs : List Ty} (J : Cont [i32, i32, i64, i32]) (xs : Tup Val [i32, i32, i64, i32]) :
    Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32, .bits 32, .bits 64, .bits 32]]) bs _ =>
    match bs (J, ()) with | .cons f .nil => f xs
  | _ => .hlt

@[expose]
def eGrp0_dj {rs : List Ty} (J : Cont [i32, .bool, i32]) (xs : Tup Val [i32, .bool, i32]) :
    Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32, .bool, .bits 32]]) bs _ =>
    match bs (J, ()) with | .cons f .nil => f xs
  | _ => .hlt

@[expose] def eSkip {rs : List Ty} : Nat → Expr Val Cont rs → Expr Val Cont rs
  | 0, e => e
  | n + 1, .let_ (ts := [.bits 64]) _ k => eSkip n (k (0#64, ()))
  | n + 1, .let_ (ts := [.bits 32]) _ k => eSkip n (k (0#32, ()))
  | n + 1, .let_ (ts := [.bool]) _ k => eSkip n (k (true, ()))
  | n + 1, .load (.bits 64) _ k => eSkip n (k 0#64)
  | n + 1, .load (.bits 32) _ k => eSkip n (k 0#32)
  | _, e => e

end FullBvaHeapScanHelpers

open FullBvaHeapScanHelpers

theorem bv8_trunc_and_w (x y : BitVec 8) :
    BitVec.setWidth 8 (BitVec.setWidth 32 x &&& BitVec.setWidth 32 y) = x &&& y := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and]
  have hx := x.isLt; have hy := y.isLt
  rw [Nat.mod_eq_of_lt (Nat.lt_trans hx (by decide)),
    Nat.mod_eq_of_lt (Nat.lt_trans hy (by decide)),
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left hx)]

theorem bv8_trunc_or_w (x y : BitVec 8) :
    BitVec.setWidth 8 (BitVec.setWidth 32 x ||| BitVec.setWidth 32 y) = x ||| y := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_or]
  have hx := x.isLt; have hy := y.isLt
  rw [Nat.mod_eq_of_lt (Nat.lt_trans hx (by decide)),
    Nat.mod_eq_of_lt (Nat.lt_trans hy (by decide)),
    Nat.mod_eq_of_lt (Nat.or_lt_two_pow (n := 8) hx hy)]

theorem bv8_trunc_and_fb (x : BitVec 8) :
    BitVec.setWidth 8 (BitVec.setWidth 32 x &&&
      BitVec.ofNat (OfNat.ofNat 32) (OfNat.ofNat 251)) = x &&& 0xFB#8 :=
  bv8_trunc_and_w x 0xFB#8

theorem bv8_trunc_and_fd (x : BitVec 8) :
    BitVec.setWidth 8 (BitVec.setWidth 32 x &&&
      BitVec.ofNat (OfNat.ofNat 32) (OfNat.ofNat 253)) = x &&& 0xFD#8 :=
  bv8_trunc_and_w x 0xFD#8

theorem bv8_trunc_or_2 (x : BitVec 8) :
    BitVec.setWidth 8 (BitVec.setWidth 32 x |||
      BitVec.ofNat (OfNat.ofNat 32) (OfNat.ofNat 2)) = x ||| 2#8 :=
  bv8_trunc_or_w x 2#8

theorem bv8_trunc_or_4 (x : BitVec 8) :
    BitVec.setWidth 8 (BitVec.setWidth 32 x |||
      BitVec.ofNat (OfNat.ofNat 32) (OfNat.ofNat 4)) = x ||| 4#8 :=
  bv8_trunc_or_w x 4#8

theorem fullWitnessInv_with_litMark {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (h : FullWitnessInv c F0 F_cur k)
    (lm : List (BitVec 8)) : FullWitnessInv c F0 F_cur { k with lit_mark := lm } :=
  { h with arena := { h.arena with len_ok := h.arena.len_ok }
           watches := h.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }


theorem arViv_congr {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hcl : s.core.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    {ar : List (BitVec 32)}
    (hpt : ∀ i < c.arena_cap, ar[i]? = s.core.arena[i]? ∨
      (i ∈ fullArenaClauseRefsCore s.core ∧
        ar[i]? = some (s.core.arena[i]?.getD 0#32 ||| 0x00100000#32))) :
    fullArenaClauseRefsCore { s.core with arena := ar } = fullArenaClauseRefsCore s.core ∧
    (∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseGarbCore { s.core with arena := ar } r = fullArenaClauseGarbCore s.core r ∧
      fullArenaClauseSizeCore { s.core with arena := ar } r = fullArenaClauseSizeCore s.core r ∧
      fullArenaClauseLitsCore { s.core with arena := ar } r =
        fullArenaClauseLitsCore s.core r) := by
  have hal_le := hcl.arena_len_le
  have hgt_eq : ∀ r ∈ fullArenaClauseRefsCore s.core, ∀ i,
      r < i → i < fullArenaNextOff s.core.arena s.core.arena_len r →
      ar[i]? = s.core.arena[i]? := by
    intro r hr i hgt hlt
    have hwf := hw.arena.refs_wf r hr
    rcases hpt i (by omega) with heq | ⟨hi_ref, _⟩
    · exact heq
    · exfalso; have := fullArenaScanRefs_disjoint hr hi_ref hgt; omega
  have hnxt : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaNextOff ar s.core.arena_len r =
      fullArenaNextOff s.core.arena s.core.arena_len r := by
    intro r hr
    have hwf := hw.arena.refs_wf r hr
    have h2eq : ar[r + 2]? = s.core.arena[r + 2]? := hgt_eq r hr (r + 2) (by omega) (by omega)
    rcases hpt r (by omega) with heq | ⟨_, hset_r⟩
    · exact fullArenaNextOff_congr_block heq h2eq fun i hi1 hi2 => hgt_eq r hr i (by omega) hi2
    · have h1 : ¬ (r + 3 > s.core.arena_len) := by omega
      have h2 : ¬ (r + 3 + (s.core.arena[r + 2]?.getD 0#32).toNat > s.core.arena_len) := by
        unfold fullArenaClauseSizeCore at hwf; omega
      unfold fullArenaNextOff
      simp only [h1, ↓reduceIte, h2eq, h2, hset_r, Option.getD_some, bv32_or_viv_shrk]
      split
      · rename_i hshrk
        have hnxt_eq : fullArenaNextOff s.core.arena s.core.arena_len r =
            fullArenaSkipShrk s.core.arena s.core.arena_len
              (r + 3 + (s.core.arena[r + 2]?.getD 0#32).toNat)
              (s.core.arena_len - (r + 3 + (s.core.arena[r + 2]?.getD 0#32).toNat)) := by
          unfold fullArenaNextOff; simp only [h1, ↓reduceIte, h2]; rw [ite_eq_left hshrk]
        exact fullArenaSkipShrk_congr fun i hi1 hi2 =>
          hgt_eq r hr i (by omega) (by rw [hnxt_eq]; exact hi2)
      · rfl
  refine ⟨fullArenaClauseRefsCore_congr rfl hnxt, fun r hr => ?_⟩
  have hwf := hw.arena.refs_wf r hr
  have h2eq : ar[r + 2]? = s.core.arena[r + 2]? := hgt_eq r hr (r + 2) (by omega) (by omega)
  have hsz : fullArenaClauseSizeCore { s.core with arena := ar } r =
      fullArenaClauseSizeCore s.core r := by unfold fullArenaClauseSizeCore; rw [h2eq]
  refine ⟨?_, hsz, ?_⟩
  · unfold fullArenaClauseGarbCore fullArenaHdrCore
    rcases hpt r (by omega) with heq | ⟨_, hset_r⟩
    · rw [heq]
    · rw [hset_r, Option.getD_some, bv32_or_viv_garb]
  · exact fullArenaClauseLitsCore_congr hsz fun j hj =>
      hgt_eq r hr (r + 3 + j) (by omega) (by omega)


/-- Bit-2 `lit_mark` restoration invariant over literals `ar[qw + 3 + lo ..< qw + 3 + hi)`. -/
@[expose] def LmBit2Inv (c : FullCfg) (ar : List (BitVec 32)) (lm0 : List (BitVec 8))
    (qw lo hi : Nat) (lm : List (BitVec 8)) : Prop :=
  lm.length = 2 * c.max_vars ∧
  ∀ l < 2 * c.max_vars, lm[l]? = lm0[l]? ∨
    (∃ k, lo ≤ k ∧ k < hi ∧ (ar[qw + 3 + k]?.getD 0#32).toNat = l ∧
      lm[l]? = some (lm0[l]?.getD 0#8 ||| 2#8))

theorem lmBit2Inv_init {c : FullCfg} {ar : List (BitVec 32)} {lm0 : List (BitVec 8)}
    {qw : Nat} (hlm0 : lm0.length = 2 * c.max_vars) : LmBit2Inv c ar lm0 qw 0 0 lm0 :=
  ⟨hlm0, fun _ _ => Or.inl rfl⟩

theorem lmBit2Inv_skip {c : FullCfg} {ar : List (BitVec 32)} {lm0 lm : List (BitVec 8)}
    {qw j : Nat} (h : LmBit2Inv c ar lm0 qw 0 j lm) : LmBit2Inv c ar lm0 qw 0 (j + 1) lm :=
  ⟨h.1, fun l hl => by
    rcases h.2 l hl with heq | ⟨k, h0, hk, har, hset⟩
    · exact Or.inl heq
    · exact Or.inr ⟨k, h0, by omega, har, hset⟩⟩

theorem lmBit2Inv_or2 {c : FullCfg} {ar : List (BitVec 32)} {lm0 lm : List (BitVec 8)}
    {qw j : Nat} (_hlm0 : lm0.length = 2 * c.max_vars) (h : LmBit2Inv c ar lm0 qw 0 j lm)
    (hj_ar : qw + 3 + j < ar.length)
    (hl_lt : (ar[qw + 3 + j]'hj_ar).toNat < 2 * c.max_vars) :
    let l := (ar[qw + 3 + j]'hj_ar).toNat
    LmBit2Inv c ar lm0 qw 0 (j + 1) (lm.set l ((lm[l]'(by rw [h.1]; exact hl_lt)) ||| 2#8)) := by
  obtain ⟨hlm, hall⟩ := h
  intro l
  refine ⟨by simp [hlm], fun i hi => ?_⟩
  by_cases hil : i = l
  · subst hil
    refine Or.inr ⟨j, Nat.zero_le _, by omega,
      by rw [List.getElem?_eq_getElem hj_ar, Option.getD_some], ?_⟩
    rw [List.getElem?_set_self (by omega)]
    rcases hall l hl_lt with heq | ⟨_, _, _, _, hset⟩
    · have : lm[l]'(by omega) = lm0[l]?.getD 0#8 := by
        rw [← heq, List.getElem?_eq_getElem (by omega), Option.getD_some]
      rw [this]
    · rw [List.getElem?_eq_getElem (by omega)] at hset
      rw [Option.some.inj hset, bv8_or2_idem]
  · rw [List.getElem?_set_ne (Ne.symm hil)]
    rcases hall i hi with heq | ⟨k, h0, hk, har, hset⟩
    · exact Or.inl heq
    · exact Or.inr ⟨k, h0, by omega, har, hset⟩

theorem lmBit2Inv_clear_step {c : FullCfg} {ar : List (BitVec 32)}
    {lm0 lm : List (BitVec 8)}
    {qw j csz : Nat} (hlm0 : lm0.length = 2 * c.max_vars)
    (hlm0_b1 : ∀ l < 2 * c.max_vars, (lm0[l]?.getD 0#8 &&& 2#8) = 0#8)
    (h : LmBit2Inv c ar lm0 qw j csz lm) (hj : j < csz) (hj_ar : qw + 3 + j < ar.length)
    (hl_lt : (ar[qw + 3 + j]'hj_ar).toNat < 2 * c.max_vars) :
    let cj := (ar[qw + 3 + j]'hj_ar).toNat
    LmBit2Inv c ar lm0 qw (j + 1) csz
      (lm.set cj ((lm[cj]'(by rw [h.1]; exact hl_lt)) &&& 0xFD#8)) := by
  obtain ⟨hlm, hall⟩ := h
  intro cj
  have hcj_eq : (ar[qw + 3 + j]?.getD 0#32).toNat = cj := by
    rw [List.getElem?_eq_getElem hj_ar, Option.getD_some]
  have hclr : ((lm[cj]'(by omega)) &&& 0xFD#8) = lm0[cj]?.getD 0#8 := by
    apply bv8_clear_bit1_eq_of_or2 (hlm0_b1 cj hl_lt)
    rcases hall cj hl_lt with heq | ⟨_, _, _, _, hset⟩
    · left; rw [← heq, List.getElem?_eq_getElem (by omega), Option.getD_some]
    · right; rw [List.getElem?_eq_getElem (by omega)] at hset; exact Option.some.inj hset
  refine ⟨by simp [hlm], fun i hi => ?_⟩
  by_cases hic : i = cj
  · subst hic; left
    rw [List.getElem?_set_self (by omega), hclr,
      List.getElem?_eq_getElem (by omega), Option.getD_some]
  · rw [List.getElem?_set_ne (Ne.symm hic)]
    rcases hall i hi with heq | ⟨k, hk1, hk2, har, hset⟩
    · exact Or.inl heq
    · have hkne : k ≠ j := fun h => by subst h; rw [hcj_eq] at har; exact hic har.symm
      exact Or.inr ⟨k, by omega, hk2, har, hset⟩

theorem lmBit2Inv_done {c : FullCfg} {ar : List (BitVec 32)} {lm0 lm : List (BitVec 8)}
    {qw csz : Nat} (hlm0 : lm0.length = 2 * c.max_vars)
    (h : LmBit2Inv c ar lm0 qw csz csz lm) : lm = lm0 := by
  apply list_eq_of_getElem?_eq (by rw [h.1, hlm0])
  intro i hi
  rcases h.2 i (by omega) with heq | ⟨k, hk1, hk2, _⟩
  · exact heq
  · omega

theorem lmBit2Inv_preserves_bit0 {c : FullCfg} {ar : List (BitVec 32)}
    {lm0 lm : List (BitVec 8)} {qw lo hi : Nat} (h : LmBit2Inv c ar lm0 qw lo hi lm)
    {l : Nat} (hl : l < 2 * c.max_vars) :
    (lm[l]?.getD 0#8 &&& 1#8) = (lm0[l]?.getD 0#8 &&& 1#8) := by
  rcases h.2 l hl with heq | ⟨_, _, _, _, hset⟩
  · rw [heq]
  · rw [hset, Option.getD_some, bv8_or2_and_bit0]

theorem lmBit2Inv_preserves_bit2 {c : FullCfg} {ar : List (BitVec 32)}
    {lm0 lm : List (BitVec 8)} {qw lo hi : Nat} (h : LmBit2Inv c ar lm0 qw lo hi lm)
    {l : Nat} (hl : l < 2 * c.max_vars) :
    (lm[l]?.getD 0#8 &&& 4#8) = (lm0[l]?.getD 0#8 &&& 4#8) := by
  rcases h.2 l hl with heq | ⟨_, _, _, _, hset⟩
  · rw [heq]
  · rw [hset, Option.getD_some, bv8_or2_and_bit2]

theorem fullDenseInvW_set_flags {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {fl' : List (BitVec 32)} (hfl : fl'.length = c.max_vars) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with flags := fl' } } :=
  fullDenseInv_with_core_aux (tc' := s.core.tmp_cnt) (tl' := s.core.tmp_len) (sc' := s.scratch)
    hinv hinv.1.core_ok.repr_len hinv.1.core_ok.min_clr_len_arr hinv.1.core_ok.tmp_len_arr
    hfl hinv.1.core_ok.tmp_len_le hinv.1.scratch_ok rfl rfl

end LeanQbe.T.Examples.Kissat.FullBvaHeap
