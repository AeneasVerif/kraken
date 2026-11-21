module

public import LeanQbe.T.Examples.Kissat.FullBvaHeap
public import LeanQbe.T.Examples.Kissat.FullBvaFwdLemmas2
public import LeanQbe.T.Logic.C0HeadStep
public import LeanQbe.T.Logic.ControlComb
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` 3-Hop BVA & Heap Factoring Proofs — Part 1 (`Foundations, FreshVar, 3-Hop, FHeap`)

Provides:
1. Scoped `FullBvaHeapTactics`: `i64` load/store view over `FullCoreState.repr` (`u32[2 * max_vars]`
   = `u64[max_vars]`), index-0 and immediate-offset `FullMem` accessors, and bitvector helpers.
2. Pure generalized BVA UNSAT soundness (`bvaExtendGen`, `extUnsatSound_bvaExtendGen`,
   `fullDenseInv_add_fresh_var_gen`), `PH_VIV` header-bit preservation, and the `Nodup` pigeonhole
   clause-matching theorem (`bva_match_large_entails`).
3. Canonical specs for all `13` functions of `FullBvaHeap`.
4. Parametric `(Γ : Env)` `Func.wp` proofs for:
   - `full_init_fresh_var` (`full_init_fresh_var_heap_wp` + canonical `full_init_fresh_var_wp`
     matching `Full.fullInitFreshVarSpec` directly)
   - `full_bva_hop1`, `full_bva_hop2`, `full_bva_hop3`
   - `full_fheap_up`, `full_fheap_down`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullBvaHeap

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

/-! ## 1. `i64` Reinterpretation over `repr` & Scoped Tactics (`FullBvaHeapTactics`) -/

def pack64 (lo hi : BitVec 32) : BitVec 64 :=
  lo.setWidth 64 ||| (hi.setWidth 64 <<< 32)

def repr64Get (r : List (BitVec 32)) (i : Nat) : BitVec 64 :=
  pack64 (r[2 * i]?.getD 0#32) (r[2 * i + 1]?.getD 0#32)

def repr64Set (r : List (BitVec 32)) (i : Nat) (v : BitVec 64) : List (BitVec 32) :=
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
def bvaExtendGen (fv : Nat) (L : List Nat) (Qs : List (List Nat))
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
def FullDenseInvNoLm (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
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
def fullInitFreshVarHeapSpec : Spec [i64, i32] [] := fun (h, fv, ()) m Q _ =>
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

def fullBvaHop3Spec : Spec [i64, i32, i32] [i64] := fun (h, src_lit, _dst_idx, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvNoLm c F0 F_cur s ∧ src_lit.toNat < 2 * s.core.cur_vars ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (r : BitVec 64) repr' mclr' ant' sig' shrk' m',
      let s' : FullState :=
        { core := { s.core with repr := repr', min_clr := mclr', tmp_cnt := 0, tmp_len := 0 }
          scratch := { s.scratch with ant_sz := ant', sim_sig := sig', shrink_stk := shrk' } }
      FullDenseInvNoLm c F0 F_cur s' → (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullFheapUpSpec : Spec [i64, i64, i64, i32] [] :=
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

def fullFheapDownSpec : Spec [i64, i64, i64, i32, i32] [] :=
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
def BvaRowEntryOk (F_cur : List (List Nat)) (s : FullState) (fr : Nat) (w : BitVec 32)
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

def fullBvaMatchLargeSpec : Spec [i64, i32, i32, i32] [.bool] :=
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

def fullBvaScanCandsSpec : Spec [i64, i32, i32, i64] [i32] :=
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

def fullBvaPickCandSpec : Spec [i64, i32, i32] [i32] :=
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

def fullBvaFilterRowSpec : Spec [i64, i32, i32, i32, i32, i32] [i32] :=
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

def fullBvaCommitSpec : Spec [i64, i32] [.bool] := fun (h, best_k, ()) m Q _ =>
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

def fullBvaTryLitHeapSpec : Spec [i64, i32, i64] [.bool] := fun (h, f0, _init_cv, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInv c F0 s ∧ f0.toNat < 2 * s.core.cur_vars ∧ (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) s' m',
      FullDenseInv c F0 s' → s.core.cur_vars ≤ s'.core.cur_vars → s'.core.fuel = s.core.fuel →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

def fullFactorHeapSpec : Spec [i64, i64] [i64] := fun (h, _budget, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullDenseInv c F0 s' → s.core.cur_vars ≤ s'.core.cur_vars → s'.core.fuel = s.core.fuel →
      r = 1#64 → (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-! ## 4. `full_init_fresh_var_heap_wp` & Canonical `full_init_fresh_var_wp` -/

private theorem initFreshVar_post {c : FullCfg} {s s' : FullState} {fv : BitVec 32}
    {R : Mem 64 → Prop} {Q : Post []} {m' : Mem 64}
    (hfv_lt : fv.toNat < s.core.cur_vars) (hclen : s.core.LengthsOk c) (hlen' : s'.LengthsOk c)
    (hcv_le : s.core.cur_vars ≤ c.max_vars)
    (hcore : s'.core =
      { s.core with
        wvec := (((s.core.wvec.set (4 * fv.toNat) 0#32).set (4 * fv.toNat + 1) 0#32).set
          (4 * fv.toNat + 2) 0#32).set (4 * fv.toNat + 3) 0#32
        vals := (s.core.vals.set (2 * fv.toNat) 0#8).set (2 * fv.toNat + 1) 0#8
        mrk := s.core.mrk.set fv.toNat 0#8, lvl := s.core.lvl.set fv.toNat 0#32
        rsns := s.core.rsns.set fv.toNat 0xFFFFFFFF#32, flags := s.core.flags.set fv.toNat 1145#32
        unassigned := s.core.unassigned + 1#64 })
    (hext_pres : FullExtScratchPres s s')
    (hsb : s'.scratch.scratch_buf = s.scratch.scratch_buf)
    (hws : s'.scratch.wsort = s.scratch.wsort)
    (htm : s'.scratch.tarjan_mark = s.scratch.tarjan_mark)
    (htr : s'.scratch.tarjan_reach = s.scratch.tarjan_reach)
    (hss : s'.scratch.sim_sig = s.scratch.sim_sig)
    (hm' : (FullMem c s' ⋆ R) m')
    (hQ : ∀ vals' mrk' flags' lvl' rsns' wvec' unass' sc' m',
      let s1 : FullState :=
        { s with
          core := { s.core with vals := vals', mrk := mrk', flags := flags', lvl := lvl',
                                rsns := rsns', wvec := wvec', unassigned := unass' }
          scratch := sc' }
      s1.LengthsOk c → FullExtScratchPres s s1 →
      sc'.scratch_buf = s.scratch.scratch_buf → sc'.wsort = s.scratch.wsort →
      sc'.tarjan_mark = s.scratch.tarjan_mark → sc'.tarjan_reach = s.scratch.tarjan_reach →
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
      (FullMem c s1 ⋆ R) m' → Q () m') : Q () m' := by
  have hs'_eq : s' = { s with core := s'.core, scratch := s'.scratch } := by cases s'; rfl
  let vals' := (s.core.vals.set (2 * fv.toNat) 0#8).set (2 * fv.toNat + 1) 0#8
  let mrk' := s.core.mrk.set fv.toNat 0#8
  let flags' := s.core.flags.set fv.toNat 1145#32
  let lvl' := s.core.lvl.set fv.toNat 0#32
  let rsns' := s.core.rsns.set fv.toNat 0xFFFFFFFF#32
  let wvec' := (((s.core.wvec.set (4 * fv.toNat) 0#32).set (4 * fv.toNat + 1) 0#32).set
    (4 * fv.toNat + 2) 0#32).set (4 * fv.toNat + 3) 0#32
  let unass' := s.core.unassigned + 1#64
  refine hQ vals' mrk' flags' lvl' rsns' wvec' unass' s'.scratch m'
    (by rw [← hcore, ← hs'_eq]; exact hlen')
    hext_pres hsb hws htm htr hss ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (by rw [← hcore, ← hs'_eq]; exact hm')
  · dsimp only [vals']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by rw [hclen.vals_len]; omega)]
    rfl
  · dsimp only [vals']
    rw [List.getElem?_set_self (by simp [hclen.vals_len]; omega)]; rfl
  · intro l _ _
    dsimp only [vals']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  · dsimp only [mrk']; rw [List.getElem?_set_self (by rw [hclen.mrk_len]; omega)]; rfl
  · intro v _ hv; exact List.getElem?_set_ne (Ne.symm hv)
  · dsimp only [lvl']; rw [List.getElem?_set_self (by rw [hclen.lvl_len]; omega)]; rfl
  · intro v _ hv; exact List.getElem?_set_ne (Ne.symm hv)
  · dsimp only [rsns']; rw [List.getElem?_set_self (by rw [hclen.rsns_len]; omega)]; rfl
  · intro v _ hv; exact List.getElem?_set_ne (Ne.symm hv)
  · intro k hk; dsimp only [wvec']
    rcases k with _ | _ | _ | _ | k
    · rw [show 4 * fv.toNat + 0 = 4 * fv.toNat from rfl, List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_self (by simp [hclen.wvec_len]; omega)]; rfl
    · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_self (by simp [hclen.wvec_len]; omega)]; rfl
    · rw [List.getElem?_set_ne (by omega),
        List.getElem?_set_self (by simp [hclen.wvec_len]; omega)]; rfl
    · rw [List.getElem?_set_self (by simp [hclen.wvec_len]; omega)]; rfl
    · omega
  · intro i _ hi; dsimp only [wvec']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]

theorem full_init_fresh_var_heap_wp (Γ : Env) :
    ∀ args m Q X, fullInitFreshVarHeapSpec args m Q X →
      Func.wp Γ full_init_fresh_var_body args m Q X := by
  rintro ⟨h, fv, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hslen, hfv_lt, hm, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hclen := hslen.core_ok; have hsc := hslen.scratch_ok; have hcv_le := hclen.cur_vars_le
  have hwv_len := hclen.wvec_len; have hvals_len := hclen.vals_len; have hmrk_len := hclen.mrk_len
  have hlvl_len := hclen.lvl_len; have hrsns_len := hclen.rsns_len; have hfl_len := hclen.flags_len
  have hpos_len := hsc.pos_len; have hph_len := hsc.phases_len; have hqp_len := hsc.q_prev_len
  have hqn_len := hsc.q_next_len; have hqs_len := hsc.q_stamp_len; have hsc_len := hsc.score_len
  have hfv64 : (BitVec.setWidth 64 fv).toNat = fv.toNat := by c0_bound
  have hwb0 : (BitVec.setWidth 64 fv <<< (2 : Nat)).toNat = 4 * fv.toNat := by c0_bound
  have hwb1 : ((BitVec.setWidth 64 fv <<< (2 : Nat)) + 1).toNat = 4 * fv.toNat + 1 := by
    change ((BitVec.setWidth 64 fv <<< (2 : Nat)) + 1#64).toNat = _; c0_bound
  have hwb2 : ((BitVec.setWidth 64 fv <<< (2 : Nat)) + 2).toNat = 4 * fv.toNat + 2 := by
    change ((BitVec.setWidth 64 fv <<< (2 : Nat)) + 2#64).toNat = _; c0_bound
  have hwb3 : ((BitVec.setWidth 64 fv <<< (2 : Nat)) + 3).toNat = 4 * fv.toNat + 3 := by
    change ((BitVec.setWidth 64 fv <<< (2 : Nat)) + 3#64).toNat = _; c0_bound
  have hv2 : (BitVec.setWidth 64 fv <<< (1 : Nat)).toNat = 2 * fv.toNat := by c0_bound
  have hv2p1 : ((BitVec.setWidth 64 fv <<< (1 : Nat)) ||| 1).toNat = 2 * fv.toNat + 1 := by
    change ((BitVec.setWidth 64 fv <<< (1 : Nat)) ||| 1#64).toNat = _
    rw [FullBvaFwdTactics.bv64_or1_of_even (by rw [hv2]; omega), hv2]
  have hv2p1_lt : ((BitVec.setWidth 64 fv <<< (1 : Nat)) ||| 1).toNat < s.core.vals.length := by
    rw [hv2p1, hvals_len]; omega
  have hfl_or : (((((1 : BitVec 32) ||| 8) ||| 16) ||| 1024) ||| 32) ||| 64 = 1145#32 := by decide
  unfold Func.wp full_init_fresh_var_body; dsimp only
  open scoped FullBvaFwdTactics in bf_fast_nogrp
  refine wp_join_state0 (α := FullState)
    (fun sm mm =>
      (FullMem c sm ⋆ R) mm ∧ sm.LengthsOk c ∧
      sm.core =
        { s.core with
          wvec := (((s.core.wvec.set (4 * fv.toNat) 0#32).set (4 * fv.toNat + 1) 0#32).set
            (4 * fv.toNat + 2) 0#32).set (4 * fv.toNat + 3) 0#32
          vals := (s.core.vals.set (2 * fv.toNat) 0#8).set (2 * fv.toNat + 1) 0#8
          mrk := s.core.mrk.set fv.toNat 0#8, lvl := s.core.lvl.set fv.toNat 0#32
          rsns := s.core.rsns.set fv.toNat 0xFFFFFFFF#32
          flags := s.core.flags.set fv.toNat 1145#32 } ∧
      FullExtScratchPres s sm ∧ sm.scratch.scratch_buf = s.scratch.scratch_buf ∧
      sm.scratch.wsort = s.scratch.wsort ∧ sm.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
      sm.scratch.tarjan_reach = s.scratch.tarjan_reach ∧
      sm.scratch.sim_sig = s.scratch.sim_sig)
    (fun _ sm mm ⟨hmm, hlenm, hcorem, hextm, hsbm, hwsm, htmm, htrm, hssm⟩ => ?_)
    (fun Jm hJm => ?_)
  · clear hm
    have hqsm_len := hlenm.scratch_ok.q_stamp_len
    open scoped FullBvaFwdTactics in bf_fast
    refine initFreshVar_post hfv_lt hclen ?_ hcv_le ?_ ?_ ?_ ?_ ?_ ?_ ?_ hm hQ
    · exact ⟨{ hlenm.core_ok with }, { hlenm.scratch_ok with q_stamp_len := by simp [hqsm_len] }⟩
    · dsimp only; rw [hcorem]; rfl
    · exact ⟨hextm.1, hextm.2⟩
    · exact hsbm
    · exact hwsm
    · exact htmm
    · exact htrm
    · exact hssm
  · open scoped FullBvaFwdTactics in bf_fast
    all_goals
      refine hJm _ _ ⟨hm, ?_, ?_, ⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩
      · exact ⟨
          { hclen with
            wvec_len := by simp [hwv_len], vals_len := by simp [hvals_len],
            mrk_len := by simp [hmrk_len], lvl_len := by simp [hlvl_len],
            rsns_len := by simp [hrsns_len], flags_len := by simp [hfl_len] },
          { hsc with
            phases_len := by simp [hph_len], pos_len := by simp [hpos_len],
            score_len := by simp [hsc_len], q_prev_len := by simp [hqp_len],
            q_next_len := by simp [hqn_len] }⟩
      · dsimp only; rw [hfv64, hwb0, hwb1, hwb2, hwb3, hv2, hv2p1, hfl_or]; rfl

/-- Canonical `Full.fullInitFreshVarSpec` corollary (zero callee hypotheses required). -/
theorem full_init_fresh_var_wp (Γ : Env) :
    ∀ args m Q X, Full.fullInitFreshVarSpec args m Q X →
      Func.wp Γ full_init_fresh_var_body args m Q X := by
  rintro ⟨h, fv, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hslen, hfv_lt, hm, hQ⟩
  exact full_init_fresh_var_heap_wp Γ _ m Q X ⟨c, s, R, rfl, hslen, hfv_lt, hm,
    fun vals' mrk' flags' lvl' rsns' wvec' unass' sc' m' hlen' hext' hsb _ _ _ _
      hv0 hv1 hv_oth hm0 hm_oth hl0 hl_oth hr0 hr_oth hw0 hw_oth hm' =>
      hQ vals' mrk' flags' lvl' rsns' wvec' unass' sc' m' hlen' hext' hsb
        hv0 hv1 hv_oth hm0 hm_oth hl0 hl_oth hr0 hr_oth hw0 hw_oth hm'⟩

/-! ## 5. 3-Hop Structural Overlap Scorer (`full_bva_hop1`, `full_bva_hop2`, `full_bva_hop3`) -/

private theorem hop_wvec_bounds {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hinv : FullDenseInvNoLm c F0 F_cur s) {sl : Nat}
    (hsl : sl < 2 * s.core.cur_vars) :
    fullWatchOffCore s.core sl + fullWatchSizeCore s.core sl ≤ s.core.wlen ∧
    DenseWatchSliceOk F_cur s.core sl (fullWatchOffCore s.core sl)
      (fullWatchSizeCore s.core sl) := by
  have hdw : DenseWatchesInv F_cur s.core := by
    have h := hinv.2.1.watches; unfold ModeWatchesInv at h
    rwa [ite_eq_right hinv.2.2.2.2.2] at h
  exact ⟨hdw.layout.bounds sl hsl, hdw.slices sl hsl⟩

theorem full_bva_hop1_wp (Γ : Env) :
    ∀ args m Q X, fullBvaHop1Spec args m Q X → Func.wp Γ full_bva_hop1_body args m Q X := by
  rintro ⟨h, src_lit, dst_idx, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hinv, hsrc_lt, htc_le, hmclr_ok, hm, hQ⟩
  have hmx := c.hmaxv; have hwcap := c.hwcap; have har_b := c.harena
  unfold dimacsBound at hmx hwcap har_b
  have hcl := hinv.1.core_ok; have hsc := hinv.1.scratch_ok
  have hcv_le := hcl.cur_vars_le; have hrepr_len := hcl.repr_len
  have hwv_len := hcl.wvec_len; have hws_len := hcl.wstk_len_arr; have har_len := hcl.arena_len_arr
  have hwlen_le := hcl.wlen_le; have hal_le := hcl.arena_len_le
  have hmclr_len := hcl.min_clr_len_arr
  have hsidx_lt : (src_lit >>> 1).toNat < s.core.cur_vars := by
    rw [bv32_lshr1_nat]; omega
  c0_hsteps_nogrp
  · exact hQ _ s.core.repr s.core.min_clr s.core.tmp_cnt s.scratch.ant_sz m
      hinv htc_le hmclr_ok (Nat.le_refl _) hm
  · refine wp_join_state1 (t := i64) (α := BitVec 64) (fun r => r) (fun _ ml => m = ml)
      (fun _ res0 ml hml => ?_) (fun J0 hJ0 => ?_)
    · rcases hml with rfl
      c0_hsteps_nogrp
      refine wp_loop_inv
        (fun (res, sgn, ()) ml => ∃ ant : BitVec 64,
          sgn.toNat ≤ 2 ∧ ant.toNat ≤ s.scratch.ant_sz.toNat ∧
          (FullMem c { s with scratch := { s.scratch with ant_sz := ant } } ⋆ R) ml)
        (fun (_, sgn, _) _ => 2 - sgn.toNat)
        (fun Js hJs => by
          c0_hsteps; exact hJs (res0, 0#32, ()) m ⟨s.scratch.ant_sz, by decide, Nat.le_refl _, hm⟩)
        (fun Js (res, sgn, ()) ml ⟨ant, hsgn_le, hant_le, hml⟩ ihs => ?_)
      c0_hsteps_nogrp
      refine wp_join_state0 (α := BitVec 64)
        (fun antF mf => antF.toNat ≤ s.scratch.ant_sz.toNat ∧
          (FullMem c { s with scratch := { s.scratch with ant_sz := antF } } ⋆ R) mf)
        (fun _ antF mf ⟨hantF, hmf⟩ => ?_)
        (fun Jend hJend => ?_)
      · c0_hsteps_nogrp
        refine wp_join_state1 (t := i64) (α := BitVec 64) (fun r => r) (fun _ ml => mf = ml)
          (fun _ resC ml hml => ?_) (fun Jc hJc => ?_)
        · rcases hml with rfl
          c0_hsteps
          · have htc1 : s.core.tmp_cnt + 1 ≤ s.core.cur_vars := by c0_bound
            have hinv' : FullDenseInvNoLm c F0 F_cur
                { core := { s.core with
                    repr := repr64Set s.core.repr (src_lit >>> 1).toNat (resC + 1)
                    min_clr := s.core.min_clr.set s.core.tmp_cnt (src_lit >>> 1)
                    tmp_cnt := s.core.tmp_cnt + 1 }
                  scratch := { s.scratch with ant_sz := antF } } :=
              fullDenseInvNoLm_with_core_aux hinv (by rw [repr64Set_length, hrepr_len])
                (by simp [hmclr_len]) hcl.tmp_len_arr hcl.flags_len hcl.tmp_len_le
                { hsc with } rfl rfl
            have hm' : (FullMem c
                { core := { s.core with
                    repr := repr64Set s.core.repr (src_lit >>> 1).toNat (resC + 1)
                    min_clr := s.core.min_clr.set s.core.tmp_cnt (src_lit >>> 1)
                    tmp_cnt := s.core.tmp_cnt + 1 }
                  scratch := { s.scratch with ant_sz := antF } } ⋆ R) m := by
              have h1 : (BitVec.ofNat 64 s.core.tmp_cnt + 1).toNat = s.core.tmp_cnt + 1 := by
                change (BitVec.ofNat 64 s.core.tmp_cnt + 1#64).toNat = _; c0_bound
              have h2 : (BitVec.ofNat 64 s.core.tmp_cnt).toNat = s.core.tmp_cnt := by c0_bound
              have h3 : (BitVec.setWidth 64 (src_lit >>> 1)).toNat = (src_lit >>> 1).toNat := by
                c0_bound
              rw [h1, h2, h3] at hm; exact hm
            exact hQ _ _ _ (s.core.tmp_cnt + 1) antF m hinv' htc1 (fun i hi => by
              by_cases hie : i = s.core.tmp_cnt
              · subst hie; rw [List.getElem?_set_self (by omega), Option.getD_some]; omega
              · rw [List.getElem?_set_ne (Ne.symm hie)]; exact hmclr_ok i (by omega)) hantF hm'
          · have hinv' : FullDenseInvNoLm c F0 F_cur
                { core := { s.core with
                    repr := repr64Set s.core.repr (src_lit >>> 1).toNat (resC + 1) }
                  scratch := { s.scratch with ant_sz := antF } } :=
              fullDenseInvNoLm_with_core_aux hinv (by rw [repr64Set_length, hrepr_len])
                hmclr_len hcl.tmp_len_arr hcl.flags_len hcl.tmp_len_le { hsc with } rfl rfl
            have hm' : (FullMem c
                { core := { s.core with
                    repr := repr64Set s.core.repr (src_lit >>> 1).toNat (resC + 1) }
                  scratch := { s.scratch with ant_sz := antF } } ⋆ R) m := by
              have h3 : (BitVec.setWidth 64 (src_lit >>> 1)).toNat = (src_lit >>> 1).toNat := by
                c0_bound
              rw [h3] at hm; exact hm
            exact hQ _ _ _ s.core.tmp_cnt antF m hinv' htc_le hmclr_ok hantF hm'
        · c0_hsteps
          · exact hJc 0x3FFFFFFFFFFFFFFF#64 mf rfl
          · exact hJc res mf rfl
      · c0_hsteps
        · have hsgn_lt : sgn.toNat < 2 := by c0_bound
          have hsl_nat : (((src_lit >>> (1 : Nat)) <<< (1 : Nat)) ||| sgn).toNat =
              2 * (src_lit >>> (1 : Nat)).toNat + sgn.toNat := by
            have hs01 : sgn.toNat = 0 ∨ sgn.toNat = 1 := by omega
            rcases hs01 with h0 | h1
            · have hs0 : sgn = 0#32 := BitVec.eq_of_toNat_eq h0; subst hs0
              rw [BitVec.or_zero]; c0_bound
            · have hs1 : sgn = 1#32 := BitVec.eq_of_toNat_eq h1; subst hs1
              rw [FullBvaFwdTactics.bv32_or1_of_even (by c0_bound)]; c0_bound
          have hsl_lt : (((src_lit >>> (1 : Nat)) <<< (1 : Nat)) ||| sgn).toNat <
              2 * s.core.cur_vars := by omega
          obtain ⟨hbd_sl, hslice_sl⟩ := hop_wvec_bounds hinv hsl_lt
          let sl : BitVec 32 := ((src_lit >>> (1 : Nat)) <<< (1 : Nat)) ||| sgn
          have hsl_lt_sl : sl.toNat < 2 * s.core.cur_vars := hsl_lt
          have hwv_sl0 : (BitVec.setWidth 64 sl <<< (1 : Nat)).toNat < s.core.wvec.length := by
            c0_bound
          have hwv_sl1 : ((BitVec.setWidth 64 sl <<< (1 : Nat)) + 1).toNat <
              s.core.wvec.length := by
            change ((BitVec.setWidth 64 sl <<< (1 : Nat)) + 1#64).toNat < _; c0_bound
          have hoff_eq : (s.core.wvec[2 * sl.toNat]'(by omega)).toNat =
              fullWatchOffCore s.core sl.toNat := by
            unfold fullWatchOffCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          have hsz_eq : (s.core.wvec[2 * sl.toNat + 1]'(by omega)).toNat =
              fullWatchSizeCore s.core sl.toNat := by
            unfold fullWatchSizeCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          let off0 := fullWatchOffCore s.core sl.toNat
          let sz0 := fullWatchSizeCore s.core sl.toNat
          have hoff_sz_le : off0 + sz0 ≤ s.core.wlen := hbd_sl
          have h2sl0 : (BitVec.setWidth 64 sl <<< (1 : Nat)).toNat = 2 * sl.toNat := by c0_bound
          have h2sl1 : ((BitVec.setWidth 64 sl <<< (1 : Nat)) + 1).toNat = 2 * sl.toNat + 1 := by
            change ((BitVec.setWidth 64 sl <<< (1 : Nat)) + 1#64).toNat = _; c0_bound
          have hoff_c0 : (BitVec.setWidth 64
              (s.core.wvec[(BitVec.setWidth 64 sl <<< (1 : Nat)).toNat]'hwv_sl0)).toNat = off0 := by
            rw [bv64_setWidth_32]; simp only [h2sl0]; exact hoff_eq
          have hmod0 : 2 * sl.toNat % 2 ^ 64 = 2 * sl.toNat := Nat.mod_eq_of_lt (by omega)
          have hmod1 : (2 * sl.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = 2 * sl.toNat + 1 :=
            by c0_bound
          have hend_mod : ((s.core.wvec[2 * sl.toNat % 2 ^ 64]'(by rw [hmod0]; omega)).toNat +
              (s.core.wvec[(2 * sl.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                rw [hmod1]; omega)).toNat) % 2 ^ 64 = off0 + sz0 := by
            simp only [hmod0, hmod1, hoff_eq, hsz_eq]; exact Nat.mod_eq_of_lt (by omega)
          c0_hsteps_nogrp
          refine wp_loop_inv
            (fun (res1, p, ()) mlp => ∃ antp : BitVec 64,
              off0 ≤ p.toNat ∧ p.toNat ≤ off0 + sz0 ∧ antp.toNat ≤ ant.toNat ∧
              DenseWatchSliceOk F_cur s.core sl.toNat p.toNat (off0 + sz0 - p.toNat) ∧
              (FullMem c { s with scratch := { s.scratch with ant_sz := antp } } ⋆ R) mlp)
            (fun (_, p, _) _ => off0 + sz0 - p.toNat)
            (fun Jp hJp => by
              c0_hfast
              exact hJp (res, _, ()) ml ⟨ant, by rw [hoff_c0]; exact Nat.le_refl _,
                by rw [hoff_c0]; omega, Nat.le_refl _,
                by rw [hoff_c0, Nat.add_sub_cancel_left]; exact hslice_sl, hml⟩)
            (fun Jp (res1, p, ()) mlp ⟨antp, hp_ge, hp_le, hantp_le, hrem, hmlp⟩ ihp => ?_)
          c0_hfast
          · have hp_lt : p.toNat < off0 + sz0 := by rw [← hend_mod]; assumption
            have hp_ws : p.toNat < s.core.wstk.length := by omega
            have hant1 : (antp - 1#64).toNat ≤ ant.toNat := by simp only [bv_c0]; omega
            have hp1_n : (p + 1).toNat = p.toNat + 1 := by
              change (p + 1#64).toNat = _; simp only [bv_c0]; omega
            have hp1_mod : (p.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = p.toNat + 1 := by
              rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]; omega
            c0_hfast
            · have ⟨_, _, hrem_next⟩ := FullBvaFwdHelpers.bva_slice_bin_info hrem (by omega) hp_ws
                (by assumption)
              exact ihp (_, p + 1, ()) m (by dsimp only; rw [hp1_n]; omega)
                ⟨antp - 1#64, by rw [hp1_n]; omega, by rw [hp1_n]; omega, hant1,
                 by rw [hp1_n, show off0 + sz0 - (p.toNat + 1) = off0 + sz0 - p.toNat - 1 by omega]
                    exact hrem_next, hm⟩
            · have ⟨_, _, hrem_next⟩ := FullBvaFwdHelpers.bva_slice_bin_info hrem (by omega) hp_ws
                (by assumption)
              exact ihp (_, p + 1, ()) m (by dsimp only; rw [hp1_n]; omega)
                ⟨antp - 1#64, by rw [hp1_n]; omega, by rw [hp1_n]; omega, hant1,
                 by rw [hp1_n, show off0 + sz0 - (p.toNat + 1) = off0 + sz0 - p.toNat - 1 by omega]
                    exact hrem_next, hm⟩
            · have hm_flat : (FullMem c
                  { s with scratch := { s.scratch with ant_sz := antp - 1#64 } } ⋆ R) m := hm
              clear hm
              have ⟨h2le, hrem_next⟩ := FullBvaFwdHelpers.bva_slice_occ_info hrem (by omega) hp_ws
                (by assumption)
              have hp1_ws : p.toNat + 1 < s.core.wstk.length := by omega
              have ⟨_, hcr_ref, _⟩ := FullBvaFwdHelpers.fwd_slice_occ_info hrem (by omega) hp_ws
                hp1_ws (by assumption)
              have hcr_wf := hinv.2.1.arena.refs_wf _ hcr_ref
              have hp2_n : (p + 1 + 1).toNat = p.toNat + 2 := by
                change (p + 1#64 + 1#64).toNat = _; simp only [bv_c0]; omega
              let cr := s.core.wstk[p.toNat + 1]'hp1_ws
              have hcr_al : cr.toNat + 3 + fullArenaClauseSizeCore s.core cr.toNat ≤
                  s.core.arena_len := by
                have h1 := hcr_wf.2.2.1; have h2 := hcr_wf.2.2.2.1; dsimp only [cr]; omega
              have hcr_eq : s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws) = cr := by
                dsimp only [cr]; simp only [hp1_n]
              have hcr0_eq : (BitVec.setWidth 64
                  (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws))).toNat = cr.toNat := by
                rw [bv64_setWidth_32, hcr_eq]
              have hcr_b0 : (BitVec.setWidth 64
                  (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws))).toNat <
                  s.core.arena.length := by rw [hcr0_eq]; omega
              have hcr2_eq : (BitVec.setWidth 64
                  (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws)) + 2).toNat =
                  cr.toNat + 2 := by
                change (BitVec.setWidth 64 _ + 2#64).toNat = _
                rw [hcr_eq]; simp only [bv_c0]; omega
              have hcr_b2 : (BitVec.setWidth 64
                  (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws)) + 2).toNat <
                  s.core.arena.length := by rw [hcr2_eq]; omega
              have hsz_cr : (s.core.arena[cr.toNat + 2]'(by omega)).toNat =
                  fullArenaClauseSizeCore s.core cr.toNat := by
                unfold fullArenaClauseSizeCore
                rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
              have hcr_sz_le : cr.toNat + 3 + (s.core.arena[cr.toNat + 2]'(by omega)).toNat ≤
                  s.core.arena.length := by rw [hsz_cr]; omega
              c0_hfast
              · clear hQ ihs hJend
                refine wp_loop_inv
                  (fun (resk, k, ()) mk =>
                    k.toNat ≤ (s.core.arena[cr.toNat + 2]'(by omega)).toNat ∧ mk = m)
                  (fun (_, k, _) _ => (s.core.arena[cr.toNat + 2]'(by omega)).toNat - k.toNat)
                  (fun Jk hJk => by c0_hfast; exact hJk (res1, 0#32, ()) m ⟨Nat.zero_le _, rfl⟩)
                  (fun Jk (resk, k, ()) mk ⟨hk_le, hmk⟩ ihk => ?_)
                subst hmk; c0_hsplit
                · have hk_lt : k.toNat < (s.core.arena[cr.toNat + 2]'(by omega)).toNat := by
                    have h1 : k.toNat < (s.core.arena[(BitVec.setWidth 64
                        (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws)) +
                        2).toNat]'hcr_b2).toNat := by assumption
                    simpa only [hcr2_eq] using h1
                  have hcrk_b : (BitVec.setWidth 64
                      (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws)) + 3 +
                      BitVec.setWidth 64 k).toNat < s.core.arena.length := by
                    change (BitVec.setWidth 64 _ + 3#64 + BitVec.setWidth 64 k).toNat < _
                    rw [hcr_eq]; simp only [bv_c0]; omega
                  have hk1 : (k + 1#32).toNat = k.toNat + 1 := by simp only [bv_c0]; omega
                  c0_hfast
                  all_goals
                    exact ihk (_, k + 1#32, ()) mk (by dsimp only; rw [hk1]; omega)
                      ⟨by rw [hk1]; omega, rfl⟩
                · c0_hfast
                  exact ihp (resk, p + 1 + 1, ()) mk (by dsimp only; rw [hp2_n]; omega)
                    ⟨antp - 1#64, by rw [hp2_n]; omega, by rw [hp2_n]; omega, hant1,
                     by rw [hp2_n, show off0 + sz0 - (p.toNat + 2) = off0 + sz0 - p.toNat - 2
                          by omega]; exact hrem_next, hm_flat⟩
              · exact ihp (res1, p + 1 + 1, ()) m (by dsimp only; rw [hp2_n]; omega)
                  ⟨antp - 1#64, by rw [hp2_n]; omega, by rw [hp2_n]; omega, hant1,
                   by rw [hp2_n, show off0 + sz0 - (p.toNat + 2) = off0 + sz0 - p.toNat - 2
                        by omega]; exact hrem_next, hm_flat⟩
            · exfalso
              have ⟨h2le, _⟩ := FullBvaFwdHelpers.bva_slice_occ_info hrem (by omega) hp_ws
                (by assumption)
              have hge : ¬ (p.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 <
                  ((s.core.wvec[2 * sl.toNat % 2 ^ 64]'(by rw [hmod0]; omega)).toNat +
                   (s.core.wvec[(2 * sl.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                     rw [hmod1]; omega)).toNat) % 2 ^ 64 := by assumption
              rw [hend_mod, hp1_mod] at hge; omega
          all_goals
            exact ihs (res1, sgn + 1#32, ()) mlp (by simp only [bv_c0]; omega)
              ⟨antp, by simp only [bv_c0]; omega, Nat.le_trans hantp_le hant_le, hmlp⟩
        · exact hJend ant ml ⟨hant_le, hml⟩
        · exact hJend ant ml ⟨hant_le, hml⟩
    · c0_hsteps
      · exact hJ0 1#64 m rfl
      · exact hJ0 0#64 m rfl

theorem full_bva_hop2_wp (Γ : Env)
    (hHop1 : ∀ args m Q X, fullBvaHop1Spec args m Q X →
      Γ "full_bva_hop1" [i64, i32, i32] [i64] args m Q X) :
    ∀ args m Q X, fullBvaHop2Spec args m Q X → Func.wp Γ full_bva_hop2_body args m Q X := by
  rintro ⟨h, src_lit, dst_idx, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hinv, hsrc_lt, htc_le, htl_le, hmclr_ok, hshrk_ok, hm, hQ⟩
  have hmx := c.hmaxv; have hwcap := c.hwcap; have har_b := c.harena
  unfold dimacsBound at hmx hwcap har_b
  have hcl := hinv.1.core_ok; have hsc := hinv.1.scratch_ok
  have hcv_le := hcl.cur_vars_le; have hsig_len := hsc.sim_sig_len
  have hshrk_len := hsc.shrink_stk_len
  have hwv_len := hcl.wvec_len; have hws_len := hcl.wstk_len_arr; have har_len := hcl.arena_len_arr
  have hwlen_le := hcl.wlen_le; have hal_le := hcl.arena_len_le
  have hsidx_lt : (src_lit >>> 1).toNat < s.core.cur_vars := by rw [bv32_lshr1_nat]; omega
  c0_hsteps_nogrp
  · exact hQ _ s.core.repr s.core.min_clr s.core.tmp_cnt s.core.tmp_len s.scratch.ant_sz
      s.scratch.sim_sig s.scratch.shrink_stk m hinv htc_le htl_le hmclr_ok hshrk_ok
      (Nat.le_refl _) hm
  · refine wp_join_state1 (t := i64) (α := BitVec 64) (fun r => r) (fun _ ml => m = ml)
      (fun _ res0 ml hml => ?_) (fun J0 hJ0 => ?_)
    · rcases hml with rfl
      c0_hsteps_nogrp
      let mkSt (rp mc : List (BitVec 32)) (tc : Nat) (ant : BitVec 64) : FullState :=
        { core := { s.core with repr := rp, min_clr := mc, tmp_cnt := tc }
          scratch := { s.scratch with ant_sz := ant } }
      refine wp_loop_inv
        (fun (res, sgn, ()) ml => ∃ rp mc tc ant,
          sgn.toNat ≤ 2 ∧ tc ≤ s.core.cur_vars ∧ ant.toNat ≤ s.scratch.ant_sz.toNat ∧
          FullDenseInvNoLm c F0 F_cur (mkSt rp mc tc ant) ∧
          (∀ i < tc, (mc[i]?.getD 0#32).toNat < c.max_vars) ∧
          (FullMem c (mkSt rp mc tc ant) ⋆ R) ml)
        (fun (_, sgn, _) _ => 2 - sgn.toNat)
        (fun Js hJs => by
          c0_hsteps; exact hJs (res0, 0#32, ()) m
            ⟨s.core.repr, s.core.min_clr, s.core.tmp_cnt, s.scratch.ant_sz, by decide, htc_le,
             Nat.le_refl _, hinv, hmclr_ok, hm⟩)
        (fun Js (res, sgn, ()) ml
            ⟨rp, mc, tc, ant, hsgn_le, htc, hant, hinv_s, hmc_ok, hml⟩ ihs => ?_)
      c0_hsteps_nogrp
      refine wp_join_state0
        (α := List (BitVec 32) × List (BitVec 32) × Nat × BitVec 64)
        (fun ⟨rpF, mcF, tcF, antF⟩ mf =>
          tcF ≤ s.core.cur_vars ∧ antF.toNat ≤ s.scratch.ant_sz.toNat ∧
          FullDenseInvNoLm c F0 F_cur (mkSt rpF mcF tcF antF) ∧
          (∀ i < tcF, (mcF[i]?.getD 0#32).toNat < c.max_vars) ∧
          (FullMem c (mkSt rpF mcF tcF antF) ⋆ R) mf)
        (fun _ ⟨rpF, mcF, tcF, antF⟩ mf ⟨htcF, hantF, hinvF, hmcF, hmf⟩ => ?_)
        (fun Jend hJend => ?_)
      · dsimp only [mkSt] at hmf hinvF
        c0_hsteps_nogrp
        refine wp_join_state1 (t := i64) (α := BitVec 64) (fun r => r) (fun _ ml => mf = ml)
          (fun _ resC ml hml => ?_) (fun Jc hJc => ?_)
        · rcases hml with rfl
          c0_hsteps
          · have htl1 : s.core.tmp_len + 1 ≤ s.core.cur_vars := by c0_bound
            let sc1 : FullScratch :=
              { s.scratch with
                ant_sz := antF
                sim_sig := s.scratch.sim_sig.set (src_lit >>> 1).toNat (resC + 1)
                shrink_stk := s.scratch.shrink_stk.set s.core.tmp_len (src_lit >>> 1) }
            have hinv' := fullDenseInvNoLm_with_core_aux (tc' := tcF) (tl' := s.core.tmp_len + 1)
              (sc' := sc1) hinvF hinvF.1.core_ok.repr_len hinvF.1.core_ok.min_clr_len_arr
              hcl.tmp_len_arr hcl.flags_len (by omega)
              { hsc with sim_sig_len := by simp [sc1, hsig_len],
                         shrink_stk_len := by simp [sc1, hshrk_len] }
              rfl rfl
            have hm' : (FullMem c
                { core := { s.core with repr := rpF, min_clr := mcF, tmp_cnt := tcF,
                                        tmp_len := s.core.tmp_len + 1 }
                  scratch := sc1 } ⋆ R) m := by
              have h1 : (BitVec.ofNat 64 s.core.tmp_len + 1).toNat = s.core.tmp_len + 1 := by
                change (BitVec.ofNat 64 s.core.tmp_len + 1#64).toNat = _; c0_bound
              have h2 : (BitVec.ofNat 64 s.core.tmp_len).toNat = s.core.tmp_len := by c0_bound
              have h3 : (BitVec.setWidth 64 (src_lit >>> 1)).toNat = (src_lit >>> 1).toNat := by
                c0_bound
              dsimp only [sc1]; rw [h1, h2, h3] at hm; exact hm
            exact hQ _ rpF mcF tcF (s.core.tmp_len + 1) antF _ _ m
              (by dsimp only [sc1] at hinv'; exact hinv') htcF htl1 hmcF
              (fun i hi => by
                by_cases hie : i = s.core.tmp_len
                · subst hie; rw [List.getElem?_set_self (by omega), Option.getD_some]; omega
                · rw [List.getElem?_set_ne (Ne.symm hie)]; exact hshrk_ok i (by omega)) hantF hm'
          · let sc2 : FullScratch :=
              { s.scratch with
                ant_sz := antF
                sim_sig := s.scratch.sim_sig.set (src_lit >>> 1).toNat (resC + 1) }
            have hinv' := fullDenseInvNoLm_with_core_aux (tc' := tcF) (tl' := s.core.tmp_len)
              (sc' := sc2) hinvF hinvF.1.core_ok.repr_len hinvF.1.core_ok.min_clr_len_arr
              hcl.tmp_len_arr hcl.flags_len hcl.tmp_len_le
              { hsc with sim_sig_len := by simp [sc2, hsig_len] } rfl rfl
            have hm' : (FullMem c
                { core := { s.core with repr := rpF, min_clr := mcF, tmp_cnt := tcF }
                  scratch := sc2 } ⋆ R) m := by
              have h3 : (BitVec.setWidth 64 (src_lit >>> 1)).toNat = (src_lit >>> 1).toNat := by
                c0_bound
              dsimp only [sc2]; rw [h3] at hm; exact hm
            exact hQ _ rpF mcF tcF s.core.tmp_len antF _ s.scratch.shrink_stk m
              (by dsimp only [sc2] at hinv'; exact hinv') htcF htl_le hmcF hshrk_ok hantF hm'
        · c0_hsteps
          · exact hJc 0x3FFFFFFFFFFFFFFF#64 mf rfl
          · exact hJc res mf rfl
      · dsimp only [mkSt] at hml
        c0_hsteps
        · have hsgn_lt : sgn.toNat < 2 := by c0_bound
          have hsl_nat : (((src_lit >>> (1 : Nat)) <<< (1 : Nat)) ||| sgn).toNat =
              2 * (src_lit >>> (1 : Nat)).toNat + sgn.toNat := by
            have hs01 : sgn.toNat = 0 ∨ sgn.toNat = 1 := by omega
            rcases hs01 with h0 | h1
            · have hs0 : sgn = 0#32 := BitVec.eq_of_toNat_eq h0; subst hs0
              rw [BitVec.or_zero]; c0_bound
            · have hs1 : sgn = 1#32 := BitVec.eq_of_toNat_eq h1; subst hs1
              rw [FullBvaFwdTactics.bv32_or1_of_even (by c0_bound)]; c0_bound
          have hsl_lt : (((src_lit >>> (1 : Nat)) <<< (1 : Nat)) ||| sgn).toNat <
              2 * s.core.cur_vars := by omega
          obtain ⟨hbd_sl, hslice_sl⟩ := hop_wvec_bounds hinv hsl_lt
          let sl : BitVec 32 := ((src_lit >>> (1 : Nat)) <<< (1 : Nat)) ||| sgn
          have hsl_lt_sl : sl.toNat < 2 * s.core.cur_vars := hsl_lt
          have hwv_sl0 : (BitVec.setWidth 64 sl <<< (1 : Nat)).toNat < s.core.wvec.length := by
            c0_bound
          have hwv_sl1 : ((BitVec.setWidth 64 sl <<< (1 : Nat)) + 1).toNat <
              s.core.wvec.length := by
            change ((BitVec.setWidth 64 sl <<< (1 : Nat)) + 1#64).toNat < _; c0_bound
          have hoff_eq : (s.core.wvec[2 * sl.toNat]'(by omega)).toNat =
              fullWatchOffCore s.core sl.toNat := by
            unfold fullWatchOffCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          have hsz_eq : (s.core.wvec[2 * sl.toNat + 1]'(by omega)).toNat =
              fullWatchSizeCore s.core sl.toNat := by
            unfold fullWatchSizeCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          let off0 := fullWatchOffCore s.core sl.toNat
          let sz0 := fullWatchSizeCore s.core sl.toNat
          have hoff_sz_le : off0 + sz0 ≤ s.core.wlen := hbd_sl
          have h2sl0 : (BitVec.setWidth 64 sl <<< (1 : Nat)).toNat = 2 * sl.toNat := by c0_bound
          have h2sl1 : ((BitVec.setWidth 64 sl <<< (1 : Nat)) + 1).toNat = 2 * sl.toNat + 1 := by
            change ((BitVec.setWidth 64 sl <<< (1 : Nat)) + 1#64).toNat = _; c0_bound
          have hoff_c0 : (BitVec.setWidth 64
              (s.core.wvec[(BitVec.setWidth 64 sl <<< (1 : Nat)).toNat]'hwv_sl0)).toNat = off0 := by
            rw [bv64_setWidth_32]; simp only [h2sl0]; exact hoff_eq
          have hmod0 : 2 * sl.toNat % 2 ^ 64 = 2 * sl.toNat := Nat.mod_eq_of_lt (by omega)
          have hmod1 : (2 * sl.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = 2 * sl.toNat + 1 :=
            by c0_bound
          have hend_mod : ((s.core.wvec[2 * sl.toNat % 2 ^ 64]'(by rw [hmod0]; omega)).toNat +
              (s.core.wvec[(2 * sl.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                rw [hmod1]; omega)).toNat) % 2 ^ 64 = off0 + sz0 := by
            simp only [hmod0, hmod1, hoff_eq, hsz_eq]; exact Nat.mod_eq_of_lt (by omega)
          c0_hsteps_nogrp
          refine wp_loop_inv
            (fun (res1, p, ()) mlp => ∃ rpp mcp tcp antp,
              off0 ≤ p.toNat ∧ p.toNat ≤ off0 + sz0 ∧ tcp ≤ s.core.cur_vars ∧
              antp.toNat ≤ ant.toNat ∧ FullDenseInvNoLm c F0 F_cur (mkSt rpp mcp tcp antp) ∧
              (∀ i < tcp, (mcp[i]?.getD 0#32).toNat < c.max_vars) ∧
              DenseWatchSliceOk F_cur s.core sl.toNat p.toNat (off0 + sz0 - p.toNat) ∧
              (FullMem c (mkSt rpp mcp tcp antp) ⋆ R) mlp)
            (fun (_, p, _) _ => off0 + sz0 - p.toNat)
            (fun Jp hJp => by
              c0_hfast
              exact hJp (res, _, ()) ml ⟨rp, mc, tc, ant, by rw [hoff_c0]; exact Nat.le_refl _,
                by rw [hoff_c0]; omega, htc, Nat.le_refl _, hinv_s, hmc_ok,
                by rw [hoff_c0, Nat.add_sub_cancel_left]; exact hslice_sl, hml⟩)
            (fun Jp (res1, p, ()) mlp ⟨rpp, mcp, tcp, antp, hp_ge, hp_le, htcp, hantp, hinvp,
                hmcp_ok, hrem, hmlp⟩ ihp => ?_)
          dsimp only [mkSt] at hmlp
          c0_hfast
          · have hp_lt : p.toNat < off0 + sz0 := by rw [← hend_mod]; assumption
            have hp_ws : p.toNat < s.core.wstk.length := by omega
            have hant1 : (antp - 1#64).toNat ≤ ant.toNat := by simp only [bv_c0]; omega
            have hp1_n : (p + 1).toNat = p.toNat + 1 := by
              change (p + 1#64).toNat = _; simp only [bv_c0]; omega
            have hp1_mod : (p.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = p.toNat + 1 := by
              rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]; omega
            have hinvp1 : FullDenseInvNoLm c F0 F_cur (mkSt rpp mcp tcp (antp - 1#64)) :=
              fullDenseInvNoLm_with_core_aux (tc' := tcp) (tl' := s.core.tmp_len) hinvp
                hinvp.1.core_ok.repr_len hinvp.1.core_ok.min_clr_len_arr hcl.tmp_len_arr
                hcl.flags_len hcl.tmp_len_le { hsc with } rfl rfl
            c0_hfast
            · have ⟨hot_lt, _, hrem_next⟩ :=
                FullBvaFwdHelpers.bva_slice_bin_info hrem (by omega) hp_ws (by assumption)
              c0_call hHop1
              refine ⟨c, F0, F_cur, mkSt rpp mcp tcp (antp - 1#64), R, rfl, hinvp1, hot_lt, htcp,
                hmcp_ok, hm, fun r1 rp1 mc1 tc1 ant1 m1 hinv1 htc1 hmc1 hant1' hm1 => ?_⟩
              c0_hfast
              exact ihp (res1 + r1, p + 1, ()) m1 (by dsimp only; rw [hp1_n]; omega)
                ⟨rp1, mc1, tc1, ant1, by rw [hp1_n]; omega, by rw [hp1_n]; omega, htc1,
                 Nat.le_trans hant1' hant1, hinv1, hmc1,
                 by rw [hp1_n, show off0 + sz0 - (p.toNat + 1) = off0 + sz0 - p.toNat - 1 by omega]
                    exact hrem_next, hm1⟩
            · have hm_flat : (FullMem c
                  { core := { s.core with repr := rpp, min_clr := mcp, tmp_cnt := tcp },
                    scratch := { s.scratch with ant_sz := antp - 1#64 } } ⋆ R) m := hm
              clear hm
              have ⟨h2le, hrem_next⟩ := FullBvaFwdHelpers.bva_slice_occ_info hrem (by omega) hp_ws
                (by assumption)
              have hp1_ws : p.toNat + 1 < s.core.wstk.length := by omega
              have ⟨_, hcr_ref, _⟩ := FullBvaFwdHelpers.fwd_slice_occ_info hrem (by omega) hp_ws
                hp1_ws (by assumption)
              have hcr_wf := hinv.2.1.arena.refs_wf _ hcr_ref
              have hp2_n : (p + 1 + 1).toNat = p.toNat + 2 := by
                change (p + 1#64 + 1#64).toNat = _; simp only [bv_c0]; omega
              let cr := s.core.wstk[p.toNat + 1]'hp1_ws
              have hcr_al : cr.toNat + 3 + fullArenaClauseSizeCore s.core cr.toNat ≤
                  s.core.arena_len := by
                have h1 := hcr_wf.2.2.1; have h2 := hcr_wf.2.2.2.1; dsimp only [cr]; omega
              have hcr_eq : s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws) = cr := by
                dsimp only [cr]; simp only [hp1_n]
              have hcr0_eq : (BitVec.setWidth 64
                  (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws))).toNat = cr.toNat := by
                rw [bv64_setWidth_32, hcr_eq]
              have hcr_b0 : (BitVec.setWidth 64
                  (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws))).toNat <
                  s.core.arena.length := by rw [hcr0_eq]; omega
              have hcr2_eq : (BitVec.setWidth 64
                  (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws)) + 2).toNat =
                  cr.toNat + 2 := by
                change (BitVec.setWidth 64 _ + 2#64).toNat = _
                rw [hcr_eq]; simp only [bv_c0]; omega
              have hcr_b2 : (BitVec.setWidth 64
                  (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws)) + 2).toNat <
                  s.core.arena.length := by rw [hcr2_eq]; omega
              have hsz_cr : (s.core.arena[cr.toNat + 2]'(by omega)).toNat =
                  fullArenaClauseSizeCore s.core cr.toNat := by
                unfold fullArenaClauseSizeCore
                rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
              have hcr_sz_le : cr.toNat + 3 + (s.core.arena[cr.toNat + 2]'(by omega)).toNat ≤
                  s.core.arena.length := by rw [hsz_cr]; omega
              c0_hfast
              · have hng_cr : fullArenaClauseGarbCore s.core cr.toNat = false := by
                  unfold fullArenaClauseGarbCore fullArenaHdrCore
                  rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                  have h1 : s.core.arena[(BitVec.setWidth 64
                      (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws))).toNat]'hcr_b0 &&&
                      (524288#32 ||| 4194304#32) = 0#32 := by assumption
                  exact FullBvaFwdHelpers.garb_false_of_and_garb_red_eq_zero (by
                    simpa only [hcr0_eq] using h1)
                clear hQ ihs hJend
                refine wp_loop_inv
                  (fun (resk, k, ()) mk => ∃ rpk mck tck antk,
                    k.toNat ≤ (s.core.arena[cr.toNat + 2]'(by omega)).toNat ∧
                    tck ≤ s.core.cur_vars ∧ antk.toNat ≤ ant.toNat ∧
                    FullDenseInvNoLm c F0 F_cur (mkSt rpk mck tck antk) ∧
                    (∀ i < tck, (mck[i]?.getD 0#32).toNat < c.max_vars) ∧
                    (FullMem c (mkSt rpk mck tck antk) ⋆ R) mk)
                  (fun (_, k, _) _ => (s.core.arena[cr.toNat + 2]'(by omega)).toNat - k.toNat)
                  (fun Jk hJk => by
                    c0_hfast; exact hJk (res1, 0#32, ()) m
                      ⟨rpp, mcp, tcp, antp - 1#64, Nat.zero_le _, htcp, hant1, hinvp1, hmcp_ok,
                       hm_flat⟩)
                  (fun Jk (resk, k, ()) mk ⟨rpk, mck, tck, antk, hk_le, htck, hantk, hinvk,
                      hmck_ok, hmk⟩ ihk => ?_)
                dsimp only [mkSt] at hmk
                c0_hsplit
                · have hk_lt : k.toNat < (s.core.arena[cr.toNat + 2]'(by omega)).toNat := by
                    have h1 : k.toNat < (s.core.arena[(BitVec.setWidth 64
                        (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws)) +
                        2).toNat]'hcr_b2).toNat := by assumption
                    simpa only [hcr2_eq] using h1
                  have hk1 : (k + 1#32).toNat = k.toNat + 1 := by simp only [bv_c0]; omega
                  c0_hsplit
                  · have hcrk_b : (BitVec.setWidth 64
                        (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws)) + 3 +
                        BitVec.setWidth 64 k).toNat < s.core.arena.length := by
                      change (BitVec.setWidth 64 _ + 3#64 + BitVec.setWidth 64 k).toNat < _
                      rw [hcr_eq]; simp only [bv_c0]; omega
                    have hol_mem : (s.core.arena[cr.toNat + 3 + k.toNat]'(by omega)).toNat ∈
                        fullArenaClauseLitsCore s.core cr.toNat :=
                      List.mem_of_getElem? (FullBvaFwdHelpers.fullArenaClauseLitsCore_getElem
                        (by rw [← hsz_cr]; exact hk_lt) (by omega))
                    have hol_lt := hinv.2.1.arena.lits_lt cr.toNat hcr_ref hng_cr _ hol_mem
                    have hcrk_eq : (BitVec.setWidth 64 cr + 3 + BitVec.setWidth 64 k).toNat =
                        cr.toNat + 3 + k.toNat := by
                      change (BitVec.setWidth 64 cr + 3#64 + BitVec.setWidth 64 k).toNat = _
                      simp only [bv_c0]; omega
                    c0_hfast
                    · c0_call hHop1
                      refine ⟨c, F0, F_cur, mkSt rpk mck tck antk, R, rfl, hinvk, ?_, htck, hmck_ok,
                        hmk, fun r1 rp1 mc1 tc1 ant1 m1 hinv1 htc1 hmc1 hant1' hm1 => ?_⟩
                      · simpa only [hcr_eq, hcrk_eq] using hol_lt
                      · c0_hfast
                        exact ihk (resk + r1, k + 1#32, ()) m1 (by dsimp only; rw [hk1]; omega)
                          ⟨rp1, mc1, tc1, ant1, by rw [hk1]; omega, htc1,
                           Nat.le_trans hant1' hantk, hinv1, hmc1, hm1⟩
                    · exact ihk (resk, k + 1#32, ()) mk (by dsimp only; rw [hk1]; omega)
                        ⟨rpk, mck, tck, antk, by rw [hk1]; omega, htck, hantk, hinvk, hmck_ok, hmk⟩
                  · c0_hfast
                    exact ihp (resk, p + 1 + 1, ()) mk (by dsimp only; rw [hp2_n]; omega)
                      ⟨rpk, mck, tck, antk, by rw [hp2_n]; omega, by rw [hp2_n]; omega, htck, hantk,
                       hinvk, hmck_ok,
                       by rw [hp2_n, show off0 + sz0 - (p.toNat + 2) = off0 + sz0 - p.toNat - 2
                            by omega]; exact hrem_next, hmk⟩
                · c0_hfast
                  exact ihp (resk, p + 1 + 1, ()) mk (by dsimp only; rw [hp2_n]; omega)
                    ⟨rpk, mck, tck, antk, by rw [hp2_n]; omega, by rw [hp2_n]; omega, htck, hantk,
                     hinvk, hmck_ok,
                     by rw [hp2_n, show off0 + sz0 - (p.toNat + 2) = off0 + sz0 - p.toNat - 2
                          by omega]; exact hrem_next, hmk⟩
              · exact ihp (res1, p + 1 + 1, ()) m (by dsimp only; rw [hp2_n]; omega)
                  ⟨rpp, mcp, tcp, antp - 1#64, by rw [hp2_n]; omega, by rw [hp2_n]; omega, htcp,
                   hant1, hinvp1, hmcp_ok,
                   by rw [hp2_n, show off0 + sz0 - (p.toNat + 2) = off0 + sz0 - p.toNat - 2
                        by omega]; exact hrem_next, hm_flat⟩
            · exfalso
              have ⟨h2le, _⟩ := FullBvaFwdHelpers.bva_slice_occ_info hrem (by omega) hp_ws
                (by assumption)
              have hge : ¬ (p.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 <
                  ((s.core.wvec[2 * sl.toNat % 2 ^ 64]'(by rw [hmod0]; omega)).toNat +
                   (s.core.wvec[(2 * sl.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                     rw [hmod1]; omega)).toNat) % 2 ^ 64 := by assumption
              rw [hend_mod, hp1_mod] at hge; omega
          all_goals
            exact ihs (res1, sgn + 1#32, ()) mlp (by simp only [bv_c0]; omega)
              ⟨rpp, mcp, tcp, antp, by simp only [bv_c0]; omega, htcp, Nat.le_trans hantp hant,
               hinvp, hmcp_ok, hmlp⟩
        · exact hJend ⟨rp, mc, tc, ant⟩ ml ⟨htc, hant, hinv_s, hmc_ok, hml⟩
        · exact hJend ⟨rp, mc, tc, ant⟩ ml ⟨htc, hant, hinv_s, hmc_ok, hml⟩
    · c0_hsteps
      · exact hJ0 1#64 m rfl
      · exact hJ0 0#64 m rfl

theorem full_bva_hop3_wp (Γ : Env)
    (hHop2 : ∀ args m Q X, fullBvaHop2Spec args m Q X →
      Γ "full_bva_hop2" [i64, i32, i32] [i64] args m Q X) :
    ∀ args m Q X, fullBvaHop3Spec args m Q X → Func.wp Γ full_bva_hop3_body args m Q X := by
  rintro ⟨h, src_lit, dst_idx, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hinv, hsrc_lt, hm, hQ⟩
  have hmx := c.hmaxv; have hwcap := c.hwcap; have har_b := c.harena
  unfold dimacsBound at hmx hwcap har_b
  have hcl := hinv.1.core_ok; have hsc := hinv.1.scratch_ok
  have hcv_le := hcl.cur_vars_le; have hwv_len := hcl.wvec_len
  have hws_len := hcl.wstk_len_arr; have har_len := hcl.arena_len_arr
  have hwlen_le := hcl.wlen_le; have hal_le := hcl.arena_len_le
  have hsidx_lt : (src_lit >>> 1).toNat < s.core.cur_vars := by rw [bv32_lshr1_nat]; omega
  c0_hsteps_nogrp
  refine wp_join_state1 (t := i64) (α := BitVec 64) (fun r => r) (fun _ ml => ml = m)
    (fun _ res0 ml hml => ?_) (fun J0 hJ0 => ?_)
  · subst hml
    let mkSt (rp mc : List (BitVec 32)) (tc tl : Nat) (ant : BitVec 64) (sig : List (BitVec 64))
        (shrk : List (BitVec 32)) : FullState :=
      { core := { s.core with repr := rp, min_clr := mc, tmp_cnt := tc, tmp_len := tl }
        scratch := { s.scratch with ant_sz := ant, sim_sig := sig, shrink_stk := shrk } }
    c0_hsteps
    have hinv0 : FullDenseInvNoLm c F0 F_cur (mkSt s.core.repr s.core.min_clr 0 0 256#64
        s.scratch.sim_sig s.scratch.shrink_stk) :=
      fullDenseInvNoLm_with_core_aux hinv hcl.repr_len hcl.min_clr_len_arr hcl.tmp_len_arr
        hcl.flags_len (Nat.zero_le _) { hsc with } rfl rfl
    refine wp_loop_inv
      (fun (res, sgn, ()) ml => ∃ rp mc tc tl ant sig shrk,
        sgn.toNat ≤ 2 ∧ tc ≤ s.core.cur_vars ∧ tl ≤ s.core.cur_vars ∧
        FullDenseInvNoLm c F0 F_cur (mkSt rp mc tc tl ant sig shrk) ∧
        (∀ i < tc, (mc[i]?.getD 0#32).toNat < c.max_vars) ∧
        (∀ i < tl, (shrk[i]?.getD 0#32).toNat < c.max_vars) ∧
        (FullMem c (mkSt rp mc tc tl ant sig shrk) ⋆ R) ml)
      (fun (_, sgn, _) _ => 2 - sgn.toNat)
      (fun Js hJs => by
        c0_hsteps; exact hJs (res0, 0#32, ()) m
          ⟨s.core.repr, s.core.min_clr, 0, 0, 256#64, s.scratch.sim_sig, s.scratch.shrink_stk,
           by decide, Nat.zero_le _, Nat.zero_le _, hinv0,
           fun _ h => by omega, fun _ h => by omega, hm⟩)
      (fun Js (res, sgn, ()) ml ⟨rp, mc, tc, tl, ant, sig, shrk, hsgn_le, htc, htl, hinv_s,
          hmc_ok, hshrk_ok, hml⟩ ihs => ?_)
    c0_hsteps_nogrp
    refine wp_join_state0
      (α := List (BitVec 32) × List (BitVec 32) × Nat × Nat × BitVec 64 ×
        List (BitVec 64) × List (BitVec 32))
      (fun ⟨rpF, mcF, tcF, tlF, antF, sigF, shrkF⟩ mf =>
        tcF ≤ s.core.cur_vars ∧ tlF ≤ s.core.cur_vars ∧
        FullDenseInvNoLm c F0 F_cur (mkSt rpF mcF tcF tlF antF sigF shrkF) ∧
        (∀ i < tcF, (mcF[i]?.getD 0#32).toNat < c.max_vars) ∧
        (∀ i < tlF, (shrkF[i]?.getD 0#32).toNat < c.max_vars) ∧
        (FullMem c (mkSt rpF mcF tcF tlF antF sigF shrkF) ⋆ R) mf)
      (fun _ ⟨rpF, mcF, tcF, tlF, antF, sigF, shrkF⟩ mf
          ⟨htcF, htlF, hinvF, hmcF, hshrkF, hmf⟩ => ?_)
      (fun Jend hJend => ?_)
    · -- Cleanup loops: zero `s1[st1[0..tcF)]` then `s2[st2[0..tlF)]`, reset `tmp_cnt=0, tmp_len=0`
      have hmcF_len : mcF.length = c.max_vars := hinvF.1.core_ok.min_clr_len_arr
      have hshrkF_len : shrkF.length = c.max_vars := hinvF.1.scratch_ok.shrink_stk_len
      c0_hsteps
      refine wp_loop_inv
        (fun (i, ()) mi => ∃ rpi, i.toNat ≤ tcF ∧ rpi.length = 2 * c.max_vars ∧
          (FullMem c (mkSt rpi mcF tcF tlF antF sigF shrkF) ⋆ R) mi)
        (fun (i, ()) _ => tcF - i.toNat)
        (fun J1 hJ1 => by
          c0_hsteps; exact hJ1 (0#64, ()) mf ⟨rpF, Nat.zero_le _, hinvF.1.core_ok.repr_len, hmf⟩)
        (fun J1 (i, ()) mi ⟨rpi, hi_le, hrpi_len, hmi⟩ ih1 => ?_)
      dsimp only [mkSt] at hmi
      c0_hsteps
      · have hi_lt : i.toNat < tcF := by c0_bound
        have hidx_lt : (mcF[i.toNat]'(by omega)).toNat < c.max_vars := by
          have := hmcF i.toNat hi_lt
          rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
        c0_hsteps
        exact ih1 (i + 1#64, ()) m (by c0_bound)
          ⟨_, by c0_bound, by rw [repr64Set_length, hrpi_len], hm⟩
      · refine wp_loop_inv
          (fun (i, ()) mi2 => ∃ sigi, i.toNat ≤ tlF ∧ sigi.length = c.max_vars ∧
            (FullMem c (mkSt rpi mcF tcF tlF antF sigi shrkF) ⋆ R) mi2)
          (fun (i, ()) _ => tlF - i.toNat)
          (fun J2 hJ2 => by
            c0_hsteps; exact hJ2 (0#64, ()) mi ⟨sigF, Nat.zero_le _, hinvF.1.scratch_ok.sim_sig_len,
              hmi⟩)
          (fun J2 (i, ()) mi2 ⟨sigi, hi2_le, hsigi_len, hmi2⟩ ih2 => ?_)
        dsimp only [mkSt] at hmi2
        c0_hsteps
        · have hi2_lt : i.toNat < tlF := by c0_bound
          have hidx_lt : (shrkF[i.toNat]'(by omega)).toNat < c.max_vars := by
            have := hshrkF i.toNat hi2_lt
            rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
          c0_hsteps
          exact ih2 (i + 1#64, ()) m (by c0_bound) ⟨_, by c0_bound, by simp [hsigi_len], hm⟩
        · have hsc_fin : ({ s.scratch with
              ant_sz := antF, sim_sig := sigi, shrink_stk := shrkF } : FullScratch).LengthsOk c :=
            { hsc with sim_sig_len := hsigi_len, shrink_stk_len := hshrkF_len }
          dsimp only [mkSt] at hinvF
          have hinv_fin := fullDenseInvNoLm_with_core_aux (tc' := 0) (tl' := 0) hinvF hrpi_len
            hmcF_len hcl.tmp_len_arr hcl.flags_len (Nat.zero_le _) hsc_fin rfl rfl
          exact hQ res rpi mcF antF sigi shrkF m hinv_fin hm
    · dsimp only [mkSt] at hml
      c0_hsteps
      · have hsgn_lt : sgn.toNat < 2 := by c0_bound
        have hsl_nat : (((src_lit >>> (1 : Nat)) <<< (1 : Nat)) ||| sgn).toNat =
            2 * (src_lit >>> (1 : Nat)).toNat + sgn.toNat := by
          have hs01 : sgn.toNat = 0 ∨ sgn.toNat = 1 := by omega
          rcases hs01 with h0 | h1
          · have hs0 : sgn = 0#32 := BitVec.eq_of_toNat_eq h0; subst hs0
            rw [BitVec.or_zero]; c0_bound
          · have hs1 : sgn = 1#32 := BitVec.eq_of_toNat_eq h1; subst hs1
            rw [FullBvaFwdTactics.bv32_or1_of_even (by c0_bound)]; c0_bound
        have hsl_lt : (((src_lit >>> (1 : Nat)) <<< (1 : Nat)) ||| sgn).toNat <
            2 * s.core.cur_vars := by omega
        obtain ⟨hbd_sl, hslice_sl⟩ := hop_wvec_bounds hinv hsl_lt
        let sl : BitVec 32 := ((src_lit >>> (1 : Nat)) <<< (1 : Nat)) ||| sgn
        have hsl_lt_sl : sl.toNat < 2 * s.core.cur_vars := hsl_lt
        have hwv_sl0 : (BitVec.setWidth 64 sl <<< (1 : Nat)).toNat < s.core.wvec.length := by
          c0_bound
        have hwv_sl1 : ((BitVec.setWidth 64 sl <<< (1 : Nat)) + 1).toNat < s.core.wvec.length := by
          change ((BitVec.setWidth 64 sl <<< (1 : Nat)) + 1#64).toNat < _; c0_bound
        have hoff_eq : (s.core.wvec[2 * sl.toNat]'(by omega)).toNat =
            fullWatchOffCore s.core sl.toNat := by
          unfold fullWatchOffCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
        have hsz_eq : (s.core.wvec[2 * sl.toNat + 1]'(by omega)).toNat =
            fullWatchSizeCore s.core sl.toNat := by
          unfold fullWatchSizeCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
        let off0 := fullWatchOffCore s.core sl.toNat
        let sz0 := fullWatchSizeCore s.core sl.toNat
        have hoff_sz_le : off0 + sz0 ≤ s.core.wlen := hbd_sl
        have h2sl0 : (BitVec.setWidth 64 sl <<< (1 : Nat)).toNat = 2 * sl.toNat := by c0_bound
        have h2sl1 : ((BitVec.setWidth 64 sl <<< (1 : Nat)) + 1).toNat = 2 * sl.toNat + 1 := by
          change ((BitVec.setWidth 64 sl <<< (1 : Nat)) + 1#64).toNat = _; c0_bound
        have hoff_c0 : (BitVec.setWidth 64
            (s.core.wvec[(BitVec.setWidth 64 sl <<< (1 : Nat)).toNat]'hwv_sl0)).toNat = off0 := by
          rw [bv64_setWidth_32]; simp only [h2sl0]; exact hoff_eq
        have hmod0 : 2 * sl.toNat % 2 ^ 64 = 2 * sl.toNat := Nat.mod_eq_of_lt (by omega)
        have hmod1 : (2 * sl.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = 2 * sl.toNat + 1 :=
          by c0_bound
        have hend_mod : ((s.core.wvec[2 * sl.toNat % 2 ^ 64]'(by rw [hmod0]; omega)).toNat +
            (s.core.wvec[(2 * sl.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
              rw [hmod1]; omega)).toNat) % 2 ^ 64 = off0 + sz0 := by
          simp only [hmod0, hmod1, hoff_eq, hsz_eq]; exact Nat.mod_eq_of_lt (by omega)
        c0_hsteps_nogrp
        refine wp_loop_inv
          (fun (res1, p, ()) mlp => ∃ rpp mcp tcp tlp antp sigp shrkp,
            off0 ≤ p.toNat ∧ p.toNat ≤ off0 + sz0 ∧ tcp ≤ s.core.cur_vars ∧
            tlp ≤ s.core.cur_vars ∧
            FullDenseInvNoLm c F0 F_cur (mkSt rpp mcp tcp tlp antp sigp shrkp) ∧
            (∀ i < tcp, (mcp[i]?.getD 0#32).toNat < c.max_vars) ∧
            (∀ i < tlp, (shrkp[i]?.getD 0#32).toNat < c.max_vars) ∧
            DenseWatchSliceOk F_cur s.core sl.toNat p.toNat (off0 + sz0 - p.toNat) ∧
            (FullMem c (mkSt rpp mcp tcp tlp antp sigp shrkp) ⋆ R) mlp)
          (fun (_, p, _) _ => off0 + sz0 - p.toNat)
          (fun Jp hJp => by
            c0_hfast
            exact hJp (res, _, ()) ml ⟨rp, mc, tc, tl, ant, sig, shrk,
              by rw [hoff_c0]; exact Nat.le_refl _, by rw [hoff_c0]; omega, htc, htl, hinv_s,
              hmc_ok, hshrk_ok, by rw [hoff_c0, Nat.add_sub_cancel_left]; exact hslice_sl, hml⟩)
          (fun Jp (res1, p, ()) mlp ⟨rpp, mcp, tcp, tlp, antp, sigp, shrkp, hp_ge, hp_le, htcp,
              htlp, hinvp, hmcp_ok, hshrkp_ok, hrem, hmlp⟩ ihp => ?_)
        dsimp only [mkSt] at hmlp
        c0_hfast
        · have hp_lt : p.toNat < off0 + sz0 := by rw [← hend_mod]; assumption
          have hp_ws : p.toNat < s.core.wstk.length := by omega
          have hp1_n : (p + 1).toNat = p.toNat + 1 := by
            change (p + 1#64).toNat = _; simp only [bv_c0]; omega
          have hp1_mod : (p.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = p.toNat + 1 := by
            rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]; omega
          have hinvp1 : FullDenseInvNoLm c F0 F_cur
              (mkSt rpp mcp tcp tlp (antp - 1#64) sigp shrkp) :=
            fullDenseInvNoLm_with_core_aux (tc' := tcp) (tl' := tlp) hinvp
              hinvp.1.core_ok.repr_len hinvp.1.core_ok.min_clr_len_arr hcl.tmp_len_arr
              hcl.flags_len hinvp.1.core_ok.tmp_len_le { hinvp.1.scratch_ok with } rfl rfl
          c0_hfast
          · have ⟨hot_lt, _, hrem_next⟩ := FullBvaFwdHelpers.bva_slice_bin_info hrem (by omega)
              hp_ws (by assumption)
            c0_call hHop2
            refine ⟨c, F0, F_cur, mkSt rpp mcp tcp tlp (antp - 1#64) sigp shrkp, R, rfl, hinvp1,
              hot_lt, htcp, htlp, hmcp_ok, hshrkp_ok, hm,
              fun r1 rp1 mc1 tc1 tl1 ant1 sig1 shrk1 m1 hinv1 htc1 htl1 hmc1 hshrk1 _ hm1 => ?_⟩
            c0_hfast
            exact ihp (res1 + r1, p + 1, ()) m1 (by dsimp only; rw [hp1_n]; omega)
              ⟨rp1, mc1, tc1, tl1, ant1, sig1, shrk1, by rw [hp1_n]; omega, by rw [hp1_n]; omega,
               htc1, htl1, hinv1, hmc1, hshrk1,
               by rw [hp1_n, show off0 + sz0 - (p.toNat + 1) = off0 + sz0 - p.toNat - 1 by omega]
                  exact hrem_next, hm1⟩
          · have hm_flat : (FullMem c
                { core := { s.core with repr := rpp, min_clr := mcp,
                                        tmp_cnt := tcp, tmp_len := tlp }
                  scratch := { s.scratch with ant_sz := antp - 1#64, sim_sig := sigp,
                                              shrink_stk := shrkp } } ⋆ R) m := hm
            clear hm
            have ⟨h2le, hrem_next⟩ := FullBvaFwdHelpers.bva_slice_occ_info hrem (by omega) hp_ws
              (by assumption)
            have hp1_ws : p.toNat + 1 < s.core.wstk.length := by omega
            have ⟨_, hcr_ref, _⟩ := FullBvaFwdHelpers.fwd_slice_occ_info hrem (by omega) hp_ws
              hp1_ws (by assumption)
            have hcr_wf := hinv.2.1.arena.refs_wf _ hcr_ref
            have hp2_n : (p + 1 + 1).toNat = p.toNat + 2 := by
              change (p + 1#64 + 1#64).toNat = _; simp only [bv_c0]; omega
            let cr := s.core.wstk[p.toNat + 1]'hp1_ws
            have hcr_al : cr.toNat + 3 + fullArenaClauseSizeCore s.core cr.toNat ≤
                s.core.arena_len := by
              have h1 := hcr_wf.2.2.1; have h2 := hcr_wf.2.2.2.1; dsimp only [cr]; omega
            have hcr_eq : s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws) = cr := by
              dsimp only [cr]; simp only [hp1_n]
            have hcr0_eq : (BitVec.setWidth 64
                (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws))).toNat = cr.toNat := by
              rw [bv64_setWidth_32, hcr_eq]
            have hcr_b0 : (BitVec.setWidth 64
                (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws))).toNat <
                s.core.arena.length := by rw [hcr0_eq]; omega
            have hcr2_eq : (BitVec.setWidth 64
                (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws)) + 2).toNat =
                cr.toNat + 2 := by
              change (BitVec.setWidth 64 _ + 2#64).toNat = _; rw [hcr_eq]; simp only [bv_c0]; omega
            have hcr_b2 : (BitVec.setWidth 64
                (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws)) + 2).toNat <
                s.core.arena.length := by rw [hcr2_eq]; omega
            have hsz_cr : (s.core.arena[cr.toNat + 2]'(by omega)).toNat =
                fullArenaClauseSizeCore s.core cr.toNat := by
              unfold fullArenaClauseSizeCore
              rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
            have hcr_sz_le : cr.toNat + 3 + (s.core.arena[cr.toNat + 2]'(by omega)).toNat ≤
                s.core.arena.length := by rw [hsz_cr]; omega
            c0_hfast
            · have hng_cr : fullArenaClauseGarbCore s.core cr.toNat = false := by
                unfold fullArenaClauseGarbCore fullArenaHdrCore
                rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                have h1 : s.core.arena[(BitVec.setWidth 64
                    (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws))).toNat]'hcr_b0 &&&
                    (524288#32 ||| 4194304#32) = 0#32 := by assumption
                exact FullBvaFwdHelpers.garb_false_of_and_garb_red_eq_zero (by
                  simpa only [hcr0_eq] using h1)
              clear hQ ihs hJend
              refine wp_loop_inv
                (fun (resk, k, ()) mk => ∃ rpk mck tck tlk antk sigk shrkk,
                  k.toNat ≤ (s.core.arena[cr.toNat + 2]'(by omega)).toNat ∧
                  tck ≤ s.core.cur_vars ∧ tlk ≤ s.core.cur_vars ∧
                  FullDenseInvNoLm c F0 F_cur (mkSt rpk mck tck tlk antk sigk shrkk) ∧
                  (∀ i < tck, (mck[i]?.getD 0#32).toNat < c.max_vars) ∧
                  (∀ i < tlk, (shrkk[i]?.getD 0#32).toNat < c.max_vars) ∧
                  (FullMem c (mkSt rpk mck tck tlk antk sigk shrkk) ⋆ R) mk)
                (fun (_, k, _) _ => (s.core.arena[cr.toNat + 2]'(by omega)).toNat - k.toNat)
                (fun Jk hJk => by
                  c0_hfast; exact hJk (res1, 0#32, ()) m
                    ⟨rpp, mcp, tcp, tlp, antp - 1#64, sigp, shrkp, Nat.zero_le _, htcp, htlp,
                     hinvp1, hmcp_ok, hshrkp_ok, hm_flat⟩)
                (fun Jk (resk, k, ()) mk ⟨rpk, mck, tck, tlk, antk, sigk, shrkk, hk_le, htck, htlk,
                    hinvk, hmck_ok, hshrkk_ok, hmk⟩ ihk => ?_)
              dsimp only [mkSt] at hmk
              c0_hsplit
              · have hk_lt : k.toNat < (s.core.arena[cr.toNat + 2]'(by omega)).toNat := by
                  have h1 : k.toNat < (s.core.arena[(BitVec.setWidth 64
                      (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws)) +
                      2).toNat]'hcr_b2).toNat := by assumption
                  simpa only [hcr2_eq] using h1
                have hk1 : (k + 1#32).toNat = k.toNat + 1 := by simp only [bv_c0]; omega
                c0_hsplit
                · have hcrk_b : (BitVec.setWidth 64
                      (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws)) + 3 +
                      BitVec.setWidth 64 k).toNat < s.core.arena.length := by
                    change (BitVec.setWidth 64 _ + 3#64 + BitVec.setWidth 64 k).toNat < _
                    rw [hcr_eq]; simp only [bv_c0]; omega
                  have hol_mem : (s.core.arena[cr.toNat + 3 + k.toNat]'(by omega)).toNat ∈
                      fullArenaClauseLitsCore s.core cr.toNat :=
                    List.mem_of_getElem? (FullBvaFwdHelpers.fullArenaClauseLitsCore_getElem
                      (by rw [← hsz_cr]; exact hk_lt) (by omega))
                  have hol_lt := hinv.2.1.arena.lits_lt cr.toNat hcr_ref hng_cr _ hol_mem
                  have hcrk_eq : (BitVec.setWidth 64 cr + 3 + BitVec.setWidth 64 k).toNat =
                      cr.toNat + 3 + k.toNat := by
                    change (BitVec.setWidth 64 cr + 3#64 + BitVec.setWidth 64 k).toNat = _
                    simp only [bv_c0]; omega
                  c0_hfast
                  · c0_call hHop2
                    refine ⟨c, F0, F_cur, mkSt rpk mck tck tlk antk sigk shrkk, R, rfl, hinvk, ?_,
                      htck, htlk, hmck_ok, hshrkk_ok, hmk,
                      fun r1 rp1 mc1 tc1 tl1 ant1 sig1 shrk1 m1 hinv1 htc1 htl1 hmc1 hshrk1 _
                          hm1 => ?_⟩
                    · simpa only [hcr_eq, hcrk_eq] using hol_lt
                    · c0_hfast
                      exact ihk (resk + r1, k + 1#32, ()) m1 (by dsimp only; rw [hk1]; omega)
                        ⟨rp1, mc1, tc1, tl1, ant1, sig1, shrk1, by rw [hk1]; omega, htc1, htl1,
                         hinv1, hmc1, hshrk1, hm1⟩
                  · exact ihk (resk, k + 1#32, ()) mk (by dsimp only; rw [hk1]; omega)
                      ⟨rpk, mck, tck, tlk, antk, sigk, shrkk, by rw [hk1]; omega, htck, htlk,
                       hinvk, hmck_ok, hshrkk_ok, hmk⟩
                · c0_hfast
                  exact ihp (resk, p + 1 + 1, ()) mk (by dsimp only; rw [hp2_n]; omega)
                    ⟨rpk, mck, tck, tlk, antk, sigk, shrkk, by rw [hp2_n]; omega,
                     by rw [hp2_n]; omega, htck, htlk, hinvk, hmck_ok, hshrkk_ok,
                     by rw [hp2_n, show off0 + sz0 - (p.toNat + 2) = off0 + sz0 - p.toNat - 2
                          by omega]; exact hrem_next, hmk⟩
              · c0_hfast
                exact ihp (resk, p + 1 + 1, ()) mk (by dsimp only; rw [hp2_n]; omega)
                  ⟨rpk, mck, tck, tlk, antk, sigk, shrkk, by rw [hp2_n]; omega,
                   by rw [hp2_n]; omega, htck, htlk, hinvk, hmck_ok, hshrkk_ok,
                   by rw [hp2_n, show off0 + sz0 - (p.toNat + 2) = off0 + sz0 - p.toNat - 2
                        by omega]; exact hrem_next, hmk⟩
            · exact ihp (res1, p + 1 + 1, ()) m (by dsimp only; rw [hp2_n]; omega)
                ⟨rpp, mcp, tcp, tlp, antp - 1#64, sigp, shrkp, by rw [hp2_n]; omega,
                 by rw [hp2_n]; omega, htcp, htlp, hinvp1, hmcp_ok, hshrkp_ok,
                 by rw [hp2_n, show off0 + sz0 - (p.toNat + 2) = off0 + sz0 - p.toNat - 2
                      by omega]; exact hrem_next, hm_flat⟩
          · exfalso
            have ⟨h2le, _⟩ := FullBvaFwdHelpers.bva_slice_occ_info hrem (by omega) hp_ws
              (by assumption)
            have hge : ¬ (p.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 <
                ((s.core.wvec[2 * sl.toNat % 2 ^ 64]'(by rw [hmod0]; omega)).toNat +
                 (s.core.wvec[(2 * sl.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                   rw [hmod1]; omega)).toNat) % 2 ^ 64 := by assumption
            rw [hend_mod, hp1_mod] at hge; omega
        all_goals
          exact ihs (res1, sgn + 1#32, ()) mlp (by simp only [bv_c0]; omega)
            ⟨rpp, mcp, tcp, tlp, antp, sigp, shrkp, by simp only [bv_c0]; omega, htcp, htlp, hinvp,
             hmcp_ok, hshrkp_ok, hmlp⟩
      · exact hJend ⟨rp, mc, tc, tl, ant, sig, shrk⟩ ml
          ⟨htc, htl, hinv_s, hmc_ok, hshrk_ok, hml⟩
      · exact hJend ⟨rp, mc, tc, tl, ant, sig, shrk⟩ ml
          ⟨htc, htl, hinv_s, hmc_ok, hshrk_ok, hml⟩
  · c0_hsteps
    · exact hJ0 1#64 m rfl
    · exact hJ0 0#64 m rfl

/-! ## 6. Max-Degree Binary Heap Sifts (`full_fheap_up_wp`, `full_fheap_down_wp`) -/

theorem full_fheap_up_wp (Γ : Env) :
    ∀ args m Q X, fullFheapUpSpec args m Q X → Func.wp Γ full_fheap_up_body args m Q X := by
  rintro ⟨hp_ptr, ps_ptr, wvec_ptr, p0, ⟨⟩⟩ m Q X
    ⟨nlits, hp0, ps0, wvec, R, hhp_len, hps_len, hwv_len, hnl_lt, hp0_lt, hhp0_ok, hm, hQ⟩
  have hi32 : i32.bytes = 4 := rfl
  have hl0_lt : (hp0[p0.toNat]'(by omega)).toNat < nlits := by
    have := hhp0_ok p0.toNat (Nat.le_refl _)
    rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
  have h2l0 : ((BitVec.setWidth 64 (hp0[p0.toNat]'(by omega)) <<< (1 : Nat)) + 1#64).toNat =
      2 * (hp0[p0.toNat]'(by omega)).toNat + 1 := by c0_bound
  c0_hsteps_nogrp
  refine wp_join_state1 (t := i32) (α := BitVec 32 × List (BitVec 32) × List (BitVec 32))
    (fun st => st.1)
    (fun ⟨pf, hpf, psf⟩ mf =>
      pf.toNat ≤ p0.toNat ∧ hpf.length = hp0.length ∧ psf.length = ps0.length ∧
      (∀ i ≤ p0.toNat, ∃ j ≤ p0.toNat, hpf[i]? = hp0[j]?) ∧
      (∀ i, p0.toNat < i → hpf[i]? = hp0[i]?) ∧
      (array (t := i32) hp_ptr hpf ⋆ array (t := i32) ps_ptr psf ⋆
        array (t := i32) wvec_ptr wvec ⋆ R) mf)
    (fun _ ⟨pf, hpf, psf⟩ mf ⟨hpf_le, hhpf_len, hpsf_len, hsubf, houtf, hmf⟩ => ?_)
    (fun Jend hJend => ?_)
  · clear m hm; c0_hsteps
    have hset : ∀ x : BitVec 32, (BitVec.setWidth 64 x).toNat = x.toNat := bv64_setWidth_32
    let hpf' := hpf.set pf.toNat (hp0[p0.toNat]'(by omega))
    let psf' := psf.set (hp0[p0.toNat]'(by omega)).toNat pf
    have hmem : (array (t := i32) hp_ptr hpf' ⋆ array (t := i32) ps_ptr psf' ⋆
        array (t := i32) wvec_ptr wvec ⋆ R) m := by
      simp only [sep_emp] at hm
      exact sep_ac (show (array (t := i32) ps_ptr psf' ⋆ (array (t := i32) hp_ptr hpf' ⋆
          (array (t := i32) wvec_ptr wvec ⋆ R))) m from by
        dsimp only [hpf', psf']; simpa only [hset] using hm)
    refine hQ hpf' psf' _ (by simp [hpf', hhpf_len]) (by simp [psf', hpsf_len])
      (fun i hi => ?_) (fun i hi => ?_) hmem
    · dsimp only [hpf']; by_cases hie : i = pf.toNat
      · subst hie
        refine ⟨p0.toNat, Nat.le_refl _, ?_⟩
        rw [List.getElem?_set_self (by omega), List.getElem?_eq_getElem (by omega)]
      · rw [List.getElem?_set_ne (Ne.symm hie)]; exact hsubf i hi
    · dsimp only [hpf']; rw [List.getElem?_set_ne (by omega)]; exact houtf i hi
  · refine wp_loop_inv
      (fun (p, ()) ml => ∃ hpl psl,
        p.toNat ≤ p0.toNat ∧ hpl.length = hp0.length ∧ psl.length = ps0.length ∧
        (∀ i ≤ p0.toNat, ∃ j ≤ p0.toNat, hpl[i]? = hp0[j]?) ∧
        (∀ i, p0.toNat < i → hpl[i]? = hp0[i]?) ∧
        (array (t := i32) hp_ptr hpl ⋆ array (t := i32) ps_ptr psl ⋆
          array (t := i32) wvec_ptr wvec ⋆ R) ml)
      (fun (p, ()) _ => p.toNat)
      (fun J hJ => by
        c0_hsteps; exact hJ (p0, ()) m ⟨hp0, ps0, Nat.le_refl _, rfl, rfl,
          fun i hi => ⟨i, hi, rfl⟩, fun _ _ => rfl, hm⟩)
      (fun J (p, ()) ml ⟨hpl, psl, hp_le, hhpl_len, hpsl_len, hsub, hout, hml⟩ ih => ?_)
    clear m hm
    have hset : ∀ x : BitVec 32, (BitVec.setWidth 64 x).toNat = x.toNat := bv64_setWidth_32
    c0_hsteps
    · have hp_pos : 0 < p.toNat := by c0_bound
      have hpp_nat : ((p - 1) >>> (1 : Nat)).toNat = (p.toNat - 1) / 2 := by c0_bound
      have hpp_lt : ((p - 1) >>> (1 : Nat)).toNat < p.toNat := by omega
      have hpl_ok : (hpl[((p - 1) >>> (1 : Nat)).toNat]'(by omega)).toNat < nlits := by
        obtain ⟨j, hj, heq⟩ := hsub ((p - 1) >>> (1 : Nat)).toNat (by omega)
        have h1 := hhp0_ok j hj
        rw [← heq, List.getElem?_eq_getElem (by omega), Option.getD_some] at h1; exact h1
      have hpl_ok_sw : (hpl[(BitVec.setWidth 64 ((p - 1) >>> (1 : Nat))).toNat]'(by
          simp only [hset]; omega)).toNat < nlits := by simp only [hset]; exact hpl_ok
      c0_hsteps
      · exact hJend ⟨p, hpl, psl⟩ ml ⟨hp_le, hhpl_len, hpsl_len, hsub, hout, hml⟩
      · let hpl' := hpl.set p.toNat (hpl[((p - 1) >>> (1 : Nat)).toNat]'(by omega))
        let psl' := psl.set (hpl[((p - 1) >>> (1 : Nat)).toNat]'(by omega)).toNat p
        have hmem : (array (t := i32) hp_ptr hpl' ⋆ array (t := i32) ps_ptr psl' ⋆
            array (t := i32) wvec_ptr wvec ⋆ R) m := by
          simp only [sep_emp] at hm
          exact sep_ac (show (array (t := i32) ps_ptr psl' ⋆ (array (t := i32) hp_ptr hpl' ⋆
              (array (t := i32) wvec_ptr wvec ⋆ R))) m from by
            dsimp only [hpl', psl']; simpa only [hset] using hm)
        refine ih ((p - 1) >>> (1 : Nat), ()) _ hpp_lt
          ⟨hpl', psl', by omega, by simp [hpl', hhpl_len], by simp [psl', hpsl_len],
           fun i hi => ?_,
           fun i hi => by
             dsimp only [hpl']; rw [List.getElem?_set_ne (by omega)]; exact hout i hi,
           hmem⟩
        dsimp only [hpl']
        by_cases hie : i = p.toNat
        · subst hie
          obtain ⟨j, hj, heq⟩ := hsub ((p - 1) >>> (1 : Nat)).toNat (by omega)
          refine ⟨j, hj, ?_⟩
          rw [List.getElem?_set_self (by omega), ← heq, List.getElem?_eq_getElem (by omega)]
        · rw [List.getElem?_set_ne (Ne.symm hie)]; exact hsub i hi
    · exact hJend ⟨p, hpl, psl⟩ ml ⟨hp_le, hhpl_len, hpsl_len, hsub, hout, hml⟩

theorem full_fheap_down_wp (Γ : Env) :
    ∀ args m Q X, fullFheapDownSpec args m Q X → Func.wp Γ full_fheap_down_body args m Q X := by
  rintro ⟨hp_ptr, ps_ptr, wvec_ptr, p0, n, ⟨⟩⟩ m Q X
    ⟨nlits, hp0, ps0, wvec, R, hhp_len, hps_len, hwv_len, hnl_lt, hp0_lt, hn_le, hhp0_ok, hm, hQ⟩
  have hi32 : i32.bytes = 4 := rfl
  have hset : ∀ x : BitVec 32, (BitVec.setWidth 64 x).toNat = x.toNat := bv64_setWidth_32
  have hl0_lt : (hp0[p0.toNat]'(by omega)).toNat < nlits := by
    have := hhp0_ok p0.toNat hp0_lt
    rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
  have h2l0 : ((BitVec.setWidth 64 (hp0[p0.toNat]'(by omega)) <<< (1 : Nat)) + 1#64).toNat =
      2 * (hp0[p0.toNat]'(by omega)).toNat + 1 := by c0_bound
  c0_hsteps_nogrp
  refine wp_join_state1 (t := i32) (α := BitVec 32 × List (BitVec 32) × List (BitVec 32))
    (fun st => st.1)
    (fun ⟨pf, hpf, psf⟩ mf =>
      pf.toNat < n.toNat ∧ hpf.length = hp0.length ∧ psf.length = ps0.length ∧
      (∀ i < n.toNat, ∃ j < n.toNat, hpf[i]? = hp0[j]?) ∧
      (∀ i, n.toNat ≤ i → hpf[i]? = hp0[i]?) ∧
      (array (t := i32) hp_ptr hpf ⋆ array (t := i32) ps_ptr psf ⋆
        array (t := i32) wvec_ptr wvec ⋆ R) mf)
    (fun _ ⟨pf, hpf, psf⟩ mf ⟨hpf_lt, hhpf_len, hpsf_len, hsubf, houtf, hmf⟩ => ?_)
    (fun Jend hJend => ?_)
  · clear m hm; c0_hsteps
    let hpf' := hpf.set pf.toNat (hp0[p0.toNat]'(by omega))
    let psf' := psf.set (hp0[p0.toNat]'(by omega)).toNat pf
    have hmem : (array (t := i32) hp_ptr hpf' ⋆ array (t := i32) ps_ptr psf' ⋆
        array (t := i32) wvec_ptr wvec ⋆ R) m := by
      simp only [sep_emp] at hm
      exact sep_ac (show (array (t := i32) ps_ptr psf' ⋆ (array (t := i32) hp_ptr hpf' ⋆
          (array (t := i32) wvec_ptr wvec ⋆ R))) m from by
        dsimp only [hpf', psf']; simpa only [hset] using hm)
    refine hQ hpf' psf' _ (by simp [hpf', hhpf_len]) (by simp [psf', hpsf_len])
      (fun i hi => ?_) (fun i hi => ?_) hmem
    · dsimp only [hpf']; by_cases hie : i = pf.toNat
      · subst hie; refine ⟨p0.toNat, hp0_lt, ?_⟩
        rw [List.getElem?_set_self (by omega), List.getElem?_eq_getElem (by omega)]
      · rw [List.getElem?_set_ne (Ne.symm hie)]; exact hsubf i hi
    · dsimp only [hpf']; rw [List.getElem?_set_ne (by omega)]; exact houtf i hi
  · refine wp_loop_inv
      (fun (p, ()) ml => ∃ hpl psl,
        p.toNat < n.toNat ∧ hpl.length = hp0.length ∧ psl.length = ps0.length ∧
        (∀ i < n.toNat, ∃ j < n.toNat, hpl[i]? = hp0[j]?) ∧
        (∀ i, n.toNat ≤ i → hpl[i]? = hp0[i]?) ∧
        (array (t := i32) hp_ptr hpl ⋆ array (t := i32) ps_ptr psl ⋆
          array (t := i32) wvec_ptr wvec ⋆ R) ml)
      (fun (p, ()) _ => n.toNat - p.toNat)
      (fun J hJ => by
        c0_hsteps; exact hJ (p0, ()) m ⟨hp0, ps0, hp0_lt, rfl, rfl,
          fun i hi => ⟨i, hi, rfl⟩, fun _ _ => rfl, hm⟩)
      (fun J (p, ()) ml ⟨hpl, psl, hp_lt, hhpl_len, hpsl_len, hsub, hout, hml⟩ ih => ?_)
    clear m hm
    have hcp_nat : ((p <<< (1 : Nat)) + 1).toNat = 2 * p.toNat + 1 := by c0_bound
    c0_hsteps_nogrp
    · exact hJend ⟨p, hpl, psl⟩ ml ⟨hp_lt, hhpl_len, hpsl_len, hsub, hout, hml⟩
    · have hcp_lt : ((p <<< (1 : Nat)) + 1).toNat < n.toNat := by c0_bound
      have hcl_ok : (hpl[((p <<< (1 : Nat)) + 1).toNat]'(by omega)).toNat < nlits := by
        obtain ⟨j, hj, heq⟩ := hsub ((p <<< (1 : Nat)) + 1).toNat hcp_lt
        have h1 := hhp0_ok j hj
        rw [← heq, List.getElem?_eq_getElem (by omega), Option.getD_some] at h1; exact h1
      have hcl_ok_sw : (hpl[(BitVec.setWidth 64 ((p <<< (1 : Nat)) + 1)).toNat]'(by
          simp only [hset]; omega)).toNat < nlits := by simp only [hset]; exact hcl_ok
      c0_hsteps_nogrp
      refine wp_join_state (α := BitVec 32 × BitVec 32 × BitVec 32)
        (fun ⟨cp', cl', cd'⟩ => (cp', cl', cd', ()))
        (fun ⟨cp', cl', _⟩ mf =>
          p.toNat < cp'.toNat ∧ cp'.toNat < n.toNat ∧
          (∃ j < n.toNat, some cl' = hp0[j]?) ∧ cl'.toNat < nlits ∧ ml = mf)
        (fun _ ⟨cp', cl', cd'⟩ mf ⟨hgt_p, hcp'_lt, hcl'_mem, hcl'_lt, hmf⟩ => ?_)
        (fun Jc hJc => ?_)
      · rcases hmf with rfl
        c0_hsteps
        · exact hJend ⟨p, hpl, psl⟩ ml ⟨hp_lt, hhpl_len, hpsl_len, hsub, hout, hml⟩
        · let hpl' := hpl.set p.toNat cl'
          let psl' := psl.set cl'.toNat p
          refine ih (cp', ()) _ (by dsimp only; omega)
            ⟨hpl', psl', hcp'_lt, by simp [hpl', hhpl_len], by simp [psl', hpsl_len],
             fun i hi => ?_,
             fun i hi => by
               dsimp only [hpl']; rw [List.getElem?_set_ne (by omega)]; exact hout i hi,
             by dsimp only [hpl', psl'] at *; simp only [hset, sep_emp] at *; ecancel⟩
          dsimp only [hpl']
          by_cases hie : i = p.toNat
          · subst hie
            obtain ⟨j, hj, heq⟩ := hcl'_mem
            refine ⟨j, hj, ?_⟩
            rw [List.getElem?_set_self (by omega), heq]
          · rw [List.getElem?_set_ne (Ne.symm hie)]; exact hsub i hi
      · c0_hsteps
        · have hcp1_lt : (((p <<< (1 : Nat)) + 1) + 1).toNat < n.toNat := by c0_bound
          have hsl_ok :
              (hpl[(((p <<< (1 : Nat)) + 1) + 1).toNat]'(by omega)).toNat < nlits := by
            obtain ⟨j, hj, heq⟩ := hsub (((p <<< (1 : Nat)) + 1) + 1).toNat hcp1_lt
            have h1 := hhp0_ok j hj
            rw [← heq, List.getElem?_eq_getElem (by omega), Option.getD_some] at h1; exact h1
          have hsl_ok_sw :
              (hpl[(BitVec.setWidth 64 (((p <<< (1 : Nat)) + 1) + 1)).toNat]'(by
                simp only [hset]; omega)).toNat < nlits := by simp only [hset]; exact hsl_ok
          c0_hsteps
          · obtain ⟨j, hj, heq⟩ := hsub (((p <<< (1 : Nat)) + 1) + 1).toNat hcp1_lt
            exact hJc ⟨_, _, _⟩ ml ⟨by c0_bound, hcp1_lt,
              ⟨j, hj, by simp only [hset]; rw [← heq, List.getElem?_eq_getElem (by omega)]⟩,
              by simp only [hset]; exact hsl_ok, rfl⟩
          · obtain ⟨j, hj, heq⟩ := hsub ((p <<< (1 : Nat)) + 1).toNat hcp_lt
            exact hJc ⟨_, _, _⟩ ml ⟨by c0_bound, hcp_lt,
              ⟨j, hj, by simp only [hset]; rw [← heq, List.getElem?_eq_getElem (by omega)]⟩,
              by simp only [hset]; exact hcl_ok, rfl⟩
        · obtain ⟨j, hj, heq⟩ := hsub ((p <<< (1 : Nat)) + 1).toNat hcp_lt
          exact hJc ⟨_, _, _⟩ ml ⟨by c0_bound, hcp_lt,
            ⟨j, hj, by simp only [hset]; rw [← heq, List.getElem?_eq_getElem (by omega)]⟩,
            by simp only [hset]; exact hcl_ok, rfl⟩
    · exact absurd (by assumption : true = false) (by decide)

end LeanQbe.T.Examples.Kissat.FullBvaHeap
