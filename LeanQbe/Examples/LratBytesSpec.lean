module

public import LeanQbe.Examples.LratBytes
public import LeanQbe.Examples.LratRupLemmas
public import LeanQbe.AbiLemmas
public import Kraken.Bedrock2.Test.LratTrimCheckProof
import all Kraken.Mem
import all Kraken.Separation

/-!
# Shared specifications, pure executable mirror, and `region` lemmas for `LratBytes`

Defines:
1. `lratBytesFns_wf`: well-formedness (`Func.Wf`) of all 6 functions in `lratBytesFns`.
2. `loadub_At` and `region` ↔ `byte1Array` / `int4Array` / `word8Array` / `ZeroTermInts` bridges.
3. The 100% structurally recursive pure mirror `runLratCheckBytes` (`parseBodyPure`,
   `readLeb128Pure`, `readAddLitsPure`, `rupCheckPure`, `checkPrfPure`).
4. `WorkCfg`, `WorkState`, and the exact contracts for all 5 internal callees
   (`lbParseDimacsHeaderSpec`, `lbParseDimacsBodySpec`, `lbReadAddLitsSpec`,
   `lbRupCheckSpec`, `lbCheckPrfSpec`) plus `lratCheckBytesExactSpec`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.LratBytes

open Std Std.ExtHashMap Std.Sat
open Std.Tactic.BVDecide.LRAT.Internal
open Kraken.Bedrock2.Test
open LeanQbe.LratRup

/-! ## 1. Well-formedness of `lratBytesFns` -/

theorem lbParseDimacsHeader_wf : Func.Wf lbParseDimacsHeader := by
  unfold lbParseDimacsHeader skipWsCommentsQbe skipWs1Qbe readDimacsNat isWsByte; wf_tac

theorem lbParseDimacsBody_wf : Func.Wf lbParseDimacsBody := by
  unfold lbParseDimacsBody skipWsCommentsQbe readDimacsNat isWsByte; wf_tac

theorem lbReadAddLits_wf : Func.Wf lbReadAddLits := by
  unfold lbReadAddLits readLeb128; wf_tac

theorem lbRupCheck_wf : Func.Wf lbRupCheck := by
  unfold lbRupCheck rupPhase1 rupInner readLeb128 assignedLit assignLitChecked backtrack; wf_tac

theorem lbCheckPrf_wf : Func.Wf lbCheckPrf := by
  unfold lbCheckPrf readLeb128; wf_tac

theorem lratCheckBytes_wf : Func.Wf lratCheckBytes := by
  unfold lratCheckBytes; wf_tac

theorem lratBytesFns_wf : ∀ f ∈ lratBytesFns, Func.Wf f.body := by
  intro f hf
  simp only [lratBytesFns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lbParseDimacsHeader_wf
  · exact lbParseDimacsBody_wf
  · exact lbReadAddLits_wf
  · exact lbRupCheck_wf
  · exact lbCheckPrf_wf
  · exact lratCheckBytes_wf

/-! ## 2. Byte-stream `loadub` and `region` ↔ Kraken array bridges -/

theorem toBytes_u8 (b : UInt8) : Int.toBytes 1 (b.toNat : Int) = [b] := by
  have hb := b.toNat_lt
  simp only [Int.toBytes, Int.take]
  rw [Int.emod_eq_of_lt (by omega) (by omega)]
  simp

theorem loadub_At {base : Val} {bs : List UInt8} {i : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hi : i < bs.length) (hlen : bs.length ≤ 2 ^ 64)
    (hm : (Eq (bs.At base) ⋆ R) m) :
    loadVal m .l .b false (base + BitVec.ofNat 64 i) = some (BitVec.ofNat 64 bs[i].toNat) := by
  have hsplit : bs = bs.take i ++ ([bs[i]] ++ bs.drop (i + 1)) := by
    rw [List.singleton_append, ← List.drop_eq_getElem_cons hi, List.take_append_drop]
  have heq : Eq (bs.At base) =
      (Eq ((Int.toBytes 1 (bs[i].toNat : Int)).At (base + BitVec.ofNat 64 i)) ⋆
        (Eq ((bs.take i).At base) ⋆
          Eq ((bs.drop (i + 1)).At (base + BitVec.ofNat 64 i + 1)))) := by
    conv => lhs; rw [hsplit]
    rw [eq_append_At base (bs.take i) ([bs[i]] ++ bs.drop (i + 1))
          (by simp [List.length_take_of_le (Nat.le_of_lt hi)]; omega),
        List.length_take_of_le (Nat.le_of_lt hi),
        eq_append_At (base + BitVec.ofNat 64 i) [bs[i]] (bs.drop (i + 1))
          (by simp; omega),
        toBytes_u8]
    simp only [List.length_singleton]
    ac_rfl
  have hm' : (Eq ((Int.toBytes 1 (bs[i].toNat : Int)).At (base + BitVec.ofNat 64 i)) ⋆
      ((Eq ((bs.take i).At base) ⋆ Eq ((bs.drop (i + 1)).At (base + BitVec.ofNat 64 i + 1))) ⋆ R)) m := by
    rw [heq] at hm; exact sep_cast hm (by ac_rfl)
  rw [loadVal_toBytes (s := .b) hm']
  have hb := bs[i].toNat_lt
  simp only [Sz.bytes, Int.take, Cls.trunc, Sz.extend]
  rw [Int.emod_eq_of_lt (by omega) (by omega)]
  exact congrArg some (BitVec.eq_of_toNat_eq (by simp))

theorem byte1Array_to_region {a : Val} {xs : List Val} {f : Mem 64}
    (h : xs.length ≤ 2 ^ 64) (hf : byte1Array a xs f) :
    region a xs.length f := by
  rw [byte1Array_eq a xs h] at hf
  exact ⟨bytesN 1 xs, by simp [bytesN_length], hf.symm⟩

theorem int4Array_to_region {a : Val} {xs : List Val} {f : Mem 64}
    (h : 4 * xs.length ≤ 2 ^ 64) (hf : int4Array a xs f) :
    region a (4 * xs.length) f := by
  rw [int4Array_eq a xs h] at hf
  exact ⟨bytesN 4 xs, by simp [bytesN_length], hf.symm⟩

theorem word8Array_to_region {a : Val} {xs : List Val} {f : Mem 64}
    (h : 8 * xs.length ≤ 2 ^ 64) (hf : word8Array a xs f) :
    region a (8 * xs.length) f := by
  rw [word8Array_eq a xs h] at hf
  exact ⟨bytesN 8 xs, by simp [bytesN_length], hf.symm⟩

theorem zeroTermInts_to_region {a : Val} {xs : List Val} {f : Mem 64}
    (h : 4 * (xs.length + 1) ≤ 2 ^ 64) (hf : ZeroTermInts a xs f) :
    region a (4 * (xs.length + 1)) f := by
  unfold ZeroTermInts at hf
  have hr := int4Array_to_region (by simpa using h) hf
  simpa using hr

private theorem toBytes_ofBytes_toNat {n : Nat} {bs : List UInt8}
    (hn : n = 1 ∨ n = 4 ∨ n = 8) (hl : bs.length = n) :
    Int.toBytes n ((BitVec.ofInt 64 (Int.ofBytes bs)).toNat : Int) = bs := by
  rw [← Int.toBytes_emod]
  have hdvd : (2 ^ (8 * n) : Int) ∣ ((2 ^ 64 : Nat) : Int) := by
    rcases hn with rfl | rfl | rfl <;> decide
  have hdvd2 : (2 ^ (8 * n) : Int) ∣ (2 ^ 64 : Int) := by
    rcases hn with rfl | rfl | rfl <;> decide
  have h1 : ((BitVec.ofInt 64 (Int.ofBytes bs)).toNat : Int).take (8 * n) =
      (Int.ofBytes bs).take (8 * n) := by
    simp only [Int.take]
    rw [← BitVec.toInt_emod_two_pow, Int.emod_emod_of_dvd _ hdvd2, BitVec.toInt_ofInt,
        ← Int.emod_emod_of_dvd _ hdvd, Int.bmod_emod, Int.emod_emod_of_dvd _ hdvd]
  rw [h1, Int.toBytes_emod, ← hl]
  exact Int.toBytes_ofBytes_all bs

private theorem region_to_bytes_array {n : Nat} (arr : Val → List Val → Mem 64 → Prop)
    (hnil : ∀ a, arr a [] = emp)
    (hcons : ∀ a v vs, arr a (v :: vs) = (Eq ((Int.toBytes n v.toNat).At a) ⋆ arr (a + BitVec.ofNat 64 n) vs))
    (hn : n = 1 ∨ n = 4 ∨ n = 8) (a : Val) (k : Nat) (hk : n * k ≤ 2 ^ 64) :
    ∀ {f : Mem 64}, region a (n * k) f → ∃ xs : List Val, xs.length = k ∧ arr a xs f := by
  induction k generalizing a with
  | zero =>
    intro f hf
    simp only [Nat.mul_zero, region_zero] at hf
    exact ⟨[], rfl, by rw [hnil]; exact hf⟩
  | succ k ih =>
    intro f hf
    have hmul : n * (k + 1) = n + n * k := by rw [Nat.mul_succ, Nat.add_comm]
    have hnk : n * k ≤ 2 ^ 64 := Nat.le_trans (Nat.le_add_left _ _) (hmul ▸ hk)
    have hnle : n + n * k ≤ 2 ^ 64 := hmul ▸ hk
    have hsp : region a (n + n * k) f := hmul ▸ hf
    rw [region_split hnle] at hsp
    obtain ⟨f1, f2, hu, hd, ⟨bs1, hl1, rfl⟩, hf2⟩ := hsp
    obtain ⟨xs, hxs, h2⟩ := ih (a + BitVec.ofNat 64 n) hnk hf2
    let v : Val := BitVec.ofInt 64 (Int.ofBytes bs1)
    have hv : Int.toBytes n v.toNat = bs1 := toBytes_ofBytes_toNat hn hl1
    refine ⟨v :: xs, by simp [hxs], ?_⟩
    rw [hcons, hv]
    exact ⟨_, f2, hu, hd, rfl, h2⟩

theorem region_to_byte1Array {a : Val} (k : Nat) (hk : k ≤ 2 ^ 64) {f : Mem 64}
    (hf : region a k f) :
    ∃ xs : List Val, xs.length = k ∧ byte1Array a xs f :=
  region_to_bytes_array byte1Array (fun _ => rfl) (fun _ _ _ => rfl)
    (Or.inl rfl) a k (by omega) (by simpa using hf)

theorem region_to_int4Array {a : Val} (k : Nat) (hk : 4 * k ≤ 2 ^ 64) {f : Mem 64}
    (hf : region a (4 * k) f) :
    ∃ xs : List Val, xs.length = k ∧ int4Array a xs f :=
  region_to_bytes_array int4Array (fun _ => rfl) (fun _ _ _ => rfl)
    (Or.inr (Or.inl rfl)) a k hk hf

theorem region_to_word8Array {a : Val} (k : Nat) (hk : 8 * k ≤ 2 ^ 64) {f : Mem 64}
    (hf : region a (8 * k) f) :
    ∃ xs : List Val, xs.length = k ∧ word8Array a xs f :=
  region_to_bytes_array word8Array (fun _ => rfl) (fun _ _ _ => rfl)
    (Or.inr (Or.inr rfl)) a k hk hf

theorem region_pop_int4 {a : Val} {rem : Nat} (hrem : 0 < rem)
    (hfit : 4 * rem ≤ 2 ^ 64) {f : Mem 64} (hf : region a (4 * rem) f) :
    ∃ v0 : Val, (int4 a v0 ⋆ region (a + 4) (4 * (rem - 1))) f := by
  have heq : 4 * rem = 4 * 1 + 4 * (rem - 1) := by omega
  rw [heq, region_split (by omega)] at hf
  obtain ⟨f1, f2, hu, hd, hf1, hf2⟩ := hf
  obtain ⟨xs, hxs, h1⟩ := region_to_int4Array 1 (by omega) hf1
  rcases xs with _ | ⟨v0, _ | _⟩ <;> simp at hxs
  simp only [int4Array_cons, int4Array_nil, sep_emp] at h1
  exact ⟨v0, f1, f2, hu, hd, h1, by simpa using hf2⟩

theorem region_pop_store_int4 {wcur : Val} {rem : Nat} (v : Val) {R : Mem 64 → Prop} {m : Mem 64}
    (hrem : 0 < rem) (hfit : 4 * rem ≤ 2 ^ 64)
    (hm : (region wcur (4 * rem) ⋆ R) m) :
    storeOk m .w wcur ∧
    (int4 wcur v ⋆ region (wcur + 4) (4 * (rem - 1)) ⋆ R) (storeMem m .w wcur v) := by
  obtain ⟨f_w, f_rest, hu, hd, hf_w, hf_rest⟩ := hm
  obtain ⟨v0, hv0_cell⟩ := region_pop_int4 hrem hfit hf_w
  have hm_cell : ((int4 wcur v0 ⋆ region (wcur + 4) (4 * (rem - 1))) ⋆ R) m :=
    ⟨f_w, f_rest, hu, hd, hv0_cell, hf_rest⟩
  rw [sep_assoc] at hm_cell
  obtain ⟨ok, hm'⟩ := LratRup.store_int4 v hm_cell
  exact ⟨ok, sep_cast hm' (by ac_rfl)⟩

theorem region_merge_eq {a : Val} {n1 n2 n : Nat}
    (hsum : n1 + n2 = n) (hfit : n ≤ 2 ^ 64) :
    (region a n1 ⋆ region (a + BitVec.ofNat 64 n1) n2) = region a n := by
  subst hsum
  exact (region_split (a := a) (n1 := n1) (n2 := n2) hfit).symm

/-! ### Shared BitVec, pointer, separation, and WP helpers -/

namespace ProofUtil
scoped macro "sep_ac" h:term : term => `(sep_cast $h (by ac_rfl))
end ProofUtil

open ProofUtil

theorem ptr_add_ofNat (base : Val) (a b : Nat) :
    base + BitVec.ofNat 64 a + BitVec.ofNat 64 b = base + BitVec.ofNat 64 (a + b) :=
  BitVec.eq_of_toNat_eq (by simp [BitVec.toNat_add]; omega)

theorem ptr_step_1 (base : Val) (i : Nat) :
    base + BitVec.ofNat 64 i + 1 = base + BitVec.ofNat 64 (i + 1) :=
  ptr_add_ofNat base i 1

theorem cursor_eq_iff {base : Val} {i j : Nat} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64) :
    base + BitVec.ofNat 64 i = base + BitVec.ofNat 64 j ↔ i = j := by
  constructor
  · intro h
    have h2 : BitVec.ofNat 64 i = BitVec.ofNat 64 j := by grind
    have h3 := congrArg BitVec.toNat h2
    simpa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using h3
  · rintro rfl; rfl

theorem bv64_u8_eq {b k : UInt8} :
    BitVec.ofNat 64 b.toNat = BitVec.ofNat 64 k.toNat ↔ b = k := by
  have hb := b.toNat_lt
  have hk := k.toNat_lt
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp [Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : k.toNat < 2 ^ 64)] at this
    exact UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq this)
  · rintro rfl; rfl

theorem bv_add_ofNat (a b : Nat) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) :=
  BitVec.eq_of_toNat_eq (by simp [BitVec.toNat_add])

theorem bv_sub_ofNat {a b : Nat} (hba : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) :=
  BitVec.eq_of_toNat_eq (by
    simp [BitVec.toNat_sub, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (by omega : b < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : a - b < 2 ^ 64)]; omega)

theorem bv_shl_ofNat {a k : Nat} (ha : a < 2 ^ 64) (_hk : k < 64) :
    BitVec.ofNat 64 a <<< k = BitVec.ofNat 64 (a <<< k) :=
  BitVec.eq_of_toNat_eq (by
    simp [BitVec.toNat_shiftLeft, Nat.mod_eq_of_lt ha])

theorem bv_shr_ofNat {a k : Nat} (ha : a < 2 ^ 64) (_hk : k < 64) :
    BitVec.ofNat 64 a >>> k = BitVec.ofNat 64 (a >>> k) :=
  BitVec.eq_of_toNat_eq (by
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt ha,
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha)])

theorem bv_shr_one {u : Nat} (hu : u < 2 ^ 64) :
    BitVec.ofNat 64 u >>> (1 : Nat) = BitVec.ofNat 64 (u / 2) := by
  simpa [Nat.shiftRight_eq_div_pow] using bv_shr_ofNat hu (by decide)

theorem bv_and_pow2_sub_one {a k : Nat} (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a &&& BitVec.ofNat 64 (2 ^ k - 1) = BitVec.ofNat 64 (a % 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le a _) ha)]
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_and, Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < 64
  · simp [hi, Bool.and_comm]
  · have hai : a.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [hi, hai]

theorem bv_and_one {u : Nat} (hu : u < 2 ^ 64) :
    BitVec.ofNat 64 u &&& (1 : Val) = BitVec.ofNat 64 (u % 2) :=
  bv_and_pow2_sub_one (k := 1) hu

theorem bv_align_pow2 {x k : Nat} (hk : k < 64) (hx : x < 2 ^ 64) :
    BitVec.ofNat 64 x &&& (-(BitVec.ofNat 64 (2 ^ k))) = BitVec.ofNat 64 ((x / 2 ^ k) * 2 ^ k) := by
  have hp : 2 ^ k < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hk
  have hpow_pos : 0 < 2 ^ k := @Nat.two_pow_pos k
  have hlt : (x / 2 ^ k) * 2 ^ k < 2 ^ 64 := by
    have := Nat.div_mul_le_self x (2 ^ k); omega
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_neg, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx,
    Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hlt]
  have hm : (2 ^ 64 - 2 ^ k) % 2 ^ 64 = 2 ^ 64 - 2 ^ k := by omega
  have hsh : (x >>> k) <<< k = x &&& (2 ^ 64 - 2 ^ k) := by
    apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Nat.testBit_and]
    by_cases hik : k ≤ i <;> by_cases hi64 : i < 64
    · have ht1 : (2 ^ 64 - 2 ^ k).testBit i = true := by
        have hsub : 2 ^ 64 - 2 ^ k = (2 ^ (64 - k) - 1) <<< k := by
          rw [Nat.shiftLeft_eq, Nat.mul_sub_right_distrib, Nat.one_mul, ← Nat.pow_add,
            Nat.sub_add_cancel (by omega)]
        rw [hsub, Nat.testBit_shiftLeft]
        simp [hik, Nat.testBit_two_pow_sub_one, show i - k < 64 - k by omega]
      simp [hik, ht1, Nat.add_sub_cancel' hik]
    · have hx0 : x.testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [hik, Nat.add_sub_cancel' hik, hx0]
    · have ht0 : (2 ^ 64 - 2 ^ k).testBit i = false := by
        have hsub : 2 ^ 64 - 2 ^ k = (2 ^ (64 - k) - 1) <<< k := by
          rw [Nat.shiftLeft_eq, Nat.mul_sub_right_distrib, Nat.one_mul, ← Nat.pow_add,
            Nat.sub_add_cancel (by omega)]
        rw [hsub, Nat.testBit_shiftLeft]
        simp [hik]
      simp [hik, ht0]
    · have hx0 : x.testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [hik, hx0]
  rw [hm, ← hsh, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]

theorem bv_ult_eq {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a).ult (BitVec.ofNat 64 b) = decide (a < b) := by
  simp [BitVec.ult, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem bv_ule_eq {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a).ule (BitVec.ofNat 64 b) = decide (a ≤ b) := by
  simp [BitVec.ule, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem bv_eq_zero_iff {v : Nat} (hv : v < 2 ^ 64) :
    BitVec.ofNat 64 v = (0 : Val) ↔ v = 0 := by
  simpa using cursor_eq_iff (base := 0) hv (by decide)

theorem ult_branch {a b : Nat} {P Q : Prop} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (ht : a < b → P) (hf : ¬ a < b → Q) :
    ((BitVec.ofNat 64 a).ult (BitVec.ofNat 64 b) = true → P) ∧
    ((BitVec.ofNat 64 a).ult (BitVec.ofNat 64 b) = false → Q) := by
  rw [bv_ult_eq ha hb]; simp only [decide_eq_true_eq, decide_eq_false_iff_not]; exact ⟨ht, hf⟩

theorem ule_branch {a b : Nat} {P Q : Prop} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (ht : a ≤ b → P) (hf : ¬ a ≤ b → Q) :
    ((BitVec.ofNat 64 a).ule (BitVec.ofNat 64 b) = true → P) ∧
    ((BitVec.ofNat 64 a).ule (BitVec.ofNat 64 b) = false → Q) := by
  rw [bv_ule_eq ha hb]; simp only [decide_eq_true_eq, decide_eq_false_iff_not]; exact ⟨ht, hf⟩

theorem bv_eq_zero_branch {v : Nat} {P Q : Prop} (hv : v < 2 ^ 64)
    (hz : v = 0 → P) (hnz : v ≠ 0 → Q) :
    (BitVec.ofNat 64 v = (0 : Val) → P) ∧ (BitVec.ofNat 64 v ≠ (0 : Val) → Q) := by
  simp only [ne_eq, bv_eq_zero_iff hv]; exact ⟨hz, hnz⟩

theorem bv_odd_branch {u : Nat} {P Q : Prop} (hu : u < 2 ^ 64)
    (hodd : (u % 2 != 0) = true → P) (heven : (u % 2 != 0) = false → Q) :
    (BitVec.ofNat 64 u &&& (1 : Val) ≠ 0 → P) ∧
    (¬ BitVec.ofNat 64 u &&& (1 : Val) ≠ 0 → Q) := by
  rw [bv_and_one hu]
  have hiff : (BitVec.ofNat 64 (u % 2) ≠ (0 : Val)) ↔ (u % 2 != 0) = true := by
    rw [ne_eq, bv_eq_zero_iff (by omega), bne_iff_ne]
  constructor
  · intro h; exact hodd (hiff.mp h)
  · intro h; exact heven (Bool.eq_false_iff.mpr (fun ht => h (hiff.mpr ht)))

theorem cursor_eof_branch {base : Val} {i n : Nat} {P Q : Prop}
    (hi : i ≤ n) (hn : n < 2 ^ 64)
    (heof : i = n → P) (hneof : i < n → Q) :
    (base + BitVec.ofNat 64 i = base + BitVec.ofNat 64 n → P) ∧
    (base + BitVec.ofNat 64 i ≠ base + BitVec.ofNat 64 n → Q) := by
  have hiff := cursor_eq_iff (base := base) (by omega : i < 2 ^ 64) hn
  simp only [ne_eq, hiff]
  exact ⟨heof, fun h => hneof (Nat.lt_of_le_of_ne hi h)⟩

theorem wp_call_ret1 {Γ : Env} {Q : Post} {X : XPost} {f : Sym} {args : List (Arg Val)}
    {k : Expr Val Cont} {m : Mem 64} (Pred : Val → Mem 64 → Prop)
    (hcall : Γ f (args.map Arg.val) m (fun rs m' => ∃ r, rs = [r] ∧ Pred r m') (fun _ _ _ => False))
    (hk : ∀ r m', Pred r m' → wp Γ Q X k [r] [] m') :
    wp Γ Q X (.call f args k) [] [] m := by
  simp only [wp, true_and]
  exact ⟨_, fun _ _ _ => False, hcall, by rintro _ m' ⟨r, rfl, hp⟩; exact hk r m' hp,
    fun _ _ _ h => h.elim⟩

theorem parseDigitsAux_lt_bound {acc : Nat} {bs : List UInt8} {v : Nat} {rest : List UInt8}
    (hacc : acc < dimacsBound) (h : parseDigitsAux acc bs = some (v, rest)) :
    v < dimacsBound := by
  induction bs generalizing acc with
  | nil => simp [parseDigitsAux] at h; obtain ⟨rfl, _⟩ := h; exact hacc
  | cons b bs ih =>
    simp only [parseDigitsAux] at h
    split at h
    · split at h
      · rename_i hlt; exact ih hlt h
      · nomatch h
    · split at h
      · simp at h; obtain ⟨rfl, _⟩ := h; exact hacc
      · nomatch h

theorem parseNat_lt_bound {bs : List UInt8} {v : Nat} {rest : List UInt8}
    (h : parseNat bs = some (v, rest)) : v < dimacsBound := by
  cases bs with
  | nil => nomatch h
  | cons b bs =>
    simp only [parseNat] at h
    split at h
    · rename_i hd
      unfold isDimacsDigit at hd
      have := b.toNat_lt
      exact parseDigitsAux_lt_bound (by unfold dimacsBound; omega) h
    · nomatch h

private theorem bv64_ofNat_slt_zero {v : Nat} (hv : v < 2 ^ 28) :
    (BitVec.ofNat 64 v).slt 0#64 = false := by
  unfold BitVec.slt BitVec.toInt
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : v < 2 ^ 64), decide_eq_false_iff_not]
  split <;> omega

theorem isValidLit_ofNat {mv v : Nat} (hv1 : 1 ≤ v) (hvm : v ≤ mv) (hmv : mv < dimacsBound) :
    IsValidLit mv (BitVec.ofNat 64 v) := by
  unfold dimacsBound at hmv
  have hslt := bv64_ofNat_slt_zero (v := v) (by omega)
  refine ⟨by unfold IsInt32; grind, ?_, ?_, by omega⟩
  · intro hz
    have := congrArg BitVec.toNat hz
    simp [Nat.mod_eq_of_lt (by omega : v < 2 ^ 64)] at this
    omega
  · unfold bvAbs
    rw [show (0 : BitVec 64) = 0#64 from rfl, hslt]
    simp [Nat.mod_eq_of_lt (by omega : v < 2 ^ 64), hvm]

/-! ## 3. Pure executable mirror (`runLratCheckBytes`) -/

/-- Structural mirror of `@lit_loop` in `lbParseDimacsBody`. -/
def parseClausePure : Nat → Nat → Nat → List Val → List UInt8 →
    Option (List Val × Nat × List UInt8)
  | 0, _, _, _, _ => none
  | fuel + 1, mv, poolRem, acc, bs =>
    match skipWsComments bs with
    | [] => none
    | 45 :: rest =>
      if poolRem == 0 then none
      else match parseNat rest with
      | none => none
      | some (v, rest') =>
        if v == 0 || mv < v then none
        else parseClausePure fuel mv (poolRem - 1) (-BitVec.ofNat 64 v :: acc) rest'
    | b :: rest =>
      if poolRem == 0 then none
      else match parseNat (b :: rest) with
      | none => none
      | some (v, rest') =>
        if v == 0 then some (acc.reverse, poolRem - 1, rest')
        else if mv < v then none
        else parseClausePure fuel mv (poolRem - 1) (BitVec.ofNat 64 v :: acc) rest'

/-- Structural mirror of `@cl_loop` in `lbParseDimacsBody`. -/
def parseBodyPure (mv : Nat) : Nat → Nat → List (List Val) → List UInt8 →
    Option (List (List Val) × Nat)
  | 0, poolRem, revClauses, bs =>
    if (skipWsComments bs).isEmpty then some (revClauses.reverse, poolRem) else none
  | k + 1, poolRem, revClauses, bs => do
    let (clits, poolRem', bs') ← parseClausePure (bs.length + 1) mv poolRem [] bs
    parseBodyPure mv k poolRem' (clits :: revClauses) bs'

/-- Structural mirror of `readLeb128` (1..4 bytes, `< 2^28`). -/
def readLeb128Aux : Nat → Nat → Nat → List UInt8 → Option (Nat × List UInt8)
  | 0, _, _, _ => none
  | _ + 1, _, _, [] => none
  | fuel + 1, acc, sh, b :: bs =>
    let acc2 := acc ||| ((b.toNat &&& 127) <<< sh)
    if (b.toNat &&& 128) != 0 then
      let sh2 := sh + 7
      if sh2 < 28 then readLeb128Aux fuel acc2 sh2 bs else none
    else
      some (acc2, bs)

def readLeb128Pure (bs : List UInt8) : Option (Nat × List UInt8) :=
  readLeb128Aux 4 0 0 bs

/-- Decode non-zero zig-zag integer `u` (`v = u / 2`, negative iff `u % 2 == 1`). -/
def decodeZigZag (u : Nat) : Val :=
  let v : Val := BitVec.ofNat 64 (u / 2)
  if u % 2 == 1 then -v else v

theorem isValidLit_decodeZigZag {mv u : Nat} (_hu : u < 2 ^ 28)
    (hv1 : 1 ≤ u / 2) (hvm : u / 2 ≤ mv) (hmv : mv < dimacsBound) :
    IsValidLit mv (decodeZigZag u) := by
  unfold decodeZigZag
  have hv := isValidLit_ofNat hv1 hvm hmv
  split
  · exact isValidLit_neg hv
  · exact hv

private theorem lo7_shift_lt {x sh : Nat} (hsh : sh ≤ 21) :
    (x &&& 127) <<< sh < 2 ^ 28 := by
  rw [Nat.shiftLeft_eq]
  have h1 : x &&& 127 < 2 ^ 7 := Nat.and_lt_two_pow x (n := 7) (by decide)
  have h2 : 2 ^ sh ≤ 2 ^ 21 := Nat.pow_le_pow_right (by omega) hsh
  have h3 : (x &&& 127) * 2 ^ sh < 2 ^ 7 * 2 ^ 21 :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ h2)
      (Nat.mul_lt_mul_of_pos_right h1 (by decide))
  omega

theorem readLeb128Aux_some {fuel acc sh : Nat} {bs bs' : List UInt8} {u : Nat}
    (hacc : acc < 2 ^ 28) (hsh : sh + 7 * fuel ≤ 28)
    (h : readLeb128Aux fuel acc sh bs = some (u, bs')) :
    u < 2 ^ 28 ∧ ∃ k, 0 < k ∧ k ≤ bs.length ∧ bs' = bs.drop k := by
  induction fuel generalizing acc sh bs with
  | zero => simp [readLeb128Aux] at h
  | succ fuel ih =>
    cases bs with
    | nil => simp [readLeb128Aux] at h
    | cons b rest =>
      have hacc2 : (acc ||| ((b.toNat &&& 127) <<< sh)) < 2 ^ 28 :=
        Nat.or_lt_two_pow hacc (lo7_shift_lt (by omega))
      simp only [readLeb128Aux] at h
      split at h
      · split at h
        · obtain ⟨hu, k, hk0, hkle, rfl⟩ := ih hacc2 (by omega) h
          exact ⟨hu, k + 1, by omega, by simp; omega, by simp⟩
        · simp at h
      · injection h with hp
        injection hp with hu_eq hbs_eq
        subst hu_eq hbs_eq
        exact ⟨hacc2, 1, by omega, by simp, by simp⟩

theorem readLeb128Pure_some {bs bs' : List UInt8} {u : Nat}
    (h : readLeb128Pure bs = some (u, bs')) :
    u < 2 ^ 28 ∧ bs'.length < bs.length ∧
    ∃ k, 0 < k ∧ k ≤ bs.length ∧ bs' = bs.drop k := by
  obtain ⟨hu, k, hk0, hkle, rfl⟩ := readLeb128Aux_some (by decide) (by decide) h
  exact ⟨hu, by simp; omega, k, hk0, hkle, rfl⟩

theorem readLeb128Pure_drop {prfBytes : List UInt8} {idx u : Nat} {bs' : List UInt8}
    (hidx : idx ≤ prfBytes.length)
    (h : readLeb128Pure (prfBytes.drop idx) = some (u, bs')) :
    u < 2 ^ 28 ∧
    bs'.length < (prfBytes.drop idx).length ∧
    prfBytes.length - bs'.length ≤ prfBytes.length ∧
    idx < prfBytes.length - bs'.length ∧
    bs' = prfBytes.drop (prfBytes.length - bs'.length) := by
  obtain ⟨hu, hlt, k, hk0, hkle, hdrop⟩ := readLeb128Pure_some h
  rw [List.length_drop] at hkle hlt
  rw [List.drop_drop] at hdrop
  have hlen' : bs'.length = prfBytes.length - (idx + k) := by rw [hdrop, List.length_drop]
  have hidx' : prfBytes.length - bs'.length = idx + k := by omega
  exact ⟨hu, by rw [List.length_drop]; omega, by omega, by omega, by rwa [hidx']⟩

theorem readLeb128_spec {Γ : Env} {Q : Post} {X : XPost} {fail : Cont}
    {cur pend prf_ptr : Val} {prfBytes : List UInt8} {idx : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} {done : Val → Val → Expr Val Cont}
    (hfit : prf_ptr.toNat + prfBytes.length < 2 ^ 64)
    (hidx : idx ≤ prfBytes.length)
    (hcur : cur = prf_ptr + BitVec.ofNat 64 idx)
    (hpend : pend = prf_ptr + BitVec.ofNat 64 prfBytes.length)
    (hm : (Eq (prfBytes.At prf_ptr) ⋆ R) m)
    (hfail : readLeb128Pure (prfBytes.drop idx) = none → fail [] m)
    (hdone : ∀ u bs',
      readLeb128Pure (prfBytes.drop idx) = some (u, bs') →
      u < 2 ^ 28 →
      bs'.length < (prfBytes.drop idx).length →
      bs' = prfBytes.drop (prfBytes.length - bs'.length) →
      idx < prfBytes.length - bs'.length →
      wp Γ Q X (done (BitVec.ofNat 64 u)
        (prf_ptr + BitVec.ofNat 64 (prfBytes.length - bs'.length))) [] [] m) :
    wp Γ Q X (readLeb128 fail cur pend done) [] [] m := by
  subst hcur hpend
  unfold readLeb128
  apply wp_join (fun as m' => ∃ u idx',
    as = [BitVec.ofNat 64 u, prf_ptr + BitVec.ofNat 64 idx'] ∧
    m' = m ∧ idx' ≤ prfBytes.length ∧
    readLeb128Pure (prfBytes.drop idx) = some (u, prfBytes.drop idx'))
  · rintro _ _ ⟨u, idx', rfl, rfl, hidx', hres⟩
    wp_unfold
    obtain ⟨hu, hlt, _, hgt, hdrop⟩ := readLeb128Pure_drop hidx hres
    have heq_idx : prfBytes.length - (prfBytes.drop idx').length = idx' := by
      rw [List.length_drop]; omega
    rw [← heq_idx]
    exact hdone u (prfBytes.drop idx') hres hu hlt hdrop hgt
  · intro Jdone hJdone
    apply wp_loop (fun fuel as m' => ∃ i acc sh,
      1 ≤ fuel ∧ sh + 7 * fuel = 28 ∧ acc < 2 ^ 28 ∧
      i ≤ prfBytes.length ∧ m' = m ∧
      as = [prf_ptr + BitVec.ofNat 64 i, BitVec.ofNat 64 acc, BitVec.ofNat 64 sh] ∧
      readLeb128Pure (prfBytes.drop idx) = readLeb128Aux fuel acc sh (prfBytes.drop i))
    · rintro Jleb fuel as _ ⟨i, acc, sh, hfuel1, hsh_eq, hacc, hi, rfl, rfl, hpure⟩ ih
      obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by omega⟩
      wp_unfold
      refine ⟨fun heof => ?_, fun hneof => ?_⟩
      · have hi_eq : i = prfBytes.length := (cursor_eq_iff (by omega) (by omega)).mp heof
        subst hi_eq; rw [List.drop_length] at hpure; exact hfail hpure
      · have hilt : i < prfBytes.length := by
          rcases Nat.eq_or_lt_of_le hi with rfl | h; exact absurd rfl hneof; exact h
        refine ⟨_, loadub_At hilt (by omega) hm, ?_⟩
        rw [List.drop_eq_getElem_cons hilt] at hpure
        have hb : prfBytes[i].toNat < 256 := prfBytes[i].toNat_lt
        have hlo_lt : prfBytes[i].toNat &&& 127 < 128 :=
          Nat.and_lt_two_pow prfBytes[i].toNat (n := 7) (by decide)
        have hsl_lt : (prfBytes[i].toNat &&& 127) <<< sh < 2 ^ 28 := lo7_shift_lt (by omega)
        have hacc2_lt : (acc ||| ((prfBytes[i].toNat &&& 127) <<< sh)) < 2 ^ 28 :=
          Nat.or_lt_two_pow hacc hsl_lt
        have hhi_lt : prfBytes[i].toNat &&& 128 < 256 :=
          Nat.and_lt_two_pow prfBytes[i].toNat (n := 8) (by decide)
        have hlo_bv : BitVec.ofNat 64 prfBytes[i].toNat &&& (127 : Val) =
            BitVec.ofNat 64 (prfBytes[i].toNat &&& 127) :=
          BitVec.eq_of_toNat_eq (by simp)
        have hhi_bv : BitVec.ofNat 64 prfBytes[i].toNat &&& (128 : Val) =
            BitVec.ofNat 64 (prfBytes[i].toNat &&& 128) :=
          BitVec.eq_of_toNat_eq (by simp)
        have hsh_mod : (BitVec.ofNat 64 sh).toNat % 64 = sh := by
          simp [Nat.mod_eq_of_lt (by omega : sh < 2 ^ 64), Nat.mod_eq_of_lt (by omega : sh < 64)]
        have hacc2_bv : BitVec.ofNat 64 acc ||| BitVec.ofNat 64 ((prfBytes[i].toNat &&& 127) <<< sh) =
            BitVec.ofNat 64 (acc ||| ((prfBytes[i].toNat &&& 127) <<< sh)) :=
          BitVec.eq_of_toNat_eq (by simp)
        rw [hlo_bv, hsh_mod, bv_shl_ofNat (by omega) (by omega), hacc2_bv, hhi_bv, ptr_step_1]
        have ⟨hmore_b, hnmore_b⟩ := bv_eq_zero_branch (by omega : prfBytes[i].toNat &&& 128 < 2 ^ 64)
          (fun h0 => by simp [h0] : prfBytes[i].toNat &&& 128 = 0 → ((prfBytes[i].toNat &&& 128) != 0) = false)
          (fun hnz => by simp [hnz] : prfBytes[i].toNat &&& 128 ≠ 0 → ((prfBytes[i].toNat &&& 128) != 0) = true)
        refine ⟨fun hmore => ?_, fun hnmore => ?_⟩
        · simp only [readLeb128Aux, hnmore_b hmore, ↓reduceIte] at hpure
          rw [show (7 : Val) = BitVec.ofNat 64 7 from rfl,
              show (28 : Val) = BitVec.ofNat 64 28 from rfl, bv_add_ofNat sh 7]
          refine ult_branch (a := sh + 7) (b := 28) (by omega) (by decide) (fun hlt28 => ?_) (fun hnlt28 => ?_)
          · simp only [hlt28, ↓reduceIte] at hpure
            exact ih fuel' _ _ (by omega)
              ⟨i + 1, _, sh + 7, by omega, by omega, hacc2_lt, hilt, rfl, rfl, hpure⟩
          · simp only [hnlt28, ↓reduceIte] at hpure
            exact hfail hpure
        · simp only [readLeb128Aux, hmore_b (Classical.not_not.mp hnmore),
            Bool.false_eq_true, ↓reduceIte] at hpure
          exact hJdone _ _ ⟨_, i + 1, rfl, rfl, hilt, hpure⟩
    · intro Jleb hJleb
      wp_unfold
      exact hJleb 4 _ _ ⟨idx, 0, 0, by decide, by decide, by decide, hidx, rfl, by simp, rfl⟩

/-- Structural mirror of `lbReadAddLits`. -/
def readAddLitsAux : Nat → Nat → Nat → List Val → List UInt8 →
    Option (List Val × Nat × List UInt8)
  | 0, _, _, _, _ => none
  | fuel + 1, mv, poolRem, acc, bs =>
    if poolRem == 0 then none
    else match readLeb128Pure bs with
    | none => none
    | some (0, bs') => some (acc.reverse, poolRem - 1, bs')
    | some (u, bs') =>
      let v := u / 2
      if v == 0 || mv < v then none
      else readAddLitsAux fuel mv (poolRem - 1) (decodeZigZag u :: acc) bs'

def readAddLitsPure (mv poolRem : Nat) (bs : List UInt8) :
    Option (List Val × Nat × List UInt8) :=
  readAddLitsAux (bs.length + 1) mv poolRem [] bs

/-- Outcome of `rupPhase1`. -/
inductive Phase1Res
  | fail
  | taut
  | ok (vals : List Val) (trailLen : Nat)

/-- Structural mirror of `rupPhase1` over `vals : List Val` (`length = mv + 1`). -/
def rupPhase1Pure (mv : Nat) : List Val → List Val → Nat → Phase1Res
  | [], vals, trailLen => .ok vals trailLen
  | lit :: lits, vals, trailLen =>
    let idx := (bvAbs lit).toNat
    let val := evalAssignedLit (vals.getD idx 0) lit
    if val.slt 0 then
      rupPhase1Pure mv lits vals trailLen
    else if (0 : Val).slt val then
      .taut
    else if trailLen == mv + 1 then
      .fail
    else
      let nlit := -lit
      let vals' := vals.set idx (bvSignByte nlit)
      rupPhase1Pure mv lits vals' (trailLen + 1)

/-- Structural mirror of `rupInner` over `vals : List Val`. -/
def rupInnerPure (mv : Nat) : List Val → Val → List Val → Nat →
    Option (Val × List Val × Nat)
  | [], unit, vals, trailLen => some (unit, vals, trailLen)
  | lit :: lits, unit, vals, trailLen =>
    let idx := (bvAbs lit).toNat
    let val := evalAssignedLit (vals.getD idx 0) lit
    if val.slt 0 then
      if unit == -lit then none
      else rupInnerPure mv lits unit vals trailLen
    else
      let stepUnit : Option (Val × List Val × Nat) :=
        if val == 0 then
          if trailLen == mv + 1 then none
          else
            let vals' := vals.set idx (bvSignByte lit)
            rupInnerPure mv lits lit vals' (trailLen + 1)
        else
          rupInnerPure mv lits lit vals trailLen
      if lo32 unit != 0 then
        if unit == lit then stepUnit else none
      else
        stepUnit

/-- Structural mirror of `@consume` in `lbRupCheck`. -/
def consumeHintsAux : Nat → Nat → List (Option (List Val)) → List UInt8 → Option (List UInt8)
  | 0, _, _, _ => none
  | fuel + 1, id, table, bs =>
    match readLeb128Pure bs with
    | none => none
    | some (0, bs') => some bs'
    | some (u, bs') =>
      if u % 2 != 0 then none
      else
        let aid := u / 2
        if aid < id then
          match table[aid]? with
          | some (some _) => consumeHintsAux fuel id table bs'
          | _ => none
        else none

def consumeHintsPure (id : Nat) (table : List (Option (List Val))) (bs : List UInt8) :
    Option (List UInt8) :=
  consumeHintsAux (bs.length + 1) id table bs

/-- Structural mirror of `@ph2` in `lbRupCheck`. -/
def rupPhase2Aux : Nat → Nat → Nat → List (Option (List Val)) → List Val → Nat →
    List UInt8 → Option (List UInt8)
  | 0, _, _, _, _, _, _ => none
  | fuel + 1, mv, id, table, vals, trailLen, bs =>
    match readLeb128Pure bs with
    | none => none
    | some (0, _) => none
    | some (u, bs') =>
      if u % 2 != 0 then none
      else
        let aid := u / 2
        if aid < id then
          match table[aid]? with
          | some (some alits) =>
            match rupInnerPure mv alits 0 vals trailLen with
            | none => none
            | some (unit, vals', trailLen') =>
              if lo32 unit != 0 then
                rupPhase2Aux fuel mv id table vals' trailLen' bs'
              else
                consumeHintsPure id table bs'
          | _ => none
        else none

/-- Structural mirror of `lbRupCheck`. -/
def rupCheckPure (mv id : Nat) (clits : List Val) (table : List (Option (List Val)))
    (bs : List UInt8) : Option (List UInt8) :=
  match rupPhase1Pure mv clits (List.replicate (mv + 1) 0) 0 with
  | .fail => none
  | .taut => consumeHintsPure id table bs
  | .ok vals trailLen => rupPhase2Aux (bs.length + 1) mv id table vals trailLen bs

/-- Structural mirror of `@del_loop` in `lbCheckPrf`. -/
def delLoopAux : Nat → Nat → List (Option (List Val)) → List UInt8 →
    Option (List (Option (List Val)) × List UInt8)
  | 0, _, _, _ => none
  | fuel + 1, cap, table, bs =>
    match readLeb128Pure bs with
    | none => none
    | some (0, bs') => some (table, bs')
    | some (u, bs') =>
      if u % 2 != 0 then none
      else
        let did := u / 2
        if did == 0 || !(did < cap) then none
        else match table[did]? with
        | some (some _) => delLoopAux fuel cap (table.set did none) bs'
        | _ => none

/-- Structural mirror of `lbCheckPrf`. -/
def checkPrfAux : Nat → Nat → Nat → Nat → List (Option (List Val)) → List UInt8 → Bool
  | 0, _, _, _, _, _ => false
  | _, _, _, _, _, [] => false
  | fuel + 1, mv, nc, poolRem, table, tag :: bs1 =>
    let cap := table.length
    if tag == 97 then
      match readLeb128Pure bs1 with
      | none => false
      | some (uid, bs2) =>
        if uid % 2 != 0 then false
        else
          let id := uid / 2
          if !(nc < id) || !(id < cap) then false
          else match table[id]? with
          | some none =>
            match readAddLitsPure mv poolRem bs2 with
            | none => false
            | some (clits, poolRem', bs3) =>
              match rupCheckPure mv id clits table bs3 with
              | none => false
              | some bs4 =>
                if clits.isEmpty then true
                else checkPrfAux fuel mv nc poolRem' (table.set id (some clits)) bs4
          | _ => false
    else if tag == 100 then
      match delLoopAux (bs1.length + 1) cap table bs1 with
      | none => false
      | some (table', bs2) => checkPrfAux fuel mv nc poolRem table' bs2
    else false

def checkPrfPure (mv nc poolRem : Nat) (table : List (Option (List Val)))
    (bs : List UInt8) : Bool :=
  checkPrfAux (bs.length + 1) mv nc poolRem table bs

/-- Initial `List (Option (List Val))` table of length `cap` (`none` at `0`, `some cl` at `1..nc`,
`none` at `nc + 1 .. cap - 1`). -/
def initClauseTable (cap : Nat) (clauses : List (List Val)) : List (Option (List Val)) :=
  none :: clauses.map some ++ List.replicate (cap - (clauses.length + 1)) none

/-- Total executable mirror of `lrat_check_bytes(cnfBytes, prfBytes, work_len)`. -/
def runLratCheckBytes (cnfBytes prfBytes : List UInt8) (work_len : Nat) : Bool :=
  if work_len < 128 then false
  else match parseHeader cnfBytes with
  | none => false
  | some (mv, nc, bodyRest) =>
    let v_bytes := ((mv + 8) / 8) * 8
    let t_raw := 4 * (mv + 1)
    let t_bytes := ((t_raw + 7) / 8) * 8
    let fixed := 80 + v_bytes + t_bytes
    if work_len < fixed then false
    else
      let rem := work_len - fixed
      let c_half := rem / 16
      let p_cap := prfBytes.length % 268435456
      let want := nc + p_cap + 32
      let cap := if c_half < want then c_half else want
      if cap ≤ nc then false
      else
        let cb_bytes := 8 * cap
        let pool_rem := rem - cb_bytes
        let pool_ints := pool_rem / 4
        match parseBodyPure mv nc pool_ints [] bodyRest with
        | none => false
        | some (clauses, pool_ints') =>
          checkPrfPure mv nc pool_ints' (initClauseTable cap clauses) prfBytes

/-! ## 4. Workspace layout invariant (`WorkCfg`, `WorkState`) and exact contracts -/

/-- Static workspace geometry computed by `lrat_check_bytes` after `lb_parse_dimacs_header`. -/
structure WorkCfg where
  hdr : Val
  mv : Nat
  nc : Nat
  cap : Nat
  poolInts : Nat
  hmv : mv < dimacsBound
  hnc : nc < dimacsBound
  hnc_cap : nc < cap
  hfit : hdr.toNat + (80 + ((mv + 8) / 8) * 8 + ((4 * (mv + 1) + 7) / 8) * 8 +
    8 * cap + 4 * poolInts) < 2 ^ 64

namespace WorkCfg

def vBytes (c : WorkCfg) : Nat := ((c.mv + 8) / 8) * 8
def tRaw (c : WorkCfg) : Nat := 4 * (c.mv + 1)
def tBytes (c : WorkCfg) : Nat := ((c.tRaw + 7) / 8) * 8
def activeBytes (c : WorkCfg) : Nat := 80 + c.vBytes + c.tBytes + 8 * c.cap + 4 * c.poolInts

def vb (c : WorkCfg) : Val := c.hdr + 80
def tb (c : WorkCfg) : Val := c.vb + BitVec.ofNat 64 c.vBytes
def tlim (c : WorkCfg) : Val := c.tb + BitVec.ofNat 64 c.tRaw
def cb (c : WorkCfg) : Val := c.tb + BitVec.ofNat 64 c.tBytes
def pbase (c : WorkCfg) : Val := c.cb + BitVec.ofNat 64 (8 * c.cap)
def plim (c : WorkCfg) : Val := c.pbase + BitVec.ofNat 64 (4 * c.poolInts)

def hdrWords (c : WorkCfg) (pcur cur : Val) : List Val :=
  [BitVec.ofNat 64 c.mv, BitVec.ofNat 64 c.nc, BitVec.ofNat 64 c.cap,
   c.vb, c.tb, c.tlim, c.cb, c.plim, pcur, cur]

theorem fit_active (c : WorkCfg) : c.hdr.toNat + c.activeBytes < 2 ^ 64 := by
  have := c.hfit; unfold activeBytes vBytes tBytes tRaw; omega

private theorem bv_add_ofNat_toNat {a : Val} {n : Nat} (h : a.toNat + n < 2 ^ 64) :
    (a + BitVec.ofNat 64 n).toNat = a.toNat + n := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : n < 2 ^ 64), Nat.mod_eq_of_lt h]

theorem toNat_vb (c : WorkCfg) : c.vb.toNat = c.hdr.toNat + 80 := by
  have := c.fit_active; unfold activeBytes at this
  exact bv_add_ofNat_toNat (n := 80) (by omega)

theorem toNat_tb (c : WorkCfg) : c.tb.toNat = c.vb.toNat + c.vBytes := by
  have := c.fit_active; have := c.toNat_vb; unfold activeBytes at *
  exact bv_add_ofNat_toNat (n := c.vBytes) (by omega)

theorem toNat_tlim (c : WorkCfg) : c.tlim.toNat = c.tb.toNat + c.tRaw := by
  have := c.fit_active; have := c.toNat_vb; have := c.toNat_tb
  have htb : c.tRaw ≤ c.tBytes := by unfold tBytes; omega
  unfold activeBytes at *; exact bv_add_ofNat_toNat (n := c.tRaw) (by omega)

theorem toNat_cb (c : WorkCfg) : c.cb.toNat = c.tb.toNat + c.tBytes := by
  have := c.fit_active; have := c.toNat_vb; have := c.toNat_tb
  unfold activeBytes at *; exact bv_add_ofNat_toNat (n := c.tBytes) (by omega)

theorem toNat_pbase (c : WorkCfg) : c.pbase.toNat = c.cb.toNat + 8 * c.cap := by
  have := c.fit_active; have := c.toNat_vb; have := c.toNat_tb; have := c.toNat_cb
  unfold activeBytes at *; exact bv_add_ofNat_toNat (n := 8 * c.cap) (by omega)

theorem toNat_plim (c : WorkCfg) : c.plim.toNat = c.pbase.toNat + 4 * c.poolInts := by
  have := c.fit_active; have := c.toNat_vb; have := c.toNat_tb
  have := c.toNat_cb; have := c.toNat_pbase
  unfold activeBytes at *; exact bv_add_ofNat_toNat (n := 4 * c.poolInts) (by omega)

theorem pcur_ne_zero (c : WorkCfg) {off : Nat} (hoff : off ≤ 4 * c.poolInts) :
    c.pbase + BitVec.ofNat 64 off ≠ 0 := by
  have := c.fit_active; have := c.toNat_vb; have := c.toNat_tb
  have := c.toNat_cb; have := c.toNat_pbase; unfold activeBytes at *
  intro h0
  have h0n := congrArg BitVec.toNat h0
  rw [bv_add_ofNat_toNat (n := off) (by omega)] at h0n
  have : (0 : Val).toNat = 0 := rfl
  omega

theorem pcur_eq_plim_iff (c : WorkCfg) {rem : Nat} (hrem : rem ≤ c.poolInts) :
    c.pbase + BitVec.ofNat 64 (4 * (c.poolInts - rem)) = c.plim ↔ rem = 0 := by
  have := c.fit_active; have := c.toNat_vb; have := c.toNat_tb
  have := c.toNat_cb; have := c.toNat_pbase; unfold activeBytes at *; unfold plim
  rw [cursor_eq_iff (by omega) (by omega)]
  omega

end WorkCfg

/-- Agreement between physical `ptrs : List Val`, logical `table : List (Option (List Val))`,
and `PoolUsed : Mem 64 → Prop`. -/
def TableRel (mv cap : Nat) (ptrs : List Val) (table : List (Option (List Val)))
    (PoolUsed : Mem 64 → Prop) : Prop :=
  ∃ (hplen : ptrs.length = cap) (htlen : table.length = cap),
    ∀ i (hi : i < cap),
      match table[i]'(htlen ▸ hi) with
      | none => ptrs[i]'(hplen ▸ hi) = 0
      | some lits =>
        ptrs[i]'(hplen ▸ hi) ≠ 0 ∧
        (∀ x ∈ lits, IsValidLit mv x) ∧
        (∃ R, PoolUsed = (ZeroTermInts (ptrs[i]'(hplen ▸ hi)) lits ⋆ R))

theorem TableRel.frame_right {mv cap : Nat} {ptrs : List Val} {table : List (Option (List Val))}
    {PoolUsed : Mem 64 → Prop} (P : Mem 64 → Prop)
    (h : TableRel mv cap ptrs table PoolUsed) :
    TableRel mv cap ptrs table (PoolUsed ⋆ P) := by
  obtain ⟨hplen, htlen, hrel⟩ := h
  refine ⟨hplen, htlen, fun i hi => ?_⟩
  have hi_spec := hrel i hi
  cases hti : table[i]'(htlen ▸ hi) with
  | none => rw [hti] at hi_spec; exact hi_spec
  | some lits =>
    rw [hti] at hi_spec
    obtain ⟨hne, hv, R_i, hpu⟩ := hi_spec
    exact ⟨hne, hv, R_i ⋆ P, by rw [hpu, sep_assoc]⟩

/-- Full workspace memory state over `[c.hdr, c.hdr + c.activeBytes)`. -/
def WorkState (c : WorkCfg) (poolUsedInts poolRemInts : Nat) (cur : Val)
    (ptrs : List Val) (table : List (Option (List Val))) (PoolUsed : Mem 64 → Prop) :
    Mem 64 → Prop := fun m =>
  poolUsedInts + poolRemInts = c.poolInts ∧
  TableRel c.mv c.cap ptrs table PoolUsed ∧
  (∀ f, PoolUsed f → region c.pbase (4 * poolUsedInts) f) ∧
  let pcur := c.pbase + BitVec.ofNat 64 (4 * poolUsedInts)
  (word8Array c.hdr (c.hdrWords pcur cur) ⋆
    byte1Array c.vb (assignBytes c.mv Assignment.empty) ⋆
    region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
    region c.tb c.tRaw ⋆
    region c.tlim (c.tBytes - c.tRaw) ⋆
    word8Array c.cb ptrs ⋆
    PoolUsed ⋆
    region pcur (4 * poolRemInts)) m

theorem workState_sep {c : WorkCfg} {poolUsedInts poolRemInts : Nat} {cur : Val}
    {ptrs : List Val} {table : List (Option (List Val))} {PoolUsed F : Mem 64 → Prop}
    {m : Mem 64} :
    (WorkState c poolUsedInts poolRemInts cur ptrs table PoolUsed ⋆ F) m ↔
      poolUsedInts + poolRemInts = c.poolInts ∧
      TableRel c.mv c.cap ptrs table PoolUsed ∧
      (∀ f, PoolUsed f → region c.pbase (4 * poolUsedInts) f) ∧
      ((word8Array c.hdr (c.hdrWords (c.pbase + BitVec.ofNat 64 (4 * poolUsedInts)) cur) ⋆
        byte1Array c.vb (assignBytes c.mv Assignment.empty) ⋆
        region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
        region c.tb c.tRaw ⋆
        region c.tlim (c.tBytes - c.tRaw) ⋆
        word8Array c.cb ptrs ⋆
        PoolUsed ⋆
        region (c.pbase + BitVec.ofNat 64 (4 * poolUsedInts)) (4 * poolRemInts)) ⋆ F) m := by
  unfold WorkState; simp only [sep_pure_l]

theorem loadl_hdr {c : WorkCfg} {pcur cur : Val} {sg : Bool} {R : Mem 64 → Prop} {m : Mem 64}
    (i : Nat) (hi : i < 10)
    (h : (word8Array c.hdr (c.hdrWords pcur cur) ⋆ R) m)
    {a : Val} (ha : a = c.hdr + BitVec.ofNat 64 (8 * i)) :
    loadVal m .l .l sg a =
      some ((c.hdrWords pcur cur)[i]'(by simpa [WorkCfg.hdrWords] using hi)) := by
  subst ha; exact loadl_word8Array _ h

theorem sep_mono2 {P1 P1' P2 P2' : Mem 64 → Prop}
    (h1 : ∀ f, P1 f → P1' f) (h2 : ∀ f, P2 f → P2' f) :
    ∀ f, (P1 ⋆ P2) f → (P1' ⋆ P2') f :=
  fun _ h => sep_mono h1 (sep_mono_r h2 h)

/-- Collapse the 8 partitioned workspace regions back into `region c.hdr c.activeBytes`. -/
theorem workCfg_regions_to_activeBytes (c : WorkCfg) {poolUsedInts poolRemInts : Nat}
    (hsum : poolUsedInts + poolRemInts = c.poolInts) {m : Mem 64}
    (hm : (region c.hdr 80 ⋆
      region c.vb (c.mv + 1) ⋆
      region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1)) ⋆
      region c.tb c.tRaw ⋆
      region c.tlim (c.tBytes - c.tRaw) ⋆
      region c.cb (8 * c.cap) ⋆
      region c.pbase (4 * poolUsedInts) ⋆
      region (c.pbase + BitVec.ofNat 64 (4 * poolUsedInts)) (4 * poolRemInts)) m) :
    region c.hdr c.activeBytes m := by
  have hfit : c.activeBytes ≤ 2 ^ 64 := by have := c.fit_active; omega
  have hmv := c.hmv; unfold dimacsBound at hmv
  have hvb : c.mv + 1 ≤ c.vBytes := by unfold WorkCfg.vBytes; omega
  have htb : c.tRaw ≤ c.tBytes := by unfold WorkCfg.tBytes WorkCfg.tRaw; omega
  unfold WorkCfg.activeBytes at hfit ⊢
  have hm2 : (region c.hdr 80 ⋆
      ((region c.vb (c.mv + 1) ⋆ region (c.vb + BitVec.ofNat 64 (c.mv + 1)) (c.vBytes - (c.mv + 1))) ⋆
        ((region c.tb c.tRaw ⋆ region c.tlim (c.tBytes - c.tRaw)) ⋆
          (region c.cb (8 * c.cap) ⋆
            (region c.pbase (4 * poolUsedInts) ⋆
              region (c.pbase + BitVec.ofNat 64 (4 * poolUsedInts)) (4 * poolRemInts)))))) m :=
    sep_ac hm
  rw [
    region_merge_eq (a := c.vb) (n1 := c.mv + 1) (n2 := c.vBytes - (c.mv + 1)) (n := c.vBytes) (by omega) (by omega),
    show c.tlim = c.tb + BitVec.ofNat 64 c.tRaw from rfl,
    region_merge_eq (a := c.tb) (n1 := c.tRaw) (n2 := c.tBytes - c.tRaw) (n := c.tBytes) (by omega) (by omega),
    region_merge_eq (a := c.pbase) (n1 := 4 * poolUsedInts) (n2 := 4 * poolRemInts) (n := 4 * c.poolInts) (by omega) (by omega),
    show c.pbase = c.cb + BitVec.ofNat 64 (8 * c.cap) from rfl,
    region_merge_eq (a := c.cb) (n1 := 8 * c.cap) (n2 := 4 * c.poolInts) (n := 8 * c.cap + 4 * c.poolInts) rfl (by omega),
    show c.cb = c.tb + BitVec.ofNat 64 c.tBytes from rfl,
    region_merge_eq (a := c.tb) (n1 := c.tBytes) (n2 := 8 * c.cap + 4 * c.poolInts) (n := c.tBytes + (8 * c.cap + 4 * c.poolInts)) rfl (by omega),
    show c.tb = c.vb + BitVec.ofNat 64 c.vBytes from rfl,
    region_merge_eq (a := c.vb) (n1 := c.vBytes) (n2 := c.tBytes + (8 * c.cap + 4 * c.poolInts)) (n := c.vBytes + (c.tBytes + (8 * c.cap + 4 * c.poolInts))) rfl (by omega),
    show c.vb = c.hdr + BitVec.ofNat 64 80 from rfl,
    region_merge_eq (a := c.hdr) (n1 := 80) (n2 := c.vBytes + (c.tBytes + (8 * c.cap + 4 * c.poolInts))) (n := c.activeBytes) (by unfold WorkCfg.activeBytes; omega) hfit] at hm2
  exact hm2

/-- Any `WorkState` collapses back into `region c.hdr c.activeBytes`. -/
theorem WorkState.to_region {c : WorkCfg} {poolUsedInts poolRemInts : Nat} {cur : Val}
    {ptrs : List Val} {table : List (Option (List Val))} {PoolUsed : Mem 64 → Prop} {m : Mem 64}
    (h : WorkState c poolUsedInts poolRemInts cur ptrs table PoolUsed m) :
    region c.hdr c.activeBytes m := by
  obtain ⟨hsum, ⟨hplen, _, _⟩, hpu, hm⟩ := h
  have := c.fit_active; have hmv := c.hmv; unfold dimacsBound at hmv
  unfold WorkCfg.activeBytes WorkCfg.vBytes WorkCfg.tBytes WorkCfg.tRaw at *
  dsimp only at hm
  refine workCfg_regions_to_activeBytes c hsum ?_
  refine sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2 (sep_mono2
    (fun _ hf => by have := word8Array_to_region (by simp [WorkCfg.hdrWords]) hf; simpa [WorkCfg.hdrWords] using this)
    (fun _ hf => by simpa using byte1Array_to_region (by simp; omega) hf))
    (fun _ h => h)) (fun _ h => h)) (fun _ h => h))
    (fun _ hf => by have := word8Array_to_region (by rw [hplen]; omega) hf; rwa [hplen] at this))
    hpu) (fun _ h => h) m hm

/-! ### Exact callee contracts -/

/-- Exact contract for `lb_parse_dimacs_header(cnf_ptr, cnf_end, hdr)`. -/
def lbParseDimacsHeaderSpec : Spec := fun args m Q _ =>
  ∃ (cnf_ptr hdr : Val) (cnfBytes : List UInt8) (R : Mem 64 → Prop),
    args = [cnf_ptr, cnf_ptr + BitVec.ofNat 64 cnfBytes.length, hdr] ∧
    cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
    hdr.toNat + 80 < 2 ^ 64 ∧
    (Eq (cnfBytes.At cnf_ptr) ⋆ region hdr 80 ⋆ R) m ∧
    ∀ (r : Val) (m' : Mem 64),
      (match parseHeader cnfBytes with
       | none =>
         r = 0 ∧ (Eq (cnfBytes.At cnf_ptr) ⋆ region hdr 80 ⋆ R) m'
       | some (mv, nc, rest) =>
         r = 1 ∧ mv < dimacsBound ∧ nc < dimacsBound ∧
         rest = cnfBytes.drop (cnfBytes.length - rest.length) ∧
         rest.length ≤ cnfBytes.length ∧
         ∃ w2 w3 w4 w5 w6 w7 w8 : Val,
           (Eq (cnfBytes.At cnf_ptr) ⋆
             word8Array hdr
               [BitVec.ofNat 64 mv, BitVec.ofNat 64 nc, w2, w3, w4, w5, w6, w7, w8,
                cnf_ptr + BitVec.ofNat 64 (cnfBytes.length - rest.length)] ⋆ R) m') →
      Q [r] m'

/-- Exact contract for `lb_parse_dimacs_body(cnf_end, hdr)`. -/
def lbParseDimacsBodySpec : Spec := fun args m Q _ =>
  ∃ (c : WorkCfg) (cnf_ptr : Val) (cnfBytes : List UInt8) (idx0 : Nat)
    (R : Mem 64 → Prop),
    args = [cnf_ptr + BitVec.ofNat 64 cnfBytes.length, c.hdr] ∧
    cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
    idx0 ≤ cnfBytes.length ∧
    (Eq (cnfBytes.At cnf_ptr) ⋆
      WorkState c 0 c.poolInts (cnf_ptr + BitVec.ofNat 64 idx0)
        (List.replicate c.cap 0) (List.replicate c.cap none) emp ⋆ R) m ∧
    ∀ (r : Val) (m' : Mem 64),
      (match parseBodyPure c.mv c.nc c.poolInts [] (cnfBytes.drop idx0) with
       | none =>
         r = 0 ∧ (Eq (cnfBytes.At cnf_ptr) ⋆ region c.hdr c.activeBytes ⋆ R) m'
       | some (clauses, poolRem') =>
         r = 1 ∧ clauses.length = c.nc ∧ poolRem' ≤ c.poolInts ∧
         ∃ (ptrs : List Val) (PoolUsed : Mem 64 → Prop),
           (Eq (cnfBytes.At cnf_ptr) ⋆
             WorkState c (c.poolInts - poolRem') poolRem'
               (cnf_ptr + BitVec.ofNat 64 idx0)
               ptrs (initClauseTable c.cap clauses) PoolUsed ⋆ R) m') →
      Q [r] m'

/-- Exact contract for `lb_read_add_lits(hdr, prf_end)`. -/
def lbReadAddLitsSpec : Spec := fun args m Q _ =>
  ∃ (c : WorkCfg) (prf_ptr : Val) (prfBytes : List UInt8) (idx0 poolUsed poolRem : Nat)
    (ptrs : List Val) (table : List (Option (List Val))) (PoolUsed R : Mem 64 → Prop),
    args = [c.hdr, prf_ptr + BitVec.ofNat 64 prfBytes.length] ∧
    prf_ptr.toNat + prfBytes.length < 2 ^ 64 ∧
    idx0 ≤ prfBytes.length ∧
    (Eq (prfBytes.At prf_ptr) ⋆
      WorkState c poolUsed poolRem (prf_ptr + BitVec.ofNat 64 idx0) ptrs table PoolUsed ⋆ R) m ∧
    ∀ (r : Val) (m' : Mem 64),
      (match readAddLitsPure c.mv poolRem (prfBytes.drop idx0) with
       | none =>
         r = 0 ∧ (Eq (prfBytes.At prf_ptr) ⋆ region c.hdr c.activeBytes ⋆ R) m'
       | some (clits, poolRem', bs') =>
         let c_ptr := c.pbase + BitVec.ofNat 64 (4 * poolUsed)
         let idx' := prfBytes.length - bs'.length
         r = (if clits.isEmpty then 2 else 1) ∧
         bs' = prfBytes.drop idx' ∧ idx' ≤ prfBytes.length ∧
         clits.length + 1 + poolRem' = poolRem ∧
         c_ptr ≠ 0 ∧
         (∀ x ∈ clits, IsValidLit c.mv x) ∧
         (Eq (prfBytes.At prf_ptr) ⋆
           WorkState c (poolUsed + (clits.length + 1)) poolRem'
             (prf_ptr + BitVec.ofNat 64 idx')
             ptrs table (PoolUsed ⋆ ZeroTermInts c_ptr clits) ⋆ R) m') →
      Q [r] m'

/-- Exact contract for `lb_rup_check(hdr, id, c_ptr, prf_end)`. -/
def lbRupCheckSpec : Spec := fun args m Q _ =>
  ∃ (c : WorkCfg) (id : Nat) (c_ptr prf_ptr : Val) (prfBytes : List UInt8)
    (idx0 poolUsed poolRem : Nat) (clits ptrs : List Val)
    (table : List (Option (List Val))) (PoolUsed R : Mem 64 → Prop),
    args = [c.hdr, BitVec.ofNat 64 id, c_ptr, prf_ptr + BitVec.ofNat 64 prfBytes.length] ∧
    id < c.cap ∧
    prf_ptr.toNat + prfBytes.length < 2 ^ 64 ∧
    idx0 ≤ prfBytes.length ∧
    (∀ x ∈ clits, IsValidLit c.mv x) ∧
    (∃ R_c, PoolUsed = (ZeroTermInts c_ptr clits ⋆ R_c)) ∧
    (Eq (prfBytes.At prf_ptr) ⋆
      WorkState c poolUsed poolRem (prf_ptr + BitVec.ofNat 64 idx0) ptrs table PoolUsed ⋆ R) m ∧
    ∀ (r : Val) (m' : Mem 64),
      (match rupCheckPure c.mv id clits table (prfBytes.drop idx0) with
       | none =>
         r = 0 ∧ (Eq (prfBytes.At prf_ptr) ⋆ region c.hdr c.activeBytes ⋆ R) m'
       | some bs' =>
         let idx' := prfBytes.length - bs'.length
         r = 1 ∧ bs' = prfBytes.drop idx' ∧ idx' ≤ prfBytes.length ∧
         (Eq (prfBytes.At prf_ptr) ⋆
           WorkState c poolUsed poolRem (prf_ptr + BitVec.ofNat 64 idx')
             ptrs table PoolUsed ⋆ R) m') →
      Q [r] m'

/-- Exact contract for `lb_check_prf(hdr, prf_end)`. -/
def lbCheckPrfSpec : Spec := fun args m Q _ =>
  ∃ (c : WorkCfg) (prf_ptr : Val) (prfBytes : List UInt8) (poolUsed poolRem : Nat)
    (ptrs : List Val) (table : List (Option (List Val))) (PoolUsed R : Mem 64 → Prop),
    args = [c.hdr, prf_ptr + BitVec.ofNat 64 prfBytes.length] ∧
    prf_ptr.toNat + prfBytes.length < 2 ^ 64 ∧
    (Eq (prfBytes.At prf_ptr) ⋆
      WorkState c poolUsed poolRem prf_ptr ptrs table PoolUsed ⋆ R) m ∧
    ∀ (r : Val) (m' : Mem 64),
      r = (if checkPrfPure c.mv c.nc poolRem table prfBytes then 1 else 0) →
      (Eq (prfBytes.At prf_ptr) ⋆ region c.hdr c.activeBytes ⋆ R) m' →
      Q [r] m'

/-- Exact contract for `lrat_check_bytes`. -/
def lratCheckBytesExactSpec : Spec := fun args m Q _ =>
  ∃ (cnf_ptr prf_ptr work_ptr : Val) (cnfBytes prfBytes : List UInt8) (work_len : Nat)
    (R_mem : Mem 64 → Prop),
    args = [cnf_ptr, BitVec.ofNat 64 cnfBytes.length,
            prf_ptr, BitVec.ofNat 64 prfBytes.length,
            work_ptr, BitVec.ofNat 64 work_len] ∧
    cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
    prf_ptr.toNat + prfBytes.length < 2 ^ 64 ∧
    work_ptr.toNat + work_len < 2 ^ 64 ∧
    ((Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ region work_ptr work_len) ⋆ R_mem) m ∧
    ∀ (r : Val) (m' : Mem 64),
      r = (if runLratCheckBytes cnfBytes prfBytes work_len then 1 else 0) →
      ((Eq (cnfBytes.At cnf_ptr) ⋆ Eq (prfBytes.At prf_ptr) ⋆ region work_ptr work_len) ⋆ R_mem) m' →
      Q [r] m'

end LeanQbe.LratBytes
