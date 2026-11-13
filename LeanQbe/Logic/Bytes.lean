module

public import LeanQbe.Logic.Cells
public import LeanQbe.AbiLemmas
import all Kraken.Mem
import all Kraken.Separation

/-!
# Concrete bytes and untyped regions

* `bytesN n xs`: the bytes an array of `n`-byte values denotes; `byte1Array_eq`, `int4Array_eq`,
  `word8Array_eq` turn an array predicate into `Eq ((bytesN n xs).At a)`. With `eq_append_At` and the
  tactic `solve_bytes_at` this proves that a concrete byte list satisfies a separation-logic precondition
  (non-vacuity of a specification).
* `loadub_At`: `loadub` from a byte list in memory (an input buffer); `expectByte_branch`: the end test,
  the load and the comparison with an expected byte, as `wp_unfold` leaves them.
* `region a n` (`LeanQbe.Abi`: `n` bytes at `a`, contents unknown) against the array predicates, both
  ways (`byte1Array_to_region`, `region_to_int4Array`, …), popping one `int4` off a region
  (`region_pop_int4`, `region_pop_store_int4`), and merging (`region_merge_eq`).
* `sep_mono2`, `sep_mono_mid`: weakening both sides, or the middle one of three, of a `⋆`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe

open Std Std.ExtHashMap
open Kraken.Bedrock2.Test

/-! ## The bytes of an array -/

/-- `n` bytes per value, little-endian. -/
def bytesN (n : Nat) (xs : List Val) : List UInt8 := xs.flatMap fun v => Int.toBytes n v.toNat

theorem bytesN_length (n : Nat) (xs : List Val) : (bytesN n xs).length = n * xs.length := by
  induction xs with
  | nil => simp [bytesN]
  | cons x xs ih =>
    simp only [bytesN, List.flatMap_cons, List.length_append, Int.toBytes_length] at ih ⊢
    rw [ih, List.length_cons, Nat.mul_succ]; omega

theorem eq_nil_At (a : Val) : (emp : Mem 64 → Prop) = Eq (([] : List UInt8).At a) := by
  funext m; apply propext; constructor
  · intro h; rw [h]; apply ExtHashMap.ext_getElem?; intro k; simp [List.At]
  · intro h; rw [← h]; apply ExtHashMap.ext_getElem?; intro k; simp [List.At]

theorem eq_cons_At {n : Nat} (a v : Val) (bs : List UInt8) (h : n + bs.length ≤ 2 ^ 64) :
    (Eq ((Int.toBytes n v.toNat).At a) ⋆ Eq (bs.At (a + BitVec.ofNat 64 n))) =
      Eq ((Int.toBytes n v.toNat ++ bs).At a) := by
  rw [Mem.At_append_sep _ _ _ (by rw [Int.toBytes_length]; exact h), Int.toBytes_length]

private theorem bytesArray_eq (n : Nat) (arr : Val → List Val → Mem 64 → Prop)
    (hnil : ∀ a, arr a [] = emp)
    (hcons : ∀ a x xs, arr a (x :: xs) = (Eq ((Int.toBytes n x.toNat).At a) ⋆ arr (a + BitVec.ofNat 64 n) xs))
    (a : Val) (xs : List Val) (h : n * xs.length ≤ 2 ^ 64) :
    arr a xs = Eq ((bytesN n xs).At a) := by
  induction xs generalizing a with
  | nil => rw [hnil, bytesN, List.flatMap_nil, eq_nil_At]
  | cons x xs ih =>
    have hl := bytesN_length n xs
    have h' : n * xs.length + n ≤ 2 ^ 64 := Nat.mul_succ n xs.length ▸ h
    rw [hcons, bytesN, List.flatMap_cons, ih _ (by omega)]
    exact eq_cons_At a x _ (by omega)

theorem byte1Array_eq (a : Val) (xs : List Val) (h : xs.length ≤ 2 ^ 64) :
    byte1Array a xs = Eq ((bytesN 1 xs).At a) :=
  bytesArray_eq 1 byte1Array byte1Array_nil byte1Array_cons a xs (by simpa using h)

theorem int4Array_eq (a : Val) (xs : List Val) (h : 4 * xs.length ≤ 2 ^ 64) :
    int4Array a xs = Eq ((bytesN 4 xs).At a) :=
  bytesArray_eq 4 int4Array int4Array_nil int4Array_cons a xs h

theorem word8Array_eq (a : Val) (xs : List Val) (h : 8 * xs.length ≤ 2 ^ 64) :
    word8Array a xs = Eq ((bytesN 8 xs).At a) :=
  bytesArray_eq 8 word8Array word8Array_nil word8Array_cons a xs h

theorem eq_append_At (a : Val) (b1 b2 : List UInt8) (h : b1.length + b2.length ≤ 2 ^ 64) :
    Eq ((b1 ++ b2).At a) = (Eq (b1.At a) ⋆ Eq (b2.At (a + BitVec.ofNat 64 b1.length))) :=
  Mem.At_append_sep _ _ _ h

theorem mem_at_cast {P : Mem 64 → Prop} {bs : List UInt8} {a : Val}
    (h : Eq (bs.At a) = P) : P (bs.At a) := h ▸ rfl

/-- Proves `P (bs.At a)`, where `P` is a `⋆` of `byte1Array` / `int4Array` / `word8Array` predicates at
concrete addresses and `bs` is the matching `++` of `bytesN` lists: turns each array into the bytes it
denotes (`byte1Array_eq`, …), splits `bs` (`eq_append_At`), computes the addresses, and reorders
(`ac_rfl`).

`simp` must be able to compute the length of every list; it can for literal lists. The extra simp lemmas
of `solve_bytes_at [l₁, …]` are used in three places: for the length of the list of a `word8Array`, for
splitting `bs`, and for computing the addresses. So a record laid out as a `word8Array` passes the lemma
that gives the length of its field list. The lists of `byte1Array` and `int4Array` are measured by plain
`simp`. -/
syntax "solve_bytes_at" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| solve_bytes_at) => `(tactic| solve_bytes_at [])
  | `(tactic| solve_bytes_at [$extra,*]) => `(tactic| (
      try simp only [sep_emp]
      repeat (first
        | rw [byte1Array_eq _ _ (by simp)]
        | rw [int4Array_eq _ _ (by simp)]
        | rw [word8Array_eq _ _ (by simp [$extra,*])])
      refine mem_at_cast ?_
      repeat rw [eq_append_At _ _ _ (by simp [bytesN_length, $extra,*])]
      simp only [bytesN_length, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceMul, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, $extra,*]
      ac_rfl))

/-! ## Byte lists in memory -/

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

theorem expectByte_branch {base : Val} {bs : List UInt8} {i : Nat} {k : UInt8}
    {R : Mem 64 → Prop} {m : Mem 64} {P Q : Prop}
    (hbase : base.toNat + bs.length < 2 ^ 64) (hi : i ≤ bs.length) (hm : (Eq (bs.At base) ⋆ R) m)
    (heof : bs.drop i = [] → Q)
    (hmatch : ∀ (hlt : i < bs.length), bs[i] = k → P)
    (hmismatch : ∀ (hlt : i < bs.length), bs[i] ≠ k → Q) :
    (base + BitVec.ofNat 64 i = base + BitVec.ofNat 64 bs.length → Q) ∧
    (base + BitVec.ofNat 64 i ≠ base + BitVec.ofNat 64 bs.length →
      ∃ v, loadVal m .l .b false (base + BitVec.ofNat 64 i) = some v ∧
        ((v = BitVec.ofNat 64 k.toNat → P) ∧ (v ≠ BitVec.ofNat 64 k.toNat → Q))) :=
  cursor_eof_branch hi (by omega) (fun heq => heof (by rw [heq]; simp))
    (fun hlt => ⟨_, loadub_At hlt (by omega) hm,
      fun heq => hmatch hlt ((bv64_u8_eq (k := k)).mp heq),
      fun hne => hmismatch hlt (fun h => hne ((bv64_u8_eq (k := k)).mpr h))⟩)

/-! ## Regions -/

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

private theorem toBytes_ofBytes_toNat {n : Nat} {bs : List UInt8}
    (hn : n = 1 ∨ n = 4 ∨ n = 8) (hl : bs.length = n) :
    Int.toBytes n ((BitVec.ofInt 64 (Int.ofBytes bs)).toNat : Int) = bs := by
  grind

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
  obtain ⟨ok, hm'⟩ := store_int4 v hm_cell
  exact ⟨ok, sep_cast hm' (by ac_rfl)⟩

theorem region_merge_eq {a : Val} {n1 n2 n : Nat}
    (hsum : n1 + n2 = n) (hfit : n ≤ 2 ^ 64) :
    (region a n1 ⋆ region (a + BitVec.ofNat 64 n1) n2) = region a n := by
  subst hsum
  exact (region_split (a := a) (n1 := n1) (n2 := n2) hfit).symm

/-! ## Monotonicity of `⋆`, beside `sep_mono` and `sep_mono_r` (`AbiLemmas`) -/

theorem sep_mono2 {P1 P1' P2 P2' : Mem 64 → Prop}
    (h1 : ∀ f, P1 f → P1' f) (h2 : ∀ f, P2 f → P2' f) :
    ∀ f, (P1 ⋆ P2) f → (P1' ⋆ P2') f :=
  fun _ h => sep_mono h1 (sep_mono_r h2 h)

theorem sep_mono_mid {A B B' C : Mem 64 → Prop} {m : Mem 64}
    (h : ∀ f, B f → B' f) (hm : (A ⋆ B ⋆ C) m) : (A ⋆ B' ⋆ C) m := by
  obtain ⟨f12, f3, hu1, hd1, ⟨f1, f2, hu2, hd2, hA, hB⟩, hC⟩ := hm
  exact ⟨f12, f3, hu1, hd1, ⟨f1, f2, hu2, hd2, hA, h f2 hB⟩, hC⟩

end LeanQbe
