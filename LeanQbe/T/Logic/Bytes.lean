module

public import LeanQbe.T.Logic.Cells
import all Kraken.Mem
import all Kraken.Separation

/-!
# Concrete bytes and untyped regions for `LeanQbe.T` (`T4`)

Typed-IR counterpart of `LeanQbe/Logic/Bytes.lean`:
* `bytesN n xs`, `byte1Array_eq`, `int4Array_eq`, `word8Array_eq`, `t_solve_bytes_at`
  (and scoped `solve_bytes_at` in `LeanQbe.T`).
* `loadu8_At` (`loadVal m i8` from a `bytes` / `Eq (bs.At base)` slice) and `expectByte_branch`.
* `region_split`, `region_zero`, `region_sep_elim`, `region_merge_eq`, `bytes_to_region`,
  `byte1Array_to_region`, `int4Array_to_region`, `word8Array_to_region`,
  `region_to_byte1Array`, `region_to_int4Array`, `region_to_word8Array`,
  `region_pop_int4`, `region_pop_store_int4`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

open Std Std.ExtHashMap
open Kraken.Bedrock2.Test

/-! ## Regions (`LeanQbe.T.region`) -/

theorem region_sep_elim {a : BitVec 64} {n : Nat} {F : Mem 64 → Prop} {M : Mem 64}
    (h : (region a n ⋆ F) M) : ∃ bs : List UInt8, bs.length = n ∧ (Eq (bs.At a) ⋆ F) M := by
  obtain ⟨f1, f2, hu, hd, ⟨bs, hl, rfl⟩, hF⟩ := h
  exact ⟨bs, hl, _, f2, hu, hd, rfl, hF⟩

theorem region_split {a : BitVec 64} {n1 n2 : Nat} (h : n1 + n2 ≤ 2 ^ 64) :
    region a (n1 + n2) = (region a n1 ⋆ region (a + BitVec.ofNat 64 n1) n2) := by
  funext f
  apply propext
  constructor
  · rintro ⟨bs, hl, rfl⟩
    have e := Mem.At_append_sep (bs.take n1) (bs.drop n1) a (by simp; omega)
    rw [List.take_append_drop, List.length_take, Nat.min_eq_left (by omega)] at e
    obtain ⟨f1, f2, hu, hd, h1, h2⟩ := (congrFun e (bs.At a)).mp rfl
    exact ⟨f1, f2, hu, hd, ⟨_, by simp; omega, h1.symm⟩, ⟨_, by simp; omega, h2.symm⟩⟩
  · rintro ⟨f1, f2, hu, hd, ⟨bs1, hl1, rfl⟩, ⟨bs2, hl2, rfl⟩⟩
    have e := Mem.At_append_sep bs1 bs2 a (by omega)
    rw [hl1] at e
    exact ⟨bs1 ++ bs2, by simp; omega, ((congrFun e f).mpr ⟨_, _, hu, hd, rfl, rfl⟩).symm⟩

theorem region_zero {a : BitVec 64} : region a 0 = ExtHashMap.emp := by
  funext f
  apply propext
  constructor
  · rintro ⟨bs, hl, rfl⟩
    rw [List.length_eq_zero_iff] at hl
    subst hl
    simp [ExtHashMap.emp, List.At]
  · intro hf
    refine ⟨[], rfl, ?_⟩
    simp [ExtHashMap.emp] at hf
    simp [hf, List.At]

theorem bytes_to_region {a : BitVec 64} {bs : List UInt8} {f : Mem 64}
    (h : bytes a bs f) : region a bs.length f :=
  ⟨bs, rfl, h.symm⟩

/-! ## The bytes of an array -/

/-- `n` bytes per value, little-endian. -/
def bytesN (n : Nat) (xs : List (BitVec 64)) : List UInt8 :=
  xs.flatMap fun v => Int.toBytes n v.toNat

theorem bytesN_length (n : Nat) (xs : List (BitVec 64)) :
    (bytesN n xs).length = n * xs.length := by
  induction xs with
  | nil => simp [bytesN]
  | cons x xs ih =>
    simp only [bytesN, List.flatMap_cons, List.length_append, Int.toBytes_length] at ih ⊢
    rw [ih, List.length_cons, Nat.mul_succ]; omega

theorem eq_nil_At (a : BitVec 64) : (emp : Mem 64 → Prop) = Eq (([] : List UInt8).At a) := by
  funext m; apply propext; constructor
  · intro h; rw [h]; apply ExtHashMap.ext_getElem?; intro k; simp [List.At]
  · intro h; rw [← h]; apply ExtHashMap.ext_getElem?; intro k; simp [List.At]

theorem eq_cons_At {n : Nat} (a v : BitVec 64) (bs : List UInt8) (h : n + bs.length ≤ 2 ^ 64) :
    (Eq ((Int.toBytes n v.toNat).At a) ⋆ Eq (bs.At (a + BitVec.ofNat 64 n))) =
      Eq ((Int.toBytes n v.toNat ++ bs).At a) := by
  rw [Mem.At_append_sep _ _ _ (by rw [Int.toBytes_length]; exact h), Int.toBytes_length]

private theorem bytesArray_eq (n : Nat) (arr : BitVec 64 → List (BitVec 64) → Mem 64 → Prop)
    (hnil : ∀ a, arr a [] = emp)
    (hcons : ∀ a x xs,
      arr a (x :: xs) = (Eq ((Int.toBytes n x.toNat).At a) ⋆ arr (a + BitVec.ofNat 64 n) xs))
    (a : BitVec 64) (xs : List (BitVec 64)) (h : n * xs.length ≤ 2 ^ 64) :
    arr a xs = Eq ((bytesN n xs).At a) := by
  induction xs generalizing a with
  | nil => rw [hnil, bytesN, List.flatMap_nil, eq_nil_At]
  | cons x xs ih =>
    have hl := bytesN_length n xs
    have h' : n * xs.length + n ≤ 2 ^ 64 := Nat.mul_succ n xs.length ▸ h
    rw [hcons, bytesN, List.flatMap_cons, ih _ (by omega)]
    exact eq_cons_At a x _ (by omega)

theorem byte1Array_eq (a : BitVec 64) (xs : List (BitVec 64)) (h : xs.length ≤ 2 ^ 64) :
    byte1Array a xs = Eq ((bytesN 1 xs).At a) :=
  bytesArray_eq 1 byte1Array byte1Array_nil byte1Array_cons a xs (by simpa using h)

theorem int4Array_eq (a : BitVec 64) (xs : List (BitVec 64)) (h : 4 * xs.length ≤ 2 ^ 64) :
    int4Array a xs = Eq ((bytesN 4 xs).At a) :=
  bytesArray_eq 4 int4Array int4Array_nil int4Array_cons a xs h

theorem word8Array_eq (a : BitVec 64) (xs : List (BitVec 64)) (h : 8 * xs.length ≤ 2 ^ 64) :
    word8Array a xs = Eq ((bytesN 8 xs).At a) :=
  bytesArray_eq 8 word8Array word8Array_nil word8Array_cons a xs h

theorem eq_append_At (a : BitVec 64) (b1 b2 : List UInt8) (h : b1.length + b2.length ≤ 2 ^ 64) :
    Eq ((b1 ++ b2).At a) = (Eq (b1.At a) ⋆ Eq (b2.At (a + BitVec.ofNat 64 b1.length))) :=
  Mem.At_append_sep _ _ _ h

theorem mem_at_cast {P : Mem 64 → Prop} {bs : List UInt8} {a : BitVec 64}
    (h : Eq (bs.At a) = P) : P (bs.At a) := h ▸ rfl

syntax "t_solve_bytes_at" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| t_solve_bytes_at) => `(tactic| t_solve_bytes_at [])
  | `(tactic| t_solve_bytes_at [$extra,*]) => `(tactic| (
      try simp only [sep_emp]
      repeat (first
        | rw [LeanQbe.T.byte1Array_eq _ _ (by simp)]
        | rw [LeanQbe.T.int4Array_eq _ _ (by simp)]
        | rw [LeanQbe.T.word8Array_eq _ _ (by simp [$extra,*])])
      refine LeanQbe.T.mem_at_cast ?_
      repeat rw [LeanQbe.T.eq_append_At _ _ _ (by simp [LeanQbe.T.bytesN_length, $extra,*])]
      simp only [LeanQbe.T.bytesN_length, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceMul, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, $extra,*]
      ac_rfl))

scoped syntax "solve_bytes_at" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| solve_bytes_at) => `(tactic| t_solve_bytes_at)
  | `(tactic| solve_bytes_at [$extra,*]) => `(tactic| t_solve_bytes_at [$extra,*])

/-! ## Byte lists in memory -/

theorem toBytes_u8 (b : UInt8) : Int.toBytes 1 (b.toNat : Int) = [b] := by
  have hb := b.toNat_lt
  simp only [Int.toBytes, Int.take]
  rw [Int.emod_eq_of_lt (by omega) (by omega)]
  simp

theorem loadu8_At {base : BitVec 64} {bs : List UInt8} {i : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hi : i < bs.length) (hlen : bs.length ≤ 2 ^ 64)
    (hm : (Eq (bs.At base) ⋆ R) m) :
    loadVal m i8 (base + BitVec.ofNat 64 i) = some (BitVec.ofNat 8 bs[i].toNat) := by
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
  rw [loadVal_toBytes_bits (n := 8) (by decide) hm']
  congr 1

theorem load_bytes_at {base : BitVec 64} {bs : List UInt8} {i : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hi : i < bs.length) (hlen : bs.length ≤ 2 ^ 64)
    (hm : (bytes base bs ⋆ R) m) :
    loadVal m i8 (base + BitVec.ofNat 64 i) = some (BitVec.ofNat 8 bs[i].toNat) :=
  loadu8_At hi hlen hm

theorem load_bytes_step {m : Mem 64} {p : BitVec 64} {Q : BitVec 8 → Prop}
    (base : BitVec 64) (i : Nat) {bs : List UInt8} {R : Mem 64 → Prop}
    (hi : i < bs.length) (hlen : bs.length ≤ 2 ^ 64)
    (hm : (bytes base bs ⋆ R) m) (heq : p = base + BitVec.ofNat 64 i := by rfl)
    (hk : Q (BitVec.ofNat 8 bs[i].toNat)) :
    ∃ x, loadVal m i8 p = some x ∧ Q x :=
  ⟨BitVec.ofNat 8 bs[i].toNat, heq ▸ load_bytes_at hi hlen hm, hk⟩

theorem expectByte_branch {base : BitVec 64} {bs : List UInt8} {i : Nat} {k : UInt8}
    {R : Mem 64 → Prop} {m : Mem 64} {P Q : Prop}
    (hbase : base.toNat + bs.length < 2 ^ 64) (hi : i ≤ bs.length) (hm : (Eq (bs.At base) ⋆ R) m)
    (heof : bs.drop i = [] → Q)
    (hmatch : ∀ (hlt : i < bs.length), bs[i] = k → P)
    (hmismatch : ∀ (hlt : i < bs.length), bs[i] ≠ k → Q) :
    (base + BitVec.ofNat 64 i = base + BitVec.ofNat 64 bs.length → Q) ∧
    (base + BitVec.ofNat 64 i ≠ base + BitVec.ofNat 64 bs.length →
      ∃ v, loadVal m i8 (base + BitVec.ofNat 64 i) = some v ∧
        ((v = BitVec.ofNat 8 k.toNat → P) ∧ (v ≠ BitVec.ofNat 8 k.toNat → Q))) := by
  refine cursor_eof_branch hi (by omega) (fun heq => heof (by rw [heq]; simp))
    (fun hlt => ⟨_, loadu8_At hlt (by omega) hm, ?_, ?_⟩)
  · intro heq
    apply hmatch hlt
    have hk : bs[i].toNat = k.toNat := by
      have h1 := congrArg BitVec.toNat heq
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bs[i].toNat_lt,
        Nat.mod_eq_of_lt k.toNat_lt] at h1
      exact h1
    exact UInt8.toBitVec_inj.mp (BitVec.eq_of_toNat_eq hk)
  · intro hne
    apply hmismatch hlt
    intro heq
    apply hne
    subst heq
    rfl

/-! ## Regions and Bedrock2 arrays -/

theorem byte1Array_to_region {a : BitVec 64} {xs : List (BitVec 64)} {f : Mem 64}
    (h : xs.length ≤ 2 ^ 64) (hf : byte1Array a xs f) :
    region a xs.length f := by
  rw [byte1Array_eq a xs h] at hf
  exact ⟨bytesN 1 xs, by simp [bytesN_length], hf.symm⟩

theorem int4Array_to_region {a : BitVec 64} {xs : List (BitVec 64)} {f : Mem 64}
    (h : 4 * xs.length ≤ 2 ^ 64) (hf : int4Array a xs f) :
    region a (4 * xs.length) f := by
  rw [int4Array_eq a xs h] at hf
  exact ⟨bytesN 4 xs, by simp [bytesN_length], hf.symm⟩

theorem word8Array_to_region {a : BitVec 64} {xs : List (BitVec 64)} {f : Mem 64}
    (h : 8 * xs.length ≤ 2 ^ 64) (hf : word8Array a xs f) :
    region a (8 * xs.length) f := by
  rw [word8Array_eq a xs h] at hf
  exact ⟨bytesN 8 xs, by simp [bytesN_length], hf.symm⟩

private theorem toBytes_ofBytes_toNat {n : Nat} {bs : List UInt8}
    (hn : n = 1 ∨ n = 4 ∨ n = 8) (hl : bs.length = n) :
    Int.toBytes n ((BitVec.ofInt 64 (Int.ofBytes bs)).toNat : Int) = bs := by
  grind

private theorem region_to_bytes_array {n : Nat}
    (arr : BitVec 64 → List (BitVec 64) → Mem 64 → Prop)
    (hnil : ∀ a, arr a [] = emp)
    (hcons : ∀ a v vs,
      arr a (v :: vs) = (Eq ((Int.toBytes n v.toNat).At a) ⋆ arr (a + BitVec.ofNat 64 n) vs))
    (hn : n = 1 ∨ n = 4 ∨ n = 8) (a : BitVec 64) (k : Nat) (hk : n * k ≤ 2 ^ 64) :
    ∀ {f : Mem 64}, region a (n * k) f → ∃ xs : List (BitVec 64), xs.length = k ∧ arr a xs f := by
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
    let v : BitVec 64 := BitVec.ofInt 64 (Int.ofBytes bs1)
    have hv : Int.toBytes n v.toNat = bs1 := toBytes_ofBytes_toNat hn hl1
    refine ⟨v :: xs, by simp [hxs], ?_⟩
    rw [hcons, hv]
    exact ⟨_, f2, hu, hd, rfl, h2⟩

theorem region_to_byte1Array {a : BitVec 64} (k : Nat) (hk : k ≤ 2 ^ 64) {f : Mem 64}
    (hf : region a k f) :
    ∃ xs : List (BitVec 64), xs.length = k ∧ byte1Array a xs f :=
  region_to_bytes_array byte1Array (fun _ => rfl) (fun _ _ _ => rfl)
    (Or.inl rfl) a k (by omega) (by simpa using hf)

theorem region_to_int4Array {a : BitVec 64} (k : Nat) (hk : 4 * k ≤ 2 ^ 64) {f : Mem 64}
    (hf : region a (4 * k) f) :
    ∃ xs : List (BitVec 64), xs.length = k ∧ int4Array a xs f :=
  region_to_bytes_array int4Array (fun _ => rfl) (fun _ _ _ => rfl)
    (Or.inr (Or.inl rfl)) a k hk hf

theorem region_to_word8Array {a : BitVec 64} (k : Nat) (hk : 8 * k ≤ 2 ^ 64) {f : Mem 64}
    (hf : region a (8 * k) f) :
    ∃ xs : List (BitVec 64), xs.length = k ∧ word8Array a xs f :=
  region_to_bytes_array word8Array (fun _ => rfl) (fun _ _ _ => rfl)
    (Or.inr (Or.inr rfl)) a k hk hf

theorem region_pop_int4 {a : BitVec 64} {rem : Nat} (hrem : 0 < rem)
    (hfit : 4 * rem ≤ 2 ^ 64) {f : Mem 64} (hf : region a (4 * rem) f) :
    ∃ v0 : BitVec 64, (int4 a v0 ⋆ region (a + 4) (4 * (rem - 1))) f := by
  have heq : 4 * rem = 4 * 1 + 4 * (rem - 1) := by omega
  rw [heq, region_split (by omega)] at hf
  obtain ⟨f1, f2, hu, hd, hf1, hf2⟩ := hf
  obtain ⟨xs, hxs, h1⟩ := region_to_int4Array 1 (by omega) hf1
  rcases xs with _ | ⟨v0, _ | _⟩ <;> simp at hxs
  simp only [int4Array_cons, int4Array_nil, sep_emp] at h1
  exact ⟨v0, f1, f2, hu, hd, h1, by simpa using hf2⟩

theorem region_pop_store_int4 {wcur : BitVec 64} {rem : Nat} (v : BitVec 32)
    {R : Mem 64 → Prop} {m : Mem 64} (hrem : 0 < rem) (hfit : 4 * rem ≤ 2 ^ 64)
    (hm : (region wcur (4 * rem) ⋆ R) m) :
    storeOk m i32 wcur ∧
    (int4 wcur (v.setWidth 64) ⋆ region (wcur + 4) (4 * (rem - 1)) ⋆ R) (storeMem m i32 wcur v) := by
  obtain ⟨f_w, f_rest, hu, hd, hf_w, hf_rest⟩ := hm
  obtain ⟨v0, hv0_cell⟩ := region_pop_int4 hrem hfit hf_w
  have hm_cell : ((int4 wcur v0 ⋆ region (wcur + 4) (4 * (rem - 1))) ⋆ R) m :=
    ⟨f_w, f_rest, hu, hd, hv0_cell, hf_rest⟩
  rw [sep_assoc] at hm_cell
  obtain ⟨ok, hm'⟩ := store_int4 v hm_cell
  exact ⟨ok, sep_cast hm' (by ac_rfl)⟩

theorem region_merge_eq {a : BitVec 64} {n1 n2 n : Nat}
    (hsum : n1 + n2 = n) (hfit : n ≤ 2 ^ 64) :
    (region a n1 ⋆ region (a + BitVec.ofNat 64 n1) n2) = region a n := by
  subst hsum
  exact (region_split (a := a) (n1 := n1) (n2 := n2) hfit).symm

theorem region_pop_store_int4_64 {wcur : BitVec 64} {rem : Nat} (v : BitVec 64)
    {R : Mem 64 → Prop} {m : Mem 64} (hrem : 0 < rem) (hfit : 4 * rem ≤ 2 ^ 64)
    (hm : (region wcur (4 * rem) ⋆ R) m) :
    storeOk m i32 wcur ∧
    (int4 wcur v ⋆ region (wcur + 4) (4 * (rem - 1)) ⋆ R)
      (storeMem m i32 wcur (v.setWidth 32)) := by
  obtain ⟨hok, hm'⟩ := region_pop_store_int4 (v.setWidth 32) hrem hfit hm
  rw [int4_setWidth32] at hm'
  exact ⟨hok, hm'⟩

theorem cursor_loadu8_branch {base : BitVec 64} {bs : List UInt8} {i : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} {P : Prop} {Q : BitVec 8 → Prop}
    (hbase : base.toNat + bs.length < 2 ^ 64) (hi : i ≤ bs.length)
    (hm : (Eq (bs.At base) ⋆ R) m)
    (heof : i = bs.length → bs.drop i = [] → P)
    (hstep : ∀ (hlt : i < bs.length), bs.drop i = bs[i] :: bs.drop (i + 1) →
      Q (BitVec.ofNat 8 bs[i].toNat)) :
    (base + BitVec.ofNat 64 i = base + BitVec.ofNat 64 bs.length → P) ∧
    (base + BitVec.ofNat 64 i ≠ base + BitVec.ofNat 64 bs.length →
      ∃ v, loadVal m i8 (base + BitVec.ofNat 64 i) = some v ∧ Q v) :=
  cursor_eof_branch hi (by omega)
    (fun heq => heof heq (by simp [heq]))
    (fun hlt => ⟨_, loadu8_At hlt (by omega) hm, hstep hlt (List.drop_eq_getElem_cons hlt)⟩)

theorem expectByte_step {base : BitVec 64} {bs : List UInt8} {i : Nat} (k : UInt8)
    {R : Mem 64 → Prop} {m : Mem 64} {P Q : Prop}
    (hbase : base.toNat + bs.length < 2 ^ 64) (hi : i ≤ bs.length)
    (hm : (Eq (bs.At base) ⋆ R) m)
    (heof : bs.drop i = [] → Q)
    (hmis : ∀ b rest, bs.drop i = b :: rest → b ≠ k → Q)
    (hmatch : i + 1 ≤ bs.length → bs.drop i = k :: bs.drop (i + 1) → P) :
    (base + BitVec.ofNat 64 i = base + BitVec.ofNat 64 bs.length → Q) ∧
    (base + BitVec.ofNat 64 i ≠ base + BitVec.ofNat 64 bs.length →
      ∃ v, loadVal m i8 (base + BitVec.ofNat 64 i) = some v ∧
        ((v.setWidth 64 = BitVec.ofNat 64 k.toNat → P) ∧
         (v.setWidth 64 ≠ BitVec.ofNat 64 k.toNat → Q))) := by
  refine cursor_loadu8_branch hbase hi hm (fun _ hnil => heof hnil) (fun hlt hdrop => ?_)
  rw [setWidth64_ofNat8]
  exact ⟨fun heq => hmatch hlt (by rwa [bv64_u8_eq.mp heq] at hdrop),
    fun hne => hmis bs[i] (bs.drop (i + 1)) hdrop (fun h => hne (bv64_u8_eq.mpr h))⟩

end LeanQbe.T
