module

public import LeanQbe.T.Logic.U32
public import LeanQbe.T.Logic.Bytes
public import LeanQbe.T.Logic.Cells
public import LeanQbe.T.Logic.MemLemmas
public import LeanQbe.T.Logic.C0StepAttr
public import LeanQbe.T.OpsLemmas

set_option autoImplicit false

/-!
Shared separation-logic and memory-algebra helpers (`MemAlgebra`).

All memory theorems use public bridge lemmas only (`0` `import all Kraken.{Mem,Separation}`).
Includes `storeBytes_*` / `loadBytes_*`, `sep_append_bytes`, `region` / `array` / `cell` /
`array64_split3` conversions, `pack64` / `repr64Get` / `repr64Set`, `@[c0_load]` and
`@[c0_store]` extensions, `boxNat_*`, and generic `List`/`Perm`/`Nodup` helpers.
-/

public section

namespace LeanQbe.T

open Std.ExtHashMap
open Kraken.Bedrock2.Test

/-! ## Separation logic & byte-store helpers (public bridges only) -/

theorem sep_mono_left {P P' Q : Mem 64 → Prop}
    (h : ∀ m, P m → P' m) {m : Mem 64} (hm : (P ⋆ Q) m) : (P' ⋆ Q) m :=
  sep_mono h hm

theorem sep_exists_l {α : Type} (P : α → Mem 64 → Prop) (R : Mem 64 → Prop) {m : Mem 64} :
    ((fun m => ∃ x, P x m) ⋆ R) m ↔ ∃ x, (P x ⋆ R) m :=
  sep_ex_l

theorem sep_exists_r {α : Type} (P : Mem 64 → Prop) (R : α → Mem 64 → Prop) {m : Mem 64} :
    (P ⋆ fun m => ∃ x, R x m) m ↔ ∃ x, (P ⋆ R x) m :=
  sep_ex_r

theorem sep_pure_left_iff {φ : Prop} {P R : Mem 64 → Prop} {m : Mem 64} :
    ((fun m => φ ∧ P m) ⋆ R) m ↔ φ ∧ (P ⋆ R) m :=
  sep_pure_l

theorem sep_pure_right_iff {φ : Prop} {P R : Mem 64 → Prop} {m : Mem 64} :
    (P ⋆ fun m => φ ∧ R m) m ↔ φ ∧ (P ⋆ R) m :=
  sep_pure_r

theorem bytes_to_region_sep {m : Mem 64} {a : BitVec 64} {bs : List UInt8}
    {R : Mem 64 → Prop} (h : (bytes a bs ⋆ R) m) :
    (region a bs.length ⋆ R) m :=
  sep_mono (fun _ hf => bytes_to_region hf) h

theorem storeBytes_nil (m : Mem 64) (a : BitVec 64) : m.storeBytes a [] = m := by
  have hsep : (emp ⋆ Eq m) m := by
    rw [emp_sep]
  rw [eq_nil_At a] at hsep
  have hst := Mem.storeBytes_sep a 0 [] [] (Eq m) m ⟨hsep, rfl, rfl⟩
  rw [← eq_nil_At a, emp_sep] at hst
  exact hst.symm

theorem loadBytes_zero (m : Mem 64) (a : BitVec 64) : m.loadBytes a 0 = some [] := by
  have hsep : (emp ⋆ Eq m) m := by
    rw [emp_sep]
  rw [eq_nil_At a] at hsep
  exact Mem.loadBytes_sep [] a 0 (Eq m) m hsep rfl (by omega)

theorem storeBytes_sep_At {m : Mem 64} {a : BitVec 64} {oldbs newbs : List UInt8}
    {R : Mem 64 → Prop} (hlen : newbs.length = oldbs.length)
    (h : (Eq (oldbs.At a) ⋆ R) m) :
    (Eq (newbs.At a) ⋆ R) (m.storeBytes a newbs) :=
  Mem.storeBytes_sep a oldbs.length oldbs newbs R m ⟨h, rfl, hlen⟩

theorem storeBytes_sep_bytes {m : Mem 64} {a : BitVec 64} {oldbs newbs : List UInt8}
    {R : Mem 64 → Prop} (hlen : newbs.length = oldbs.length)
    (h : (bytes a oldbs ⋆ R) m) :
    (bytes a newbs ⋆ R) (m.storeBytes a newbs) :=
  storeBytes_sep_At hlen h

theorem storeBytes_region_sep {m : Mem 64} {a : BitVec 64} {n : Nat}
    {newbs : List UInt8} {R : Mem 64 → Prop}
    (hlen : newbs.length = n) (h : (region a n ⋆ R) m) :
    (bytes a newbs ⋆ R) (m.storeBytes a newbs) := by
  rcases region_sep_elim h with ⟨oldbs, hold, hsep⟩
  exact storeBytes_sep_bytes (hlen.trans hold.symm) hsep

theorem loadBytes_sep_bytes {m : Mem 64} {a : BitVec 64} {bs : List UInt8}
    {R : Mem 64 → Prop} (hfit : bs.length ≤ 2 ^ 64) (h : (bytes a bs ⋆ R) m) :
    m.loadBytes a bs.length = some bs :=
  Mem.loadBytes_sep bs a bs.length R m h rfl hfit

theorem sep_append_bytes (a : BitVec 64) (bs1 bs2 : List UInt8)
    (hfit : bs1.length + bs2.length ≤ 2 ^ 64 := by omega) :
    bytes a (bs1 ++ bs2) =
      (bytes a bs1 ⋆ bytes (a + BitVec.ofNat 64 bs1.length) bs2) :=
  eq_append_At a bs1 bs2 hfit

theorem sep_append_bytes_eq {a : BitVec 64} {bs1 bs2 : List UInt8} {p : BitVec 64}
    (hp : p = a + BitVec.ofNat 64 bs1.length)
    (hfit : bs1.length + bs2.length ≤ 2 ^ 64 := by omega) :
    bytes a (bs1 ++ bs2) = (bytes a bs1 ⋆ bytes p bs2) := by
  subst hp
  exact eq_append_At a bs1 bs2 hfit

theorem sep_append_bytes_join {m : Mem 64} {a : BitVec 64} {bs1 bs2 : List UInt8}
    {R : Mem 64 → Prop} (hfit : bs1.length + bs2.length ≤ 2 ^ 64)
    (h : ((bytes a bs1 ⋆ bytes (a + BitVec.ofNat 64 bs1.length) bs2) ⋆ R) m) :
    (bytes a (bs1 ++ bs2) ⋆ R) m := by
  rw [sep_append_bytes a bs1 bs2 hfit]
  exact h

theorem storeBytes_sep_append {m : Mem 64} {a : BitVec 64}
    {old1 old2 new1 new2 : List UInt8} {R : Mem 64 → Prop}
    (h1 : new1.length = old1.length) (h2 : new2.length = old2.length)
    (hfit : old1.length + old2.length ≤ 2 ^ 64)
    (h : (bytes a (old1 ++ old2) ⋆ R) m) :
    let m1 := m.storeBytes a new1
    (bytes a (new1 ++ new2) ⋆ R)
      (m1.storeBytes (a + BitVec.ofNat 64 new1.length) new2) := by
  dsimp only
  rw [sep_append_bytes a old1 old2 hfit, sep_assoc] at h
  have hm1 := storeBytes_sep_bytes h1 h
  rw [← sep_assoc, sep_comm (bytes a new1) (bytes (a + BitVec.ofNat 64 old1.length) old2),
    sep_assoc, ← h1] at hm1
  have hm2 := storeBytes_sep_bytes h2 hm1
  rw [← sep_assoc, sep_comm (bytes (a + BitVec.ofNat 64 new1.length) new2) (bytes a new1)] at hm2
  have hfit' : new1.length + new2.length ≤ 2 ^ 64 := by omega
  rwa [← sep_append_bytes a new1 new2 hfit'] at hm2

theorem storeBytes_region_append_sep {m : Mem 64} {a : BitVec 64}
    {n1 n2 : Nat} {new1 new2 : List UInt8} {R : Mem 64 → Prop}
    (h1 : new1.length = n1) (h2 : new2.length = n2) (hfit : n1 + n2 ≤ 2 ^ 64)
    (h : (region a (n1 + n2) ⋆ R) m) :
    let m1 := m.storeBytes a new1
    (bytes a (new1 ++ new2) ⋆ R) (m1.storeBytes (a + BitVec.ofNat 64 n1) new2) := by
  rcases region_sep_elim h with ⟨old, hold, hsep⟩
  have htake : (old.take n1).length = n1 := by rw [List.length_take]; omega
  have hdrop : (old.drop n1).length = n2 := by rw [List.length_drop]; omega
  rw [← List.take_append_drop n1 old] at hsep
  have hres := storeBytes_sep_append (h1.trans htake.symm) (h2.trans hdrop.symm)
    (by omega) hsep
  simpa [h1] using hres

theorem storeInt_region_sep {m : Mem 64} {a : BitVec 64} {n : Nat}
    {R : Mem 64 → Prop} (v : Int) (h : (region a n ⋆ R) m) :
    (bytes a (Int.toBytes n v) ⋆ R) (m.storeInt a n v) := by
  rcases region_sep_elim h with ⟨old, hold, hsep⟩
  exact Mem.storeInt_sep a n old R m ⟨hsep, hold⟩ v

theorem storeOk_storeMem_self {m : Mem 64} {t : Ty} {a : BitVec 64}
    {v : Val t} {P R : Mem 64 → Prop}
    (hst : storeOk m t a ∧ (P ⋆ R) (storeMem m t a v)) :
    storeOk m t a ∧ (P ⋆ R) (storeMem m t a v) :=
  hst

/-! ## `bytesOf` / `bytes64` / `bytesN` / `region` / `cell` / `array` bridges -/

private theorem int_toBytes_length : ∀ (n : Nat) (v : Int), (Int.toBytes n v).length = n
  | 0, _ => by simp [Int.toBytes.eq_1]
  | n + 1, v => by simp [Int.toBytes.eq_2, int_toBytes_length n (v / 256)]

theorem bytesOf_nil {t : Ty} : bytesOf ([] : List (Val t)) = [] := by
  simp [bytesOf]

theorem bytesOf_cons {t : Ty} (v : Val t) (vs : List (Val t)) :
    bytesOf (v :: vs) =
      Int.toBytes t.bytes (BitVec.setWidth (8 * t.bytes) (toBits t v)).toInt ++ bytesOf vs := by
  simp [bytesOf]

theorem bytesOf_append {t : Ty} (xs ys : List (Val t)) :
    bytesOf (xs ++ ys) = bytesOf xs ++ bytesOf ys := by
  simp [bytesOf, List.flatMap_append]

theorem bytes64_nil : bytes64 [] = [] := by
  simp [bytes64]

theorem bytes64_cons (v : BitVec 64) (vs : List (BitVec 64)) :
    bytes64 (v :: vs) = Int.toBytes 8 v.toInt ++ bytes64 vs := by
  simp [bytes64]

theorem bytes64_append (xs ys : List (BitVec 64)) :
    bytes64 (xs ++ ys) = bytes64 xs ++ bytes64 ys := by
  simp [bytes64, List.flatMap_append]

theorem bytesN_nil (n : Nat) : bytesN n [] = [] := by
  simp [bytesN]

theorem bytesN_cons (n : Nat) (v : BitVec 64) (vs : List (BitVec 64)) :
    bytesN n (v :: vs) = Int.toBytes n (v.toNat : Int) ++ bytesN n vs := by
  simp [bytesN]

theorem bytesN_append (n : Nat) (xs ys : List (BitVec 64)) :
    bytesN n (xs ++ ys) = bytesN n xs ++ bytesN n ys := by
  simp [bytesN, List.flatMap_append]

theorem region_split_sep {m : Mem 64} {a : BitVec 64} (n1 n2 : Nat) {R : Mem 64 → Prop}
    (hfit : n1 + n2 ≤ 2 ^ 64) (h : (region a (n1 + n2) ⋆ R) m) :
    (region a n1 ⋆ region (a + BitVec.ofNat 64 n1) n2 ⋆ R) m := by
  rw [region_split hfit] at h
  exact h

theorem cell_eq_bytesOf {t : Ty} (a : BitVec 64) (v : Val t) (ht : t.bytes ≤ 2 ^ 64) :
    cell a v = Eq ((bytesOf [v]).At a) := by
  funext m
  apply propext
  have h1 : cell a v = array a [v] := by
    rw [array_cons, array_nil, sep_emp]
  rw [h1]
  refine ⟨fun hm => (array_eq_bytesOf a [v] (by simpa using ht) hm).symm, ?_⟩
  intro hm
  change (bytesOf [v]).At a = m at hm
  subst hm
  exact array_bytes a [v] (by simpa using ht)

theorem cell_eq_At {t : Ty} (a : BitVec 64) (v : Val t) (ht : t.bytes ≤ 2 ^ 64) :
    cell a v =
      Eq ((Int.toBytes t.bytes (BitVec.setWidth (8 * t.bytes) (toBits t v)).toInt).At a) := by
  have hc := cell_eq_bytesOf a v ht
  simpa [bytesOf_cons, bytesOf_nil] using hc

theorem cell64_eq_At (a v : BitVec 64) :
    cell64 a v = Eq ((Int.toBytes 8 v.toInt).At a) := by
  have hcb := cell64_bytes a v
  rw [cell64_eq_cell, cell_eq_bytesOf (t := i64) a v (by decide)] at hcb ⊢
  change ((bytesOf (t := i64) [v]).At a) = ((Int.toBytes 8 v.toInt).At a) at hcb
  rw [hcb]

theorem cell_to_region {t : Ty} (a : BitVec 64) (v : Val t) (ht : t.bytes ≤ 2 ^ 64)
    {m : Mem 64} (hm : cell a v m) : region a t.bytes m := by
  rw [cell_eq_At a v ht] at hm
  change _ = m at hm
  subst hm
  exact ⟨_, int_toBytes_length _ _, rfl⟩

theorem cell64_to_region (a v : BitVec 64) {m : Mem 64} (hm : cell64 a v m) :
    region a 8 m := by
  rw [cell64_eq_cell] at hm
  exact cell_to_region (t := i64) a v (by decide) hm

theorem word8Array_eq_array64 (a : BitVec 64) (xs : List (BitVec 64)) :
    word8Array a xs = array64 a xs := by
  induction xs generalizing a with
  | nil => rw [word8Array_nil, array64_nil]
  | cons v vs ih =>
    rw [word8Array_cons, array64_cons, ← cell64_eq_word8, ih]

theorem region_to_word8 {a : BitVec 64} {m : Mem 64} (hm : region a 8 m) :
    ∃ v : BitVec 64, word8 a v m := by
  rcases region_to_word8Array 1 (by omega) hm with ⟨xs, hlen, hxs⟩
  rcases List.length_eq_one_iff.mp hlen with ⟨v, rfl⟩
  rw [word8Array_cons, word8Array_nil, sep_emp] at hxs
  exact ⟨v, hxs⟩

theorem region_to_cell64 {a : BitVec 64} {m : Mem 64} (hm : region a 8 m) :
    ∃ v : BitVec 64, cell64 a v m := by
  rcases region_to_word8 hm with ⟨v, hv⟩
  rw [← cell64_eq_word8] at hv
  exact ⟨v, hv⟩

theorem region_to_array64 {a : BitVec 64} (k : Nat) (hfit : 8 * k ≤ 2 ^ 64)
    {m : Mem 64} (hm : region a (8 * k) m) :
    ∃ xs : List (BitVec 64), xs.length = k ∧ array64 a xs m := by
  rcases region_to_word8Array k hfit hm with ⟨xs, hlen, hxs⟩
  rw [word8Array_eq_array64] at hxs
  exact ⟨xs, hlen, hxs⟩

theorem array_to_region {t : Ty} (a : BitVec 64) (xs : List (Val t))
    (hfit : t.bytes * xs.length ≤ 2 ^ 64) {m : Mem 64} (hm : array a xs m) :
    region a (t.bytes * xs.length) m := by
  have heq := array_eq_bytesOf a xs hfit hm
  subst heq
  simpa [bytesOf_length] using
    bytes_to_region (a := a) (bs := bytesOf xs) (f := (bytesOf xs).At a) rfl

theorem array64_to_region (a : BitVec 64) (xs : List (BitVec 64))
    (hfit : 8 * xs.length ≤ 2 ^ 64) {m : Mem 64} (hm : array64 a xs m) :
    region a (8 * xs.length) m := by
  rw [array64_eq_array] at hm
  exact array_to_region (t := i64) a xs hfit hm

/-! ## `array_split*`, `array64_split*`, `word8Array_split*`, `pack64` / `repr64` -/

theorem array_split2 {t : Ty} (a : BitVec 64) (xs1 xs2 : List (Val t)) :
    array a (xs1 ++ xs2) =
      (array a xs1 ⋆ array (a + BitVec.ofNat 64 (t.bytes * xs1.length)) xs2) :=
  array_append a xs1 xs2

theorem array_split3 {t : Ty} (a : BitVec 64) (xs1 xs2 xs3 : List (Val t)) :
    array a (xs1 ++ xs2 ++ xs3) =
      (array a xs1 ⋆
        array (a + BitVec.ofNat 64 (t.bytes * xs1.length)) xs2 ⋆
        array (a + BitVec.ofNat 64 (t.bytes * (xs1 ++ xs2).length)) xs3) := by
  rw [array_append a (xs1 ++ xs2) xs3, array_append a xs1 xs2, sep_assoc]

theorem array_join3 {t : Ty} {m : Mem 64} (a : BitVec 64)
    (xs1 xs2 xs3 : List (Val t)) {R : Mem 64 → Prop}
    (h : (array a xs1 ⋆
      array (a + BitVec.ofNat 64 (t.bytes * xs1.length)) xs2 ⋆
      array (a + BitVec.ofNat 64 (t.bytes * (xs1 ++ xs2).length)) xs3 ⋆ R) m) :
    (array a (xs1 ++ xs2 ++ xs3) ⋆ R) m := by
  rw [array_split3 a xs1 xs2 xs3]
  exact h

theorem array64_split2 (a : BitVec 64) (xs1 xs2 : List (BitVec 64)) :
    array64 a (xs1 ++ xs2) =
      (array64 a xs1 ⋆ array64 (a + BitVec.ofNat 64 (8 * xs1.length)) xs2) :=
  array64_append a xs1 xs2

theorem array64_split3 (a : BitVec 64) (xs1 xs2 xs3 : List (BitVec 64)) :
    array64 a (xs1 ++ xs2 ++ xs3) =
      (array64 a xs1 ⋆
        array64 (a + BitVec.ofNat 64 (8 * xs1.length)) xs2 ⋆
        array64 (a + BitVec.ofNat 64 (8 * (xs1 ++ xs2).length)) xs3) := by
  rw [array64_append a (xs1 ++ xs2) xs3, array64_append a xs1 xs2, sep_assoc]

theorem array64_join3 {m : Mem 64} (a : BitVec 64)
    (xs1 xs2 xs3 : List (BitVec 64)) {R : Mem 64 → Prop}
    (h : (array64 a xs1 ⋆
      array64 (a + BitVec.ofNat 64 (8 * xs1.length)) xs2 ⋆
      array64 (a + BitVec.ofNat 64 (8 * (xs1 ++ xs2).length)) xs3 ⋆ R) m) :
    (array64 a (xs1 ++ xs2 ++ xs3) ⋆ R) m := by
  rw [array64_split3 a xs1 xs2 xs3]
  exact h

theorem array64_bytes_split3 (a : BitVec 64) (xs1 xs2 xs3 : List (BitVec 64))
    (hfit : 8 * (xs1 ++ xs2 ++ xs3).length ≤ 2 ^ 64) :
    (array64 a xs1 ⋆
      array64 (a + BitVec.ofNat 64 (8 * xs1.length)) xs2 ⋆
      array64 (a + BitVec.ofNat 64 (8 * (xs1 ++ xs2).length)) xs3)
      ((bytes64 (xs1 ++ xs2 ++ xs3)).At a) := by
  rw [← array64_split3 a xs1 xs2 xs3]
  exact array64_bytes a (xs1 ++ xs2 ++ xs3) hfit

theorem word8Array_split2 (a : BitVec 64) (xs1 xs2 : List (BitVec 64)) :
    word8Array a (xs1 ++ xs2) =
      (word8Array a xs1 ⋆ word8Array (a + BitVec.ofNat 64 (8 * xs1.length)) xs2) :=
  word8Array_append a xs1 xs2

theorem word8Array_split3 (a : BitVec 64) (xs1 xs2 xs3 : List (BitVec 64)) :
    word8Array a (xs1 ++ xs2 ++ xs3) =
      (word8Array a xs1 ⋆
        word8Array (a + BitVec.ofNat 64 (8 * xs1.length)) xs2 ⋆
        word8Array (a + BitVec.ofNat 64 (8 * (xs1 ++ xs2).length)) xs3) := by
  rw [word8Array_append a (xs1 ++ xs2) xs3, word8Array_append a xs1 xs2, sep_assoc]

theorem word8Array_join3 {m : Mem 64} (a : BitVec 64)
    (xs1 xs2 xs3 : List (BitVec 64)) {R : Mem 64 → Prop}
    (h : (word8Array a xs1 ⋆
      word8Array (a + BitVec.ofNat 64 (8 * xs1.length)) xs2 ⋆
      word8Array (a + BitVec.ofNat 64 (8 * (xs1 ++ xs2).length)) xs3 ⋆ R) m) :
    (word8Array a (xs1 ++ xs2 ++ xs3) ⋆ R) m := by
  rw [word8Array_split3 a xs1 xs2 xs3]
  exact h

theorem byte1Array_split3 (a : BitVec 64) (xs1 xs2 xs3 : List (BitVec 64)) :
    byte1Array a (xs1 ++ xs2 ++ xs3) =
      (byte1Array a xs1 ⋆
        byte1Array (a + BitVec.ofNat 64 xs1.length) xs2 ⋆
        byte1Array (a + BitVec.ofNat 64 (xs1 ++ xs2).length) xs3) := by
  rw [byte1Array_append a (xs1 ++ xs2) xs3, byte1Array_append a xs1 xs2, sep_assoc]

theorem int4Array_split3 (a : BitVec 64) (xs1 xs2 xs3 : List (BitVec 64)) :
    int4Array a (xs1 ++ xs2 ++ xs3) =
      (int4Array a xs1 ⋆
        int4Array (a + BitVec.ofNat 64 (4 * xs1.length)) xs2 ⋆
        int4Array (a + BitVec.ofNat 64 (4 * (xs1 ++ xs2).length)) xs3) := by
  rw [int4Array_append a (xs1 ++ xs2) xs3, int4Array_append a xs1 xs2, sep_assoc]

private theorem int_take8_mod (a b : Int) (h : a % (256 : Int) = b % (256 : Int)) :
    (a.take 8).toNat = (b.take 8).toNat := by
  have h1 : a.take 8 = a % 256 := rfl
  have h2 : b.take 8 = b % 256 := rfl
  rw [h1, h2, h]

private theorem int_ediv_mod_pow (n : Nat) (a b : Int)
    (h : a % (2 ^ (8 * (n + 1)) : Int) = b % (2 ^ (8 * (n + 1)) : Int)) :
    (a / 256) % (2 ^ (8 * n) : Int) = (b / 256) % (2 ^ (8 * n) : Int) := by
  let M : Int := 2 ^ (8 * n)
  have hM : (0 : Int) < M := Int.pow_pos (by omega)
  have hpow : (2 ^ (8 * (n + 1)) : Int) = 256 * M := by
    have hn : 8 * (n + 1) = 8 + 8 * n := by omega
    rw [hn, Int.pow_add]
    rfl
  rw [hpow] at h
  have decomp (x : Int) :
      (x / 256) % M = (x % (256 * M)) / 256 := by
    have hx : x = 256 * M * (x / (256 * M)) + x % (256 * M) :=
      (Int.mul_ediv_add_emod x (256 * M)).symm
    have hrem_nn : 0 ≤ x % (256 * M) := Int.emod_nonneg x (by omega)
    have hrem_lt : x % (256 * M) < 256 * M := Int.emod_lt_of_pos x (by omega)
    have hq : x / 256 = M * (x / (256 * M)) + (x % (256 * M)) / 256 := by
      have hx2 : x = 256 * (M * (x / (256 * M))) + x % (256 * M) := by
        rw [← Int.mul_assoc]
        exact hx
      rw [← Int.mul_add_ediv_left (M * (x / (256 * M))) (x % (256 * M)) (by omega), ← hx2]
    rw [hq, Int.add_comm (M * _), Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt (Int.ediv_nonneg hrem_nn (by omega))
      (Int.ediv_lt_of_lt_mul (by omega) (by omega))
  rw [decomp a, decomp b, h]

private theorem int_toBytes_mod_eq :
    ∀ (n : Nat) (a b : Int),
      a % (2 ^ (8 * n) : Int) = b % (2 ^ (8 * n) : Int) →
      Int.toBytes n a = Int.toBytes n b
  | 0, _, _, _ => by simp [Int.toBytes.eq_1]
  | n + 1, a, b, h => by
    rw [Int.toBytes.eq_2, Int.toBytes.eq_2]
    have hpow : (2 ^ (8 * (n + 1)) : Int) = 256 * (2 ^ (8 * n) : Int) := by
      have hn : 8 * (n + 1) = 8 + 8 * n := by omega
      rw [hn, Int.pow_add]
      rfl
    have hmod256 : a % (256 : Int) = b % (256 : Int) := by
      have hd : (256 : Int) ∣ (2 ^ (8 * (n + 1)) : Int) := ⟨2 ^ (8 * n), hpow⟩
      calc a % 256 = (a % (2 ^ (8 * (n + 1)) : Int)) % 256 := (Int.emod_emod_of_dvd a hd).symm
        _ = (b % (2 ^ (8 * (n + 1)) : Int)) % 256 := by rw [h]
        _ = b % 256 := Int.emod_emod_of_dvd b hd
    have hhead : (a.take 8).toNat.toUInt8 = (b.take 8).toNat.toUInt8 :=
      congrArg Nat.toUInt8 (int_take8_mod a b hmod256)
    have htail : Int.toBytes n (a / 256) = Int.toBytes n (b / 256) :=
      int_toBytes_mod_eq n (a / 256) (b / 256) (int_ediv_mod_pow n a b h)
    rw [hhead, htail]

theorem toBytes_bv_toInt_eq_toNat {n : Nat} (x : BitVec (8 * n)) :
    Int.toBytes n x.toInt = Int.toBytes n (x.toNat : Int) := by
  apply int_toBytes_mod_eq n
  rw [BitVec.toInt_eq_toNat_cond]
  split
  · rfl
  · change ((x.toNat : Int) - (2 ^ (8 * n) : Int)) % (2 ^ (8 * n) : Int) =
      (x.toNat : Int) % (2 ^ (8 * n) : Int)
    exact Int.sub_emod_right _ _

theorem toBytes_append_nat :
    ∀ (n1 n2 : Nat) (x : Nat),
      Int.toBytes (n1 + n2) (x : Int) =
        Int.toBytes n1 (x : Int) ++ Int.toBytes n2 ((x / 2 ^ (8 * n1) : Nat) : Int)
  | 0, n2, x => by simp [Int.toBytes.eq_1]
  | n1 + 1, n2, x => by
    rw [show n1 + 1 + n2 = (n1 + n2) + 1 by omega, Int.toBytes.eq_2, Int.toBytes.eq_2,
      List.cons_append]
    congr 1
    have hdiv : (x : Int) / 256 = ((x / 256 : Nat) : Int) := rfl
    have hpow : 2 ^ (8 * (n1 + 1)) = 256 * 2 ^ (8 * n1) := by
      rw [show 8 * (n1 + 1) = 8 + 8 * n1 by omega, Nat.pow_add]
    have hq : x / 256 / 2 ^ (8 * n1) = x / 2 ^ (8 * (n1 + 1)) := by
      rw [hpow, ← Nat.div_div_eq_div_mul]
    rw [hdiv, toBytes_append_nat n1 n2 (x / 256), hq]

theorem nat_or_mul_two_pow32 (lo hi : Nat) (hlo : lo < 4294967296) :
    (lo + hi * 4294967296) % 4294967296 = lo ∧
      (lo + hi * 4294967296) / 4294967296 = hi := by
  omega

@[expose] def pack64 (lo hi : BitVec 32) : BitVec 64 :=
  BitVec.setWidth 64 lo ||| (BitVec.setWidth 64 hi <<< (32 : Nat))

@[expose] def repr64Get (xs : List (BitVec 64)) (idx : Nat) : BitVec 32 :=
  let w := xs.getD (idx / 2) 0
  if idx % 2 = 0 then BitVec.truncate 32 w else BitVec.truncate 32 (w >>> 32)

@[expose] def repr64Set (xs : List (BitVec 64)) (idx : Nat) (val : BitVec 32) :
    List (BitVec 64) :=
  let w := xs.getD (idx / 2) 0
  let w' :=
    if idx % 2 = 0 then
      pack64 val (BitVec.truncate 32 (w >>> 32))
    else
      pack64 (BitVec.truncate 32 w) val
  xs.set (idx / 2) w'

theorem repr64Set_length (xs : List (BitVec 64)) (idx : Nat) (val : BitVec 32) :
    (repr64Set xs idx val).length = xs.length := by
  simp [repr64Set, List.length_set]

private theorem pack64_toNat (lo hi : BitVec 32) :
    (pack64 lo hi).toNat = lo.toNat + hi.toNat * 4294967296 := by
  unfold pack64
  apply Nat.eq_of_testBit_eq
  rw [BitVec.toNat_or, bv_toNat_shl_nat, bv_zext32_64, bv_zext32_64]
  have hlo : lo.toNat < 4294967296 := lo.isLt
  have hhi : hi.toNat < 4294967296 := hi.isLt
  have hp32 : (2 : Nat) ^ 32 = 4294967296 := rfl
  have hp64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  rw [hp32, hp64, Nat.mod_eq_of_lt (by omega)]
  intro j
  rw [Nat.testBit_or]
  have hadd := Nat.testBit_two_pow_mul_add hi.toNat (b := lo.toNat) (i := 32) (by omega) j
  rw [hp32, Nat.mul_comm 4294967296 hi.toNat] at hadd
  rw [Nat.add_comm lo.toNat (hi.toNat * 4294967296), hadd]
  have hshift := Nat.testBit_two_pow_mul_add hi.toNat (b := 0) (i := 32) (by omega) j
  rw [hp32, Nat.add_zero, Nat.mul_comm 4294967296 hi.toNat] at hshift
  by_cases hj : j < 32
  · have hhi0 : (hi.toNat * 4294967296).testBit j = false := by
      rw [hshift]; simp [hj, Nat.zero_testBit]
    simp [hj, hhi0]
  · have hpow : 4294967296 ≤ 2 ^ j := by
      rw [← hp32]
      exact Nat.pow_le_pow_right (by omega) (by omega)
    have hlo0 : lo.toNat.testBit j = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlo hpow)
    have hhi1 : (hi.toNat * 4294967296).testBit j = hi.toNat.testBit (j - 32) := by
      rw [hshift]; simp [hj]
    simp [hj, hlo0, hhi1]

theorem pack64_lo (lo hi : BitVec 32) : BitVec.truncate 32 (pack64 lo hi) = lo := by
  apply BitVec.eq_of_toNat_eq
  rw [bv_toNat_truncate, pack64_toNat]
  have := lo.isLt
  change (lo.toNat + hi.toNat * 4294967296) % 4294967296 = lo.toNat
  omega

theorem pack64_hi (lo hi : BitVec 32) : BitVec.truncate 32 (pack64 lo hi >>> 32) = hi := by
  apply BitVec.eq_of_toNat_eq
  rw [bv_toNat_truncate, bv_toNat_ushiftRight_nat, pack64_toNat]
  have := lo.isLt
  have := hi.isLt
  change (lo.toNat + hi.toNat * 4294967296) / 4294967296 % 4294967296 = hi.toNat
  omega

theorem repr64Get_set_same (xs : List (BitVec 64)) {idx : Nat} (hi : idx / 2 < xs.length)
    (val : BitVec 32) :
    repr64Get (repr64Set xs idx val) idx = val := by
  unfold repr64Get repr64Set
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set_self hi]
  by_cases hp : idx % 2 = 0
  · simp [hp, pack64_lo]
  · simp [hp, pack64_hi]

theorem repr64Get_set_ne (xs : List (BitVec 64)) {i j : Nat}
    (hij : i ≠ j) (hi : i / 2 < xs.length) (val : BitVec 32) :
    repr64Get (repr64Set xs i val) j = repr64Get xs j := by
  unfold repr64Get repr64Set
  simp only [List.getD_eq_getElem?_getD]
  by_cases hdiv : j / 2 = i / 2
  · have hm : i % 2 ≠ j % 2 := by omega
    rw [hdiv, List.getElem?_set_self hi]
    by_cases hp : i % 2 = 0
    · have hjp : j % 2 ≠ 0 := by omega
      simp [hp, hjp, pack64_hi]
    · have hjp : j % 2 = 0 := by omega
      simp [hp, hjp, pack64_lo]
  · rw [List.getElem?_set_ne (Ne.symm hdiv)]

theorem toBytes8_eq_append (lo hi : BitVec 32) :
    Int.toBytes 8 (pack64 lo hi).toInt = Int.toBytes 4 lo.toInt ++ Int.toBytes 4 hi.toInt := by
  have h64 := toBytes_bv_toInt_eq_toNat (n := 8) (pack64 lo hi)
  have hlo32 := toBytes_bv_toInt_eq_toNat (n := 4) lo
  have hhi32 := toBytes_bv_toInt_eq_toNat (n := 4) hi
  have happ := toBytes_append_nat 4 4 (pack64 lo hi).toNat
  change Int.toBytes 8 ↑(pack64 lo hi).toNat = _ at happ
  rw [h64, hlo32, hhi32, happ, pack64_toNat]
  have hlo := lo.isLt
  have hdiv : (lo.toNat + hi.toNat * 4294967296) / 2 ^ (8 * 4) = hi.toNat := by
    change (lo.toNat + hi.toNat * 4294967296) / 4294967296 = hi.toNat
    omega
  rw [hdiv]
  congr 1
  apply int_toBytes_mod_eq 4
  have hpow : (2 ^ (8 * 4) : Int) = 4294967296 := rfl
  rw [hpow]
  omega

theorem cell64_eq_cell32_sep (a : BitVec 64) (lo hi : BitVec 32) :
    cell64 a (pack64 lo hi) = (cell (t := i32) a lo ⋆ cell (t := i32) (a + 4) hi) := by
  have hlen : (Int.toBytes 4 lo.toInt).length = 4 := int_toBytes_length 4 lo.toInt
  have hfit : (Int.toBytes 4 lo.toInt).length + (Int.toBytes 4 hi.toInt).length ≤ 2 ^ 64 := by
    rw [int_toBytes_length, int_toBytes_length]; omega
  rw [cell64_eq_At, toBytes8_eq_append lo hi, eq_append_At a _ _ hfit, hlen]
  have hc1 : cell (t := i32) a lo = Eq ((Int.toBytes 4 lo.toInt).At a) := by
    have h := cell_eq_At (t := i32) a lo (by decide)
    change cell (t := i32) a lo = Eq ((Int.toBytes 4 (BitVec.setWidth 32 lo).toInt).At a) at h
    rwa [BitVec.setWidth_eq] at h
  have hc2 : cell (t := i32) (a + 4) hi = Eq ((Int.toBytes 4 hi.toInt).At (a + 4)) := by
    have h := cell_eq_At (t := i32) (a + 4) hi (by decide)
    change cell (t := i32) (a + 4) hi = Eq ((Int.toBytes 4 (BitVec.setWidth 32 hi).toInt).At _) at h
    rwa [BitVec.setWidth_eq] at h
  rw [hc1, hc2]
  rfl

theorem cell32_sep_eq_cell64 (a : BitVec 64) (lo hi : BitVec 32) :
    (cell (t := i32) a lo ⋆ cell (t := i32) (a + 4) hi) = cell64 a (pack64 lo hi) :=
  (cell64_eq_cell32_sep a lo hi).symm

theorem array32_focus_pair (a : BitVec 64) (pfx : List (BitVec 32))
    (lo hi : BitVec 32) (sfx : List (BitVec 32)) :
    array (t := i32) a (pfx ++ [lo, hi] ++ sfx) =
      (array (t := i32) a pfx ⋆
        cell64 (a + BitVec.ofNat 64 (4 * pfx.length)) (pack64 lo hi) ⋆
        array (t := i32) (a + BitVec.ofNat 64 (4 * (pfx.length + 2))) sfx) := by
  rw [array_split3 (t := i32) a pfx [lo, hi] sfx]
  have hmid : array (t := i32) (a + BitVec.ofNat 64 (4 * pfx.length)) [lo, hi] =
      cell64 (a + BitVec.ofNat 64 (4 * pfx.length)) (pack64 lo hi) := by
    rw [array_cons, array_cons, array_nil, sep_emp]
    have h4 : BitVec.ofNat 64 (i32.bytes) = 4 := rfl
    rw [h4, cell32_sep_eq_cell64]
  have hi32 : (i32 : Ty).bytes = 4 := rfl
  have hlen : (pfx ++ [lo, hi]).length = pfx.length + 2 := by simp
  rw [hi32, hmid, hlen]

theorem array32_set_pair {m : Mem 64} (a : BitVec 64) (pfx : List (BitVec 32))
    (_lo0 _hi0 lo1 hi1 : BitVec 32) (sfx : List (BitVec 32)) {R : Mem 64 → Prop}
    (h : (array (t := i32) a pfx ⋆
      cell64 (a + BitVec.ofNat 64 (4 * pfx.length)) (pack64 lo1 hi1) ⋆
      array (t := i32) (a + BitVec.ofNat 64 (4 * (pfx.length + 2))) sfx ⋆ R) m) :
    (array (t := i32) a (pfx ++ [lo1, hi1] ++ sfx) ⋆ R) m := by
  rw [array32_focus_pair a pfx lo1 hi1 sfx]
  exact h

/-! ## `@[c0_load]` and `@[c0_store]` wrappers for `word8Array`, `byte1Array`, `int4Array` -/

@[c0_load] theorem c0_load_word8_c0 {R : Mem 64 → Prop} {m : Mem 64} {a v : BitVec 64}
    (h : (word8 a v ⋆ R) m) :
    loadVal m i64 a = some v :=
  load_word8 h

@[c0_store] theorem c0_store_word8_c0 {R : Mem 64 → Prop} {m : Mem 64} {a v0 : BitVec 64}
    (v : BitVec 64) (h : (word8 a v0 ⋆ R) m) :
    storeOk m i64 a ∧ (word8 a v ⋆ R) (storeMem m i64 a v) :=
  store_word8 v h

@[c0_load] theorem c0_load_byte1_c0 {R : Mem 64 → Prop} {m : Mem 64} {a v : BitVec 64}
    (h : (byte1 a v ⋆ R) m) :
    loadVal m i8 a = some (BitVec.setWidth 8 v) :=
  load_byte1 h

@[c0_store] theorem c0_store_byte1_c0 {R : Mem 64 → Prop} {m : Mem 64} {a v0 : BitVec 64}
    (v : BitVec 8) (h : (byte1 a v0 ⋆ R) m) :
    storeOk m i8 a ∧ (byte1 a (BitVec.setWidth 64 v) ⋆ R) (storeMem m i8 a v) :=
  store_byte1 v h

@[c0_load] theorem c0_load_int4_c0 {R : Mem 64 → Prop} {m : Mem 64} {a v : BitVec 64}
    (h : (int4 a v ⋆ R) m) :
    loadVal m i32 a = some (BitVec.setWidth 32 v) :=
  load_int4 h

@[c0_store] theorem c0_store_int4_c0 {R : Mem 64 → Prop} {m : Mem 64} {a v0 : BitVec 64}
    (v : BitVec 32) (h : (int4 a v0 ⋆ R) m) :
    storeOk m i32 a ∧ (int4 a (BitVec.setWidth 64 v) ⋆ R) (storeMem m i32 a v) :=
  store_int4 v h

@[c0_load] theorem c0_load_word8Array_idx {R : Mem 64 → Prop} {m : Mem 64} {a : BitVec 64}
    {xs : List (BitVec 64)} {i : Nat}
    (h : (word8Array a xs ⋆ R) m) (hi : i < xs.length) :
    loadVal m i64 (a + BitVec.ofNat 64 (8 * i)) = some xs[i] :=
  load_word8Array hi h

@[c0_load] theorem c0_load_word8Array_zero {R : Mem 64 → Prop} {m : Mem 64} {a : BitVec 64}
    {xs : List (BitVec 64)}
    (h : (word8Array a xs ⋆ R) m) (hi : 0 < xs.length) :
    loadVal m i64 a = some xs[0] := by
  simpa using load_word8Array hi h

@[c0_load] theorem c0_load_word8Array_mul8 {R : Mem 64 → Prop} {m : Mem 64} {a idx : BitVec 64}
    {xs : List (BitVec 64)}
    (h : (word8Array a xs ⋆ R) m) (hi : idx.toNat < xs.length) :
    loadVal m i64 (a + idx * 8) = some xs[idx.toNat] := by
  rw [bv64_add_mul8_eq]
  exact load_word8Array hi h

@[c0_load] theorem c0_load_word8Array_shl3 {R : Mem 64 → Prop} {m : Mem 64} {a idx : BitVec 64}
    {xs : List (BitVec 64)}
    (h : (word8Array a xs ⋆ R) m) (hi : idx.toNat < xs.length) :
    loadVal m i64 (a + (idx <<< (3 : BitVec 64))) = some xs[idx.toNat] := by
  rw [bv64_add_shl3_eq]
  exact load_word8Array hi h

@[c0_store] theorem c0_store_word8Array_idx {R : Mem 64 → Prop} {m : Mem 64} {a : BitVec 64}
    {xs : List (BitVec 64)} {i : Nat} (v : BitVec 64)
    (h : (word8Array a xs ⋆ R) m) (hi : i < xs.length) :
    storeOk m i64 (a + BitVec.ofNat 64 (8 * i)) ∧
      (word8Array a (xs.set i v) ⋆ R) (storeMem m i64 (a + BitVec.ofNat 64 (8 * i)) v) :=
  store_word8Array v hi h

@[c0_store] theorem c0_store_word8Array_zero {R : Mem 64 → Prop} {m : Mem 64} {a : BitVec 64}
    {xs : List (BitVec 64)} (v : BitVec 64)
    (h : (word8Array a xs ⋆ R) m) (hi : 0 < xs.length) :
    storeOk m i64 a ∧
      (word8Array a (xs.set 0 v) ⋆ R) (storeMem m i64 a v) := by
  simpa using store_word8Array v hi h

@[c0_store] theorem c0_store_word8Array_mul8 {R : Mem 64 → Prop} {m : Mem 64} {a idx : BitVec 64}
    {xs : List (BitVec 64)} (v : BitVec 64)
    (h : (word8Array a xs ⋆ R) m) (hi : idx.toNat < xs.length) :
    storeOk m i64 (a + idx * 8) ∧
      (word8Array a (xs.set idx.toNat v) ⋆ R) (storeMem m i64 (a + idx * 8) v) := by
  rw [bv64_add_mul8_eq]
  exact store_word8Array v hi h

@[c0_store] theorem c0_store_word8Array_shl3 {R : Mem 64 → Prop} {m : Mem 64} {a idx : BitVec 64}
    {xs : List (BitVec 64)} (v : BitVec 64)
    (h : (word8Array a xs ⋆ R) m) (hi : idx.toNat < xs.length) :
    storeOk m i64 (a + (idx <<< (3 : BitVec 64))) ∧
      (word8Array a (xs.set idx.toNat v) ⋆ R)
        (storeMem m i64 (a + (idx <<< (3 : BitVec 64))) v) := by
  rw [bv64_add_shl3_eq]
  exact store_word8Array v hi h

@[c0_load] theorem c0_load_byte1Array_idx {R : Mem 64 → Prop} {m : Mem 64} {a : BitVec 64}
    {xs : List (BitVec 64)} {i : Nat}
    (h : (byte1Array a xs ⋆ R) m) (hi : i < xs.length) :
    loadVal m i8 (a + BitVec.ofNat 64 i) = some (BitVec.setWidth 8 xs[i]) :=
  load_byte1Array hi h

@[c0_load] theorem c0_load_byte1Array_zero {R : Mem 64 → Prop} {m : Mem 64} {a : BitVec 64}
    {xs : List (BitVec 64)}
    (h : (byte1Array a xs ⋆ R) m) (hi : 0 < xs.length) :
    loadVal m i8 a = some (BitVec.setWidth 8 xs[0]) := by
  simpa using load_byte1Array hi h

@[c0_load] theorem c0_load_byte1Array_bv64 {R : Mem 64 → Prop} {m : Mem 64} {a idx : BitVec 64}
    {xs : List (BitVec 64)}
    (h : (byte1Array a xs ⋆ R) m) (hi : idx.toNat < xs.length) :
    loadVal m i8 (a + idx) = some (BitVec.setWidth 8 xs[idx.toNat]) := by
  have heq : idx = BitVec.ofNat 64 idx.toNat := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [show a + idx = a + BitVec.ofNat 64 idx.toNat from congrArg (a + ·) heq]
  exact load_byte1Array hi h

@[c0_store] theorem c0_store_byte1Array_idx {R : Mem 64 → Prop} {m : Mem 64} {a : BitVec 64}
    {xs : List (BitVec 64)} {i : Nat} (v : BitVec 8)
    (h : (byte1Array a xs ⋆ R) m) (hi : i < xs.length) :
    storeOk m i8 (a + BitVec.ofNat 64 i) ∧
      (byte1Array a (xs.set i (BitVec.setWidth 64 v)) ⋆ R)
        (storeMem m i8 (a + BitVec.ofNat 64 i) v) :=
  store_byte1Array v hi h

@[c0_store] theorem c0_store_byte1Array_zero {R : Mem 64 → Prop} {m : Mem 64} {a : BitVec 64}
    {xs : List (BitVec 64)} (v : BitVec 8)
    (h : (byte1Array a xs ⋆ R) m) (hi : 0 < xs.length) :
    storeOk m i8 a ∧
      (byte1Array a (xs.set 0 (BitVec.setWidth 64 v)) ⋆ R) (storeMem m i8 a v) := by
  simpa using store_byte1Array v hi h

@[c0_store] theorem c0_store_byte1Array_bv64 {R : Mem 64 → Prop} {m : Mem 64} {a idx : BitVec 64}
    {xs : List (BitVec 64)} (v : BitVec 8)
    (h : (byte1Array a xs ⋆ R) m) (hi : idx.toNat < xs.length) :
    storeOk m i8 (a + idx) ∧
      (byte1Array a (xs.set idx.toNat (BitVec.setWidth 64 v)) ⋆ R)
        (storeMem m i8 (a + idx) v) := by
  have heq : idx = BitVec.ofNat 64 idx.toNat := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [show a + idx = a + BitVec.ofNat 64 idx.toNat from congrArg (a + ·) heq]
  exact store_byte1Array v hi h

theorem store_byte1Array64_bv64 {R : Mem 64 → Prop} {m : Mem 64} {a idx : BitVec 64}
    {xs : List (BitVec 64)} (v : BitVec 64)
    (hi : idx.toNat < xs.length) (h : (byte1Array a xs ⋆ R) m) :
    storeOk m i8 (a + idx) ∧
      (byte1Array a (xs.set idx.toNat v) ⋆ R)
        (storeMem m i8 (a + idx) (BitVec.setWidth 8 v)) := by
  have heq : idx = BitVec.ofNat 64 idx.toNat := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [show a + idx = a + BitVec.ofNat 64 idx.toNat from congrArg (a + ·) heq]
  exact store_byte1Array64 v hi h

@[c0_load] theorem c0_load_int4Array_idx {R : Mem 64 → Prop} {m : Mem 64} {a : BitVec 64}
    {xs : List (BitVec 64)} {i : Nat}
    (h : (int4Array a xs ⋆ R) m) (hi : i < xs.length) :
    loadVal m i32 (a + BitVec.ofNat 64 (4 * i)) = some (BitVec.setWidth 32 xs[i]) :=
  load_int4Array hi h

@[c0_load] theorem c0_load_int4Array_zero {R : Mem 64 → Prop} {m : Mem 64} {a : BitVec 64}
    {xs : List (BitVec 64)}
    (h : (int4Array a xs ⋆ R) m) (hi : 0 < xs.length) :
    loadVal m i32 a = some (BitVec.setWidth 32 xs[0]) := by
  simpa using load_int4Array hi h

@[c0_load] theorem c0_load_int4Array_mul4 {R : Mem 64 → Prop} {m : Mem 64} {a idx : BitVec 64}
    {xs : List (BitVec 64)}
    (h : (int4Array a xs ⋆ R) m) (hi : idx.toNat < xs.length) :
    loadVal m i32 (a + idx * 4) = some (BitVec.setWidth 32 xs[idx.toNat]) := by
  rw [bv64_mul4_eq]
  exact load_int4Array hi h

@[c0_load] theorem c0_load_int4Array_shl2 {R : Mem 64 → Prop} {m : Mem 64} {a idx : BitVec 64}
    {xs : List (BitVec 64)}
    (h : (int4Array a xs ⋆ R) m) (hi : idx.toNat < xs.length) :
    loadVal m i32 (a + (idx <<< (2 : BitVec 64))) = some (BitVec.setWidth 32 xs[idx.toNat]) := by
  have heq : idx <<< (2 : BitVec 64) = BitVec.ofNat 64 (4 * idx.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [bv_toNat_shl_bv, bv64_two_toNat, BitVec.toNat_ofNat]
    change (idx.toNat * 4) % 2 ^ 64 = (4 * idx.toNat) % 2 ^ 64
    rw [Nat.mul_comm]
  rw [heq]
  exact load_int4Array hi h

@[c0_store] theorem c0_store_int4Array_idx {R : Mem 64 → Prop} {m : Mem 64} {a : BitVec 64}
    {xs : List (BitVec 64)} {i : Nat} (v : BitVec 32)
    (h : (int4Array a xs ⋆ R) m) (hi : i < xs.length) :
    storeOk m i32 (a + BitVec.ofNat 64 (4 * i)) ∧
      (int4Array a (xs.set i (BitVec.setWidth 64 v)) ⋆ R)
        (storeMem m i32 (a + BitVec.ofNat 64 (4 * i)) v) :=
  store_int4Array v hi h

@[c0_store] theorem c0_store_int4Array_zero {R : Mem 64 → Prop} {m : Mem 64} {a : BitVec 64}
    {xs : List (BitVec 64)} (v : BitVec 32)
    (h : (int4Array a xs ⋆ R) m) (hi : 0 < xs.length) :
    storeOk m i32 a ∧
      (int4Array a (xs.set 0 (BitVec.setWidth 64 v)) ⋆ R) (storeMem m i32 a v) := by
  simpa using store_int4Array v hi h

@[c0_store] theorem c0_store_int4Array_mul4 {R : Mem 64 → Prop} {m : Mem 64} {a idx : BitVec 64}
    {xs : List (BitVec 64)} (v : BitVec 32)
    (h : (int4Array a xs ⋆ R) m) (hi : idx.toNat < xs.length) :
    storeOk m i32 (a + idx * 4) ∧
      (int4Array a (xs.set idx.toNat (BitVec.setWidth 64 v)) ⋆ R)
        (storeMem m i32 (a + idx * 4) v) := by
  rw [bv64_mul4_eq]
  exact store_int4Array v hi h

@[c0_store] theorem c0_store_int4Array_shl2 {R : Mem 64 → Prop} {m : Mem 64} {a idx : BitVec 64}
    {xs : List (BitVec 64)} (v : BitVec 32)
    (h : (int4Array a xs ⋆ R) m) (hi : idx.toNat < xs.length) :
    storeOk m i32 (a + (idx <<< (2 : BitVec 64))) ∧
      (int4Array a (xs.set idx.toNat (BitVec.setWidth 64 v)) ⋆ R)
        (storeMem m i32 (a + (idx <<< (2 : BitVec 64))) v) := by
  have heq : idx <<< (2 : BitVec 64) = BitVec.ofNat 64 (4 * idx.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [bv_toNat_shl_bv, bv64_two_toNat, BitVec.toNat_ofNat]
    change (idx.toNat * 4) % 2 ^ 64 = (4 * idx.toNat) % 2 ^ 64
    rw [Nat.mul_comm]
  rw [heq]
  exact store_int4Array v hi h

/-! ## Tagged `boxNat_*` helpers (no clash with `LeanLCNF.boxNat`) -/

namespace MemAlgebra

abbrev boxNat (n : Nat) : BitVec 64 :=
  BitVec.ofNat 64 (2 * n + 1)

end MemAlgebra

theorem boxNat_toNat (n : Nat) (h : 2 * n + 1 < 18446744073709551616) :
    (BitVec.ofNat 64 (2 * n + 1)).toNat = 2 * n + 1 :=
  bv64_ofNat_toNat_lt _ h

theorem boxNat_and_one (n : Nat) :
    (BitVec.ofNat 64 (2 * n + 1) &&& 1 : BitVec 64) = 1 := by
  apply BitVec.eq_of_toNat_eq
  rw [bv64_toNat_and_one, bv64_one_toNat, BitVec.toNat_ofNat]
  change (2 * n + 1) % 18446744073709551616 % 2 = 1
  omega

theorem boxNat_ushr1 (n : Nat) (h : 2 * n + 1 < 18446744073709551616) :
    (BitVec.ofNat 64 (2 * n + 1) >>> (1 : BitVec 64)) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [bv64_lshr1_bv, bv64_ofNat_toNat_lt _ h, bv64_ofNat_toNat_lt _ (by omega)]
  omega

theorem boxNat_add_fast (a b : Nat) (h : 2 * (a + b) + 1 < 18446744073709551616) :
    BitVec.ofNat 64 (2 * a + 1) + BitVec.ofNat 64 (2 * b + 1) - 1 =
      BitVec.ofNat 64 (2 * (a + b) + 1) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (1 : BitVec 64).toNat = 1 := rfl
  rw [BitVec.toNat_sub, BitVec.toNat_add, bv64_ofNat_toNat_lt (2 * a + 1) (by omega),
    bv64_ofNat_toNat_lt (2 * b + 1) (by omega), bv64_ofNat_toNat_lt (2 * (a + b) + 1) h, h1]
  change (2 ^ 64 - 1 + (2 * a + 1 + (2 * b + 1)) % 2 ^ 64) % 2 ^ 64 = 2 * (a + b) + 1
  have hp64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  rw [hp64]
  omega

theorem boxNat_sub_step (n : Nat) (hn : 0 < n) (h : 2 * n + 1 < 18446744073709551616) :
    BitVec.ofNat 64 (2 * n + 1) - 2 = BitVec.ofNat 64 (2 * (n - 1) + 1) := by
  apply BitVec.eq_of_toNat_eq
  have h2 : (2 : BitVec 64).toNat = 2 := rfl
  rw [bv64_sub_toNat (by rw [bv64_ofNat_toNat_lt _ h, h2]; omega),
    bv64_ofNat_toNat_lt _ h, bv64_ofNat_toNat_lt _ (by omega), h2]
  omega

theorem boxNat_umul_eq (a b : Nat) (ha : 2 * a + 1 < 18446744073709551616)
    (hb : 2 * b + 1 < 18446744073709551616) (hmul : 2 * (a * b) + 1 < 18446744073709551616) :
    (((BitVec.ofNat 64 (2 * a + 1) >>> (1 : BitVec 64)) *
      (BitVec.ofNat 64 (2 * b + 1) >>> (1 : BitVec 64))) <<< (1 : BitVec 64)) ||| 1 =
      BitVec.ofNat 64 (2 * (a * b) + 1) := by
  rw [boxNat_ushr1 a ha, boxNat_ushr1 b hb]
  have hprod : (BitVec.ofNat 64 a * BitVec.ofNat 64 b).toNat = a * b := by
    rw [BitVec.toNat_mul, bv64_ofNat_toNat_lt _ (by omega), bv64_ofNat_toNat_lt _ (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  rw [bv64_lit2p1, hprod]

theorem boxNat_umul_ov_iff (a b : Nat) (ha : 2 * a + 1 < 18446744073709551616)
    (hb : 2 * b + 1 < 18446744073709551616) (hpos : 0 < a) :
    (BitVec.ult (BitVec.ofNat 64 4611686018427387903 / BitVec.ofNat 64 a) (BitVec.ofNat 64 b)) =
      decide (4611686018427387903 < a * b) := by
  rw [bv64_ult_eq, BitVec.toNat_udiv, bv64_ofNat_toNat_lt _ (by omega),
    bv64_ofNat_toNat_lt _ (by omega), bv64_ofNat_toNat_lt _ (by omega)]
  have hiff : 4611686018427387903 / a < b ↔ 4611686018427387903 < a * b := by
    rw [← Nat.not_le (a := b) (b := 4611686018427387903 / a),
      ← Nat.not_le (a := a * b) (b := 4611686018427387903), Nat.mul_comm a b]
    exact not_congr (Nat.le_div_iff_mul_le hpos)
  by_cases h : 4611686018427387903 / a < b
  · rw [decide_eq_true h, decide_eq_true (hiff.mp h)]
  · rw [decide_eq_false h, decide_eq_false (mt hiff.mpr h)]

/-! ## Generic `List` / `Perm` / `Nodup` helpers -/

theorem nodup_map_of_inj {α β : Type _} {f : α → β} {l : List α}
    (hinj : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) (hnd : l.Nodup) :
    (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd ⊢
    refine ⟨?_, ih (fun x hx y hy hxy => hinj x (by simp [hx]) y (by simp [hy]) hxy) hnd.2⟩
    intro hmem
    rcases List.mem_map.mp hmem with ⟨b, hb, hfab⟩
    have heq := hinj b (by simp [hb]) a (by simp) hfab
    subst heq
    exact hnd.1 hb

theorem nodup_lt_length_le :
    ∀ {l : List Nat} {n : Nat}, l.Nodup → (∀ x ∈ l, x < n) → l.length ≤ n
  | [], _, _, _ => Nat.zero_le _
  | a :: t, 0, _, hb => absurd (hb a (by simp)) (Nat.not_lt_zero _)
  | a :: t, n + 1, hnd, hb => by
    rw [List.nodup_cons] at hnd
    let f : Nat → Nat := fun y => if y < a then y else y - 1
    have hft : ∀ x ∈ t, x ≠ a := fun x hx heq => hnd.1 (heq ▸ hx)
    have hf_nd : (t.map f).Nodup := by
      apply nodup_map_of_inj _ hnd.2
      intro x hx y hy hxy
      have hxa := hft x hx
      have hya := hft y hy
      dsimp only [f] at hxy
      split at hxy <;> split at hxy <;> omega
    have hf_lt : ∀ z ∈ t.map f, z < n := by
      intro z hz
      rcases List.mem_map.mp hz with ⟨y, hy, rfl⟩
      have hyb := hb y (by simp [hy])
      have hya := hft y hy
      have ha := hb a (by simp)
      dsimp only [f]
      split <;> omega
    have ih := nodup_lt_length_le hf_nd hf_lt
    simp only [List.length_map] at ih
    simp only [List.length_cons]
    omega

theorem nodup_lt_of_missing {l : List Nat} {n k : Nat}
    (hk : k < n) (hmissing : k ∉ l) (hnd : l.Nodup) (hb : ∀ x ∈ l, x < n) :
    l.length ≤ n - 1 := by
  have h1 : (k :: l).Nodup := List.nodup_cons.mpr ⟨hmissing, hnd⟩
  have h2 : ∀ x ∈ (k :: l), x < n := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact hk
    · exact hb x hmem
  have hle := nodup_lt_length_le h1 h2
  simp only [List.length_cons] at hle
  omega

theorem inj_lt_of_missing {n k : Nat} (f : Fin k → Nat)
    (hinj : ∀ i j : Fin k, f i = f j → i = j)
    (hb : ∀ i : Fin k, f i < n) : k ≤ n := by
  have ofFn_nodup : ∀ m (g : Fin m → Nat),
      (∀ i j : Fin m, g i = g j → i = j) → (List.ofFn g).Nodup := by
    intro m
    induction m with
    | zero => intro _ _; simp
    | succ m ih =>
      intro g hginj
      rw [List.ofFn_succ, List.nodup_cons]
      refine ⟨?_, ih (fun i => g i.succ) (fun i j heq => Fin.succ_inj.mp (hginj _ _ heq))⟩
      intro hmem
      rcases List.mem_ofFn.mp hmem with ⟨j, hj⟩
      exact Fin.succ_ne_zero j (hginj j.succ 0 hj)
  let l := List.ofFn f
  have hnd : l.Nodup := ofFn_nodup k f hinj
  have hbl : ∀ x ∈ l, x < n := by
    intro x hx
    rcases List.mem_ofFn.mp hx with ⟨i, rfl⟩
    exact hb i
  have hle := nodup_lt_length_le hnd hbl
  simpa [l] using hle

theorem count_set_eq {α : Type _} [DecidableEq α] (l : List α) {i : Nat}
    (hi : i < l.length) (v : α) :
    (l.set i v).count v = l.count v + (if l[i] = v then 0 else 1) := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a t ih =>
    cases i with
    | zero =>
      simp only [List.set_cons_zero, List.getElem_cons_zero, List.count_cons]
      by_cases ha : a = v
      · simp [ha]
      · simp [ha, beq_false_of_ne ha]
    | succ i' =>
      simp only [List.length_cons] at hi
      simp only [List.set_cons_succ, List.getElem_cons_succ, List.count_cons]
      have hrec := ih (i := i') (by omega)
      omega

private theorem perm_cons_set {α : Type _} (x : α) (xs : List α) :
    ∀ {k : Nat} (hk : k < xs.length), (xs[k] :: xs.set k x).Perm (x :: xs) := by
  induction xs with
  | nil => intro k hk; simp at hk
  | cons y ys ih =>
    intro k hk
    cases k with
    | zero => exact List.Perm.swap x y ys
    | succ k' =>
      simp only [List.length_cons] at hk
      simp only [List.getElem_cons_succ, List.set_cons_succ]
      exact (List.Perm.swap y ys[k'] (ys.set k' x)).trans
        ((List.Perm.cons y (ih (by omega))).trans (List.Perm.swap x y ys))

theorem list_swap_perm {α : Type _} (l : List α) {i j : Nat}
    (hi : i < l.length) (hj : j < l.length) :
    ((l.set i l[j]).set j l[i]).Perm l := by
  have hperm {a b : Nat} (l : List α) (hab : a < b) (ha : a < l.length) (hb : b < l.length) :
      ((l.set a l[b]).set b l[a]).Perm l := by
    induction l generalizing a b with
    | nil => simp at ha
    | cons x xs ih =>
      cases a with
      | zero =>
        cases b with
        | zero => omega
        | succ b' =>
          simp only [List.length_cons] at hb
          simp only [List.set_cons_zero, List.set_cons_succ, List.getElem_cons_zero,
            List.getElem_cons_succ]
          exact perm_cons_set x xs (by omega)
      | succ a' =>
        cases b with
        | zero => omega
        | succ b' =>
          simp only [List.length_cons] at ha hb
          simp only [List.set_cons_succ, List.getElem_cons_succ]
          exact List.Perm.cons x (ih (by omega) (by omega) (by omega))
  rcases Nat.lt_trichotomy i j with hij | rfl | hji
  · exact hperm l hij hi hj
  · rw [List.set_getElem_self, List.set_getElem_self]
  · have := hperm l hji hj hi
    have hcomm : (l.set i l[j]).set j l[i] = (l.set j l[i]).set i l[j] :=
      List.set_comm l[j] l[i] (Ne.symm (by omega))
    rwa [hcomm]

theorem replacePrefix_set {α : Type _} (pfx rest : List α) {i : Nat} (v : α)
    (hi : i < pfx.length) :
    (pfx ++ rest).set i v = pfx.set i v ++ rest :=
  List.set_append_left i v hi

theorem zeroPrefix_set {α : Type _} (z : α) (n i : Nat) (xs : List α) (hi : i < n) :
    (List.replicate n z ++ xs.drop n).set i z = List.replicate n z ++ xs.drop n := by
  have hlen : i < (List.replicate n z).length := by simpa using hi
  rw [List.set_append_left i z hlen]
  congr 1
  apply List.ext_getElem
  · simp
  · intro k hk1 hk2
    by_cases hki : k = i
    · subst hki; simp
    · simp

end LeanQbe.T
