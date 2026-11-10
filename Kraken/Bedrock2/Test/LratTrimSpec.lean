module

public import Kraken.Bedrock2.SemanticsLemmas
public import Kraken.Bedrock2.Interp
public import Kraken.Bedrock2.Test.LratTrim
public import Std.Tactic.BVDecide.LRAT.Checker
public import Std.Tactic.BVDecide.LRAT.Internal.Rup
public import Std.Tactic.BVDecide.LRAT.Internal.Add
public import Std.Tactic.BVDecide.LRAT.Internal.Empty
import Std.Tactic.BVDecide
meta import Std.Tactic.BVDecide.Reflect

@[expose] public section

open Std Std.ExtHashMap Std.Sat
open Std.Tactic.BVDecide.LRAT
open Std.Tactic.BVDecide.LRAT.Internal

namespace Kraken.Bedrock2.Test

/-! ## 1. External Specification for `_Noreturn lrat_fail` -/

/-- External specification modeling `lrat_fail` as a non-returning failure call (`exit(1)`):
it consumes no memory (`mGive = ∅`) and holds for any postcondition (including `fun _ _ => False`). -/
def lratFailExt : ExtSpec 64 :=
  fun _ mGive action _ _ => action = "lrat_fail" ∧ mGive = ∅

theorem lratFailExt_ok : ExtSpec.Ok lratFailExt where
  mGive_unique := by rintro _ _ _ _ _ _ _ _ _ _ _ _ ⟨_, rfl⟩ ⟨_, rfl⟩; rfl
  weaken := by rintro _ _ _ _ _ _ _ h; exact h
  intersect := by rintro _ _ _ _ _ _ h _; exact h

/-- One-step rule for `interact lrat_fail(...)`: since `lratFailExt` holds for `mid := fun _ _ => False`,
any `interact [] "lrat_fail" arges` whose arguments evaluate succeeds for arbitrary `post`. -/
theorem exec_lrat_fail {e : Env} {B : Nat} {arges : List Expr} {args : List (BitVec 64)}
    {t : Trace 64} {m : Mem 64} {l : Locals 64} {post : Trace 64 → Mem 64 → Locals 64 → Prop}
    (ha : evalArgs m l arges = some args) :
    Exec lratFailExt e B (.interact [] "lrat_fail" arges) t m l post := by
  refine .interact [] "lrat_fail" arges args B t m l post m ∅ (fun _ _ => False) ?_ ha ⟨rfl, rfl⟩
    (by rintro _ _ ⟨⟩)
  refine ⟨?_, ExtHashMap.eq_empty_iff_forall_not_mem.mpr fun k hk =>
    ExtHashMap.not_mem_empty (ExtHashMap.mem_inter_iff.mp hk).2⟩
  apply ExtHashMap.ext_getElem?
  intro k
  simp [ExtHashMap.union_eq, ExtHashMap.getElem?_union]

/-! ## 2. Scalar Memory Cells (`word8`, `int4`, `byte1`) & Signed BitVec Helpers -/

/-- A 64-bit word `v` stored at address `a`. -/
def word8 (a v : BitVec 64) : Mem 64 → Prop :=
  Eq ((Int.toBytes 8 v.toNat).At a)

/-- A 32-bit integer `v` (low 32 bits of `v`) stored at address `a`. -/
def int4 (a v : BitVec 64) : Mem 64 → Prop :=
  Eq ((Int.toBytes 4 v.toNat).At a)

/-- An 8-bit integer `v` (low 8 bits of `v`) stored at address `a`. -/
def byte1 (a v : BitVec 64) : Mem 64 → Prop :=
  Eq ((Int.toBytes 1 v.toNat).At a)

/-- `v` is a sign-extended 32-bit integer (`(v <<< 32).sshiftRight 32 = v`). -/
abbrev IsInt32 (v : BitVec 64) : Prop :=
  (v <<< 32).sshiftRight 32 = v

/-- `v` is a sign-extended 8-bit integer (`(v <<< 56).sshiftRight 56 = v`). -/
abbrev IsInt8 (v : BitVec 64) : Prop :=
  (v <<< 56).sshiftRight 56 = v

@[simp] theorem isInt32_zero : IsInt32 0 := by decide
@[simp] theorem isInt32_one : IsInt32 1 := by decide
@[simp] theorem isInt32_neg_one : IsInt32 (-1) := by decide

@[simp] theorem isInt8_zero : IsInt8 0 := by decide
@[simp] theorem isInt8_one : IsInt8 1 := by decide
@[simp] theorem isInt8_neg_one : IsInt8 (-1) := by decide

theorem load_word8 {m : Mem 64} {a v : BitVec 64} {R : Mem 64 → Prop}
    (hsep : m =⋆ word8 a v ⋆ R) :
    load? .eight m a = some v := by
  have h := load?_sep (sz := .eight) hsep (Int.toBytes_length 8 v.toNat) (by decide)
  simpa [show ((v.toNat : Int).take (8 * 8)) = v.toNat from
    Int.emod_eq_of_lt (Int.natCast_nonneg _) (by have := v.isLt; omega)] using h

theorem store_word8 {e : Env} {B : Nat} {ea ev : Expr} {t : Trace 64} {m : Mem 64} {l : Locals 64}
    {post : Trace 64 → Mem 64 → Locals 64 → Prop} {a v0 v : BitVec 64} {R : Mem 64 → Prop}
    (ha : ea.eval m l = some a) (hv : ev.eval m l = some v)
    (hsep : m =⋆ word8 a v0 ⋆ R)
    (hpost : ∀ m', (m' =⋆ word8 a v ⋆ R) → post t m' l) :
    Exec lratFailExt e B (.store .eight ea ev) t m l post :=
  Exec.store_sep (sz := .eight) ha hv hsep (Int.toBytes_length 8 v0.toNat) (by decide) hpost

theorem load_int4_raw {m : Mem 64} {a v : BitVec 64} {R : Mem 64 → Prop}
    (hsep : m =⋆ int4 a v ⋆ R) :
    load? .four m a = some (v &&& 0xffffffff#64) := by
  have h := load?_sep (sz := .four) hsep (Int.toBytes_length 4 v.toNat) (by decide)
  have := Nat.and_two_pow_sub_one_eq_mod v.toNat 32
  simpa [show BitVec.ofInt 64 ((v.toNat : Int).take (8 * 4)) = v &&& 0xffffffff#64 from
    BitVec.eq_of_toNat_eq (by simp [Int.take]; grind)] using h

private theorem sext32_mask (v : BitVec 64) :
    interpBinop .srs (interpBinop .slu (v &&& 0xffffffff#64) 32#64) 32#64 =
      (v <<< 32).sshiftRight 32 := by
  simp [interpBinop, shamt]; grind

/-- Evaluating `(load4(ea) << 32) .>> 32` on `m =⋆ int4 a v ⋆ R` when `IsInt32 v`. -/
theorem eval_load4_sext {m : Mem 64} {l : Locals 64} {ea : Expr} {a v : BitVec 64}
    {R : Mem 64 → Prop} (ha : ea.eval m l = some a) (hsep : m =⋆ int4 a v ⋆ R) (hv : IsInt32 v) :
    (Expr.op .srs (.op .slu (.load .four ea) (.literal 32)) (.literal 32)).eval m l = some v := by
  simp [Expr.eval, ha, load_int4_raw hsep, sext32_mask, hv]

theorem store_int4 {e : Env} {B : Nat} {ea ev : Expr} {t : Trace 64} {m : Mem 64} {l : Locals 64}
    {post : Trace 64 → Mem 64 → Locals 64 → Prop} {a v0 v : BitVec 64} {R : Mem 64 → Prop}
    (ha : ea.eval m l = some a) (hv : ev.eval m l = some v)
    (hsep : m =⋆ int4 a v0 ⋆ R)
    (hpost : ∀ m', (m' =⋆ int4 a v ⋆ R) → post t m' l) :
    Exec lratFailExt e B (.store .four ea ev) t m l post :=
  Exec.store_sep (sz := .four) ha hv hsep (Int.toBytes_length 4 v0.toNat) (by decide) hpost

theorem load_byte1_raw {m : Mem 64} {a v : BitVec 64} {R : Mem 64 → Prop}
    (hsep : m =⋆ byte1 a v ⋆ R) :
    load? .one m a = some (v &&& 0xff#64) := by
  have h := load?_sep (sz := .one) hsep (Int.toBytes_length 1 v.toNat) (by decide)
  have h1 : Int.toBytes 1 (v.toNat : Int) = [v.toNat.toUInt8] := toBytes_one v
  rwa [h1, ofInt_ofBytes_byte (by decide)] at h

private theorem sext8_mask (v : BitVec 64) :
    interpBinop .srs (interpBinop .slu (v &&& 0xff#64) 56#64) 56#64 =
      (v <<< 56).sshiftRight 56 := by
  simp [interpBinop, shamt]; grind

/-- Evaluating `(load1(ea) << 56) .>> 56` on `m =⋆ byte1 a v ⋆ R` when `IsInt8 v`. -/
theorem eval_load1_sext {m : Mem 64} {l : Locals 64} {ea : Expr} {a v : BitVec 64}
    {R : Mem 64 → Prop} (ha : ea.eval m l = some a) (hsep : m =⋆ byte1 a v ⋆ R) (hv : IsInt8 v) :
    (Expr.op .srs (.op .slu (.load .one ea) (.literal 56)) (.literal 56)).eval m l = some v := by
  simp [Expr.eval, ha, load_byte1_raw hsep, sext8_mask, hv]

theorem store_byte1 {e : Env} {B : Nat} {ea ev : Expr} {t : Trace 64} {m : Mem 64} {l : Locals 64}
    {post : Trace 64 → Mem 64 → Locals 64 → Prop} {a v0 v : BitVec 64} {R : Mem 64 → Prop}
    (ha : ea.eval m l = some a) (hv : ev.eval m l = some v)
    (hsep : m =⋆ byte1 a v0 ⋆ R)
    (hpost : ∀ m', (m' =⋆ byte1 a v ⋆ R) → post t m' l) :
    Exec lratFailExt e B (.store .one ea ev) t m l post :=
  Exec.store_sep (sz := .one) ha hv hsep (Int.toBytes_length 1 v0.toNat) (by decide) hpost

/-! ## 3. Contiguous Array Predicates (`word8Array`, `int4Array`, `byte1Array`) -/

def word8Array (a : BitVec 64) : List (BitVec 64) → Mem 64 → Prop
  | [] => emp
  | v :: vs => word8 a v ⋆ word8Array (a + 8) vs

def int4Array (a : BitVec 64) : List (BitVec 64) → Mem 64 → Prop
  | [] => emp
  | v :: vs => int4 a v ⋆ int4Array (a + 4) vs

def byte1Array (a : BitVec 64) : List (BitVec 64) → Mem 64 → Prop
  | [] => emp
  | v :: vs => byte1 a v ⋆ byte1Array (a + 1) vs

@[simp] theorem word8Array_nil (a : BitVec 64) : word8Array a [] = emp := rfl
@[simp] theorem word8Array_cons (a v : BitVec 64) (vs : List (BitVec 64)) :
    word8Array a (v :: vs) = (word8 a v ⋆ word8Array (a + 8) vs) := rfl

@[simp] theorem int4Array_nil (a : BitVec 64) : int4Array a [] = emp := rfl
@[simp] theorem int4Array_cons (a v : BitVec 64) (vs : List (BitVec 64)) :
    int4Array a (v :: vs) = (int4 a v ⋆ int4Array (a + 4) vs) := rfl

@[simp] theorem byte1Array_nil (a : BitVec 64) : byte1Array a [] = emp := rfl
@[simp] theorem byte1Array_cons (a v : BitVec 64) (vs : List (BitVec 64)) :
    byte1Array a (v :: vs) = (byte1 a v ⋆ byte1Array (a + 1) vs) := rfl

theorem word8Array_append (a : BitVec 64) (xs ys : List (BitVec 64)) :
    word8Array a (xs ++ ys) =
      (word8Array a xs ⋆ word8Array (a + BitVec.ofNat 64 (8 * xs.length)) ys) := by
  induction xs generalizing a with
  | nil => simp [emp_sep]
  | cons x xs ih =>
    rw [List.cons_append, word8Array_cons, word8Array_cons, ih, ← sep_assoc, List.length_cons]
    congr 2; exact BitVec.eq_of_toNat_eq (by grind)

theorem int4Array_append (a : BitVec 64) (xs ys : List (BitVec 64)) :
    int4Array a (xs ++ ys) =
      (int4Array a xs ⋆ int4Array (a + BitVec.ofNat 64 (4 * xs.length)) ys) := by
  induction xs generalizing a with
  | nil => simp [emp_sep]
  | cons x xs ih =>
    rw [List.cons_append, int4Array_cons, int4Array_cons, ih, ← sep_assoc, List.length_cons]
    congr 2; exact BitVec.eq_of_toNat_eq (by grind)

theorem byte1Array_append (a : BitVec 64) (xs ys : List (BitVec 64)) :
    byte1Array a (xs ++ ys) =
      (byte1Array a xs ⋆ byte1Array (a + BitVec.ofNat 64 xs.length) ys) := by
  induction xs generalizing a with
  | nil => simp [emp_sep]
  | cons x xs ih =>
    rw [List.cons_append, byte1Array_cons, byte1Array_cons, ih, ← sep_assoc, List.length_cons]
    congr 2; exact BitVec.eq_of_toNat_eq (by grind)

theorem word8Array_focus (a : BitVec 64) (xs : List (BitVec 64)) {i : Nat} (hi : i < xs.length) :
    word8Array a xs =
      (word8 (a + BitVec.ofNat 64 (8 * i)) xs[i] ⋆
        (word8Array a (xs.take i) ⋆
          word8Array (a + BitVec.ofNat 64 (8 * i) + 8) (xs.drop (i + 1)))) := by
  conv => lhs; rw [← List.take_append_drop i xs, List.drop_eq_getElem_cons hi]
  rw [word8Array_append, word8Array_cons, List.length_take_of_le (Nat.le_of_lt hi),
    ← sep_assoc, sep_comm (word8Array a (xs.take i)), sep_assoc]

theorem int4Array_focus (a : BitVec 64) (xs : List (BitVec 64)) {i : Nat} (hi : i < xs.length) :
    int4Array a xs =
      (int4 (a + BitVec.ofNat 64 (4 * i)) xs[i] ⋆
        (int4Array a (xs.take i) ⋆
          int4Array (a + BitVec.ofNat 64 (4 * i) + 4) (xs.drop (i + 1)))) := by
  conv => lhs; rw [← List.take_append_drop i xs, List.drop_eq_getElem_cons hi]
  rw [int4Array_append, int4Array_cons, List.length_take_of_le (Nat.le_of_lt hi),
    ← sep_assoc, sep_comm (int4Array a (xs.take i)), sep_assoc]

theorem int4Array_set (a : BitVec 64) (xs : List (BitVec 64)) {i : Nat} (hi : i < xs.length) (v : BitVec 64) :
    int4Array a (xs.set i v) =
      (int4 (a + BitVec.ofNat 64 (4 * i)) v ⋆
        (int4Array a (xs.take i) ⋆
          int4Array (a + BitVec.ofNat 64 (4 * i) + 4) (xs.drop (i + 1)))) := by
  rw [int4Array_focus a (xs.set i v) (i := i) (by simp [hi])]
  simp [List.take_set_of_le (Nat.le_refl i), List.drop_set_of_lt (Nat.lt_succ_self i)]

theorem byte1Array_focus (a : BitVec 64) (xs : List (BitVec 64)) {i : Nat} (hi : i < xs.length) :
    byte1Array a xs =
      (byte1 (a + BitVec.ofNat 64 i) xs[i] ⋆
        (byte1Array a (xs.take i) ⋆
          byte1Array (a + BitVec.ofNat 64 i + 1) (xs.drop (i + 1)))) := by
  conv => lhs; rw [← List.take_append_drop i xs, List.drop_eq_getElem_cons hi]
  rw [byte1Array_append, byte1Array_cons, List.length_take_of_le (Nat.le_of_lt hi),
    ← sep_assoc, sep_comm (byte1Array a (xs.take i)), sep_assoc]

theorem byte1Array_set (a : BitVec 64) (xs : List (BitVec 64)) {i : Nat} (hi : i < xs.length) (v : BitVec 64) :
    byte1Array a (xs.set i v) =
      (byte1 (a + BitVec.ofNat 64 i) v ⋆
        (byte1Array a (xs.take i) ⋆
          byte1Array (a + BitVec.ofNat 64 i + 1) (xs.drop (i + 1)))) := by
  rw [byte1Array_focus a (xs.set i v) (i := i) (by simp [hi])]
  simp [List.take_set_of_le (Nat.le_refl i), List.drop_set_of_lt (Nat.lt_succ_self i)]

theorem word8Array_set (a : BitVec 64) (xs : List (BitVec 64)) {i : Nat} (hi : i < xs.length) (v : BitVec 64) :
    word8Array a (xs.set i v) =
      (word8 (a + BitVec.ofNat 64 (8 * i)) v ⋆
        (word8Array a (xs.take i) ⋆
          word8Array (a + BitVec.ofNat 64 (8 * i) + 8) (xs.drop (i + 1)))) := by
  rw [word8Array_focus a (xs.set i v) (i := i) (by simp [hi])]
  simp [List.take_set_of_le (Nat.le_refl i), List.drop_set_of_lt (Nat.lt_succ_self i)]

theorem load_word8Array_elem {m : Mem 64} {a : BitVec 64} {xs : List (BitVec 64)}
    {i : Nat} {R : Mem 64 → Prop} (hi : i < xs.length) (hsep : m =⋆ word8Array a xs ⋆ R) :
    load? .eight m (a + BitVec.ofNat 64 (8 * i)) = some xs[i] := by
  rw [word8Array_focus a xs hi, sep_assoc] at hsep
  exact load_word8 hsep

theorem eval_load_word8Array_elem {m : Mem 64} {l : Locals 64} {ea : Expr}
    {a : BitVec 64} {xs : List (BitVec 64)} {i : Nat} {R : Mem 64 → Prop}
    (hi : i < xs.length) (ha : ea.eval m l = some (a + BitVec.ofNat 64 (8 * i)))
    (hsep : m =⋆ word8Array a xs ⋆ R) :
    (Expr.load .eight ea).eval m l = some xs[i] := by
  simp [Expr.eval, ha, load_word8Array_elem hi hsep]

theorem store_word8Array_elem {e : Env} {B : Nat} {ea ev : Expr} {t : Trace 64} {m : Mem 64} {l : Locals 64}
    {post : Trace 64 → Mem 64 → Locals 64 → Prop} {a : BitVec 64} {xs : List (BitVec 64)}
    {i : Nat} {v : BitVec 64} {R : Mem 64 → Prop}
    (hi : i < xs.length) (ha : ea.eval m l = some (a + BitVec.ofNat 64 (8 * i)))
    (hv : ev.eval m l = some v) (hsep : m =⋆ word8Array a xs ⋆ R)
    (hpost : ∀ m', (m' =⋆ word8Array a (xs.set i v) ⋆ R) → post t m' l) :
    Exec lratFailExt e B (.store .eight ea ev) t m l post := by
  rw [word8Array_focus a xs hi, sep_assoc] at hsep
  exact store_word8 ha hv hsep fun m' hm' =>
    hpost m' (by rwa [← sep_assoc, ← word8Array_set a xs hi v] at hm')

theorem eval_load4_int4Array_elem {m : Mem 64} {l : Locals 64} {ea : Expr}
    {a : BitVec 64} {xs : List (BitVec 64)} {i : Nat} {R : Mem 64 → Prop}
    (hi : i < xs.length) (ha : ea.eval m l = some (a + BitVec.ofNat 64 (4 * i)))
    (hsep : m =⋆ int4Array a xs ⋆ R) (h32 : IsInt32 xs[i]) :
    (Expr.op .srs (.op .slu (.load .four ea) (.literal 32)) (.literal 32)).eval m l = some xs[i] := by
  rw [int4Array_focus a xs hi, sep_assoc] at hsep
  exact eval_load4_sext ha hsep h32

theorem store_int4Array_elem {e : Env} {B : Nat} {ea ev : Expr} {t : Trace 64} {m : Mem 64} {l : Locals 64}
    {post : Trace 64 → Mem 64 → Locals 64 → Prop} {a : BitVec 64} {xs : List (BitVec 64)}
    {i : Nat} {v : BitVec 64} {R : Mem 64 → Prop}
    (hi : i < xs.length) (ha : ea.eval m l = some (a + BitVec.ofNat 64 (4 * i)))
    (hv : ev.eval m l = some v) (hsep : m =⋆ int4Array a xs ⋆ R)
    (hpost : ∀ m', (m' =⋆ int4Array a (xs.set i v) ⋆ R) → post t m' l) :
    Exec lratFailExt e B (.store .four ea ev) t m l post := by
  rw [int4Array_focus a xs hi, sep_assoc] at hsep
  exact store_int4 ha hv hsep fun m' hm' =>
    hpost m' (by rwa [← sep_assoc, ← int4Array_set a xs hi v] at hm')

theorem eval_load1_byte1Array_elem {m : Mem 64} {l : Locals 64} {ea : Expr}
    {a : BitVec 64} {xs : List (BitVec 64)} {i : Nat} {R : Mem 64 → Prop}
    (hi : i < xs.length) (ha : ea.eval m l = some (a + BitVec.ofNat 64 i))
    (hsep : m =⋆ byte1Array a xs ⋆ R) (h8 : IsInt8 xs[i]) :
    (Expr.op .srs (.op .slu (.load .one ea) (.literal 56)) (.literal 56)).eval m l = some xs[i] := by
  rw [byte1Array_focus a xs hi, sep_assoc] at hsep
  exact eval_load1_sext ha hsep h8

theorem store_byte1Array_elem {e : Env} {B : Nat} {ea ev : Expr} {t : Trace 64} {m : Mem 64} {l : Locals 64}
    {post : Trace 64 → Mem 64 → Locals 64 → Prop} {a : BitVec 64} {xs : List (BitVec 64)}
    {i : Nat} {v : BitVec 64} {R : Mem 64 → Prop}
    (hi : i < xs.length) (ha : ea.eval m l = some (a + BitVec.ofNat 64 i))
    (hv : ev.eval m l = some v) (hsep : m =⋆ byte1Array a xs ⋆ R)
    (hpost : ∀ m', (m' =⋆ byte1Array a (xs.set i v) ⋆ R) → post t m' l) :
    Exec lratFailExt e B (.store .one ea ev) t m l post := by
  rw [byte1Array_focus a xs hi, sep_assoc] at hsep
  exact store_byte1 ha hv hsep fun m' hm' =>
    hpost m' (by rwa [← sep_assoc, ← byte1Array_set a xs hi v] at hm')

/-- A 0-terminated 32-bit integer array at address `p` containing `xs ++ [0]`. -/
def ZeroTermInts (p : BitVec 64) (xs : List (BitVec 64)) : Mem 64 → Prop :=
  int4Array p (xs ++ [0])

@[simp] theorem zeroTermInts_nil (p : BitVec 64) :
    ZeroTermInts p [] = int4 p 0 := by
  simp [ZeroTermInts, sep_emp]

@[simp] theorem zeroTermInts_cons (p x : BitVec 64) (xs : List (BitVec 64)) :
    ZeroTermInts p (x :: xs) = (int4 p x ⋆ ZeroTermInts (p + 4) xs) := rfl

theorem zeroTermInts_eq_append (p : BitVec 64) (xs : List (BitVec 64)) :
    ZeroTermInts p xs =
      (int4Array p xs ⋆ int4 (p + BitVec.ofNat 64 (4 * xs.length)) 0) := by
  simp [ZeroTermInts, int4Array_append, sep_emp]

theorem zeroTermInts_focus_elem (p : BitVec 64) (xs : List (BitVec 64)) {i : Nat} (hi : i < xs.length) :
    ZeroTermInts p xs =
      (int4 (p + BitVec.ofNat 64 (4 * i)) xs[i] ⋆
        (int4Array p (xs.take i) ⋆
          ZeroTermInts (p + BitVec.ofNat 64 (4 * i) + 4) (xs.drop (i + 1)))) := by
  unfold ZeroTermInts
  rw [int4Array_focus p (xs ++ [0]) (i := i) (by simp; omega)]
  rw [List.getElem_append_left hi, List.take_append_of_le_length (Nat.le_of_lt hi),
    List.drop_append_of_le_length (Nat.succ_le_of_lt hi)]

theorem zeroTermInts_focus_end (p : BitVec 64) (xs : List (BitVec 64)) :
    ZeroTermInts p xs =
      (int4 (p + BitVec.ofNat 64 (4 * xs.length)) 0 ⋆ int4Array p xs) := by
  rw [zeroTermInts_eq_append, sep_comm]

theorem eval_load4_zeroTermInts_elem {m : Mem 64} {l : Locals 64} {ea : Expr}
    {p : BitVec 64} {xs : List (BitVec 64)} {i : Nat} {R : Mem 64 → Prop}
    (hi : i < xs.length) (ha : ea.eval m l = some (p + BitVec.ofNat 64 (4 * i)))
    (hsep : m =⋆ ZeroTermInts p xs ⋆ R) (h32 : IsInt32 xs[i]) :
    (Expr.op .srs (.op .slu (.load .four ea) (.literal 32)) (.literal 32)).eval m l = some xs[i] := by
  rw [zeroTermInts_focus_elem p xs hi, sep_assoc] at hsep
  exact eval_load4_sext ha hsep h32

theorem eval_load4_zeroTermInts_end {m : Mem 64} {l : Locals 64} {ea : Expr}
    {p : BitVec 64} {xs : List (BitVec 64)} {R : Mem 64 → Prop}
    (ha : ea.eval m l = some (p + BitVec.ofNat 64 (4 * xs.length)))
    (hsep : m =⋆ ZeroTermInts p xs ⋆ R) :
    (Expr.op .srs (.op .slu (.load .four ea) (.literal 32)) (.literal 32)).eval m l = some 0 := by
  rw [zeroTermInts_focus_end p xs, sep_assoc] at hsep
  exact eval_load4_sext ha hsep isInt32_zero

/-- Map a list of positive 32-bit antecedent IDs to `Array Nat` (for `propagateHints`). -/
def toHints (aids : List (BitVec 64)) : Array Nat :=
  (aids.map BitVec.toNat).toArray

/-! ## 4. `struct lrat_kernel_state` Representation (`KernelFields` & `kernelState`) -/

/-- The 20 64-bit fields of `struct lrat_kernel_state` at offsets `0, 8, ..., 152`. -/
structure KernelFields where
  used_begin : BitVec 64        -- offset 0
  antecedents_begin : BitVec 64 -- offset 8
  literals_begin : BitVec 64    -- offset 16
  values_begin : BitVec 64      -- offset 24
  marks_begin : BitVec 64       -- offset 32
  trail_begin : BitVec 64       -- offset 40
  trail_end : BitVec 64         -- offset 48
  work_begin : BitVec 64        -- offset 56
  empty_clause : BitVec 64      -- offset 64
  first_proof_id : BitVec 64    -- offset 72
  strict : BitVec 64            -- offset 80
  trimming : BitVec 64          -- offset 88
  checking : BitVec 64          -- offset 96
  forward : BitVec 64           -- offset 104
  stat_trimmed_cnf : BitVec 64  -- offset 112
  stat_trimmed_prf : BitVec 64  -- offset 120
  stat_chk_total : BitVec 64    -- offset 128
  stat_chk_empty : BitVec 64    -- offset 136
  stat_resolved : BitVec 64     -- offset 144
  stat_lit_assigned : BitVec 64 -- offset 152

def KernelFields.toList (k : KernelFields) : List (BitVec 64) :=
  [k.used_begin, k.antecedents_begin, k.literals_begin, k.values_begin,
   k.marks_begin, k.trail_begin, k.trail_end, k.work_begin,
   k.empty_clause, k.first_proof_id, k.strict, k.trimming,
   k.checking, k.forward, k.stat_trimmed_cnf, k.stat_trimmed_prf,
   k.stat_chk_total, k.stat_chk_empty, k.stat_resolved, k.stat_lit_assigned]

def kernelState (st : BitVec 64) (k : KernelFields) : Mem 64 → Prop :=
  word8Array st k.toList

/-! ## 5. Bridge Between Signed 32-Bit Literals, `CNF.Clause Nat`, and `Internal.Assignment` -/

/-- Absolute value of a 64-bit word using Bedrock2's `lit .< 0 ? -lit : lit`. -/
def bvAbs (lit : BitVec 64) : BitVec 64 :=
  if lit.slt 0 then -lit else lit

/-- Sign byte of a 64-bit word using Bedrock2's `(lit .>> 63) | 1` (`-1` if `lit < 0`, `1` if `lit ≥ 0`). -/
def bvSignByte (lit : BitVec 64) : BitVec 64 :=
  (lit.sshiftRight 63) ||| 1

/-- A 64-bit word `lit` represents a valid non-zero 32-bit signed DIMACS literal with variable in `1..max_var`. -/
def IsValidLit (max_var : Nat) (lit : BitVec 64) : Prop :=
  IsInt32 lit ∧ lit ≠ 0 ∧ (bvAbs lit).toNat ≤ max_var ∧ max_var < 2 ^ 31

/-- Map a Bedrock2 literal `lit` to `Std.Sat.Literal Nat = (Nat × Bool)`, using 1-based variable index
`(bvAbs lit).toNat` as the atom and `!lit.slt 0` (i.e. `0 < lit.toInt`) as polarity. -/
def toLiteral (lit : BitVec 64) : Literal Nat :=
  ((bvAbs lit).toNat, !lit.slt 0)

/-- Map a list of Bedrock2 literals to `Std.Sat.CNF.Clause Nat`. -/
def toClause (lits : List (BitVec 64)) : CNF.Clause Nat :=
  CNF.Clause.ofLiterals (lits.map toLiteral)

@[simp] theorem literals_toClause (lits : List (BitVec 64)) :
    (toClause lits).literals = lits.map toLiteral :=
  CNF.Clause.literals_ofLiterals

theorem bvAbs_pos {max_var : Nat} {lit : BitVec 64} (h : IsValidLit max_var lit) :
    0 < (bvAbs lit).toNat := by
  unfold IsValidLit bvAbs IsInt32 at *
  grind

theorem bvAbs_neg {max_var : Nat} {lit : BitVec 64} (h : IsValidLit max_var lit) :
    bvAbs (-lit) = bvAbs lit := by
  unfold IsValidLit bvAbs IsInt32 at *
  grind

theorem neg_slt_zero {max_var : Nat} {lit : BitVec 64} (h : IsValidLit max_var lit) :
    (-lit).slt 0 = !lit.slt 0 := by
  unfold IsValidLit bvAbs IsInt32 at *
  grind

@[simp] theorem toLiteral_neg {max_var : Nat} {lit : BitVec 64} (h : IsValidLit max_var lit) :
    toLiteral (-lit) = ((toLiteral lit).1, !(toLiteral lit).2) := by
  simp only [toLiteral, bvAbs_neg h, neg_slt_zero h]

theorem toLiteral_inj {l1 l2 : BitVec 64} :
    toLiteral l1 = toLiteral l2 ↔ l1 = l2 := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  unfold toLiteral bvAbs at h
  grind

theorem bvSignByte_eq {lit : BitVec 64} :
    bvSignByte lit = if lit.slt 0 then -1 else 1 := by
  have h : lit.sshiftRight 63 = if lit.slt 0 then -1 else 0 := by
    apply BitVec.eq_of_toInt_eq
    simp only [BitVec.toInt_sshiftRight, BitVec.slt]
    split <;> simp <;> grind
  unfold bvSignByte
  rw [h]; split <;> decide

theorem isInt8_bvSignByte (lit : BitVec 64) : IsInt8 (bvSignByte lit) := by
  rw [bvSignByte_eq]; split <;> decide

/-- Byte value stored at `values_begin + i` for atom `i` under `assign : Internal.Assignment`. -/
def assignByte (assign : Assignment) (i : Nat) : BitVec 64 :=
  if i = 0 then 0
  else match assign.get? i with
  | none => 0
  | some true => 1
  | some false => -1

theorem isInt8_assignByte (assign : Assignment) (i : Nat) : IsInt8 (assignByte assign i) := by
  simp only [assignByte]
  split
  · decide
  · rcases assign.get? i with _ | ⟨_ | _⟩ <;> decide

/-- The list of `max_var + 1` bytes at `values_begin[0 .. max_var]` representing `assign`. -/
def assignBytes (max_var : Nat) (assign : Assignment) : List (BitVec 64) :=
  (List.range (max_var + 1)).map (assignByte assign)

@[simp] theorem length_assignBytes (max_var : Nat) (assign : Assignment) :
    (assignBytes max_var assign).length = max_var + 1 := by
  simp [assignBytes]

@[simp] theorem getElem_assignBytes (max_var : Nat) (assign : Assignment) {i : Nat}
    (hi : i < max_var + 1) :
    (assignBytes max_var assign)[i]'(by simp [hi]) = assignByte assign i := by
  simp [assignBytes]

@[simp] theorem assignBytes_empty (max_var : Nat) :
    assignBytes max_var Assignment.empty = List.replicate (max_var + 1) 0 := by
  apply List.ext_getElem (by simp)
  intro i _ hi
  simp [assignBytes, assignByte]

theorem assignBytes_set_insert (max_var : Nat) (assign : Assignment) {lit : BitVec 64}
    (hlit : IsValidLit max_var lit) :
    (assignBytes max_var assign).set (toLiteral lit).1 (bvSignByte lit) =
      assignBytes max_var (assign.insert (toLiteral lit).1 (toLiteral lit).2) := by
  have hpos := bvAbs_pos hlit
  apply List.ext_getElem (by simp)
  intro i _ hi
  rw [getElem_assignBytes _ _ (by simpa using hi)]
  by_cases heq : i = (toLiteral lit).1
  · subst heq
    simp [toLiteral, assignByte, Nat.ne_of_gt hpos, Assignment.get?_insert_of_eq rfl, bvSignByte_eq]
    cases lit.slt 0 <;> rfl
  · rw [List.getElem_set_ne (Ne.symm heq), getElem_assignBytes _ _ (by simpa using hi)]
    by_cases h0 : i = 0 <;> simp [assignByte, h0, Assignment.get?_insert_of_ne (Ne.symm heq)]

/-- Value computed by `inline_assigned_literal` (`if lit < 0 then -b else b`) on `b = assignByte assign atom`. -/
def evalAssignedLit (b lit : BitVec 64) : BitVec 64 :=
  if lit.slt 0 then -b else b

theorem evalAssignedLit_spec {max_var : Nat} (assign : Assignment) {lit : BitVec 64}
    (hlit : IsValidLit max_var lit) :
    let v := evalAssignedLit (assignByte assign (toLiteral lit).1) lit
    match assign.get? (toLiteral lit).1 with
    | none => v = 0
    | some pol =>
      if pol == (toLiteral lit).2 then v = 1 ∧ (0#64).slt v = true ∧ v.slt 0 = false
      else v = -1 ∧ v.slt 0 = true ∧ (0#64).slt v = false := by
  have hpos := Nat.ne_of_gt (bvAbs_pos hlit)
  simp only [assignByte, toLiteral, evalAssignedLit, hpos, ↓reduceIte]
  rcases assign.get? (bvAbs lit).toNat with _ | ⟨_ | _⟩ <;> cases lit.slt 0 <;> decide

/-! ## 6. Trail Clearing (`inline_backtrack`) & Marks Array (`br_check_clause_strictly_by_resolution`) -/

/-- Effect of `inline_backtrack` clearing `bs[(bvAbs tlit).toNat] := 0` for each `tlit ∈ trail`. -/
def clearTrailBytes (bs : List (BitVec 64)) (trail : List (BitVec 64)) : List (BitVec 64) :=
  trail.foldl (fun acc tlit => acc.set (bvAbs tlit).toNat 0) bs

@[simp] theorem clearTrailBytes_nil (bs : List (BitVec 64)) :
    clearTrailBytes bs [] = bs := rfl

@[simp] theorem clearTrailBytes_cons (bs : List (BitVec 64)) (t : BitVec 64) (ts : List (BitVec 64)) :
    clearTrailBytes bs (t :: ts) = clearTrailBytes (bs.set (bvAbs t).toNat 0) ts := rfl

@[simp] theorem length_clearTrailBytes (bs : List (BitVec 64)) (trail : List (BitVec 64)) :
    (clearTrailBytes bs trail).length = bs.length := by
  induction trail generalizing bs with
  | nil => rfl
  | cons t ts ih => rw [clearTrailBytes_cons, ih, List.length_set]

theorem getElem?_clearTrailBytes (bs : List (BitVec 64)) (trail : List (BitVec 64))
    {i : Nat} (hi : i < bs.length) :
    (clearTrailBytes bs trail)[i]? =
      some (if ∃ tlit ∈ trail, (bvAbs tlit).toNat = i then 0 else bs[i]) := by
  induction trail generalizing bs with
  | nil => simp [List.getElem?_eq_getElem hi]
  | cons t ts ih =>
    rw [clearTrailBytes_cons, ih _ (by simp [hi])]
    apply congrArg some
    by_cases hex : ∃ tlit ∈ ts, (bvAbs tlit).toNat = i
    · simp [hex]
    · by_cases ht : (bvAbs t).toNat = i
      · subst ht; simp [hex, List.getElem_set_self]
      · simp [hex, ht, List.getElem_set_ne ht]

theorem getElem_clearTrailBytes (bs : List (BitVec 64)) (trail : List (BitVec 64))
    {i : Nat} (hi : i < bs.length) :
    (clearTrailBytes bs trail)[i]'(by simpa using hi) =
      if ∃ tlit ∈ trail, (bvAbs tlit).toNat = i then 0 else bs[i] := by
  have h := getElem?_clearTrailBytes bs trail hi
  rw [List.getElem?_eq_getElem (by simpa using hi)] at h
  exact Option.some.inj h

/-- If every non-zero entry of `bs` is covered by some literal in `trail`, then `clearTrailBytes bs trail`
resets `bs` to `List.replicate bs.length 0`. -/
theorem clearTrailBytes_eq_replicate_zero {bs : List (BitVec 64)} {trail : List (BitVec 64)}
    (hcov : ∀ (i : Nat) (hi : i < bs.length), bs[i] ≠ 0 → ∃ tlit ∈ trail, (bvAbs tlit).toNat = i) :
    clearTrailBytes bs trail = List.replicate bs.length 0 := by
  apply List.ext_getElem (by simp)
  intro i _ hi
  rw [getElem_clearTrailBytes bs trail (by simpa using hi), List.getElem_replicate]
  split <;> grind

/-- Invariant relating the trail of assigned literals `trail` to `assign : Assignment`:
every atom assigned in `assign` appears in `trail`. -/
def TrailCoversAssign (max_var : Nat) (assign : Assignment) (trail : List (BitVec 64)) : Prop :=
  ∀ i : Nat, i < max_var + 1 → assignByte assign i ≠ 0 → ∃ tlit ∈ trail, (bvAbs tlit).toNat = i

@[simp] theorem assignByte_empty (i : Nat) : assignByte Assignment.empty i = 0 := by
  unfold assignByte; split <;> simp

theorem trailCoversAssign_empty (max_var : Nat) :
    TrailCoversAssign max_var Assignment.empty [] := by
  grind [TrailCoversAssign, assignByte_empty]

theorem trailCoversAssign_insert {max_var : Nat} {assign : Assignment} {trail : List (BitVec 64)}
    (lit : BitVec 64) (hcov : TrailCoversAssign max_var assign trail) :
    TrailCoversAssign max_var (assign.insert (toLiteral lit).1 (toLiteral lit).2) (trail ++ [lit]) := by
  intro i hi hne
  by_cases heq : i = (toLiteral lit).1
  · exact ⟨lit, by simp, heq.symm⟩
  · obtain ⟨tlit, hmem, habs⟩ := hcov i hi (by
      by_cases hi0 : i = 0 <;> simp_all [assignByte, Assignment.get?_insert_of_ne (Ne.symm heq)])
    exact ⟨tlit, by simp [hmem], habs⟩

theorem clearTrailBytes_assignBytes {max_var : Nat} {assign : Assignment} {trail : List (BitVec 64)}
    (hcov : TrailCoversAssign max_var assign trail) :
    clearTrailBytes (assignBytes max_var assign) trail = assignBytes max_var Assignment.empty := by
  rw [assignBytes_empty, clearTrailBytes_eq_replicate_zero]
  · simp
  · grind [length_assignBytes, getElem_assignBytes, TrailCoversAssign]

/-- Combined memory predicate for `values_begin` (`max_var + 1` bytes) and `trail_begin` (`trail ++ trail_free`). -/
def ValuesTrail (max_var : Nat) (values_begin trail_begin trail_end : BitVec 64)
    (assign : Assignment) (trail trail_free : List (BitVec 64)) : Mem 64 → Prop :=
  fun m =>
    trail_end = trail_begin + BitVec.ofNat 64 (4 * trail.length) ∧
    TrailCoversAssign max_var assign trail ∧
    (m =⋆ byte1Array values_begin (assignBytes max_var assign) ⋆
      int4Array trail_begin (trail ++ trail_free))

/-- Read-only separation-logic invariant for a predicate `P_ro : Mem 64 → Prop` holding the clause pointer
table at `literals_begin` and all active 0-terminated clause literal arrays in memory, linked to
`clauses : Array (Option (CNF.Clause Nat))`. Because `P_ro` sits in the frame (`m =⋆ P_ro ⋆ R_rw`),
`ClauseTable` is automatically preserved across all stores to `R_rw`. -/
def ClauseTable (max_var : Nat) (literals_begin : BitVec 64) (lit_ptrs : List (BitVec 64))
    (clauses : Array (Option (CNF.Clause Nat))) (P_ro : Mem 64 → Prop) : Prop :=
  (∃ R, P_ro = (word8Array literals_begin lit_ptrs ⋆ R)) ∧
  ∀ (aid : Nat) (h : aid < lit_ptrs.length),
    0 < aid → lit_ptrs[aid] ≠ 0 →
      ∃ (clits : List (BitVec 64)) (R : Mem 64 → Prop),
        P_ro = (ZeroTermInts lit_ptrs[aid] clits ⋆ R) ∧
        (∀ l ∈ clits, IsValidLit max_var l) ∧
        clauses[aid - 1]? = some (some (toClause clits))

theorem ClauseTable.eval_load_ptr {max_var : Nat} {literals_begin : BitVec 64}
    {lit_ptrs : List (BitVec 64)} {clauses : Array (Option (CNF.Clause Nat))}
    {P_ro R : Mem 64 → Prop} {m : Mem 64} {l : Locals 64} {ea : Expr} {aid : Nat}
    (hct : ClauseTable max_var literals_begin lit_ptrs clauses P_ro)
    (hsep : m =⋆ P_ro ⋆ R)
    (haid : aid < lit_ptrs.length)
    (ha : ea.eval m l = some (literals_begin + BitVec.ofNat 64 (8 * aid))) :
    (Expr.load .eight ea).eval m l = some lit_ptrs[aid] := by
  obtain ⟨R1, hP⟩ := hct.1
  rw [hP, sep_assoc] at hsep
  exact eval_load_word8Array_elem haid ha hsep

theorem ClauseTable.lookup_clause {max_var : Nat} {literals_begin : BitVec 64}
    {lit_ptrs : List (BitVec 64)} {clauses : Array (Option (CNF.Clause Nat))}
    {P_ro R : Mem 64 → Prop} {m : Mem 64} {aid : Nat}
    (hct : ClauseTable max_var literals_begin lit_ptrs clauses P_ro)
    (hsep : m =⋆ P_ro ⋆ R)
    (haid : aid < lit_ptrs.length) (hpos : 0 < aid) (hne : lit_ptrs[aid] ≠ 0) :
    ∃ (clits : List (BitVec 64)) (R' : Mem 64 → Prop),
      (m =⋆ ZeroTermInts lit_ptrs[aid] clits ⋆ R') ∧
      (∀ l ∈ clits, IsValidLit max_var l) ∧
      clauses[aid - 1]? = some (some (toClause clits)) := by
  obtain ⟨clits, R1, hP, hvalid, hcl⟩ := hct.2 aid haid hpos hne
  rw [hP, sep_assoc] at hsep
  exact ⟨clits, R1 ⋆ R, hsep, hvalid, hcl⟩

end Kraken.Bedrock2.Test
