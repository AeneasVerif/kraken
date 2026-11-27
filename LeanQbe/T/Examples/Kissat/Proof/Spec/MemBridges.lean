/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Ref.Dimacs
public import LeanQbe.T.Examples.Kissat.Ref.Sat
public import LeanQbe.T.Logic.Bytes
public import LeanQbe.T.Logic.Rules
public import Kraken.Mem
public import Kraken.Separation

/-!
# Shared Kissat Memory Bridges, DIMACS Pure Mirrors, and BitVec Helpers (`Proof.Spec.MemBridges`)

Consolidated architecture-free memory/BitVec/DIMACS bridge layer for `Kissat.Proof.Spec`:
1. Pure DIMACS parser bounds (`skipWsComments_length_le`, `parseNat_lt_bound`,
   `parseNat_length_lt`, `parseClauseAux_fuel_irrel`).
2. Typed-array / `region` conversions (`array_to_region`, `region_to_array_i8`,
   `region_to_array_i32`, `region_to_array64`, `array_slice_focus`), `BitVec` address helpers,
   and 8-byte alignment size helpers (`valsBytes`, `markBytes`, `u32VarBytes`, `whBytes`,
   `fixedBytes`).
3. Ingestion helpers (`bv64_align8`, `bv64_mul24`, `bv32_and1_add1`, `bv8_zext32_eq`,
   `UnitSatTrace`, `UnitUnsatTrace`, `parseClauseAux_vars_pos`, `parseClauses_some_of_acc`,
   `cnf_unsat_add`).
4. `dimacsState` memory predicate, pure scanner/model-checker mirrors (`nextLitPure`,
   `evalLitVals`, `checkClauseValsAux`, `checkClausesVals`, `runKissatCheckModel`,
   `modelOfVals`), and `runKissatCheckModel_sound`.
5. Separation-logic framing helpers (`nv_sep_append`, `sep_exists_eq`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Spec

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat.Ref
open Kraken.Bedrock2.Test

/-! ## 1. Pure DIMACS parser length and bound helpers -/
private theorem skipWsCommentsAux_true_cons (c : UInt8) (bs : List UInt8) :
    skipWsCommentsAux true (c :: bs) =
      if c = 10 then skipWsCommentsAux false bs else skipWsCommentsAux true bs := by
  by_cases h : c = 10
  · subst h; rfl
  · simp only [h, ↓reduceIte]; rw [skipWsCommentsAux.eq_3]; exact h

private theorem skipWsCommentsAux_false_cons (b : UInt8) (bs : List UInt8) :
    skipWsCommentsAux false (b :: bs) =
      if isDimacsWs b then skipWsCommentsAux false bs
      else if b == 99 then skipWsCommentsAux true bs else b :: bs := rfl

private theorem skipWsCommentsAux_length_le (inC : Bool) (bs : List UInt8) :
    (skipWsCommentsAux inC bs).length ≤ bs.length := by
  induction bs generalizing inC with
  | nil => cases inC <;> simp [skipWsCommentsAux]
  | cons b bs ih =>
    cases inC
    · rw [skipWsCommentsAux_false_cons]; grind
    · rw [skipWsCommentsAux_true_cons]; split <;> exact Nat.le_trans (ih _) (by simp)

theorem skipWsComments_length_le (bs : List UInt8) :
    (skipWsComments bs).length ≤ bs.length := skipWsCommentsAux_length_le false bs

theorem parseDigitsAux_lt_bound {acc : Nat} {bs : List UInt8} {v : Nat} {rest : List UInt8}
    (hacc : acc < dimacsBound) (h : parseDigitsAux acc bs = some (v, rest)) :
    v < dimacsBound := by
  induction bs generalizing acc with
  | nil => simp [parseDigitsAux] at h; obtain ⟨rfl, _⟩ := h; exact hacc
  | cons b bs ih =>
    simp only [parseDigitsAux] at h
    grind

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

private theorem parseDigitsAux_length_le {acc : Nat} {bs : List UInt8} {v : Nat}
    {rest : List UInt8} (h : parseDigitsAux acc bs = some (v, rest)) :
    rest.length ≤ bs.length := by
  induction bs generalizing acc with
  | nil => simp [parseDigitsAux] at h; obtain ⟨_, rfl⟩ := h; exact Nat.le_refl _
  | cons b bs ih =>
    rw [parseDigitsAux] at h
    by_cases hd : isDimacsDigit b
    · simp only [hd, ↓reduceIte] at h; split at h
      · exact Nat.le_trans (ih h) (Nat.le_succ _)
      · cases h
    · by_cases hws : isDimacsWs b <;>
        simp only [hd, hws, Bool.false_eq_true, ↓reduceIte] at h <;> cases h; exact Nat.le_refl _

theorem parseNat_length_lt {bs : List UInt8} {v : Nat} {rest : List UInt8}
    (h : parseNat bs = some (v, rest)) : rest.length < bs.length := by
  cases bs with
  | nil => nomatch h
  | cons b bs =>
    rw [parseNat] at h
    by_cases hd : isDimacsDigit b
    · simp only [hd, ↓reduceIte] at h; exact Nat.lt_succ_of_le (parseDigitsAux_length_le h)
    · simp only [hd, Bool.false_eq_true, ↓reduceIte] at h; cases h

private theorem parseClauseAux_succ_eq (fuel mv : Nat) (acc : List (Literal Nat))
    (bs : List UInt8) :
    parseClauseAux (fuel + 1) mv acc bs =
      match skipWsComments bs with
      | [] => none
      | 45 :: rest => match parseNat rest with
        | some (v, rest') =>
          if 1 ≤ v && v ≤ mv then parseClauseAux fuel mv ((v, false) :: acc) rest' else none
        | none => none
      | b :: rest => match parseNat (b :: rest) with
        | some (0, rest') => some (CNF.Clause.ofLiterals acc.reverse, rest')
        | some (v, rest') =>
          if 1 ≤ v && v ≤ mv then parseClauseAux fuel mv ((v, true) :: acc) rest' else none
        | none => none := rfl


private theorem parseClauseAux_succ_45 {fuel mv : Nat} {acc : List (Literal Nat)}
    {bs rest : List UInt8} (h : skipWsComments bs = 45 :: rest) :
    parseClauseAux (fuel + 1) mv acc bs =
      match parseNat rest with
      | some (v, rest') =>
        if 1 ≤ v && v ≤ mv then parseClauseAux fuel mv ((v, false) :: acc) rest' else none
      | none => none := by
  rw [parseClauseAux_succ_eq, h]; rfl

private theorem parseClauseAux_succ_pos {fuel mv : Nat} {acc : List (Literal Nat)}
    {b : UInt8} {bs rest : List UInt8} (h : skipWsComments bs = b :: rest) (hb : b ≠ 45) :
    parseClauseAux (fuel + 1) mv acc bs =
      match parseNat (b :: rest) with
      | some (0, rest') => some (CNF.Clause.ofLiterals acc.reverse, rest')
      | some (v, rest') =>
        if 1 ≤ v && v ≤ mv then parseClauseAux fuel mv ((v, true) :: acc) rest' else none
      | none => none := by
  rw [parseClauseAux_succ_eq, h]
  split
  · rename_i heq; cases heq
  · rename_i heq; exact absurd (List.cons.inj heq).1 hb
  · rename_i heq; cases heq; rfl

theorem parseClauseAux_fuel_irrel {f1 f2 mv : Nat} {acc : List (Literal Nat)}
    {bs : List UInt8} (h1 : bs.length < f1) (h2 : bs.length < f2) :
    parseClauseAux f1 mv acc bs = parseClauseAux f2 mv acc bs := by
  induction f1 generalizing f2 acc bs with
  | zero => omega
  | succ fuel1 ih =>
    cases f2 with
    | zero => omega
    | succ fuel2 =>
      have hsw_len := skipWsComments_length_le bs
      cases hsw : skipWsComments bs with
      | nil => simp [parseClauseAux_succ_eq, hsw]
      | cons b rest =>
        have hcr_len : (b :: rest).length ≤ bs.length := by rwa [← hsw]
        by_cases hb : b = 45
        · subst hb; rw [parseClauseAux_succ_45 hsw, parseClauseAux_succ_45 hsw]
          rcases hpn : parseNat rest with _ | ⟨v, rest'⟩
          · rfl
          · have := parseNat_length_lt hpn; grind
        · rw [parseClauseAux_succ_pos hsw hb, parseClauseAux_succ_pos hsw hb]
          rcases hpn : parseNat (b :: rest) with _ | ⟨v, rest'⟩
          · rfl
          · cases v with | zero => rfl | succ _ => have := parseNat_length_lt hpn; grind

/-! ## 2. Typed-array / `region` conversions and `BitVec` address helpers -/

theorem array_to_region {t : Ty} {a : BitVec 64} {xs : List (Val t)} {f : Mem 64}
    (h : t.bytes * xs.length ≤ 2 ^ 64) (hf : array a xs f) :
    region a (t.bytes * xs.length) f :=
  ⟨bytesOf xs, bytesOf_length xs, array_eq_bytesOf a xs h hf⟩

theorem bytesOf_i8_eq_map (xs : List (BitVec 8)) :
    bytesOf (t := i8) xs = xs.map UInt8.ofBitVec := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [bytesOf, List.flatMap_cons, List.map_cons, toBits, i8, Ty.bytes, Ty.size] at ih ⊢
    rw [ih]
    have h1 : Int.toBytes 1 (x.setWidth 8).toInt = [UInt8.ofBitVec x] := by
      rw [BitVec.setWidth_eq, ← Int.toBytes_emod, show (8 * 1 : Nat) = 8 by rfl]
      change Int.toBytes 1 (x.toInt % (2 ^ 8 : Int)) = [UInt8.ofBitVec x]
      rw [BitVec.toInt_emod_two_pow]
      exact toBytes_u8 (UInt8.ofBitVec x)
    rw [h1]; rfl

theorem byte1_eq_cell_i8 (a v : BitVec 64) : byte1 a v = cell (t := i8) a (v.setWidth 8) := by
  unfold byte1 cell; congr 2
  have h1 : (8 * i8.bytes : Nat) = 8 := rfl
  rw [← Int.toBytes_emod (n := 1), ← Int.toBytes_emod (n := i8.bytes)]
  congr 1
  simp only [Int.take, toBits, i8, Ty.bytes, Ty.size, BitVec.setWidth_eq]
  change (v.toNat : Int) % (2 ^ 8 : Int) = (v.setWidth 8).toInt % (2 ^ 8 : Int)
  rw [BitVec.toInt_emod_two_pow, BitVec.toNat_setWidth]
  exact_mod_cast (rfl : v.toNat % 2 ^ 8 = v.toNat % 2 ^ 8)

theorem int4_eq_cell_i32 (a v : BitVec 64) : int4 a v = cell (t := i32) a (v.setWidth 32) := by
  unfold int4 cell; congr 2
  rw [← Int.toBytes_emod (n := 4), ← Int.toBytes_emod (n := i32.bytes)]
  congr 1
  simp only [Int.take, toBits, i32, Ty.bytes, Ty.size, BitVec.setWidth_eq]
  change (v.toNat : Int) % (2 ^ 32 : Int) = (v.setWidth 32).toInt % (2 ^ 32 : Int)
  rw [BitVec.toInt_emod_two_pow, BitVec.toNat_setWidth]
  exact_mod_cast (rfl : v.toNat % 2 ^ 32 = v.toNat % 2 ^ 32)

theorem byte1Array_eq_array_i8 (a : BitVec 64) (xs : List (BitVec 64)) :
    byte1Array a xs = array (t := i8) a (xs.map (·.setWidth 8)) := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    rw [byte1Array_cons, List.map_cons, array_cons, byte1_eq_cell_i8, ih]; rfl

theorem int4Array_eq_array_i32 (a : BitVec 64) (xs : List (BitVec 64)) :
    int4Array a xs = array (t := i32) a (xs.map (·.setWidth 32)) := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    rw [int4Array_cons, List.map_cons, array_cons, int4_eq_cell_i32, ih]; rfl

theorem region_to_array_i8 {a : BitVec 64} (k : Nat) (hk : k ≤ 2 ^ 64) {f : Mem 64}
    (hf : region a k f) : ∃ xs : List (BitVec 8), xs.length = k ∧ array (t := i8) a xs f := by
  obtain ⟨ws, hlen, hba⟩ := region_to_byte1Array k hk hf
  rw [byte1Array_eq_array_i8] at hba
  exact ⟨ws.map (·.setWidth 8), by simp [hlen], hba⟩

theorem region_to_array_i32 {a : BitVec 64} (k : Nat) (hk : 4 * k ≤ 2 ^ 64) {f : Mem 64}
    (hf : region a (4 * k) f) :
    ∃ xs : List (BitVec 32), xs.length = k ∧ array (t := i32) a xs f := by
  obtain ⟨ws, hlen, hia⟩ := region_to_int4Array k hk hf
  rw [int4Array_eq_array_i32] at hia
  exact ⟨ws.map (·.setWidth 32), by simp [hlen], hia⟩

theorem region_to_array64 {a : BitVec 64} (k : Nat) (hk : 8 * k ≤ 2 ^ 64) {f : Mem 64}
    (hf : region a (8 * k) f) : ∃ xs : List (BitVec 64), xs.length = k ∧ array64 a xs f := by
  obtain ⟨ws, hlen, hwa⟩ := region_to_word8Array k hk hf
  rw [← array64_eq_word8Array] at hwa
  exact ⟨ws, hlen, hwa⟩

theorem array_slice_focus {t : Ty} (a : BitVec 64) (xs : List (Val t)) {off sz : Nat}
    (h : off + sz ≤ xs.length) :
    array a xs =
      (array (a + BitVec.ofNat 64 (t.bytes * off)) ((xs.drop off).take sz) ⋆
        (array a (xs.take off) ⋆
          array (a + BitVec.ofNat 64 (t.bytes * (off + sz))) (xs.drop (off + sz)))) := by
  have h1 : xs = xs.take off ++ ((xs.drop off).take sz ++ xs.drop (off + sz)) := by
    have hd : xs.drop (off + sz) = (xs.drop off).drop sz := by
      rw [List.drop_drop, Nat.add_comm]
    rw [hd, List.take_append_drop, List.take_append_drop]
  have hlen1 : (xs.take off).length = off := List.length_take_of_le (by omega)
  have hlen2 : ((xs.drop off).take sz).length = sz := by
    rw [List.length_take, List.length_drop]; omega
  conv => lhs; rw [h1]
  rw [array_append, hlen1, array_append, hlen2, ptr_add_ofNat, ← Nat.mul_add]
  ac_rfl

/-- `BitVec` address and arithmetic helpers matching C0 lowering. -/
theorem bv32_zext64_eq (x : BitVec 32) : x.setWidth 64 = BitVec.ofNat 64 x.toNat := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ 64)]

theorem bv32_lshr_1 (x : BitVec 32) : (x >>> 1).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem bv32_xor_1 (x : BitVec 32) : (x ^^^ (1 : BitVec 32)).toNat = x.toNat ^^^ 1 := by
  simp [BitVec.toNat_xor]

theorem bv32_and_1 (x : BitVec 32) : (x &&& (1 : BitVec 32)).toNat = x.toNat % 2 := by
  simp [BitVec.toNat_and, Nat.and_one_is_mod]

theorem bv_ofNat_toNat_eq {n : Nat} (x : BitVec n) : BitVec.ofNat n x.toNat = x :=
  BitVec.eq_of_toNat_eq (by simp)

theorem litNeg_lt_two_mul {l mv : Nat} (hl : l < 2 * mv) : (l ^^^ 1) < 2 * mv := by
  have h := litNeg_eq l; unfold litNeg at h; split at h <;> omega

theorem bv32_mul4_eq (x : BitVec 32) :
    x.setWidth 64 * (4 : BitVec 64) = BitVec.ofNat 64 (4 * x.toNat) := by
  rw [bv32_zext64_eq]; grind

theorem bv64_mul4_nat (n : Nat) :
    BitVec.ofNat 64 n * (4 : BitVec 64) = BitVec.ofNat 64 (4 * n) := by grind

theorem bv32_mul16_eq (x : BitVec 32) :
    x.setWidth 64 * (16 : BitVec 64) = BitVec.ofNat 64 (4 * (4 * x.toNat)) := by
  rw [bv32_zext64_eq]; grind

theorem bv64_mul16_nat (n : Nat) :
    BitVec.ofNat 64 n * (16 : BitVec 64) = BitVec.ofNat 64 (4 * (4 * n)) := by grind

theorem bv_shl_sext1 {n : Nat} :
    BitVec.ofNat 64 n <<< (((1 : BitVec 32).signExtend 64).toNat % 64) =
      BitVec.ofNat 64 (2 * n) := by
  have hs : ((1 : BitVec 32).signExtend 64).toNat % 64 = 1 := rfl
  rw [hs]; apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega

theorem bv_shl_sext2 {n : Nat} :
    BitVec.ofNat 64 n <<< (((2 : BitVec 32).signExtend 64).toNat % 64) =
      BitVec.ofNat 64 (4 * n) := by
  have hs : ((2 : BitVec 32).signExtend 64).toNat % 64 = 2 := rfl
  rw [hs]; apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega

theorem bv_shl_sext4 {n : Nat} :
    BitVec.ofNat 64 n <<< (((4 : BitVec 32).signExtend 64).toNat % 64) =
      BitVec.ofNat 64 (16 * n) := by
  have hs : ((4 : BitVec 32).signExtend 64).toNat % 64 = 4 := rfl
  rw [hs]; apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega

theorem bv_shr_sext2 {n : Nat} (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n >>> (((2 : BitVec 32).signExtend 64).toNat % 64) =
      BitVec.ofNat 64 (n / 4) := by
  have hs : ((2 : BitVec 32).signExtend 64).toNat % 64 = 2 := rfl
  rw [hs]; apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (by omega : n / 4 < 2 ^ 64)]

theorem bv_shr_sext6 {n : Nat} (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n >>> (((6 : BitVec 32).signExtend 64).toNat % 64) =
      BitVec.ofNat 64 (n / 64) := by
  have hs : ((6 : BitVec 32).signExtend 64).toNat % 64 = 6 := rfl
  rw [hs]; apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (by omega : n / 64 < 2 ^ 64)]

theorem bv64_trunc32_ofNat {n : Nat} (hn : n < 2 ^ 32) :
    (BitVec.ofNat 64 n).setWidth 32 = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  simp [Nat.mod_eq_of_lt hn]

theorem bv32_ofNat_toNat {n : Nat} (hn : n < 2 ^ 32) :
    (BitVec.ofNat 32 n).toNat = n := by
  simp [Nat.mod_eq_of_lt hn]

theorem bv64_ofNat_toNat {n : Nat} (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n).toNat = n := by
  simp [Nat.mod_eq_of_lt hn]

theorem bv32_ult_eq {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (BitVec.ofNat 32 a).ult (BitVec.ofNat 32 b) = decide (a < b) := by
  simp [BitVec.ult, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem bv32_ule_eq {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (BitVec.ofNat 32 a).ule (BitVec.ofNat 32 b) = decide (a ≤ b) := by
  simp [BitVec.ule, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem trunc32_8_zero : (0 : BitVec 32).setWidth 8 = 0#8 := rfl
theorem trunc32_8_one : (1 : BitVec 32).setWidth 8 = 1#8 := rfl
theorem trunc32_8_neg1 : (-(1 : BitVec 32)).setWidth 8 = 0xFF#8 := rfl

theorem i8_sext32_zero : (0#8).signExtend 32 = 0#32 := rfl

theorem i8_vals_sgt0 {b : BitVec 8} (hd : b = 0#8 ∨ b = 1#8 ∨ b = 0xFF#8) :
    (0#32).slt (b.signExtend 32) = true ↔ b = 1#8 := by
  rcases hd with rfl | rfl | rfl <;> decide

theorem i8_vals_slt0 {b : BitVec 8} (hd : b = 0#8 ∨ b = 1#8 ∨ b = 0xFF#8) :
    (b.signExtend 32).slt 0#32 = true ↔ b = 0xFF#8 := by
  rcases hd with rfl | rfl | rfl <;> decide

theorem i8_vals_eq0 {b : BitVec 8} (hd : b = 0#8 ∨ b = 1#8 ∨ b = 0xFF#8) :
    b.signExtend 32 = 0#32 ↔ b = 0#8 := by
  rcases hd with rfl | rfl | rfl <;> decide

/-! ## 3. Arena geometry (`ArenaCfg`), state (`ArenaState`), and memory predicate (`ArenaMem`) -/

/-- Rounded 8-byte-aligned byte sizes matching `kissat_init_state`. -/
@[expose] def valsBytes (mv : Nat) : Nat := ((2 * mv + 7) / 8) * 8
@[expose] def markBytes (mv : Nat) : Nat := ((mv + 7) / 8) * 8
@[expose] def u32VarBytes (mv : Nat) : Nat := ((4 * mv + 7) / 8) * 8
@[expose] def whBytes (mv : Nat) : Nat := ((8 * mv + 7) / 8) * 8
@[expose] def fixedBytes (mv : Nat) : Nat :=
  200 + valsBytes mv + markBytes mv + 4 * u32VarBytes mv + whBytes mv

theorem valsBytes_ge (mv : Nat) : 2 * mv ≤ valsBytes mv := by unfold valsBytes; omega
theorem markBytes_ge (mv : Nat) : mv ≤ markBytes mv := by unfold markBytes; omega
theorem u32VarBytes_ge (mv : Nat) : 4 * mv ≤ u32VarBytes mv := by unfold u32VarBytes; omega
theorem whBytes_ge (mv : Nat) : 8 * mv ≤ whBytes mv := by unfold whBytes; omega

theorem fixedBytes_lt {mv : Nat} (hmv : mv < dimacsBound) : fixedBytes mv < 2 ^ 34 := by
  unfold fixedBytes valsBytes markBytes u32VarBytes whBytes dimacsBound at *; omega

/-! ## 3. Alignment, `UnitSatTrace`, and `UnitUnsatTrace` helpers -/

theorem bv64_align8 {n : Nat} (hn : n + 7 < 2 ^ 64) :
    (BitVec.ofNat 64 n + (7 : BitVec 64)) &&& (~~~(7 : BitVec 64)) =
      BitVec.ofNat 64 (((n + 7) / 8) * 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [show (7 : BitVec 64) = BitVec.ofNat 64 7 from rfl, bv_add_ofNat]
  have h1 : BitVec.ofNat 64 (n + 7) &&& ~~~(BitVec.ofNat 64 7) =
      BitVec.ofNat 64 (((n + 7) / 8) * 8) := by
    apply BitVec.eq_of_toNat_eq
    have hmod : (n + 7) % 2 ^ 64 = n + 7 := Nat.mod_eq_of_lt hn
    have hmod2 : (((n + 7) / 8) * 8) % 2 ^ 64 = ((n + 7) / 8) * 8 :=
      Nat.mod_eq_of_lt (by omega)
    simp only [BitVec.toNat_and, BitVec.toNat_not, BitVec.toNat_ofNat, hmod, hmod2]
    have hnot : (2 ^ 64 - 1 - 7 % 2 ^ 64) = 2 ^ 64 - 8 := by decide
    rw [hnot]
    have hdiv := Nat.and_div_two_pow (a := n + 7) (b := 2 ^ 64 - 8) (n := 3)
    have hrem := Nat.and_mod_two_pow (a := n + 7) (b := 2 ^ 64 - 8) (n := 3)
    have hbdiv : (2 ^ 64 - 8) / 2 ^ 3 = 2 ^ 61 - 1 := by decide
    have hbrem : (2 ^ 64 - 8) % 2 ^ 3 = 0 := by decide
    rw [hbdiv] at hdiv; rw [hbrem, Nat.and_zero] at hrem
    have hq : ((n + 7) / 8) &&& (2 ^ 61 - 1) = (n + 7) / 8 := by
      have hlt : (n + 7) / 8 < 2 ^ 61 := by omega
      simpa [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hlt] using
        Nat.and_two_pow_sub_one_eq_mod ((n + 7) / 8) 61
    have hpow : (2 ^ 3 : Nat) = 8 := by decide
    rw [hpow] at hdiv hrem
    rw [hq] at hdiv
    omega
  exact congrArg BitVec.toNat h1

theorem bv64_mul24 (n : Nat) :
    BitVec.ofNat 64 n * (24 : BitVec 64) = BitVec.ofNat 64 (n * 24) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, Nat.mul_mod]

theorem bv32_and1_add1 (x : BitVec 32) :
    ((x &&& (1 : BitVec 32)) + (1 : BitVec 32)).setWidth 8 =
      BitVec.ofNat 8 (x.toNat % 2 + 1) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (x &&& (1 : BitVec 32)).toNat = x.toNat % 2 := bv32_and_1 x
  have h2 : (1 : BitVec 32).toNat = 1 := rfl
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, h1, h2, BitVec.toNat_ofNat]
  omega

theorem bv8_zext32_eq {a b : BitVec 8} :
    a.setWidth 32 = b.setWidth 32 ↔ a = b := by
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    have ht := congrArg BitVec.toNat h
    have ha : a.toNat < 2 ^ 32 := by have := a.isLt; omega
    have hb : b.toNat < 2 ^ 32 := by have := b.isLt; omega
    simp only [BitVec.toNat_setWidth, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at ht
    exact ht
  · intro h; rw [h]

/-- Memory footprint of `KissatDimacs { mv; nc; cur; val }` at address `d` (32 bytes = 4 `u64`s). -/
@[expose] def dimacsState (d mv nc cur val : BitVec 64) : Mem 64 → Prop :=
  array64 d [mv, nc, cur, val]

theorem dimacsState_eq_word8Array (d mv nc cur val : BitVec 64) :
    dimacsState d mv nc cur val = word8Array d [mv, nc, cur, val] :=
  array64_eq_word8Array d [mv, nc, cur, val]

theorem dimacsState_to_region {d mv nc cur val : BitVec 64} {f : Mem 64}
    (h : dimacsState d mv nc cur val f) : region d 32 f := by
  rw [dimacsState_eq_word8Array] at h
  simpa using word8Array_to_region (by simp) h

theorem region32_to_dimacsState {d : BitVec 64} {f : Mem 64}
    (h : region d 32 f) : ∃ mv nc cur val, dimacsState d mv nc cur val f := by
  obtain ⟨ws, hlen, hwa⟩ := region_to_word8Array 4 (by decide) (by simpa using h)
  rcases ws with _ | ⟨mv, _ | ⟨nc, _ | ⟨cur, _ | ⟨val, _ | _⟩⟩⟩⟩ <;> simp at hlen
  exact ⟨mv, nc, cur, val, by rwa [dimacsState_eq_word8Array]⟩

theorem dimacsState_bytes (d mv nc cur val : BitVec 64) :
    dimacsState d mv nc cur val ((bytes64 [mv, nc, cur, val]).At d) :=
  array64_bytes d [mv, nc, cur, val] (by simp)

theorem load_dimacs_mv {d mv nc cur val : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (dimacsState d mv nc cur val ⋆ R) m) : loadVal m i64 d = some mv := by
  simpa [dimacsState] using loadVal_array64 (i := 0) (by simp) hm

theorem load_dimacs_nc {d mv nc cur val : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (dimacsState d mv nc cur val ⋆ R) m) : loadVal m i64 (d + 8) = some nc := by
  simpa [dimacsState] using loadVal_array64 (i := 1) (by simp) hm

theorem load_dimacs_cur {d mv nc cur val : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (dimacsState d mv nc cur val ⋆ R) m) : loadVal m i64 (d + 16) = some cur := by
  simpa [dimacsState] using loadVal_array64 (i := 2) (by simp) hm

theorem load_dimacs_val {d mv nc cur val : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (dimacsState d mv nc cur val ⋆ R) m) : loadVal m i64 (d + 24) = some val := by
  simpa [dimacsState] using loadVal_array64 (i := 3) (by simp) hm

theorem store_dimacs_mv {d mv nc cur val : BitVec 64} (mv' : BitVec 64)
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (dimacsState d mv nc cur val ⋆ R) m) :
    storeOk m i64 d ∧ (dimacsState d mv' nc cur val ⋆ R) (storeMem m i64 d mv') := by
  simpa [dimacsState] using store_array64 (i := 0) mv' (by simp) hm

theorem store_dimacs_nc {d mv nc cur val : BitVec 64} (nc' : BitVec 64)
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (dimacsState d mv nc cur val ⋆ R) m) :
    storeOk m i64 (d + 8) ∧ (dimacsState d mv nc' cur val ⋆ R) (storeMem m i64 (d + 8) nc') := by
  simpa [dimacsState] using store_array64 (i := 1) nc' (by simp) hm

theorem store_dimacs_cur {d mv nc cur val : BitVec 64} (cur' : BitVec 64)
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (dimacsState d mv nc cur val ⋆ R) m) :
    storeOk m i64 (d + 16) ∧
      (dimacsState d mv nc cur' val ⋆ R) (storeMem m i64 (d + 16) cur') := by
  simpa [dimacsState] using store_array64 (i := 2) cur' (by simp) hm

theorem store_dimacs_val {d mv nc cur val : BitVec 64} (val' : BitVec 64)
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (dimacsState d mv nc cur val ⋆ R) m) :
    storeOk m i64 (d + 24) ∧
      (dimacsState d mv nc cur val' ⋆ R) (storeMem m i64 (d + 24) val') := by
  simpa [dimacsState] using store_array64 (i := 3) val' (by simp) hm

/-- Word-level predicate computed by `kissat_is_ws`. -/
@[expose] def isWsWord (b : BitVec 64) : Bool :=
  (b == 32) || (BitVec.ule 9 b && BitVec.ule b 13)

/-- Word-level predicate computed by `kissat_is_digit`. -/
@[expose] def isDigitWord (b : BitVec 64) : Bool :=
  BitVec.ule 48 b && BitVec.ule b 57

theorem isWsWord_ofUInt8 (b : UInt8) :
    isWsWord (BitVec.ofNat 64 b.toNat) = isDimacsWs b := by
  unfold isWsWord isDimacsWs
  have hb := b.toNat_lt
  simp only [BitVec.ule, BitVec.toNat_ofNat, u8_le_iff_toNat,
    Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ 64)]
  grind

theorem isDigitWord_ofUInt8 (b : UInt8) :
    isDigitWord (BitVec.ofNat 64 b.toNat) = isDimacsDigit b := by
  unfold isDigitWord isDimacsDigit
  have hb := b.toNat_lt
  simp only [BitVec.ule, BitVec.toNat_ofNat, u8_le_iff_toNat,
    Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ 64)]
  grind

theorem cursor_ult_eq {base : BitVec 64} {i n : Nat}
    (hfit : base.toNat + n < 2 ^ 64) (hi : i ≤ n) :
    (base + BitVec.ofNat 64 i).ult (base + BitVec.ofNat 64 n) = decide (i < n) := by
  simp only [BitVec.ult, bv_add_ofNat_toNat (by omega : base.toNat + i < 2 ^ 64),
    bv_add_ofNat_toNat hfit]
  grind

theorem cursor_ule_rev_eq {base : BitVec 64} {i n : Nat}
    (hfit : base.toNat + n < 2 ^ 64) (hi : i ≤ n) :
    (base + BitVec.ofNat 64 n).ule (base + BitVec.ofNat 64 i) = decide (i = n) := by
  simp only [BitVec.ule, bv_add_ofNat_toNat (by omega : base.toNat + i < 2 ^ 64),
    bv_add_ofNat_toNat hfit]
  grind

theorem cursor_ult_rev_false {base : BitVec 64} {i n : Nat}
    (hfit : base.toNat + n < 2 ^ 64) (hi : i ≤ n) :
    (base + BitVec.ofNat 64 n).ult (base + BitVec.ofNat 64 i) = false := by
  simp only [BitVec.ult, bv_add_ofNat_toNat (by omega : base.toNat + i < 2 ^ 64),
    bv_add_ofNat_toNat hfit]
  grind

theorem cursor_sub_eq {base : BitVec 64} {i n : Nat}
    (hfit : base.toNat + n < 2 ^ 64) (hi : i ≤ n) :
    (base + BitVec.ofNat 64 n) - (base + BitVec.ofNat 64 i) = BitVec.ofNat 64 (n - i) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le (by
      rw [BitVec.le_def, bv_add_ofNat_toNat (by omega), bv_add_ofNat_toNat hfit]; omega),
    bv_add_ofNat_toNat hfit, bv_add_ofNat_toNat (by omega),
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

theorem bv32_u8_eq {b k : UInt8} :
    (BitVec.ofNat 8 b.toNat).setWidth 32 = (BitVec.ofNat 8 k.toNat).setWidth 32 ↔ b = k := by
  grind

/-! ## 2. Pure mirror of `kissat_next_lit` & `kissat_check_model` and soundness bridge -/

/-- Signed `i8` byte is strictly positive (`1..127`). -/
@[expose, inline] def i8BytePos (b : UInt8) : Bool :=
  0 < b.toNat && b.toNat < 128

/-- Signed `i8` byte is strictly negative (`128..255`). -/
@[expose, inline] def i8ByteNeg (b : UInt8) : Bool :=
  128 ≤ b.toNat

theorem i8_sext32_sgt_zero (b : UInt8) :
    (0#32).slt ((BitVec.ofNat 8 b.toNat).signExtend 32) = i8BytePos b := by
  have hb := b.toNat_lt
  unfold i8BytePos BitVec.slt
  grind

theorem i8_sext32_slt_zero (b : UInt8) :
    ((BitVec.ofNat 8 b.toNat).signExtend 32).slt 0#32 = i8ByteNeg b := by
  have hb := b.toNat_lt
  unfold i8ByteNeg BitVec.slt
  grind

/-- Outcome of parsing a single DIMACS literal token (`kissat_next_lit`). -/
inductive NextLitRes where
  | err
  | endClause (rest : List UInt8)
  | lit (l : Nat) (rest : List UInt8)
  deriving Repr, DecidableEq

/-- Pure executable specification of `kissat_next_lit` with max variable `mv`. -/
@[expose] def nextLitPure (mv : Nat) (bs : List UInt8) : NextLitRes :=
  match skipWsComments bs with
  | [] => .err
  | b :: rest =>
    if b == 45 then
      match parseNat rest with
      | none => .err
      | some (v, rest') =>
        if 1 ≤ v && v ≤ mv then .lit (mkLit (v - 1) false) rest' else .err
    else
      match parseNat (b :: rest) with
      | none => .err
      | some (0, rest') => .endClause rest'
      | some (v, rest') =>
        if v ≤ mv then .lit (mkLit (v - 1) true) rest' else .err

theorem nextLitPure_endClause_length_lt {mv : Nat} {bs rest : List UInt8}
    (h : nextLitPure mv bs = .endClause rest) : rest.length < bs.length := by
  unfold nextLitPure at h
  have hsw_len := skipWsComments_length_le bs
  cases hsw : skipWsComments bs with
  | nil => rw [hsw] at h; cases h
  | cons b tail =>
    rw [hsw] at h hsw_len
    by_cases hb : b = 45
    · simp only [hb, beq_self_eq_true, ↓reduceIte] at h
      cases hpn : parseNat tail with
      | none => rw [hpn] at h; cases h
      | some p =>
        rcases p with ⟨v, rest'⟩; rw [hpn] at h; dsimp only at h
        by_cases hc : (1 ≤ v && v ≤ mv) = true <;> simp [hc] at h
    · simp only [beq_eq_false_iff_ne.mpr hb, Bool.false_eq_true, ↓reduceIte] at h
      cases hpn : parseNat (b :: tail) with
      | none => rw [hpn] at h; cases h
      | some p =>
        rcases p with ⟨v, rest'⟩; rw [hpn] at h
        cases v with
        | zero =>
          simp only [NextLitRes.endClause.injEq] at h; subst h
          have hlt := parseNat_length_lt hpn
          omega
        | succ k => by_cases hc : k + 1 ≤ mv <;> simp [hc] at h

theorem nextLitPure_lit_bounds {mv l : Nat} {bs rest : List UInt8}
    (h : nextLitPure mv bs = .lit l rest) :
    l < 2 * mv ∧ l < 2 * dimacsBound ∧ rest.length < bs.length := by
  unfold nextLitPure at h
  have hsw_len := skipWsComments_length_le bs
  cases hsw : skipWsComments bs with
  | nil => rw [hsw] at h; cases h
  | cons b tail =>
    rw [hsw] at h hsw_len
    by_cases hb : b = 45
    · simp only [hb, beq_self_eq_true, ↓reduceIte] at h
      cases hpn : parseNat tail with
      | none => rw [hpn] at h; cases h
      | some p =>
        rcases p with ⟨v, rest'⟩; rw [hpn] at h; dsimp only at h
        by_cases hc : (1 ≤ v && v ≤ mv) = true
        · simp only [hc, ↓reduceIte, NextLitRes.lit.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
          have hvlt := parseNat_lt_bound hpn
          have hlen := parseNat_length_lt hpn
          simp only [mkLit, Bool.false_eq_true, ↓reduceIte, List.length_cons] at hsw_len ⊢
          omega
        · simp [Bool.eq_false_iff.mpr hc] at h
    · simp only [beq_eq_false_iff_ne.mpr hb, Bool.false_eq_true, ↓reduceIte] at h
      cases hpn : parseNat (b :: tail) with
      | none => rw [hpn] at h; cases h
      | some p =>
        rcases p with ⟨v, rest'⟩; rw [hpn] at h
        cases v with
        | zero => cases h
        | succ k =>
          by_cases hle : k + 1 ≤ mv
          · simp only [hle, ↓reduceIte, NextLitRes.lit.injEq] at h
            rcases h with ⟨rfl, rfl⟩
            have hvlt := parseNat_lt_bound hpn
            have hlen := parseNat_length_lt hpn
            simp only [mkLit, ↓reduceIte] at ⊢
            omega
          · simp [hle] at h

private theorem parseClauseAux_succ_pos' {fuel mv : Nat} {acc : List (Literal Nat)}
    {b : UInt8} {bs tail : List UInt8} (hsw : skipWsComments bs = b :: tail) (hb : b ≠ 45) :
    parseClauseAux (fuel + 1) mv acc bs =
      match parseNat (b :: tail) with
      | some (0, rest') => some (CNF.Clause.ofLiterals acc.reverse, rest')
      | some (v, rest') =>
        if 1 ≤ v && v ≤ mv then parseClauseAux fuel mv ((v, true) :: acc) rest' else none
      | none => none := by
  have := hb
  simp only [parseClauseAux, hsw]
  rcases parseNat (b :: tail) with _ | ⟨v, rest'⟩
  · simp
  · cases v <;> simp

/-- Exact one-step equivalence between `Ref.parseClauseAux` and `nextLitPure`. -/
theorem parseClauseAux_eq_nextLitPure (fuel mv : Nat) (acc : List (Literal Nat))
    (bs : List UInt8) :
    parseClauseAux (fuel + 1) mv acc bs =
      match nextLitPure mv bs with
      | .err => none
      | .endClause rest' => some (CNF.Clause.ofLiterals acc.reverse, rest')
      | .lit l rest' => parseClauseAux fuel mv (kissatLitToDimacsLiteral l :: acc) rest' := by
  cases hsw : skipWsComments bs with
  | nil => simp [parseClauseAux, nextLitPure, hsw]
  | cons b tail =>
    by_cases hb : b = 45
    · subst hb
      simp only [parseClauseAux, nextLitPure, hsw, beq_self_eq_true, ↓reduceIte]
      cases hpn : parseNat tail with
      | none => rfl
      | some p =>
        rcases p with ⟨v, rest'⟩
        by_cases hcond : (1 ≤ v && v ≤ mv) = true
        · simp only [hcond, ↓reduceIte]
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
          have hlit : kissatLitToDimacsLiteral (mkLit (v - 1) false) = (v, false) := by
            simp [kissatLitToDimacsLiteral]; omega
          rw [hlit]
        · have hf : (1 ≤ v && v ≤ mv) = false := Bool.eq_false_iff.mpr hcond
          simp [hf]
    · rw [parseClauseAux_succ_pos' hsw hb]
      simp only [nextLitPure, hsw, beq_eq_false_iff_ne.mpr hb, Bool.false_eq_true, ↓reduceIte]
      cases hpn : parseNat (b :: tail) with
      | none => rfl
      | some p =>
        rcases p with ⟨v, rest'⟩
        cases v with
        | zero => rfl
        | succ k =>
          by_cases hle : k + 1 ≤ mv
          · have hlit : kissatLitToDimacsLiteral (mkLit k true) = (k + 1, true) := by
              simp [kissatLitToDimacsLiteral]
            simp only [hle, Nat.succ_le_succ_iff, Nat.zero_le, Bool.true_and,
              Nat.add_sub_cancel, decide_true, ↓reduceIte, hlit]
          · simp [hle]

/-- Evaluate a 0-based Kissat literal `l` against `valsBytes` (at byte `2 * litVar l`). -/
@[expose] def evalLitVals (valsBytes : List UInt8) (l : Nat) : Bool :=
  let b := valsBytes.getD (2 * litVar l) 0
  if litSign l then i8ByteNeg b else i8BytePos b

/-- Pure mirror of the inner clause loop in `kissat_check_model`. -/
@[expose]
def checkClauseValsAux : Nat → Nat → List UInt8 → Bool → List UInt8 → Option (Bool × List UInt8)
  | 0, _, _, _, _ => none
  | fuel + 1, mv, valsBytes, sat, bs =>
    match nextLitPure mv bs with
    | .err => none
    | .endClause rest => some (sat, rest)
    | .lit l rest => checkClauseValsAux fuel mv valsBytes (sat || evalLitVals valsBytes l) rest

/-- Pure mirror of the outer clause loop in `kissat_check_model`. -/
@[expose] def checkClausesVals (mv : Nat) (valsBytes : List UInt8) : Nat → List UInt8 → Bool
  | 0, bs => (skipWsComments bs).isEmpty
  | k + 1, bs =>
    match checkClauseValsAux (bs.length + 1) mv valsBytes false bs with
    | some (true, rest) => checkClausesVals mv valsBytes k rest
    | _ => false

/-- Total executable mirror of `kissat_check_model(cnfBytes, valsBytes, mv_max)`. -/
@[expose] def runKissatCheckModel (cnfBytes valsBytes : List UInt8) (mv_max : Nat) : Bool :=
  match parseHeader cnfBytes with
  | none => false
  | some (mv, nc, rest) =>
    if mv > mv_max then false
    else checkClausesVals mv valsBytes nc rest

/-- Extract a 1-based `Bool` model array of size `mv + 1` from `valsBytes`, matching the
1-based variable indexing of `Ref.parseDimacs`. -/
@[expose] def modelOfVals (mv : Nat) (valsBytes : List UInt8) : Array Bool :=
  Array.ofFn (n := mv + 1) fun i =>
    if i.1 == 0 then false else i8BytePos (valsBytes.getD (2 * (i.1 - 1)) 0)

theorem evalLitVals_implies_model {mv l : Nat} {valsBytes : List UInt8}
    (hlt : l < 2 * mv) (h : evalLitVals valsBytes l = true) :
    evalVar (modelOfVals mv valsBytes) (kissatLitToDimacsLiteral l).1 =
      (kissatLitToDimacsLiteral l).2 := by
  have hvlt : litVar l < mv := by unfold litVar; omega
  have hev : evalVar (modelOfVals mv valsBytes) (litVar l + 1) =
      i8BytePos (valsBytes.getD (2 * litVar l) 0) := by
    simp [evalVar, modelOfVals, hvlt]
  unfold evalLitVals at h
  simp only [kissatLitToDimacsLiteral, hev]
  cases hs : litSign l
  · rw [hs] at h; simpa using h
  · rw [hs] at h; dsimp only at h
    unfold i8ByteNeg at h; unfold i8BytePos
    grind

theorem checkClauseValsAux_fuel_irrel {f1 f2 mv : Nat} {valsBytes : List UInt8} {sat : Bool}
    {bs : List UInt8} (h1 : bs.length < f1) (h2 : bs.length < f2) :
    checkClauseValsAux f1 mv valsBytes sat bs = checkClauseValsAux f2 mv valsBytes sat bs := by
  induction f1 generalizing f2 sat bs with
  | zero => omega
  | succ f1 ih =>
    cases f2 with
    | zero => omega
    | succ f2 =>
      simp only [checkClauseValsAux]
      cases hn : nextLitPure mv bs with
      | err => rfl
      | endClause rest => rfl
      | lit l rest =>
        have ⟨_, _, hlt⟩ := nextLitPure_lit_bounds hn
        exact ih (by omega) (by omega)

private theorem checkClauseValsAux_sound {fuel mv : Nat} {valsBytes : List UInt8} {sat sat' : Bool}
    {acc : List (Literal Nat)} {bs rest : List UInt8}
    (hsat : sat = true → ∃ lit ∈ acc, evalVar (modelOfVals mv valsBytes) lit.1 = lit.2)
    (h : checkClauseValsAux fuel mv valsBytes sat bs = some (sat', rest)) :
    ∃ cl, parseClauseAux fuel mv acc bs = some (cl, rest) ∧
      (sat' = true → cl.Sat (evalVar (modelOfVals mv valsBytes))) := by
  induction fuel generalizing sat acc bs with
  | zero => simp [checkClauseValsAux] at h
  | succ fuel ih =>
    rw [checkClauseValsAux] at h
    rw [parseClauseAux_eq_nextLitPure]
    cases hn : nextLitPure mv bs with
    | err => rw [hn] at h; cases h
    | endClause rest' =>
      rw [hn] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      refine ⟨CNF.Clause.ofLiterals acc.reverse, rfl, fun ht => ?_⟩
      obtain ⟨lit, hmem, heq⟩ := hsat ht
      rw [CNF.Clause.sat_iff_exists_mem_eq]
      exact ⟨lit, by rw [← CNF.Clause.mem_literals_iff]; simp [hmem], heq⟩
    | lit l rest' =>
      rw [hn] at h
      have ⟨hlt, _, _⟩ := nextLitPure_lit_bounds hn
      refine ih (fun ht => ?_) h
      simp only [Bool.or_eq_true] at ht
      rcases ht with h1 | h2
      · obtain ⟨lit, hmem, heq⟩ := hsat h1
        exact ⟨lit, List.mem_cons_of_mem _ hmem, heq⟩
      · exact ⟨kissatLitToDimacsLiteral l, List.mem_cons_self,
          evalLitVals_implies_model hlt h2⟩

private theorem checkClausesVals_sound {mv k : Nat} {valsBytes bs : List UInt8}
    {accCnf : CNF Nat}
    (hacc : accCnf.Sat (evalVar (modelOfVals mv valsBytes)))
    (h : checkClausesVals mv valsBytes k bs = true) :
    ∃ cnf, parseClauses mv k accCnf bs = some cnf ∧
      cnf.Sat (evalVar (modelOfVals mv valsBytes)) := by
  induction k generalizing accCnf bs with
  | zero =>
    simp only [checkClausesVals] at h
    exact ⟨accCnf, by simp [parseClauses, h], hacc⟩
  | succ k ih =>
    simp only [checkClausesVals] at h
    cases hc : checkClauseValsAux (bs.length + 1) mv valsBytes false bs with
    | none => rw [hc] at h; cases h
    | some p =>
      rcases p with ⟨sat, rest⟩
      rw [hc] at h
      cases sat with
      | false => cases h
      | true =>
        obtain ⟨cl, hcl, hcl_sat⟩ := checkClauseValsAux_sound (acc := []) (by simp) hc
        have hpc : parseClause mv bs = some (cl, rest) := hcl
        have hadd_sat : (accCnf.add cl).Sat (evalVar (modelOfVals mv valsBytes)) :=
          CNF.sat_add.mpr ⟨hcl_sat rfl, hacc⟩
        obtain ⟨cnf, hpc', hsat'⟩ := ih hadd_sat h
        exact ⟨cnf, by simp [parseClauses, hpc, hpc'], hsat'⟩

/-- Pure soundness of `runKissatCheckModel`, bridging `Ref.parseDimacs` directly to
`Ref.checkModel_sound`. -/
theorem runKissatCheckModel_sound {cnfBytes valsBytes : List UInt8} {mv_max : Nat}
    (h : runKissatCheckModel cnfBytes valsBytes mv_max = true) :
    ∃ cnf mv, parseDimacs cnfBytes = some cnf ∧
      checkModel cnf (modelOfVals mv valsBytes) = true ∧
      ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α := by
  unfold runKissatCheckModel at h
  cases hh : parseHeader cnfBytes with
  | none => rw [hh] at h; cases h
  | some p =>
    rcases p with ⟨mv, nc, rest⟩
    rw [hh] at h; dsimp only at h
    split at h
    · cases h
    · obtain ⟨cnf, hcls, hsat⟩ := checkClausesVals_sound (accCnf := CNF.empty) (by simp) h
      have hcm : checkModel cnf (modelOfVals mv valsBytes) = true :=
        (checkModel_iff_sat cnf (modelOfVals mv valsBytes)).mpr hsat
      have hsound := checkModel_sound hcm
      exact ⟨cnf, mv, by simp [parseDimacs, hh, hcls], hcm, hsound.1, hsound.2⟩

/-- Every variable in a clause returned by `parseClauseAux` is positive when `acc` is positive. -/
theorem parseClauseAux_vars_pos {fuel mv : Nat} {acc : List (Literal Nat)}
    {bs rest : List UInt8} {cl : CNF.Clause Nat}
    (hacc : ∀ lit ∈ acc, 1 ≤ lit.1)
    (h : parseClauseAux fuel mv acc bs = some (cl, rest)) :
    ∀ lit ∈ cl.literals, 1 ≤ lit.1 := by
  induction fuel generalizing acc bs with
  | zero => simp [parseClauseAux] at h
  | succ fuel ih =>
    rw [parseClauseAux_eq_nextLitPure] at h
    cases hn : nextLitPure mv bs with
    | err => rw [hn] at h; cases h
    | endClause rest' =>
      rw [hn] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      intro lit hlit
      simp only [CNF.Clause.literals_ofLiterals, List.mem_reverse] at hlit
      exact hacc lit hlit
    | lit l rest' =>
      rw [hn] at h
      refine ih (fun lit hlit => ?_) h
      rcases List.mem_cons.mp hlit with rfl | hm
      · simp [kissatLitToDimacsLiteral]
      · exact hacc lit hm

theorem kissatLitToDimacsLiteral_inj {l1 l2 : Nat}
    (h : kissatLitToDimacsLiteral l1 = kissatLitToDimacsLiteral l2) : l1 = l2 := by
  unfold kissatLitToDimacsLiteral litVar litSign at h
  simp only [Prod.mk.injEq, Bool.not_inj_iff] at h
  rcases h with ⟨hv, hs⟩
  rcases Nat.mod_two_eq_zero_or_one l1 with h1 | h1 <;>
    rcases Nat.mod_two_eq_zero_or_one l2 with h2 | h2 <;> simp [h1, h2] at hs <;> omega

/-- Deterministic unit-only SAT trace (all clauses are unit-assigning and non-conflicting). -/
inductive UnitSatTrace (mv : Nat) : List (BitVec 8) → Nat → List UInt8 → Nat →
    List (BitVec 8) → Nat → Prop where
  | done {vals te bs} :
      (skipWsComments bs).isEmpty = true →
      UnitSatTrace mv vals te bs 0 vals te
  | step {vals te bs l rest k vals' te'} :
      l < 2 * mv →
      parseClause mv bs = some (CNF.Clause.ofLiterals [kissatLitToDimacsLiteral l], rest) →
      vals[l]?.getD 0#8 = 0#8 →
      UnitSatTrace mv ((vals.set l 1#8).set (l ^^^ 1) 0xFF#8) (te + 1) rest k vals' te' →
      UnitSatTrace mv vals te bs (k + 1) vals' te'

/-- Deterministic unit-only UNSAT trace (unit prefix ending in a unit conflict, valid tail). -/
inductive UnitUnsatTrace (mv : Nat) : List (BitVec 8) → List UInt8 → Nat → Prop where
  | conflict {vals bs l rest k} :
      l < 2 * mv →
      parseClause mv bs = some (CNF.Clause.ofLiterals [kissatLitToDimacsLiteral l], rest) →
      vals[l]?.getD 0#8 = 0xFF#8 →
      (∃ cnf, parseClauses mv k CNF.empty rest = some cnf) →
      UnitUnsatTrace mv vals bs (k + 1)
  | step {vals bs l rest k} :
      l < 2 * mv →
      parseClause mv bs = some (CNF.Clause.ofLiterals [kissatLitToDimacsLiteral l], rest) →
      vals[l]?.getD 0#8 = 0#8 →
      UnitUnsatTrace mv ((vals.set l 1#8).set (l ^^^ 1) 0xFF#8) rest k →
      UnitUnsatTrace mv vals bs (k + 1)

theorem parseClauses_some_of_acc {mv k : Nat} {bs : List UInt8}
    {acc1 acc2 cnf1 : CNF Nat}
    (h : parseClauses mv k acc1 bs = some cnf1) :
    ∃ cnf2, parseClauses mv k acc2 bs = some cnf2 := by
  induction k generalizing bs acc1 acc2 with
  | zero =>
    simp only [parseClauses] at h ⊢
    split at h
    · exact ⟨acc2, by simp_all⟩
    · cases h
  | succ k ih =>
    simp only [parseClauses] at h ⊢
    cases hpc : parseClause mv bs with
    | none => rw [hpc] at h; cases h
    | some p =>
      rcases p with ⟨cl, rest⟩
      rw [hpc] at h
      exact ih h

theorem cnf_unsat_add {F : CNF Nat} {cl : CNF.Clause Nat}
    (hu : F.Unsat) : (F.add cl).Unsat := by
  rw [CNF.unsat_iff_not_sat] at hu ⊢
  intro α hα; exact hu α (CNF.sat_add.mp hα).2


/-! ## 5. Shared separation-logic framing helpers -/

theorem nv_sep_append {P Q : Mem 64 → Prop} {a b : BitVec 64} {bs1 bs2 : List UInt8}
    (hb : b = a + BitVec.ofNat 64 bs1.length) (hlen : bs1.length + bs2.length ≤ 2 ^ 64)
    (h1 : P (bs1.At a)) (h2 : Q (bs2.At b)) : (P ⋆ Q) ((bs1 ++ bs2).At a) := by
  have heq := congrFun (Mem.At_append_sep bs1 bs2 a hlen) ((bs1 ++ bs2).At a)
  rw [← hb] at heq
  exact sep_mono2 (fun _ h => h ▸ h1) (fun _ h => h ▸ h2) _ (heq.mp rfl)

theorem sep_exists_eq {P Q : Mem 64 → Prop} {M : Mem 64}
    (h : (P ⋆ Q) M) : ∃ m : Mem 64, P m ∧ (Eq m ⋆ Q) M := by
  have hm := sep_mono (Q := Q)
    (fun x hx => (⟨x, ⟨hx, rfl⟩⟩ : ∃ m : Mem 64, P m ∧ Eq m x)) h
  rw [sep_ex_l] at hm
  obtain ⟨m, hm'⟩ := hm
  exact ⟨m, sep_pure_l (φ := P m) (P := Eq m) (R := Q).mp hm'⟩

theorem sep_swap_l {P Q R : Mem 64 → Prop} {m : Mem 64}
    (h : (P ⋆ (Q ⋆ R)) m) : (Q ⋆ (P ⋆ R)) m := by
  rw [← sep_assoc, sep_comm P Q, sep_assoc] at h; exact h

/-! ## 6. Shared BitVec arithmetic and list helpers -/

theorem bv64_add_small_eq {a b : BitVec 64} (h : a.toNat + b.toNat < 2 ^ 64) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

theorem bv64_add_small {k x : BitVec 64} {n : Nat} (hk : k.toNat = n)
    (hsum : n + x.toNat < 2 ^ 64) : (k + x).toNat = n + x.toNat := by
  rw [BitVec.toNat_add, hk, Nat.mod_eq_of_lt hsum]

theorem bv64_add1_toNat_lt {g : BitVec 64} (h : g.toNat + 1 < 2 ^ 64) :
    (g + 1).toNat = g.toNat + 1 := by
  rw [BitVec.toNat_add, show (1 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt h]

theorem nodup_of_map {α : Type _} {β : Type _} (f : α → β) :
    ∀ {xs : List α}, (xs.map f).Nodup → xs.Nodup
  | [], _ => .nil
  | _ :: _, h =>
    let hm := List.nodup_cons.mp h
    List.nodup_cons.mpr ⟨fun hmem => hm.1 (List.mem_map_of_mem hmem), nodup_of_map f hm.2⟩

end LeanQbe.T.Examples.Kissat.Proof.Spec
